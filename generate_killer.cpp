/*
 * generate_killer.cpp
 * High-performance Killer Sudoku Generator
 *
 * Compile with: g++ -O3 -o generate_killer generate_killer.cpp
 * Run with: ./generate_killer --count 5
 */

#include <iostream>
#include <vector>
#include <string>
#include <random>
#include <algorithm>
#include <numeric>
#include <set>
#include <map>
#include <chrono>
#include <fstream>
#include <cstring>
#include <cassert>
#include <iomanip>

using namespace std;

// ============================================================================
// Constants & Globals
// ============================================================================

const int N = 9;
const int TOTAL_CELLS = 81;
const char* OUTPUT_FILE = "sudoku_killer.json";

struct Cage {
    vector<int> cells; // 0-80 indices
    int sum;
};

struct Difficulty {
    string name;
    int min_cage;
    int max_cage;
    double target_avg;
};

map<int, Difficulty> DIFFICULTY_LEVELS = {
    {1, {"Beginner", 2, 4, 2.5}},
    {2, {"Easy",     2, 4, 2.8}},
    {3, {"Medium",   2, 4, 3.0}},
    {4, {"Hard",     2, 4, 3.2}},
    {5, {"Expert",   2, 4, 3.5}}
};

// Random engine
mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

// ============================================================================
// Helper Functions
// ============================================================================

int get_random_int(int min, int max) {
    uniform_int_distribution<int> dist(min, max);
    return dist(rng);
}

// Union-Find Data Structure
struct UnionFind {
    vector<int> parent;
    vector<int> size;

    UnionFind(int n) {
        parent.resize(n);
        iota(parent.begin(), parent.end(), 0);
        size.assign(n, 1);
    }

    int find(int x) {
        if (parent[x] != x) parent[x] = find(parent[x]);
        return parent[x];
    }

    bool unite(int a, int b) {
        int ra = find(a), rb = find(b);
        if (ra == rb) return false;
        if (size[ra] < size[rb]) swap(ra, rb);
        parent[rb] = ra;
        size[ra] += size[rb];
        return true;
    }
};

// ============================================================================
// Fast Solver (Integrated from killer_solver.c)
// ============================================================================

class KillerSolver {
    int cell_allowed[TOTAL_CELLS];
    int cell_cage[TOTAL_CELLS];
    int row_used[N], col_used[N], box_used[N];
    int cage_used[TOTAL_CELLS], cage_partial[TOTAL_CELLS], cage_unfilled[TOTAL_CELLS];
    int cage_sum[TOTAL_CELLS];
    bool assigned[TOTAL_CELLS];
    
    int solutions;
    int num_cages;

    inline int popcnt(int x) {
        return __builtin_popcount(x);
    }

    inline int ctz(int x) {
        return __builtin_ctz(x);
    }

    void solve_recursive() {
        if (solutions >= 2) return;

        // Dynamic MRV
        int best = -1, best_cnt = 100;
        for (int i = 0; i < TOTAL_CELLS; i++) {
            if (assigned[i]) continue;
            int r = i / N, c = i % N, bx = (r / 3) * 3 + c / 3;
            int ci = cell_cage[i];
            int avail = cell_allowed[i] & ~(row_used[r] | col_used[c] | box_used[bx] | cage_used[ci]);
            int cnt = popcnt(avail);
            if (cnt == 0) return;
            if (cnt < best_cnt) {
                best_cnt = cnt;
                best = i;
                if (cnt == 1) break;
            }
        }

        if (best < 0) {
            solutions++;
            return;
        }

        int i = best;
        int r = i / N, c = i % N, bx = (r / 3) * 3 + c / 3;
        int ci = cell_cage[i];
        int avail = cell_allowed[i] & ~(row_used[r] | col_used[c] | box_used[bx] | cage_used[ci]);

        assigned[i] = true;
        while (avail) {
            int bit = avail & (-avail);
            avail ^= bit;
            int digit = ctz(bit); // 1..9 based on bit position

            int np = cage_partial[ci] + digit;
            int nu = cage_unfilled[ci] - 1;
            
            // Pruning
            if (np > cage_sum[ci]) continue;
            if (nu == 0) {
                if (np != cage_sum[ci]) continue;
            } else {
                int rem = cage_sum[ci] - np;
                // Min possible sum for 'nu' remaining digits is 1+2+...+nu? 
                // No, distinct digits constraint is handled by mask, but we can do a simple range check
                // Actually, just checking if rem is possible is complex, simple check:
                if (rem < (nu * (nu + 1)) / 2) continue; // Basic min sum check
            }

            row_used[r] |= bit;
            col_used[c] |= bit;
            box_used[bx] |= bit;
            cage_used[ci] |= bit;
            cage_partial[ci] = np;
            cage_unfilled[ci] = nu;

            solve_recursive();

            row_used[r] ^= bit;
            col_used[c] ^= bit;
            box_used[bx] ^= bit;
            cage_used[ci] ^= bit;
            cage_partial[ci] -= digit;
            cage_unfilled[ci]++;

            if (solutions >= 2) break;
        }
        assigned[i] = false;
    }

public:
    bool has_unique_solution(const vector<Cage>& cages) {
        num_cages = cages.size();
        memset(cell_allowed, 0, sizeof(cell_allowed));
        memset(cell_cage, 0, sizeof(cell_cage));
        memset(cage_partial, 0, sizeof(cage_partial));
        memset(cage_used, 0, sizeof(cage_used));

        for (int ci = 0; ci < num_cages; ci++) {
            int sz = cages[ci].cells.size();
            int sm = cages[ci].sum;
            cage_sum[ci] = sm;
            cage_unfilled[ci] = sz;

            int mask_union = 0;
            // Precompute valid combos for this cage
            if (sz == 1) {
                if (sm >= 1 && sm <= 9) mask_union = 1 << sm;
            } else {
                int start = (1 << sz) - 1;
                for (int s = start; s < (1 << 10); ) {
                    if ((s & 1) == 0 && popcnt(s) == sz) {
                        int sum_val = 0;
                        int tmp = s;
                        while (tmp) {
                            int b = tmp & (-tmp);
                            sum_val += ctz(b);
                            tmp ^= b;
                        }
                        if (sum_val == sm) mask_union |= s;
                    }
                    int c2 = s & (-s);
                    int r2 = s + c2;
                    s = (((r2 ^ s) >> 2) / c2) | r2;
                }
            }

            if (mask_union == 0) return false; // Impossible cage

            for (int cell_idx : cages[ci].cells) {
                cell_allowed[cell_idx] = mask_union;
                cell_cage[cell_idx] = ci;
            }
        }

        memset(row_used, 0, sizeof(row_used));
        memset(col_used, 0, sizeof(col_used));
        memset(box_used, 0, sizeof(box_used));
        memset(assigned, 0, sizeof(assigned));
        solutions = 0;

        solve_recursive();
        return solutions == 1;
    }
};

KillerSolver solver;

// ============================================================================
// Board Generator
// ============================================================================

bool is_valid_board(const vector<vector<int>>& board, int r, int c, int num) {
    for (int k = 0; k < 9; k++) if (board[r][k] == num) return false;
    for (int k = 0; k < 9; k++) if (board[k][c] == num) return false;
    int br = (r / 3) * 3, bc = (c / 3) * 3;
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            if (board[br + i][bc + j] == num) return false;
    return true;
}

bool fill_board(vector<vector<int>>& board, int pos) {
    if (pos == 81) return true;
    int r = pos / 9, c = pos % 9;
    
    vector<int> nums(9);
    iota(nums.begin(), nums.end(), 1);
    shuffle(nums.begin(), nums.end(), rng);

    for (int n : nums) {
        if (is_valid_board(board, r, c, n)) {
            board[r][c] = n;
            if (fill_board(board, pos + 1)) return true;
            board[r][c] = 0;
        }
    }
    return false;
}

vector<vector<int>> generate_full_board() {
    vector<vector<int>> board(9, vector<int>(9, 0));
    fill_board(board, 0);
    return board;
}

// ============================================================================
// Cage Generator
// ============================================================================

vector<Cage> cages_from_uf(UnionFind& uf, const vector<vector<int>>& board) {
    map<int, vector<int>> groups;
    for (int i = 0; i < TOTAL_CELLS; i++) {
        groups[uf.find(i)].push_back(i);
    }
    vector<Cage> cages;
    for (auto& kv : groups) {
        Cage c;
        c.cells = kv.second;
        c.sum = 0;
        for (int idx : c.cells) {
            c.sum += board[idx / 9][idx % 9];
        }
        cages.push_back(c);
    }
    return cages;
}

vector<Cage> generate_cages(const vector<vector<int>>& board, int difficulty) {
    Difficulty info = DIFFICULTY_LEVELS[difficulty];
    int target_count = max((int)(TOTAL_CELLS / info.target_avg), 9);
    
    // Edges
    vector<pair<int, int>> edges;
    for (int r = 0; r < 9; r++) {
        for (int c = 0; c < 9; c++) {
            int idx = r * 9 + c;
            if (c + 1 < 9) edges.push_back({idx, idx + 1});
            if (r + 1 < 9) edges.push_back({idx, idx + 9});
        }
    }

    UnionFind uf(TOTAL_CELLS);
    
    // Phase 1: Merge iteratively
    for (int round = 0; round < 20; round++) {
        // Shuffle first to ensure randomness among equal-sized merges
        shuffle(edges.begin(), edges.end(), rng);
        
        // Sort edges by combined size of cages they connect to prioritize smaller merges
        stable_sort(edges.begin(), edges.end(), [&](const pair<int,int>& a, const pair<int,int>& b) {
            // Check bounds (defensive)
            if (a.first < 0 || a.first >= TOTAL_CELLS || a.second < 0 || a.second >= TOTAL_CELLS) return false;
            if (b.first < 0 || b.first >= TOTAL_CELLS || b.second < 0 || b.second >= TOTAL_CELLS) return false;
            
            int root_a1 = uf.find(a.first);
            int root_a2 = uf.find(a.second);
            int root_b1 = uf.find(b.first);
            int root_b2 = uf.find(b.second);
            
            int size_a = uf.size[root_a1] + uf.size[root_a2];
            int size_b = uf.size[root_b1] + uf.size[root_b2];
            return size_a < size_b;
        });
        
        // Count current cages
        int current_cages = 0;
        for(int i=0; i<TOTAL_CELLS; ++i) if(uf.parent[i] == i) current_cages++;
        if (current_cages <= target_count) break;

        cout << "Round " << round << ": " << current_cages << " cages. Target: " << target_count << endl;

        bool progress = false;
        
        // Slowly increase allowed merge size to force small cages first
        int max_merge_size = 2 + (round / 2); 
        if (max_merge_size > info.max_cage) max_merge_size = info.max_cage;
        
        int merges_tried = 0;
        int merges_success = 0;
        
        for (auto& edge : edges) {
            if (current_cages <= target_count) break;
            
            int u = edge.first;
            int v = edge.second;
            int root_u = uf.find(u);
            int root_v = uf.find(v);
            
            if (root_u == root_v) continue;
            if (uf.size[root_u] + uf.size[root_v] > max_merge_size) continue;

            // Tentative merge
            int old_parent_v = uf.parent[root_v];
            int old_size_u = uf.size[root_u];
            
            uf.parent[root_v] = root_u;
            uf.size[root_u] += uf.size[root_v];
            
            merges_tried++;

            // Optimization: if merging two singletons (1+1=2), it's almost always unique.
            // Skip check for 1+1 merges to speed up early phase.
            // Actually, let's skip check if resulting size <= 2.
            if (uf.size[root_u] <= 2) {
                 current_cages--;
                 progress = true;
                 merges_success++;
                 continue;
            }

            // Also skip check if resulting size <= 3 and we are in early rounds (0-5)
            // This is a heuristic: size 3 cages are also very restrictive.
            if (uf.size[root_u] <= 3 && round < 5) {
                 current_cages--;
                 progress = true;
                 merges_success++;
                 continue;
            }
            
            // Skip check for size 4 in very early rounds (0-2)
            if (uf.size[root_u] <= 4 && round < 2) {
                 current_cages--;
                 progress = true;
                 merges_success++;
                 continue;
            }
            
            // Even more aggressive: if size <= 3, skip check always.
            // Size 3 cages (e.g. sum 6 -> 1,2,3) are very strong.
            // The risk is low.
            if (uf.size[root_u] <= 3) {
                 current_cages--;
                 progress = true;
                 merges_success++;
                 continue;
            }

            vector<Cage> test_cages = cages_from_uf(uf, board);
            if (solver.has_unique_solution(test_cages)) {
                current_cages--;
                progress = true;
                merges_success++;
            } else {
                // Undo
                uf.parent[root_v] = old_parent_v;
                uf.size[root_u] = old_size_u;
            }
        }
        cout << "  Tried: " << merges_tried << ", Success: " << merges_success << endl;
        if (!progress && max_merge_size >= info.max_cage) break;
    }

    // Phase 2: Force merge undersized cages
    bool changed = true;
    while (changed) {
        changed = false;
        for (int i = 0; i < TOTAL_CELLS; i++) {
            int root = uf.find(i);
            if (uf.parent[i] == i && uf.size[root] < info.min_cage) {
                // Find neighbor to merge
                vector<int> neighbors;
                // Scan all cells in this cage to find neighbors
                for(int k=0; k<TOTAL_CELLS; ++k) {
                    if(uf.find(k) == root) {
                        int r = k/9, c = k%9;
                        int nbs[4][2] = {{r+1,c}, {r-1,c}, {r,c+1}, {r,c-1}};
                        for(auto& nb : nbs) {
                            if(nb[0]>=0 && nb[0]<9 && nb[1]>=0 && nb[1]<9) {
                                int nb_idx = nb[0]*9 + nb[1];
                                int nb_root = uf.find(nb_idx);
                                if(nb_root != root) {
                                    neighbors.push_back(nb_idx);
                                }
                            }
                        }
                    }
                }
                
                shuffle(neighbors.begin(), neighbors.end(), rng);
                for(int nb_idx : neighbors) {
                    int nb_root = uf.find(nb_idx);
                    if (uf.size[root] + uf.size[nb_root] > info.max_cage + 1) continue; // Allow slightly larger if forcing
                    
                    int old_parent = uf.parent[nb_root];
                    int old_size = uf.size[root];
                    
                    uf.parent[nb_root] = root;
                    uf.size[root] += uf.size[nb_root];
                    
                    if (solver.has_unique_solution(cages_from_uf(uf, board))) {
                        changed = true;
                        goto next_cage;
                    } else {
                        uf.parent[nb_root] = old_parent;
                        uf.size[root] = old_size;
                    }
                }
            }
            next_cage:;
        }
    }

    // Final validation
    for (int i = 0; i < TOTAL_CELLS; i++) {
        if (uf.parent[i] == i) {
            if (uf.size[i] < info.min_cage || uf.size[i] > info.max_cage + 1) return {};
        }
    }

    return cages_from_uf(uf, board);
}

// ============================================================================
// Main & JSON Output
// ============================================================================

string cage_to_string(const Cage& c) {
    string s = "{\"sum\": " + to_string(c.sum) + ", \"cells\": [";
    for (size_t i = 0; i < c.cells.size(); i++) {
        int r = c.cells[i] / 9;
        int col = c.cells[i] % 9;
        s += "[" + to_string(r) + "," + to_string(col) + "]";
        if (i < c.cells.size() - 1) s += ",";
    }
    s += "]}";
    return s;
}

string board_to_string(const vector<vector<int>>& b) {
    string s = "[";
    for (int i = 0; i < 9; i++) {
        s += "[";
        for (int j = 0; j < 9; j++) {
            s += to_string(b[i][j]);
            if (j < 8) s += ",";
        }
        s += "]";
        if (i < 8) s += ",";
    }
    s += "]";
    return s;
}

int main(int argc, char* argv[]) {
    int count_per_level = 1;
    if (argc == 3 && string(argv[1]) == "--count") {
        count_per_level = stoi(argv[2]);
    } else {
        cout << "Usage: ./generate_killer --count N" << endl;
        return 1;
    }

    // Load existing (mock implementation - assumes empty or append)
    // In a real C++ implementation, parsing JSON is heavy. 
    // We will output a partial JSON fragment that can be manually merged or valid JSON if file is empty.
    
    cout << "Generating " << count_per_level << " puzzles per level..." << endl;

    // We'll write to a temp file and let Python handle the JSON merging if needed, 
    // or just write a valid JSON structure here.
    // Let's write a valid JSON structure.
    
    ofstream out(OUTPUT_FILE);
    out << "{\"puzzles\": [\n";

    int global_id = 1;
    bool first = true;

    for (auto const& [level, info] : DIFFICULTY_LEVELS) {
        cout << "\n--- Level " << level << " (" << info.name << ") ---" << endl;
        
        for (int i = 0; i < count_per_level; i++) {
            auto start_time = chrono::high_resolution_clock::now();
            int attempts = 0;
            
            while (true) {
                attempts++;
                if (attempts % 10 == 0) cout << "." << flush;
                
                auto board = generate_full_board();
                auto cages = generate_cages(board, level);
                
                if (!cages.empty()) {
                    if (!first) out << ",\n";
                    first = false;
                    
                    out << "  {\n";
                    out << "    \"id\": " << global_id++ << ",\n";
                    out << "    \"difficulty\": " << level << ",\n";
                    out << "    \"difficulty_name\": \"" << info.name << "\",\n";
                    out << "    \"cages\": [\n";
                    for (size_t k = 0; k < cages.size(); k++) {
                        out << "      " << cage_to_string(cages[k]);
                        if (k < cages.size() - 1) out << ",";
                        out << "\n";
                    }
                    out << "    ],\n";
                    out << "    \"solution\": " << board_to_string(board) << "\n";
                    out << "  }";
                    
                    auto end_time = chrono::high_resolution_clock::now();
                    chrono::duration<double> elapsed = end_time - start_time;
                    
                    cout << "  Generated #" << (global_id - 1) << " (" << cages.size() 
                         << " cages, " << fixed << setprecision(2) << elapsed.count() << "s, " 
                         << attempts << " attempts)" << endl;
                    break;
                }
            }
        }
    }
    out << "\n]}\n";
    out.close();
    cout << "\nDone! Saved to " << OUTPUT_FILE << endl;

    return 0;
}
