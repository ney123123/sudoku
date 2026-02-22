/*
 * generate_arrow.cpp
 * Arrow Sudoku Generator
 * 9x9 grid + arrows: circle value = sum of body cell values.
 *
 * Compile: g++ -std=c++17 -O3 -o generate_arrow generate_arrow.cpp
 * Run: ./generate_arrow --count N
 */

#include <iostream>
#include <vector>
#include <string>
#include <random>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <cstring>
#include <iomanip>
#include <map>
#include <numeric>
#include <set>

using namespace std;

const int N = 9;
const int TOTAL_CELLS = 81;
const char* OUTPUT_FILE = "sudoku_arrow.json";

struct Difficulty {
    string name;
    int target_clues;
};

map<int, Difficulty> DIFFICULTY_LEVELS = {
    {1, {"Beginner", 38}},
    {2, {"Easy",     33}},
    {3, {"Medium",   28}},
    {4, {"Hard",     23}},
    {5, {"Expert",   10}}
};

// Level 1-4: body length 2 or 3; Level 5: body length 3 or 4
const int MIN_ARROWS = 8;
const int MAX_ARROWS = 12;

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

inline int get_box(int r, int c) {
    return (r / 3) * 3 + (c / 3);
}

struct Arrow {
    int circle_r, circle_c;
    vector<pair<int,int>> body;
};

// ============================================================================
// Full 9x9 solution filler (backtrack, random digit order)
// ============================================================================

static int filler_board[N][N];
static int filler_row[N], filler_col[N], filler_box[N];

static bool filler_can_place(int r, int c, int digit) {
    int bit = 1 << (digit - 1);
    if (filler_row[r] & bit) return false;
    if (filler_col[c] & bit) return false;
    if (filler_box[get_box(r, c)] & bit) return false;
    return true;
}

static void filler_place(int r, int c, int digit) {
    int bit = 1 << (digit - 1);
    filler_board[r][c] = digit;
    filler_row[r] |= bit;
    filler_col[c] |= bit;
    filler_box[get_box(r, c)] |= bit;
}

static void filler_unplace(int r, int c, int digit) {
    int bit = 1 << (digit - 1);
    filler_board[r][c] = 0;
    filler_row[r] ^= bit;
    filler_col[c] ^= bit;
    filler_box[get_box(r, c)] ^= bit;
}

static bool fill_recursive(int pos) {
    if (pos >= TOTAL_CELLS) return true;
    int r = pos / N, c = pos % N;
    vector<int> digits(N);
    iota(digits.begin(), digits.end(), 1);
    shuffle(digits.begin(), digits.end(), rng);
    for (int d : digits) {
        if (!filler_can_place(r, c, d)) continue;
        filler_place(r, c, d);
        if (fill_recursive(pos + 1)) return true;
        filler_unplace(r, c, d);
    }
    return false;
}

static void generate_full_solution(int out[N][N]) {
    memset(filler_board, 0, sizeof(filler_board));
    memset(filler_row, 0, sizeof(filler_row));
    memset(filler_col, 0, sizeof(filler_col));
    memset(filler_box, 0, sizeof(filler_box));
    fill_recursive(0);
    memcpy(out, filler_board, sizeof(filler_board));
}

// ============================================================================
// Arrow placement: find body cells (same row or column, contiguous) that sum to circle value
// ============================================================================

static bool used_cells[N][N];

static void clear_used() {
    memset(used_cells, 0, sizeof(used_cells));
}

static void mark_arrow_used(const Arrow& ar) {
    used_cells[ar.circle_r][ar.circle_c] = true;
    for (const auto& p : ar.body) used_cells[p.first][p.second] = true;
}

static bool arrow_overlaps_used(const Arrow& ar) {
    if (used_cells[ar.circle_r][ar.circle_c]) return true;
    for (const auto& p : ar.body)
        if (used_cells[p.first][p.second]) return true;
    return false;
}

// Try to find a body of length body_len in the solution that sums to target, using only unused cells.
// Body must be contiguous in one row or one column; body must not include (cr, cc).
static bool find_body(const int solution[N][N], int cr, int cc, int target, int body_len,
                      vector<pair<int,int>>& out_body) {
    out_body.clear();
    if (body_len <= 0 || body_len > 4) return false;

    // Try contiguous segments in same row
    for (int r = 0; r < N; r++) {
        for (int c0 = 0; c0 + body_len <= N; c0++) {
            int sum = 0;
            bool skip = false;
            for (int k = 0; k < body_len; k++) {
                int c = c0 + k;
                if (used_cells[r][c]) { skip = true; break; }
                if (r == cr && c == cc) { skip = true; break; }
                sum += solution[r][c];
            }
            if (!skip && sum == target) {
                for (int k = 0; k < body_len; k++)
                    out_body.push_back({r, c0 + k});
                return true;
            }
        }
    }

    // Try contiguous segments in same column
    for (int c = 0; c < N; c++) {
        for (int r0 = 0; r0 + body_len <= N; r0++) {
            int sum = 0;
            bool skip = false;
            for (int k = 0; k < body_len; k++) {
                int r = r0 + k;
                if (used_cells[r][c]) { skip = true; break; }
                if (r == cr && c == cc) { skip = true; break; }
                sum += solution[r][c];
            }
            if (!skip && sum == target) {
                for (int k = 0; k < body_len; k++)
                    out_body.push_back({r0 + k, c});
                return true;
            }
        }
    }
    return false;
}

// Place arrows on the solution. Returns false if we cannot place enough arrows.
static bool place_arrows(const int solution[N][N], int difficulty, vector<Arrow>& arrows) {
    arrows.clear();
    clear_used();

    int body_len_min = (difficulty == 5) ? 3 : 2;
    int body_len_max = (difficulty == 5) ? 4 : 3;
    uniform_int_distribution<int> num_arrows_dist(MIN_ARROWS, MAX_ARROWS);
    int target_arrows = num_arrows_dist(rng);

    vector<pair<int,int>> order;
    for (int r = 0; r < N; r++)
        for (int c = 0; c < N; c++)
            order.push_back({r, c});

    for (int attempt = 0; attempt < 3; attempt++) {
        arrows.clear();
        clear_used();
        shuffle(order.begin(), order.end(), rng);

        for (int a = 0; a < target_arrows; a++) {
            bool found = false;
            for (const auto& pt : order) {
                int cr = pt.first, cc = pt.second;
                if (used_cells[cr][cc]) continue;
                int T = solution[cr][cc];
                if (T < 2 || T > 36) continue;  // body sum typically 2..36

                uniform_int_distribution<int> len_dist(body_len_min, body_len_max);
                int body_len = len_dist(rng);
                vector<pair<int,int>> body;
                if (find_body(solution, cr, cc, T, body_len, body)) {
                    Arrow ar;
                    ar.circle_r = cr;
                    ar.circle_c = cc;
                    ar.body = body;
                    if (!arrow_overlaps_used(ar)) {
                        arrows.push_back(ar);
                        mark_arrow_used(ar);
                        found = true;
                        break;
                    }
                }
            }
            if (!found) break;
        }
        if ((int)arrows.size() >= MIN_ARROWS)
            return true;
    }
    return false;
}

// ============================================================================
// Arrow Sudoku Solver (solution count cap 2)
// ============================================================================

class ArrowSolver {
    int board[N][N];
    int row_used[N], col_used[N], box_used[N];
    vector<Arrow> arrows_;
    int solutions;
    chrono::steady_clock::time_point deadline_;
    bool use_deadline_;
    long long nodes_;

    bool can_place(int r, int c, int digit) const {
        int bit = 1 << (digit - 1);
        if (row_used[r] & bit) return false;
        if (col_used[c] & bit) return false;
        if (box_used[get_box(r, c)] & bit) return false;
        return true;
    }

    void place(int r, int c, int digit) {
        int bit = 1 << (digit - 1);
        board[r][c] = digit;
        row_used[r] |= bit;
        col_used[c] |= bit;
        box_used[get_box(r, c)] |= bit;
    }

    void unplace(int r, int c, int digit) {
        int bit = 1 << (digit - 1);
        board[r][c] = 0;
        row_used[r] ^= bit;
        col_used[c] ^= bit;
        box_used[get_box(r, c)] ^= bit;
    }

    bool check_arrows() const {
        for (const auto& ar : arrows_) {
            int circle_val = board[ar.circle_r][ar.circle_c];
            int body_sum = 0;
            for (const auto& p : ar.body)
                body_sum += board[p.first][p.second];
            if (circle_val != body_sum) return false;
        }
        return true;
    }

    void solve_recursive(int pos) {
        if (solutions >= 2) return;
        nodes_++;
        if (use_deadline_ && (nodes_ % 512 == 0) && chrono::steady_clock::now() >= deadline_) {
            solutions = 2;
            return;
        }
        if (pos >= TOTAL_CELLS) {
            if (check_arrows()) solutions++;
            return;
        }
        int r = pos / N, c = pos % N;
        if (board[r][c] != 0) {
            solve_recursive(pos + 1);
            return;
        }
        for (int d = 1; d <= N; d++) {
            if (!can_place(r, c, d)) continue;
            place(r, c, d);
            solve_recursive(pos + 1);
            unplace(r, c, d);
            board[r][c] = 0;
            if (solutions >= 2) return;
        }
    }

public:
    ArrowSolver() { memset(board, 0, sizeof(board)); }

    void load(const int b[N][N], const vector<Arrow>& arrows) {
        memcpy(board, b, sizeof(board));
        arrows_ = arrows;
        memset(row_used, 0, sizeof(row_used));
        memset(col_used, 0, sizeof(col_used));
        memset(box_used, 0, sizeof(box_used));
        for (int r = 0; r < N; r++)
            for (int c = 0; c < N; c++) {
                int v = board[r][c];
                if (v >= 1 && v <= N) place(r, c, v);
            }
    }

    bool has_unique_solution(double timeout_sec = 5.0) {
        solutions = 0;
        nodes_ = 0;
        use_deadline_ = (timeout_sec > 0);
        if (use_deadline_)
            deadline_ = chrono::steady_clock::now() + chrono::duration_cast<chrono::steady_clock::duration>(chrono::duration<double>(timeout_sec));
        solve_recursive(0);
        return solutions == 1;
    }
};

const double SOLVER_TIMEOUT_SEC = 5.0;

// ============================================================================
// Build puzzle: circle given, body empty; then dig other cells with uniqueness
// ============================================================================

static bool is_in_any_arrow(int r, int c, const vector<Arrow>& arrows) {
    for (const auto& ar : arrows) {
        if (ar.circle_r == r && ar.circle_c == c) return true;
        for (const auto& p : ar.body)
            if (p.first == r && p.second == c) return true;
    }
    return false;
}

static void create_puzzle(const int solution[N][N], const vector<Arrow>& arrows,
                          int puzzle[N][N], int difficulty) {
    memcpy(puzzle, solution, sizeof(int) * N * N);

    // Circle = given, body = empty
    for (const auto& ar : arrows) {
        puzzle[ar.circle_r][ar.circle_c] = solution[ar.circle_r][ar.circle_c];
        for (const auto& p : ar.body)
            puzzle[p.first][p.second] = 0;
    }

    int target_clues = DIFFICULTY_LEVELS[difficulty].target_clues;
    vector<int> indices;
    for (int i = 0; i < TOTAL_CELLS; i++) {
        int r = i / N, c = i % N;
        if (is_in_any_arrow(r, c, arrows)) continue;
        indices.push_back(i);
    }
    shuffle(indices.begin(), indices.end(), rng);

    ArrowSolver solver;
    int clues = 0;
    for (int r = 0; r < N; r++)
        for (int c = 0; c < N; c++)
            if (puzzle[r][c] != 0) clues++;

    for (int i : indices) {
        if (clues <= target_clues) break;
        int r = i / N, c = i % N;
        if (puzzle[r][c] == 0) continue;
        int backup = puzzle[r][c];
        puzzle[r][c] = 0;
        solver.load(puzzle, arrows);
        if (solver.has_unique_solution(SOLVER_TIMEOUT_SEC))
            clues--;
        else
            puzzle[r][c] = backup;
    }
}

// ============================================================================
// JSON output
// ============================================================================

static string board_to_json(const int b[N][N]) {
    string s = "[";
    for (int i = 0; i < N; i++) {
        s += "[";
        for (int j = 0; j < N; j++) {
            s += to_string(b[i][j]);
            if (j < N - 1) s += ",";
        }
        s += "]";
        if (i < N - 1) s += ",";
    }
    s += "]";
    return s;
}

static string arrows_to_json(const vector<Arrow>& arrows) {
    string s = "[";
    for (size_t i = 0; i < arrows.size(); i++) {
        const Arrow& ar = arrows[i];
        s += "{\"circle\": [" + to_string(ar.circle_r) + "," + to_string(ar.circle_c) + "], \"body\": [";
        for (size_t j = 0; j < ar.body.size(); j++) {
            s += "[" + to_string(ar.body[j].first) + "," + to_string(ar.body[j].second) + "]";
            if (j < ar.body.size() - 1) s += ",";
        }
        s += "]}";
        if (i < arrows.size() - 1) s += ",";
    }
    s += "]";
    return s;
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char* argv[]) {
    int count_per_level = 1;
    for (int i = 1; i < argc; i++) {
        if (string(argv[i]) == "--count" && i + 1 < argc) {
            count_per_level = stoi(argv[++i]);
        }
    }

    int num_levels = (int)DIFFICULTY_LEVELS.size();
    cout << "Arrow Sudoku (9x9 + arrows: circle = sum(body))" << endl;
    cout << "Generating " << count_per_level << " puzzles per level (" << num_levels << " levels)..." << endl;

    ofstream out(OUTPUT_FILE);
    out << "{\"puzzles\": [\n";
    int global_id = 1;
    bool first = true;

    for (const auto& kv : DIFFICULTY_LEVELS) {
        int level = kv.first;
        const Difficulty& info = kv.second;
        cout << "\n--- Level " << level << " (" << info.name << ", target " << info.target_clues << " clues) ---" << endl;

        for (int i = 0; i < count_per_level; i++) {
            auto start = chrono::high_resolution_clock::now();
            cout << "  #" << global_id << " " << flush;

            int solution[N][N];
            vector<Arrow> arrows;
            int attempts = 0;
            for (;;) {
                attempts++;
                generate_full_solution(solution);
                if (place_arrows(solution, level, arrows))
                    break;
            }

            int puzzle[N][N];
            create_puzzle(solution, arrows, puzzle, level);

            auto end = chrono::high_resolution_clock::now();
            chrono::duration<double> elapsed = end - start;

            if (!first) out << ",\n";
            first = false;
            out << "  {\n";
            out << "    \"id\": " << global_id << ",\n";
            out << "    \"difficulty\": " << level << ",\n";
            out << "    \"difficulty_name\": \"" << info.name << "\",\n";
            out << "    \"puzzle\": " << board_to_json(puzzle) << ",\n";
            out << "    \"solution\": " << board_to_json(solution) << ",\n";
            out << "    \"arrows\": " << arrows_to_json(arrows) << "\n";
            out << "  }";

            int clues = 0;
            for (int r = 0; r < N; r++)
                for (int c = 0; c < N; c++)
                    if (puzzle[r][c] != 0) clues++;
            cout << " clues=" << clues << " arrows=" << arrows.size() << " (" << fixed << setprecision(2) << elapsed.count() << "s)" << endl;
            global_id++;
        }
    }

    out << "\n]}\n";
    out.close();
    cout << "\nDone! Saved to " << OUTPUT_FILE << endl;
    return 0;
}
