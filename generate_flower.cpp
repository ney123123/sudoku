/*
 * generate_flower.cpp
 * Gattai-5 Cross (Flower Sudoku) Generator.
 * 15x15 board, 5 overlapping 9x9 grids in cross layout, 189 cells.
 * Output: grid with -1 = no cell, 0 = empty, 1-9 = value.
 *
 * Compile: g++ -std=c++17 -O3 -o generate_flower generate_flower.cpp
 * Run: ./generate_flower --count N
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

using namespace std;

// ============================================================================
// Constants & Layout (Gattai-5 Cross: 15x15, 189 cells)
// ============================================================================

const int ROWS = 15;
const int COLS = 15;
const int TOTAL = 189;
const int NUM_GRIDS = 5;
const int N = 9;

struct Difficulty {
    string name;
    int target_clues;
};

static map<int, Difficulty> DIFFICULTY_LEVELS = {
    {1, {"Beginner",     165}},
    {2, {"Easy",         145}},
    {3, {"Medium",       125}},
    {4, {"Hard",         105}},
    {5, {"Expert",        85}}
};

struct Slot { int g, lr, lc, lb; };
struct CellLayout {
    int n;
    Slot s[4];  // max 4 grids per cell (e.g. (6,5) in center+top+bottom+left)
};

static bool valid_cell[ROWS][COLS];
static int cell_r[TOTAL], cell_c[TOTAL];
static int fill_order[TOTAL];  // fill center 9x9 first, then rest
static CellLayout layout[TOTAL];

// Gattai-5 Cross: Center (3-11,3-11), Top (0-8,3-11), Bottom (6-14,3-11), Left (3-11,0-8), Right (3-11,6-14)
static void init_layout() {
    memset(valid_cell, 0, sizeof(valid_cell));
    // Top band: rows 0-2, cols 3-11
    for (int r = 0; r <= 2; r++)
        for (int c = 3; c <= 11; c++) valid_cell[r][c] = true;
    // Middle: rows 3-11, all cols 0-14 (no corners in this band)
    for (int r = 3; r <= 11; r++)
        for (int c = 0; c <= 14; c++) valid_cell[r][c] = true;
    // Bottom band: rows 12-14, cols 3-11
    for (int r = 12; r <= 14; r++)
        for (int c = 3; c <= 11; c++) valid_cell[r][c] = true;

    int idx = 0;
    for (int r = 0; r < ROWS; r++) {
        for (int c = 0; c < COLS; c++) {
            if (!valid_cell[r][c]) continue;
            cell_r[idx] = r;
            cell_c[idx] = c;
            layout[idx].n = 0;
            // Center (grid 0): (3-11, 3-11)
            if (r >= 3 && r <= 11 && c >= 3 && c <= 11) {
                int lr = r - 3, lc = c - 3;
                layout[idx].s[layout[idx].n++] = {0, lr, lc, (lr/3)*3 + lc/3};
            }
            // Top (grid 1): (0-8, 3-11)
            if (r >= 0 && r <= 8 && c >= 3 && c <= 11) {
                int lr = r, lc = c - 3;
                layout[idx].s[layout[idx].n++] = {1, lr, lc, (lr/3)*3 + lc/3};
            }
            // Bottom (grid 2): (6-14, 3-11)
            if (r >= 6 && r <= 14 && c >= 3 && c <= 11) {
                int lr = r - 6, lc = c - 3;
                layout[idx].s[layout[idx].n++] = {2, lr, lc, (lr/3)*3 + lc/3};
            }
            // Left (grid 3): (3-11, 0-8)
            if (r >= 3 && r <= 11 && c >= 0 && c <= 8) {
                int lr = r - 3, lc = c;
                layout[idx].s[layout[idx].n++] = {3, lr, lc, (lr/3)*3 + lc/3};
            }
            // Right (grid 4): (3-11, 6-14)
            if (r >= 3 && r <= 11 && c >= 6 && c <= 14) {
                int lr = r - 3, lc = c - 6;
                layout[idx].s[layout[idx].n++] = {4, lr, lc, (lr/3)*3 + lc/3};
            }
            idx++;
        }
    }
    if (idx != TOTAL) abort();

    // Fill order: center (3-11,3-11) first, then remaining cells (helps backtracking)
    int o = 0;
    for (int i = 0; i < TOTAL; i++) {
        int r = cell_r[i], c = cell_c[i];
        if (r >= 3 && r <= 11 && c >= 3 && c <= 11) fill_order[o++] = i;
    }
    for (int i = 0; i < TOTAL; i++) {
        int r = cell_r[i], c = cell_c[i];
        if (!(r >= 3 && r <= 11 && c >= 3 && c <= 11)) fill_order[o++] = i;
    }
    if (o != TOTAL) abort();
}

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

// ============================================================================
// Solver (solution count cap 2, optional timeout)
// ============================================================================

class FlowerSolver {
    int board[ROWS][COLS];
    int row_used[NUM_GRIDS][N];
    int col_used[NUM_GRIDS][N];
    int box_used[NUM_GRIDS][N];
    int solutions;
    chrono::steady_clock::time_point deadline_;
    bool use_deadline_;
    long long nodes_;

    bool can_place(int cell_idx, int digit) const {
        int bit = 1 << (digit - 1);
        const CellLayout& L = layout[cell_idx];
        for (int i = 0; i < L.n; i++) {
            int g = L.s[i].g, lr = L.s[i].lr, lc = L.s[i].lc, lb = L.s[i].lb;
            if (row_used[g][lr] & bit) return false;
            if (col_used[g][lc] & bit) return false;
            if (box_used[g][lb] & bit) return false;
        }
        return true;
    }

    void place(int cell_idx, int digit) {
        int bit = 1 << (digit - 1);
        const CellLayout& L = layout[cell_idx];
        for (int i = 0; i < L.n; i++) {
            int g = L.s[i].g, lr = L.s[i].lr, lc = L.s[i].lc, lb = L.s[i].lb;
            row_used[g][lr] |= bit;
            col_used[g][lc] |= bit;
            box_used[g][lb] |= bit;
        }
    }

    void unplace(int cell_idx, int digit) {
        int bit = 1 << (digit - 1);
        const CellLayout& L = layout[cell_idx];
        for (int i = 0; i < L.n; i++) {
            int g = L.s[i].g, lr = L.s[i].lr, lc = L.s[i].lc, lb = L.s[i].lb;
            row_used[g][lr] ^= bit;
            col_used[g][lc] ^= bit;
            box_used[g][lb] ^= bit;
        }
    }

    void solve_recursive(int cell_idx) {
        if (solutions >= 2) return;
        nodes_++;
        if (use_deadline_ && (nodes_ % 512 == 0) && chrono::steady_clock::now() >= deadline_) {
            solutions = 2;
            return;
        }

        while (cell_idx < TOTAL && board[cell_r[cell_idx]][cell_c[cell_idx]] != 0)
            cell_idx++;
        if (cell_idx >= TOTAL) {
            solutions++;
            return;
        }

        int r = cell_r[cell_idx], c = cell_c[cell_idx];
        for (int d = 1; d <= N; d++) {
            if (!can_place(cell_idx, d)) continue;
            board[r][c] = d;
            place(cell_idx, d);
            solve_recursive(cell_idx + 1);
            unplace(cell_idx, d);
            board[r][c] = 0;
            if (solutions >= 2) return;
        }
    }

public:
    FlowerSolver() { memset(board, 0, sizeof(board)); }

    void load(const int b[ROWS][COLS]) {
        for (int r = 0; r < ROWS; r++)
            for (int c = 0; c < COLS; c++) board[r][c] = b[r][c];
        memset(row_used, 0, sizeof(row_used));
        memset(col_used, 0, sizeof(col_used));
        memset(box_used, 0, sizeof(box_used));
        for (int i = 0; i < TOTAL; i++) {
            int r = cell_r[i], c = cell_c[i];
            int v = board[r][c];
            if (v >= 1 && v <= N) place(i, v);
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

// ============================================================================
// Full grid filler (backtracking, random digit order)
// ============================================================================

static int filler_board[ROWS][COLS];
static int filler_row[NUM_GRIDS][N], filler_col[NUM_GRIDS][N], filler_box[NUM_GRIDS][N];

static bool filler_can_place(int cell_idx, int digit) {
    int bit = 1 << (digit - 1);
    const CellLayout& L = layout[cell_idx];
    for (int i = 0; i < L.n; i++) {
        int g = L.s[i].g, lr = L.s[i].lr, lc = L.s[i].lc, lb = L.s[i].lb;
        if (filler_row[g][lr] & bit) return false;
        if (filler_col[g][lc] & bit) return false;
        if (filler_box[g][lb] & bit) return false;
    }
    return true;
}

static void filler_place(int cell_idx, int digit) {
    int bit = 1 << (digit - 1);
    int r = cell_r[cell_idx], c = cell_c[cell_idx];
    filler_board[r][c] = digit;
    const CellLayout& L = layout[cell_idx];
    for (int i = 0; i < L.n; i++) {
        int g = L.s[i].g, lr = L.s[i].lr, lc = L.s[i].lc, lb = L.s[i].lb;
        filler_row[g][lr] |= bit;
        filler_col[g][lc] |= bit;
        filler_box[g][lb] |= bit;
    }
}

static void filler_unplace(int cell_idx, int digit) {
    int bit = 1 << (digit - 1);
    int r = cell_r[cell_idx], c = cell_c[cell_idx];
    filler_board[r][c] = 0;
    const CellLayout& L = layout[cell_idx];
    for (int i = 0; i < L.n; i++) {
        int g = L.s[i].g, lr = L.s[i].lr, lc = L.s[i].lc, lb = L.s[i].lb;
        filler_row[g][lr] ^= bit;
        filler_col[g][lc] ^= bit;
        filler_box[g][lb] ^= bit;
    }
}

static bool fill_recursive(int pos) {
    if (pos >= TOTAL) return true;
    int cell_idx = fill_order[pos];
    vector<int> digits(N);
    iota(digits.begin(), digits.end(), 1);
    shuffle(digits.begin(), digits.end(), rng);
    for (int d : digits) {
        if (!filler_can_place(cell_idx, d)) continue;
        filler_place(cell_idx, d);
        if (fill_recursive(pos + 1)) return true;
        filler_unplace(cell_idx, d);
    }
    return false;
}

static void generate_full_solution(int out[ROWS][COLS]) {
    memset(filler_board, 0, sizeof(filler_board));
    for (int r = 0; r < ROWS; r++)
        for (int c = 0; c < COLS; c++)
            if (!valid_cell[r][c]) filler_board[r][c] = -1;
    memset(filler_row, 0, sizeof(filler_row));
    memset(filler_col, 0, sizeof(filler_col));
    memset(filler_box, 0, sizeof(filler_box));
    for (int attempt = 0; attempt < 50; attempt++) {
        if (attempt > 0) {
            int o = 0;
            for (int i = 0; i < TOTAL; i++)
                if (cell_r[i] >= 3 && cell_r[i] <= 11 && cell_c[i] >= 3 && cell_c[i] <= 11)
                    fill_order[o++] = i;
            for (int i = 0; i < TOTAL; i++)
                if (!(cell_r[i] >= 3 && cell_r[i] <= 11 && cell_c[i] >= 3 && cell_c[i] <= 11))
                    fill_order[o++] = i;
        }
        if (fill_recursive(0)) break;
        if (attempt == 49) {
            cerr << "Filler failed after 50 attempts.\n";
            abort();
        }
        memset(filler_board, 0, sizeof(filler_board));
        for (int r = 0; r < ROWS; r++)
            for (int c = 0; c < COLS; c++)
                if (!valid_cell[r][c]) filler_board[r][c] = -1;
        memset(filler_row, 0, sizeof(filler_row));
        memset(filler_col, 0, sizeof(filler_col));
        memset(filler_box, 0, sizeof(filler_box));
    }
    for (int r = 0; r < ROWS; r++)
        for (int c = 0; c < COLS; c++) out[r][c] = filler_board[r][c];
}

// ============================================================================
// Create puzzle (dig holes with uniqueness check)
// ============================================================================

const double SOLVER_TIMEOUT_SEC = 5.0;

static void create_puzzle(const int solution[ROWS][COLS],
                          int puzzle[ROWS][COLS],
                          int difficulty) {
    for (int r = 0; r < ROWS; r++)
        for (int c = 0; c < COLS; c++) puzzle[r][c] = solution[r][c];
    int target_clues = DIFFICULTY_LEVELS[difficulty].target_clues;

    vector<int> indices(TOTAL);
    iota(indices.begin(), indices.end(), 0);
    shuffle(indices.begin(), indices.end(), rng);

    FlowerSolver solver;
    int clues = TOTAL;
    for (int i : indices) {
        if (clues <= target_clues) break;
        int r = cell_r[i], c = cell_c[i];
        if (puzzle[r][c] == 0) continue;
        int backup = puzzle[r][c];
        puzzle[r][c] = 0;
        solver.load(puzzle);
        if (solver.has_unique_solution(SOLVER_TIMEOUT_SEC)) {
            clues--;
        } else {
            puzzle[r][c] = backup;
        }
    }
}

// ============================================================================
// JSON output (-1 = no cell, 0 = empty, 1-9 = value)
// ============================================================================

static string board_to_json(const int b[ROWS][COLS]) {
    string s = "[";
    for (int i = 0; i < ROWS; i++) {
        s += "[";
        for (int j = 0; j < COLS; j++) {
            s += to_string(b[i][j]);
            if (j < COLS - 1) s += ",";
        }
        s += "]";
        if (i < ROWS - 1) s += ",";
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

    init_layout();

    int num_levels = (int)DIFFICULTY_LEVELS.size();
    cout << "Gattai-5 Cross (Flower Sudoku): " << ROWS << "x" << COLS << ", " << TOTAL << " cells" << endl;
    cout << "Generating " << count_per_level << " puzzles per level (" << num_levels << " levels)..." << endl;

    ofstream out("sudoku_flower.json");
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
            int solution[ROWS][COLS];
            generate_full_solution(solution);
            int puzzle[ROWS][COLS];
            create_puzzle(solution, puzzle, level);
            auto end = chrono::high_resolution_clock::now();
            chrono::duration<double> elapsed = end - start;

            if (!first) out << ",\n";
            first = false;
            out << "  {\n";
            out << "    \"id\": " << global_id << ",\n";
            out << "    \"difficulty\": " << level << ",\n";
            out << "    \"difficulty_name\": \"" << info.name << "\",\n";
            out << "    \"puzzle\": " << board_to_json(puzzle) << ",\n";
            out << "    \"solution\": " << board_to_json(solution) << "\n";
            out << "  }";

            int clues = 0;
            for (int k = 0; k < TOTAL; k++)
                if (puzzle[cell_r[k]][cell_c[k]] != 0) clues++;
            cout << " clues=" << clues << " (" << fixed << setprecision(2) << elapsed.count() << "s)" << endl;
            global_id++;
        }
    }

    out << "\n]}\n";
    out.close();
    cout << "\nDone! Saved to sudoku_flower.json" << endl;
    return 0;
}
