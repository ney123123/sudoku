/*
 * generate_samurai.cpp
 * Samurai Sudoku Generator: 4x4 (8x8, 64 cells) or 9x9 (21x21, 369 cells) mode.
 * Output: grid with -1 = no cell, 0 = empty, 1-N = value.
 *
 * Compile: g++ -std=c++17 -O3 -o generate_samurai generate_samurai.cpp
 * Run: ./generate_samurai --size 9 --count N   (default size 9)
 *      ./generate_samurai --size 4 --count N
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
// Constants & Layout (max dimensions; actual size set at runtime by --size)
// ============================================================================

const int MAX_ROWS = 21;
const int MAX_COLS = 21;
const int MAX_CELLS = 369;
const int NUM_GRIDS = 5;
const int MAX_N = 9;

struct Difficulty {
    string name;
    int target_clues;
};

// N=9: 7 levels, 369 cells
static map<int, Difficulty> DIFFICULTY_9 = {
    {1, {"Beginner",     320}},
    {2, {"Easy",         300}},
    {3, {"Medium",       280}},
    {4, {"Intermediate", 260}},
    {5, {"Hard",         240}},
    {6, {"Expert",       220}},
    {7, {"Evil",         200}}
};

// N=4: 3 levels, 64 cells
static map<int, Difficulty> DIFFICULTY_4 = {
    {1, {"Easy",   55}},
    {2, {"Medium", 50}},
    {3, {"Hard",   45}}
};

struct Slot { int g, lr, lc, lb; };
struct CellLayout {
    int n;
    Slot s[2];
};

// Runtime size (set in main from --size 4 or 9)
static int g_N = 9;
static int g_ROWS = 21;
static int g_COLS = 21;
static int g_TOTAL = 369;
static const char* g_OUTPUT = "sudoku_samurai.json";
static map<int, Difficulty>* g_DIFFICULTY = &DIFFICULTY_9;

static bool valid_cell[MAX_ROWS][MAX_COLS];
static int cell_r[MAX_CELLS], cell_c[MAX_CELLS];
static CellLayout layout[MAX_CELLS];

static void init_layout_9() {
    memset(valid_cell, 0, sizeof(valid_cell));
    for (int r = 0; r <= 8; r++)
        for (int c = 0; c <= 8; c++) valid_cell[r][c] = true;
    for (int r = 0; r <= 8; r++)
        for (int c = 12; c <= 20; c++) valid_cell[r][c] = true;
    for (int r = 6; r <= 14; r++)
        for (int c = 6; c <= 14; c++) valid_cell[r][c] = true;
    for (int r = 12; r <= 20; r++)
        for (int c = 0; c <= 8; c++) valid_cell[r][c] = true;
    for (int r = 12; r <= 20; r++)
        for (int c = 12; c <= 20; c++) valid_cell[r][c] = true;

    int idx = 0;
    for (int r = 0; r < g_ROWS; r++) {
        for (int c = 0; c < g_COLS; c++) {
            if (!valid_cell[r][c]) continue;
            cell_r[idx] = r;
            cell_c[idx] = c;
            layout[idx].n = 0;
            if (r >= 0 && r <= 8 && c >= 0 && c <= 8) {
                layout[idx].s[layout[idx].n++] = {0, r, c, (r/3)*3 + c/3};
            }
            if (r >= 0 && r <= 8 && c >= 12 && c <= 20) {
                layout[idx].s[layout[idx].n++] = {1, r, c-12, (r/3)*3 + (c-12)/3};
            }
            if (r >= 6 && r <= 14 && c >= 6 && c <= 14) {
                layout[idx].s[layout[idx].n++] = {2, r-6, c-6, ((r-6)/3)*3 + (c-6)/3};
            }
            if (r >= 12 && r <= 20 && c >= 0 && c <= 8) {
                layout[idx].s[layout[idx].n++] = {3, r-12, c, ((r-12)/3)*3 + c/3};
            }
            if (r >= 12 && r <= 20 && c >= 12 && c <= 20) {
                layout[idx].s[layout[idx].n++] = {4, r-12, c-12, ((r-12)/3)*3 + (c-12)/3};
            }
            idx++;
        }
    }
    if (idx != g_TOTAL) abort();
}

// 4x4 Samurai: 8x8 grid, 64 cells, 5 grids with 2x2 overlaps
static void init_layout_4() {
    memset(valid_cell, 0, sizeof(valid_cell));
    for (int r = 0; r < 8; r++)
        for (int c = 0; c < 8; c++) valid_cell[r][c] = true;

    int idx = 0;
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            cell_r[idx] = r;
            cell_c[idx] = c;
            layout[idx].n = 0;
            // Grid 0: top-left (0-3, 0-3)
            if (r >= 0 && r <= 3 && c >= 0 && c <= 3) {
                layout[idx].s[layout[idx].n++] = {0, r, c, (r/2)*2 + c/2};
            }
            // Grid 1: top-right (0-3, 4-7)
            if (r >= 0 && r <= 3 && c >= 4 && c <= 7) {
                layout[idx].s[layout[idx].n++] = {1, r, c-4, (r/2)*2 + (c-4)/2};
            }
            // Grid 2: center (2-5, 2-5)
            if (r >= 2 && r <= 5 && c >= 2 && c <= 5) {
                layout[idx].s[layout[idx].n++] = {2, r-2, c-2, ((r-2)/2)*2 + (c-2)/2};
            }
            // Grid 3: bottom-left (4-7, 0-3)
            if (r >= 4 && r <= 7 && c >= 0 && c <= 3) {
                layout[idx].s[layout[idx].n++] = {3, r-4, c, ((r-4)/2)*2 + c/2};
            }
            // Grid 4: bottom-right (4-7, 4-7)
            if (r >= 4 && r <= 7 && c >= 4 && c <= 7) {
                layout[idx].s[layout[idx].n++] = {4, r-4, c-4, ((r-4)/2)*2 + (c-4)/2};
            }
            idx++;
        }
    }
    if (idx != 64) abort();
}

static void init_layout() {
    if (g_N == 9) init_layout_9();
    else init_layout_4();
}

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

// ============================================================================
// Samurai Solver (solution count cap 2, optional timeout)
// ============================================================================

class SamuraiSolver {
    int board[MAX_ROWS][MAX_COLS];
    int row_used[NUM_GRIDS][MAX_N];
    int col_used[NUM_GRIDS][MAX_N];
    int box_used[NUM_GRIDS][MAX_N];
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

        while (cell_idx < g_TOTAL && board[cell_r[cell_idx]][cell_c[cell_idx]] != 0)
            cell_idx++;
        if (cell_idx >= g_TOTAL) {
            solutions++;
            return;
        }

        int r = cell_r[cell_idx], c = cell_c[cell_idx];
        for (int d = 1; d <= g_N; d++) {
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
    SamuraiSolver() { memset(board, 0, sizeof(board)); }

    void load(const int b[MAX_ROWS][MAX_COLS]) {
        for (int r = 0; r < g_ROWS; r++)
            for (int c = 0; c < g_COLS; c++) board[r][c] = b[r][c];
        memset(row_used, 0, sizeof(row_used));
        memset(col_used, 0, sizeof(col_used));
        memset(box_used, 0, sizeof(box_used));
        for (int i = 0; i < g_TOTAL; i++) {
            int r = cell_r[i], c = cell_c[i];
            int v = board[r][c];
            if (v >= 1 && v <= g_N) place(i, v);
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

    int solution_count(double timeout_sec = 5.0) {
        solutions = 0;
        nodes_ = 0;
        use_deadline_ = (timeout_sec > 0);
        if (use_deadline_)
            deadline_ = chrono::steady_clock::now() + chrono::duration_cast<chrono::steady_clock::duration>(chrono::duration<double>(timeout_sec));
        solve_recursive(0);
        return solutions;
    }
};

// ============================================================================
// Full grid filler (backtracking, random digit order)
// ============================================================================

static int filler_board[MAX_ROWS][MAX_COLS];
static int filler_row[NUM_GRIDS][MAX_N], filler_col[NUM_GRIDS][MAX_N], filler_box[NUM_GRIDS][MAX_N];

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

static bool fill_recursive(int cell_idx) {
    if (cell_idx >= g_TOTAL) return true;
    int r = cell_r[cell_idx], c = cell_c[cell_idx];
    vector<int> digits(g_N);
    iota(digits.begin(), digits.end(), 1);
    shuffle(digits.begin(), digits.end(), rng);
    for (int d : digits) {
        if (!filler_can_place(cell_idx, d)) continue;
        filler_place(cell_idx, d);
        if (fill_recursive(cell_idx + 1)) return true;
        filler_unplace(cell_idx, d);
    }
    return false;
}

static void generate_full_solution(int out[MAX_ROWS][MAX_COLS]) {
    memset(filler_board, 0, sizeof(filler_board));
    for (int r = 0; r < g_ROWS; r++)
        for (int c = 0; c < g_COLS; c++)
            if (!valid_cell[r][c]) filler_board[r][c] = -1;
    memset(filler_row, 0, sizeof(filler_row));
    memset(filler_col, 0, sizeof(filler_col));
    memset(filler_box, 0, sizeof(filler_box));
    fill_recursive(0);
    for (int r = 0; r < g_ROWS; r++)
        for (int c = 0; c < g_COLS; c++) out[r][c] = filler_board[r][c];
}

// ============================================================================
// Create puzzle (dig holes with uniqueness check)
// ============================================================================

const double SOLVER_TIMEOUT_SEC = 5.0;

static void create_puzzle(const int solution[MAX_ROWS][MAX_COLS],
                          int puzzle[MAX_ROWS][MAX_COLS],
                          int difficulty) {
    for (int r = 0; r < g_ROWS; r++)
        for (int c = 0; c < g_COLS; c++) puzzle[r][c] = solution[r][c];
    int target_clues = (*g_DIFFICULTY)[difficulty].target_clues;

    vector<int> indices(g_TOTAL);
    iota(indices.begin(), indices.end(), 0);
    shuffle(indices.begin(), indices.end(), rng);

    SamuraiSolver solver;
    int clues = g_TOTAL;
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
// JSON output (-1 = no cell, 0 = empty, 1-N = value)
// ============================================================================

static string board_to_json(const int b[MAX_ROWS][MAX_COLS]) {
    string s = "[";
    for (int i = 0; i < g_ROWS; i++) {
        s += "[";
        for (int j = 0; j < g_COLS; j++) {
            s += to_string(b[i][j]);
            if (j < g_COLS - 1) s += ",";
        }
        s += "]";
        if (i < g_ROWS - 1) s += ",";
    }
    s += "]";
    return s;
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char* argv[]) {
    int count_per_level = 1;
    int size = 9;
    for (int i = 1; i < argc; i++) {
        if (string(argv[i]) == "--count" && i + 1 < argc) {
            count_per_level = stoi(argv[++i]);
        } else if (string(argv[i]) == "--size" && i + 1 < argc) {
            size = stoi(argv[++i]);
        }
    }
    if (size != 4 && size != 9) {
        cout << "Usage: ./generate_samurai [--size 4|9] [--count N]" << endl;
        cout << "  --size 4: 4x4 Samurai (8x8 grid, 64 cells), 3 difficulty levels" << endl;
        cout << "  --size 9: 9x9 Samurai (21x21 grid, 369 cells), 7 difficulty levels (default)" << endl;
        return 1;
    }

    g_N = size;
    if (g_N == 4) {
        g_ROWS = 8;
        g_COLS = 8;
        g_TOTAL = 64;
        g_OUTPUT = "sudoku_samurai_4.json";
        g_DIFFICULTY = &DIFFICULTY_4;
    } else {
        g_ROWS = 21;
        g_COLS = 21;
        g_TOTAL = 369;
        g_OUTPUT = "sudoku_samurai.json";
        g_DIFFICULTY = &DIFFICULTY_9;
    }

    init_layout();

    int num_levels = (int)g_DIFFICULTY->size();
    cout << "Samurai " << g_N << "x" << g_N << " (" << g_ROWS << "x" << g_COLS << ", " << g_TOTAL << " cells)" << endl;
    cout << "Generating " << count_per_level << " puzzles per level (" << num_levels << " levels)..." << endl;

    ofstream out(g_OUTPUT);
    out << "{\"puzzles\": [\n";
    int global_id = 1;
    bool first = true;

    for (const auto& kv : *g_DIFFICULTY) {
        int level = kv.first;
        const Difficulty& info = kv.second;
        cout << "\n--- Level " << level << " (" << info.name << ", target " << info.target_clues << " clues) ---" << endl;

        for (int i = 0; i < count_per_level; i++) {
            auto start = chrono::high_resolution_clock::now();
            cout << "  #" << global_id << " " << flush;
            int solution[MAX_ROWS][MAX_COLS];
            generate_full_solution(solution);
            int puzzle[MAX_ROWS][MAX_COLS];
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
            for (int k = 0; k < g_TOTAL; k++)
                if (puzzle[cell_r[k]][cell_c[k]] != 0) clues++;
            cout << " clues=" << clues << " (" << fixed << setprecision(2) << elapsed.count() << "s)" << endl;
            global_id++;
        }
    }

    out << "\n]}\n";
    out.close();
    cout << "\nDone! Saved to " << g_OUTPUT << endl;
    return 0;
}
