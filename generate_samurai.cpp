/*
 * generate_samurai.cpp
 * Samurai Sudoku Generator (5 overlapping 9x9 grids, 369 cells)
 * Output: 21x21 grid; -1 = no cell, 0 = empty, 1-9 = value.
 *
 * Compile: g++ -std=c++17 -O3 -o generate_samurai generate_samurai.cpp
 * Run: ./generate_samurai --count N
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
// Constants & Layout
// ============================================================================

const int SAMURAI_ROWS = 21;
const int SAMURAI_COLS = 21;
const int TOTAL_CELLS = 369;
const int N = 9;
const int NUM_GRIDS = 5;
const char* OUTPUT_FILE = "sudoku_samurai.json";

struct Difficulty {
    string name;
    int target_clues;
};

// 7 difficulty levels (target clue count out of 369)
map<int, Difficulty> DIFFICULTY_LEVELS = {
    {1, {"Beginner",     320}},
    {2, {"Easy",         300}},
    {3, {"Medium",       280}},
    {4, {"Intermediate", 260}},
    {5, {"Hard",         240}},
    {6, {"Expert",       220}},
    {7, {"Evil",         200}}
};

// For each of 369 cells: which grid(s) it belongs to and local row/col/box per grid
struct Slot { int g, lr, lc, lb; };
struct CellLayout {
    int n;
    Slot s[2];
};

static bool valid_cell[SAMURAI_ROWS][SAMURAI_COLS];
static int cell_r[TOTAL_CELLS], cell_c[TOTAL_CELLS];
static CellLayout layout[TOTAL_CELLS];

static void init_layout() {
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
    for (int r = 0; r < SAMURAI_ROWS; r++) {
        for (int c = 0; c < SAMURAI_COLS; c++) {
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
    if (idx != TOTAL_CELLS) abort();
}

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

// ============================================================================
// Samurai Solver (solution count cap 2, optional timeout)
// ============================================================================

class SamuraiSolver {
    int board[SAMURAI_ROWS][SAMURAI_COLS];
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

        while (cell_idx < TOTAL_CELLS && board[cell_r[cell_idx]][cell_c[cell_idx]] != 0)
            cell_idx++;
        if (cell_idx >= TOTAL_CELLS) {
            solutions++;
            return;
        }

        int r = cell_r[cell_idx], c = cell_c[cell_idx];
        for (int d = 1; d <= 9; d++) {
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

    void load(const int b[SAMURAI_ROWS][SAMURAI_COLS]) {
        memcpy(board, b, sizeof(board));
        memset(row_used, 0, sizeof(row_used));
        memset(col_used, 0, sizeof(col_used));
        memset(box_used, 0, sizeof(box_used));
        for (int i = 0; i < TOTAL_CELLS; i++) {
            int r = cell_r[i], c = cell_c[i];
            int v = board[r][c];
            if (v >= 1 && v <= 9) place(i, v);
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

static int filler_board[SAMURAI_ROWS][SAMURAI_COLS];
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

static bool fill_recursive(int cell_idx) {
    if (cell_idx >= TOTAL_CELLS) return true;
    int r = cell_r[cell_idx], c = cell_c[cell_idx];
    vector<int> digits(9);
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

static void generate_full_solution(int out[SAMURAI_ROWS][SAMURAI_COLS]) {
    memset(filler_board, 0, sizeof(filler_board));
    for (int r = 0; r < SAMURAI_ROWS; r++)
        for (int c = 0; c < SAMURAI_COLS; c++)
            if (!valid_cell[r][c]) filler_board[r][c] = -1;
    memset(filler_row, 0, sizeof(filler_row));
    memset(filler_col, 0, sizeof(filler_col));
    memset(filler_box, 0, sizeof(filler_box));
    fill_recursive(0);
    memcpy(out, filler_board, sizeof(filler_board));
}

// ============================================================================
// Create puzzle (dig holes with uniqueness check)
// ============================================================================

const double SOLVER_TIMEOUT_SEC = 5.0;

static void create_puzzle(const int solution[SAMURAI_ROWS][SAMURAI_COLS],
                          int puzzle[SAMURAI_ROWS][SAMURAI_COLS],
                          int difficulty) {
    memcpy(puzzle, solution, sizeof(int) * SAMURAI_ROWS * SAMURAI_COLS);
    int target_clues = DIFFICULTY_LEVELS[difficulty].target_clues;

    vector<int> indices(TOTAL_CELLS);
    iota(indices.begin(), indices.end(), 0);
    shuffle(indices.begin(), indices.end(), rng);

    SamuraiSolver solver;
    int clues = TOTAL_CELLS;
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
// JSON output (21x21: -1 = no cell, 0 = empty, 1-9 = value)
// ============================================================================

static string board_to_json(const int b[SAMURAI_ROWS][SAMURAI_COLS]) {
    string s = "[";
    for (int i = 0; i < SAMURAI_ROWS; i++) {
        s += "[";
        for (int j = 0; j < SAMURAI_COLS; j++) {
            s += to_string(b[i][j]);
            if (j < SAMURAI_COLS - 1) s += ",";
        }
        s += "]";
        if (i < SAMURAI_ROWS - 1) s += ",";
    }
    s += "]";
    return s;
}

// ============================================================================
// Main
// ============================================================================

int main(int argc, char* argv[]) {
    int count_per_level = 1;
    if (argc == 3 && string(argv[1]) == "--count") {
        count_per_level = stoi(argv[2]);
    } else {
        cout << "Usage: ./generate_samurai --count N" << endl;
        return 1;
    }

    init_layout();

    cout << "Generating " << count_per_level << " puzzles per level (7 levels)..." << endl;

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
            int solution[SAMURAI_ROWS][SAMURAI_COLS];
            generate_full_solution(solution);
            int puzzle[SAMURAI_ROWS][SAMURAI_COLS];
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
            for (int k = 0; k < TOTAL_CELLS; k++)
                if (puzzle[cell_r[k]][cell_c[k]] != 0) clues++;
            cout << " clues=" << clues << " (" << fixed << setprecision(2) << elapsed.count() << "s)" << endl;
            global_id++;
        }
    }

    out << "\n]}\n";
    out.close();
    cout << "\nDone! Saved to " << OUTPUT_FILE << endl;
    return 0;
}
