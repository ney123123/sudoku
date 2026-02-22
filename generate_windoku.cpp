/*
 * generate_windoku.cpp
 * Windoku (Four Windows) Sudoku Generator
 * 9x9 grid + 4 extra 3x3 window regions that must each contain 1-9.
 * Windows: (1-3,1-3), (1-3,5-7), (5-7,1-3), (5-7,5-7) in 0-based indexing.
 *
 * Compile: g++ -std=c++17 -O3 -o generate_windoku generate_windoku.cpp
 * Run: ./generate_windoku --count N
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

const int N = 9;
const int TOTAL_CELLS = 81;
const int NUM_WINDOWS = 4;
const char* OUTPUT_FILE = "sudoku_windoku.json";

struct Difficulty {
    string name;
    int target_clues;
};

map<int, Difficulty> DIFFICULTY_LEVELS = {
    {1, {"Beginner",     51}},
    {2, {"Easy",         45}},
    {3, {"Medium",       35}},
    {4, {"Intermediate", 30}},
    {5, {"Hard",         25}},
    {6, {"Expert",       20}},
    {7, {"Evil",         15}}
};

mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());

// Return window index 0-3, or -1 if (r,c) is not in any window
inline int get_window(int r, int c) {
    if (r >= 1 && r <= 3 && c >= 1 && c <= 3) return 0;
    if (r >= 1 && r <= 3 && c >= 5 && c <= 7) return 1;
    if (r >= 5 && r <= 7 && c >= 1 && c <= 3) return 2;
    if (r >= 5 && r <= 7 && c >= 5 && c <= 7) return 3;
    return -1;
}

inline int get_box(int r, int c) {
    return (r / 3) * 3 + (c / 3);
}

// ============================================================================
// Windoku Solver (solution count cap 2, optional timeout)
// ============================================================================

class WindokuSolver {
    int board[N][N];
    int row_used[N], col_used[N], box_used[N], window_used[NUM_WINDOWS];
    int solutions;
    chrono::steady_clock::time_point deadline_;
    bool use_deadline_;
    long long nodes_;

    bool can_place(int r, int c, int digit) const {
        int bit = 1 << (digit - 1);
        if (row_used[r] & bit) return false;
        if (col_used[c] & bit) return false;
        if (box_used[get_box(r, c)] & bit) return false;
        int w = get_window(r, c);
        if (w >= 0 && (window_used[w] & bit)) return false;
        return true;
    }

    void place(int r, int c, int digit) {
        int bit = 1 << (digit - 1);
        row_used[r] |= bit;
        col_used[c] |= bit;
        box_used[get_box(r, c)] |= bit;
        int w = get_window(r, c);
        if (w >= 0) window_used[w] |= bit;
    }

    void unplace(int r, int c, int digit) {
        int bit = 1 << (digit - 1);
        row_used[r] ^= bit;
        col_used[c] ^= bit;
        box_used[get_box(r, c)] ^= bit;
        int w = get_window(r, c);
        if (w >= 0) window_used[w] ^= bit;
    }

    void solve_recursive(int pos) {
        if (solutions >= 2) return;
        nodes_++;
        if (use_deadline_ && (nodes_ % 512 == 0) && chrono::steady_clock::now() >= deadline_) {
            solutions = 2;
            return;
        }
        if (pos >= TOTAL_CELLS) {
            solutions++;
            return;
        }
        int r = pos / N, c = pos % N;
        if (board[r][c] != 0) {
            solve_recursive(pos + 1);
            return;
        }
        for (int d = 1; d <= N; d++) {
            if (!can_place(r, c, d)) continue;
            board[r][c] = d;
            place(r, c, d);
            solve_recursive(pos + 1);
            unplace(r, c, d);
            board[r][c] = 0;
            if (solutions >= 2) return;
        }
    }

public:
    WindokuSolver() { memset(board, 0, sizeof(board)); }

    void load(const int b[N][N]) {
        memcpy(board, b, sizeof(board));
        memset(row_used, 0, sizeof(row_used));
        memset(col_used, 0, sizeof(col_used));
        memset(box_used, 0, sizeof(box_used));
        memset(window_used, 0, sizeof(window_used));
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

// ============================================================================
// Full grid filler (backtracking, random digit order)
// ============================================================================

static int filler_board[N][N];
static int filler_row[N], filler_col[N], filler_box[N], filler_window[NUM_WINDOWS];

static bool filler_can_place(int r, int c, int digit) {
    int bit = 1 << (digit - 1);
    if (filler_row[r] & bit) return false;
    if (filler_col[c] & bit) return false;
    if (filler_box[get_box(r, c)] & bit) return false;
    int w = get_window(r, c);
    if (w >= 0 && (filler_window[w] & bit)) return false;
    return true;
}

static void filler_place(int r, int c, int digit) {
    int bit = 1 << (digit - 1);
    filler_board[r][c] = digit;
    filler_row[r] |= bit;
    filler_col[c] |= bit;
    filler_box[get_box(r, c)] |= bit;
    int w = get_window(r, c);
    if (w >= 0) filler_window[w] |= bit;
}

static void filler_unplace(int r, int c, int digit) {
    int bit = 1 << (digit - 1);
    filler_board[r][c] = 0;
    filler_row[r] ^= bit;
    filler_col[c] ^= bit;
    filler_box[get_box(r, c)] ^= bit;
    int w = get_window(r, c);
    if (w >= 0) filler_window[w] ^= bit;
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
    memset(filler_window, 0, sizeof(filler_window));
    fill_recursive(0);
    memcpy(out, filler_board, sizeof(filler_board));
}

// ============================================================================
// Create puzzle (dig holes with uniqueness check)
// ============================================================================

const double SOLVER_TIMEOUT_SEC = 5.0;

static void create_puzzle(const int solution[N][N], int puzzle[N][N], int difficulty) {
    memcpy(puzzle, solution, sizeof(int) * N * N);
    int target_clues = DIFFICULTY_LEVELS[difficulty].target_clues;

    vector<int> indices(TOTAL_CELLS);
    iota(indices.begin(), indices.end(), 0);
    shuffle(indices.begin(), indices.end(), rng);

    WindokuSolver solver;
    int clues = TOTAL_CELLS;
    for (int i : indices) {
        if (clues <= target_clues) break;
        int r = i / N, c = i % N;
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
    cout << "Windoku (9x9 + 4 windows)" << endl;
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
            generate_full_solution(solution);
            int puzzle[N][N];
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
            for (int r = 0; r < N; r++)
                for (int c = 0; c < N; c++)
                    if (puzzle[r][c] != 0) clues++;
            cout << " clues=" << clues << " (" << fixed << setprecision(2) << elapsed.count() << "s)" << endl;
            global_id++;
        }
    }

    out << "\n]}\n";
    out.close();
    cout << "\nDone! Saved to " << OUTPUT_FILE << endl;
    return 0;
}
