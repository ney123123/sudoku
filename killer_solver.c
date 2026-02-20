/*
 * Fast Killer Sudoku uniqueness checker.
 * Reads cage definitions from stdin, outputs solution count (capped at 2).
 *
 * Input format (one line each):
 *   NUM_CAGES
 *   For each cage: SIZE SUM CELL0 CELL1 ... (cells are 0-80, row-major)
 *
 * Output: "0", "1", or "2" (number of solutions found, max 2).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define N 9
#define TOTAL 81

static int num_cages;
static int cage_size[TOTAL];
static int cage_sum[TOTAL];
static int cage_cells[TOTAL][N];
static int cell_cage[TOTAL];

static int cell_allowed[TOTAL];      /* bitmask from cage combos */
static int row_used[N], col_used[N], box_used[N];
static int cage_used[TOTAL], cage_partial[TOTAL], cage_unfilled[TOTAL];
static int assigned[TOTAL];

static int solutions;
static int order[TOTAL];

/* popcount for small ints */
static inline int popcnt(int x) {
    int c = 0;
    while (x) { c++; x &= x - 1; }
    return c;
}

static void solve(void) {
    if (solutions >= 2) return;

    /* dynamic MRV: find best unassigned cell */
    int best = -1, best_cnt = 100;
    for (int i = 0; i < TOTAL; i++) {
        if (assigned[i]) continue;
        int r = i / N, c = i % N, bx = (r / 3) * 3 + c / 3;
        int ci = cell_cage[i];
        int avail = cell_allowed[i]
                  & ~(row_used[r] | col_used[c] | box_used[bx] | cage_used[ci]);
        int cnt = popcnt(avail);
        if (cnt == 0) return;       /* dead end */
        if (cnt < best_cnt) {
            best_cnt = cnt;
            best = i;
            if (cnt == 1) break;
        }
    }

    if (best < 0) { solutions++; return; }

    int i = best;
    int r = i / N, c = i % N, bx = (r / 3) * 3 + c / 3;
    int ci = cell_cage[i];
    int avail = cell_allowed[i]
              & ~(row_used[r] | col_used[c] | box_used[bx] | cage_used[ci]);

    assigned[i] = 1;
    while (avail) {
        int bit = avail & (-avail);
        avail ^= bit;
        int digit = __builtin_ctz(bit);     /* bit position = digit value */

        int np = cage_partial[ci] + digit;
        int nu = cage_unfilled[ci] - 1;
        if (np > cage_sum[ci]) continue;
        if (nu == 0) { if (np != cage_sum[ci]) continue; }
        else {
            int rem = cage_sum[ci] - np;
            if (rem < nu) continue;
        }

        row_used[r] |= bit;
        col_used[c] |= bit;
        box_used[bx] |= bit;
        cage_used[ci] |= bit;
        cage_partial[ci] = np;
        cage_unfilled[ci] = nu;

        solve();

        row_used[r] ^= bit;
        col_used[c] ^= bit;
        box_used[bx] ^= bit;
        cage_used[ci] ^= bit;
        cage_partial[ci] -= digit;
        cage_unfilled[ci]++;

        if (solutions >= 2) break;
    }
    assigned[i] = 0;
}

static int compute_allowed(void) {
    memset(cell_allowed, 0, sizeof(cell_allowed));
    memset(cell_cage, 0, sizeof(cell_cage));

    for (int ci = 0; ci < num_cages; ci++) {
        int sz = cage_size[ci], sm = cage_sum[ci];
        int mask_union = 0;

        if (sz == 1) {
            if (sm >= 1 && sm <= 9) mask_union = 1 << sm;
        } else {
            int start = (1 << sz) - 1;
            for (int s = start; s < (1 << 10); ) {
                if ((s & 1) == 0 && popcnt(s) == sz) {
                    int sum = 0, tmp = s;
                    while (tmp) {
                        int b = tmp & (-tmp);
                        sum += __builtin_ctz(b);
                        tmp ^= b;
                    }
                    if (sum == sm) mask_union |= s;
                }
                int c2 = s & (-s);
                int r2 = s + c2;
                s = (((r2 ^ s) >> 2) / c2) | r2;
            }
        }

        if (mask_union == 0) return 0;

        for (int j = 0; j < sz; j++) {
            cell_allowed[cage_cells[ci][j]] |= mask_union;
            cell_cage[cage_cells[ci][j]] = ci;
        }
    }
    return 1;
}

int main(void) {
    /* Persistent mode: read queries until EOF */
    while (scanf("%d", &num_cages) == 1) {
        for (int ci = 0; ci < num_cages; ci++) {
            scanf("%d %d", &cage_size[ci], &cage_sum[ci]);
            cage_unfilled[ci] = cage_size[ci];
            cage_partial[ci] = 0;
            cage_used[ci] = 0;
            for (int j = 0; j < cage_size[ci]; j++) {
                int cell;
                scanf("%d", &cell);
                cage_cells[ci][j] = cell;
            }
        }

        if (!compute_allowed()) {
            printf("0\n");
            fflush(stdout);
            continue;
        }

        memset(row_used, 0, sizeof(row_used));
        memset(col_used, 0, sizeof(col_used));
        memset(box_used, 0, sizeof(box_used));
        memset(assigned, 0, sizeof(assigned));
        solutions = 0;

        solve();
        printf("%d\n", solutions);
        fflush(stdout);
    }
    return 0;
}
