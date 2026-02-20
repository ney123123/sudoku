import argparse
import json
import os
import random
import sys
import time
from itertools import combinations

sys.setrecursionlimit(50000)

SIZE = 9
TOTAL_CELLS = SIZE * SIZE
DIGITS = frozenset(range(1, SIZE + 1))
CELLS = [(r, c) for r in range(SIZE) for c in range(SIZE)]

DIFFICULTY_LEVELS = {
    1: {"name": "Beginner", "min_cage": 2, "max_cage": 4, "target_avg": 2.7},
    2: {"name": "Easy",     "min_cage": 3, "max_cage": 5, "target_avg": 3.3},
    3: {"name": "Medium",   "min_cage": 3, "max_cage": 5, "target_avg": 3.8},
    4: {"name": "Hard",     "min_cage": 3, "max_cage": 5, "target_avg": 4.3},
    5: {"name": "Expert",   "min_cage": 4, "max_cage": 6, "target_avg": 5.0},
}

OUTPUT_FILE = "sudoku_killer.json"


# ---------------------------------------------------------------------------
# Precompute valid digit combinations: COMBOS[(n, s)] -> list of frozensets
# For cage of size n with target sum s, all subsets of {1..9} that work.
# ---------------------------------------------------------------------------

COMBOS = {}


def _precompute_combos():
    for n in range(1, 10):
        for combo in combinations(range(1, 10), n):
            s = sum(combo)
            COMBOS.setdefault((n, s), []).append(frozenset(combo))


_precompute_combos()

# ---------------------------------------------------------------------------
# Grid adjacency
# ---------------------------------------------------------------------------

_DIRS = [(-1, 0), (1, 0), (0, -1), (0, 1)]


def _cell_neighbors(r, c):
    out = []
    for dr, dc in _DIRS:
        nr, nc = r + dr, c + dc
        if 0 <= nr < SIZE and 0 <= nc < SIZE:
            out.append((nr, nc))
    return out


_NBR = {cell: _cell_neighbors(*cell) for cell in CELLS}

# ---------------------------------------------------------------------------
# Standard topology (rows, cols, 3x3 boxes) -- fixed for all puzzles
# ---------------------------------------------------------------------------

_ALL_UNITS = []
for _r in range(SIZE):
    _ALL_UNITS.append(tuple(((_r, _c) for _c in range(SIZE))))
for _c in range(SIZE):
    _ALL_UNITS.append(tuple(((_r, _c) for _r in range(SIZE))))
for _br in range(0, SIZE, 3):
    for _bc in range(0, SIZE, 3):
        _ALL_UNITS.append(
            tuple((_br + dr, _bc + dc) for dr in range(3) for dc in range(3))
        )

_UNITS = {}
_PEERS = {}
for _cell in CELLS:
    _UNITS[_cell] = [u for u in _ALL_UNITS if _cell in u]
    _ps = set()
    for _u in _UNITS[_cell]:
        _ps.update(_u)
    _ps.discard(_cell)
    _PEERS[_cell] = frozenset(_ps)

# ---------------------------------------------------------------------------
# Board generation (backtracking, ported from generate.py)
# ---------------------------------------------------------------------------


def _is_valid(board, row, col, num):
    if num in board[row]:
        return False
    if any(board[r][col] == num for r in range(SIZE)):
        return False
    br, bc = 3 * (row // 3), 3 * (col // 3)
    for r in range(br, br + 3):
        for c in range(bc, bc + 3):
            if board[r][c] == num:
                return False
    return True


def generate_full_board():
    board = [[0] * SIZE for _ in range(SIZE)]

    def fill(pos):
        if pos == TOTAL_CELLS:
            return True
        row, col = divmod(pos, SIZE)
        nums = list(range(1, SIZE + 1))
        random.shuffle(nums)
        for num in nums:
            if _is_valid(board, row, col, num):
                board[row][col] = num
                if fill(pos + 1):
                    return True
                board[row][col] = 0
        return False

    fill(0)
    return board


# ---------------------------------------------------------------------------
# Cage generation (Union-Find random merge)
# ---------------------------------------------------------------------------



def _cell_index(r, c):
    return r * SIZE + c




def generate_cages(solution, difficulty):
    """Build cages by starting from 81 singletons and iteratively merging
    adjacent cages while preserving unique solvability."""
    info = DIFFICULTY_LEVELS[difficulty]
    min_cage = info["min_cage"]
    max_cage = info["max_cage"]
    target_avg = info["target_avg"]
    target_count = max(int(round(TOTAL_CELLS / target_avg)), 9)

    cage_of = list(range(TOTAL_CELLS))
    cage_members = {i: {i} for i in range(TOTAL_CELLS)}

    edges = []
    for r, c in CELLS:
        idx = _cell_index(r, c)
        for nr, nc in _NBR[(r, c)]:
            nidx = _cell_index(nr, nc)
            if idx < nidx:
                edges.append((idx, nidx))

    def _merge(ca, cb):
        if len(cage_members[ca]) < len(cage_members[cb]):
            ca, cb = cb, ca
        for idx in cage_members[cb]:
            cage_of[idx] = ca
        cage_members[ca] |= cage_members[cb]
        old_cb = cage_members.pop(cb)
        return ca, cb, old_cb

    def _undo_merge(ca, cb, old_cb):
        for idx in old_cb:
            cage_of[idx] = cb
        cage_members[ca] -= old_cb
        cage_members[cb] = old_cb

    def _to_cage_list():
        cages = []
        for cid in sorted(cage_members.keys()):
            cells = []
            cage_sum = 0
            for idx in sorted(cage_members[cid]):
                r, c = divmod(idx, SIZE)
                cells.append([r, c])
                cage_sum += solution[r][c]
            cages.append({"cells": cells, "sum": cage_sum})
        return cages

    # Merge iteratively, prioritizing smaller cages
    for _round in range(10):
        # Sort edges by combined size of cages they connect
        edges.sort(key=lambda x: len(cage_members[cage_of[x[0]]]) + len(cage_members[cage_of[x[1]]]) + random.random())
        
        if len(cage_members) <= target_count:
            break
            
        progress = False
        batch = []
        batch_size = 3
        
        for a, b in edges:
            if len(cage_members) <= target_count:
                break
            ca, cb = cage_of[a], cage_of[b]
            if ca == cb:
                continue
            if len(cage_members[ca]) + len(cage_members[cb]) > max_cage:
                continue

            merged_ca, merged_cb, old_cb = _merge(ca, cb)
            batch.append((merged_ca, merged_cb, old_cb))
            
            if len(batch) >= batch_size:
                if has_unique_solution(_to_cage_list()):
                    progress = True
                    batch = []
                else:
                    # Batch failed, undo all
                    for m_ca, m_cb, m_old in reversed(batch):
                        _undo_merge(m_ca, m_cb, m_old)
                    batch = []
        
        # Process remaining batch
        if batch:
            if has_unique_solution(_to_cage_list()):
                progress = True
            else:
                for m_ca, m_cb, m_old in reversed(batch):
                    _undo_merge(m_ca, m_cb, m_old)
        
        # print(f"Round {_round}: {len(cage_members)} cages", flush=True)
        if not progress:
            break

    # Phase 2: force-merge undersized cages
    changed = True
    while changed:
        changed = False
        for cid in list(cage_members.keys()):
            if cid not in cage_members:
                continue
            if len(cage_members[cid]) >= min_cage:
                continue
            merged = False
            for member_idx in list(cage_members[cid]):
                mr, mc = divmod(member_idx, SIZE)
                for nr, nc in _NBR[(mr, mc)]:
                    nidx = _cell_index(nr, nc)
                    ncid = cage_of[nidx]
                    if ncid == cid:
                        continue
                    if len(cage_members[cid]) + len(cage_members[ncid]) \
                            > max_cage:
                        continue
                    m_ca, m_cb, m_old = _merge(cid, ncid)
                    if has_unique_solution(_to_cage_list()):
                        changed = True
                        merged = True
                        break
                    else:
                        _undo_merge(m_ca, m_cb, m_old)
                if merged:
                    break

    # Validate: all cages must meet size constraints
    for cid, members in cage_members.items():
        if len(members) < min_cage or len(members) > max_cage:
            return None
    return _to_cage_list()


# ---------------------------------------------------------------------------
# Killer Sudoku solver (constraint propagation + backtracking)
# ---------------------------------------------------------------------------



def _build_cage_index(cages):
    """Map each cell to its cage index, and build cage data structures."""
    cell_to_cage = {}
    cage_cells = []
    cage_sums = []
    for ci, cage in enumerate(cages):
        cells = [tuple(c) for c in cage["cells"]]
        cage_cells.append(cells)
        cage_sums.append(cage["sum"])
        for cell in cells:
            cell_to_cage[cell] = ci
    return cell_to_cage, cage_cells, cage_sums



_SOLVER_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "killer_solver")

import subprocess


class _SolverProcess:
    """Persistent C solver process for fast uniqueness checks."""

    def __init__(self):
        self._proc = None

    def _ensure(self):
        if self._proc is None or self._proc.poll() is not None:
            self._proc = subprocess.Popen(
                [_SOLVER_PATH],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                text=True,
                bufsize=1,
            )

    def check(self, cages):
        self._ensure()
        lines = [str(len(cages))]
        for cage in cages:
            cells = cage["cells"]
            cell_indices = " ".join(str(c[0] * SIZE + c[1]) for c in cells)
            lines.append(f"{len(cells)} {cage['sum']} {cell_indices}")
        self._proc.stdin.write("\n".join(lines) + "\n")
        self._proc.stdin.flush()
        result = self._proc.stdout.readline().strip()
        return result == "1"

    def close(self):
        if self._proc and self._proc.poll() is None:
            self._proc.stdin.close()
            self._proc.wait()


_solver = _SolverProcess()


def has_unique_solution(cages):
    """Check uniqueness via persistent compiled C solver."""
    return _solver.check(cages)


# ---------------------------------------------------------------------------
# Persistence
# ---------------------------------------------------------------------------


def cages_to_key(cages):
    parts = []
    for cage in cages:
        cells_tuple = tuple(tuple(c) for c in sorted(cage["cells"]))
        parts.append((cells_tuple, cage["sum"]))
    return tuple(sorted(parts))


def load_existing(filepath):
    if not os.path.exists(filepath):
        return {"puzzles": []}
    with open(filepath, "r", encoding="utf-8") as f:
        return json.load(f)


def save_puzzles(data, filepath):
    with open(filepath, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)


def get_existing_keys(data):
    keys = set()
    for entry in data["puzzles"]:
        keys.add(cages_to_key(entry["cages"]))
    return keys


# ---------------------------------------------------------------------------
# Main generation loop
# ---------------------------------------------------------------------------


def generate_puzzles(count_per_level):
    data = load_existing(OUTPUT_FILE)
    existing_keys = get_existing_keys(data)
    next_id = max((p["id"] for p in data["puzzles"]), default=0) + 1
    total = count_per_level * len(DIFFICULTY_LEVELS)
    generated = 0

    for level in sorted(DIFFICULTY_LEVELS.keys()):
        info = DIFFICULTY_LEVELS[level]
        print(f"\n--- Level {level} ({info['name']}) ---")

        for _ in range(count_per_level):
            t0 = time.time()
            attempts = 0
            while True:
                attempts += 1
                if attempts % 5 == 0:
                    print(f"  (attempt {attempts}...)", flush=True)

                solution = generate_full_board()
                cages = generate_cages(solution, level)
                if cages is None:
                    continue

                key = cages_to_key(cages)
                if key not in existing_keys:
                    existing_keys.add(key)
                    break

            entry = {
                "id": next_id,
                "difficulty": level,
                "difficulty_name": info["name"],
                "cages": cages,
                "solution": solution,
            }
            data["puzzles"].append(entry)
            next_id += 1
            generated += 1
            elapsed = time.time() - t0
            n_cages = len(cages)
            avg_sz = TOTAL_CELLS / n_cages
            print(f"  [{generated}/{total}] #{entry['id']} "
                  f"({n_cages} cages, avg {avg_sz:.1f}, "
                  f"{elapsed:.1f}s, {attempts} attempts)")

    save_puzzles(data, OUTPUT_FILE)
    print(f"\nDone! {generated} puzzles saved to {OUTPUT_FILE}")
    print(f"Total puzzles in file: {len(data['puzzles'])}")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(
        description="Generate Killer Sudoku puzzles")
    parser.add_argument(
        "--count", type=int, required=True,
        help="Number of puzzles to generate per difficulty level",
    )
    args = parser.parse_args()
    if args.count < 1:
        print("Error: --count must be at least 1")
        sys.exit(1)

    print(
        f"Generating {args.count} puzzle(s) per level x "
        f"{len(DIFFICULTY_LEVELS)} levels "
        f"= {args.count * len(DIFFICULTY_LEVELS)} total"
    )
    start = time.time()
    generate_puzzles(args.count)
    print(f"Total time: {time.time() - start:.1f}s")


if __name__ == "__main__":
    main()
