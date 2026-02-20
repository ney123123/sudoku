import argparse
import json
import os
import random
import sys
import time
from collections import deque

sys.setrecursionlimit(200000)

SIZE = 16
TOTAL_CELLS = SIZE * SIZE
NUM_REGIONS = 16
REGION_SIZE = 16
DIGITS = frozenset(range(1, SIZE + 1))
CELLS = [(r, c) for r in range(SIZE) for c in range(SIZE)]

MAX_BBOX_DIM = 10
BOARD_GEN_TIMEOUT = 5.0
PUZZLE_TIMEOUT = 60.0

DIFFICULTY_LEVELS = {
    1: {"name": "Easy", "clues": 150},
    2: {"name": "Medium", "clues": 120},
    3: {"name": "Hard", "clues": 100},
}

OUTPUT_FILE = "sudoku_jigsaw_16.json"

# ---------------------------------------------------------------------------
# Precompute grid adjacency
# ---------------------------------------------------------------------------

_DIRS = [(-1, 0), (1, 0), (0, -1), (0, 1)]


def _cell_neighbors(r, c):
    out = []
    for dr, dc in _DIRS:
        nr, nc = r + dr, c + dc
        if 0 <= nr < SIZE and 0 <= nc < SIZE:
            out.append((nr, nc))
    return tuple(out)


_NBR = {cell: _cell_neighbors(*cell) for cell in CELLS}

# ---------------------------------------------------------------------------
# Region generation (random growth + compactness bias + anti-snake)
# ---------------------------------------------------------------------------


def _is_connected(cells):
    if len(cells) <= 1:
        return True
    cells_set = set(cells)
    start = next(iter(cells_set))
    visited = {start}
    queue = deque([start])
    while queue:
        cell = queue.popleft()
        for nb in _NBR[cell]:
            if nb in cells_set and nb not in visited:
                visited.add(nb)
                queue.append(nb)
    return len(visited) == len(cells_set)


def _region_compact(cells):
    rows = [r for r, _ in cells]
    cols = [c for _, c in cells]
    return (max(rows) - min(rows) + 1) <= MAX_BBOX_DIM and \
           (max(cols) - min(cols) + 1) <= MAX_BBOX_DIM


def generate_regions(max_retries=500):
    for _ in range(max_retries):
        result = _try_generate_regions()
        if result is not None:
            return result
    return None


def _collect_region_cells(region_map):
    rc = [[] for _ in range(NUM_REGIONS)]
    for r in range(SIZE):
        for c in range(SIZE):
            rc[region_map[r][c]].append((r, c))
    return rc


def _same_region_nbs(r, c, rid, region_map):
    """Neighbors of (r,c) that belong to the same region."""
    return [(nr, nc) for nr, nc in _NBR[(r, c)]
            if region_map[nr][nc] == rid]


def _removal_keeps_connected(r, c, rid, region_map):
    """Would removing (r,c) from region rid keep it connected?"""
    same = _same_region_nbs(r, c, rid, region_map)
    if len(same) <= 1:
        return True
    visited = {same[0]}
    q = deque([same[0]])
    targets = set(same[1:])
    while q and targets:
        cur = q.popleft()
        for nb in _NBR[cur]:
            if nb not in visited and region_map[nb[0]][nb[1]] == rid \
                    and nb != (r, c):
                visited.add(nb)
                q.append(nb)
                targets.discard(nb)
    return not targets


def _try_generate_regions():
    """Start from regular 4x4 boxes, then randomize borders.  Each
    perturbation moves one cell A→B then compensates with a different
    cell B→A, preserving region sizes and connectivity."""
    region_map = [[0] * SIZE for _ in range(SIZE)]
    for r in range(SIZE):
        for c in range(SIZE):
            region_map[r][c] = (r // 4) * 4 + (c // 4)

    num_attempts = TOTAL_CELLS * 8
    swaps_done = 0
    for _ in range(num_attempts):
        r1 = random.randint(0, SIZE - 1)
        c1 = random.randint(0, SIZE - 1)
        rid_a = region_map[r1][c1]

        diff_nbs = [(nr, nc) for nr, nc in _NBR[(r1, c1)]
                    if region_map[nr][nc] != rid_a]
        if not diff_nbs:
            continue
        nr, nc = random.choice(diff_nbs)
        rid_b = region_map[nr][nc]

        if not _removal_keeps_connected(r1, c1, rid_a, region_map):
            continue

        region_map[r1][c1] = rid_b

        if not _is_connected(
            [(r, c) for r, c in CELLS if region_map[r][c] == rid_a]
        ):
            region_map[r1][c1] = rid_a
            continue

        candidates = []
        for r2 in range(SIZE):
            for c2 in range(SIZE):
                if region_map[r2][c2] != rid_b or (r2, c2) == (r1, c1):
                    continue
                has_a_nb = any(region_map[xr][xc] == rid_a
                               for xr, xc in _NBR[(r2, c2)])
                if not has_a_nb:
                    continue
                candidates.append((r2, c2))

        random.shuffle(candidates)
        compensated = False
        for r2, c2 in candidates:
            if not _removal_keeps_connected(r2, c2, rid_b, region_map):
                continue
            region_map[r2][c2] = rid_a
            rc_a = [(r, c) for r, c in CELLS if region_map[r][c] == rid_a]
            if not _is_connected(rc_a) or not _region_compact(rc_a):
                region_map[r2][c2] = rid_b
                continue
            rc_b = [(r, c) for r, c in CELLS if region_map[r][c] == rid_b]
            if not _is_connected(rc_b) or not _region_compact(rc_b):
                region_map[r2][c2] = rid_b
                continue
            compensated = True
            break

        if not compensated:
            region_map[r1][c1] = rid_a
            continue

        swaps_done += 1

    return region_map if swaps_done > 0 else None


# ---------------------------------------------------------------------------
# Dynamic topology (rebuilt per puzzle because regions differ)
# ---------------------------------------------------------------------------


def build_topology(region_map):
    all_units = []
    for r in range(SIZE):
        all_units.append(tuple((r, c) for c in range(SIZE)))
    for c in range(SIZE):
        all_units.append(tuple((r, c) for r in range(SIZE)))
    rcells = {}
    for r in range(SIZE):
        for c in range(SIZE):
            rcells.setdefault(region_map[r][c], []).append((r, c))
    for rid in sorted(rcells):
        all_units.append(tuple(rcells[rid]))

    units = {}
    peers = {}
    for cell in CELLS:
        units[cell] = [u for u in all_units if cell in u]
        ps = set()
        for u in units[cell]:
            ps.update(u)
        ps.discard(cell)
        peers[cell] = frozenset(ps)
    return units, peers


# ---------------------------------------------------------------------------
# Constraint-propagation engine (with embedded timeout)
# ---------------------------------------------------------------------------


class _Timeout(Exception):
    pass


_deadline = float("inf")
_elim_counter = 0


def _eliminate(cands, cell, val, units, peers):
    global _elim_counter
    _elim_counter += 1
    if _elim_counter % 2000 == 0 and time.time() > _deadline:
        raise _Timeout
    if val not in cands[cell]:
        return True
    cands[cell] = cands[cell] - {val}
    rem = cands[cell]
    if not rem:
        return False
    if len(rem) == 1:
        sole = next(iter(rem))
        for p in peers[cell]:
            if not _eliminate(cands, p, sole, units, peers):
                return False
    for unit in units[cell]:
        places = [c for c in unit if val in cands[c]]
        if not places:
            return False
        if len(places) == 1 and len(cands[places[0]]) > 1:
            if not _assign(cands, places[0], val, units, peers):
                return False
    return True


def _assign(cands, cell, val, units, peers):
    for v in cands[cell] - {val}:
        if not _eliminate(cands, cell, v, units, peers):
            return False
    return True


def _init_candidates(board, units, peers):
    cands = {cell: set(DIGITS) for cell in CELLS}
    for r, c in CELLS:
        if board[r][c] != 0:
            if not _assign(cands, (r, c), board[r][c], units, peers):
                return None
    return cands


# ---------------------------------------------------------------------------
# Solver
# ---------------------------------------------------------------------------


def _solve(cands, solutions, limit, units, peers):
    if cands is None or len(solutions) >= limit:
        return
    if time.time() > _deadline:
        raise _Timeout
    unsolved = [(cell, len(cands[cell])) for cell in CELLS if len(cands[cell]) > 1]
    if not unsolved:
        solutions.append(True)
        return
    cell, _ = min(unsolved, key=lambda x: x[1])
    for val in cands[cell]:
        if len(solutions) >= limit:
            return
        snap = {c: set(v) for c, v in cands.items()}
        if _assign(snap, cell, val, units, peers):
            _solve(snap, solutions, limit, units, peers)


def has_unique_solution(board, units, peers):
    cands = _init_candidates(board, units, peers)
    if cands is None:
        return False
    solutions = []
    _solve(cands, solutions, 2, units, peers)
    return len(solutions) == 1


# ---------------------------------------------------------------------------
# Full board generation
# ---------------------------------------------------------------------------


def _fill(cands, units, peers):
    unsolved = [(cell, len(cands[cell])) for cell in CELLS if len(cands[cell]) > 1]
    if not unsolved:
        board = [[0] * SIZE for _ in range(SIZE)]
        for (r, c), vals in cands.items():
            board[r][c] = next(iter(vals))
        return board
    cell, _ = min(unsolved, key=lambda x: x[1])
    vals = list(cands[cell])
    random.shuffle(vals)
    for val in vals:
        snap = {c: set(v) for c, v in cands.items()}
        if _assign(snap, cell, val, units, peers):
            result = _fill(snap, units, peers)
            if result is not None:
                return result
    return None


def generate_full_board(units, peers):
    cands = {cell: set(DIGITS) for cell in CELLS}
    return _fill(cands, units, peers)


# ---------------------------------------------------------------------------
# Puzzle creation
# ---------------------------------------------------------------------------


def _cp_fully_solves(puzzle, units, peers):
    """Return True if constraint propagation alone resolves every cell."""
    cands = _init_candidates(puzzle, units, peers)
    if cands is None:
        return False
    return all(len(cands[cell]) == 1 for cell in CELLS)


def create_puzzle(solution, difficulty, units, peers):
    target_clues = DIFFICULTY_LEVELS[difficulty]["clues"]
    to_remove = TOTAL_CELLS - target_clues
    puzzle = [row[:] for row in solution]
    positions = list(CELLS)
    random.shuffle(positions)
    removed = 0

    for r, c in positions:
        if removed >= to_remove:
            break
        if puzzle[r][c] == 0:
            continue
        backup = puzzle[r][c]
        puzzle[r][c] = 0

        if _cp_fully_solves(puzzle, units, peers):
            removed += 1
            continue

        if difficulty >= 2:
            try:
                if has_unique_solution(puzzle, units, peers):
                    removed += 1
                    continue
            except _Timeout:
                pass

        puzzle[r][c] = backup
    return puzzle


# ---------------------------------------------------------------------------
# Persistence
# ---------------------------------------------------------------------------


def board_to_key(board):
    return tuple(tuple(row) for row in board)


def load_existing(filepath):
    if not os.path.exists(filepath):
        return {"puzzles": []}
    with open(filepath, "r", encoding="utf-8") as f:
        return json.load(f)


def save_puzzles(data, filepath):
    with open(filepath, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)


def get_existing_keys(data):
    return {board_to_key(e["puzzle"]) for e in data["puzzles"]}


# ---------------------------------------------------------------------------
# Main loop
# ---------------------------------------------------------------------------


def generate_puzzles(count_per_level):
    global _deadline
    data = load_existing(OUTPUT_FILE)
    existing_keys = get_existing_keys(data)
    next_id = max((p["id"] for p in data["puzzles"]), default=0) + 1
    total = count_per_level * len(DIFFICULTY_LEVELS)
    generated = 0

    for level in sorted(DIFFICULTY_LEVELS.keys()):
        info = DIFFICULTY_LEVELS[level]
        print(f"\n--- Level {level} ({info['name']}) - {info['clues']} clues ---")

        for _ in range(count_per_level):
            t0 = time.time()
            attempts = 0
            while True:
                attempts += 1
                if attempts % 5 == 0:
                    print(f"  (attempt {attempts}...)", flush=True)
                region_map = generate_regions()
                if region_map is None:
                    continue
                units, peers = build_topology(region_map)
                _deadline = time.time() + BOARD_GEN_TIMEOUT
                try:
                    solution = generate_full_board(units, peers)
                except _Timeout:
                    continue
                finally:
                    _deadline = float("inf")
                if solution is None:
                    continue
                _deadline = time.time() + PUZZLE_TIMEOUT
                try:
                    puzzle = create_puzzle(solution, level, units, peers)
                except _Timeout:
                    continue
                finally:
                    _deadline = float("inf")
                key = board_to_key(puzzle)
                if key not in existing_keys:
                    existing_keys.add(key)
                    break

            entry = {
                "id": next_id,
                "difficulty": level,
                "difficulty_name": info["name"],
                "regions": region_map,
                "puzzle": puzzle,
                "solution": solution,
            }
            data["puzzles"].append(entry)
            next_id += 1
            generated += 1
            elapsed = time.time() - t0
            print(f"  [{generated}/{total}] Generated puzzle #{entry['id']} ({elapsed:.1f}s)")

    save_puzzles(data, OUTPUT_FILE)
    print(f"\nDone! {generated} puzzles saved to {OUTPUT_FILE}")
    print(f"Total puzzles in file: {len(data['puzzles'])}")


def main():
    parser = argparse.ArgumentParser(
        description="Generate 16x16 Jigsaw Sudoku puzzles")
    parser.add_argument(
        "--count", type=int, required=True,
        help="Number of puzzles to generate per difficulty level",
    )
    args = parser.parse_args()
    if args.count < 1:
        print("Error: --count must be at least 1")
        sys.exit(1)

    print(
        f"Generating {args.count} puzzle(s) per level x {len(DIFFICULTY_LEVELS)} levels "
        f"= {args.count * len(DIFFICULTY_LEVELS)} total"
    )
    print("(16x16 Jigsaw puzzles are slow to generate - please be patient)\n")
    start = time.time()
    generate_puzzles(args.count)
    print(f"Total time: {time.time() - start:.1f}s")


if __name__ == "__main__":
    main()
