import argparse
import json
import os
import random
import sys
import time
from collections import deque

sys.setrecursionlimit(100000)

SIZE = 9
TOTAL_CELLS = SIZE * SIZE
NUM_REGIONS = 9
REGION_SIZE = 9
DIGITS = frozenset(range(1, SIZE + 1))
CELLS = [(r, c) for r in range(SIZE) for c in range(SIZE)]

MAX_BBOX_DIM = 6

DIFFICULTY_LEVELS = {
    1: {"name": "Beginner", "clues": 40},
    2: {"name": "Easy", "clues": 34},
    3: {"name": "Medium", "clues": 28},
    4: {"name": "Hard", "clues": 24},
    5: {"name": "Expert", "clues": 22},
}

OUTPUT_FILE = "sudoku_jigsaw.json"

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
# Region generation  (random growth + compactness bias + anti-snake)
# ---------------------------------------------------------------------------


def _centroid(cells):
    n = len(cells)
    return sum(r for r, _ in cells) / n, sum(c for _, c in cells) / n


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


def _weighted_pick(valid, cells):
    cr, cc = _centroid(cells)
    weights = [1.0 / (1.0 + abs(r - cr) + abs(c - cc)) for r, c in valid]
    total_w = sum(weights)
    pick = random.random() * total_w
    cumul = 0.0
    for cell, w in zip(valid, weights):
        cumul += w
        if cumul >= pick:
            return cell
    return valid[-1]


def generate_regions(max_retries=2000):
    for _ in range(max_retries):
        result = _try_generate_regions()
        if result is not None:
            return result
    return None


def _try_generate_regions():
    region_map = [[-1] * SIZE for _ in range(SIZE)]
    region_cells = [[] for _ in range(NUM_REGIONS)]
    unassigned = set(CELLS)

    centers = [(1, 1), (1, 4), (1, 7),
               (4, 1), (4, 4), (4, 7),
               (7, 1), (7, 4), (7, 7)]
    jitter = [(-1, 0), (1, 0), (0, -1), (0, 1), (0, 0)]
    seeds = []
    for cr, cc in centers:
        dr, dc = random.choice(jitter)
        seeds.append((max(0, min(8, cr + dr)), max(0, min(8, cc + dc))))
    random.shuffle(seeds)

    frontiers = [set() for _ in range(NUM_REGIONS)]
    for rid, cell in enumerate(seeds):
        region_map[cell[0]][cell[1]] = rid
        region_cells[rid].append(cell)
        unassigned.discard(cell)
        for nb in _NBR[cell]:
            if nb in unassigned:
                frontiers[rid].add(nb)

    while unassigned:
        growable = []
        for rid in range(NUM_REGIONS):
            if len(region_cells[rid]) >= REGION_SIZE:
                continue
            frontiers[rid] &= unassigned
            if frontiers[rid]:
                growable.append(rid)

        if not growable:
            return None

        min_size = min(len(region_cells[i]) for i in growable)
        smallest = [i for i in growable if len(region_cells[i]) == min_size]
        rid = random.choice(smallest)
        chosen = _weighted_pick(list(frontiers[rid]), region_cells[rid])

        region_map[chosen[0]][chosen[1]] = rid
        region_cells[rid].append(chosen)
        unassigned.discard(chosen)
        frontiers[rid].discard(chosen)
        for nb in _NBR[chosen]:
            if nb in unassigned:
                frontiers[rid].add(nb)

    for rid in range(NUM_REGIONS):
        if len(region_cells[rid]) != REGION_SIZE:
            return None
        if not _is_connected(region_cells[rid]):
            return None
        if not _region_compact(region_cells[rid]):
            return None
    return region_map


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
# Constraint-propagation engine
# ---------------------------------------------------------------------------


_elim_counter = 0


def _eliminate(cands, cell, val, units, peers):
    global _elim_counter
    _elim_counter += 1
    if _elim_counter % 500 == 0 and time.time() > _deadline:
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


_deadline = float("inf")


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


PUZZLE_TIMEOUT = 5.0


class _Timeout(Exception):
    pass


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
        if has_unique_solution(puzzle, units, peers):
            removed += 1
        else:
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
                region_map = generate_regions()
                if region_map is None:
                    continue
                units, peers = build_topology(region_map)
                _deadline = time.time() + PUZZLE_TIMEOUT
                try:
                    solution = generate_full_board(units, peers)
                    if solution is None:
                        continue
                    puzzle = create_puzzle(solution, level, units, peers)
                except _Timeout:
                    continue
                finally:
                    _deadline = float("inf")
                key = board_to_key(puzzle)
                if key not in existing_keys:
                    existing_keys.add(key)
                    break
                if attempts > 100:
                    print(f"  Warning: {attempts} attempts to avoid duplicate")

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
    parser = argparse.ArgumentParser(description="Generate Jigsaw Sudoku puzzles")
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
    start = time.time()
    generate_puzzles(args.count)
    print(f"Total time: {time.time() - start:.1f}s")


if __name__ == "__main__":
    main()
