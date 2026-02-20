import argparse
import json
import os
import random
import sys
import time

sys.setrecursionlimit(100000)

SIZE = 16
BOX = 4
TOTAL_CELLS = SIZE * SIZE
DIGITS = frozenset(range(1, SIZE + 1))
CELLS = [(r, c) for r in range(SIZE) for c in range(SIZE)]

DIFFICULTY_LEVELS = {
    1: {"name": "Beginner", "clues": 190},
    2: {"name": "Easy", "clues": 165},
    3: {"name": "Medium", "clues": 140},
    4: {"name": "Hard", "clues": 125},
    5: {"name": "Expert", "clues": 110},
}

OUTPUT_FILE = "sudoku_16.json"

# ---------------------------------------------------------------------------
# Precompute topology (peers / units) once at import time
# ---------------------------------------------------------------------------
_PEERS = {}
_UNITS = {}


def _init_topology():
    all_units = []
    for r in range(SIZE):
        all_units.append(tuple((r, c) for c in range(SIZE)))
    for c in range(SIZE):
        all_units.append(tuple((r, c) for r in range(SIZE)))
    for br in range(0, SIZE, BOX):
        for bc in range(0, SIZE, BOX):
            all_units.append(
                tuple((br + dr, bc + dc) for dr in range(BOX) for dc in range(BOX))
            )
    for cell in CELLS:
        _UNITS[cell] = [u for u in all_units if cell in u]
        peer_set = set()
        for u in _UNITS[cell]:
            peer_set.update(u)
        peer_set.discard(cell)
        _PEERS[cell] = frozenset(peer_set)


_init_topology()

# ---------------------------------------------------------------------------
# Constraint-propagation engine
# ---------------------------------------------------------------------------


def _eliminate(cands, cell, val):
    if val not in cands[cell]:
        return True
    cands[cell] = cands[cell] - {val}
    remaining = cands[cell]
    if not remaining:
        return False
    if len(remaining) == 1:
        sole = next(iter(remaining))
        for peer in _PEERS[cell]:
            if not _eliminate(cands, peer, sole):
                return False
    for unit in _UNITS[cell]:
        places = [c for c in unit if val in cands[c]]
        if not places:
            return False
        if len(places) == 1 and len(cands[places[0]]) > 1:
            if not _assign(cands, places[0], val):
                return False
    return True


def _assign(cands, cell, val):
    other = cands[cell] - {val}
    for v in other:
        if not _eliminate(cands, cell, v):
            return False
    return True


def _init_candidates(board):
    cands = {cell: set(DIGITS) for cell in CELLS}
    for r, c in CELLS:
        if board[r][c] != 0:
            if not _assign(cands, (r, c), board[r][c]):
                return None
    return cands


# ---------------------------------------------------------------------------
# Solver (counts solutions up to a limit)
# ---------------------------------------------------------------------------


def _solve(cands, solutions, limit):
    if cands is None or len(solutions) >= limit:
        return
    unsolved = [(cell, len(cands[cell])) for cell in CELLS if len(cands[cell]) > 1]
    if not unsolved:
        solutions.append(True)
        return
    cell, _ = min(unsolved, key=lambda x: x[1])
    for val in cands[cell]:
        if len(solutions) >= limit:
            return
        snap = {c: set(v) for c, v in cands.items()}
        if _assign(snap, cell, val):
            _solve(snap, solutions, limit)


def has_unique_solution(board):
    cands = _init_candidates(board)
    if cands is None:
        return False
    solutions = []
    _solve(cands, solutions, 2)
    return len(solutions) == 1


# ---------------------------------------------------------------------------
# Board generation (constraint propagation + randomised backtracking)
# ---------------------------------------------------------------------------


def _fill(cands):
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
        if _assign(snap, cell, val):
            result = _fill(snap)
            if result is not None:
                return result
    return None


def generate_full_board():
    cands = {cell: set(DIGITS) for cell in CELLS}
    return _fill(cands)


# ---------------------------------------------------------------------------
# Puzzle creation (remove cells while preserving unique solution)
# ---------------------------------------------------------------------------


def create_puzzle(solution, difficulty):
    target_clues = DIFFICULTY_LEVELS[difficulty]["clues"]
    cells_to_remove = TOTAL_CELLS - target_clues

    puzzle = [row[:] for row in solution]
    positions = list(CELLS)
    random.shuffle(positions)

    removed = 0
    for r, c in positions:
        if removed >= cells_to_remove:
            break
        if puzzle[r][c] == 0:
            continue
        backup = puzzle[r][c]
        puzzle[r][c] = 0
        if has_unique_solution(puzzle):
            removed += 1
        else:
            puzzle[r][c] = backup

    return puzzle


# ---------------------------------------------------------------------------
# Persistence helpers
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
        print(f"\n--- Level {level} ({info['name']}) - {info['clues']} clues ---")

        for _ in range(count_per_level):
            t0 = time.time()
            attempts = 0
            while True:
                attempts += 1
                solution = generate_full_board()
                puzzle = create_puzzle(solution, level)
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
    parser = argparse.ArgumentParser(description="Generate 16x16 Sudoku puzzles")
    parser.add_argument(
        "--count",
        type=int,
        required=True,
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
    print("(16x16 puzzles take longer to generate, especially at higher difficulty)\n")
    start = time.time()
    generate_puzzles(args.count)
    total_elapsed = time.time() - start
    print(f"Total time: {total_elapsed:.1f}s")


if __name__ == "__main__":
    main()
