import argparse
import copy
import json
import os
import random
import sys
import time

DIFFICULTY_LEVELS = {
    1: {"name": "Beginner", "clues": 45},
    2: {"name": "Easy", "clues": 40},
    3: {"name": "Medium", "clues": 33},
    4: {"name": "Intermediate", "clues": 28},
    5: {"name": "Hard", "clues": 25},
    6: {"name": "Expert", "clues": 23},
    7: {"name": "Evil", "clues": 20},
}

OUTPUT_FILE = "sudoku.json"


def is_valid(board, row, col, num):
    if num in board[row]:
        return False
    if any(board[r][col] == num for r in range(9)):
        return False
    box_r, box_c = 3 * (row // 3), 3 * (col // 3)
    for r in range(box_r, box_r + 3):
        for c in range(box_c, box_c + 3):
            if board[r][c] == num:
                return False
    return True


def generate_full_board():
    board = [[0] * 9 for _ in range(9)]

    def fill(pos):
        if pos == 81:
            return True
        row, col = divmod(pos, 9)
        nums = list(range(1, 10))
        random.shuffle(nums)
        for num in nums:
            if is_valid(board, row, col, num):
                board[row][col] = num
                if fill(pos + 1):
                    return True
                board[row][col] = 0
        return False

    fill(0)
    return board


def count_solutions(board, limit=2):
    """Count solutions up to `limit`. Returns as soon as limit is reached."""
    count = [0]

    def solve(pos):
        if count[0] >= limit:
            return
        if pos == 81:
            count[0] += 1
            return
        row, col = divmod(pos, 9)
        if board[row][col] != 0:
            solve(pos + 1)
            return
        for num in range(1, 10):
            if is_valid(board, row, col, num):
                board[row][col] = num
                solve(pos + 1)
                board[row][col] = 0
                if count[0] >= limit:
                    return

    solve(0)
    return count[0]


def has_unique_solution(board):
    test_board = copy.deepcopy(board)
    return count_solutions(test_board, limit=2) == 1


def create_puzzle(solution, difficulty):
    target_clues = DIFFICULTY_LEVELS[difficulty]["clues"]
    cells_to_remove = 81 - target_clues

    puzzle = copy.deepcopy(solution)
    positions = [(r, c) for r in range(9) for c in range(9)]
    random.shuffle(positions)

    removed = 0
    for row, col in positions:
        if removed >= cells_to_remove:
            break
        if puzzle[row][col] == 0:
            continue
        backup = puzzle[row][col]
        puzzle[row][col] = 0
        if has_unique_solution(puzzle):
            removed += 1
        else:
            puzzle[row][col] = backup

    return puzzle


def board_to_key(board):
    return tuple(tuple(row) for row in board)


def load_existing_puzzles(filepath):
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
        keys.add(board_to_key(entry["puzzle"]))
    return keys


def generate_puzzles(count_per_level):
    data = load_existing_puzzles(OUTPUT_FILE)
    existing_keys = get_existing_keys(data)
    next_id = max((p["id"] for p in data["puzzles"]), default=0) + 1

    total = count_per_level * len(DIFFICULTY_LEVELS)
    generated = 0

    for level in sorted(DIFFICULTY_LEVELS.keys()):
        info = DIFFICULTY_LEVELS[level]
        print(f"\n--- Level {level} ({info['name']}) - {info['clues']} clues ---")

        for i in range(count_per_level):
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
                    print(f"  Warning: took {attempts} attempts to avoid duplicate")

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
            print(f"  [{generated}/{total}] Generated puzzle #{entry['id']}")

    save_puzzles(data, OUTPUT_FILE)
    print(f"\nDone! {generated} puzzles saved to {OUTPUT_FILE}")
    print(f"Total puzzles in file: {len(data['puzzles'])}")


def main():
    parser = argparse.ArgumentParser(description="Generate Sudoku puzzles")
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

    print(f"Generating {args.count} puzzle(s) per level x {len(DIFFICULTY_LEVELS)} levels "
          f"= {args.count * len(DIFFICULTY_LEVELS)} total")
    start = time.time()
    generate_puzzles(args.count)
    elapsed = time.time() - start
    print(f"Time elapsed: {elapsed:.1f}s")


if __name__ == "__main__":
    main()
