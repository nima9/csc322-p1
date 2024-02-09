"""
sud2sat reads a single Sudoku puzzle (in some specified text format) 
and converts it to a CNF formula suitable for input to the miniSAT SAT solver (described below.) 
For the basic task, you only need to consider the “minimal” enoding 
of puzzles as CNF formulas (described in class).

"""

import argparse


def main(args):
    sudoku = read_sudoku_puzzle(args.puzzle)

    for row in sudoku:
        print(row)


def read_sudoku_puzzle(file_path):
    puzzle = []
    with open(file_path, "r") as file:
        for line in file:
            row = [int(num) for num in line.strip().split()]
            puzzle.append(row)
    return puzzle


# Example usage:


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("puzzle", type=str)
    args = parser.parse_args()
    main(args)
