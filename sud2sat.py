"""
sud2sat reads a single Sudoku puzzle (in some specified text format) 
and converts it to a CNF formula suitable for input to the miniSAT SAT solver (described below.) 
For the basic task, you only need to consider the “minimal” enoding 
of puzzles as CNF formulas (described in class).

"""


def read_sudoku_puzzle(file_path):
    puzzle = []
    with open(file_path, "r") as file:
        for line in file:
            row = [int(num) for num in line.strip().split()]
            puzzle.append(row)
        # print(puzzle)

    return puzzle


# Example usage:
file_path = "ex1.txt"
puzzle = read_sudoku_puzzle(file_path)
for row in puzzle:
    print(row)
