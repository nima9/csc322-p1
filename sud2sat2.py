"""
sud2sat reads a single Sudoku puzzle (in some specified text format) 
and converts it to a CNF formula suitable for input to the miniSAT SAT solver (described below.) 
For the basic task, you only need to consider the minimal encoding 
of puzzles as CNF formulas (described in class).

efficient encoding = minimal encoding + at_most_one_num

This "sud2sat2.py" is
"""

import argparse


def main(args):
    sudoku = read_sudoku_puzzle(args.puzzle)
    solution = {
        "num_variables": 0,  # int representing num of variables
        "num_clauses": 0,  # int representing num of clauses
        "clauses": [],  # 2d array of ints each int reps a variable ie 1 = x_1 terminate each clause line with 0
    }

    solution["num_variables"] = len(sudoku) ** 3

    encoding = get_efficient_encoding(len(sudoku))
    encoding.extend(add_puzzle_constraints(sudoku))

    solution["clauses"] = encoding
    solution["num_clauses"] = len(encoding)
    dimacs_format(solution, args.output_file)


def get_minimal_encoding(size):
    encoding = at_least_one_num(size)
    encoding.extend(max_once_in_every_row(size))
    encoding.extend(max_once_in_every_column(size))
    encoding.extend(max_once_sub_grid_3x3(size))
    return encoding


def get_efficient_encoding(size):
    encoding = get_minimal_encoding(size)
    encoding.extend(at_most_one_num(size))
    return encoding


# converts a row, a column, and a integer to a single variable.
def do_the_math(i, j, k, size):
    return size**2 * (i - 1) + size * (j - 1) + k


def dimacs_format(solution, output_file):
    with open(output_file, "w") as file:
        # set up file header
        file.write(f"p cnf {solution['num_variables']} {solution['num_clauses']}\n")

        """ 
        write each clause line ie [[1,2,-3],[4,5,6]] is
        1 2 -3
        4 5 6
        which represents
        (x1 | x2 | ~x3) & (x4 | x5 | x6)
        """
        for clause in solution["clauses"]:
            file.write(f"{' '.join(map(str,clause))} 0\n")


def read_sudoku_puzzle(file_path):
    puzzle = []
    with open(file_path, "r") as file:
        data = (
            file.read()
            .strip()
            .replace("\n", "")
            .replace(" ", "")
            .replace(".", "0")
            .replace("*", "0")
            .replace("?", "0")
        )
        rows = [
            data[i : i + 9] for i in range(0, len(data), 9)
        ]  # maybe change that are all problems going to be 9 x 9
        for row in rows:
            puzzle.append([int(num) for num in row])
    return puzzle


"""
---Notes---
ex: size 2x2 sudoku puzzle
(~a or ~b) and (~c or ~d) = [[-1, -2], [-3, -4]]
domain [1,2] //meaning, the value of each cell can be 1 or 2
variables [111, 112, 121, 122, 211, 212, 221, 222] //total number of cells
rows = [[-111,-121], [-112,-122], [-211,-212], [-221,-222]]
columns = [[],[]]
"""


def add_puzzle_constraints(sudoku):
    clauses = []
    for row in range(len(sudoku)):
        for column in range(len(sudoku[row])):
            if sudoku[row][column] != 0:
                clauses.append(
                    [do_the_math(row + 1, column + 1, sudoku[row][column], len(sudoku))]
                )
    return clauses


# Minimal Encoding
# ----------------
def at_least_one_num(size):
    clauses = []
    for i in range(1, size + 1):
        for j in range(1, size + 1):
            clause = []
            for k in range(1, size + 1):
                clause.append(do_the_math(i, j, k, size))
            clauses.append(clause)
    return clauses


def max_once_in_every_row(size):
    clauses = []
    for i in range(1, size + 1):
        for k in range(1, size + 1):
            for j in range(1, size):  # j=1 and 8
                for l in range(j + 1, size + 1):
                    clauses.append(
                        [
                            -1 * do_the_math(i, j, k, size),
                            -1 * do_the_math(i, l, k, size),
                        ]
                    )
    return clauses


def max_once_in_every_column(size):
    clauses = []
    for j in range(1, size + 1):
        for k in range(1, size + 1):
            for i in range(1, size):  # i=1 and 8
                for l in range(i + 1, size + 1):
                    clauses.append(
                        [
                            -1 * do_the_math(i, j, k, size),
                            -1 * do_the_math(l, j, k, size),
                        ]
                    )
    return clauses


# encoding the rules for the 3x3 sub-grids of a 9x9 sudoku puzzle
# if puzzle is 9x9, size = 9 .      default value for parameter 'size' is 9
def max_once_sub_grid_3x3(size=9):
    # hardcoded for 9x9 sudoku puzzle
    clauses = []
    for k in range(1, 9 + 1):
        for a in range(0, 2 + 1):
            for b in range(0, 2 + 1):
                for u in range(1, 3 + 1):
                    for v in range(1, 3 + 1):
                        for w in range(v + 1, 3 + 1):
                            clauses.append(
                                [
                                    -1 * do_the_math(3 * a + u, 3 * b + v, k, size=9),
                                    -1 * do_the_math(3 * a + u, 3 * b + w, k, size=9),
                                ]
                            )
                        for w in range(u + 1, 3 + 1):
                            for t in range(1, 3 + 1):
                                clauses.append(
                                    [
                                        -1
                                        * do_the_math(3 * a + u, 3 * b + v, k, size=9),
                                        -1
                                        * do_the_math(3 * a + w, 3 * b + t, k, size=9),
                                    ]
                                )
    return clauses


# ex: clauses[0][0] will equal: -1*do_the_math(1,1,1,9) = -1


# Efficient Encoding
# ------------------
def at_most_one_num(size):
    clauses = []
    for i in range(1, size + 1):
        for j in range(1, size + 1):
            for k in range(1, size):  # k goes from 1 to 8
                for l in range(k + 1, size + 1):
                    clauses.append(
                        [
                            -1 * do_the_math(i, j, k, size),
                            -1 * do_the_math(i, j, l, size),
                        ]
                    )
    return clauses


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("puzzle", type=str)
    parser.add_argument("output_file", type=str)
    args = parser.parse_args()
    main(args)
