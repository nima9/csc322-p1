"""
sud2sat reads a single Sudoku puzzle (in some specified text format) 
and converts it to a CNF formula suitable for input to the miniSAT SAT solver (described below.) 
For the basic task, you only need to consider the minimal enoding 
of puzzles as CNF formulas (described in class).

"""
import argparse


def main(args):
    sudoku = read_sudoku_puzzle(args.puzzle)
    solution = {
                'num_variables': 0, # int representing num of variables
                'num_clauses': 0, # int representing num of clauses
                'clauses': [] # 2d array of ints each int reps a variable ie 1 = x_1 terminate each clause line with 0
                }

    dimacs_format(solution, args.output_file)


def dimacs_format(solution, output_file):
    with open(output_file, "w") as file:
        # set up file header
        file.write(f"p cnf {solution['num_variables']} {solution['num_clauses']}\n")

        ''' 
        write each clause line ie [[1,2,-3],[4,5,6]] is
        1 2 -3
        4 5 6
        which represents
        (x1 | x2 | x3) & (x4 | x5 | x6)
        '''
        for clause in solution['clauses']:
            file.write(f"{' '.join(map(str,clause))}\n")


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
        rows = [data[i : i + 9] for i in range(0, len(data), 9)]
        for row in rows:
            puzzle.append([int(num) for num in row])
    return puzzle


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("puzzle", type=str)
    parser.add_argument("output_file", type=str)
    args = parser.parse_args()
    main(args)
