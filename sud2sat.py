"""
sud2sat reads a single Sudoku puzzle (in some specified text format) 
and converts it to a CNF formula suitable for input to the miniSAT SAT solver (described below.) 
For the basic task, you only need to consider the “minimal” enoding 
of puzzles as CNF formulas (described in class).

"""
import argparse

def main(args):
    read_sudoku_puzzle(argv)

    return


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('puzzle', type=str)
    args = parser.parse_args()
    main(args)