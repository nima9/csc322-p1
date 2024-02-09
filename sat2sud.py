"""
sat2sud reads the output produced by miniSAT for a given puzzle 
instance and converts it back into a solved Sudoku puzzle (as a text file, with newlines for readability.)

"""

import argparse


def main(args):
    sat_solution = read_sat_file(args.solution)


def read_sat_file(file_path):
    with open(file_path, "r") as file:
        sat_solution = file.read().splitlines()
    print(sat_solution)
    return sat_solution


# Example usage:


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("solution", type=str)
    args = parser.parse_args()
    main(args)
