"""
sat2sud reads the output produced by miniSAT for a given puzzle 
instance and converts it back into a solved Sudoku puzzle (as a text file, with newlines for readability.)

sudoku empty spaces can be 0, ., *, and ?

This "sat2sud.py" is for 'extended encoding'

"""

import argparse


def main(args):
    sat_solution = read_sat_file(args.solution)
    if sat_solution["SAT"]:
        sudoku = sat_to_sudoku(sat_solution["variables"])
        sudoku_format(sudoku, args.output_file)
    else:
        print("Passed unsatisfiable problem output file will be empty")
        sudoku_format("", args.output_file)


def sat_to_sudoku(variables):
    """ """
    size = int(len(variables) ** (1 / 3))
    sudoku = [[[0] for _ in range(size)] for _ in range(size)]

    for i in range(size):
        for j in range(size):
            # given some cell, determine which number goes there
            for k in range(size):
                index = i * size**2 + j * size + k

                # if k+1 goes in the cell, add it to list, then go to the next cell
                if int(variables[index]) > 0:
                    sudoku[i][j] = k + 1
                    break  # skip to the next cell
    return sudoku


def sudoku_format(sudoku, output_file):
    """
    Translate the variables from miniSAT to sudoku format ie
    123 456 789
    987 123 456
    ect ...

    """
    with open(output_file, "w") as file:
        """
        write each sudoku line to output file
        ie
        [[1,2,3,1,2,3],[4,5,6,4,5,6]]
        to
        123 123
        456 456
        """
        for row in sudoku:
            # gen func to break ls into 3 sized chunks
            def chunks(ls):
                for i in range(0, len(row), 3):
                    yield f"{ls[i]}{ls[i+1]}{ls[i+2]}"

            file.write(f"{' '.join(map(str,chunks(row)))}\n")


def read_sat_file(file_path):
    """
    read the provided sat file and place the variables represented as ints into a dict
    """
    sat_solution = {
        "SAT": 0,  # bool representing if satisfiable of sudoku
        "variables": [],  # ls[int] representing variables
    }
    with open(file_path, "r") as file:
        line = file.readline().strip()
        sat_solution["SAT"] = line == "SAT"
        if sat_solution["SAT"]:
            line = file.readline().strip("\n")
            sat_solution["variables"] = line.split(" ")

    return sat_solution


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("solution", type=str)
    parser.add_argument("output_file", type=str)
    args = parser.parse_args()
    main(args)
