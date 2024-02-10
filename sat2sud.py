"""
sat2sud reads the output produced by miniSAT for a given puzzle 
instance and converts it back into a solved Sudoku puzzle (as a text file, with newlines for readability.)

sudoku empty spaces can be 0, ., *, and ?

"""

import argparse


def main(args):
    sat_solution = read_sat_file(args.solution)

    sudoku = [[1,2,3,1,2,3],[4,5,6,4,5,6]] # 2d array of ints representing a solved sudoku puzzle
    sudoku_format(sudoku, args.output_file)


def sudoku_format(sudoku, output_file):
    with open(output_file, "w") as file:
        '''
        write each sudoku line to output file 
        ie 
        [[1,2,3,1,2,3],[4,5,6,4,5,6]]
        to
        123 123
        456 456
        '''
        for row in sudoku:
            # gen func to break ls into 3 sized chunks
            def chunks(ls):
                for i in range(0, len(row), 3):
                    yield f"{ls[i]}{ls[i+1]}{ls[i+2]}"

            file.write(f"{' '.join(map(str,chunks(row)))}\n")


def read_sat_file(file_path):
    sat_solution = {
                'SAT': 0, # bool representing if satisfiable of sudoku
                'variables': [], # ls[int] representing variables
                }
    with open(file_path, "r") as file:
        line = file.readline().strip()
        sat_solution["SAT"] = line=='SAT'
        if(sat_solution["SAT"]):
            line = file.readline().strip('\n')
            sat_solution['variables'] = line.split(' ')
    
    return sat_solution


# Example usage:


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("solution", type=str)
    parser.add_argument("output_file", type=str)
    args = parser.parse_args()
    main(args)
