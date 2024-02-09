"""
sat2sud reads the output produced by miniSAT for a given puzzle 
instance and converts it back into a solved Sudoku puzzle (as a text file, with newlines for readability.)

"""
import argparse

def main(args):
    read_sat_file(args.solution)

    return


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('solution', type=str)
    args = parser.parse_args()
    main(args)