# required task
import argparse

def main(args):
    puzzle = parse_puzzle(args.puzzle)

    write_ans(args.output_file)
    return


def parse_puzzle(puzzle):
    return puzzle


def write_ans(output_file):
    with open(output_file, "w") as file:
        file.write(f"")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("puzzle", type=str)
    parser.add_argument("output_file", type=str)
    args = parser.parse_args()
    main(args)