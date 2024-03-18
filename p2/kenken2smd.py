# required task
import argparse

def main(args):
    puzzle = parse_puzzle(args.puzzle)

    write_ans(args.output_file)
    return


def parse_puzzle(puzzle):
    parse_dict = {
                    'var': [], #list of all variables
                    'row': [], # vars in each row
                    'columns': [], # vars in each columns
                    'region': [{
                                'operator': '', # operator
                                'equals': -1, # int for what equals
                                'vars': [], # vars in region
                                'name': '' # region name
                                }],
                  }
    return puzzle


def write_ans(output_file, encoded):
    with open(output_file, "w") as file:
        file.write("(set-logic UFNIA)")
        file.write("(set-option :produce-models true)")
        file.write("set-option :produce-assignments true)")
        for var in encoded['var']:
            file.write(f"(declare-const {var} Int)")
        for row in encoded['row']:
            file.write(f"(assert (distinct {row} )) ; line {} {}")
        for column in encoded['column']:
            file.write(f"(assert (distinct {column} )) ; line {} {}")
        for region in encoded['regions']:
            file.write(f"(assert ({region['operator']}))")

        file.write("(check-sat)")
        file.write(f"(get-value ({encoded['var']}))")
        file.write("(exit)")
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("puzzle", type=str)
    parser.add_argument("output_file", type=str)
    args = parser.parse_args()
    main(args)