# required task
import argparse
from itertools import permutations

def main(args):
    puzzle = parse_puzzle(args.puzzle)

    write_ans(args.output_file)
    return


def parse_puzzle(puzzle):
    parse_dict = {
                    'var': [], #list of all variables
                    'row': [{
                                'line_one': -1,
                                'line_two': -1,
                                'vars': []
                            }], # (assert (distinct V0 V1 V2 V3 V4 V5 V6 V7 V8 )) ; line What is this!!!! ???0 1
                    'columns': [{
                                    'line_one': -1,
                                    'line_two': -1,
                                    'vars': []
                                }], # vars in each columns
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
        file.write("(set-logic UFNIA)\n")
        file.write("(set-option :produce-models true)\n")
        file.write("set-option :produce-assignments true)\n")
        for var in encoded['var']:
            file.write(f"(declare-const {format_list(var)} Int)\n")
        for row in encoded['row']:
            file.write(f"(assert (distinct {format_list(row['vars'])} )) ; line {row['line_one']} {row['line_two']}\n") # maybe comments? need to figure out the numbers mean in line ? ?
        for column in encoded['column']:
            file.write(f"(assert (distinct {format_list(column['vars'])} )) ; line {row['line_one']} {row['line_two']}\n") # need to figure out what the numbers mean in line ? ?
        for region in encoded['regions']:
            if region['operator'] in  ["-", '/']:
                file.write(f"(assert {format_order_operators(region['equals'], region['operator'], region['vars'])} ; Region {region['name']}\n") # needs more work needs combinatorial combination of region['vars']
            else:
                file.write(f"(assert (= {region['equals']} ({region['operator']} {format_list(region['vars'])}))) ; Region {region['name']}\n")

        file.write("(check-sat)")
        file.write(f"(get-value ({encoded['var']}))")
        file.write("(exit)")

def format_order_operators(equals, operator, vars):
    var_str = '(or '
    perms_list = list(map(list, permutations(vars)))
    for permutation in perms_list:
        for vars in permutation:
            var_str = var_str + f'(= {equals} ({operator} {format_list(vars)}))'
    var_str = var_str + ')'
    return var_str

def format_list(vars):
    var_str = ''
    for var in vars:
        var_str = var_str + var + ' '
    return var_str[:-1] # remove last space


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("puzzle", type=str)
    parser.add_argument("output_file", type=str)
    args = parser.parse_args()
    main(args)