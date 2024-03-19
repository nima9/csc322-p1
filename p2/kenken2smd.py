# required task
import argparse
from itertools import permutations

def main(args):
    encoded = parse_puzzle(args.puzzle)
    write_ans(args.output_file, encoded)
    return


def parse_puzzle(puzzle_path):
    parse_encoding = {
                    'var': [], #list of all variables
                    'row': [], # list of form {'line_one': -1,'line_two': -1,'vars': []}
                    'columns': [], # list of form {'line_one': -1,'line_two': -1,'vars': []}
                    'region': [], # list of form {'operator': '','equals': -1,'vars': [],'name': ''}
                  }
    
    with open(puzzle_path, 'r') as f:
        var_counter = 0
        row_counter = 0
        column_counter = 0
        contents = f.read()
        contents = contents.split('\n')
        for line in contents:
            line_ls = line.split(',')
            if len(line_ls) < 7:
                pass
            else:
                for j in range(len(line_ls)):
                    new_region = line_ls[j].split('.')
                    new_var = 'V' + repr(var_counter)
                    parse_encoding['var'].append(new_var)
                    var_counter += 1
                    try:
                        parse_encoding['columns'][j]['vars'].append(new_var)
                    except:
                        parse_encoding['columns'].append({'line_one': 0,'line_two': column_counter,'vars': []})
                        parse_encoding['columns'][j]['vars'].append(new_var)
                        column_counter += 1
                    
                    i = next((i for i, item in enumerate(parse_encoding['region']) if item['name'] == new_region[0]), None)
                    if i == None:
                        # print(new_region, line_ls[j], line_ls[j+1])
                        parse_encoding['region'].append({'operator': new_region[1][-1:],'equals': new_region[1][:-1],'vars': [new_var],'name': new_region[0]})
                    else:
                        parse_encoding['region'][i]['vars'].append(new_var)

                parse_encoding['row'].append({'line_one': row_counter,'line_two': 0,'vars': parse_encoding['var'][-7:]})
                row_counter += 1

    return parse_encoding


def write_ans(output_file, encoded):
    with open(output_file, "w") as file:
        file.write("(set-logic UFNIA)\n")
        file.write("(set-option :produce-models true)\n")
        file.write("(set-option :produce-assignments true)\n")
        for var in encoded['var']:
            file.write(f"(declare-const {var} Int)\n")
        for row in encoded['row']:
            file.write(f"(assert (distinct {format_list(row['vars'])} )) ; line {row['line_one']} {row['line_two']}\n") # maybe comments? need to figure out the numbers mean in line ? ?
        for column in encoded['columns']:
            file.write(f"(assert (distinct {format_list(column['vars'])} )) ; line {column['line_one']} {column['line_two']}\n") # need to figure out what the numbers mean in line ? ?
        for region in encoded['region']:
            if region['operator'] in  ["-", '/']:
                file.write(f"(assert {format_order_operators(region['equals'], region['operator'], region['vars'])} ; Region {region['name']}\n") # needs more work needs combinatorial combination of region['vars']
            else:
                file.write(f"(assert (= {region['equals']} ({region['operator']} {format_list(region['vars'])}))) ; Region {region['name']}\n")

        file.write("(check-sat)")
        file.write(f"(get-value ({format_list(encoded['var'])}))")
        file.write("(exit)")

def format_order_operators(equals, operator, vars):
    var_str = '(or '
    perms_list = list(map(list, permutations(vars)))
    for permutation in perms_list:
        var_str = var_str + f'(= {equals} ({operator} {format_list(permutation)}))'
    var_str = var_str + '))'
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