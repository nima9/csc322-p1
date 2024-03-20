import argparse
from itertools import permutations

def main(args):
    encoded = parse_puzzle(args.puzzle)
    write_ans(args.output_file, encoded)
    return


def parse_puzzle(puzzle_path):
    """Parses a ken-ken puzzle to extract the list of variables and what each cell contains."""
    parse_encoding = {
                    'var': [], #list of all variables
                    'const': [], # list of regions with no operator of form {'var': '', 'value': -1, 'region': ''}
                    'row': [], # list of form {'line_one': -1,'line_two': -1,'vars': []}
                    'columns': [], # list of form {'line_one': -1,'line_two': -1,'vars': []}
                    'region': [], # list of form {'operator': '','equals': -1,'vars': [],'name': ''}
                  }
    
    with open(puzzle_path, 'r') as f:
        var_counter = 0
        row_counter = 0
        column_counter = 0
        contents = f.read().split('\n')
        for line in contents:
            line_ls = line.split(',')
            if len(line_ls) < 7:
                # skips lines that aren't part of the puzzle
                pass
            else:
                for j in range(len(line_ls)):
                    # separate region name from rule, if there is a rule. Either way, new_region is a list.
                    new_region = line_ls[j].split('.')
                    # create next variable (e.g. V0, V1, V2)
                    new_var = 'V' + repr(var_counter)
                    var_counter += 1
                    # adds variable to dictionary
                    parse_encoding['var'].append(new_var)
                    
                    try:
                        # for all but the first row, this will append the variable to its appropriate column
                        parse_encoding['columns'][j]['vars'].append(new_var)
                    except:
                        # this does the same, but for the first row
                        parse_encoding['columns'].append({'line_one': 0,'line_two': column_counter,'vars': []})
                        parse_encoding['columns'][j]['vars'].append(new_var)
                        column_counter += 1
                    
                    # Gets the index of the region the variable belongs to, or None if it is the first variable to belong to that region.
                    i = next((i for i, item in enumerate(parse_encoding['region']) if item['name'] == new_region[0]), None)
                    if i == None:
                        # If this is the first variable to belong to its region, the region hasn't been created yet.
                        # The variable either has a rule or is a constant.
                        if not str(new_region[1][-1:]).isdigit():
                            # handles regions with rules
                            parse_encoding['region'].append({'operator': new_region[1][-1:],'equals': new_region[1][:-1],'vars': [new_var],'name': new_region[0]})
                        else:
                            # handles constants
                            parse_encoding['const'].append({'var': new_var, 'value': new_region[1], 'region': new_region[0]})
                    else:
                        # Otherwise, the variable is added to the region, using its index 
                        parse_encoding['region'][i]['vars'].append(new_var)

                # adds all variables to appropriate row
                parse_encoding['row'].append({'line_one': row_counter,'line_two': 0,'vars': parse_encoding['var'][-7:]})
                row_counter += 1

    return parse_encoding


def write_ans(output_file, encoded):
    """Converts a dictionary into a set of SMT-LIB commands to be parsed by an SMT integer solver, and writes them to a file."""

    with open(output_file, "w") as file:
        # Necessary for all SMT files
        file.write("(set-logic UFNIA)\n")
        file.write("(set-option :produce-models true)\n")
        file.write("(set-option :produce-assignments true)\n")

        # Make rules for the existence of variables
        for var in encoded['var']:
            file.write(f"(declare-const {var} Int)\n")
        # Makes rules to specify the possible range of variables
        for var in encoded['var']:
            file.write(f"(assert (and (> {var} 0) (< {var} 8)))\n")
        # Makes rules allowing only one number per row and column
        for row in encoded['row']:
            file.write(f"(assert (distinct {format_list(row['vars'])} )) ; line {row['line_one']} {row['line_two']}\n") 
        for column in encoded['columns']:
            file.write(f"(assert (distinct {format_list(column['vars'])} )) ; line {column['line_one']} {column['line_two']}\n") 
        # Make rules for regions with only one cell to have the correct number
        for const in encoded['const']:
            file.write(f"(assert (= {const['var']} {const['value']})) ; Region {const['region']}\n")
        # Make rules for each region's operator
        for region in encoded['region']:
            if region['operator'] in  ["-", '/']:
                file.write(f"(assert {format_order_operators(region['equals'], region['operator'], region['vars'])} ; Region {region['name']}\n") 
            else:
                file.write(f"(assert (= {region['equals']} ({region['operator']} {format_list(region['vars'])}))) ; Region {region['name']}\n")

        # give instructions to the SMT solver for how to output its results
        file.write("(check-sat)\n")
        file.write(f"(get-value ({format_list(encoded['var'])}))\n")
        file.write("(exit)")

def format_order_operators(equals, operator, vars):
    """Creates all permutations of variables for negative and divide regions in a ken-ken puzzle"""
    var_str = '(or '
   
    # format permutations as a 2D list, containing 2^n sublists, with n being the number of variables
    perms_list = list(map(list, permutations(vars))) 

    # combines all permutations into a string, formatted for the SMT solver
    for permutation in perms_list:
        var_str = var_str + f'(= {equals} ({operator} {format_list(permutation)}))'
    var_str = var_str + '))'
    return var_str

def format_list(vars):
    """Converts a list of variables into a string where they are separated by spaces."""
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