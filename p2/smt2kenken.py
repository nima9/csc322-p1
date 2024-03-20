import argparse

def main(args):
    decoded = parse_smt(args.smt)
    write_puzzle(args.output_file, decoded)

def parse_smt(smt):
    """Returns a list of the values in all the cells"""
    vars = []

    with open(smt, 'r') as f:
        contents = f.read().split("\n")
        for line in contents:
            if line == "unsat":
                vars = None
                break
            elif line == "sat":
                # first line has no variable
                continue
            else:
                # the value of a cell is always the last non-parenthese, non-whitespace character
                line = line.replace("(", "").replace(")", "")
                line = line.strip()
                vars.append(line[-1])
    return vars
    
def write_puzzle(output_path, vars):
    """Converts a list of values into a string depicting the values arranged in a row-major grid, and writes it to a file."""
    
    with open (output_path, 'w') as f:
        if vars == None:
            f.write("uh oh spaghettios")
        else:
            for var in vars:
                f.write(var)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("smt", type=str)
    parser.add_argument("output_file", type=str)
    main(parser.parse_args())