import argparse
import json


# run: pp.py json.json
def main(args):
    spaces = " " * 17
    print("\n\n" + spaces + "~~~ ⌄⌄ UN-SOLVED PUZZLE ⌄⌄ ~~~")
    data = get_data(args.json_file, False)
    prettyprint(data["rules"], data["values"], data["connections"])

    print("\n\n" + spaces + "~~~ ⌄⌄ SOLVED PUZZLE ⌄⌄ ~~~")
    data = get_data(args.json_file, True)
    prettyprint(data["rules"], data["values"], data["connections"])


def get_data(json_file, solved):
    """Reads the json file and extracts each cell's rule (if it has one), value (if the puzzle is solved) and the directions it connects to other cells"""
    data = {
        "rules": [],  # lists the rule of each cell in row-major order, leaving empty strings for cells which aren't in the top-left of their region
        "values": [],  # lists the value of each cell in row-major order, or is full of empty strings
        "connections": [],  # for each cell, lists whether it connects to the cell on its right, bottom, or both
    }

    with open(json_file, "r") as f:
        input = json.load(f)["data"]
    input = input.split("A")[1]
    (answer, input) = input.split("T")
    (target, input) = input.split("S")
    (symbols, input) = input.split("V")
    (vertical, horizontal) = input.split("H")

    if solved:
        answer.replace("\r\n", "")
        for n in answer.split(" "):
            data["values"].append(n.strip())
    else:
        data["values"] = [" "] * 49
    target = target.replace("\r\n", " ")
    symbols = symbols.replace("\r\n", " ")
    for i in range(49):
        n = target[4 * i : 4 * (i + 1)].strip()
        s = symbols[2 * i : 2 * (i + 1)].strip()
        if n == "0" or s == "0":
            data["rules"].append("")
        elif s == "1":
            data["rules"].append(n)
        else:
            data["rules"].append(n + s)
    vertical = vertical.replace("\r\n", " ")
    horizontal = horizontal.replace("\r\n", " ")
    for i in range(7):
        for j in range(7):
            v = (
                vertical[2 * (6 * i + j) : 2 * (6 * i + j + 1)].strip()
                if j < 6
                else "1"
            )
            h = (
                horizontal[2 * (6 * j + i) : 2 * (6 * j + i + 1)].strip()
                if i < 6
                else "1"
            )
            if h == "0" and v == "0":
                data["connections"].append("both")
            elif h == "0":
                data["connections"].append("bottom")
            elif v == "0":
                data["connections"].append("right")
            else:
                data["connections"].append("")
    return data


def prettyprint(rules, values, connections):
    cell_width = 8
    cell_height = 3
    s = ""

    # iterate over rules and cell values simultaneously
    # for each cell, print a box containing the rule near the top left and the value near the bottom right
    # if the cell's region will continue in a certain direction, make the boundary on the box in that direction incomplete
    # see second example
    s += " " + "-" * ((cell_width + 1) * 7 - 1)
    for i in range(7):
        # row 1
        s += "\n|"
        for j in range(7):
            s += " " + rule(rules, i, j)
            if j == 6:
                s += "|"
            elif connects(connections, i, j, "right"):
                s += " "
            else:
                s += "|"
        # row 2
        s += "\n" + "|"
        for j in range(7):
            # row 2 always has a pipe, even if the cells are connected
            s += " " * cell_width
            s += "|"
        # row 3
        s += "\n" + "|"
        for j in range(7):
            s += " " * (cell_width - 2) + value(values, i, j) + " "
            if j == 6:
                s += "|"
            elif connects(connections, i, j, "right"):
                s += " "
            else:
                s += "|"
        # horizontal bar row
        s += "\n"
        if i == 6:
            # the last line is always a complete bar
            s += " " + "-" * ((cell_width + 1) * 7 - 1)
        else:
            s += "|"
            for j in range(7):
                # vertical connections result in incomplete bars
                if connects(connections, i, j, "bottom"):
                    s += " " * 2 + "-" + " " * 2 + "-" + " " * 2
                else:
                    s += "-" * cell_width
                if j == 6:
                    s += "|"
                elif connects(connections, i, j, "right") and connects(
                    connections, i + 1, j, "right"
                ):
                    # when the cells above and below connect horizontally, the bar has no pipe
                    s += "-"
                else:
                    s += "|"
    print(s)


def rule(rules, row, column):
    """Returns the rule of the cell, if it is in the top-left of its region, plus enough spaces to reach three characters no matter what"""
    rule = rules[7 * row + column]
    while len(rule) < 7:
        rule += " "
    return rule


def value(values, row, column):
    """Returns the value of the given cell"""
    return values[7 * row + column]


def connects(connections, row, column, direction):
    """Returns true if the cell has a connection in the given direction(s)"""
    return (
        connections[7 * row + column] == direction
        or connections[7 * row + column] == "both"
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("json_file", type=str)
    args = parser.parse_args()
    main(args)
