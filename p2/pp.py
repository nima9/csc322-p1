import argparse

def main(args):
    data = get_data(args.json_file)
    prettyprint(data["rules"], data["values"], data["regions"])

def get_data(json_file):
    """Reads the json file and extracts each cell's rule (if it has one), value (if the puzzle is solved) and region"""
    data = {
        "rules": [], # lists the rule of each cell in row-major order, leaving empty strings for cells which aren't in the top-left of their region
        "values": [], # lists the value of each cell in row-major order, or is full of empty strings
        "regions": [], # lists the region of each cell in row-major order
    }
    return data

def prettyprint(rules, values, regions):
    """
 ---------------------------
| 1 | 2 | 3 | 4   5 | 6 | 7 |
|---|---|---|       |   |---|
| 2 | 3 | 4 | 5   6 | 7   1 |
|---|---|---|-------|-------|
| 3 | 4 | 5 | 6 | 7 | 1 | 2 |
|---|---|---|-------|---|---|
| 4 | 5 | 6 | 7   1 | 2 | 3 |
|---|---|---|-------|---|---|
| 5 | 6 | 7 | 1   2 | 3 | 4 |
|---|---|---|-------|---|---|
| 6 | 7 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|-------|---|---|
| 7 | 1 | 2 | 3 | 4 | 5 | 6 |
 ---------------------------

  --------------------------
 | 3      | 3-     |        |
 |        |        |        |
 |      3 |      2 |        |
 |--------|  -  -  |--------|
 | 2/     |        |        |
 |        |        |        |
 |      4 |      5 |        |
 |  -  -  |--------|--------|
 |        |                 |
 |        |        |        |
 |      2 |                 |
  --------------------------
    """

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
            s += " " + rule(rules, i, j) + " " * (cell_width - 3)
            if j == 6:
                s += "|"
            elif connects(regions, (i, j), (i, j+1)):
                s += " "
            else:
                s += "|"
        # row 2
        s += "\n|"
        for j in range(7):
            # row 2 always has a pipe, even if the cells are connected
            s += " " * cell_width
            s += "|"
        # row 3
        s += "\n|"
        for j in range(7):
            s += " " * (cell_width - 2) + value(values, i, j) + " "
            if j == 6:
                s += "|"
            elif connects(regions, (i, j), (i, j+1)):
                s += " "
            else:
                s += "|"
        # horizontal bar row
        if i == 6:
            # the last line is always a complete bar
            s += "\n " + "-" * ((cell_width + 1) * 7 - 1)
        else:
            s += "\n|"
            for j in range(7):
                # vertical connections result in incomplete bars
                if connects(regions, (i, j), (i+1, j)):
                    s += " " * 2 + "-" + " " * 2 + "-" + " " * 2
                else:
                    s += "-" * cell_width
                if j == 6:
                    s += "|"
                elif connects(regions, (i, j), (i, j+1)) and connects(regions, (i+1, j), (i+1, j+1)):
                    # when the cells above and below connect horizontally, the bar has no pipe
                    s += "-"
                else:
                    s += "|"
    print(s)

def rule(rules, row, column):
    """Returns the rule of the cell, if it is in the top-left of its region, plus enough spaces to reach two characters no matter what"""
    return rules[9 * row + column]

def value(values, row, column):
    """Returns the value of the given cell"""
    return values[9 * row + column]

def connects(regions, coord1, coord2):
    """Returns true if the cell at coord1 and the cell at coord2 belong to the same region, false otherwise"""
    region1 = regions[9 * coord1[0] + coord1[1]]
    region2 = regions[9 * coord2[0] + coord2[1]]
    return region1 == region2

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("json_file", type=str)
    args = parser.parse_args()
    main(args)