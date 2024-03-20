def main(args):
    #vars = get_vars(args)
    vars = "1234567234567134567124567123567123467123457123456"
    prettyprint(vars)

def prettyprint(vars):
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

    print(s)

if __name__ == "__main__":
    main("")