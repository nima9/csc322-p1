# Project 2 for CSC 322 Class (with Alex, Carter, and Nima - Group 15)

## Student Names and IDs for Group 15:

- Alexander Lambert - V00956639
- Carter Cranston   - V01000607
- Nima Mohajeri     - V00857216

## This submission contains the following files:

- `kenken2smt.py`
- `smt2kenken.py`
- `pp.py`
- `Report-stats.txt`
- `Report-gen.pdf`
- `README.md`

<br/>

<details><summary>How to run `kenken2smt.py`.</summary>

#### `input.txt` is a text file containing a 7x7 kenken puzzle that is of the form specified by the `Project 2.pdf` documentation. After running, `output.smt` will contain the puzzle, converted into smt-lib format.

##### How to run kenken2smt.py:
```
python3 kenken2smt.py <input.txt> <output.smt>
```
###### Parameters explained for `kenken2smt.py` ^^
- `<input.txt>`: pass the input file in a .txt format
- `<output.smt>`: pass the name of what you want your output.smt to be named after running `kenken2smt.py`, Example: “myoutput.smt”.

</details>


<details><summary>How to run `smt2kenken.py`.</summary>

#### `input.smt` is the file containing the output from mathsat. After running `smt2kenken.py`, there will be an `output.txt` file which will contain the solution to the puzzle, or the sentence “uh oh spaghettios this problem is unsat!”.
##### How to run `smt2kenken.py`
```
python3 smt2kenken.py <input.smt> <output.txt>
```
###### Parameters explained for `smt2kenken.py` ^^
- `<input.smt>`: pass the input file in a .smt format
- `<output.txt>`: pass the name of what you want your output.txt to be named after running `smt2kenken.py`, ex: “myoutput.txt”.

</details>





<details><summary>How to run Pretty Print (`pp.py`).</summary>

#### for running `pp.py`: `input.json` is the file containing the .json file as specified by the `Project 2.pdf` documentation.
After running, `output.txt`, it will contain two ASCII graphics representing the unsolved and solved puzzle.

##### How to run `pp.py`:
```
python3 pp.py <input.json> <output.txt>
```
###### Parameters explained for `pp.py` ^^
- `<input.json>`: pass the input file in a .json format
- `<output.txt>`: pass the name of what you want your output.txt to be named after running `pp.py`, ex: “myoutput.txt”.
</details>



<br/>



#### Report-gen.txt:
- Explains how our programs work, and why we wrote them the way we did.


#### Report-stats.txt:
- This is the report comparing the mathsat run times of the hard vs average puzzle. This is our performance evaluation report.
