How to Run:
kenken2smt.py:
    input.txt is a text file containing a 7x7 kenken puzzle that is of the form specified by the Project 2-1.pdf documentation
    output.smt is what you want the name of the file that kenken2smt.py outputs the smt-lib formatted file for input into mathsat

python3 kenken2smt.py input.txt output.smt


smt2kenken.py:
    input.smt is the file containing the output of mathsat
    output.txt is the name file that smt2kenken.py outputs either the solution to the kenken file if SAT else it writes unsatisfiable

python3 smt2kenken.py input.smt output.txt

pp.py:
    input.txt is the file containing the json file as specified by Project2-1.pdf document

python3 pp.py input.txt