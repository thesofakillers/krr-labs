# Necessary libraries that will be employed
import itertools
from copy import deepcopy
from dataclasses import dataclass
from typing import List

from sudoku_func import *

#!{sys.executable} -m pip install clingo
#!{sys.executable} -m pip install python-sat
import pysat
from pysat.formula import CNF
from pysat.solvers import MinisatGH, Glucose3


def solve_sudoku_SAT(sudoku: List[List[int]], k: int):
    """
    Solve a sudoku input by encoding the problem into SAT,
    calling a SAT solver, and retrieving the solution for
    the sudoku input from a satisfying truth assignment given
    by the SAT solver.

    Parameters:
        sudoku (list(list(int))): An input puzzle.
        k (int): The dimension of the sudoku input.

    Returns:
        A generator using yield instead of returning a (list(list(list(int)))).
    """
    # YOUR CODE HERE
    min_value = 1
    max_value = int(k**2)
    # https://krr-talk.computational-complexity.nl/t/idpool-for-question-1/235/2
    vpool = pysat.formula.IDPool()  # we use tuples of (row, col, value)
    cnf = CNF()
    # {{{ ------------------------- Helper Functions -------------------------
    def find_adjacents(cell, n, include_cell=False):
        """finds adjacent cells of a given cell in n*n matrix"""
        row, col = cell
        adjacents = [
            (row + i, col + j)
            for i in [-1, 0, 1]
            for j in [-1, 0, 1]
            if 0 <= row + i < n
            and 0 <= col + j < n
            and ((i, j) != (0, 0) if not include_cell else True)
        ]
        return adjacents

    def find_knights(cell, n, include_cell=False):
        """finds knight's move cells of a given cell in n*n matrix"""
        row, col = cell
        knights = [
            (row + i, col + j)
            for i in [-2, -1, 1, 2]
            for j in [-2, -1, 1, 2]
            if 0 <= row + i < n and 0 <= col + j < n and abs(j) != abs(i)
        ]
        if include_cell:
            knights.append(cell)
        return knights

    # }}}
    # {{{---------------------- encoding the problem into SAT ---------------------
    cells = list(itertools.product(range(max_value), repeat=2))
    non_border_cells = [
        cell for cell in cells if (0 not in cell) and (max_value - 1 not in cell)
    ]
    cells_by_row = [[cell for cell in cells if cell[0] == j] for j in range(max_value)]
    cells_by_col = [[cell for cell in cells if cell[1] == j] for j in range(max_value)]
    cells_by_block = [
        [
            cell
            for cell in cells
            if cell[0] in range(j * k, j * k + k) and cell[1] in range(i * k, i * k + k)
        ]
        for j in range(k)
        for i in range(k)
    ]
    cells_by_adjacency = [
        find_adjacents(cell, max_value, True) for cell in non_border_cells
    ]
    cells_by_knights = [find_knights(cell, max_value, True) for cell in cells]

    # Each cell contains a value between 1 and k*k
    for (i, j) in cells:
        input_value = sudoku[i][j]
        # If a cell (i,j) contains a value u in the input
        if input_value != 0:
            # then the cell (i, j) in the solution must contain the same value u
            cnf.append([vpool.id((i, j, input_value))])
        else:
            # each cell contains a value between 1 and k**2
            cnf.append(
                [vpool.id((i, j, val)) for val in range(min_value, max_value + 1)]
            )

    def ensure_uniques(cells_by_group):
        """
        Each two different cells in the same group must contain different values.
        same as (!p1 | !p2) & (!p1 | !p3) & (!p3 | !p2) & (p1 | p2 | p3) ...
        """
        for cell_group in cells_by_group:
            for value in range(min_value, max_value + 1):
                # commenting out the following line as it is covered
                # cnf.append([vpool.id((i, j, value)) for (i, j) in cell_group])
                for cell_pair in itertools.combinations(cell_group, 2):
                    cnf.append([-1 * vpool.id((i, j, value)) for (i, j) in cell_pair])

    # Each two different cells in the same row must contain different values.
    ensure_uniques(cells_by_row)
    # Each two different cells in the same column must contain different values.
    ensure_uniques(cells_by_col)
    # Each two different cells in the same k*k block must contain different values
    ensure_uniques(cells_by_block)
    # TODO: this is about ADJACENCY, not uniqueness in set. need new func
    # Each two different cells that are directly adjacent must contain diff values
    ensure_uniques(cells_by_adjacency)
    # Each two diff cells that can be reached by knights move must contain diff values
    ensure_uniques(cells_by_knights)
    #  }}}
    #  {{{--------------- calling a SAT solver -----------------------------------
    print(len(cnf.clauses))
    assignments = []
    counter = 0
    with MinisatGH(bootstrap_with=cnf.clauses) as m:
        solvable = True
        while solvable:
            solvable = m.solve()
            print(solvable)
            print(m.accum_stats())
            if not solvable:
                # there are no remaining assignments
                break
            else:
                counter += 1
                assignment = m.get_model()
                assignments.append(assignment)
                print(counter)
                # add negated assignment as a disjunction
                m.add_clause([-1 * var for var in assignment])
                # TODO: remember to remove this break
                break
    #  }}}
    # {{{--------- retrieving the solutions forthe sudoku input -------------------
    for assignment in assignments:
        # initialize list of lists
        solution = deepcopy(sudoku)
        for variable in assignment:
            if variable > 0:
                (i, j, val) = vpool.obj(variable)
                solution[i][j] = val
        print(pretty_repr(solution, k))
        yield solution
    # }}}


if __name__ == "__main__":
    # This cell will test whether your code for solve_sudoku_SAT()
    # finds the right number of solutions on several test inputs.

    from sudoku_func import check_num_solutions
    from sudoku_func import test_inputs

    # Run tests
    for num, test_input in enumerate(test_inputs, 1):
        print("- Testing on test input #{}".format(num))
        assert (
            check_num_solutions(
                test_input.sudoku,
                test_input.k,
                test_input.num_solutions,
                solve_sudoku_SAT,
            )
            == True
        )
        print("  Found exactly the set of correct solutions")
