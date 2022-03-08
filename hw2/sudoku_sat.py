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
from pysat.solvers import MinisatGH


def assignment_to_sudoku(assignment, vpool, max_value, fillable_sudoku=None):
    """
    Converts a pysat assignment to a sudoku array
    """
    if fillable_sudoku is None:
        solution = [[0 for _ in range(max_value)] for _ in range(max_value)]
    else:
        solution = deepcopy(fillable_sudoku)
    for variable in assignment:
        if variable > 0:
            (i, j, val) = vpool.obj(variable)
            solution[i][j] = val
    return solution


def ensure_diff_to_target(target, group, cnf, vpool, min_value, max_value):
    """
    Ensures that each cell in the group has a different value from the target cell
    """
    target_i, target_j = target
    for value in range(min_value, max_value + 1):
        for i, j in group:
            cnf.append(
                [
                    -1 * vpool.id((target_i, target_j, value)),
                    -1 * vpool.id((i, j, value)),
                ]
            )


def ensure_group_set(
    cells_by_group, cnf, vpool, min_value, max_value, complete_coverage=False
):
    """
    Ensures each group of cells in the cell_by_group array
    is a set such that each cell has a unique value within that group.

    same as (!p1 | !p2) & (!p1 | !p3) & (!p3 | !p2) & (p1 | p2 | p3) ...

    updates the passed cnf with new clauses in place.
    """
    for cell_group in cells_by_group:
        for value in range(min_value, max_value + 1):
            if complete_coverage:
                # this clause is typically already covered
                cnf.append([vpool.id((i, j, value)) for (i, j) in cell_group])
            for cell_pair in itertools.combinations(cell_group, 2):
                cnf.append([-1 * vpool.id((i, j, value)) for (i, j) in cell_pair])


def find_adj_diag(cell, n, include_cell=False):
    """finds adjacent diagonal cells of a given cell in n*n matrix"""
    row, col = cell
    adj_diag = [
        (row + i, col + j)
        for i in (-1, 1)
        for j in (-1, 1)
        if 0 <= row + i < n and 0 <= col + j < n
    ]
    if include_cell:
        adj_diag.append(cell)
    return adj_diag


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
    # {{{ -------------------- Useful precomputations --------------------------
    cells = list(itertools.product(range(max_value), repeat=2))
    non_border_cells = [
        cell for cell in cells if (0 not in cell) and (max_value - 1 not in cell)
    ]
    centers_idxs = range(max_value)[1::k]
    non_block_center_cells = [
        cell
        for cell in non_border_cells
        if cell[0] not in centers_idxs or cell[1] not in centers_idxs
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
    cells_by_adj_diag = {
        cell: find_adj_diag(cell, max_value, False) for cell in non_block_center_cells
    }
    cells_by_knights = {cell: find_knights(cell, max_value, False) for cell in cells}
    # }}}
    # {{{---------------------- encoding the problem into SAT ---------------------
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
    # Each two different cells in the same row must contain different values.
    ensure_group_set(cells_by_row, cnf, vpool, min_value, max_value)
    # Each two different cells in the same column must contain different values.
    ensure_group_set(cells_by_col, cnf, vpool, min_value, max_value)
    # Each two different cells in the same k*k block must contain different values
    ensure_group_set(cells_by_block, cnf, vpool, min_value, max_value)
    # Each two different cells that are directly adjacent must contain diff values
    for cell, adj_cells in cells_by_adj_diag.items():
        ensure_diff_to_target(cell, adj_cells, cnf, vpool, min_value, max_value)
    # Each two diff cells that can be reached by knights move must contain diff values
    for cell, knight_cells in cells_by_knights.items():
        ensure_diff_to_target(cell, knight_cells, cnf, vpool, min_value, max_value)
    #  }}}
    #  {{{------ calling a SAT solver and converting assingment to sudoku----------
    with MinisatGH(bootstrap_with=cnf.clauses) as m:
        solvable = True
        while solvable:
            solvable = m.solve()
            if not solvable:
                # there are no remaining assignments
                break
            else:
                assignment = m.get_model()
                solution = assignment_to_sudoku(assignment, vpool, max_value, sudoku)
                # add negated assignment as a disjunction
                m.add_clause([-1 * var for var in assignment])
                yield solution
    #  }}}


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
