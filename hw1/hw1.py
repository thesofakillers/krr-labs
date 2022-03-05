"""Psuedocode for KRR homework"""
# SAT: Given a propositional logic CNF formula φ, it outputs a 0 if φ is not satisfiable, and it outputs a 1 if φ is satisfiable
from future import SAT


def findNTruthAssignments(cnf_formula, n):
    """
    tries to find n satisfying truth assignments
    of a propositional logic CNF formula
    """
    truth_assignments = set()
    for i in range(n):
        # try to get truth assignment
        assignment = determineSATandFindTA(cnf_formula)
        if assignment == "unsat":
            # we've reached the end of available truth assignments
            return truth_assignments
        else:
            truth_assignments.add(assignment)
            clause = assignmentToDisjunction(not assignment)
        # add the negation of our assignment as a clause to our formula
        cnf_formula = cnf_formula and clause
    return truth_assignments


def assignmentToDisjunction(assignment):
    """
    Given a truth assignment, it outputs a disjunction of variables
    """
    disjunction = assignment[0]
    for variable in assignment[1:]:
        disjunction = disjunction or variable
    return disjunction


def determineSATandFindTA(cnf_formula):
    """
    Given a CNF formula, tries to find a truth assignment
    """
    if not SAT(cnf_formula):
        return "unsat"
    assignment = TruthAssignment()
    for variable in cnf_formula.variables:
        simp_formula = simplifyByAssignment(
            cnf_formula,
            variable,
            True,
        )
        if SAT(simp_formula):
            assignment.add(variable, True)
        else:
            assignment.append(variable, False)
        cnf_formula = simp_formula
    return assignment


def simplifyByAssignment(cnf_formula, variable):
    """
    Simplifies a CNF formula in case a given variable is set to true
    """
    # intialize empty CNF Formula
    simp_formula = CNFFormula()
    for clause in cnf_formula:
        if variable in clause:
            # skip this clause,
            continue
        elif variable.neg in clause:
            # remove negation of variable from clause
            clause = clause.remove(variable.neg)
        # add clause to simplified formula
        simp_formula.add_clause(clause)
    return simp_formula
