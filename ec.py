#!/usr/bin/env python3

import sys

import circuit.circuit as circ
from circuit.cnf import SatVar, Solver, Solution, Cnf
from circuit.circuit import Circuit
from transform import transform
from transform import gate_xor
from transform import gate_or
from transform import equivalent

# Implementation hints:
#
# 1) You need to build a *miter circuit* (or rather a miter CNF) in order to
#    compare the two circuits. For the circuit part, you can just use the
#    transform function from Exercise 2 (make sure to use different prefixes
#    for the two circuits, as they will usually have overlapping variable
#    names).
#
# 2) Make sure you cover the following error conditions:
#    * The two circuits have different number of inputs or outputs
#    * The inputs and outputs of the two circuits do not have the same names
#    In these cases you can return (False, None).
#
# 3) Run the test script to see if your code works!

def createInputCnf(inputs: set, prefix1: str, prefix2: str) -> Cnf:
    '''The fucntion createInputCnf takes the common inputs of the circuits being checked,
    taking into account their different prefixes, and builds the input connections required
    by the miter circuit logic. Its output is the cnf representing these connections
    '''
    inputCnf = Cnf()

    for i in inputs:
        inputCnf &= equivalent(SatVar(i), SatVar(prefix1 + i))
        inputCnf &= equivalent(SatVar(i), SatVar(prefix2 + i))

    return inputCnf

def createComparatorCnf(outputs: set, prefix1: str, prefix2: str) -> (Cnf, SatVar):
    '''The function createComparatorCnf takes the common outputs of the circuits being checked,
    taking into account their differente prefixes, and builds the output miter logic
    with its XOR and OR gates. Its output is both the miter output CNF and the SatVar
    variable for the miter output symbol
    '''
    # Generation of XOR gates for miter circuit output
    comparator = Cnf()
    comp_signals = []
    i = 0
    for output in outputs:
        xor_i = SatVar('xor_' + str(i))
        output1 = SatVar(prefix1 + output)
        output2 = SatVar(prefix2 + output)
        comparator &= gate_xor(output1, output2, xor_i)
        comp_signals.append(xor_i)
        i += 1

    # Generation of OR gates for miter circuit output
    or_neutral = SatVar('or_neutral')
    comparator &= (~or_neutral)
    i = 0
    for xor_i in comp_signals:
        out = SatVar('or_' + str(i))
        curr = xor_i
        if i == 0:
            comparator &= gate_or(or_neutral, xor_i, out)
        else:
            prev = SatVar('or_' + str(i-1))
            comparator &= gate_or(prev, xor_i, out)
        i += 1

    return comparator, out

def check(c1: Circuit, c2: Circuit) -> (bool, Solution):
    '''The function check() takes two Circuits as input and performs an equivalence
    check using a SAT solver. it returns a tuple, where the first entry is a
    Boolean value (True for equivalent, False for different) and the second
    value is -- in case of a difference found -- a Solution to the underlying
    SAT problem, representing a counterexample. If the circuits are indeed
    equivalent, the second entry will be None.

    '''

    inputs1 = c1.getInputs()
    inputs2 = c2.getInputs()
    outputs1 = c1.getOutputs()
    outputs2 = c2.getOutputs()
    prefix1 = 'c1_'
    prefix2 = 'c2_'

    # Checking for inequal number or names of inputs and outputs
    if (len(inputs1) != len(inputs2)) or (len(outputs1) != len(outputs2)):
        return False, None
    else:
        if (len(inputs1 - inputs2) != 0) or (len(outputs1 - outputs2) != 0):
            return False, None

    # Tseitin Transformation of the two circuits
    cnf1 = transform(c1, prefix1)
    cnf2 = transform(c2, prefix2)

    # Generating connection among correspondent inputs
    inputConnections = createInputCnf(inputs1, prefix1, prefix2)

    # Generating comparison logic for miter circuit
    comparator, out = createComparatorCnf(outputs1, prefix1, prefix2)

    # Composition of the miter circuit
    miter = inputConnections & cnf1 & cnf2 & comparator & out

    # CNF SAT solving
    solver = Solver()
    solution = solver.solve(miter)

    if solution:
        return False, solution
    return True, None

    pass

