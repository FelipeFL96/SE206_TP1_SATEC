#!/usr/bin/env python3

import sys

import circuit.circuit as circ
from circuit.cnf import SatVar, Solver, Solution, Cnf
from circuit.circuit import Circuit
from transform import transform
from transform import gate_xor
from transform import gate_or

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

def comparatorXorStage(prefix1: str, prefix2: str, signals: list) -> (Cnf, list):
    i = 0
    xor_cnf = Cnf()
    xor_outputs = []
    for sig in signals:
        xor_cnf &= gate_xor(SatVar(prefix1 + sig), SatVar(prefix2 + sig), SatVar('xor_' + str(i)))
        xor_outputs.append('xor_' + str(i))
        i += 1
    return xor_cnf, xor_outputs

def comparatorOrStage(signals: list) -> (Cnf, SatVar):
    i = 0
    or_cnf = Cnf()
    or_cnf &= (~SatVar('false'))

    for sig in signals:
        out = SatVar('or_' + str(i))
        m = SatVar(sig)
        if i == 0:
            or_cnf &= gate_or(SatVar('false'), m, out)
        else:
            prev = SatVar('or_' + str(i-1))
            or_cnf &= gate_or(prev, m, out)
        i += 1
    return or_cnf, out

def comparator(prefix1: str, prefix2: str, circuit_outputs: list) -> (Cnf, SatVar):
    xor_cnf, out_sigs = comparatorXorStage(prefix1, prefix2, circuit_outputs)
    or_cnf, miter_out = comparatorOrStage(out_sigs)
    return xor_cnf & or_cnf, miter_out

def binrow(num: int, n: int) -> list:
    fat = num
    tab = []
    for i in range(0,n):
        if fat%2 == 0:
            tab.insert(0, False)
        else:
            tab.insert(0, True)
        fat //= 2
    return tab

def createMiter(outputs: set, prefix1: str, prefix2: str) -> Cnf:
    comparator = Cnf()
    miter_signals = []

    i = 0
    for output in outputs:
        comparator &= gate_xor(SatVar(prefix1 + output), SatVar(prefix2 + output), SatVar('m_' + str(i)))
        miter_signals.append('m_' + str(i))
        i += 1

    i = 0
    or_neutral = SatVar('or_neutral')
    comparator &= (~or_neutral)
    for m_i in miter_signals:
        out = SatVar('or_' + str(i))
        m = SatVar(m_i)
        if i == 0:
            comparator &= gate_or(or_neutral, m, out)
        else:
            prev = SatVar('or_' + str(i-1))
            comparator &= gate_or(prev, m, out)
        i += 1
    return comparator, out

def createTests(inputs: set()) -> list:
    tests = []
    n = len(inputs)

    for i in range(0, 2**n):
        b = binrow(i, n)
        row = dict()
        for (inputStr, value) in zip(inputs, b):
            row[inputStr] = value
        tests.append(row)
    return tests

def setInputs(cnf: Cnf, values: dict, prefix1: str, prefix2: str) -> Cnf:
    setCnf = Cnf()
    for v in values:
        if values[v] == False:
            setCnf = cnf & (~SatVar(prefix1+v)) & (~SatVar(prefix2+v))
        else:
            setCnf = cnf & (SatVar(prefix1+v)) & (SatVar(prefix2+v))
    return setCnf

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

    if (len(inputs1) != len(inputs2)) or (len(outputs1) != len(outputs2)):
        return False, None
    else:
        if (len(inputs1 - inputs2) != 0) or (len(outputs1 - outputs2) != 0):
            return False, None

    #Faire une transformation Tseitin des deux circuits,
    cnf1 = transform(c1, prefix1)
    cnf2 = transform(c2, prefix2)

    #rajouter la logique de comparaison du miter, et
    comparator, out = createMiter(outputs1, prefix1, prefix2)

    #rajouter une contrainte sur la sortie pour la forcer à 1 (comment exprimer cette contrainte en CNF?).
    miter = cnf1 & cnf2 & comparator & (~out)

    #« Connecter » les entrées correspondantes (comment exprimer cela en CNF?)
    solver = Solver()
    tests = createTests(inputs1)
    for test in tests:
        testCnf = setInputs(miter, test, prefix1, prefix2)
        solution = solver.solve(testCnf)
        if solution:
            return False, solution

    return True, None

    pass

