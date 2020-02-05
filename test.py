#!/usr/bin/env python3

import os
import traceback

import circuit.circuit as circ
from circuit.cnf import SatVar, Solver
import transform
import ec

# This file contains test code for your implementations. You can run
# it in order to debug your code.

red = '\033[31m'
blue = '\033[34;1m'
green = '\033[32m'
cyan = '\033[36m'
normal = '\033[0m'

def print_result(message):
    print (blue + "[RESUL] " + normal + message)

def print_info(message):
    print (cyan + "[INFO ] " + normal + message)

def print_passed(message):
    print (green + "[PASS ] " + normal + message)

def print_error(message):
    print (red + "[ERROR] " + normal + message)

# =============================================================================
# Test code for full adder CNF
# =============================================================================

def test_adder():
    from adder import mk_adder

    cnf = mk_adder()
    adder = circ.parse('benchmarks/fa.crc')

    if cnf is None:
        print_error("CNF is empty (None). Go do something about it...")
        return False

    # Function to constrain CNF with input conditions
    def constrain(cnf, test):
        def constr(x):
            return SatVar(x) if test[x] else ~SatVar(x)
        return cnf & constr('a') & constr('b') & constr('cin')

    # Functions to display test cases
    def head():
        print_result("a b cin | cout s")
        print_result("--------+-------")
    def row(sim, sat):
        r =  "%i %i  %i  |   " % (sim['a'], sim['b'], sim['cin'])
        good = True
        complete = True
        if (not sat):
            r += red + '-  -' + normal + ' [UNSAT]'
            good = False
        else:
            if not ('cout' in sat.keys()):
                r += red
                r += '-  '
                complete = False
            elif sim['cout'] == sat['cout']:
                r += green
                r += '%i  ' % sim['cout']
            else:
                r += red
                r += '%i  ' % sat['cout']
                good = False
            if not ('s' in sat.keys()):
                r += red
                r += '-'
                complete = False
            elif sim['s'] == sat['s']:
                r += green
                r += '%i' % sim['s'] + normal
            else:
                r += red
                r += '%i' % sat['s'] + normal
                good = False
            if not good:
                r += ' [wrong outputs]'
            if not complete:
                r += ' [incomplete solution]'
        print_result(r)
        return good and complete

    # test all input conditions
    B = [False, True]
    tests = [{'a':a, 'b':b, 'cin':c} for a in B for b in B for c in B]
    solver = Solver()
    head()
    pass_test = True
    for test in tests:
        sim = adder.simulate(test)
        sat = solver.solve(constrain(cnf, test))
        pass_test = row(sim, sat) and pass_test
    return pass_test

# =============================================================================
# Test code for transform()
# =============================================================================

# Generator function to enumerate solutions
def allSAT(cnf, blockVars = None):
    solver = Solver()
    while True:
        solution = solver.solve(cnf)
        if not solution:
            while True:
                yield None
        yield solution
        block = ~solution
        cnf &= block

# Test if solutions of CNF are consistent with circuit simulations
def check(filename, max_tests):
    c = circ.parse(filename)
    try:
        cnf = transform.transform(c)
    except Exception as e:
        print_error("Transformation of circuit '%s' failed." % c.name)
        print (e)
        print(traceback.format_exc())
        return (False, 0, 0)

    inputs = c.getInputs()
    outputs = c.getOutputs()
    def validate(sol):
        invalues = dict()
        for i in inputs:
            try:
                invalues[i] = sol[i]
            except KeyError:
                invalues[i] = False
        result = c.simulate(invalues)
        for o in outputs:
            try:
                oval = sol[o]
            except KeyError:
                print_error("Did not find value for output signal '%s' in solution" % o)
                return False
            if oval != result[o]:
                print_error("Inconsistent output value for signal '%s'" % o)
                return False
        return True

    tests = 0
    good = 0
    solutions = allSAT(cnf, c.getInputs())
    while tests < max_tests:
        solution = next(solutions)
        if not solution:
            break
        if validate(solution):
            good += 1
        tests += 1
    return (True, good, tests)

def test_transform(max_tests = 10):
    import transform

    files = filter(lambda f: f.endswith('.crc'), os.listdir('./benchmarks'))
    benchmarks = ['./benchmarks/' + f for f in files]
    all_passed = True
    for bench in benchmarks:
        print_info("Testing transformation of circuit '%s'" % bench)
        b,i,j = check(bench, max_tests)
        all_passed = b and (i == j) and all_passed
    return all_passed

# =============================================================================
# Test code for equivalence checker
# =============================================================================

def check_ec(c1, c2, result):
    r, cex  = ec.check(c1, c2)
    if r:
        print_result("Circuits are EQUIVALENT")
    else:
        print_result("Circuits are DIFFERENT")
    if r ^ result:
        if result:
            print_error('Circuits are equivalent, but reported different.')
        else:
            print_error('Circuits are different, but reported equivalent.')
    return r == result

def test_ec():
    twoa = circ.parse('benchmarks/twoa.crc')
    twob = circ.parse('benchmarks/twob.crc')

    succ = True
    succ &=  check_ec(twoa, twob, False)
    succ &=  check_ec(twob, twoa, False)

    adder1 = circ.parse('benchmarks/fa.crc')
    adder2 = circ.parse('benchmarks/fa2.crc')
    adder3 = circ.parse('benchmarks/fa3.crc')
    adder4 = circ.parse('benchmarks/fa4.crc')  # faulty adder

    # These should be equivalent
    succ &= check_ec(adder1, adder2, True)
    succ &= check_ec(adder2, adder3, True)
    succ &= check_ec(adder1, adder3, True)

    # Those aren't
    succ &= check_ec(adder1, adder4, False)
    succ &= check_ec(adder2, adder4, False)
    succ &= check_ec(adder3, adder4, False)

    # Those are completely different
    carry_ripple = circ.parse('benchmarks/cra8.crc')
    succ &= check_ec(adder1, carry_ripple, False)

    # That's a bigger one
    cra16 = circ.parse('benchmarks/cra16.crc')
    cla16 = circ.parse('benchmarks/cla16.crc')
    flt16 = circ.parse('benchmarks/faulty16.crc')

    succ &= check_ec(cra16, cla16, True)
    succ &= check_ec(flt16, cla16, False)
    succ &= check_ec(cra16, flt16, False)

    # And the biggest...
    cra32 = circ.parse('benchmarks/cra32.crc')
    cla32 = circ.parse('benchmarks/cla32.crc')
    flt32 = circ.parse('benchmarks/faulty32.crc')

    succ &= check_ec(cra32, cla32, True)
    succ &= check_ec(flt32, cla32, False)
    succ &= check_ec(cra32, flt32, False)

    return succ

# =============================================================================
# Main code
# =============================================================================

if __name__ == '__main__':
    print_info("===========================================")
    print_info("Testing full adder CNF")
    print_info("===========================================")
    try:
        if test_adder():
            print_passed("Congratulations, your adder is correct.")
        else:
            print_error("Some test cases failed, go debug your code.")
    except Exception as e:
        print_error("Something went seriously wrong.")
        print (e)
        print(traceback.format_exc())

    print_info("===========================================")
    print_info("Testing Tseitin transformation")
    print_info("===========================================")
    try:
        if test_transform():
            print_passed("Congratulations, your transformation seems to be correct.")
        else:
            print_error("Some test cases failed, go debug your code.")
    except Exception as e:
        print_error("Something went seriously wrong.")
        print (e)
        print(traceback.format_exc())

    print_info("===========================================")
    print_info("Testing equivalence checker")
    print_info("===========================================")
    try:
        if test_ec():
            print_passed("Congratulations, your equivalence checker seems to be correct.")
        else:
            print_error("Some test cases failed, go debug your code.")
    except Exception as e:
        print_error("Something went seriously wrong.")
        print (e)
        print(traceback.format_exc())

