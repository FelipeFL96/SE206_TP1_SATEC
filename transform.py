#!/usr/bin/env python3

import sys

import circuit.circuit as circ
from circuit.cnf import SatVar, Solver, Cnf
from circuit.circuit import Circuit
from circuit.circuit import Node
from circuit.circuit import OpNode
from circuit.circuit import UnOp
from circuit.circuit import BinOp
from circuit.circuit import Variable
from circuit.circuit import Literal

# Implementation hints:
#
# 1) For all inputs, outputs, and named signals of the circuit, it is
#    required that the variable names in the CNF are the same as the
#    signal names, i.e. after solving the CNF, it must be possible to
#    obtain the assignment of a circuit signal by indexing the
#    solution with the signal name: a = solution['a']. The variable
#    names for any other internal nodes can be chosen freely.  If a
#    prefix is given, then all variable names must begin with this
#    prefix.
#
# 2) In order to implement the transformation, you will need to
#    traverse the circuit graph for all outputs (and named internal
#    signals). Make sure that you do not forget any of the defined
#    node types. Check the file circuit.py to find out about the
#    possible node types. You can use the function node.getID() in
#    order to obtain a unique identifier for a node.
#
# 3) Test your code! There is a test script named test.py. If your
#    code passes all the tests, there is a good chance that it is
#    correct.

inputs = dict()
outputs = dict()
signals = dict()
internals = dict()

def equals(in1, out) -> Cnf:
    if isinstance(in1, bool):
        if in1:
            return (out)
        else:
            return (~out)
    return (~in1 | out) & (in1 | ~out)

def gate_not(in1, out) -> Cnf:
    if isinstance(in1, bool):
        if in1:
            return (~out)
        else:
            return (out)
    return (~in1|~out) & (in1|out)

def gate_and(in1, in2, out) -> Cnf :
    if isinstance(in1, bool) and isinstance(in2, bool):
        if in1 and in2:
            return (out)
        else:
            return (~out)
    if isinstance(in1, bool):
        if (in1):
            return (~in2|out) & (in2|~out)
        else:
            return (in2|~out) & (~out)
    if isinstance(in2, bool):
        if (in2):
            return (~in1|out) & (in1|~out)
        else:
            return (in1|~out) & (~out)
    return (~in1|~in2|out) & (in1|~out) & (in2|~out)

def gate_or(in1, in2, out) -> Cnf :
    if isinstance(in1, bool) and isinstance(in2, bool):
        if not(in1) and not(in2):
            return (~out)
        else:
            return (out)
    if isinstance(in1, bool):
        if (in1):
            return  (out) & (~in2|out)
        else:
            return (in2|~out) & (~in2|out)
    if isinstance(in2, bool):
        if (in2):
            return (~out) & (~in1|out)
        else:
            return (in1|~out) & (~in1|out)
    return (in1|in2|~out) & (~in1|out) & (~in2|out)

def gate_xor(in1, in2, out) -> Cnf :
    if isinstance(in1, bool) and isinstance(in2, bool):
        if in1 == in2:
            return (~out)
        else:
            return (out)
    if isinstance(in1, bool):
        if (in1):
            return (~in2|~out) & (in2|out)
        else:
            return (in2|~out) & (~in2|out)
    if isinstance(in2, bool):
        if (in2):
            return (~in1|~out) & (in1|out)
        else:
            return (in1|~out) & (~in1|out)
    return (~in1|~in2|~out) & (in1|in2|~out) & (in1|~in2|out) & (~in1|in2|out)

def isLiteral(n: Node, c: Circuit) -> bool:
    if isinstance(n, Literal):
        return True
    elif isinstance(n, Variable):
        if n.getName() in inputs:
            return False
        return isLiteral(c.getEquation(n.getName()), c)
    elif isinstance(n, UnOp):
        return isLiteral(n.getChild(0), c)
    elif isinstance(n, BinOp):
        return isLiteral(n.getChild(0), c) and isLiteral(n.getChild(1), c)

def getLiteralValue(n: Node, c: Circuit) -> bool:
    if isinstance(n, Literal):
        return n.getValue()
    elif isinstance(n, Variable):
        if n.getName() in inputs:
            return False
        return getLiteralValue(c.getEquation(n.getName()), c)
    elif isinstance(n, UnOp):
        return getLiteralValue(n.getChild(0), c)
    elif isinstance(n, BinOp):
        return getLiteralValue(n.getChild(0), c) and getLiteralValue(n.getChild(1), c)

def getSatVar(v: Variable, c: Circuit) -> SatVar:
    if v.getName() in inputs:
        return inputs[v.getName()]
    elif v.getName() in signals:
        if isLiteral(v, c):
            return getLiteralValue(v, c)
        else:
            return signals[v.getName()]


def transform_node(n: Node, out: SatVar, c: Circuit) -> Cnf:
    '''The function transformNode recursively analyses the nodes objects it receives and 
    builds the corresponding CNF. Each step's output is its node's CNF so that the final
    execution has the complete CNF for a given node.
    '''
    cnf = Cnf()

    # Child nodes analysis
    children = []
    for child in n.getChildren():
        if isinstance(child, Literal):
            children.append(child.getValue())
        elif isinstance(child, Variable):
            children.append(getSatVar(child, c))
        elif isinstance(child, OpNode):
            internals[child.getID()] = SatVar('y_' + str(child.getID()))
            children.append(internals[child.getID()])
            cnf = cnf & transform_node(child, internals[child.getID()], c)

    # CNF building for operation nodes
    if len(children) == 2:
        if n.getOp() == '&':
            cnf = cnf & gate_and(children[0], children[1], out)
        elif n.getOp() == '|':
            cnf = cnf & gate_or(children[0], children[1], out)
        elif n.getOp() == '^':
            cnf = cnf & gate_xor(children[0], children[1], out)
    elif len(children) == 1:
        if n.getOp() == '~':
            cnf = cnf & gate_not(children[0], out)
    elif isinstance(n, Variable):
            cnf = cnf & equals(signals[n.getName()], out)

    return cnf

def transform(c: Circuit, prefix: str='') -> Cnf:
    '''The function transform takes a Circuit c and returns a Cnf obtained by the
    Tseitin transformation of c. The optional prefix string will be used for
    all variable names in the Cnf.

    '''
    inputs.clear()
    internals.clear()
    signals.clear()
    solution = Cnf()

    # Filling input dictionary
    for in_str in c.getInputs():
        inputs[in_str] = SatVar(in_str)

    # Filling signals dictionary (outputs and internal signals)
    for sig_str in c.getSignals():
        signals[sig_str] = SatVar(prefix + sig_str)

    # Obtaining the CNFs for each signal (either intern or output)
    for sig_str in c.getSignals():
        node = c.getEquation(sig_str)
        solution = solution & transform_node(node, signals[sig_str], c)

    return solution
    pass

