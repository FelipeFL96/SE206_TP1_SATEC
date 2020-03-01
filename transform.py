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

def equivalent(in1: SatVar, out: SatVar) -> Cnf:
    return (~in1 | out) & (in1 | ~out)

def gate_not(in1: SatVar, out: SatVar) -> Cnf:
    return (~in1|~out) & (in1|out)

def gate_and(in1: SatVar, in2: SatVar, out: SatVar) -> Cnf:
    return (~in1|~in2|out) & (in1|~out) & (in2|~out)

def gate_or(in1: SatVar, in2: SatVar, out: SatVar) -> Cnf:
    return (in1|in2|~out) & (~in1|out) & (~in2|out)

def gate_xor(in1: SatVar, in2: SatVar, out: SatVar) -> Cnf:
    return (~in1|~in2|~out) & (in1|in2|~out) & (in1|~in2|out) & (~in1|in2|out)

def transform_node(n: Node, out: SatVar, c: Circuit) -> Cnf:
    '''The function transformNode recursively analyses the nodes objects it receives and 
    builds the corresponding CNF. Each step's output is its node's CNF so that the final
    execution has the complete CNF for a given node.
    '''
    cnf = Cnf()

    # Child nodes analysis for operation nodes
    children = []
    for child in n.getChildren():
        if isinstance(child, Literal):
            lit = SatVar('l_' + str(child.getID()))
            children.append(lit)
            if child.getValue() == True:
                cnf &= lit
            else:
                cnf &= ~lit
        elif isinstance(child, Variable):
            if child.getName() in inputs:
                var = inputs[child.getName()]
            elif child.getName() in signals:
                var = signals[child.getName()]
            children.append(var)
        elif isinstance(child, OpNode):
            internal = SatVar('y_' + str(child.getID()))
            children.append(internal)
            cnf &= transform_node(child, internal, c)

    # CNF building
    if isinstance(n, OpNode):
        if len(children) == 1:
            if n.getOp() == '~':
                cnf &= gate_not(children[0], out)
        elif len(children) == 2:
            if n.getOp() == '&':
                cnf &= gate_and(children[0], children[1], out)
            elif n.getOp() == '|':
                cnf &= gate_or(children[0], children[1], out)
            elif n.getOp() == '^':
                cnf &= gate_xor(children[0], children[1], out)
    elif isinstance(n, Variable):
            cnf &= equivalent(signals[n.getName()], out)
    elif isinstance(n, Literal):
            lit = SatVar('l_' + str(n.getID()))
            cnf &= equivalent(lit, out)
            if n.getValue() == True:
                cnf &= lit
            else:
                cnf &= ~lit

    return cnf

def transform(c: Circuit, prefix: str='') -> Cnf:
    '''The function transform takes a Circuit c and returns a Cnf obtained by the
    Tseitin transformation of c. The optional prefix string will be used for
    all variable names in the Cnf.

    '''
    inputs.clear()
    signals.clear()
    solution = Cnf()

    # Filling input dictionary
    for in_str in c.getInputs():
        inputs[in_str] = SatVar(prefix + in_str)

    # Filling signals dictionary (outputs and internal signals)
    for sig_str in c.getSignals():
        signals[sig_str] = SatVar(prefix + sig_str)

    # Obtaining the CNFs for each signal (either intern or output)
    for sig_str in c.getSignals():
        node = c.getEquation(sig_str)
        solution = solution & transform_node(node, signals[sig_str], c)

    return solution
    pass

