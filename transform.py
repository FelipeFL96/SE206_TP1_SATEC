#!/usr/bin/env python3

import sys

import circuit.circuit as circ
from circuit.cnf import SatVar, Solver, Cnf
from circuit.circuit import Circuit
from circuit.circuit import Node
from circuit.circuit import OpNode
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

def gate_not(in1, out) -> Cnf:
    return (~in1|~out) & (in1|out)

def gate_and(in1, in2, out) -> Cnf :
    return (~in1|~in2|out) & (in1|~out) & (in2|~out)

def gate_or(in1, in2, out) -> Cnf :
    return (in1|in2|~out) & (~in1|out) & (~in2|out)

def gate_xor(in1, in2, out) -> Cnf :
    return (~in1|~in2|~out) & (in1|in2|~out) & (in1|~in2|out) & (~in1|in2|out)

def getSatVar(v: Variable) -> SatVar:
    if v.getName() in inputs:
        return inputs[v.getName()]
    elif v.getName() in signals:
        return signals[v.getName()]

def transform_node(n: Node, out: SatVar) -> Cnf:
    cnf = Cnf()

    # Obtenção dos nós filhos
    children = []
    for child in n.getChildren():
        if isinstance(child, Variable):
            children.append(getSatVar(child))
        elif isinstance(child, OpNode):
            internals[child.getID()] = SatVar('y_' + str(child.getID()))
            children.append(internals[child.getID()])
            cnf = cnf & transform_node(child, internals[child.getID()])

    # Para operações binárias
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

    return cnf


def transform(c: Circuit, prefix: str='') -> Cnf:
    '''The function transform takes a Circuit c and returns a Cnf obtained by the
    Tseitin transformation of c. The optional prefix string will be used for
    all variable names in the Cnf.

    '''
    inputs.clear()
    outputs.clear()
    internals.clear()
    signals.clear()
    solution = Cnf()

    #Filling input dictionary
    for in_str in c.getInputs():
        inputs[in_str] = SatVar(in_str)

    #Filling signals dictionary
    for sig_str in c.getSignals():
        signals[sig_str] = SatVar(sig_str)

    #Filling output signal dictionary
    for out_str in c.getOutputs():
        outputs[out_str] = SatVar(out_str)

    for out_str in c.getOutputs():
        node = c.getEquation(out_str)
        solution = solution & transform_node(node, outputs[out_str])

    for sig_str in c.getSignals():
        node = c.getEquation(sig_str)
        solution = solution & transform_node(node, signals[sig_str])

    return solution
    pass

