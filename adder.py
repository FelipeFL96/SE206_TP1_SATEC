#!/usr/bin/env python3

import circuit.circuit as circ
from circuit.cnf import SatVar, Solver, Cnf

# circ full_adder {
#      inputs: a, b, cin
#      outputs: s, cout
#      s0 = a ^ b
#      s = s0 ^ cin
#      cout = (a & b) | (s0 & cin)
# }

# Inputs
a = SatVar('a')
b = SatVar('b')
cin = SatVar('cin')

# Outputs
s = SatVar('s')
cout = SatVar('cout')

# Internal variables (if needed)
s0 = SatVar('s0')
s1 = SatVar('s1')
s2 = SatVar('s2')

def gate_and(in1, in2, out) -> Cnf :
    return (~in1|~in2|out) & (in1|~out) & (in2|~out)

def gate_or(in1, in2, out) -> Cnf :
    return (in1|in2|~out) & (~in1|out) & (~in2|out)

def gate_xor(in1, in2, out) -> Cnf :
    return (~in1|~in2|~out) & (in1|in2|~out) & (in1|~in2|out) & (~in1|in2|out)


def mk_adder() -> Cnf:
    add1 = gate_xor(a, b ,s0)
    add2 = gate_xor(s0, cin, s)
    add_cnf =  add1 & add2

    carry1 = gate_and(a, b, s1)
    carry2 = gate_and(s0, cin, s2)
    carry3 = gate_or(s1, s2, cout)
    carry_cnf = carry1 & carry2 & carry3

    return add_cnf & carry_cnf
