#!/usr/bin/env python3
from parser import parse_file, test_to_bmc
from rich import print
from rich.panel import Panel
from bmc import BMC
from goto import *
import re
from collections import defaultdict
from rich.console import Console

import os
import sys

def split_path(file_path):
    dirpath, filename = os.path.split(file_path)
    return dirpath, filename

if len(sys.argv) != 2:
    print("Usage: python proofcov.py <path_to_file>")
    sys.exit(1)

file_path = sys.argv[1]
dirpath, filename = split_path(file_path)

print("Opening file", dirpath + "/" + filename)
tests = parse_file(filename, dirpath)
# We assume all tests test the same file
test_files = set(list(map(lambda t : t.input_file, tests)))
assert(len(test_files) == 1)
input_file = test_files.pop()
all_lines = set()
all_subexprs = set()
all_nodes = defaultdict(set)
# TODO: currently we extract annotated nodes during each run, but it only has to
# be done once. Since every test should work over the same #INPUT they should
# have the same annotated nodes
annotated_nodes = []

COVCOL = '[dodger_blue1]'
NORCOL = '[bright_black1]'
COVCOL = '[red]'
NORCOL = '[dodger_blue1]'

def color_annotated(node, subexprs, above_covered=False, top_level=False):
    if isinstance(node, BinOp):
        p = r"subexpr_(\d+)_(\d+)"
        r = re.match(p, node.subexpr)
        t = (int(r[1]), int(r[2]))
        c = t in subexprs
        lhsstr, lhsc, wrap1 = color_annotated(node.lhs, subexprs, c)
        rhsstr, rhsc, wrap2 = color_annotated(node.rhs, subexprs, c)

        if c:
            opstr = f'{COVCOL}{node.op}{NORCOL}'
        else:
            opstr = f'{node.op}'


        # if c:
        if top_level:
            return lhsstr + " " + opstr + " " + rhsstr
        if not wrap1 and not wrap2:
            return lhsstr + " " + opstr + " " + rhsstr, c, True

        if c:
            return f"{COVCOL}({NORCOL}" + lhsstr + " " + opstr + " " + rhsstr + f"{COVCOL}){NORCOL}", c, True
        else:
            return f"{NORCOL}(" + lhsstr + " " + opstr + " " + rhsstr + f"{NORCOL})", c, True
        # else:
            # return "(" + lhsstr + " [dodger_blue1]" + node.op + " [bright_black1]" + rhsstr + ")"
    elif isinstance(node, Var):
        name = node.name
        root = name.split(".")[0]
        if above_covered:
            return f'{COVCOL}{root}{NORCOL}', above_covered, False
        else:
            return "[bright_black1]" + root, above_covered, False

    elif isinstance(node, Constant):
        if above_covered:
            return "[red]" + str(node), above_covered, False
        else:
            return "[bright_black1]" + str(node), above_covered, False
    else:
        assert(False)




def color_annotated2(node, subexprs, above_covered=False, top_level=False):
    if isinstance(node, BinOp):
        p = r"subexpr_(\d+)_(\d+)"
        r = re.match(p, node.subexpr)
        t = int(r[2])
        c = t in subexprs
        lhsstr, lhsc, wrap1 = color_annotated2(node.lhs, subexprs, c)
        rhsstr, rhsc, wrap2 = color_annotated2(node.rhs, subexprs, c)

        if c:
            opstr = f'{COVCOL}{node.op}{NORCOL}'
        else:
            opstr = f'{node.op}'


        # if c:
        if top_level:
            return lhsstr + " " + opstr + " " + rhsstr
        if not wrap1 and not wrap2:
            return lhsstr + " " + opstr + " " + rhsstr, c, True

        if c:
            return f"{COVCOL}({NORCOL}" + lhsstr + " " + opstr + " " + rhsstr + f"{COVCOL}){NORCOL}", c, True
        else:
            return f"{NORCOL}(" + lhsstr + " " + opstr + " " + rhsstr + f"{NORCOL})", c, True
        # else:
            # return "(" + lhsstr + " [dodger_blue1]" + node.op + " [bright_black1]" + rhsstr + ")"
    elif isinstance(node, Var):
        name = node.name
        root = name.split(".")[0]
        if above_covered:
            return f'{COVCOL}{root}{NORCOL}', above_covered, False
        else:
            return "[bright_black1]" + root, above_covered, False

    elif isinstance(node, Constant):
        if above_covered:
            return "[red]" + str(node), above_covered, False
        else:
            return "[bright_black1]" + str(node), above_covered, False
    else:
        assert(False)

console = Console()
for t in tests:
    console.clear()
    formula, annotated_nodes = test_to_bmc(t)
    input()
    # assert(len(annotated_nodes) == 1)
    # print(formula)
    sat = BMC.check_sat(formula)
    if (sat):
        print("Test [red]fail")
        # BMC.get_model(formula)
    else:
        node_src_lines = list(map(lambda x : x[1], annotated_nodes))
        nodes = list(map(lambda x : x[0], annotated_nodes))
        for (an, al) in annotated_nodes:
            all_nodes[al-t.input_begin + 1].add(an)
        print("Test [green]pass")
        result = BMC.get_core(formula)
        lines = []
        subexprs = []
        for x in result:
            if isinstance(x, tuple):
                (l, subexpr) = x
                subexprs.append(x)
                all_subexprs.add((l - t.input_begin + 1, subexpr))
            else:
                lines.append(x)

        for l in lines:
            if t.input_begin <= l and l < t.input_begin + t.input_length:
                all_lines.add(l - t.input_begin)
        core = list(lines)
        core.sort()
        core = list(map(str, core))
        core2 = list(subexprs)
        core2.sort()
        core2 = list(map(str, subexprs))
        print(Panel.fit(', '.join(core), title="Used Lines"))
        print(Panel.fit(', '.join(core2), title="Used Subexpressions"))

        f = t.code.split('\n')
        s = ""
        num_digits = len(str(len(f)))
        for n, l in enumerate(f):
            lineno = f"[white]{n+1:0{num_digits}}:  "
            #Treat annotated lines:

            if n+1 in node_src_lines:
                i = node_src_lines.index(n+1)
                ca = color_annotated(nodes[i], subexprs, top_level=True)
                #TODO: this probably only works for if (foo) {  } else { }
                s += lineno + '[bright_black]if ' + ca + ' [bright_black]{\n'
            elif (n+1) in lines:
                s += lineno + "[dodger_blue1]" + l + '\n'
            else:
                s += lineno + "[bright_black]" + l + '\n'
        input()
        print(Panel(s, title="Coverage"))
        input()




all_lines = list(all_lines)
all_lines.sort()
fin = open(dirpath + '/' + input_file, 'r')
s = ""
from collections import defaultdict
subexpr_lines = defaultdict(set)
for l, x in all_subexprs:
    subexpr_lines[l].add(x)


for n, l in enumerate(fin.readlines()):
    if n+1 in subexpr_lines:
        node = all_nodes[n+1].pop() # TODO: we pick just one of the nodes
        # i = node_src_lines.index(n+1)
        ca = color_annotated2(node, subexpr_lines[n+1], top_level=True)
        #TODO: this probably only works for if (foo) {  } else { }
        s += '[bright_black]if ' + ca + ' [bright_black]{\n'
    elif (n) in all_lines:
        s += "[dodger_blue1]" + l
    else:
        s += "[bright_black]" + l

print("\n\n")
print(Panel(s, title="Combined Coverage for " + input_file))
