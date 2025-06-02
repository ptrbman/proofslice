from rich import print
import random

def compute(v1, op, v2):
    if op == '+':
        return v1 + v2
    elif op == '*':
        return v1 * v2
    elif op == '-':
        return v1 - v2
    else:
        assert(False)

def gen_problem(var_count, constraint_count):
    init_vars = [chr(97+i) for i in range(var_count)]
    vs = list(reversed(init_vars))
    print("Variables:", vs)
    values = {}
    for v in vs:
        values[v] = random.randint(0, 5)

    ops = ['+', '-', '*']
    # ops = ['+', '-']

    next_x = 0
    constraints = []

    # header = ["int " + ', '.join(vs) + ';']
    header = []
    result_vars = []

    for i in range(constraint_count):
        result_var = 'x_' + str(i)
        result_vars.append(result_var)
        random.shuffle(vs)
        v1, v2 = vs.pop(), vs.pop()
        op = random.choice(ops)
        result_val = compute(values[v1], op, values[v2])
        values[result_var] = result_val
        constraints.append(result_var + " = " + v1 + " " + op + " " + v2 + ";")
        vs.append(result_var)
    constraints.append("result = " + result_vars[-1] + ';')
    values['result'] = values[result_vars[-1]]
    for v in init_vars:
        header.append(f"int {v} = {values[v]};")
    header.append("int " + ', '.join(result_vars) + ';')
    header.append("int result;")
    return header, constraints, values

header, constraints, values = gen_problem(26, 25)

name = 'arith01'

fcode = open(f'examples/arith/{name}.c', 'w')
ftests = open(f'examples/arith/{name}.tests', 'w')

for c in constraints:
    fcode.write(c + '\n')
fcode.close()

testlines = []
testlines.append('#BEGINTEST')
testlines.append('void test() {')
for h in header:
    testlines.append('\t' + h)
testlines.append(f'\n\t#INPUT {name}.c\n')
testlines.append(f"\t#ASSERT result == {values['result']}")
testlines.append("}")
testlines.append("#ENDTEST")

for t in testlines:
    ftests.write(t + '\n')
ftests.close()

print("[red]Result")
for h in header:
    print(h)

print("\n")
for c in constraints:
    print(c)

print("\nVALUES")
print(values)

print("\n[red]Test")
for t in testlines:
    print(t)
