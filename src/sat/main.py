# python
from pysat.solvers import Glucose3
from pypblib import pblib
from pathlib import Path
from typing import List, Dict, Tuple
import re
import sys

# make the project root importable so `from src.model...` works when running this file
project_root = Path(__file__).resolve().parents[2]
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from src.model.rectangle import rectangle
from src.model.position import Position

board: List[List[int]] = []
A_r: Dict[int, List[Position]] = {}
B_ijr: Dict[Tuple[int, int], Dict[int, List[Position]]] = {}
x_ijr: List[List[List[int]]] = []
y_ij: List[List[int]] = []
rectangles: List[rectangle] = []

input_file = Path(__file__).resolve().parents[2] / 'dataset' / 'BoPP_instances' / 'test1' / 'extend_p1.txt'
if not input_file.exists():
    raise FileNotFoundError(f"Input file not found: `{input_file}`. Adjust path or run configuration.")

text = input_file.read_text(encoding='utf-8')
numbers = re.findall(r'-?\d+', text)
if not numbers:
    raise ValueError(f"No integers found in `{input_file}`")

tokens = iter(map(int, numbers))
try:
    m = next(tokens)
    n = next(tokens)
    board = [[next(tokens) for _ in range(n)] for _ in range(m)]
    r = next(tokens)
    for _ in range(r):
        width = next(tokens)
        height = next(tokens)
        cost = next(tokens)
        rectangles.append(rectangle(width, height, cost))
except StopIteration:
    raise ValueError(f"Unexpected end of input while parsing `{input_file}`. File may be malformed.") from None

# 1) Build A_r: all top-left placements where rectangle r fits
for i in range(m):
    for j in range(n):
        for ridx in range(len(rectangles)):
            w = rectangles[ridx].width
            h = rectangles[ridx].height
            if i + h <= m and j + w <= n:
                A_r.setdefault(ridx, []).append(Position(i, j))

# 2) Build B_ijr: for each cell (i,j), which placements (r, pos) cover it
for i in range(m):
    for j in range(n):
        B_ijr[(i, j)] = {}
        for ridx in range(len(rectangles)):
            w = rectangles[ridx].width
            h = rectangles[ridx].height
            cov = []
            for pos in A_r.get(ridx, []):
                x0, y0 = pos.x, pos.y
                if x0 <= i < x0 + h and y0 <= j < y0 + w:
                    cov.append(Position(x0, y0))
            if cov:
                B_ijr[(i, j)][ridx] = cov

# 3) Allocate SAT variables
# x_ijr[i][j][r] = var id for "place rect r at (i,j)"
x_ijr = [[[0 for _ in range(len(rectangles))] for _ in range(n)] for _ in range(m)]
# y_ij[i][j] = var id for "cell (i,j) is covered"
y_ij = [[0 for _ in range(n)] for _ in range(m)]

var_count = 1
for ridx in range(len(rectangles)):
    for pos in A_r.get(ridx, []):
        i, j = pos.x, pos.y
        x_ijr[i][j][ridx] = var_count
        var_count += 1

for i in range(m):
    for j in range(n):
        y_ij[i][j] = var_count
        var_count += 1

# 4) Create solver and PBLib encoder (correct API usage)
solver = Glucose3()
# REPLACED: use simple interface with plain lists and track next free variable
formula: List[List[int]] = []
next_free_var = var_count

# CNF: at most one placement per rectangle (pairwise)
for r in range(len(rectangles)):
    placements = [
        x_ijr[pos.x][pos.y][r]
        for pos in A_r.get(r, [])
        if x_ijr[pos.x][pos.y][r] != 0
    ]
    for a in range(len(placements)):
        for b in range(a + 1, len(placements)):
            solver.add_clause([-placements[a], -placements[b]])

# 5) Encode constraints with PBLib

# For each (i,j) with board[i][j] > 0:
# sum(covering_vars) + (¬y_ij) >= 1
for i in range(m):
    for j in range(n):
        if board[i][j] > 0:
            lits: List[int] = []
            coefs: List[int] = []
            # add covering x vars (only non-zero ids)
            for ridx, pos_list in B_ijr.get((i, j), {}).items():
                for pos in pos_list:
                    u, v = pos.x, pos.y
                    x_var = x_ijr[u][v][ridx]
                    if x_var != 0:
                        lits.append(x_var)   # x_uvr
                        coefs.append(1)
            # add ¬y_ij
            y_var = y_ij[i][j]
            lits.append(-y_var)
            coefs.append(1)

            if lits:  # avoid empty PB
                # simple interface: encode_geq(weights, literals, k, formula, first_free_variable) -> next_free_variable
                next_free_var = pblib.encode_geq(coefs, lits, 1, formula, next_free_var)

# For each (i,j) with board[i][j] < 0:
# for every covering x_uvr: (¬x_uvr + y_ij) >= 1  i.e., x_uvr -> y_ij
for i in range(m):
    for j in range(n):
        if board[i][j] < 0:
            y_var = y_ij[i][j]
            for ridx, pos_list in B_ijr.get((i, j), {}).items():
                for pos in pos_list:
                    u, v = pos.x, pos.y
                    x_var = x_ijr[u][v][ridx]
                    if x_var != 0:
                        next_free_var = pblib.encode_geq([1, 1], [-x_var, y_var], 1, formula, next_free_var)

# 6) Add all encoded clauses to the SAT solver (via get_clauses)
# REPLACED: 'formula' is a plain list of clauses
for clause in formula:
    solver.add_clause(clause)

# 7) Solve and print model
if solver.solve():
    print("SAT")
    model = solver.get_model()
    pos = set(v for v in model if v > 0)

    print("\nPlaced rectangles:")
    for ridx in range(len(rectangles)):
        for pos0 in A_r.get(ridx, []):
            i, j = pos0.x, pos0.y
            var = x_ijr[i][j][ridx]
            if var in pos:
                print(f"Rectangle {ridx} (w={rectangles[ridx].width}, h={rectangles[ridx].height}) at ({i},{j})")

    print("\nCovered positions:")
    for i in range(m):
        for j in range(n):
            if y_ij[i][j] in pos:
                print(f"Position ({i},{j}) covered")
else:
    print("UNSAT")
