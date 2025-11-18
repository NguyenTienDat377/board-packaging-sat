# python

from pysat.solvers import Glucose3, Solver
from pypblib import pblib
from pypblib.pblib import PBConfig, Pb2cnf, WeightedLit
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

enable_kissat = False
all_clauses = []
base_clauses = []  # Store base constraint clauses for reuse
cache_base_clauses = False  # Flag to control caching
id_counter = 0
board: List[List[int]] = []
A_r: Dict[int, List[Position]] = {}
B_ijr: Dict[Tuple[int, int], Dict[int, List[Position]]] = {}
x_ijr: List[List[List[int]]] = []
y_ij: List[List[int]] = []
rectangles: List[rectangle] = []
sat_solver = None  # Will be set during execution

# Scaling factor
SCALING_FACTOR = 1  # p = 1, 2, 3, ...

input_file = Path(__file__).resolve().parents[2] / 'dataset' / 'BoPP_instances' / 'test1' / 'extend_p1.txt'
if not input_file.exists():
    raise FileNotFoundError(f"Input file not found: `{input_file}`. Adjust path or run configuration.")

text = input_file.read_text(encoding='utf-8')
numbers = re.findall(r'-?\d+', text)
if not numbers:
    raise ValueError(f"No integers found in `{input_file}`")

tokens = iter(map(int, numbers))
try:
    m_base = next(tokens)
    n_base = next(tokens)
    board_base = [[next(tokens) for _ in range(n_base)] for _ in range(m_base)]
    r = next(tokens)
    rectangles_base = []
    for _ in range(r):
        width = next(tokens)
        height = next(tokens)
        cost = next(tokens)
        rectangles_base.append(rectangle(width, height, cost))
except StopIteration:
    raise ValueError(f"Unexpected end of input while parsing `{input_file}`. File may be malformed.") from None

p = SCALING_FACTOR
m = m_base * p
n = n_base * p

board = [[0 for _ in range(n)] for _ in range(m)]
for i_base in range(m_base):
    for j_base in range(n_base):
        value = board_base[i_base][j_base]
        # Fill p×p block
        for di in range(p):
            for dj in range(p):
                board[i_base * p + di][j_base * p + dj] = value

for rect_base in rectangles_base:
    scaled_rect = rectangle(
        width=rect_base.width * p,
        height=rect_base.height * p,
        cost=rect_base.cost * (p ** 2)
    )
    rectangles.append(scaled_rect)

def plus_clause(clause):
    sat_solver.add_clause(clause)
    if cache_base_clauses:
        base_clauses.append(clause)
    if enable_kissat:
        all_clauses.append(clause)

def at_most_exactly_one(positions: List[Position], ridx: int):
    n = len(positions)
    for i in range (0, n):
        x1, y1 = positions[i].x, positions[i].y
        for j in range (i + 1, n):
            x2, y2 = positions[j].x, positions[j].y
            plus_clause([-x_ijr[x1][y1][ridx], -x_ijr[x2][y2][ridx]])


def build_Ar():
    for i in range(m):
        for j in range(n):
            for ridx in range(len(rectangles)):
                w = rectangles[ridx].width
                h = rectangles[ridx].height
                if i + h <= m and j + w <= n:
                    A_r.setdefault(ridx, []).append(Position(i, j))

def build_Bijr():
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

def exactly_k(var: List[int], k, type):
    global id_counter

    pbConfig = PBConfig()
    pbConfig.set_PB_Encoder(pblib.PB_BEST)

    pb2 = Pb2cnf(pbConfig)

    formula = []

    weights = [1] * len(var)

    if type == "at_most_k":
        max_var = pb2.encode_at_most_k(weights, var, k, formula, id_counter + 1)
    elif type == "at_least_k":
        max_var = pb2.encode_at_least_k(weights, var, k, formula, id_counter + 1)

    for clause in formula: plus_clause(clause)

    id_counter = max_var

def encode_pb(weights: List[int], lits: List[int], k: int, comparator: str):

    global id_counter

    pbConfig = PBConfig()
    pbConfig.set_PB_Encoder(pblib.PB_BEST)
    pb2 = Pb2cnf(pbConfig)
    formula = []

    if comparator == ">=":
        max_var = pb2.encode_geq(weights, lits, k, formula, id_counter + 1)
    elif comparator == "<=":
        max_var = pb2.encode_leq(weights, lits, k, formula, id_counter + 1)
    else:
        raise ValueError(f"Unknown comparator: {comparator}. Use '>=', '<=', or '=='")

    for clause in formula:
        plus_clause(clause)

    id_counter = max_var



def create_variables():
    global x_ijr, y_ij, id_counter

    x_ijr = [[[0 for _ in range(len(rectangles))] for _ in range(n)] for _ in range(m)]
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

    id_counter = var_count


def at_most_one_rectangle_per_position():
    for ridx in range(len(rectangles)):
        positions = A_r.get(ridx, [])
        at_most_exactly_one(positions, ridx)

def positive_revenue_constraint():
    """
    Constraint (3): y_ij ≤ ∑∑ x_uvr for i ∈ M, j ∈ N : g_ij > 0
    Encoded as: ∑∑ x_uvr - y_ij ≥ 0
    """
    for i in range(m):
        for j in range(n):
            if board[i][j] <= 0:
                continue

            covering_vars = []
            for ridx in B_ijr.get((i, j), {}):
                cov_positions = B_ijr[(i, j)][ridx]
                for pos in cov_positions:
                    x0, y0 = pos.x, pos.y
                    covering_vars.append(x_ijr[x0][y0][ridx])

            if not covering_vars:
                continue

            # Build PB constraint: ∑ x_uvr - y_ij ≥ 0
            # Weights: +1 for each x_uvr, -1 for y_ij
            weights = [1] * len(covering_vars) + [-1]
            lits = covering_vars + [y_ij[i][j]]

            encode_pb(weights, lits, 0, ">=")

def negative_revenue_constraint():
    """
    Constraint (4): |R|·y_ij ≥ ∑∑ x_uvr for i ∈ M, j ∈ N : g_ij < 0
    Encoded as: ∑∑ x_uvr - |R|·y_ij ≤ 0
    """
    R_size = len(rectangles)

    for i in range(m):
        for j in range(n):
            if board[i][j] >= 0:
                continue

            covering_vars = []
            for ridx in B_ijr.get((i, j), {}):
                cov_positions = B_ijr[(i, j)][ridx]
                for pos in cov_positions:
                    x0, y0 = pos.x, pos.y
                    covering_vars.append(x_ijr[x0][y0][ridx])

            if not covering_vars:
                continue

            # Build PB constraint: ∑ x_uvr - |R|·y_ij ≤ 0
            # Weights: +1 for each x_uvr, -|R| for y_ij
            weights = [1] * len(covering_vars) + [-R_size]
            lits = covering_vars + [y_ij[i][j]]

            encode_pb(weights, lits, 0, "<=")


def objective_constraint(min_value: int):
    """
    Add constraint: objective ≥ min_value
    Objective = ∑∑ g_ij*y_ij - ∑∑ c_r*x_ijr

    Encoded as: ∑∑ g_ij*y_ij - ∑∑ c_r*x_ijr ≥ min_value
    """
    weights = []
    lits = []

    # Add revenue terms: g_ij * y_ij
    for i in range(m):
        for j in range(n):
            if board[i][j] != 0:  # Only add non-zero revenue positions
                weights.append(board[i][j])
                lits.append(y_ij[i][j])

    # Add cost terms: -c_r * x_ijr
    for ridx in range(len(rectangles)):
        rect_cost = rectangles[ridx].cost
        for pos in A_r.get(ridx, []):
            i, j = pos.x, pos.y
            weights.append(-rect_cost)
            lits.append(x_ijr[i][j][ridx])

    # Encode: sum(weights * lits) >= min_value
    encode_pb(weights, lits, min_value, ">=")


def calculate_objective(model) -> int:
    if model is None:
        return 0

    revenue = 0
    for i in range(m):
        for j in range(n):
            if y_ij[i][j] in model:
                revenue += board[i][j]

    total_cost = 0
    for ridx in range(len(rectangles)):
        for pos in A_r.get(ridx, []):
            i, j = pos.x, pos.y
            if x_ijr[i][j][ridx] in model:
                total_cost += rectangles[ridx].cost
                break  # Rectangle can only be placed once

    return revenue - total_cost


def print_solution(model):
    """
    Print the solution in a readable format.
    Shows which rectangles are placed and where, plus the board coverage.
    """
    if model is None:
        print("No solution found (UNSAT)")
        return

    print("\n" + "="*60)
    print("SOLUTION FOUND")
    print("="*60)

    # Extract placed rectangles
    placed_rectangles = []
    for ridx in range(len(rectangles)):
        for pos in A_r.get(ridx, []):
            i, j = pos.x, pos.y
            var_id = x_ijr[i][j][ridx]
            if var_id in model:  # Rectangle is placed
                placed_rectangles.append({
                    'ridx': ridx,
                    'position': (i, j),
                    'width': rectangles[ridx].width,
                    'height': rectangles[ridx].height,
                    'cost': rectangles[ridx].cost
                })


    print(f"\nPlaced Rectangles: {len(placed_rectangles)}")
    print("-" * 60)
    for idx, rect in enumerate(placed_rectangles, 1):
        print(f"  {idx}. Rectangle {rect['ridx']} at position ({rect['position'][0]}, {rect['position'][1]}) "
              f"- Size: {rect['height']}x{rect['width']}, Cost: {rect['cost']}")

    visual_board = [[' . ' for _ in range(n)] for _ in range(m)]

    for rect in placed_rectangles:
        ridx = rect['ridx']
        i, j = rect['position']
        h, w = rect['height'], rect['width']

        # Mark the rectangle on the board
        for di in range(h):
            for dj in range(w):
                visual_board[i + di][j + dj] = f' {ridx} '

    print("\nBoard Visualization (numbers = rectangle indices):")
    print("-" * 60)
    print("   ", end="")
    for j in range(n):
        print(f"{j:3}", end="")
    print()

    for i in range(m):
        print(f"{i:2} ", end="")
        for j in range(n):
            print(visual_board[i][j], end="")
        print()

    # Print revenue board
    print("\nRevenue Board:")
    print("-" * 60)
    print("   ", end="")
    for j in range(n):
        print(f"{j:4}", end="")
    print()

    for i in range(m):
        print(f"{i:2} ", end="")
        for j in range(n):
            print(f"{board[i][j]:4}", end="")
        print()

    print("="*60)


def validate_solution(model):
    """
    Validate the solution against all constraints and calculate objective value.
    """
    if model is None:
        print("Cannot validate: No solution found")
        return False

    print("\n" + "="*60)
    print("VALIDATION")
    print("="*60)

    valid = True

    # Extract placed rectangles
    placed_rectangles = []
    for ridx in range(len(rectangles)):
        for pos in A_r.get(ridx, []):
            i, j = pos.x, pos.y
            var_id = x_ijr[i][j][ridx]
            if var_id in model:
                placed_rectangles.append({
                    'ridx': ridx,
                    'position': (i, j),
                    'width': rectangles[ridx].width,
                    'height': rectangles[ridx].height,
                    'cost': rectangles[ridx].cost
                })


    print("\n[Constraint 2] Each rectangle placed at most once:")
    rect_count = {}
    for rect in placed_rectangles:
        ridx = rect['ridx']
        rect_count[ridx] = rect_count.get(ridx, 0) + 1

    constraint2_valid = True
    for ridx, count in rect_count.items():
        if count > 1:
            print(f"  ✗ Rectangle {ridx} placed {count} times (should be ≤ 1)")
            constraint2_valid = False
            valid = False

    if constraint2_valid:
        print("  ✓ All rectangles placed at most once")


    coverage = [[0 for _ in range(n)] for _ in range(m)]
    for rect in placed_rectangles:
        i, j = rect['position']
        h, w = rect['height'], rect['width']
        for di in range(h):
            for dj in range(w):
                coverage[i + di][j + dj] += 1

    y_values = [[False for _ in range(n)] for _ in range(m)]
    for i in range(m):
        for j in range(n):
            var_id = y_ij[i][j]
            if var_id in model:
                y_values[i][j] = True

    print("\n[Constraint 3] Coverage for positive revenue positions:")
    constraint3_valid = True
    for i in range(m):
        for j in range(n):
            if board[i][j] > 0:
                if y_values[i][j] and coverage[i][j] == 0:
                    print(f"  ✗ Position ({i},{j}): y_ij=1 but not covered by any rectangle")
                    constraint3_valid = False
                    valid = False

    if constraint3_valid:
        print("  ✓ All positive revenue positions correctly covered")


    print("\n[Constraint 4] Coverage for negative revenue positions:")
    constraint4_valid = True
    for i in range(m):
        for j in range(n):
            if board[i][j] < 0:
                if coverage[i][j] > 0 and not y_values[i][j]:
                    print(f"  ✗ Position ({i},{j}): covered but y_ij=0")
                    constraint4_valid = False
                    valid = False

    if constraint4_valid:
        print("  ✓ All negative revenue positions correctly handled")


    print("\n" + "-"*60)
    print("OBJECTIVE VALUE CALCULATION:")
    print("-"*60)

    revenue = 0
    for i in range(m):
        for j in range(n):
            if y_values[i][j]:
                revenue += board[i][j]

    total_cost = sum(rect['cost'] for rect in placed_rectangles)
    objective = revenue - total_cost

    print(f"  Revenue from covered positions: {revenue}")
    print(f"  Cost of placed rectangles:      {total_cost}")
    print(f"  Total Objective Value:          {objective}")

    print("\n" + "="*60)
    if valid:
        print("✓ SOLUTION IS VALID")
    else:
        print("✗ SOLUTION HAS VIOLATIONS")
    print("="*60)

    return valid


if __name__ == "__main__":
    print("="*60)
    print("BOARD PACKAGING SAT SOLVER - ITERATIVE OPTIMIZATION")
    print("="*60)
    print(f"Scaling factor p: {p}")
    print(f"Base board size: {m_base} x {n_base}")
    print(f"Scaled board size: {m} x {n}")
    print(f"Number of board positions: {m * n}")
    print(f"Number of rectangles: {len(rectangles)}")
    print(f"Input file: {input_file.name}")
    if p == 1:
        print("Note: Solve p=1 to optimality first to get baseline")
    elif p >= 2:
        theoretical_upper = 244 * (p ** 2)
        print(f"Theoretical upper bound (244*p²): {theoretical_upper}")


    print("\n[1/6] Building A_r (valid positions)...")
    build_Ar()
    total_positions = sum(len(positions) for positions in A_r.values())
    print(f"      Total valid positions: {total_positions}")

    print("[2/6] Building B_ijr (coverage mapping)...")
    build_Bijr()


    print("[3/6] Creating SAT variables...")
    create_variables()
    print(f"      Total variables: {id_counter - 1}")

    print("[4/6] Calculating bounds...")
    # Upper bound: maximum possible revenue (all positive positions)
    max_revenue = sum(board[i][j] for i in range(m) for j in range(n) if board[i][j] > 0)
    min_cost = min(rect.cost for rect in rectangles) if rectangles else 0
    upper_bound = max_revenue
    print(f"      Maximum possible revenue: {max_revenue}")
    print(f"      Upper bound (initial): {upper_bound}")


    print("[5/6] Building base constraints...")
    print("      Encoding base constraints to CNF...")

    cache_base_clauses = True
    sat_solver = Glucose3()
    at_most_one_rectangle_per_position()
    positive_revenue_constraint()
    negative_revenue_constraint()
    cache_base_clauses = False  # Disable caching

    print(f"      Generated {len(base_clauses)} base clauses")

    # Find initial feasible solution
    print("      Finding initial feasible solution...")
    if not sat_solver.solve():
        print("\n" + "="*60)
        print("NO FEASIBLE SOLUTION FOUND (UNSAT)")
        print("="*60)
        print("The problem has no solution even without optimization.")
        exit(1)

    initial_model = sat_solver.get_model()
    lower_bound = calculate_objective(initial_model)
    best_model = initial_model
    best_objective = lower_bound

    print(f"      Initial solution objective: {lower_bound}")
    print(f"      Bounds: LB = {lower_bound}, UB = {upper_bound}")

    print("[6/6] Iterative optimization (reusing base clauses)...")
    iteration = 0
    current_bound = lower_bound + 1  # Try to improve from initial solution

    while current_bound <= upper_bound:
        iteration += 1
        print(f"\n   Iteration {iteration}: Testing objective >= {current_bound}")

        # Create new solver and add stored base clauses (FAST!)
        sat_solver = Glucose3()
        for clause in base_clauses:
            sat_solver.add_clause(clause)

        objective_constraint(current_bound)

        if sat_solver.solve():
            model = sat_solver.get_model()
            obj_value = calculate_objective(model)
            print(f"      ✓ SAT - Found solution with objective = {obj_value}")
            best_model = model
            best_objective = obj_value
            current_bound = obj_value + 1  # Try next value
        else:
            print(f"      ✗ UNSAT - No solution with objective >= {current_bound}")
            print(f"      Optimal solution found!")
            break

    print("\n" + "="*60)
    print(f"OPTIMIZATION COMPLETE")
    print("="*60)
    print(f"Iterations: {iteration}")
    print(f"Optimal objective value: {best_objective}")

    print_solution(best_model)
    validate_solution(best_model)
