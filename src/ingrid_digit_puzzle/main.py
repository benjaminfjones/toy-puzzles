"""
Solve the multiplication puzzle:

    x02
     y9
x------
  1abc8

"""
import z3


if __name__ == '__main__':
    solver = z3.Solver()

    x, y, a, b, c = z3.Ints('x y a b c')
    sym_digits = (x, y, a, b, c)
    digit_constraints = [z3.And(0 <= s, s <= 9) for s in sym_digits]

    multiplicant1 = 100*x + 2
    multiplicant2 = 10*y + 9
    product = 10000 + 100*a + 10*b + 8

    solver.add(product == multiplicant1 * multiplicant2, *digit_constraints)
    result = solver.check()
    if result == z3.sat:
        model = solver.model()
        m1 = 100*model[x].as_long() + 2
        m2 = 10*model[y].as_long() + 9
        print(f"{m1} x {m2} = {m1*m2}")
    else:
        print("No solution")
