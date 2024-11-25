"""
Via https://www.futilitycloset.com/2024/11/20/reciprocity-redux/

Originall from Lee Sallows:

> “The above three strips of ten numbers have an intriguing property. They
record how many times each of the decimal digits (shown at left) occur in the
other two strips. Hence the 6 in the left-hand strip identifies the number of
0’s in strips B and C, while the 2 in the centre strip counts the number of 3’s
present in strips A and C. Moreover, the same property holds for every number
in all three strips.”

  | A | B | C
-------------
9 | 0 | 0 | 0
8 | 0 | 0 | 0
7 | 2 | 1 | 1
6 | 0 | 1 | 1
5 | 0 | 0 | 0
4 | 1 | 3 | 2
3 | 4 | 2 | 4
2 | 3 | 3 | 2
1 | 4 | 3 | 3
0 | 6 | 7 | 7

The goal of this program is to produce solutions satisfying the description above.

- Is there more than one solution?
- If so, how many are there?

"""

import itertools

import z3  # type: ignore


def mk_ints(prefix: str, num: int) -> list[z3.ArithRef]:
    return [z3.Int(f"{prefix}_{i}") for i in range(num)]


def exactly(atoms: list[z3.BoolRef], k: int) -> z3.BoolRef:
    """
    Encode the constraint that exactly `k` of the atoms are true.

    This is the naive encoding. We could do better using "pooled", for instance.
    """
    n = len(atoms)
    indices = list(range(n))
    assert 0 <= k < n
    cs = itertools.combinations(indices, k)
    res = z3.BoolVal(False)
    for c in cs:
        lc = list(c)
        conj = z3.And(*[atoms[i] if i in lc else z3.Not(atoms[i]) for i in indices])
        res = z3.Or(res, conj)
    return res  # type: ignore


def main():
    n = 10
    solver = z3.Solver()
    nums = list(range(n))

    # A_i
    a = mk_ints("a", n)
    # A_CNT_i := #{ j | A_j = i }, i.e. the number of a's equal to i
    a_cnt = mk_ints("a_cnt", n)

    b = mk_ints("b", n)
    b_cnt = mk_ints("b_cnt", n)

    c = mk_ints("c", n)
    c_cnt = mk_ints("c_cnt", n)

    # 0 <= A_i < 10
    solver.add([z3.And(0 <= a[i], a[i] <= n-1) for i in nums])
    solver.add([z3.And(0 <= b[i], b[i] <= n-1) for i in nums])
    solver.add([z3.And(0 <= c[i], c[i] <= n-1) for i in nums])

    # A_CNT_i = k <=> Exactly([a[0] == i, ..., a[9] == i], k)
    solver.add([(a_cnt[i] == k) == exactly([a[j] == i for j in nums], k) for i in nums for k in nums])
    solver.add([(b_cnt[i] == k) == exactly([b[j] == i for j in nums], k) for i in nums for k in nums])
    solver.add([(c_cnt[i] == k) == exactly([c[j] == i for j in nums], k) for i in nums for k in nums])

    # A_i = B_CNT_(n-1-i) + C_CNT_(n-i-1)
    solver.add([a[i] == b_cnt[n-1-i] + c_cnt[n-1-i] for i in nums])
    solver.add([b[i] == a_cnt[n-1-i] + c_cnt[n-1-i] for i in nums])
    solver.add([c[i] == a_cnt[n-1-i] + b_cnt[n-1-i] for i in nums])

    smt2_path = "reciprocity.smt2"
    print(f"Writing smt2 {smt2_path}")
    with open(smt2_path, "w") as f:
        f.write(solver.to_smt2())

    res = solver.check()
    if res == z3.sat:
        m = solver.model()
        print("Found a solution!")
        print(f"a = {[m[a[i]] for i in nums]}")
        print(f"b = {[m[b[i]] for i in nums]}")
        print(f"c = {[m[c[i]] for i in nums]}")
    else:
        print("Did not find a solution.")


if __name__ == "__main__":
    main()
