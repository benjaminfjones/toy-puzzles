"""
The Heist: https://www.futilitycloset.com/2024/10/23/the-heist/

A puzzle by Jared Z., Nicole H., and Benjamin E., mathematicians at the National Security Agency:

The chief detective hurried down to the police station after hearing big news: there was a heist at Pi National Bank! The police had brought in seven known gang members seen leaving the scene of the crime. They belonged to the nefarious True/False Gang, so named because each member is either required to always tell the truth or required to always lie, although everyone is capable of engaging in wrongdoing. The chief also knew from his past cases that any crime committed by the gang always included one truth teller.

When the chief showed up, he asked the gang members the following questions:

1) Are you guilty?
2) How many of the seven of you are guilty?
3) How many of the seven of you tell the truth?

Here were their responses:

Person 1: Yes; 1; 1
Person 2: Yes; 3; 3
Person 3: No; 2; 2
Person 4: No; 4; 1
Person 5: No; 3; 3
Person 6: No; 3; 3
Person 7: Yes; 2; 2

After looking these answers over, the chief prepared to arrest those responsible.

Which of these seven did the chief arrest?
"""
import itertools
from functools import cache

import z3  # type: ignore

ANSWERS = [
    (True, 1, 1),
    (True, 3, 3),
    (False, 2, 2),
    (False, 4, 1),
    (False, 3, 3),
    (False, 3, 3),
    (True, 2, 2),
]

NUM_SUSPECTS = len(ANSWERS)
SUSPECTS = list(range(NUM_SUSPECTS))

# encode guilty truth values
# g_i := suspect i is guilty
def mk_g() -> tuple[z3.BoolRef]:
  return tuple([z3.Bool(f"g_{i}") for i in range(NUM_SUSPECTS)])

# encode truth teller truth values
# t_i := suspect i is a truth teller
def mk_t() -> tuple[z3.BoolRef]:
    return tuple([z3.Bool(f"t_{i}") for i in range(NUM_SUSPECTS)])

# answer to guilty?
def ag(i):
    return ANSWERS[i][0]

# answer to num guilty
def ang(i):
    return ANSWERS[i][1]

# answer to num truth tellers
def antt(i):
    return ANSWERS[i][2]

@cache
def num_true(g: tuple[z3.BoolRef], k: int) -> z3.BoolRef:
    """
    Return a DNF constraint representing that exactly `k` of the
    propositions in `g` are true.
    """
    assert 0 <= k <= NUM_SUSPECTS
    cs = itertools.combinations(SUSPECTS, k)
    res = z3.BoolVal(False)
    for c in cs:
        lc = list(c)
        conj = z3.And(*[g[i] if i in lc else z3.Not(g[i]) for i in SUSPECTS])
        res = z3.Or(res, conj)
    return res  # type: ignore


# The chief found a solution!
# 
# guilty 0: False
# truth teller 0: False
# 
# guilty 1: True
# truth teller 1: True
# 
# guilty 2: True
# truth teller 2: False
# 
# guilty 3: True
# truth teller 3: False
# 
# guilty 4: False
# truth teller 4: True
# 
# guilty 5: False
# truth teller 5: True
# 
# guilty 6: False
# truth teller 6: False
def main():
    """
    Build constraints and solve the heist
    """
    solver = z3.Solver()
    g = mk_g()
    t = mk_t()


    for i in range(NUM_SUSPECTS):
        # i is a truth teller ==> ag(i) == g_i
        # i is _not_ a truth teller ==> ag(i) == ~g_i
        #
        # E.g. if ag[i],
        # t_i ==> g_i and ~t_i ==> ~g_i
        # This is not equivalent to t_i <==> g_i
        solver.add(z3.Implies(t[i], g[i] if ag(i) else z3.Not(g[i])))
        solver.add(z3.Implies(z3.Not(t[i]), z3.Not(g[i]) if ag(i) else g[i]))

        # Similar constraints for #guilty and #tt
        solver.add(z3.Implies(t[i], num_true(g, ang(i))))
        solver.add(z3.Implies(z3.Not(t[i]), z3.Not(num_true(g, ang(i)))))

        solver.add(z3.Implies(t[i], num_true(t, antt(i))))
        solver.add(z3.Implies(z3.Not(t[i]), z3.Not(num_true(t, antt(i)))))

    res = solver.check()
    if res == z3.sat:
        print("The chief found a solution!")
        m = solver.model()
        for i in SUSPECTS:
            print()
            print(f"guilty {i}: {m[g[i]]}")
            print(f"truth teller {i}: {m[t[i]]}")
    else:
        print("The chief is stumpted.")



if __name__ == "__main__":
    main()
