"""Finite F_2 filtered-square stress test; not a spectrum realization.

Coordinate basis i has filtration i, for i=0,1,2. Both target groups
are F_2^3 and target rho is identity. Exhaust all filtered early maps and
all filtered source rho. The late map is forced by commutativity.
The fixed equation is e_0 -> e_2, s=0,n=2,e=0, with q_early=3,q_late=4.
Classical-cycle difference is modeled by exclusion from image(gr rho).
"""
import itertools
import json


def apply(cols, x):
    z = 0
    for i, c in enumerate(cols):
        if (x >> i) & 1:
            z ^= c
    return z


def filtration(x):
    return 3 if x == 0 else (x & -x).bit_length() - 1


filtered_maps = list(itertools.product(range(8), range(0, 8, 2), range(0, 8, 4)))
tested = 0
premise_cases = 0
d_only = c_only = both = 0
failures = []
for early in filtered_maps:
    for rho in filtered_maps:
        tested += 1
        late = tuple(apply(early, r) for r in rho)
        # Same nonzero source leading class, fixed target, both valid equations.
        if rho[0] % 2 == 0 or late[0] != 4 or early[0] != 4:
            continue
        early_corrections = [x for x in (2, 4, 6) if apply(early, x) == 4]
        late_corrections = [x for x in (2, 4, 6) if apply(late, x) == 4]
        if not early_corrections or late_corrections:
            continue
        premise_cases += 1
        # Nonzero leading class is not liftable at its filtration.
        def nonliftable(a):
            return not any(filtration(x) >= a and
                           ((apply(rho, x) >> a) & 1)
                           for x in range(8))
        d = any(nonliftable(filtration(x)) for x in early_corrections)
        # Any nonzero target grade at most n, with higher source.
        c = any(apply(late, x) and filtration(apply(late, x)) <= 2
                for x in (2, 4, 6))
        if d and c:
            both += 1
        elif d:
            d_only += 1
        elif c:
            c_only += 1
        else:
            failures.append({"early": early, "late": late, "rho": rho})

result = {"field": "F2", "coordinate_filtrations": [0, 1, 2],
          "fixed_s_n_e": [0, 2, 0], "quotient_lengths": [3, 4],
          "target_rho": "identity", "filtered_squares_tested": tested,
          "late_essential_early_inessential_cases": premise_cases,
          "D_only": d_only, "C_only": c_only, "both": both,
          "failures": failures,
          "evidence_type": "finite abstract filtered-group computation"}

# A separate C-only control, filtration grades A=(0,1,2), B=(2,3).
# Early: x->y, u->z, v->z+y. Late has x,u and rho is the inclusion.
# The correction u+v has liftable leading term u, but cannot be lifted as
# a whole; v is nonliftable and cannot reach the required target grade 3.
f_early = (2, 1, 3)
f_late = (2, 1)
early_corrections = [x for x in (2, 4, 6) if apply(f_early, x) == 2]
assert early_corrections == [6]
assert filtration(6) == 1  # leading u is liftable
assert apply(f_late, 2) == 1  # crossing u -> z at grade 2
assert not any(apply(f_late, x) == 2 for x in (0, 2))
result["C_only_control"] = {
    "source_grades_early": [0, 1, 2], "source_grades_late": [0, 1],
    "target_grades": [2, 3], "s_n_e": [0, 3, 0],
    "early_columns": f_early, "late_columns": f_late,
    "early_correction": "u+v", "D": False, "C": True,
    "reason": "whole correction nonliftable; leading u liftable; v maps below y"}

print(json.dumps(result, indent=2))
assert not failures
