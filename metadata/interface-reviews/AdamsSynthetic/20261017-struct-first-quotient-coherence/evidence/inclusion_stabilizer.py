"""Independent finite check, NOT a counterexample to Standard.model.

Q = F_2^3 = B + D, B = span(e0), D = span(e1,e2).
In D^b(F_2-vector spaces), Q can be the split cofiber of
0 : D[-1] -> B. These checks concern only this abstract split triangle.
"""
from itertools import product
import json

vectors = list(product((0, 1), repeat=3))
zero = (0, 0, 0)
e0, e1, e2 = (1, 0, 0), (0, 1, 0), (0, 0, 1)


def apply(matrix, vector):
    return tuple(sum(a * b for a, b in zip(row, vector)) % 2
                 for row in matrix)


def inclusion(b):
    return b, 0, 0


def projection(v):
    return v[1], v[2]


all_matrices = [tuple(tuple(bits[3*i+j] for j in range(3))
                      for i in range(3))
                for bits in product((0, 1), repeat=9)]
invertible = [a for a in all_matrices
              if len({apply(a, v) for v in vectors}) == len(vectors)]
stabilizer = [a for a in invertible
              if all(apply(a, inclusion(b)) == inclusion(b) for b in (0, 1))]
move_e1 = [a for a in stabilizer if apply(a, e1) != e1]
both_squares = [a for a in stabilizer
                if all(projection(apply(a, v)) == projection(v) for v in vectors)]
shear = ((1, 1, 0), (0, 1, 0), (0, 0, 1))
assert len(invertible) == 168
assert len(stabilizer) == 24
assert len(move_e1) == 20
assert len(both_squares) == 4
assert shear in both_squares
assert all(apply(shear, apply(shear, v)) == v for v in vectors)
assert apply(shear, e1) == (1, 1, 0) != e1

print(json.dumps({
    "result": "PASS",
    "GL3_F2_order": len(invertible),
    "inclusion_stabilizer_order": len(stabilizer),
    "stabilizer_elements_moving_e1": len(move_e1),
    "inclusion_and_projection_stabilizer_order": len(both_squares),
    "nontrivial_shear": shear,
    "shear_moves_e1_to": apply(shear, e1),
    "evidence_level": "exhaustive finite calculation in an abstract split-cofiber model",
    "limit": "No identification with fixed Standard objects; no target theorem refuted."
}, indent=2))
