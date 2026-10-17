"""Independent exhaustive coefficient check; no spectrum identification is claimed."""

from itertools import product


def sources(q, a):
    modulus = 2**q
    for x, u, v in product(range(modulus), repeat=3):
        if (8 * v) % modulus == 0 and all(c % 2**a == 0 for c in (x, u, v)):
            yield x, u, v


def image(source, q):
    x, u, v = source
    modulus = 2**q
    return (2 * u + v) % modulus, (8 * x + 2 * v) % modulus


def hits_fixed_target(source, q):
    z, y = image(source, q)
    return z % 16 == 0 and y % 16 == 8


early = [s for s in sources(4, 1) if hits_fixed_target(s, 4)]
late = [s for s in sources(6, 1) if hits_fixed_target(s, 6)]
assert early
assert not late
assert image((0, 14, 4), 4) == (0, 8)
assert image((1, 0, 0), 6) == (0, 8)
print(f"early F1 fixed-target witnesses: {len(early)}")
print(f"late F1 fixed-target witnesses: {len(late)}")

# For a=1,2 the leading v-component is not in the late cycle subgroup.
# Its mod-2 leading coefficient is nonzero, i.e. v/2^a is odd.
for a in (1, 2):
    nonlift = [s for s in sources(4, a) if (s[2] // 2**a) % 2 == 1]
    reaches_F3 = [s for s in nonlift if all(c % 8 == 0 for c in image(s, 4))]
    assert nonlift
    assert not reaches_F3
    print(f"a={a}: nonlift leading witnesses {len(nonlift)}, images in target F3 {len(reaches_F3)}")

assert [a for a in (1, 2, 3) if 4 > 4 - a and 4 <= 6 - a] == [1, 2]
print("a=3: early and late leading cycle groups agree")
print("PASS: conditional finite filtered-group model, not a Lean spectrum counterexample")
