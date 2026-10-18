module

public import KIP126.AdamsSynthetic.Families
public import Mathlib.Algebra.Module.ZMod

@[expose] section

/-! Actual sphere E₂ operations and designated standard classes.
Squares are products in this same E₂. Nonvanishing is an explicit proposition
at the indices a consumer needs, never a default assumption on the whole family. -/

namespace KIP126.Classical.Adams
open CategoryTheory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]

public noncomputable abbrev ActualE2At (A : ClassicalAdamsFamily C) (p : Bidegree) :=
  A.sphere.Page 2 p

/-- The multiplication and scalar structure on the given family's sphere E₂.
The laws refer to this one product. `HEq` only transports equal degree sums. -/
public structure SphereE2Algebra (A : ClassicalAdamsFamily C) where
  scalar : ∀ p : Bidegree, Module (ZMod 2) (ActualE2At A p)
  product : ∀ p q : Bidegree,
    ActualE2At A p →ₗ[ℤ] ActualE2At A q →ₗ[ℤ] ActualE2At A (p + q)
  unit : ActualE2At A (0, 0)
  assoc : ∀ (p q r : Bidegree) (x : ActualE2At A p) (y : ActualE2At A q)
      (z : ActualE2At A r),
    HEq (product (p + q) r (product p q x y) z)
      (product p (q + r) x (product q r y z))
  unit_left : ∀ (p : Bidegree) (x : ActualE2At A p),
    HEq (product (0, 0) p unit x) x
  unit_right : ∀ (p : Bidegree) (x : ActualE2At A p),
    HEq (product p (0, 0) x unit) x

namespace SphereE2Algebra
variable {A : ClassicalAdamsFamily C}

public theorem product_smul_left (P : SphereE2Algebra A) (p q : Bidegree)
    (a : ZMod 2) (x : ActualE2At A p) (y : ActualE2At A q) :
    letI := P.scalar p
    letI := P.scalar (p + q)
    P.product p q (a • x) y = a • P.product p q x y := by
  letI := P.scalar p
  letI := P.scalar (p + q)
  let f : ActualE2At A p →+ ActualE2At A (p + q) :=
    { toFun := fun z => P.product p q z y
      map_zero' := by simp
      map_add' := by intros; simp }
  exact ZMod.map_smul f a x

public theorem product_smul_right (P : SphereE2Algebra A) (p q : Bidegree)
    (a : ZMod 2) (x : ActualE2At A p) (y : ActualE2At A q) :
    letI := P.scalar q
    letI := P.scalar (p + q)
    P.product p q x (a • y) = a • P.product p q x y := by
  letI := P.scalar q
  letI := P.scalar (p + q)
  exact ZMod.map_smul (P.product p q x) a y
end SphereE2Algebra

public def hiDegree (i : ℕ) : Bidegree := (1, ((2 ^ i : ℕ) : ℤ))

/-- Specified standard classes. Their identification with a source model is a
producer obligation. No dimension or uniqueness condition is silently added. -/
public structure StandardSphereClasses (A : ClassicalAdamsFamily C)
    (_P : SphereE2Algebra A) where
  hi : ∀ i : ℕ, ActualE2At A (hiDegree i)

namespace StandardSphereClasses
variable {A : ClassicalAdamsFamily C} {P : SphereE2Algebra A}

public noncomputable abbrev standardHi (H : StandardSphereClasses A P) (i : ℕ) := H.hi i

public noncomputable def standardHiSquare (H : StandardSphereClasses A P) (i : ℕ) :
    ActualE2At A (2, ((2 ^ (i + 1) : ℕ) : ℤ)) := by
  have hdegree : hiDegree i + hiDegree i = (2, ((2 ^ (i + 1) : ℕ) : ℤ)) := by
    ext <;> simp [hiDegree, pow_succ, mul_two]
  exact (eqToHom (congrArg (ActualE2At A) hdegree))
    (P.product (hiDegree i) (hiDegree i) (H.hi i) (H.hi i))

/-- The square is exactly the same product, transported only along its degree sum. -/
public theorem standardHiSquare_eq_product (H : StandardSphereClasses A P) (i : ℕ)
    (hdegree : hiDegree i + hiDegree i = (2, ((2 ^ (i + 1) : ℕ) : ℤ))) :
    H.standardHiSquare i = (eqToHom (congrArg (ActualE2At A) hdegree))
      (P.product (hiDegree i) (hiDegree i) (H.hi i) (H.hi i)) := rfl

public noncomputable abbrev standardH6 (H : StandardSphereClasses A P) :
    ActualE2At A (1, 64) := H.standardHi 6

public noncomputable abbrev standardH6Square (H : StandardSphereClasses A P) :
    ActualE2At A (2, 128) := H.standardHiSquare 6

public theorem standardH6Square_eq_product (H : StandardSphereClasses A P) :
    H.standardH6Square = P.product (1, 64) (1, 64) H.standardH6 H.standardH6 := rfl

/-- Required nonvanishing at one specified index, for use as an explicit input. -/
public def HiNonzero (H : StandardSphereClasses A P) (i : ℕ) : Prop := H.hi i ≠ 0

/-- Square nonvanishing is separate from the nonvanishing of the factor. -/
public def HiSquareNonzero (H : StandardSphereClasses A P) (i : ℕ) : Prop :=
  H.standardHiSquare i ≠ 0

end StandardSphereClasses
end KIP126.Classical.Adams
