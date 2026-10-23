module

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.BilinearMap

/-! Native quotient algebra used by the fixed E₂ source; independent of actual pages. -/

@[expose] section
namespace KIP126.Computation.CachedStandard
open CategoryTheory
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private abbrev nativePoly (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

private def nativePolynomialOfPowers (n : ℕ) : List ℕ → nativePoly n
  | [] => 1
  | i :: a :: rest =>
      if h : i < n then
        MvPolynomial.X ⟨i,h⟩ ^ a * nativePolynomialOfPowers n rest
      else 0
  | [_] => 0

private def nativeMonomialOfString (n : ℕ) (s : String) : nativePoly n :=
  if s = "" then 1
  else nativePolynomialOfPowers n ((s.splitOn ",").map (fun i => i.toNat?.getD 0))

private def nativeRelationPolynomial (n : ℕ) (s : String) : nativePoly n :=
  ((s.splitOn ";").map (nativeMonomialOfString n)).sum

private def nativeIdeal (n : ℕ) (codes : List String) : Ideal (nativePoly n) :=
  Ideal.span {p | ∃ code ∈ codes, p = nativeRelationPolynomial n code}

private abbrev nativeAlgebra (n : ℕ) (codes : List String) := nativePoly n ⧸ nativeIdeal n codes

private def nativeProjection (n : ℕ) (codes : List String) :
    nativePoly n →ₐ[ZMod 2] nativeAlgebra n codes := Ideal.Quotient.mkₐ (ZMod 2) (nativeIdeal n codes)

private def nativePart (n : ℕ) (degree : Fin n → ℕ×ℕ) (codes : List String) (s t : ℕ) :
    Submodule (ZMod 2) (nativeAlgebra n codes) :=
  (MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) degree (s,t)).map
    (nativeProjection n codes).toLinearMap

private def nativeComponent (n : ℕ) (degree : Fin n → ℕ×ℕ) (codes : List String) (s t : ℕ) :
    ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) ↥(nativePart n degree codes s t)

private theorem nativeMultiply_mem (n : ℕ) (degree : Fin n → ℕ×ℕ) (codes : List String)
    {s t s' t' : ℕ} {x y : nativeAlgebra n codes}
    (hx : x ∈ nativePart n degree codes s t) (hy : y ∈ nativePart n degree codes s' t') :
    x*y ∈ nativePart n degree codes (s+s') (t+t') := by
  obtain ⟨p,hp,rfl⟩ := hx
  obtain ⟨q,hq,rfl⟩ := hy
  exact ⟨p*q,MvPolynomial.IsWeightedHomogeneous.mul hp hq,map_mul (nativeProjection n codes) p q⟩

private def nativeProduct (n : ℕ) (degree : Fin n → ℕ×ℕ) (codes : List String) (s t s' t' : ℕ) :
    nativeComponent n degree codes s t →ₗ[ZMod 2]
      nativeComponent n degree codes s' t' →ₗ[ZMod 2]
        nativeComponent n degree codes (s+s') (t+t') := by
  refine LinearMap.mk₂ (ZMod 2)
    (fun x y=>⟨x.val*y.val,nativeMultiply_mem n degree codes x.property y.property⟩) ?_ ?_ ?_ ?_
  · intro x x' y
    apply Subtype.ext
    exact add_mul x.val x'.val y.val
  · intro a x y
    apply Subtype.ext
    exact smul_mul_assoc a x.val y.val
  · intro x y y'
    apply Subtype.ext
    exact mul_add x.val y.val y'.val
  · intro a x y
    apply Subtype.ext
    exact mul_smul_comm a x.val y.val

private def nativeUnit (n : ℕ) (degree : Fin n → ℕ×ℕ) (codes : List String) :
    nativeComponent n degree codes 0 0 := by
  refine ⟨1,?_⟩
  apply Submodule.mem_map.mpr
  refine ⟨1,?_,map_one (nativeProjection n codes)⟩
  exact MvPolynomial.isWeightedHomogeneous_one (ZMod 2) degree


end
end KIP126.Computation.CachedStandard
