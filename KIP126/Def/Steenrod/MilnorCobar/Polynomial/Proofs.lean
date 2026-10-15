module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Normalization.Proofs
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Two

@[expose] public section

/-!
# Polynomial preservation and membership proofs

Concatenation and the general coproduct differential preserve normalization
and degree, and the specified representatives are normalized cocycles.
-/

namespace KIP126.Steenrod.Milnor

noncomputable section

open KIP126.Algebra MvPolynomial

/-- The coproduct differential preserves normalization and internal degree. -/
theorem differentialPolynomial_mem (s t : ℕ) (x : cochains s t) :
    IsCochain t (differentialPolynomial s x) := by
  constructor
  · change IsWeightedHomogeneous weight (differentialPolynomial s x.val) t
    simp only [differentialPolynomial, LinearMap.add_apply, LinearMap.sum_apply,
      AlgHom.toLinearMap_apply]
    exact ((homogeneous_rename_slots Fin.succ x.property.1).add
      (homogeneous_rename_slots Fin.castSucc x.property.1)).add
      (IsWeightedHomogeneous.sum Finset.univ (fun slot => splitSlot slot x.val) t
        (fun slot _ => homogeneous_splitSlot slot x.property.1))
  · change differentialPolynomial s x.val ∈
      (⨅ slot : Fin (s + 1), LinearMap.ker (augmentSlot slot).toLinearMap)
    rw [Submodule.mem_iInf]
    intro slot
    exact differentialPolynomial_normalized x.val
      (fun i => (Submodule.mem_iInf _).mp x.property.2 i) slot

/-- Concatenation preserves normalization and adds the two internal degrees. -/
theorem cupPolynomial_mem {s s' t t' : ℕ} (x : cochains s t) (y : cochains s' t') :
    IsCochain (t + t') (cupPolynomial x.val y.val) := by
  constructor
  · exact (homogeneous_rename_slots (Fin.castAdd s') x.property.1).mul
      (homogeneous_rename_slots (Fin.natAdd s) y.property.1)
  · change cupPolynomial x.val y.val ∈
      (⨅ slot : Fin (s + s'), LinearMap.ker (augmentSlot slot).toLinearMap)
    rw [Submodule.mem_iInf]
    intro slot
    refine Fin.addCases (fun i => ?_) (fun i => ?_) slot
    · change augmentSlot (i.castAdd s') (cupPolynomial x.val y.val) = 0
      have hx : augmentSlot i x.val = 0 := (Submodule.mem_iInf _).mp x.property.2 i
      rw [cupPolynomial, map_mul,
        augmentSlot_rename (Fin.castAdd s') (Fin.castAdd_injective s s'), hx, map_zero, zero_mul]
    · change augmentSlot (i.natAdd s) (cupPolynomial x.val y.val) = 0
      have hy : augmentSlot i y.val = 0 := (Submodule.mem_iInf _).mp y.property.2 i
      rw [cupPolynomial, map_mul,
        augmentSlot_rename (Fin.natAdd s) (Fin.natAdd_injective s' s), hy, map_zero, mul_zero]

end

end KIP126.Steenrod.Milnor
