module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Projection.Proofs

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section
open KIP126.Algebra MvPolynomial
open scoped BigOperators

theorem h6SquarePureDetector_apply (p : MvPolynomial (Fin 2) F2) :
    h6SquarePureDetector p = ∑ i ∈ Finset.range 7,
      coeff (Finsupp.single 0 (128 - 2 ^ i) + Finsupp.single 1 (2 ^ i)) p := by
  simp [h6SquarePureDetector]

/-- The seven-term detector does not cancel the specified square. -/
theorem h6SquareDetector_square : h6SquareDetector h6SquareCochain.val = 1 := by
  simp only [h6SquareDetector, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  have hp : xiOneProjection 2 h6SquareCochain.val =
      (MvPolynomial.X 0 : MvPolynomial (Fin 2) F2) ^ 64 * MvPolynomial.X 1 ^ 64 := by
    simp [h6SquareCochain, cup, cupPolynomial, h6Cochain, h6Polynomial, xiOneProjection]
  rw [hp, h6SquarePureDetector_apply]
  norm_num [Finset.sum_range_succ, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul, MvPolynomial.coeff_monomial,
    Finsupp.ext_iff, Fin.forall_fin_two]
  decide

/-- A polynomial supported in one tensor slot is invisible to the detector. -/
theorem h6SquarePureDetector_rename (slot : Fin 2) (p : MvPolynomial (Fin 1) F2) :
    h6SquarePureDetector (MvPolynomial.rename (fun _ : Fin 1 => slot) p) = 0 := by
  rw [h6SquarePureDetector_apply]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i < 7 := Finset.mem_range.mp hi
  have hpos : 0 < 2 ^ i := pow_pos (by decide) _
  have hlt : 2 ^ i < 128 := by
    simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) hi'
  apply MvPolynomial.coeff_rename_eq_zero
  intro d hd
  fin_cases slot
  · have h := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hd
    have hz : d.mapDomain (fun _ : Fin 1 => (0 : Fin 2)) 1 = 0 := by
      exact Finsupp.mapDomain_notin_range (f := fun _ : Fin 1 => (0 : Fin 2)) d 1 (by simp)
    simp [hz] at h
    omega
  · have h := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hd
    have hz : d.mapDomain (fun _ : Fin 1 => (1 : Fin 2)) 0 = 0 := by
      exact Finsupp.mapDomain_notin_range (f := fun _ : Fin 1 => (1 : Fin 2)) d 0 (by simp)
    simp [hz] at h
    omega

/-- Coaugmentation at either end cannot contribute to the detector. -/
theorem h6SquareDetector_insertLeft (p : TensorPower 1) :
    h6SquareDetector (insertLeft 1 p) = 0 := by
  change h6SquarePureDetector (xiOneProjection 2 (insertLeft 1 p)) = 0
  rw [xiOneProjection_insertLeft, h6SquarePureDetector_rename]

theorem h6SquareDetector_insertRight (p : TensorPower 1) :
    h6SquareDetector (insertRight 1 p) = 0 := by
  change h6SquarePureDetector (xiOneProjection 2 (insertRight 1 p)) = 0
  rw [xiOneProjection_insertRight, h6SquarePureDetector_rename]

theorem h6SquareDetector_differential (p : TensorPower 1) :
    h6SquareDetector (differentialPolynomial 1 p) =
      h6SquarePureDetector (xiOneProjection 2 (splitSlot (0 : Fin 1) p)) := by
  simp only [differentialPolynomial, LinearMap.add_apply,
    AlgHom.toLinearMap_apply, map_add, Fin.sum_univ_one,
    h6SquareDetector_insertLeft, h6SquareDetector_insertRight, zero_add]
  rfl

end
end KIP126.Steenrod.Milnor
