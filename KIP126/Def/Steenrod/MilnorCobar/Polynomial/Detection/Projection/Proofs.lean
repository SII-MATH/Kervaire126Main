module

public import KIP126.Def.Steenrod.MilnorCobar.Polynomial.Detection.Data

@[expose] public section

namespace KIP126.Steenrod.Milnor

noncomputable section
open KIP126.Algebra MvPolynomial
open scoped BigOperators

theorem xiOneProjection_X (s : ℕ) (a : Fin s × ℕ) :
    xiOneProjection s (MvPolynomial.X a) = if a.2 = 0 then MvPolynomial.X a.1 else 0 := by
  simp [xiOneProjection]

theorem xiOneProjection_xi {s : ℕ} (slot : Fin s) (k : ℕ) :
    xiOneProjection s (xi slot k) =
      if k = 0 then 1 else if k = 1 then MvPolynomial.X slot else 0 := by
  cases k with
  | zero => simp [xi]
  | succ k => cases k <;> simp [xi, xiOneProjection_X]

/-- Only ξ₁ and ξ₂ can contribute after projecting both coproduct slots
onto pure ξ₁ powers. Higher generators contribute zero. -/
theorem xiOneProjection_coproductGenerator (j : ℕ) :
    xiOneProjection 2 (coproductGenerator (0 : Fin 1) j) =
      if j = 0 then MvPolynomial.X 0 + MvPolynomial.X 1
      else if j = 1 then MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 else 0 := by
  rcases j with _ | (_ | j)
  · simp [coproductGenerator, Finset.sum_range_succ, xiOneProjection_xi]
  · simp [coproductGenerator, Finset.sum_range_succ, xiOneProjection_xi]
  · simp only [show j + 1 + 1 ≠ 0 by omega, show j + 1 + 1 ≠ 1 by omega, if_false]
    rw [coproductGenerator, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_mul, map_pow, xiOneProjection_xi, xiOneProjection_xi]
    rcases i with _ | (_ | i)
    · simp
    · simp
    · simp

theorem xiOneProjection_split_X (j : ℕ) :
    xiOneProjection 2 (splitSlot (0 : Fin 1) (MvPolynomial.X ((0 : Fin 1), j))) =
      if j = 0 then MvPolynomial.X 0 + MvPolynomial.X 1
      else if j = 1 then MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 else 0 := by
  simpa [splitSlot] using
    xiOneProjection_coproductGenerator j

theorem xiOneProjection_insertLeft (p : TensorPower 1) :
    xiOneProjection 2 (insertLeft 1 p) =
      MvPolynomial.rename (fun _ : Fin 1 => (1 : Fin 2)) (xiOneProjection 1 p) := by
  have h : (xiOneProjection 2).comp (insertLeft 1) =
      (MvPolynomial.rename (fun _ : Fin 1 => (1 : Fin 2))).comp (xiOneProjection 1) := by
    ext ⟨slot, j⟩
    have hs : slot = 0 := Subsingleton.elim _ _
    subst slot
    by_cases hj : j = 0 <;> simp [xiOneProjection, insertLeft, hj]
  exact DFunLike.congr_fun h p

theorem xiOneProjection_insertRight (p : TensorPower 1) :
    xiOneProjection 2 (insertRight 1 p) =
      MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin 2)) (xiOneProjection 1 p) := by
  have h : (xiOneProjection 2).comp (insertRight 1) =
      (MvPolynomial.rename (fun _ : Fin 1 => (0 : Fin 2))).comp (xiOneProjection 1) := by
    ext ⟨slot, j⟩
    have hs : slot = 0 := Subsingleton.elim _ _
    subst slot
    by_cases hj : j = 0 <;> simp [xiOneProjection, insertRight, hj]
  exact DFunLike.congr_fun h p

end
end KIP126.Steenrod.Milnor
