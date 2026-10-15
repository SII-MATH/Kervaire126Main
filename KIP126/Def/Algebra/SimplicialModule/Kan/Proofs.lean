module

public import KIP126.Def.Algebra.SimplicialModule.Kan.Predicates

@[expose] public section

namespace KIP126.Algebra.SimplicialModule

open CategoryTheory Simplicial Opposite

universe u
variable {R : Type u} [Ring R] (A : SimplicialObject (ModuleCat.{u} R))

set_option backward.isDefEq.respectTransparency false

/-- The ascending correction gives exactly the prescribed face. -/
theorem lowerCorrection_face {n : ℕ} (j : Fin (n + 1))
    (x : A.obj (op ⦋n⦌)) (y : A.obj (op ⦋n + 1⦌)) :
    (A.δ j.castSucc).hom (lowerCorrection A j x y) = x := by
  have h := ConcreteCategory.congr_hom (A.δ_comp_σ_self (i := j))
    (x - (A.δ j.castSucc).hom y)
  change (A.δ j.castSucc).hom ((A.σ j).hom _) = x - (A.δ j.castSucc).hom y at h
  rw [lowerCorrection, map_add, h]
  simp

/-- The descending correction gives exactly the prescribed face. -/
theorem upperCorrection_face {n : ℕ} (j : Fin (n + 1))
    (x : A.obj (op ⦋n⦌)) (y : A.obj (op ⦋n + 1⦌)) :
    (A.δ j.succ).hom (upperCorrection A j x y) = x := by
  have h := ConcreteCategory.congr_hom (A.δ_comp_σ_succ (i := j))
    (x - (A.δ j.succ).hom y)
  change (A.δ j.succ).hom ((A.σ j).hom _) = x - (A.δ j.succ).hom y at h
  rw [upperCorrection, map_add, h]
  simp

/-- An ascending correction preserves every earlier face whose residual vanishes. -/
theorem lowerCorrection_preserves_lower {n : ℕ} (j q : Fin (n + 2)) (hq : q < j)
    (x : A.obj (op ⦋n + 1⦌)) (y : A.obj (op ⦋n + 2⦌))
    (hz : (A.δ q).hom (x - (A.δ j.castSucc).hom y) = 0) :
    (A.δ q.castSucc).hom (lowerCorrection A j x y) = (A.δ q.castSucc).hom y := by
  obtain ⟨j,rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hq)
  have hq' : q ≤ j.castSucc := by
    change q.val ≤ j.val
    change q.val < j.val + 1 at hq
    omega
  have h := ConcreteCategory.congr_hom (A.δ_comp_σ_of_le hq')
    (x - (A.δ j.succ.castSucc).hom y)
  change (A.δ q.castSucc).hom ((A.σ j.succ).hom _) = (A.σ j).hom ((A.δ q).hom _) at h
  rw [hz, map_zero] at h
  simp only [lowerCorrection, map_add, h, add_zero]

/-- A descending correction preserves earlier faces when their residual vanishes. -/
theorem upperCorrection_preserves_lower {n : ℕ} (j q : Fin (n + 2)) (hq : q < j)
    (x : A.obj (op ⦋n + 1⦌)) (y : A.obj (op ⦋n + 2⦌))
    (hz : (A.δ q).hom (x - (A.δ j.succ).hom y) = 0) :
    (A.δ q.castSucc).hom (upperCorrection A j x y) = (A.δ q.castSucc).hom y := by
  obtain ⟨j,rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hq)
  have hq' : q ≤ j.castSucc := by
    change q.val ≤ j.val
    change q.val < j.val + 1 at hq
    omega
  have h := ConcreteCategory.congr_hom (A.δ_comp_σ_of_le hq')
    (x - (A.δ j.succ.succ).hom y)
  change (A.δ q.castSucc).hom ((A.σ j.succ).hom _) = (A.σ j).hom ((A.δ q).hom _) at h
  rw [hz, map_zero] at h
  simp only [upperCorrection, map_add, h, add_zero]

/-- A descending correction preserves every later face whose residual vanishes. -/
theorem upperCorrection_preserves_upper {n : ℕ} (j : Fin (n + 2)) (q : Fin (n + 3))
    (hq : j.succ < q)
    (x : A.obj (op ⦋n + 1⦌)) (y : A.obj (op ⦋n + 2⦌))
    (hz : (A.δ (q.pred (Fin.ne_zero_of_lt hq))).hom
      (x - (A.δ j.succ).hom y) = 0) :
    (A.δ q).hom (upperCorrection A j x y) = (A.δ q).hom y := by
  have h := ConcreteCategory.congr_hom (A.δ_comp_σ_of_gt' hq)
    (x - (A.δ j.succ).hom y)
  change (A.δ q).hom ((A.σ j).hom _) = (A.σ _).hom ((A.δ _).hom _) at h
  rw [hz, map_zero] at h
  simp only [upperCorrection, map_add, h, add_zero]



/-- Compatibility makes the residual of a new face vanish on an already
matched earlier face. -/
theorem horn_residual_lower {n : ℕ} {k : Fin (n + 3)}
    {x : Fin (n + 3) → A.obj (op ⦋n + 1⦌)} (hx : HornFacesCompatible A k x)
    (i j : Fin (n + 3)) (hi : i ≠ k) (hj : j ≠ k) (hij : i < j)
    (y : A.obj (op ⦋n + 2⦌)) (hy : (A.δ i).hom y = x i) :
    (A.δ (i.castPred (Fin.ne_last_of_lt hij))).hom (x j - (A.δ j).hom y) = 0 := by
  rw [map_sub, sub_eq_zero, ← hx i j hi hj hij]
  have h : (i.castPred (Fin.ne_last_of_lt hij)).castSucc < j := by simpa using hij
  have hd := ConcreteCategory.congr_hom (A.δ_comp_δ' h) y
  change (A.δ (i.castPred _)).hom ((A.δ j).hom y) =
    (A.δ (j.pred _)).hom ((A.δ (i.castPred _).castSucc).hom y) at hd
  simpa only [Fin.castSucc_castPred, hy] using hd.symm

/-- Compatibility makes the residual of a new face vanish on an already
matched later face. -/
theorem horn_residual_upper {n : ℕ} {k : Fin (n + 3)}
    {x : Fin (n + 3) → A.obj (op ⦋n + 1⦌)} (hx : HornFacesCompatible A k x)
    (i j : Fin (n + 3)) (hi : i ≠ k) (hj : j ≠ k) (hij : i < j)
    (y : A.obj (op ⦋n + 2⦌)) (hy : (A.δ j).hom y = x j) :
    (A.δ (j.pred (Fin.ne_zero_of_lt hij))).hom (x i - (A.δ i).hom y) = 0 := by
  rw [map_sub, sub_eq_zero, hx i j hi hj hij]
  have h : (i.castPred (Fin.ne_last_of_lt hij)).castSucc < j := by simpa using hij
  have hd := ConcreteCategory.congr_hom (A.δ_comp_δ' h) y
  change (A.δ (i.castPred _)).hom ((A.δ j).hom y) =
    (A.δ (j.pred _)).hom ((A.δ (i.castPred _).castSucc).hom y) at hd
  simpa only [Fin.castSucc_castPred, hy] using hd



/-- Successive degeneracy corrections match all faces below a chosen cutoff. -/
theorem horn_lower_prefix {n : ℕ} {k : Fin (n + 3)}
    {x : Fin (n + 3) → A.obj (op ⦋n + 1⦌)} (hx : HornFacesCompatible A k x)
    (m : ℕ) (hm : m ≤ k.val) :
    ∃ y : A.obj (op ⦋n + 2⦌), ∀ q : Fin (n + 3), q.val < m → (A.δ q).hom y = x q := by
  induction m with
  | zero => exact ⟨0,fun q hq => (Nat.not_lt_zero _ hq).elim⟩
  | succ m ih =>
    obtain ⟨y,hy⟩ := ih (by omega)
    let j : Fin (n + 2) := ⟨m,by omega⟩
    refine ⟨lowerCorrection A j (x j.castSucc) y, ?_⟩
    intro q hq
    by_cases he : q.val = m
    · have hqj : q = j.castSucc := Fin.ext he
      subst q
      exact lowerCorrection_face A j _ _
    · have hqm : q.val < m := by omega
      have hqj : q < j.castSucc := hqm
      have hqk : q ≠ k := by intro h; subst q; omega
      have hjk : j.castSucc ≠ k := by
        intro h
        have := congrArg Fin.val h
        change m = k.val at this
        omega
      let q' : Fin (n + 2) := q.castPred (Fin.ne_last_of_lt hqj)
      have hlt : q' < j := hqm
      have hz := horn_residual_lower A hx q j.castSucc hqk hjk hqj y (hy q hqm)
      have h := lowerCorrection_preserves_lower A j q' hlt (x j.castSucc) y hz
      simpa only [q', Fin.castSucc_castPred] using h.trans (hy q hqm)

/-- Compatible horn faces of dimension at least two admit an actual simplex,
constructed by ascending and descending degeneracy corrections. -/
theorem horn_faces_fill {n : ℕ} {k : Fin (n + 3)}
    {x : Fin (n + 3) → A.obj (op ⦋n + 1⦌)} (hx : HornFacesCompatible A k x) :
    ∃ y : A.obj (op ⦋n + 2⦌), ∀ q : Fin (n + 3), q ≠ k → (A.δ q).hom y = x q := by
  have upper (r : ℕ) (hr : r ≤ n + 2 - k.val) :
      ∃ y : A.obj (op ⦋n + 2⦌),
        (∀ q : Fin (n + 3), q.val < k.val → (A.δ q).hom y = x q) ∧
        (∀ q : Fin (n + 3), n + 3 - r ≤ q.val → (A.δ q).hom y = x q) := by
    induction r with
    | zero =>
      obtain ⟨y,hy⟩ := horn_lower_prefix A hx k.val le_rfl
      exact ⟨y,hy,fun q hq => (by omega)⟩
    | succ r ih =>
      obtain ⟨y,hyl,hyu⟩ := ih (by omega)
      let j : Fin (n + 2) := ⟨n + 1 - r,by omega⟩
      have hjval : j.succ.val = n + 2 - r := by dsimp [j]; omega
      have hjk : j.succ ≠ k := by
        intro h
        have := congrArg Fin.val h
        rw [hjval] at this
        omega
      refine ⟨upperCorrection A j (x j.succ) y, ?_, ?_⟩
      · intro q hq
        have hqj : q < j.succ := by change q.val < j.succ.val; rw [hjval]; omega
        have hqk : q ≠ k := by intro h; subst q; omega
        let q' : Fin (n + 2) := q.castPred (Fin.ne_last_of_lt hqj)
        have hlt : q' < j := by change q.val < n + 1 - r; omega
        have hz := horn_residual_lower A hx q j.succ hqk hjk hqj y (hyl q hq)
        have h := upperCorrection_preserves_lower A j q' hlt (x j.succ) y hz
        simpa only [q', Fin.castSucc_castPred] using h.trans (hyl q hq)
      · intro q hq
        by_cases he : q = j.succ
        · subst q
          exact upperCorrection_face A j _ _
        · have hqval : j.succ.val < q.val := by
            rw [hjval]
            have hne : q.val ≠ j.succ.val := fun h => he (Fin.ext h)
            rw [hjval] at hne
            omega
          have hqj : j.succ < q := hqval
          have hqk : q ≠ k := by
            intro h
            subst q
            rw [hjval] at hqval
            omega
          have hyq : (A.δ q).hom y = x q := hyu q (by rw [hjval] at hqval; omega)
          have hz := horn_residual_upper A hx j.succ q hjk hqk hqj y hyq
          exact (upperCorrection_preserves_upper A j q hqj (x j.succ) y hz).trans hyq
  obtain ⟨y,hyl,hyu⟩ := upper (n + 2 - k.val) le_rfl
  refine ⟨y,fun q hq => ?_⟩
  by_cases h : q.val < k.val
  · exact hyl q h
  · exact hyu q (by
      have hne : q.val ≠ k.val := fun he => hq (Fin.ext he)
      omega)

end KIP126.Algebra.SimplicialModule
