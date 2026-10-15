module

public import KIP126.Def.SpectralSequence.Crossing.Proofs
public import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Page.Converse.Proofs

@[expose] public section

/-!
# 过滤复形的代表元 crossing

本文件把有限页的商页微分关系恢复为严格过滤代表元关系，
并证明同一源的两个不同目标代表元必然产生精确 crossing。
-/

namespace KIP126.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredComplex

/-- 第零页的边缘没有非零广义元素。 -/
theorem boundary_zero_apply (FC : FilteredComplex C)
    (s k : ℤ) {T : C} [Projective T]
    {v : T ⟶ FC.assocGraded s (k - 1)}
    (hv : Subobject.Factors (FC.boundarySubobject s (k - 1) 0) v) :
    v = 0 := by
  have htmp := FC.lift_boundary s (k - 1) 0 hv
  rw [show s - (↑(0 : ℕ) : ℤ) + 1 = s + 1 by omega] at htmp
  obtain ⟨a₀, b, hdb₀, hbb⟩ := htmp
  let e : Subobject.underlying.obj (FC.fil (s + 1) k) =
      Subobject.underlying.obj (FC.fil (s + 1) (k - 1 + 1)) := by
    rw [show k - 1 + 1 = k by omega]
  let a := a₀ ≫ eqToHom e.symm
  have he : eqToHom e ≫
      ((FC.fil (s + 1) (k - 1 + 1)).arrow ≫ FC.dToK (k - 1)) =
      (FC.fil (s + 1) k).arrow ≫ FC.d k := by
    have htransport : ∀ {i j : ℤ} (h : i = j),
        eqToHom (congrArg
          (fun q => Subobject.underlying.obj (FC.fil (s + 1) q)) h) ≫
          ((FC.fil (s + 1) j).arrow ≫ FC.complex.d j (k - 1)) =
        (FC.fil (s + 1) i).arrow ≫ FC.complex.d i (k - 1) := by
      intro i j h
      subst j
      simp
    have hk : k = k - 1 + 1 := by omega
    have heq : e = congrArg
        (fun q => Subobject.underlying.obj (FC.fil (s + 1) q)) hk :=
      Subsingleton.elim _ _
    rw [heq]
    simpa only [FilteredComplex.dToK, FilteredComplex.d] using htransport hk
  have hc : (a₀ ≫ eqToHom e.symm) ≫ eqToHom e = a₀ := by
    rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have hdb : a ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k =
      b ≫ (FC.fil s (k - 1)).arrow := by
    calc
      a ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k =
          a ≫ (eqToHom e ≫
            ((FC.fil (s + 1) (k - 1 + 1)).arrow ≫ FC.dToK (k - 1))) := by
              rw [he]
      _ = a₀ ≫ (FC.fil (s + 1) (k - 1 + 1)).arrow ≫ FC.dToK (k - 1) := by
        simp only [a, ← Category.assoc]
        rw [hc]
      _ = b ≫ (FC.fil s (k - 1)).arrow := hdb₀
  let j := Subobject.ofLE (FC.fil (s + 1) (k - 1))
    (FC.fil s (k - 1)) (FC.fil_anti s (k - 1))
  let c := a ≫ FC.filDiff (s + 1) k
  have hbc : b = c ≫ j := by
    apply (cancel_mono (FC.fil s (k - 1)).arrow).mp
    calc
      b ≫ (FC.fil s (k - 1)).arrow =
          a ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k := hdb.symm
      _ = c ≫ (FC.fil (s + 1) (k - 1)).arrow := by
        simp only [c, Category.assoc, filDiff, fil, d,
          (FC.differential_preserves (s + 1) k).choose_spec]
      _ = (c ≫ j) ≫ (FC.fil s (k - 1)).arrow := by
        simp only [Category.assoc, j, Subobject.ofLE_arrow]
  calc
    v = b ≫ FC.filToAssocGraded s (k - 1) := hbb.symm
    _ = c ≫ j ≫ FC.filToAssocGraded s (k - 1) := by
      simp only [hbc, Category.assoc]
    _ = 0 := by
      have hj : j ≫ FC.filToAssocGraded s (k - 1) = 0 := by
        dsimp only [j, FilteredComplex.filToAssocGraded]
        exact cokernel.condition _
      rw [hj, comp_zero]

/-- 若严格过滤微分的目标在相应页不是边缘，则它给出本质微分关系。 -/
theorem essentialRelation_of_filtered_lift
    (FC : FilteredComplex C) (bnd : FC.IsBounded)
    (t p k : ℤ) (m : ℕ) (ht : t + ↑m = p) {T : C} [Projective T]
    (a : T ⟶ Subobject.underlying.obj (FC.fil t k))
    (b : T ⟶ Subobject.underlying.obj (FC.fil p (k - 1)))
    (hdb : a ≫ (FC.fil t k).arrow ≫ FC.d k =
      b ≫ (FC.fil p (k - 1)).arrow)
    (hn : ¬ Subobject.Factors (FC.boundarySubobject p (k - 1) (↑m))
      (b ≫ FC.filToAssocGraded p (k - 1))) :
    EssentialDifferentialRelation (FC.toSpectralSequence bnd)
        (↑m) ⟨t, k⟩
        (Eq.mpr (congrArg (fun X : C => T ⟶ X)
          (show (((FC.toSpectralSequence bnd).ssData ⟨t, k⟩).V =
            FC.assocGraded t k) from rfl)) (a ≫ FC.filToAssocGraded t k))
        (Eq.mpr (congrArg (fun X : C => T ⟶ X)
          (show (((FC.toSpectralSequence bnd).ssData
            (⟨t, k⟩ + (FC.toSpectralSequence bnd).diffDeg (↑m))).V =
            FC.assocGraded p (k - 1)) by rw [← ht]; rfl))
              (b ≫ FC.filToAssocGraded p (k - 1))) := by
  subst p
  let j := Subobject.ofLE (FC.fil (t + ↑m) (k - 1))
    (FC.fil t (k - 1)) (FC.fil_anti_of_le (k - 1) (by omega))
  have hd : a ≫ FC.filDiff t k = b ≫ j := by
    apply (cancel_mono (FC.fil t (k - 1)).arrow).mp
    calc
      (a ≫ FC.filDiff t k) ≫ (FC.fil t (k - 1)).arrow =
          a ≫ (FC.fil t k).arrow ≫ FC.d k := by
            simp only [Category.assoc, filDiff, fil, d,
              (FC.differential_preserves t k).choose_spec]
      _ = b ≫ (FC.fil (t + ↑m) (k - 1)).arrow := hdb
      _ = (b ≫ j) ≫ (FC.fil t (k - 1)).arrow := by
        simp only [Category.assoc, j, Subobject.ofLE_arrow]
  constructor
  · exact (Solutions.differentialRelation_iff_representativeRelation
      FC bnd m t k _ _).2 ⟨a, b, rfl, rfl, hd⟩
  · change ¬ Subobject.Factors
      (FC.boundarySubobject (t + ↑m) (k - 1) (↑m))
        (b ≫ FC.filToAssocGraded (t + ↑m) (k - 1))
    exact hn

/-- 非零有限页边缘来自更高源过滤层的本质微分。 -/
theorem essential_ancestor_of_nonzero_boundary
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (k : ℤ)
    (m : ℕ) (t p : ℤ) (ht : t + (m : ℤ) = p)
    {T : C} [Projective T]
    (z : T ⟶ FC.assocGraded p (k - 1)) (hz : z ≠ 0)
    (hb : (FC.boundarySubobject p (k - 1) (↑m)).Factors z) :
    ∃ (u : ℤ) (j : ℕ) (huj : u + (j : ℤ) = p)
      (x' : T ⟶ FC.assocGraded u k),
      t < u ∧ EssentialDifferentialRelation (FC.toSpectralSequence bnd)
        (↑j) ⟨u, k⟩
        (Eq.mpr (congrArg (fun X : C => T ⟶ X)
          (show (((FC.toSpectralSequence bnd).ssData ⟨u, k⟩).V =
            FC.assocGraded u k) from rfl)) x')
        (Eq.mpr (congrArg (fun X : C => T ⟶ X)
          (show (((FC.toSpectralSequence bnd).ssData
            (⟨u, k⟩ + (FC.toSpectralSequence bnd).diffDeg (↑j))).V =
            FC.assocGraded p (k - 1)) by rw [← huj]; rfl)) z) := by
  induction m generalizing t p with
  | zero =>
    cases ht
    have hz₀ : z = 0 := by
      simpa only [Int.cast_zero, add_zero] using
        (FC.boundary_zero_apply (t + (0 : ℤ)) k hb)
    exact (hz hz₀).elim
  | succ n ih =>
    cases ht
    obtain ⟨a, b, hdb, hbb⟩ :=
      FC.lift_boundary_at_differential t k (n + 1) hb
    have ht' : (t + 1) + (n : ℤ) = t + ((n + 1 : ℕ) : ℤ) := by omega
    by_cases hbn : (FC.boundarySubobject (t + ((n + 1 : ℕ) : ℤ))
        (k - 1) (↑n)).Factors z
    · obtain ⟨u, j, huj, x', htu, hess⟩ :=
        ih (t + 1) (t + ((n + 1 : ℕ) : ℤ)) ht' z hz hbn
      exact ⟨u, j, huj, x', by omega, hess⟩
    · have hnot : ¬ (FC.boundarySubobject (t + ((n + 1 : ℕ) : ℤ))
          (k - 1) (↑n)).Factors
          (b ≫ FC.filToAssocGraded (t + ((n + 1 : ℕ) : ℤ)) (k - 1)) := by
        rwa [hbb]
      have hess := FC.essentialRelation_of_filtered_lift
        bnd (t + 1) (t + ((n + 1 : ℕ) : ℤ)) k n ht' a b hdb hnot
      rw [hbb] at hess
      exact ⟨t + 1, n, ht', a ≫ FC.filToAssocGraded (t + 1) k,
        by omega, hess⟩

/-- 同一有限页微分的两个不同环境目标代表元产生精确 crossing。 -/
theorem differentialRelation_crossed_of_two_exact
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (n : ℕ) (s k : ℤ) {T : C}
    [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y₁ y₂ : T ⟶ FC.assocGraded (s + ↑n) (k - 1)}
    (h₁ : DifferentialRelation (FC.toSpectralSequence bnd) n ⟨s, k⟩ x y₁)
    (h₂ : DifferentialRelation (FC.toSpectralSequence bnd) n ⟨s, k⟩ x y₂)
    (hne : y₁ ≠ y₂) :
    RelationCrossedByAt (FC.toSpectralSequence bnd)
      (fun q => q.1) n ⟨s, k⟩ x y₁ h₁ := by
  have hdiff : y₁ - y₂ ≠ 0 := sub_ne_zero.mpr hne
  have hboundary := DifferentialRelation.targets_sub_factors_boundary
    (FC.toSpectralSequence bnd) n ⟨s, k⟩ h₁ h₂
  change Subobject.Factors
    (FC.boundarySubobject (s + ↑n) (k - 1) (↑n)) (y₁ - y₂) at hboundary
  obtain ⟨u, j, huj, x', hsu, hess⟩ :=
    FC.essential_ancestor_of_nonzero_boundary bnd k n s (s + ↑n)
      (by rfl) (y₁ - y₂) hdiff hboundary
  refine ⟨u - s, by omega, (↑j), ⟨u, k⟩, _, _, ?_, hess, ?_⟩
  · change u = s + (u - s)
    omega
  · change u + ↑j = s + ↑n
    exact huj

/-- 同一有限页微分的两个不同目标代表元产生 crossing。 -/
theorem differentialRelation_crossed_of_two
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (n : ℕ) (s k : ℤ) {T : C}
    [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y₁ y₂ : T ⟶ FC.assocGraded (s + ↑n) (k - 1)}
    (h₁ : DifferentialRelation (FC.toSpectralSequence bnd) n ⟨s, k⟩ x y₁)
    (h₂ : DifferentialRelation (FC.toSpectralSequence bnd) n ⟨s, k⟩ x y₂)
    (hne : y₁ ≠ y₂) :
    RelationCrossedBy (FC.toSpectralSequence bnd)
      (fun q => q.1) n ⟨s, k⟩ x y₁ h₁ :=
  RelationCrossedByAt.toCrossed _ _ _ _
    (FC.differentialRelation_crossed_of_two_exact bnd n s k h₁ h₂ hne)

/-- 两个严格代表元关系具有不同目标时，其对应的页微分关系产生精确 crossing。 -/
theorem representativeRelation_crossed_of_two_exact
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (n : ℕ) (s k : ℤ) {T : C}
    [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y₁ y₂ : T ⟶ FC.assocGraded (s + ↑n) (k - 1)}
    (h₁ : FC.RepresentativeRelation n (Int.natCast_nonneg n) s k x y₁)
    (h₂ : FC.RepresentativeRelation n (Int.natCast_nonneg n) s k x y₂)
    (hne : y₁ ≠ y₂) :
    RelationCrossedByAt (FC.toSpectralSequence bnd)
      (fun q => q.1) n ⟨s, k⟩ x y₁
        ((Solutions.differentialRelation_iff_representativeRelation
          FC bnd n s k x y₁).2 h₁) := by
  let d₁ := (Solutions.differentialRelation_iff_representativeRelation
    FC bnd n s k x y₁).2 h₁
  let d₂ := (Solutions.differentialRelation_iff_representativeRelation
    FC bnd n s k x y₂).2 h₂
  exact FC.differentialRelation_crossed_of_two_exact bnd n s k d₁ d₂ hne

/-- 两个严格代表元关系具有不同目标时，其对应的页微分关系产生 crossing。 -/
theorem representativeRelation_crossed_of_two
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (n : ℕ) (s k : ℤ) {T : C}
    [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y₁ y₂ : T ⟶ FC.assocGraded (s + ↑n) (k - 1)}
    (h₁ : FC.RepresentativeRelation n (Int.natCast_nonneg n) s k x y₁)
    (h₂ : FC.RepresentativeRelation n (Int.natCast_nonneg n) s k x y₂)
    (hne : y₁ ≠ y₂) :
    RelationCrossedBy (FC.toSpectralSequence bnd)
      (fun q => q.1) n ⟨s, k⟩ x y₁
        ((Solutions.differentialRelation_iff_representativeRelation
          FC bnd n s k x y₁).2 h₁) :=
  RelationCrossedByAt.toCrossed _ _ _ _
    (FC.representativeRelation_crossed_of_two_exact bnd n s k h₁ h₂ hne)

/-- 若一个代表元级微分关系没有 crossing，则同一源的严格目标代表元唯一。 -/
theorem representativeRelation_target_eq_of_not_crossed
    (FC : FilteredComplex C) (bnd : FC.IsBounded) (n : ℕ) (s k : ℤ) {T : C}
    [Projective T]
    {x : T ⟶ FC.assocGraded s k}
    {y₁ y₂ : T ⟶ FC.assocGraded (s + ↑n) (k - 1)}
    (h₁ : FC.RepresentativeRelation n (Int.natCast_nonneg n) s k x y₁)
    (h₂ : FC.RepresentativeRelation n (Int.natCast_nonneg n) s k x y₂)
    (hnc : ¬ RelationCrossedBy (FC.toSpectralSequence bnd)
      (fun q => q.1) n ⟨s, k⟩ x y₁
        ((Solutions.differentialRelation_iff_representativeRelation
          FC bnd n s k x y₁).2 h₁)) :
    y₁ = y₂ := by
  by_contra hne
  exact hnc (FC.representativeRelation_crossed_of_two bnd n s k h₁ h₂ hne)

end FilteredComplex

end KIP126.SpectralSequence
