module

import KIP126.Literature.Standard
import KIP126.AdamsSynthetic.Standard.Filtration
import Mathlib.Data.Fintype.EquivFin
import Mathlib.CategoryTheory.Adjunction.Additive

/-! Object restrictions for actual exponent-sum-one classical triangles.
All statements in this file are private. The argument uses actual HF2
homology maps, finite groups in each degree, and connective tmf; no
quotient horizontal row or Mahowald conclusion is assumed.
-/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

section GenericFiniteGroups
universe u v

private theorem object_cases_same_source_middle_impossible
    {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    [Finite A] [Nontrivial B]
    (f : A →+ A) (g : A →+ B)
    (hi : Function.Injective f) (he : Function.Exact f g)
    (hs : Function.Surjective g) : False := by
  have hfs : Function.Surjective f := Finite.surjective_of_injective hi
  obtain ⟨b, hb⟩ := exists_ne (0 : B)
  obtain ⟨a, ha⟩ := hs b
  obtain ⟨x, hx⟩ := hfs a
  have hzero : g (f x) = 0 := (he (f x)).mpr ⟨x, rfl⟩
  exact hb (by rw [← ha, ← hx]; exact hzero)

private theorem object_cases_same_middle_target_impossible
    {A : Type u} {B : Type v} [AddCommGroup A] [AddCommGroup B]
    [Finite B] [Nontrivial A]
    (f : A →+ B) (g : B →+ B)
    (hi : Function.Injective f) (he : Function.Exact f g)
    (hs : Function.Surjective g) : False := by
  have hgi : Function.Injective g := (Finite.injective_iff_surjective).mpr hs
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have hzero : g (f a) = 0 := (he (f a)).mpr ⟨a, rfl⟩
  have hfzero : f a = 0 := hgi (by simpa only [map_zero] using hzero)
  exact ha (hi (by simpa only [map_zero] using hfzero))

/-- A degreewise finite graded group with a lowest nonzero degree cannot
occur in all three positions of a degreewise short exact sequence of shifts.
No vector-space structure or uniform bound on the cardinalities is assumed. -/
private theorem object_cases_no_three_shifted_short_exact
    (H : ℤ → Type u) [∀ n, AddCommGroup (H n)] [∀ n, Finite (H n)]
    (ell : ℤ) (hnonzero : Nontrivial (H ell))
    (hlow : ∀ n : ℤ, n < ell → Subsingleton (H n))
    (a b c : ℤ)
    (f : ∀ n : ℤ, H (n-a) →+ H (n-b))
    (g : ∀ n : ℤ, H (n-b) →+ H (n-c))
    (hi : ∀ n, Function.Injective (f n))
    (he : ∀ n, Function.Exact (f n) (g n))
    (hs : ∀ n, Function.Surjective (g n)) : False := by
  have hba : b ≤ a := by
    by_contra hh
    have hab : a < b := by omega
    letI : Subsingleton (H (ell+a-b)) := hlow _ (by omega)
    letI : Nontrivial (H (ell+a-a)) := by simpa only [add_sub_cancel_right] using hnonzero
    obtain ⟨x,y,hxy⟩ := exists_pair_ne (H (ell+a-a))
    exact hxy ((hi (ell+a)) (Subsingleton.elim _ _))
  have hbc : b ≤ c := by
    by_contra hh
    have hcb : c < b := by omega
    letI : Subsingleton (H (ell+c-b)) := hlow _ (by omega)
    letI : Nontrivial (H (ell+c-c)) := by simpa only [add_sub_cancel_right] using hnonzero
    obtain ⟨x,y,hxy⟩ := exists_pair_ne (H (ell+c-c))
    obtain ⟨x0,hx⟩ := hs (ell+c) x
    obtain ⟨y0,hy⟩ := hs (ell+c) y
    exact hxy (by rw [←hx, ←hy, Subsingleton.elim x0 y0])
  by_cases hbaeq : b=a
  · subst b
    letI : Nontrivial (H (ell+c-c)) := by simpa only [add_sub_cancel_right] using hnonzero
    exact object_cases_same_source_middle_impossible (f (ell+c)) (g (ell+c))
      (hi _) (he _) (hs _)
  · have hbas : b<a := by omega
    have hbceq : b=c := by
      by_contra hh
      have hbcs : b<c := by omega
      letI : Subsingleton (H (ell+b-a)) := hlow _ (by omega)
      letI : Subsingleton (H (ell+b-c)) := hlow _ (by omega)
      letI : Nontrivial (H (ell+b-b)) := by simpa only [add_sub_cancel_right] using hnonzero
      have hzero : ∀ z : H (ell+b-b), z=0 := by
        intro z
        have hgzero : g (ell+b) z = 0 := Subsingleton.elim _ _
        obtain ⟨x,hx⟩ := (he (ell+b) z).mp hgzero
        rw [←hx, Subsingleton.elim x 0, map_zero]
      obtain ⟨x,y,hxy⟩ := exists_pair_ne (H (ell+b-b))
      exact hxy ((hzero x).trans (hzero y).symm)
    subst c
    letI : Nontrivial (H (ell+a-a)) := by simpa only [add_sub_cancel_right] using hnonzero
    exact object_cases_same_middle_target_impossible (f (ell+a)) (g (ell+a))
      (hi _) (he _) (hs _)

private theorem object_cases_lowest_nontrivial_degree
    (H : ℤ → Type u) [∀ n, AddCommGroup (H n)]
    (hlow : ∀ n : ℤ, n < 0 → Subsingleton (H n))
    (hne : ∃ n : ℤ, Nontrivial (H n)) :
    ∃ ell : ℤ, Nontrivial (H ell) ∧
      ∀ n : ℤ, n < ell → Subsingleton (H n) := by
  classical
  have hnat : ∃ n : ℕ, Nontrivial (H (n:ℤ)) := by
    obtain ⟨n, hn⟩ := hne
    have hn0 : 0 ≤ n := by
      by_contra hh
      letI := hlow n (by omega)
      letI := hn
      obtain ⟨x,y,hxy⟩ := exists_pair_ne (H n)
      exact hxy (Subsingleton.elim _ _)
    exact ⟨n.toNat, by simpa only [Int.toNat_of_nonneg hn0] using hn⟩
  refine ⟨(Nat.find hnat:ℤ), Nat.find_spec hnat, ?_⟩
  intro n hn
  by_cases hnneg : n < 0
  · exact hlow n hnneg
  · have hn0 : 0 ≤ n := by omega
    have hnsmall : n.toNat < Nat.find hnat := by omega
    have hnot := Nat.find_min hnat hnsmall
    have hnnot : ¬ Nontrivial (H n) := by
      simpa only [Int.toNat_of_nonneg hn0] using hnot
    exact not_nontrivial_iff_subsingleton.mp hnnot

private theorem object_cases_no_three_bounded_below_shifted_short_exact
    (H : ℤ → Type u) [∀ n, AddCommGroup (H n)] [∀ n, Finite (H n)]
    (hlow : ∀ n : ℤ, n < 0 → Subsingleton (H n))
    (hne : ∃ n : ℤ, Nontrivial (H n))
    (a b c : ℤ)
    (f : ∀ n : ℤ, H (n-a) →+ H (n-b))
    (g : ∀ n : ℤ, H (n-b) →+ H (n-c))
    (hi : ∀ n, Function.Injective (f n))
    (he : ∀ n, Function.Exact (f n) (g n))
    (hs : ∀ n, Function.Surjective (g n)) : False := by
  obtain ⟨ell, hnz, hmin⟩ := object_cases_lowest_nontrivial_degree H hlow hne
  exact object_cases_no_three_shifted_short_exact H ell hnz hmin a b c f g hi he hs

end GenericFiniteGroups

private theorem object_cases_zero_homology_exponent_one {X Y : Spectrum} (f : X ⟶ Y)
    (hf : ZeroOnModTwoHomology model.coefficients f) :
    normalizedExponent model.classicalTower f = 1 := by
  have hfact : FactorizationFiltration model.coefficients f 1 := by
    intro n hn hle
    have hn1 : n = 1 := by omega
    subst n
    exact AdamsMapFactorization.single f hf
  have hfil : MapFiltrationAtLeast model.classicalTower f 1 := by
    simpa only [MapAdamsFiltration, Int.toNat_one, model] using
      (KIP126.AdamsSynthetic.Standard.factorization_filtration_iff f 1).mp hfact
  classical
  change (if MapFiltrationAtLeast model.classicalTower f 1 then 1 else 0) = 1
  exact if_pos hfil

private theorem object_cases_exponent_zero_has_nonzero_homology {X Y : Spectrum} (f : X ⟶ Y)
    (h0 : normalizedExponent model.classicalTower f = 0) :
    ∃ n : ℤ, ∃ x : ModTwoHomology model.coefficients n X,
      modTwoHomologyMap model.coefficients f n x ≠ 0 := by
  by_contra hh
  have hf : ZeroOnModTwoHomology model.coefficients f := by
    intro n x
    by_contra hx
    exact hh ⟨n, x, hx⟩
  have h1 := object_cases_zero_homology_exponent_one f hf
  omega

private theorem object_cases_source_homology_nontrivial_of_exponent_zero {X Y : Spectrum}
    (f : X ⟶ Y) (h0 : normalizedExponent model.classicalTower f = 0) :
    ∃ n : ℤ, Nontrivial (ModTwoHomology model.coefficients n X) := by
  obtain ⟨n, x, hx⟩ := object_cases_exponent_zero_has_nonzero_homology f h0
  refine ⟨n, ?_⟩
  have hx0 : x ≠ 0 := by
    intro h
    exact hx (by rw [h, map_zero])
  exact ⟨⟨x, 0, hx0⟩⟩

section ExactTransport
universe u

private theorem object_cases_exact_add_equiv
    {A B C A' B' C' : Type u}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    (eA : A ≃+ A') (eB : B ≃+ B') (eC : C ≃+ C')
    (f : A →+ B) (g : B →+ C) (he : Function.Exact f g) :
    Function.Exact
      ((eB.toAddMonoidHom.comp f).comp eA.symm.toAddMonoidHom)
      ((eC.toAddMonoidHom.comp g).comp eB.symm.toAddMonoidHom) := by
  intro y
  change eC (g (eB.symm y)) = 0 ↔
    ∃ x, eB (f (eA.symm x)) = y
  constructor
  · intro hz
    have hgzero : g (eB.symm y) = 0 := eC.injective (by simpa only [map_zero] using hz)
    obtain ⟨x,hx⟩ := (he (eB.symm y)).mp hgzero
    refine ⟨eA x, ?_⟩
    simp only [AddEquiv.symm_apply_apply, hx, AddEquiv.apply_symm_apply]
  · rintro ⟨x,hx⟩
    have hfx : f (eA.symm x) = eB.symm y :=
      eB.injective (by simpa only [AddEquiv.apply_symm_apply] using hx)
    have hgzero : g (eB.symm y) = 0 := (he _).mpr ⟨eA.symm x,hfx⟩
    simp only [hgzero, map_zero]

private theorem object_cases_nontrivial_add_equiv
    {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (hA : Nontrivial A) : Nontrivial B := by
  letI := hA
  obtain ⟨x,y,hxy⟩ := exists_pair_ne A
  exact ⟨⟨e x,e y,fun h => hxy (e.injective h)⟩⟩

end ExactTransport

private theorem object_cases_tmf_homology_bounded_below
    (n : ℤ) (hn : n < 0) :
    Subsingleton (ModTwoHomology model.coefficients n tmf) := by
  have hc : IsConnected tmf (-1) := by
    intro i hi
    exact tmf_connective i (by omega)
  exact connected_homology_vanishing tmf (-1) hc n (by omega)

private theorem object_cases_no_short_exact_three_tmf_shifts
    (T : Triangle Spectrum) (hH : HomologyShortExact model.coefficients T)
    (a b c : ℤ)
    (eX : ∀ n : ℤ, ModTwoHomology model.coefficients n T.obj₁ ≃+
      ModTwoHomology model.coefficients (n-a) tmf)
    (eY : ∀ n : ℤ, ModTwoHomology model.coefficients n T.obj₂ ≃+
      ModTwoHomology model.coefficients (n-b) tmf)
    (eZ : ∀ n : ℤ, ModTwoHomology model.coefficients n T.obj₃ ≃+
      ModTwoHomology model.coefficients (n-c) tmf)
    (hne : ∃ n : ℤ, Nontrivial (ModTwoHomology model.coefficients n tmf)) : False := by
  let H : ℤ → Type := fun n => ModTwoHomology model.coefficients n tmf
  letI : ∀ n : ℤ, Finite (H n) := tmf_finiteModTwoType
  let f : ∀ n : ℤ, H (n-a) →+ H (n-b) := fun n =>
    (((eY n).toAddMonoidHom.comp (modTwoHomologyMap model.coefficients T.mor₁ n)).comp
      (eX n).symm.toAddMonoidHom)
  let g : ∀ n : ℤ, H (n-b) →+ H (n-c) := fun n =>
    (((eZ n).toAddMonoidHom.comp (modTwoHomologyMap model.coefficients T.mor₂ n)).comp
      (eY n).symm.toAddMonoidHom)
  apply object_cases_no_three_bounded_below_shifted_short_exact H
    object_cases_tmf_homology_bounded_below hne a b c f g
  · intro n
    exact (eY n).injective.comp ((hH n).1.comp (eX n).symm.injective)
  · intro n
    exact object_cases_exact_add_equiv (eX n) (eY n) (eZ n) _ _ (hH n).2.1
  · intro n
    exact (eZ n).surjective.comp ((hH n).2.2.comp (eY n).symm.surjective)

private theorem object_cases_factorization_zero_on_homology
    {X Y : Spectrum} {n : ℕ} {f : X ⟶ Y}
    (h : AdamsMapFactorization model.coefficients n f) :
    ZeroOnModTwoHomology model.coefficients f := by
  cases h with
  | single f hf => exact hf
  | prepend f g hf hg =>
      intro i x
      change x ≫ (model.coefficients.object ◁ (f ≫ g)) = 0
      rw [whiskerLeft_comp, ← Category.assoc]
      change modTwoHomologyMap model.coefficients f i x ≫ _ = 0
      rw [hf i x, zero_comp]

private theorem object_cases_normalized_exponent_one_zero_homology
    {X Y : Spectrum} (f : X ⟶ Y)
    (h1 : normalizedExponent model.classicalTower f = 1) :
    ZeroOnModTwoHomology model.coefficients f := by
  have hfil : MapFiltrationAtLeast model.classicalTower f 1 := by
    classical
    by_contra hnot
    change (if MapFiltrationAtLeast model.classicalTower f 1 then 1 else 0) = 1 at h1
    simp only [if_neg hnot] at h1
    contradiction
  have hfact : FactorizationFiltration model.coefficients f 1 :=
    (factorization_filtration_iff f 1).mpr hfil
  exact object_cases_factorization_zero_on_homology (hfact 1 (by decide) (by decide))

private theorem object_cases_zero_on_homology_shift
    {X Y : Spectrum} (f : X ⟶ Y) (k : ℤ)
    (hf : ZeroOnModTwoHomology model.coefficients f) :
    ZeroOnModTwoHomology model.coefficients
      ((shiftFunctor Spectrum k).map f) := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift model.coefficients.object
  let e := (BraidedCategory.tensorLeftIsoTensorRight model.coefficients.object).symm
  letI := Functor.CommShift.ofIso e ℤ
  letI := Functor.CommShift.ofIso_compatibility e ℤ
  let F := tensorLeft model.coefficients.object
  let S := shiftFunctor Spectrum k
  intro n x
  let eS : Sphere (C := Spectrum) n ≅ S.obj (Sphere (n-k)) :=
    (shiftFunctorAdd' Spectrum (n-k) k n (by omega)).app SphereSpectrum
  let b : Sphere (C := Spectrum) (n-k) ⟶ F.obj X :=
    S.preimage (eS.inv ≫ x ≫ (F.commShiftIso k).hom.app X)
  have hb : S.map b = eS.inv ≫ x ≫ (F.commShiftIso k).hom.app X :=
    S.map_preimage _
  have hz : b ≫ F.map f = 0 := hf (n-k) b
  have hs : S.map b ≫ S.map (F.map f) = 0 := by
    rw [← Functor.map_comp, hz, Functor.map_zero]
  rw [hb] at hs
  simp only [Category.assoc] at hs
  rw [← F.commShiftIso_hom_naturality f k] at hs
  change x ≫ F.map (S.map f) = 0
  apply (cancel_mono ((F.commShiftIso k).hom.app Y)).mp
  rw [zero_comp]
  apply (cancel_epi eS.inv).mp
  rw [comp_zero]
  simpa only [Category.assoc] using hs

private theorem object_cases_zero_on_homology_neg
    {X Y : Spectrum} (f : X ⟶ Y)
    (hf : ZeroOnModTwoHomology model.coefficients f) :
    ZeroOnModTwoHomology model.coefficients (-f) := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift model.coefficients.object
  letI := closedBackground.tensorExact model.coefficients.object
  let e := (BraidedCategory.tensorLeftIsoTensorRight model.coefficients.object).symm
  letI := Functor.CommShift.ofIso e ℤ
  letI := Functor.CommShift.ofIso_compatibility e ℤ
  letI := Functor.isTriangulated_of_iso e
  let F := tensorLeft model.coefficients.object
  intro n x
  have hz : x ≫ F.map f = 0 := hf n x
  change x ≫ F.map (-f) = 0
  rw [Functor.map_neg, Preadditive.comp_neg, hz, neg_zero]

private theorem object_cases_homology_short_exact_of_boundary_zero
    (T : Triangle Spectrum) (hT : T ∈ distTriang Spectrum)
    (hz : ZeroOnModTwoHomology model.coefficients T.mor₃) :
    HomologyShortExact model.coefficients T := by
  letI := closedBackground.symmetric
  letI := closedBackground.tensorShift model.coefficients.object
  letI := closedBackground.tensorExact model.coefficients.object
  let e := (BraidedCategory.tensorLeftIsoTensorRight model.coefficients.object).symm
  letI := Functor.CommShift.ofIso e ℤ
  letI := Functor.CommShift.ofIso_compatibility e ℤ
  letI := Functor.isTriangulated_of_iso e
  let F := tensorLeft model.coefficients.object
  let U := F.mapTriangle.obj T
  have hU : U ∈ distTriang Spectrum := F.map_distinguished T hT
  have hu (n : ℤ) (a : HomotopyGroup n U.obj₃) : a ≫ U.mor₃ = 0 := by
    change a ≫ F.map T.mor₃ ≫ _ = 0
    change a ≫ (model.coefficients.object ◁ T.mor₃) ≫ _ = 0
    have hh : a ≫ (model.coefficients.object ◁ T.mor₃) = 0 := hz n a
    rw [← Category.assoc, hh, zero_comp]
  intro n
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (a-b) ≫ U.mor₁ = 0 := by
      change a ≫ U.mor₁ = b ≫ U.mor₁ at hab
      rw [Preadditive.sub_comp, hab, sub_self]
    let S := shiftFunctor Spectrum (1 : ℤ)
    have hh : S.map (a-b) ≫ S.map U.mor₁ = 0 := by
      rw [← Functor.map_comp, hab', Functor.map_zero]
    obtain ⟨d, hd⟩ := U.coyoneda_exact₁ hU (S.map (a-b)) hh
    let eS : Sphere (C := Spectrum) (n+1) ≅ S.obj (Sphere n) :=
      (shiftFunctorAdd' Spectrum n 1 (n+1) rfl).app SphereSpectrum
    have hz' : (eS.hom ≫ d) ≫ U.mor₃ = 0 := hu (n+1) _
    have hd0 : d ≫ U.mor₃ = 0 := (cancel_epi eS.hom).mp
      (by simpa only [Category.assoc, comp_zero] using hz')
    have hs0 : S.map (a-b) = 0 := hd.trans hd0
    have hab0 : a-b = 0 := S.map_injective
      (by simpa only [Functor.map_zero] using hs0)
    exact sub_eq_zero.mp hab0
  · intro a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := U.coyoneda_exact₂ hU a ha
      exact ⟨b, hb.symm⟩
    · rintro ⟨b, rfl⟩
      change (b ≫ U.mor₁) ≫ U.mor₂ = 0
      rw [Category.assoc, comp_distTriang_mor_zero₁₂ U hU, comp_zero]
  · intro a
    obtain ⟨b, hb⟩ := U.coyoneda_exact₃ hU a (hu n a)
    exact ⟨b, hb.symm⟩

private theorem object_cases_homology_short_exact_some_rotation
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
        normalizedExponent model.classicalTower T.g +
        normalizedExponent model.classicalTower T.h = 1) :
    let U := Triangle.mk T.f T.g T.h
    HomologyShortExact model.coefficients U ∨
      HomologyShortExact model.coefficients U.rotate ∨
      HomologyShortExact model.coefficients U.rotate.rotate := by
  let U := Triangle.mk T.f T.g T.h
  change HomologyShortExact model.coefficients U ∨
    HomologyShortExact model.coefficients U.rotate ∨
    HomologyShortExact model.coefficients U.rotate.rotate
  have hU : U ∈ distTriang Spectrum := T.distinguished
  by_cases hf : normalizedExponent model.classicalTower T.f = 1
  · right; left
    apply object_cases_homology_short_exact_of_boundary_zero U.rotate
      (rot_of_distTriang U hU)
    change ZeroOnModTwoHomology model.coefficients
      (-((shiftFunctor Spectrum (1 : ℤ)).map T.f))
    exact object_cases_zero_on_homology_neg _
      (object_cases_zero_on_homology_shift T.f 1
        (object_cases_normalized_exponent_one_zero_homology T.f hf))
  by_cases hg : normalizedExponent model.classicalTower T.g = 1
  · right; right
    apply object_cases_homology_short_exact_of_boundary_zero U.rotate.rotate
      (rot_of_distTriang U.rotate (rot_of_distTriang U hU))
    change ZeroOnModTwoHomology model.coefficients
      (-((shiftFunctor Spectrum (1 : ℤ)).map T.g))
    exact object_cases_zero_on_homology_neg _
      (object_cases_zero_on_homology_shift T.g 1
        (object_cases_normalized_exponent_one_zero_homology T.g hg))
  · have hh : normalizedExponent model.classicalTower T.h = 1 := by
      have hfle := normalizedExponent_le_one model.classicalTower T.f
      have hgle := normalizedExponent_le_one model.classicalTower T.g
      have hhle := normalizedExponent_le_one model.classicalTower T.h
      omega
    left
    exact object_cases_homology_short_exact_of_boundary_zero U hU
      (object_cases_normalized_exponent_one_zero_homology T.h hh)

private def object_cases_homTargetAddEquiv {X Y Z : Spectrum} (e : Y ≅ Z) :
    (X ⟶ Y) ≃+ (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun f := f ≫ e.inv
  left_inv f := by simp [Category.assoc]
  right_inv f := by simp [Category.assoc]
  map_add' f g := by simp [Preadditive.add_comp]

private def object_cases_homSourceAddEquiv {X Y Z : Spectrum} (e : X ≅ Y) :
    (X ⟶ Z) ≃+ (Y ⟶ Z) where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp [← Category.assoc]
  right_inv f := by simp [← Category.assoc]
  map_add' f g := by simp [Preadditive.comp_add]

/-- The ordinary sphere-degree change, with arbitrary signed integer shifts. -/
private def object_cases_homotopyShiftAddEquiv (Y : Spectrum) (a n : ℤ) :
    HomotopyGroup n (Y⟦a⟧) ≃+ HomotopyGroup (n-a) Y := by
  let E := shiftEquiv' Spectrum (-a) a (by omega)
  letI : E.functor.Additive := by
    change (shiftFunctor Spectrum (-a)).Additive
    infer_instance
  let adj := E.toAdjunction
  let e := (adj.homAddEquiv (Sphere (C := Spectrum) n) Y).symm
  have e' : (Sphere (C := Spectrum) n ⟶ Y⟦a⟧) ≃+
      ((Sphere (C := Spectrum) n)⟦-a⟧ ⟶ Y) := by
    change (Sphere (C := Spectrum) n ⟶ Y⟦a⟧) ≃+
      ((Sphere (C := Spectrum) n)⟦-a⟧ ⟶ Y) at e
    exact e
  exact e'.trans (object_cases_homSourceAddEquiv
    ((shiftFunctorAdd' Spectrum n (-a) (n-a) (by omega)).symm.app SphereSpectrum))

/-- Postcompose the actual left-HF2 tensor image of an object isomorphism. -/
private def object_cases_modTwoHomologyIsoAddEquiv (n : ℤ) {X Y : Spectrum} (e : X ≅ Y) :
    ModTwoHomology model.coefficients n X ≃+
      ModTwoHomology model.coefficients n Y :=
  object_cases_homTargetAddEquiv ((tensorLeft model.coefficients.object).mapIso e)

/-- Uses the fixed closedBackground comparison, and its actual braiding. -/
private def object_cases_modTwoHomologyShiftAddEquiv (X : Spectrum) (a n : ℤ) :
    ModTwoHomology model.coefficients n (X⟦a⟧) ≃+
      ModTwoHomology model.coefficients (n-a) X := by
  let B := KIP126.AdamsSynthetic.Standard.closedBackground
  let H := model.coefficients.object
  letI := B.symmetric
  letI := B.tensorShift H
  let e : H ⊗ (X⟦a⟧) ≅ (H ⊗ X)⟦a⟧ :=
    (β_ H (X⟦a⟧)) ≪≫ ((tensorRight H).commShiftIso a).app X ≪≫
      (shiftFunctor Spectrum a).mapIso (β_ X H)
  exact (object_cases_homTargetAddEquiv e).trans (object_cases_homotopyShiftAddEquiv (H ⊗ X) a n)

/-- Minimal direct interface requested for actual tmf. -/
private def object_cases_tmfHomologyShiftAddEquiv (a n : ℤ) :
    ModTwoHomology model.coefficients n (tmf⟦a⟧) ≃+
      ModTwoHomology model.coefficients (n-a) tmf :=
  object_cases_modTwoHomologyShiftAddEquiv tmf a n

/-- Transport from any actual object isomorphism, without changing the object. -/
private def object_cases_actualObjectHomologyAddEquiv (X : Spectrum) (a n : ℤ)
    (e : X ≅ tmf⟦a⟧) :
    ModTwoHomology model.coefficients n X ≃+
      ModTwoHomology model.coefficients (n-a) tmf :=
  (object_cases_modTwoHomologyIsoAddEquiv n e).trans (object_cases_tmfHomologyShiftAddEquiv a n)

/-- Prop-valued object predicate: Iso is a Type, so Nonempty is necessary. -/
private def object_cases_object_is_detector_shift (X : ClassicalObject) : Prop :=
  ∃ a : ℤ, Nonempty (X.obj model.auxiliary ≅ tmf⟦a⟧)

private theorem object_cases_detector_is_detector_shift : object_cases_object_is_detector_shift .detector := by
  refine ⟨0, ⟨?_⟩⟩
  exact tmfIso.symm ≪≫ ((shiftFunctorZero Spectrum ℤ).symm.app tmf)

private theorem object_cases_detector_shift_closed (X : ClassicalObject)
    (hX : object_cases_object_is_detector_shift X) (n : ℤ) :
    object_cases_object_is_detector_shift (.shift n X) := by
  obtain ⟨a, ⟨e⟩⟩ := hX
  refine ⟨a+n, ⟨?_⟩⟩
  exact (shiftFunctor Spectrum n).mapIso e ≪≫
    (shiftFunctorAdd Spectrum a n).symm.app tmf

private theorem object_cases_actualDetectorHomologyEquiv_exists (X : ClassicalObject)
    (hX : object_cases_object_is_detector_shift X) :
    ∃ a : ℤ, ∀ n : ℤ, Nonempty
      (ModTwoHomology model.coefficients n (X.obj model.auxiliary) ≃+
        ModTwoHomology model.coefficients (n-a) tmf) := by
  obtain ⟨a, ⟨e⟩⟩ := hX
  exact ⟨a, fun n => ⟨object_cases_actualObjectHomologyAddEquiv (X.obj model.auxiliary) a n e⟩⟩

/-- Syntactic descriptor handles every finite nested ordinary shift. -/
private def object_cases_detector_shift_weight : ClassicalObject → Option ℤ
  | .sphere => none
  | .nuCofiber => none
  | .detector => some 0
  | .shift n X => (object_cases_detector_shift_weight X).map (fun a => a+n)

private def object_cases_detectorShiftObjectIso (X : ClassicalObject) (a : ℤ)
    (ha : object_cases_detector_shift_weight X = some a) :
    X.obj model.auxiliary ≅ tmf⟦a⟧ := by
  induction X generalizing a with
  | sphere => simp [object_cases_detector_shift_weight] at ha
  | nuCofiber => simp [object_cases_detector_shift_weight] at ha
  | detector =>
      have h : a = 0 := by simpa [object_cases_detector_shift_weight] using ha.symm
      subst a
      exact tmfIso.symm ≪≫ ((shiftFunctorZero Spectrum ℤ).symm.app tmf)
  | shift n X ih =>
      cases hX : object_cases_detector_shift_weight X with
      | none => simp [object_cases_detector_shift_weight, hX] at ha
      | some b =>
          have h : a = b+n := by simpa [object_cases_detector_shift_weight, hX] using ha.symm
          subst a
          exact (shiftFunctor Spectrum n).mapIso (ih b hX) ≪≫
            (shiftFunctorAdd Spectrum b n).symm.app tmf

private def object_cases_detectorShiftHomologyAddEquiv (X : ClassicalObject) (a n : ℤ)
    (ha : object_cases_detector_shift_weight X = some a) :
    ModTwoHomology model.coefficients n (X.obj model.auxiliary) ≃+
      ModTwoHomology model.coefficients (n-a) tmf :=
  object_cases_actualObjectHomologyAddEquiv (X.obj model.auxiliary) a n (object_cases_detectorShiftObjectIso X a ha)

private theorem object_cases_descriptor_implies_object_predicate (X : ClassicalObject) (a : ℤ)
    (ha : object_cases_detector_shift_weight X = some a) : object_cases_object_is_detector_shift X :=
  ⟨a, ⟨object_cases_detectorShiftObjectIso X a ha⟩⟩

/-- Three actual detector-shift vertices are impossible in the selected
classical triangle when its actual normalization exponents sum to one.
The nonzero HF2 homology is deduced from an exponent-zero arrow. -/
private theorem object_cases_no_three_detector_vertices
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hX : object_cases_object_is_detector_shift T.X)
    (hY : object_cases_object_is_detector_shift T.Y)
    (hZ : object_cases_object_is_detector_shift T.Z) : False := by
  obtain ⟨a,⟨ex⟩⟩ := hX
  obtain ⟨b,⟨ey⟩⟩ := hY
  obtain ⟨c,⟨ez⟩⟩ := hZ
  let eX := fun n => object_cases_actualObjectHomologyAddEquiv
    (T.X.obj model.auxiliary) a n ex
  let eY := fun n => object_cases_actualObjectHomologyAddEquiv
    (T.Y.obj model.auxiliary) b n ey
  let eZ := fun n => object_cases_actualObjectHomologyAddEquiv
    (T.Z.obj model.auxiliary) c n ez
  have hne : ∃ n : ℤ, Nontrivial (ModTwoHomology model.coefficients n tmf) := by
    have hzero : normalizedExponent model.classicalTower T.f = 0 ∨
        normalizedExponent model.classicalTower T.g = 0 ∨
        normalizedExponent model.classicalTower T.h = 0 := by
      omega
    rcases hzero with hf | hg | hh
    · obtain ⟨n,hn⟩ := object_cases_source_homology_nontrivial_of_exponent_zero T.f hf
      exact ⟨n-a, object_cases_nontrivial_add_equiv (eX n) hn⟩
    · obtain ⟨n,hn⟩ := object_cases_source_homology_nontrivial_of_exponent_zero T.g hg
      exact ⟨n-b, object_cases_nontrivial_add_equiv (eY n) hn⟩
    · obtain ⟨n,hn⟩ := object_cases_source_homology_nontrivial_of_exponent_zero T.h hh
      exact ⟨n-c, object_cases_nontrivial_add_equiv (eZ n) hn⟩
  let exs : (T.X.obj model.auxiliary)⟦(1:ℤ)⟧ ≅ tmf⟦a+1⟧ :=
    (shiftFunctor Spectrum (1:ℤ)).mapIso ex ≪≫ (shiftFunctorAdd Spectrum a 1).symm.app tmf
  let eys : (T.Y.obj model.auxiliary)⟦(1:ℤ)⟧ ≅ tmf⟦b+1⟧ :=
    (shiftFunctor Spectrum (1:ℤ)).mapIso ey ≪≫ (shiftFunctorAdd Spectrum b 1).symm.app tmf
  let eXs := fun n => object_cases_actualObjectHomologyAddEquiv
    ((T.X.obj model.auxiliary)⟦(1:ℤ)⟧) (a+1) n exs
  let eYs := fun n => object_cases_actualObjectHomologyAddEquiv
    ((T.Y.obj model.auxiliary)⟦(1:ℤ)⟧) (b+1) n eys
  let U := Triangle.mk T.f T.g T.h
  rcases object_cases_homology_short_exact_some_rotation T he with h | h | h
  · exact object_cases_no_short_exact_three_tmf_shifts U h a b c eX eY eZ hne
  · exact object_cases_no_short_exact_three_tmf_shifts U.rotate h b c (a+1) eY eZ eXs hne
  · exact object_cases_no_short_exact_three_tmf_shifts U.rotate.rotate h c (a+1) (b+1)
      eZ eXs eYs hne

private theorem object_cases_no_three_detector_shift_weights
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (a b c : ℤ)
    (hX : object_cases_detector_shift_weight T.X = some a)
    (hY : object_cases_detector_shift_weight T.Y = some b)
    (hZ : object_cases_detector_shift_weight T.Z = some c) : False :=
  object_cases_no_three_detector_vertices T he
    (object_cases_descriptor_implies_object_predicate T.X a hX)
    (object_cases_descriptor_implies_object_predicate T.Y b hY)
    (object_cases_descriptor_implies_object_predicate T.Z c hZ)

private theorem object_cases_some_vertex_not_detector_shift
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    object_cases_detector_shift_weight T.X = none ∨
      object_cases_detector_shift_weight T.Y = none ∨
      object_cases_detector_shift_weight T.Z = none := by
  cases hX : object_cases_detector_shift_weight T.X with
  | none => exact Or.inl rfl
  | some a =>
    cases hY : object_cases_detector_shift_weight T.Y with
    | none => exact Or.inr (Or.inl rfl)
    | some b =>
      cases hZ : object_cases_detector_shift_weight T.Z with
      | none => exact Or.inr (Or.inr rfl)
      | some c => exact (object_cases_no_three_detector_shift_weights T he a b c hX hY hZ).elim

private theorem object_cases_non_detector_shift_is_finite
    (X : ClassicalObject) (hX : object_cases_detector_shift_weight X = none) :
    IsFiniteSpectrum (X.obj model.auxiliary) := by
  induction X with
  | sphere => exact IsFiniteSpectrum.sphere
  | nuCofiber =>
    exact IsFiniteSpectrum.cofiber (HasFunctorialCofiber.cofib_distinguished model.auxiliary.nuMap)
      (IsFiniteSpectrum.shift 3 IsFiniteSpectrum.sphere) IsFiniteSpectrum.sphere
  | detector => simp only [object_cases_detector_shift_weight, reduceCtorEq] at hX
  | shift n X ih =>
    apply IsFiniteSpectrum.shift n
    apply ih
    cases hd : object_cases_detector_shift_weight X with
    | none => rfl
    | some a => simp only [object_cases_detector_shift_weight, hd, Option.map_some, reduceCtorEq] at hX

/-- Every actual exponent-sum-one triangle in the selected closure has a
finite vertex. In particular, a three-tmf-shift residual case is absent.
No finite quotient row, synthetic Whitehead principle or extra homology
nonvanishing premise is used. -/
private theorem object_cases_finite_vertex_of_exponent_sum_one
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    IsFiniteSpectrum (T.X.obj model.auxiliary) ∨
      IsFiniteSpectrum (T.Y.obj model.auxiliary) ∨
      IsFiniteSpectrum (T.Z.obj model.auxiliary) := by
  rcases object_cases_some_vertex_not_detector_shift T he with hX | hY | hZ
  · exact Or.inl (object_cases_non_detector_shift_is_finite T.X hX)
  · exact Or.inr (Or.inl (object_cases_non_detector_shift_is_finite T.Y hY))
  · exact Or.inr (Or.inr (object_cases_non_detector_shift_is_finite T.Z hZ))

end
end KIP126.Literature.Standard
