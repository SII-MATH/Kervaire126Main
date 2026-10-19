module
import KIP126.Literature.Standard
import all KIP126.Literature.Standard.FiniteQuotientObjectCases
import Mathlib.RingTheory.Nilpotent.Basic

/-! Constructed finite sphere-cell bounds for actual selected finite sources.
A sphere ghost is killed only after the stated finite number of composites.
No global sphere detection or finite quotient horizontal row is assumed.
-/

@[expose] section
namespace KIP126.Literature.Standard.Internal.GhostResearch
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.AdamsSynthetic.Standard KIP126.Kervaire.Route KIP126.Literature
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

section Generic
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

private def ghostPower {W : Syn} (a : W ⟶ W) : ℕ → (W ⟶ W)
  | 0 => 𝟙 W
  | n+1 => ghostPower a n ≫ a

private theorem ghostPower_add {W : Syn} (a : W ⟶ W) (k l : ℕ) :
    ghostPower a (k+l) = ghostPower a k ≫ ghostPower a l := by
  induction l with
  | zero => simp [ghostPower]
  | succ l ih =>
    change ghostPower a (k+l) ≫ a = ghostPower a k ≫ (ghostPower a l ≫ a)
    rw [ih,Category.assoc]

private def SphereGhost {W : Syn} (a : W ⟶ W) : Prop :=
  ∀ (m w : ℤ) (b : BiHom m w W), b ≫ a = 0

private def GhostBound (D : Syn) (n : ℕ) : Prop :=
  ∀ (W : Syn) (a : W ⟶ W), SphereGhost a →
    ∀ t : D ⟶ W, t ≫ ghostPower a n = 0

private theorem ghostBound_sphere (m w : ℤ) :
    GhostBound (Smn (Syn:=Syn) m w) 1 := by
  intro W a ha t
  simpa only [ghostPower,Category.id_comp] using ha m w t

private theorem ghostBound_iso {D E : Syn} (e : D ≅ E) (n : ℕ)
    (hE : GhostBound E n) : GhostBound D n := by
  intro W a ha t
  have h := hE W a ha (e.inv ≫ t)
  apply (cancel_epi e.inv).mp
  simpa only [Category.assoc,comp_zero] using h

/-- The source lies in one distinguished extension of two bounded sources.
This is a nilpotence bound, never a promotion of a single ghost to zero. -/
private theorem ghostBound_middle
    (T : Triangle Syn) (hT : T ∈ distTriang Syn) (k l : ℕ)
    (hA : GhostBound T.obj₁ k) (hC : GhostBound T.obj₃ l) :
    GhostBound T.obj₂ (k+l) := by
  intro W a ha t
  have hf : T.mor₁ ≫ (t ≫ ghostPower a k) = 0 := by
    simpa only [←Category.assoc] using hA W a ha (T.mor₁ ≫ t)
  obtain ⟨b,hb⟩ := T.yoneda_exact₂ hT (t ≫ ghostPower a k) hf
  rw [ghostPower_add,←Category.assoc,hb,Category.assoc,hC W a ha b,comp_zero]

private inductive SphereCells : Syn → ℕ → Prop
  | sphere (m w : ℤ) : SphereCells (Smn m w) 1
  | iso {D E : Syn} (e : D ≅ E) {n : ℕ} : SphereCells E n → SphereCells D n
  | middle (T : Triangle Syn) (hT : T ∈ distTriang Syn) (k l : ℕ) :
      SphereCells T.obj₁ k → SphereCells T.obj₃ l → SphereCells T.obj₂ (k+l)

private theorem sphereCells_ghostBound {D : Syn} {n : ℕ}
    (hD : SphereCells D n) : GhostBound D n := by
  induction hD with
  | sphere m w => exact ghostBound_sphere m w
  | iso e h ih => exact ghostBound_iso e _ ih
  | middle T hT k l hA hC ihA ihC => exact ghostBound_middle T hT k l ihA ihC

private theorem sphereCells_map
    (F : Syn ⥤ Syn) [F.CommShift ℤ] [F.IsTriangulated]
    (hsphere : ∀ m w : ℤ, SphereCells (F.obj (Smn m w)) 1)
    {D : Syn} {n : ℕ} (hD : SphereCells D n) : SphereCells (F.obj D) n := by
  induction hD with
  | sphere m w => exact hsphere m w
  | iso e h ih => exact SphereCells.iso (F.mapIso e) ih
  | middle T hT k l hA hC ihA ihC =>
    exact SphereCells.middle (F.mapTriangle.obj T) (F.map_distinguished T hT) k l ihA ihC

end Generic

private def ghost_sphere_biShift_iso (p : ℤ×ℤ) (m w : ℤ) :
    (SyntheticCategory.biShift (Syn:=SyntheticSpectrum) p).obj (Smn m w) ≅
      Smn (m+p.1) (w+p.2) :=
  (biShiftAddIso (m,w) p (m+p.1,w+p.2) (by cases p; rfl)).app S_0_0

private theorem sphereCells_biShift (p : ℤ×ℤ) {D : SyntheticSpectrum} {n : ℕ}
    (hD : SphereCells D n) :
    SphereCells ((SyntheticCategory.biShift p).obj D) n := by
  letI := model.exactness.shiftCommShift p
  letI := model.exactness.shiftExact p
  apply sphereCells_map (SyntheticCategory.biShift p) _ hD
  intro m w
  exact SphereCells.iso (ghost_sphere_biShift_iso p m w) (SphereCells.sphere _ _)

private theorem sphereCells_ordinaryShift (a : ℤ) {D : SyntheticSpectrum} {n : ℕ}
    (hD : SphereCells D n) : SphereCells (D⟦a⟧) n := by
  exact SphereCells.iso ((SyntheticCategory.biShift_compat a).symm.app D)
    (sphereCells_biShift (a,0) hD)

private theorem sphereCells_quotient (q : ℕ) {D : SyntheticSpectrum} {n : ℕ}
    (hD : SphereCells D n) : SphereCells (XModLambdaN D q) (n+n) := by
  let T := (XModLambdaN.cofiberTriangle D q).rotate
  have hT : T ∈ distTriang SyntheticSpectrum :=
    rot_of_distTriang _ (XModLambdaN.cofiberTriangle_distinguished D q)
  exact SphereCells.middle T hT n n hD
    (sphereCells_ordinaryShift 1 (sphereCells_biShift (0,-(q:ℤ)) hD))

private theorem sphereCells_nu_sphere :
    SphereCells (model.nu.functor.obj (SphereSpectrum : Spectrum)) 1 := by
  exact SphereCells.iso
    (model.nu.unitIso ≪≫ SyntheticCategory.biShift_zero.symm.app S_0_0)
    (SphereCells.sphere 0 0)

private def ghost_sphere_suspension_iso (m w : ℤ) :
    (Smn (Syn:=SyntheticSpectrum) m w)⟦(1:ℤ)⟧ ≅ Smn (m+1) w :=
  (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).symm.app (Smn m w) ≪≫
    (biShiftAddIso (m,w) (1,0) (m+1,w) (by ext <;> simp)).app S_0_0

/-- These are the two actual diagonal sphere cells of the selected nu-cofiber.
The middle object is first F_0 nu Cnu and is transported by its actual iso. -/
private theorem sphereCells_nu_cofiber :
    SphereCells (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) 2 := by
  let T := (KIP126.Literature.normalizedTriangle model model.auxiliary.nuRouteTriangle
    nuCofiber_exponent_sum).rotate
  have hT : T ∈ distTriang SyntheticSpectrum :=
    rot_of_distTriang _ nuCofiber_distinguished
  let eA : T.obj₁ ≅ Smn (Syn:=SyntheticSpectrum) 0 0 :=
    model.nu.unitIso ≪≫ SyntheticCategory.biShift_zero.symm.app S_0_0
  let eC : T.obj₃ ≅ Smn (Syn:=SyntheticSpectrum) 4 4 := by
    change ((SyntheticCategory.biShift
      (0,(normalizedExponent model.classicalTower model.auxiliary.nuMap:ℤ))).obj
      (model.nu.functor.obj (Sphere (C:=Spectrum) 3)))⟦(1:ℤ)⟧ ≅ _
    rw [nuCofiber_nu_exponent]
    exact (shiftFunctor SyntheticSpectrum (1:ℤ)).mapIso
      ((SyntheticCategory.biShift (0,(1:ℤ))).mapIso (nuSphereThree model) ≪≫
        (biShiftAddIso (3,3) (0,1) (3,4) (by decide)).app S_0_0) ≪≫
      ghost_sphere_suspension_iso 3 4
  let eB : T.obj₂ ≅ model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary) := by
    change (SyntheticCategory.biShift
      (0,-(normalizedExponent model.classicalTower model.auxiliary.nuRouteTriangle.g:ℤ))).obj
      (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)) ≅ _
    rw [nuCofiber_bottom_exponent]
    exact SyntheticCategory.biShift_zero.app _
  exact SphereCells.iso eB.symm
    (SphereCells.middle T hT 1 1
      (SphereCells.iso eA (SphereCells.sphere 0 0))
      (SphereCells.iso eC (SphereCells.sphere 4 4)))

private theorem ghostBound_shifted_nu_sphere (p : ℤ×ℤ) (r : ℤ) :
    GhostBound (((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (SphereSpectrum : Spectrum)))⟦r⟧) 1 :=
  sphereCells_ghostBound (sphereCells_ordinaryShift r (sphereCells_biShift p sphereCells_nu_sphere))

private theorem ghostBound_shifted_nu_cofiber (p : ℤ×ℤ) (r : ℤ) :
    GhostBound (((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary)))⟦r⟧) 2 :=
  sphereCells_ghostBound (sphereCells_ordinaryShift r (sphereCells_biShift p sphereCells_nu_cofiber))

private theorem ghostBound_quotient_shifted_nu_sphere (p : ℤ×ℤ) (r : ℤ) (q : ℕ) :
    GhostBound ((XModLambdaN ((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (SphereSpectrum : Spectrum))) q)⟦r⟧) 2 :=
  sphereCells_ghostBound (sphereCells_ordinaryShift r
    (sphereCells_quotient q (sphereCells_biShift p sphereCells_nu_sphere)))

private theorem ghostBound_quotient_shifted_nu_cofiber (p : ℤ×ℤ) (r : ℤ) (q : ℕ) :
    GhostBound ((XModLambdaN ((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (ClassicalObject.nuCofiber.obj model.auxiliary))) q)⟦r⟧) 4 :=
  sphereCells_ghostBound (sphereCells_ordinaryShift r
    (sphereCells_quotient q (sphereCells_biShift p sphereCells_nu_cofiber)))

section NilpotentComparison
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]

private theorem ghostPower_eq_pow {W : Syn} (a : W ⟶ W) (n : ℕ) :
    ghostPower a n = (CategoryTheory.End.of a)^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ghostPower, ih, pow_succ', CategoryTheory.End.mul_def]

/-- The same sphere ghost has a square factoring through a source with
finite ghost bound. The bound kills only the stated composite power. -/
private theorem ghost_power_zero_of_square_factor
    {W D : Syn} (a : W ⟶ W) (ha : SphereGhost a)
    (k0 : W ⟶ D) (t : D ⟶ W) (L : ℕ) (hD : GhostBound D L)
    (hfactor : a ≫ a = k0 ≫ t) : ghostPower a (L+2) = 0 := by
  have hL : t ≫ ghostPower a L = 0 := hD W a ha t
  have h2 : ghostPower a 2 = k0 ≫ t := by
    simpa only [ghostPower, Category.id_comp] using hfactor
  calc
    ghostPower a (L+2) = ghostPower a 2 ≫ ghostPower a L := by
      rw [show L+2=2+L by omega, ghostPower_add]
    _ = (k0 ≫ t) ≫ ghostPower a L := by rw [h2]
    _ = 0 := by rw [Category.assoc,hL,comp_zero]

private theorem ghost_isNilpotent_of_square_factor
    {W D : Syn} (a : W ⟶ W) (ha : SphereGhost a)
    (k0 : W ⟶ D) (t : D ⟶ W) (L : ℕ) (hD : GhostBound D L)
    (hfactor : a ≫ a = k0 ≫ t) : IsNilpotent (CategoryTheory.End.of a) := by
  refine ⟨L+2, ?_⟩
  rw [←ghostPower_eq_pow]
  exact ghost_power_zero_of_square_factor a ha k0 t L hD hfactor

private theorem ghost_one_add_isIso_of_square_factor
    {W D : Syn} (a : W ⟶ W) (ha : SphereGhost a)
    (k0 : W ⟶ D) (t : D ⟶ W) (L : ℕ) (hD : GhostBound D L)
    (hfactor : a ≫ a = k0 ≫ t) : IsIso (𝟙 W + a) := by
  have hn := ghost_isNilpotent_of_square_factor a ha k0 t L hD hfactor
  exact (CategoryTheory.isUnit_iff_isIso _).mp hn.isUnit_one_add

private theorem ghost_one_sub_isIso_of_square_factor
    {W D : Syn} (a : W ⟶ W) (ha : SphereGhost a)
    (k0 : W ⟶ D) (t : D ⟶ W) (L : ℕ) (hD : GhostBound D L)
    (hfactor : a ≫ a = k0 ≫ t) : IsIso (𝟙 W - a) := by
  have hn := ghost_isNilpotent_of_square_factor a ha k0 t L hD hfactor
  exact (CategoryTheory.isUnit_iff_isIso _).mp hn.isUnit_one_sub

end NilpotentComparison

private def ghost_shifts_diagonal_comp_iso (a b c : ℤ) (h : a+b=c)
    (Y : SyntheticSpectrum) :
    (SyntheticCategory.biShift (b,b)).obj
        ((SyntheticCategory.biShift (a,a)).obj Y) ≅
      (SyntheticCategory.biShift (c,c)).obj Y :=
  (biShiftAddIso (a,a) (b,b) (c,c) (by ext <;> exact h)).app Y

private def ghost_shifts_nu_zero_iso (X : Spectrum) :
    model.nu.functor.obj (X⟦(0:ℤ)⟧) ≅
      (SyntheticCategory.biShift (0,0)).obj (model.nu.functor.obj X) :=
  model.nu.functor.mapIso ((shiftFunctorZero Spectrum ℤ).app X) ≪≫
    SyntheticCategory.biShift_zero.symm.app (model.nu.functor.obj X)

/-- Invert the objectwise +1 comparison at X[-1], using only actual shifts. -/
private def ghost_shifts_nu_minus_one_iso (X : Spectrum) :
    model.nu.functor.obj (X⟦(-1:ℤ)⟧) ≅
      (SyntheticCategory.biShift (-1,-1)).obj (model.nu.functor.obj X) := by
  let c : (X⟦(-1:ℤ)⟧)⟦(1:ℤ)⟧ ≅ X :=
    (shiftFunctorCompIsoId Spectrum (-1) 1 (by omega)).app X
  let e : model.nu.functor.obj X ≅
      (SyntheticCategory.biShift (1,1)).obj
        (model.nu.functor.obj (X⟦(-1:ℤ)⟧)) :=
    (model.nu.functor.mapIso c).symm ≪≫
      model.nu.suspensionIso (X⟦(-1:ℤ)⟧)
  exact
    ((SyntheticCategory.biShift (-1,-1)).mapIso e ≪≫
      ghost_shifts_diagonal_comp_iso 1 (-1) 0 (by omega)
        (model.nu.functor.obj (X⟦(-1:ℤ)⟧)) ≪≫
      SyntheticCategory.biShift_zero.app
        (model.nu.functor.obj (X⟦(-1:ℤ)⟧))).symm

private def ghost_shifts_nu_nat_iso (X : Spectrum) : (n : ℕ) →
    model.nu.functor.obj (X⟦(n:ℤ)⟧) ≅
      (SyntheticCategory.biShift ((n:ℤ),(n:ℤ))).obj (model.nu.functor.obj X)
  | 0 => ghost_shifts_nu_zero_iso X
  | n+1 =>
      model.nu.functor.mapIso
          ((shiftFunctorAdd' Spectrum (n:ℤ) 1 ((n+1:ℕ):ℤ) (by omega)).app X) ≪≫
        model.nu.suspensionIso (X⟦(n:ℤ)⟧) ≪≫
        (SyntheticCategory.biShift (1,1)).mapIso (ghost_shifts_nu_nat_iso X n) ≪≫
        ghost_shifts_diagonal_comp_iso (n:ℤ) 1 ((n+1:ℕ):ℤ) (by omega)
          (model.nu.functor.obj X)

private def ghost_shifts_nu_neg_nat_iso (X : Spectrum) : (n : ℕ) →
    model.nu.functor.obj (X⟦(-(n:ℤ))⟧) ≅
      (SyntheticCategory.biShift (-(n:ℤ),-(n:ℤ))).obj (model.nu.functor.obj X)
  | 0 => ghost_shifts_nu_zero_iso X
  | n+1 =>
      model.nu.functor.mapIso
          ((shiftFunctorAdd' Spectrum (-(n:ℤ)) (-1) (-((n+1:ℕ):ℤ)) (by omega)).app X) ≪≫
        ghost_shifts_nu_minus_one_iso (X⟦(-(n:ℤ))⟧) ≪≫
        (SyntheticCategory.biShift (-1,-1)).mapIso (ghost_shifts_nu_neg_nat_iso X n) ≪≫
        ghost_shifts_diagonal_comp_iso (-(n:ℤ)) (-1) (-((n+1:ℕ):ℤ)) (by omega)
          (model.nu.functor.obj X)

/-- Arbitrary signed integer shifts; one objectwise comparison for each X,n. -/
private def ghost_shifts_nu_int_iso (X : Spectrum) : (n : ℤ) →
    model.nu.functor.obj (X⟦n⟧) ≅
      (SyntheticCategory.biShift (n,n)).obj (model.nu.functor.obj X)
  | .ofNat n => ghost_shifts_nu_nat_iso X n
  | .negSucc n => ghost_shifts_nu_neg_nat_iso X (n+1)

/-- The same fixed nu.unitIso gives all diagonal synthetic spheres. -/
private def ghost_shifts_nu_sphere_iso (n : ℤ) :
    model.nu.functor.obj (Sphere (C := Spectrum) n) ≅
      Smn (Syn := SyntheticSpectrum) n n :=
  ghost_shifts_nu_int_iso SphereSpectrum n ≪≫
    (SyntheticCategory.biShift (n,n)).mapIso model.nu.unitIso

private def ghost_shifts_selected_sphere_iso (n : ℤ) :
    model.nu.functor.obj ((ClassicalObject.shift n .sphere).obj model.auxiliary) ≅
      Smn (Syn := SyntheticSpectrum) n n :=
  ghost_shifts_nu_sphere_iso n

private inductive ghost_cells_sphere_shift_syntax : ClassicalObject → Prop where
  | sphere : ghost_cells_sphere_shift_syntax .sphere
  | shift (n : ℤ) {X : ClassicalObject} :
      ghost_cells_sphere_shift_syntax X → ghost_cells_sphere_shift_syntax (.shift n X)

/-- Literal syntax: start with the actual Cnu and add integer shifts. -/
private inductive ghost_cells_nu_cofiber_shift_syntax : ClassicalObject → Prop where
  | nuCofiber : ghost_cells_nu_cofiber_shift_syntax .nuCofiber
  | shift (n : ℤ) {X : ClassicalObject} :
      ghost_cells_nu_cofiber_shift_syntax X → ghost_cells_nu_cofiber_shift_syntax (.shift n X)

private theorem ghost_cells_descriptor_none_syntax
    (X : ClassicalObject) (hX : object_cases_detector_shift_weight X = none) :
    ghost_cells_sphere_shift_syntax X ∨ ghost_cells_nu_cofiber_shift_syntax X := by
  induction X with
  | sphere => exact Or.inl .sphere
  | nuCofiber => exact Or.inr .nuCofiber
  | detector => simp only [object_cases_detector_shift_weight, reduceCtorEq] at hX
  | shift n X ih =>
    have hnone : object_cases_detector_shift_weight X = none := by
      cases hd : object_cases_detector_shift_weight X with
      | none => rfl
      | some a =>
        simp only [object_cases_detector_shift_weight, hd, Option.map_some, reduceCtorEq] at hX
    rcases ih hnone with hs | hc
    · exact Or.inl (.shift n hs)
    · exact Or.inr (.shift n hc)

private theorem ghost_cells_sphere_syntax_actual_iso
    (X : ClassicalObject) (hX : ghost_cells_sphere_shift_syntax X) :
    ∃ n : ℤ, Nonempty (X.obj model.auxiliary ≅ Sphere (C := Spectrum) n) := by
  induction hX with
  | sphere =>
    refine ⟨0, ⟨?_⟩⟩
    exact (shiftFunctorZero Spectrum ℤ).symm.app SphereSpectrum
  | @shift n X hX ih =>
    obtain ⟨a, ⟨e⟩⟩ := ih
    refine ⟨a+n, ⟨?_⟩⟩
    exact (shiftFunctor Spectrum n).mapIso e ≪≫
      (shiftFunctorAdd Spectrum a n).symm.app SphereSpectrum

private theorem ghost_cells_nu_cofiber_syntax_actual_iso
    (X : ClassicalObject) (hX : ghost_cells_nu_cofiber_shift_syntax X) :
    ∃ n : ℤ, Nonempty
      (X.obj model.auxiliary ≅
        (ClassicalObject.nuCofiber.obj model.auxiliary)⟦n⟧) := by
  induction hX with
  | nuCofiber =>
    refine ⟨0, ⟨?_⟩⟩
    exact (shiftFunctorZero Spectrum ℤ).symm.app
      (ClassicalObject.nuCofiber.obj model.auxiliary)
  | @shift n X hX ih =>
    obtain ⟨a, ⟨e⟩⟩ := ih
    refine ⟨a+n, ⟨?_⟩⟩
    exact (shiftFunctor Spectrum n).mapIso e ≪≫
      (shiftFunctorAdd Spectrum a n).symm.app
        (ClassicalObject.nuCofiber.obj model.auxiliary)

/-- Each branch contains both literal syntax evidence and its actual iso. -/
private def ghost_cells_literal_finite_source_case (X : ClassicalObject) : Prop :=
  (ghost_cells_sphere_shift_syntax X ∧
    ∃ n : ℤ, Nonempty (X.obj model.auxiliary ≅ Sphere (C := Spectrum) n)) ∨
  (ghost_cells_nu_cofiber_shift_syntax X ∧
    ∃ n : ℤ, Nonempty (X.obj model.auxiliary ≅
      (ClassicalObject.nuCofiber.obj model.auxiliary)⟦n⟧))

private theorem ghost_cells_descriptor_none_literal_actual
    (X : ClassicalObject) (hX : object_cases_detector_shift_weight X = none) :
    ghost_cells_literal_finite_source_case X := by
  rcases ghost_cells_descriptor_none_syntax X hX with hs | hc
  · exact Or.inl ⟨hs, ghost_cells_sphere_syntax_actual_iso X hs⟩
  · exact Or.inr ⟨hc, ghost_cells_nu_cofiber_syntax_actual_iso X hc⟩

private theorem ghost_cells_descriptor_none_actual_iso
    (X : ClassicalObject) (hX : object_cases_detector_shift_weight X = none) :
    (∃ n : ℤ, Nonempty (X.obj model.auxiliary ≅ Sphere (C := Spectrum) n)) ∨
      (∃ n : ℤ, Nonempty (X.obj model.auxiliary ≅
        (ClassicalObject.nuCofiber.obj model.auxiliary)⟦n⟧)) := by
  rcases ghost_cells_descriptor_none_literal_actual X hX with hs | hc
  · exact Or.inl hs.2
  · exact Or.inr hc.2

/-- Internal consumer of the descriptor alternative produced by ObjectCases. -/
private theorem ghost_cells_triangle_none_literal_actual
    (T : TriangleData model.auxiliary)
    (hcases : object_cases_detector_shift_weight T.X = none ∨
      object_cases_detector_shift_weight T.Y = none ∨
      object_cases_detector_shift_weight T.Z = none) :
    ghost_cells_literal_finite_source_case T.X ∨
      ghost_cells_literal_finite_source_case T.Y ∨
      ghost_cells_literal_finite_source_case T.Z := by
  rcases hcases with hX | hY | hZ
  · exact Or.inl (ghost_cells_descriptor_none_literal_actual T.X hX)
  · exact Or.inr (Or.inl (ghost_cells_descriptor_none_literal_actual T.Y hY))
  · exact Or.inr (Or.inr (ghost_cells_descriptor_none_literal_actual T.Z hZ))

private theorem ghost_cells_descriptor_eq_object_cases (X : ClassicalObject) :
    object_cases_detector_shift_weight X = object_cases_detector_shift_weight X := by
  induction X with
  | sphere => rfl
  | nuCofiber => rfl
  | detector => rfl
  | shift n X ih =>
    change (object_cases_detector_shift_weight X).map (fun a => a+n) =
      (object_cases_detector_shift_weight X).map (fun a => a+n)
    rw [ih]

/-- Actual T/he producer: a literal source case, carrying its actual iso. -/
private theorem ghost_cells_actual_triangle_literal_sources
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    ghost_cells_literal_finite_source_case T.X ∨
      ghost_cells_literal_finite_source_case T.Y ∨
      ghost_cells_literal_finite_source_case T.Z := by
  apply ghost_cells_triangle_none_literal_actual T
  simpa only [ghost_cells_descriptor_eq_object_cases] using
    object_cases_some_vertex_not_detector_shift T he

/-- The actual triangle has a literal sphere/Cnu shift vertex, including
an actual classical-object isomorphism in the chosen branch. -/
private theorem ghost_cells_some_finite_source
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    ghost_cells_literal_finite_source_case T.X ∨
      ghost_cells_literal_finite_source_case T.Y ∨
      ghost_cells_literal_finite_source_case T.Z := by
  rcases object_cases_some_vertex_not_detector_shift T he with hX | hY | hZ
  · exact Or.inl (ghost_cells_descriptor_none_literal_actual T.X hX)
  · exact Or.inr (Or.inl (ghost_cells_descriptor_none_literal_actual T.Y hY))
  · exact Or.inr (Or.inr (ghost_cells_descriptor_none_literal_actual T.Z hZ))

private theorem sphereCells_literal_finite_source (X : ClassicalObject)
    (hX : ghost_cells_literal_finite_source_case X) :
    SphereCells (model.nu.functor.obj (X.obj model.auxiliary)) 1 ∨
      SphereCells (model.nu.functor.obj (X.obj model.auxiliary)) 2 := by
  rcases hX with hs | hc
  · obtain ⟨n,⟨e⟩⟩ := hs.2
    exact Or.inl (SphereCells.iso
      (model.nu.functor.mapIso e ≪≫ ghost_shifts_nu_sphere_iso n)
      (SphereCells.sphere n n))
  · obtain ⟨n,⟨e⟩⟩ := hc.2
    exact Or.inr (SphereCells.iso
      (model.nu.functor.mapIso e ≪≫
        ghost_shifts_nu_int_iso (ClassicalObject.nuCofiber.obj model.auxiliary) n)
      (sphereCells_biShift (n,n) sphereCells_nu_cofiber))

private theorem ghostBound_mono {D : SyntheticSpectrum} {k l : ℕ}
    (hD : GhostBound D k) (hkl : k ≤ l) : GhostBound D l := by
  intro W a ha t
  have hzero := hD W a ha t
  rw [show l=k+(l-k) by omega, ghostPower_add, ←Category.assoc, hzero, zero_comp]

/-- Uniform bound four for every actual finite-source branch, every weight
shift, every ordinary shift before/after the actual quotient, and every q.
The sphere branch has the sharper bound two. -/
private theorem ghostBound_quotient_literal_finite_source
    (X : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X)
    (p : ℤ×ℤ) (s r : ℤ) (q : ℕ) :
    GhostBound ((XModLambdaN (((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦s⟧) q)⟦r⟧) 4 := by
  rcases sphereCells_literal_finite_source X hX with h1 | h2
  · exact ghostBound_mono
      (sphereCells_ghostBound (sphereCells_ordinaryShift r (sphereCells_quotient q
        (sphereCells_ordinaryShift s (sphereCells_biShift p h1))))) (by omega)
  · exact sphereCells_ghostBound (sphereCells_ordinaryShift r (sphereCells_quotient q
      (sphereCells_ordinaryShift s (sphereCells_biShift p h2))))

end
end KIP126.Literature.Standard.Internal.GhostResearch
