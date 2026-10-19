module

import all KIP126.Literature.Standard.FiniteQuotientSuspension

/-! Literal rotation of the actual mapped quotient row. The ordinary
suspension naturality on a finite first source fixes the displayed signed
third map. -/

@[expose] section
namespace KIP126.Literature.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard Internal.GhostResearch
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

section Generic
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C:=Syn)]

private theorem quotient_row_rotation_of_suspension_naturality
    (q : ℕ) (N : Triangle Syn)
    (eA : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅
      (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (eB : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅
      (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧)
    (hRow : Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
      (XModLambdaN.map N.mor₃ q ≫ eA.hom) ∈ distTriang Syn)
    (hNat : XModLambdaN.map ((shiftFunctor Syn (1:ℤ)).map N.mor₁) q ≫ eB.hom =
      eA.hom ≫ (shiftFunctor Syn (1:ℤ)).map (XModLambdaN.map N.mor₁ q)) :
    Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
      (-(XModLambdaN.map ((shiftFunctor Syn (1:ℤ)).map N.mor₁) q ≫ eB.hom)) ∈
      distTriang Syn := by
  let R := Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
    (XModLambdaN.map N.mor₃ q ≫ eA.hom)
  let U := Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
    (-(XModLambdaN.map ((shiftFunctor Syn (1:ℤ)).map N.mor₁) q ≫ eB.hom))
  let e : U ≅ R.rotate := Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) eA
    (by simp [U,R])
    (by simp [U,R])
    (by
      dsimp only [U,R,Triangle.rotate,Triangle.mk]
      simpa only [Iso.refl_hom,CategoryTheory.Functor.map_id,Category.comp_id,
        CategoryTheory.Functor.map_neg,Preadditive.comp_neg] using
        congrArg (fun k => -k) hNat)
  exact isomorphic_distinguished R.rotate (rot_of_distTriang R hRow) U e

end Generic

/-- An actual mapped row with a finite first source rotates to the literal
signed row. The new ordinary suspension comparison is constructed on the
same second vertex and retains its actual inclusion square. -/
private theorem quotient_row_rotation_finite_source_shifted_coordinates
    (X Y : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X)
    (p r : ℤ×ℤ) (a b : ℤ) (q : ℕ) (hq : 0<q)
    (hrel : p.2-p.1-a-(r.2-r.1-b)≤1)
    (N : Triangle SyntheticSpectrum)
    (aCoord : N.obj₁ ≅ ((SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))⟦a⟧)
    (bCoord : N.obj₂ ≅ ((SyntheticCategory.biShift r).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))⟦b⟧)
    (eA : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅
      (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl (N.obj₁⟦(1:ℤ)⟧) q≫eA.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q))
    (hRow : Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
      (XModLambdaN.map N.mor₃ q≫eA.hom) ∈ distTriang SyntheticSpectrum) :
    ∃ eB : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q≫eB.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫eB.hom)) ∈
        distTriang SyntheticSpectrum := by
  obtain ⟨eB,heB⟩ := finite_quotient_suspension_comparison q N.obj₂
  letI := model.exactness.shiftCommShift (0,-(q:ℤ))
  have hNat : XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫eB.hom=
      eA.hom≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.map N.mor₁ q) :=
    finite_quotient_suspension_naturality_of_vanishing q eA eB heA heB
      (fun z => suspension_finite_source_to_quotient_vanishing_of_shifted_coordinates
        X Y hX p r a b q hq hrel aCoord bCoord z) N.mor₁
  exact ⟨eB,heB,quotient_row_rotation_of_suspension_naturality q N eA eB hRow hNat⟩

private theorem quotient_row_rotation_finite_source_coordinates
    (X Y : ClassicalObject) (hX : ghost_cells_literal_finite_source_case X)
    (p r : ℤ×ℤ) (q : ℕ) (hq : 0<q)
    (hrel : p.2-p.1-(r.2-r.1)≤1)
    (N : Triangle SyntheticSpectrum)
    (aCoord : N.obj₁ ≅ (SyntheticCategory.biShift p).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (bCoord : N.obj₂ ≅ (SyntheticCategory.biShift r).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)))
    (eA : XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q ≅
      (XModLambdaN N.obj₁ q)⟦(1:ℤ)⟧)
    (heA : XModLambdaN.incl (N.obj₁⟦(1:ℤ)⟧) q≫eA.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₁ q))
    (hRow : Triangle.mk (XModLambdaN.map N.mor₁ q) (XModLambdaN.map N.mor₂ q)
      (XModLambdaN.map N.mor₃ q≫eA.hom) ∈ distTriang SyntheticSpectrum) :
    ∃ eB : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅ (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧,
      XModLambdaN.incl (N.obj₂⟦(1:ℤ)⟧) q≫eB.hom=
        (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl N.obj₂ q) ∧
      Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
        (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q≫eB.hom)) ∈
        distTriang SyntheticSpectrum := by
  exact quotient_row_rotation_finite_source_shifted_coordinates X Y hX p r 0 0 q hq
    (by simpa only [sub_zero] using hrel) N
    (aCoord ≪≫ (shiftFunctorZero SyntheticSpectrum ℤ).symm.app _)
    (bCoord ≪≫ (shiftFunctorZero SyntheticSpectrum ℤ).symm.app _) eA heA hRow

end
end KIP126.Literature.Standard
