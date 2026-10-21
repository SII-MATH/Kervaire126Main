module

import all KIP126.ProofTools.MahowaldLeibniz.CoreAtLevel
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelLabels

/-! The positive-first-exponent branch of the common finite-quotient core.
The prescribed second classical differential constructs one actual May
representative.  Its label, image, and cycle qualification belong to that
same finite quotient.  An independent source-ambiguity annihilation premise
then compares every other representative with the same original X label.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- Complete finite core when the first normalized exponent is one.
The ambiguity premise is formulated on the actual desuspended source in X,
and the image is the signed coefficient target of the finite May square. -/
private def PositiveFirstFiniteCoreStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (_hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (_hg : normalizedExponent model.classicalTower T.g = 0)
    (_hh : normalizedExponent model.classicalTower T.h = 0) : Prop :=
  ∀ (c q : ℕ) (hq : 0<q) (S V : ℤ)
    (u : Ambient model T.X (S,V)) (z : Ambient model T.Z (S,V+1))
    (v : Ambient model T.Y (S+q+1,(V+1)+q)),
    (model.classicalSuspension T.X).DesuspendsClass S (V+1)
      ((model.classical.map T.h).pageMap 2 (S,V+1) z) (by simpa using u) →
    HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (S,V+1) (S+q+1,(V+1)+q) z
      ((model.classical.map T.g).pageMap 2 (S+q+1,(V+1)+q) v) →
    ∀ (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧),
    XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)) →
    ∀ (ε : XModLambdaN ((SyntheticCategory.biShift (1,1)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,1)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+(q+1)))),
    XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,1)).map (XModLambdaN.incl _ (c+(q+1))) →
    let N := normalizedTriangle model T he
    let b := (biSuspensionHomEquiv ((V+1)-S) (V+1) (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show ((V+1)+q)-(S+q+1)=((V+1)-S)-1 by omega) rfl
          (nativeFirstLabel T.Y (S+q+1) ((V+1)+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN N.obj₂ 1) ⟶
        XModLambdaN N.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower N.obj₂).triangle hq (Nat.lt_succ_self q)).lambdaMap
    let target :=
      homotopyRegrade (show (V+1)-S=V-S+1 by omega) (show (V+1)-c=V-c+1 by omega)
        (finiteCoefficientInsert (N.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) ((V+1)-S) (V+1)
          ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv))
    (∃ a : BiHom (V-S+1) (V-c+1) (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (S,V,V-c) (finiteTargetLabel model T.X (c+(q+1)) S V c u)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)
        (c+(q+1)) = target ∧
      IsCycle model T.X (q+1) (S,V) u) ∧
    ((∀ a : BiHom (V-S+1) (V-c+1) (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      FiltrationAtLeast model.syntheticTower (S+1)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε a) →
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)
        (c+(q+1)) = 0) →
      ∀ d : BiHom (V-S+1) (V-c+1) (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (S,V,V-c) (finiteTargetLabel model T.X (c+(q+1)) S V c u)
        (rawMaySourceDesuspend T he hf (c+(q+1)) c S V ε d) →
      d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁)
        (c+(q+1)) = target)

/-- The finite May construction proves the first-exponent core without
assuming a producer, a first classical differential, or a no-crossing law. -/
private theorem positive_first_finite_core
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0) :
    PositiveFirstFiniteCoreStatement T he hT hf hg hh := by
  intro c q hq S V u z v hu hdz ey hey ε hε
  dsimp only
  obtain ⟨a₀,ha₀,himage⟩ := classical_second_differential_may_at_level
    T he hT hf hg hh c q hq S (V+1) z v hdz ey hey
  let a := homotopyRegrade (show (V+1)-S=V-S+1 by omega)
    (show (V+1)-c=V-c+1 by omega) a₀
  have haSigma : Detects (model.convergence (.quotient (c+(q+1)) (.nu (.shift 1 T.X))))
      (S,V+1,V+1-c) (finiteTargetLabel model (.shift 1 T.X) (c+(q+1)) S (V+1) c
        ((model.classical.map T.h).pageMap 2 (S,V+1) z))
      (homotopyRegrade (by dsimp; omega) (by dsimp; omega)
        (a ≫ XModLambdaN.map (normalizedSuspensionNativeIso T he hf).hom (c+(q+1)))) := by
    simpa only [a,regrade_precomp,←Category.assoc,eqToHom_trans,eqToHom_refl,Category.id_comp] using ha₀
  have haX := raw_may_source_desuspend_detects T he hf (c+(q+1)) c (by omega)
    S V ε hε u _ hu a haSigma
  have hcycle := (finite_rho_lift_label_and_cycles T.X (c+(q+1)) (c+(q+1)) c
    le_rfl (by omega) S V u _ haX _ (by
      rw [(model.quotients.tower _).rho_id,Category.comp_id])).2
  have hcycle' : IsCycle model T.X (q+1) (S,V) u := by
    refine ⟨by omega,?_⟩
    simpa only [show ((c+(q+1):ℕ):ℤ)-c=(q:ℤ)+1 by omega] using hcycle
  have hi := congrArg (homotopyRegrade (show (V+1)-S=V-S+1 by omega)
    (show (V+1)-c=V-c+1 by omega)) himage
  have hai := (show a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+(q+1)) = _ from
    by simpa only [a,regrade_comp] using hi)
  refine ⟨⟨a,haX,hai,hcycle'⟩,?_⟩
  intro hkill d hd
  have hdiff := detects_sub_filtration
    (model.convergence (.quotient (c+(q+1)) (.nu T.X))) (S,V,V-c) hd haX
  rw [←raw_may_source_desuspend_sub] at hdiff
  have hz := hkill (d-a) hdiff
  have heq : d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+(q+1)) =
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (normalizedTriangle model T he).mor₁) (c+(q+1)) :=
    sub_eq_zero.mp (by simpa only [Preadditive.sub_comp] using hz)
  exact heq.trans hai

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
