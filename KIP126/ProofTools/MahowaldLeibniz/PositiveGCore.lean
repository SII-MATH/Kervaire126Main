module

import all KIP126.ProofTools.MahowaldLeibniz.PositiveBranches
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch
import all KIP126.ProofTools.MahowaldLeibniz.MayTarget
import all KIP126.ProofTools.MahowaldLeibniz.PositiveGSource
import all KIP126.ProofTools.MahowaldLeibniz.OrdinaryImageSquare

/-! The positive second-exponent common finite quotient core. Native source
coordinates are (s+1,t); the second input lies on Z in (s+1,t+1). -/
@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- The second-exponent branch of the common finite quotient core. The
annihilation clause is a consequence about every representative with the
same native detected source; it is separate from construction of the
specified May representative. -/
private def PositiveSecondFiniteCoreStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (_hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=1)
    (_hh : normalizedExponent model.classicalTower T.h=0) : Prop :=
  ∀ (c q : ℕ) (_hq : 0<q) (s t : ℤ)
    (z : Ambient model T.Z (s+1,t+1)) (u : Ambient model T.X (s+1,t))
    (v : Ambient model T.Y (s+q+1,t+q)),
    (model.classicalSuspension T.X).DesuspendsClass (s+1) (t+1)
      ((model.classical.map T.h).pageMap 2 (s+1,t+1) z) (by simpa using u) →
    HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) (s+1,t+1) ((s+q+1)+1,(t+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+q+1) (t+q) v) →
    ∀ (ey : XModLambdaN ((normalizedTriangle model T he).obj₂⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (normalizedTriangle model T he).obj₂ (q+1))⟦(1:ℤ)⟧),
    XModLambdaN.incl _ (q+1) ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)) →
    ∀ (ε : XModLambdaN ((SyntheticCategory.biShift (1,0)).obj
      (model.nu.functor.obj (T.X.obj model.auxiliary))) (c+(q+1)) ≅
      (SyntheticCategory.biShift (1,0)).obj
        (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+(q+1)))),
    XModLambdaN.incl _ (c+(q+1)) ≫ ε.hom =
      (SyntheticCategory.biShift (1,0)).map (XModLambdaN.incl _ (c+(q+1))) →
    let V := normalizedTriangle model T he
    let b := (biSuspensionHomEquiv (t-s) t (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show (t+q)-(s+q+1)=(t-s)-1 by omega) rfl
          (nativeFirstLabel T.Y (s+q+1) (t+q) v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN V.obj₂ 1) ⟶
        XModLambdaN V.obj₂ (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower V.obj₂).triangle _hq (Nat.lt_succ_self q)).lambdaMap
    let target := finiteCoefficientInsert (V.obj₂⟦(1:ℤ)⟧) c (q+1) (by omega) (t-s) t
      ((-(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map ly)) ≫ ey.inv)
    IsCycle model T.X (q+1) (s+1,t) u ∧
    ∃ a : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
        (s+1,t,t-c) (finiteTargetLabel model T.X (c+(q+1)) (s+1) t c u)
        (positiveHSourceDesuspend T he hf (c+(q+1)) c s t ε a) ∧
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁)
        (c+(q+1)) = target ∧
      ((∀ d : BiHom (t-(s+1)) (t-c)
          (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) (c+(q+1))),
        FiltrationAtLeast model.syntheticTower (s+2) d →
          d ≫ XModLambdaN.map (model.nu.functor.map T.f) (c+(q+1)) = 0) →
        ∀ d : BiHom (t-s) (t-c) (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) (c+(q+1))),
        Detects (model.convergence (.quotient (c+(q+1)) (.nu T.X)))
          (s+1,t,t-c) (finiteTargetLabel model T.X (c+(q+1)) (s+1) t c u)
          (positiveHSourceDesuspend T he hf (c+(q+1)) c s t ε d) →
        d ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁)
          (c+(q+1)) = target)


private theorem finite_native_detection_is_cycle
    (X : ClassicalObject) (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (u : Ambient model X (s,t))
    (a : BiHom (t-s) (t-c)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1))))
    (ha : Detects (model.convergence (.quotient (c+(q+1)) (.nu X)))
      (s,t,t-c) (finiteTargetLabel model X (c+(q+1)) s t c u) a) :
    IsCycle model X (q+1) (s,t) u := by
  have h := (finite_rho_lift_label_and_cycles X (c+(q+1)) (c+(q+1)) c
    le_rfl (by omega) s t u a ha a
    (by rw [(model.quotients.tower _).rho_id,Category.comp_id])).2
  refine ⟨by omega,?_⟩
  convert h using 1
  congr 1
  omega


/-- The actual positive-g classical input supplies the common finite
representative. The final implication uses only annihilation of its
higher-filtration native ambiguity, so either classical criterion can
supply that implication without changing the constructed representative. -/
private theorem positive_second_finite_core
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=1)
    (hh : normalizedExponent model.classicalTower T.h=0) :
    PositiveSecondFiniteCoreStatement T he hT hf hg hh := by
  intro c q hq s t z u v hu hd ey hey ε hε
  dsimp only
  obtain ⟨hc,a,ha,hi⟩ := positive_g_classical_second_may_at_level
    T he hT hf hg hh c q hq s t z u v hu hd ey hey ε hε
  refine ⟨hc,a,ha,hi,?_⟩
  intro hkill d hd
  have hs := ordinary_same_x_label_raw_image T he hf (c+(q+1)) c (by omega)
    s t ε hε (by
      intro b hb
      exact hkill b (by simpa only [add_assoc,show (1:ℤ)+1=2 by norm_num] using hb)) u d a hd ha
  exact hs.trans hi

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
