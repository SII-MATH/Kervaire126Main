module

public import KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.LevelLanguage
import all KIP126.ProofTools.GeneralizedLeibniz.LevelGL
import all KIP126.ProofTools.GeneralizedLeibniz.LevelZero

/-! The generalized Leibniz rule with an arbitrary explicit lambda level.
This public entry point reuses the proved four-edge argument at the actual
quotient and weight. The original public generalized Leibniz statement is
unchanged. The zero-level input conversion does not identify its original
crossing predicates with the actual crossing conditions used here. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section

/-- AimPaper's generalized Leibniz square at any source lambda level.
The finite extension is in quotient `page + level - 1`. Its upper or left
edge must have no crossing, and its actual propagated bottom edge must have
no crossing. There is no upper bound on `level`. The infinite input is the
original zero-level extension; its required propagation is proved internally. -/
public theorem generalizedLeibnizAtLevel
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r m l s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (xInfinity : Ambient model X (s+r,t+r-1))
    (yInfinity : Ambient model Y (s+r+l,t+r-1+l))
    (hpage : 2 ≤ page) (hpr : (page:ℤ) ≤ r)
    (hm : (normalizedExponent model.classicalTower f:ℤ) ≤ m)
    (hmUpper : m ≤ (page:ℤ)-2+normalizedExponent model.classicalTower f)
    (hl : (normalizedExponent model.classicalTower f:ℤ) ≤ l)
    (hxInfinity : IsPermanent model X (s+r,t+r-1) xInfinity)
    (hyInfinity : IsPermanent model Y (s+r+l,t+r-1+l) yInfinity)
    (hdx : DifferentialAt model X r (s,t) (s+r,t+r-1) x xInfinity)
    (hFinite : LevelFiniteExtension X Y f page level m s t x y)
    (hInfinity : InfiniteExtension model X Y f l (s+r) (t+r-1) xInfinity yInfinity)
    (hsourceCrossing : LevelBoundaryNoCrossing X Y f page level r s t ∨
      LevelFiniteNoCrossing X Y f page level m s t)
    (hbottomCrossing : LevelBottomNoCrossing X Y f page level r l s t) :
    DifferentialAt model Y (r+l-m) (s+m,t+m) (s+r+l,t+r-1+l) y yInfinity := by
  obtain ⟨WFinite⟩ := (levelFiniteExtension_iff_internal X Y f page level m s t x y).mp hFinite
  obtain ⟨WInfinity⟩ := hInfinity
  exact KIP126.ProofTools.Internal.Leibniz.generalizedLeibniz_at_level
    X Y f page level r m l s t x y xInfinity yInfinity hpage hpr hm hmUpper hl
    hxInfinity hyInfinity hdx WFinite WInfinity
    (hsourceCrossing.imp
      (levelBoundaryNoCrossing_iff_internal X Y f page level r s t).mp
      (levelFiniteNoCrossing_iff_internal X Y f page level m s t).mp)
    ((levelBottomNoCrossing_iff_internal X Y f page level r l s t).mp hbottomCrossing)

/-- Every original finite extension supplies the corresponding zero-level
finite input. This preserves its actual map equation and compares its
representative labels; it makes no claim about crossing conditions. -/
public theorem finiteExtensionAtLevelZero
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m))
    (h : FiniteExtension model X Y f page m s t x y) :
    LevelFiniteExtension X Y f page 0 m s t x y := by
  obtain ⟨W⟩ := h
  apply (levelFiniteExtension_iff_internal X Y f page 0 m s t x y).mpr
  exact ⟨KIP126.ProofTools.Internal.Leibniz.level_finite_extension_of_zero
    X Y f page m s t x y W⟩

end
end KIP126.ProofTools.Standard
