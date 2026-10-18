module

public import KIP126.ProofTools.Operations
import all KIP126.ProofTools.Operations
import all KIP126.ProofTools.GeneralizedLeibniz.LevelLanguage

/-! Public predicates for the generalized Leibniz square at a specified
lambda level in the fixed standard model. The actual quotient exponent is
`page + level - 1`, and its weight is `t + e(f) - level`.

The finite extension packages actual infinity classes, their representatives,
and the extension equation. Crossing conditions quantify essential extensions
on the three actual maps in that same square. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Core.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard
noncomputable section

/-- The actual quotient-shift image of the native finite label `lambda^level x`.
The chosen comparison respects both quotient inclusion and absolute boundary.
Its construction is private; its value is an E₂ class of this actual object. -/
@[no_expose] public def levelFiniteSourceLabel (X : ClassicalObject) (q : ℕ)
    (e s t : ℤ) (level : ℕ) (x : Ambient model X (s,t)) :
    (model.family.obj ((SyntheticObject.quotient q (.shift (0,e) (.nu X))).obj
      model.nu model.auxiliary)).E₂ (s,(t-s)+s,t+e-level) :=
  KIP126.ProofTools.Internal.Leibniz.levelFiniteSourceLabel X q e s t level x

/-- A finite extension in quotient `page + level - 1` with source label
`lambda^level x` and target label `lambda^(level + m - e(f)) y`.
Both representatives and the equation belong to the same actual finite map. -/
public def LevelFiniteExtension (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m)) : Prop :=
  2 ≤ page ∧
  ∃ hm : (normalizedExponent model.classicalTower f : ℤ) ≤ m,
    m ≤ (page:ℤ)-2+normalizedExponent model.classicalTower f ∧
    ∃ (source : ((model.family.obj ((SyntheticObject.quotient (page+level-1)
        (extensionSourceObject model X Y f)).obj model.nu model.auxiliary)).sequence.ssData
          (s,(t-s)+s,t+normalizedExponent model.classicalTower f-level)).eInfty)
      (target : ((model.family.obj ((SyntheticObject.quotient (page+level-1) (.nu Y)).obj
        model.nu model.auxiliary)).sequence.ssData
          (s+m,(t-s)+(s+m),t+normalizedExponent model.classicalTower f-level)).eInfty),
      HasInfinityRepresentative _ 2 _
        (levelFiniteSourceLabel X (page+level-1) (normalizedExponent model.classicalTower f)
          s t level x) source ∧
      HasInfinityRepresentative _ 2 _
        (regradeE2 (by ext <;> dsimp; omega)
          ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary))
            (page+level-1)).pageMap 2
            (s+m,t+m,t+normalizedExponent model.classicalTower f-level)
            (nuWeightLabel model Y (s+m) (t+m)
              (t+normalizedExponent model.classicalTower f-level) (by omega) y))) target ∧
      TowerExtensionEquation
        (model.convergentMap (.quotient (page+level-1) (extensionSourceObject model X Y f))
          (.quotient (page+level-1) (.nu Y)) (finiteExtensionMap model X Y f (page+level-1)))
        (t-s,t+normalizedExponent model.classicalTower f-level) s m source target

/-- No essential crossing on the actual finite-map edge, in quotient
`page + level - 1` at fixed stem/weight `(t-s, t+e(f)-level)`. -/
public def LevelFiniteNoCrossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ) : Prop :=
  ∀ u v : ℤ, s < u → u ≤ v → v ≤ s+m →
    ∀ source target, ¬ TowerEssentialExtension
      (model.convergentMap
        (.quotient (page+level-1) (extensionSourceObject model X Y f))
        (.quotient (page+level-1) (.nu Y)) (finiteExtensionMap model X Y f (page+level-1)))
      (t-s,t+normalizedExponent model.classicalTower f-level) u (v-u) source target

/-- No essential crossing on the actual quotient-boundary edge, in quotient
`page + level - 1` at fixed stem/weight `(t-s, t+e(f)-level)`. -/
public def LevelBoundaryNoCrossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r s t : ℤ) : Prop :=
  ∀ u v : ℤ, s < u → u ≤ v → v ≤ s+r →
    ∀ source target, ¬ TowerEssentialExtension
      (model.convergentMap
        (.quotient (page+level-1) (extensionSourceObject model X Y f))
        (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
        (XModLambdaN.proj ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)
          (page+level-1) ≫
          (KIP126.ProofTools.Operations.biSuspensionIso (page+level-1:ℕ)
            ((extensionSourceObject model X Y f).obj model.nu model.auxiliary)).inv))
      (t-s,t+normalizedExponent model.classicalTower f-level) u (v-u) source target

/-- No essential crossing on the actual shifted bottom map, starting in
filtration `s+r` at stem/weight `(t-s, t+e(f)-level)`. This is tested after
propagating the infinite extension to level `r-page`. -/
public def LevelBottomNoCrossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r l s t : ℤ) : Prop :=
  ∀ u v : ℤ, s+r < u → u ≤ v → v ≤ s+r+l →
    ∀ source target, ¬ TowerEssentialExtension
      (model.convergentMap
        (.shift (1,-((page+level-1:ℕ):ℤ)) (extensionSourceObject model X Y f))
        (.shift (1,-((page+level-1:ℕ):ℤ)) (.nu Y))
        ((SyntheticCategory.biShift (1,-((page+level-1:ℕ):ℤ))).map
          (model.normalizedMap X Y f).map))
      (t-s,t+normalizedExponent model.classicalTower f-level) u (v-u) source target

private theorem levelFiniteExtension_iff_internal (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+m,t+m)) :
    LevelFiniteExtension X Y f page level m s t x y ↔
      KIP126.ProofTools.Internal.Leibniz.LevelFiniteExtension X Y f page level m s t x y := by
  constructor
  · rintro ⟨hpage,hm,hmUpper,source,target,hs,ht,heq⟩
    exact ⟨⟨hpage,hm,hmUpper,source,target,hs,ht,heq⟩⟩
  · rintro ⟨W⟩
    exact ⟨W.page_ge_two,W.length_lower,W.length_upper,W.source,W.target,
      W.source_rep,W.target_rep,W.equation⟩

private theorem levelFiniteNoCrossing_iff_internal (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (m s t : ℤ) :
    LevelFiniteNoCrossing X Y f page level m s t ↔
      KIP126.ProofTools.Internal.Leibniz.LevelFiniteNoCrossing X Y f page level m s t := Iff.rfl

private theorem levelBoundaryNoCrossing_iff_internal (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r s t : ℤ) :
    LevelBoundaryNoCrossing X Y f page level r s t ↔
      KIP126.ProofTools.Internal.Leibniz.LevelBoundaryNoCrossing X Y f page level r s t := Iff.rfl

private theorem levelBottomNoCrossing_iff_internal (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (r l s t : ℤ) :
    LevelBottomNoCrossing X Y f page level r l s t ↔
      KIP126.ProofTools.Internal.Leibniz.LevelBottomNoCrossing X Y f page level r l s t := Iff.rfl

end
end KIP126.ProofTools.Standard
