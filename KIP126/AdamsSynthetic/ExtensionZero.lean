module

public import KIP126.AdamsSynthetic.Extension
public import Mathlib.Algebra.Category.ModuleCat.Projective

@[expose] section

/-! Length-zero extensions are the E-infinity action of the same actual map.
The general arrow version records projectivity; element consumers use the
free rank-one module and need no extra hypothesis. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.Core.SpectralSequence
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit F} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

/-- The actual E∞ map, after the prescribed canonical identifications, is
exactly the graded map of the same filtered homotopy map. -/
public theorem ConvergentMap.infinity_action_graded
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence) (i : Tridegree) :
    (cx.identification i).hom ≫
      M.filteredMap.inducedGrMap i.1 (i.2.1-i.1,i.2.2) =
      (F.map g).eInftyMap i ≫ (cy.identification i).hom := by
  have h := M.comparison.iso_compat i
  rw [M.infinity_eq] at h
  simpa only [SyntheticTowerConvergence.toConvergence, Filtration.transportGraded_self,
    Category.comp_id, ConvergentMap.filteredMap, ConvergenceMorphism.filteredMap,
    FilteredMorphism.inducedGrMap, SyntheticAdamsFamily.map] using h.symm

/-- At length zero a projective test object supplies the source lift. -/
public theorem ConvergentMap.extensionEquation_zero
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (i : Tridegree) {T : ModuleCat.{v} ℤ} [Projective T]
    (x : T ⟶ ((F.obj X).sequence.ssData i).eInfty) :
    M.ExtensionEquation (i.2.1-i.1,i.2.2) i.1 0 rfl
      (by simp [SyntheticTowerConvergence.toConvergence])
      x (x ≫ (F.map g).eInftyMap i) := by
  unfold ConvergentMap.ExtensionEquation
  apply (FilteredMapExtension.relation_zero_iff_of_projective _ _ _ _ _).mpr
  simpa only [toGraded, SyntheticTowerConvergence.toConvergence,
    Filtration.transportGraded, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id] using
    congrArg (fun k => x ≫ k) (M.infinity_action_graded i)

/-- The same zero-length equation with an explicitly chosen stem reindexing. -/
public theorem ConvergentMap.extensionEquation_zero_reindex
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (i : Tridegree) (p : ℤ × ℤ) (s : ℤ)
    (hi : cx.toConvergence.reindex i = (s,p))
    {T : ModuleCat.{v} ℤ} [Projective T]
    (x : T ⟶ ((F.obj X).sequence.ssData i).eInfty) :
    M.ExtensionEquation p s 0 hi
      (by simpa only [SyntheticTowerConvergence.toConvergence, add_zero] using hi)
      x (x ≫ (F.map g).eInftyMap i) := by
  have hs : i.1 = s := congrArg Prod.fst hi
  have hp : (i.2.1-i.1,i.2.2) = p := congrArg Prod.snd hi
  subst s
  subst p
  exact M.extensionEquation_zero i x

private theorem extensionEquation_zero_transport
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (i j : Tridegree) (p : ℤ × ℤ) (s : ℤ)
    (hi : cx.toConvergence.reindex i = (s,p))
    (hj : cy.toConvergence.reindex j = (s+0,p)) (hij : i=j)
    {T : ModuleCat.{v} ℤ} [Projective T]
    (x : T ⟶ ((F.obj X).sequence.ssData i).eInfty) :
    M.ExtensionEquation p s 0 hi hj x
      ((x ≫ (F.map g).eInftyMap i) ≫
        eqToHom (congrArg (fun k => ((F.obj Y).sequence.ssData k).eInfty) hij)) := by
  subst j
  simpa only [eqToHom_refl, Category.comp_id] using
    M.extensionEquation_zero_reindex i p s hi x

public theorem elementMap_comp {A B : ModuleCat.{v} ℤ} (x : A) (f : A ⟶ B) :
    elementMap (f x) = elementMap x ≫ f := by
  ext z
  simp [elementMap]

/-- The element-level zero-length extension. Index transport only rewrites
`s + 0`; the target is the actual family map on E∞, never a selected label. -/
public theorem towerExtensionEquation_zero
    (M : ConvergentMap F g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty) :
    TowerExtensionEquation M p s 0 x
      ((eqToHom (by simp) :
        ((F.obj Y).sequence.ssData (s,p.1+s,p.2)).eInfty ⟶
        ((F.obj Y).sequence.ssData (s+0,p.1+(s+0),p.2)).eInfty)
        ((F.map g).eInftyMap (s,p.1+s,p.2) x)) := by
  unfold TowerExtensionEquation
  rw [elementMap_comp, elementMap_comp]
  exact extensionEquation_zero_transport M (s,p.1+s,p.2)
    (s+0,p.1+(s+0),p.2) p s _ _ (by simp) (elementMap x)
end
end KIP126.AdamsSynthetic
