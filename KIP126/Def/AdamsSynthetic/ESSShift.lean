module

public import KIP126.Def.AdamsSynthetic.System
public import KIP126.Def.AdamsSynthetic.ExtensionZero
public import KIP126.Def.SpectralSequence.Transport

@[expose] section

/-! Structural transport along λ-boundary suspension. All filtrations and
convergence maps belong to the given model and its fixed object closure.
The generic filtered-map calculus handles unbounded extension equations;
its ESS differential interpretation separately requires boundedness and
projective test objects. -/
namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Core.SpectralSequence KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- The canonical map of actual homotopy classes under the given bigraded shift. -/
public def shiftHomotopyClass (δ p : ℤ × ℤ) {X : Syn} (a : BiHom p.1 p.2 X) :
    BiHom (p+δ).1 (p+δ).2 ((SyntheticCategory.biShift δ).obj X) :=
  (SyntheticCategory.biShift_comp p δ).inv.app S_0_0 ≫
    (SyntheticCategory.biShift δ).map a

/-- Convergence at the stem-indexed infinity page, with only arithmetic reindexing. -/
public def towerGradedIso {H : Syn} {unit : S_0_0 ⟶ H}
    {F : SyntheticAdamsFamily Syn} {P : SyntheticTowerPresentation unit F} {X : Syn}
    (c : SyntheticTowerConvergence P X) (p : ℤ × ℤ) (s : ℤ) :
    ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty ≅
      c.filtration.associatedGraded s p :=
  c.identification (s,p.1+s,p.2) ≪≫ eqToIso (by simp)

/-- The infinity-page identification is determined by the same convergence
and filtered-piece isomorphism; it is not another freely chosen comparison. -/
public def towerInfinityIso {H : Syn} {unit : S_0_0 ⟶ H}
    {F : SyntheticAdamsFamily Syn} {P : SyntheticTowerPresentation unit F} {X Y : Syn}
    (cx : SyntheticTowerConvergence P X) (cy : SyntheticTowerConvergence P Y)
    {p q : ℤ × ℤ} (e : FilteredPieceIso cx.filtration cy.filtration p q) (s : ℤ) :
    ((F.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty ≅
      ((F.obj Y).sequence.ssData (s,q.1+s,q.2)).eInfty :=
  towerGradedIso cx p s ≪≫ e.gradedIso s ≪≫ (towerGradedIso cy q s).symm

/-- A uniform shift comparison on the selected closure. Page representatives
are transported for every valid finite page, including representatives of
infinite-page classes. Actual homotopy maps determine the ambient transport. -/
public structure SyntheticESSShiftComparison (D : Model C Syn) (δ : ℤ × ℤ) where
  filtered : ∀ (X : SyntheticObject) (p : ℤ × ℤ),
    FilteredPieceIso (D.convergence X).filtration
      (D.convergence (.shift δ X)).filtration p (p+δ)
  ambient_eq : ∀ (X : SyntheticObject) (p : ℤ × ℤ)
      (a : BiHom p.1 p.2 (X.obj D.nu D.auxiliary)),
    (filtered X p).ambient.hom a = shiftHomotopyClass δ p a
  page : ∀ (X : SyntheticObject) (r : ℤ) (_hr : 2 ≤ r) (p : ℤ × ℤ) (s : ℤ),
    (D.family.obj (X.obj D.nu D.auxiliary)).Page r (s,p.1+s,p.2) ≅
      (D.family.obj ((SyntheticObject.shift δ X).obj D.nu D.auxiliary)).Page r
        (s,(p+δ).1+s,(p+δ).2)
  representative_iff : ∀ (X : SyntheticObject) (r : ℤ) (hr : 2 ≤ r)
      (p : ℤ × ℤ) (s : ℤ)
      (x : (D.family.obj (X.obj D.nu D.auxiliary)).Page r (s,p.1+s,p.2))
      (z : ((D.family.obj (X.obj D.nu D.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty),
    HasInfinityRepresentative _ r (s,p.1+s,p.2) x z ↔
      HasInfinityRepresentative _ r (s,(p+δ).1+s,(p+δ).2)
        ((page X r hr p s).hom x)
        ((towerInfinityIso (D.convergence X) (D.convergence (.shift δ X))
          (filtered X p) s).hom z)

namespace SyntheticESSShiftComparison
variable {D : Model C Syn} {δ : ℤ × ℤ} (S : SyntheticESSShiftComparison D δ)

/-- The transport square is tied to the family maps of this very `g` and
its shift, with the given convergence on both ends. -/
public def transport (X Y : SyntheticObject)
    (g : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary) (p : ℤ × ℤ) :
    FilteredMapTransport (D.convergentMap X Y g).filteredMap
      (D.convergentMap (.shift δ X) (.shift δ Y)
        ((SyntheticCategory.biShift δ).map g)).filteredMap p (p+δ) where
  source := S.filtered X p
  target := S.filtered Y p
  map_comm := by
    simp only [ConvergentMap.filteredMap_map]
    ext a
    change syntheticHomotopyMap ((SyntheticCategory.biShift δ).map g) (p+δ)
        ((S.filtered X p).ambient.hom a) =
      (S.filtered Y p).ambient.hom (syntheticHomotopyMap g p a)
    rw [S.ambient_eq, S.ambient_eq]
    change shiftHomotopyClass δ p a ≫ (SyntheticCategory.biShift δ).map g =
      shiftHomotopyClass δ p (a ≫ g)
    simp [shiftHomotopyClass, Functor.map_comp, Category.assoc]

/-- A representative equation shifts in both directions, with its complete
source and target ambiguity handled by `transport.targetCoset_iff`. -/
public theorem equation_iff (X Y : SyntheticObject)
    (g : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary) (p : ℤ × ℤ) (s n : ℤ)
    {T : ModuleCat.{v} ℤ}
    (x : T ⟶ (D.convergence X).filtration.associatedGraded s p)
    (y : T ⟶ (D.convergence Y).filtration.associatedGraded (s+n) p) :
    FilteredMapExtension.Relation (D.convergentMap X Y g).filteredMap p s n x y ↔
      FilteredMapExtension.Relation
        (D.convergentMap (.shift δ X) (.shift δ Y)
          ((SyntheticCategory.biShift δ).map g)).filteredMap (p+δ) s n
        (x ≫ ((S.filtered X p).gradedIso s).hom)
        (y ≫ ((S.filtered Y p).gradedIso (s+n)).hom) :=
  (S.transport X Y g p).relation_iff x y

/-- The existing E∞ extension witnesses use the same transport.  This applies
both to finite-quotient objects and to untruncated objects without imposing
boundedness on their filtrations. -/
public theorem towerExtensionEquation_iff (X Y : SyntheticObject)
    (g : X.obj D.nu D.auxiliary ⟶ Y.obj D.nu D.auxiliary) (p : ℤ × ℤ) (s n : ℤ)
    (x : ((D.family.obj (X.obj D.nu D.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((D.family.obj (Y.obj D.nu D.auxiliary)).sequence.ssData
      (s+n,p.1+(s+n),p.2)).eInfty) :
    TowerExtensionEquation (D.convergentMap X Y g) p s n x y ↔
      TowerExtensionEquation
        (D.convergentMap (.shift δ X) (.shift δ Y)
          ((SyntheticCategory.biShift δ).map g)) (p+δ) s n
        ((towerInfinityIso (D.convergence X) (D.convergence (.shift δ X))
          (S.filtered X p) s).hom x)
        ((towerInfinityIso (D.convergence Y) (D.convergence (.shift δ Y))
          (S.filtered Y p) (s+n)).hom y) := by
  change FilteredMapExtension.Relation _ p s n
      (elementMap x ≫ (towerGradedIso (D.convergence X) p s).hom)
      (elementMap y ≫ (towerGradedIso (D.convergence Y) p (s+n)).hom) ↔
    FilteredMapExtension.Relation _ (p+δ) s n
      (elementMap _ ≫ (towerGradedIso (D.convergence (.shift δ X)) (p+δ) s).hom)
      (elementMap _ ≫ (towerGradedIso (D.convergence (.shift δ Y)) (p+δ) (s+n)).hom)
  rw [(S.transport X Y g p).relation_iff]
  simp only [elementMap_comp, towerInfinityIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, transport]

end SyntheticESSShiftComparison

/-- Boundary shift in the fixed bigraded closure. Its comparison with
weight shift followed by ordinary suspension is supplied below. -/
public def lambdaBoundaryShiftFunctor (n : ℕ) : Syn ⥤ Syn :=
  SyntheticCategory.biShift (1,-(n:ℤ))

/-- The chosen bigraded realization is the same shift as the legacy
`Σ ∘ Σ^(0,-n)`, up to the specified suspension comparison. -/
public def lambdaBoundaryShiftIso (n : ℕ) :
    (SyntheticCategory.biShift (0,-(n:ℤ)) ⋙ shiftFunctor Syn (1:ℤ)) ≅
      (lambdaBoundaryShiftFunctor (Syn := Syn) n) :=
  Functor.isoWhiskerLeft (SyntheticCategory.biShift (0,-(n:ℤ)))
    (SyntheticCategory.biShift_compat (Syn := Syn) 1).symm ≪≫
      biShiftAddIso (0,-(n:ℤ)) (1,0) (1,-(n:ℤ)) (by ext <;> simp)

/-- The missing structural responsibility as explicit data on one shared
model. Finite λ quotients and untruncated objects are both in its selected
closure. No global instance or bounded infinite ESS is introduced. -/
public structure SyntheticAdamsESSShiftSystem (D : Model C Syn) where
  lambdaBoundary : ∀ n : ℕ, SyntheticESSShiftComparison D (1,-(n:ℤ))

end
end KIP126.AdamsSynthetic
