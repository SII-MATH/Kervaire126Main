module

public import KIP126.AdamsSynthetic.Tower

@[expose] section

/-! Suspension comparisons of the same given Adams towers. The layer and
connecting equations preserve the original suspension sign; no unrelated
E₂ equivalence is selected. -/

namespace KIP126.AdamsSynthetic
open CategoryTheory KIP126.StableHomotopy KIP126.Classical.Adams
open KIP126.Core.SpectralSequence
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] {H : C} {unit : SphereSpectrum ⟶ H}
  {A : ClassicalAdamsFamily C}

/-- Stage and cofiber comparisons for one object and its ordinary suspension. -/
public structure ClassicalTowerSuspension (P : ClassicalTowerPresentation unit A) (X : C) where
  tower : ∀ s : ℤ, (P.tower (X⟦(1 : ℤ)⟧)).stageAt s ≅
    ((P.tower X).stageAt s)⟦(1 : ℤ)⟧
  tower_zero : (tower 0).hom ≫ (P.tower X).zeroIso.hom⟦(1 : ℤ)⟧' =
    (P.tower (X⟦(1 : ℤ)⟧)).zeroIso.hom
  tower_comm : ∀ (s t : ℤ) (hst : s ≤ t),
    (tower t).hom ≫ ((P.tower X).mapAt hst)⟦(1 : ℤ)⟧' =
      (P.tower (X⟦(1 : ℤ)⟧)).mapAt hst ≫ (tower s).hom
  layer : ∀ s : ℤ, (P.tower (X⟦(1 : ℤ)⟧)).layer s ≅
    ((P.tower X).layer s)⟦(1 : ℤ)⟧
  layer_inclusion : ∀ s : ℤ,
    HasFunctorialCofiber.cofibι
        ((P.tower (X⟦(1 : ℤ)⟧)).mapAt (show s ≤ s+1 by omega)) ≫
        (layer s).hom =
      (tower s).hom ≫ (HasFunctorialCofiber.cofibι
        ((P.tower X).mapAt (show s ≤ s+1 by omega)))⟦(1 : ℤ)⟧'
  layer_connecting : ∀ s : ℤ,
    (layer s).hom ≫ (HasFunctorialCofiber.cofibδ
        ((P.tower X).mapAt (show s ≤ s+1 by omega)))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorComm C (1 : ℤ) (1 : ℤ)).hom.app ((P.tower X).stageAt (s+1)) =
      -(HasFunctorialCofiber.cofibδ
        ((P.tower (X⟦(1 : ℤ)⟧)).mapAt (show s ≤ s+1 by omega)) ≫
          (tower (s+1)).hom⟦(1 : ℤ)⟧')

namespace ClassicalTowerSuspension
variable {P : ClassicalTowerPresentation unit A} {X : C}

public def desuspendFirstPage (S : ClassicalTowerSuspension P X) (s t : ℤ) :
    (P.tower (X⟦(1 : ℤ)⟧)).FirstPage (s,t) →+
      (P.tower X).FirstPage (s,t-1) where
  toFun z :=
    eqToHom (congrArg (Sphere (C := C))
      (show (t-1)-s = (t-s)-1 by omega)) ≫
      AbstractAdamsTower.desuspend ((P.tower X).layer s) (t-s) (z ≫ (S.layer s).hom)
  map_zero' := by simp only [Limits.zero_comp, map_zero, Limits.comp_zero]
  map_add' a b := by simp only [Preadditive.add_comp, map_add, Preadditive.comp_add]

/-- Desuspension of the actual common page-two representatives. Both labels
come from the same supplied tower presentation and actual quotient projections. -/
public def DesuspendsClass (S : ClassicalTowerSuspension P X) (s t : ℤ)
    (sx : (A.obj (X⟦(1 : ℤ)⟧)).Page 2 (s,t))
    (x : (A.obj X).Page 2 (s,t-1)) : Prop :=
  ∃ (a : (Subobject.underlying.obj (((A.obj (X⟦(1 : ℤ)⟧)).ssData (s,t)).Z 0) : ModuleCat.{v} ℤ))
    (b : (Subobject.underlying.obj (((A.obj X).ssData (s,t-1)).Z 0) : ModuleCat.{v} ℤ)),
    ((((A.obj (X⟦(1 : ℤ)⟧)).ssData (s,t)).pageπ 0) ≫
      eqToHom (by simp only [KIP126.Core.SpectralSequence.Page, A.firstPage, sub_self, Int.toNat_zero,
        Nat.cast_zero])) a = sx ∧
    ((((A.obj X).ssData (s,t-1)).pageπ 0) ≫
      eqToHom (by simp only [KIP126.Core.SpectralSequence.Page, A.firstPage, sub_self, Int.toNat_zero,
        Nat.cast_zero])) b = x ∧
    S.desuspendFirstPage s t
      ((((P.sequence (X⟦(1 : ℤ)⟧)).ambient (s,t)).hom
        ((((A.obj (X⟦(1 : ℤ)⟧)).ssData (s,t)).Z 0).arrow a)).val) =
      ((((P.sequence X).ambient (s,t-1)).hom
        ((((A.obj X).ssData (s,t-1)).Z 0).arrow b)).val)

end ClassicalTowerSuspension
end
end KIP126.AdamsSynthetic
