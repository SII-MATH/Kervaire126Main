module

public import KIP126.Def.Synthetic.AdamsSequence.Data
public import KIP126.Def.SpectralSequence.BoundedExtension.SpectralSequence.Proofs

@[expose] public section

/-! The extension sequence of an actual synthetic map. Both abutments are
actual bigraded homotopy groups; both maps are induced by that same map.
Bounded convergence is explicit input, not asserted for arbitrary objects. -/

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory CategoryTheory.Limits KIP126.SpectralSequence
open KIP126.Synthetic.Context

universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- Postcomposition by the specified synthetic map on actual homotopy. -/
def syntheticHomotopyMap {X Y : Syn} (g : X ⟶ Y) (p : ℤ × ℤ) :
    syntheticHomotopy X p ⟶ syntheticHomotopy Y p :=
  ModuleCat.ofHom (Preadditive.rightComp (Smn p.1 p.2) g).toIntLinearMap

/-- A bounded convergence input for the extension sequence of `g`.
The compatibility fields pin the generic convergence morphism to both the
actual homotopy map and the canonical E∞ map of the same Adams family. -/
structure SyntheticExtensionData (F : SyntheticAdamsFamily Syn)
    {X Y : Syn} (g : X ⟶ Y) where
  source : SyntheticAdamsConvergence F X
  target : SyntheticAdamsConvergence F Y
  map : ConvergenceMorphism source.toConvergence target.toConvergence
  aMap_eq : map.aMap = syntheticHomotopyMap g
  eMap_eq : map.eMap = (F.functor.map g).eInftyMap
  source_bounded : source.filtration.IsBounded
  target_bounded : target.filtration.IsBounded

namespace SyntheticExtensionData
variable {F : SyntheticAdamsFamily Syn} {X Y : Syn} {g : X ⟶ Y}

def complex (D : SyntheticExtensionData F g) (degree : ℤ × ℤ) :=
  (BoundedExtensionSS.mk' D.source.toConvergence D.target.toConvergence
    D.map D.source_bounded D.target_bounded).complex degree

/-- Internal ESS at a fixed homotopy stem and weight, with indices `(s,1)`
and `(s,0)` for the two terms. -/
def ess (D : SyntheticExtensionData F g) (degree : ℤ × ℤ) :
    KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ) :=
  (BoundedExtensionSS.mk' D.source.toConvergence D.target.toConvergence
    D.map D.source_bounded D.target_bounded).ess degree

/-- The ESS source ambient is the E∞ term of the same source object. -/
def sourceIso (D : SyntheticExtensionData F g) (s : ℤ) (degree : ℤ × ℤ) :
    ((D.ess degree).ssData (s, 1)).V ≅
      ((F.obj X).sequence.ssData (s, degree.1 + s, degree.2)).eInfty := by
  let E := BoundedExtensionSS.mk' D.source.toConvergence D.target.toConvergence
    D.map D.source_bounded D.target_bounded
  exact eqToIso (E.e0PageAtOne_eq degree s) ≪≫
    eqToIso (by simp only [add_sub_cancel_right]) ≪≫
    (D.source.identification (s, degree.1 + s, degree.2)).symm

/-- The ESS target ambient is the E∞ term of the same target object. -/
def targetIso (D : SyntheticExtensionData F g) (s : ℤ) (degree : ℤ × ℤ) :
    ((D.ess degree).ssData (s, 0)).V ≅
      ((F.obj Y).sequence.ssData (s, degree.1 + s, degree.2)).eInfty := by
  let E := BoundedExtensionSS.mk' D.source.toConvergence D.target.toConvergence
    D.map D.source_bounded D.target_bounded
  exact eqToIso (E.e0PageAtZero_eq degree s) ≪≫
    eqToIso (by simp only [add_sub_cancel_right]) ≪≫
    (D.target.identification (s, degree.1 + s, degree.2)).symm

end SyntheticExtensionData
end
end KIP126.Synthetic.SpectralSequence
