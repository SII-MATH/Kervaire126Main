module

public import KIP126.Def.Comparison.ClassicalSynthetic.RealizationTower.Proofs

@[expose] public section

/-! A realization map on Adams pages, induced by the ACTUAL exact strong
monoidal functor. The layer map is a formula in F.map, F's monoidal maps,
the coefficient identification and the tower identification. There is no
freely supplied map of E1/E2 groups. This is the direction of tau inversion
in BHS, SynRevAdams.tex (before Theorem `thm:synth-ASS`).

The comparisons are structural model data; existence and compatibility
proofs are separate obligations. No BHS differential or survivor is assumed.
-/
namespace KIP126.Comparison.ClassicalSynthetic.RealizationTower
open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.Classical.Adams
universe u v w
noncomputable section
variable {S : Type u} [StableHomotopyCategory.{u, v} S]
  [HasFunctorialCofiber (C := S)]
  {C : Type w} [StableHomotopyCategory.{w, v} C]
  [HasFunctorialCofiber (C := C)]
  (F : S ⥤ C) [F.Monoidal] [F.CommShift ℤ] [F.Additive]
  {HS : S} {HC : C} (unitS : 𝟙_ S ⟶ HS) (unitC : 𝟙_ C ⟶ HC)
  (coefficient : F.obj HS ≅ HC)

variable {F unitS unitC coefficient Y X}
  {base : F.obj Y ≅ X} (P : Comparison F unitS unitC coefficient Y X base)
def cycleMap (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsCycles unitS Y r hr s t →ₗ[ℤ] adamsCycles unitC X r hr s t :=
  ((e1Map P s t).comp (adamsCycles unitS Y r hr s t).subtype).codRestrict
    (adamsCycles unitC X r hr s t)
    (fun a => e1Map_mem_cycles P r hr s t a.val a.property)

def pageMap (r : ℕ) (hr : 1 ≤ r) (s t : ℤ) :
    adamsPage unitS Y r hr s t →ₗ[ℤ] adamsPage unitC X r hr s t :=
  (adamsCycleBoundaries unitS Y r hr s t).mapQ
    (adamsCycleBoundaries unitC X r hr s t) (cycleMap P r hr s t) (by
      intro a ha
      exact e1Map_mem_boundaries P r hr s t a.val ha)

/-- The E2 map is the same map on quotient representatives, transported
through the existing identity-on-representatives internal-page isos. -/
def internalE2Map (p : ℤ × ℤ) :
    (adamsTowerInternalSpectralSequence unitS Y).Page 2 p →ₗ[ℤ]
      (adamsTowerInternalSpectralSequence unitC X).Page 2 p :=
  (adamsTowerSSDataPageIso unitC X p.1 p.2 0).inv.hom.comp
    ((pageMap P 2 (by decide) p.1 p.2).comp
      (adamsTowerSSDataPageIso unitS Y p.1 p.2 0).hom.hom)

end
end KIP126.Comparison.ClassicalSynthetic.RealizationTower
