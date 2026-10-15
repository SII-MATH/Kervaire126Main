module

public import KIP126.Def.Synthetic.AdamsFiltration.Proofs

@[expose] public section

namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.SpectralSequence
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
noncomputable section
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)] {H : Syn} (unit : S_0_0 ⟶ H)

/-- The filtration is constructed from the tower; it cannot be replaced by
an independently selected filtration to make a detection statement true. -/
def towerFiltration (X : Syn) : Filtration (syntheticHomotopy X) where
  F s p := (ModuleCat.subobjectModule _).symm (towerFiltrationSubmodule unit X s p)
  mono s p := (ModuleCat.subobjectModule _).symm.monotone
    (towerFiltrationSubmodule_antitone unit X p (by omega : s ≤ s + 1))

/-- Only the E∞ identification remains input. Convergence is supplied for
the objects where it is needed, not asserted for every synthetic spectrum. -/
structure TowerConvergence (F : SyntheticAdamsFamily Syn) (X : Syn) where
  identification : ∀ i : Tridegree,
    ((F.obj X).sequence.ssData i).eInfty ≅
      (towerFiltration unit X).associatedGraded i.1 (i.2.1 - i.1, i.2.2)

def TowerConvergence.toSynthetic {F : SyntheticAdamsFamily Syn} {X : Syn}
    (c : TowerConvergence unit F X) : SyntheticAdamsConvergence F X where
  filtration := towerFiltration unit X
  identification := c.identification
end
end KIP126.Synthetic.SpectralSequence
