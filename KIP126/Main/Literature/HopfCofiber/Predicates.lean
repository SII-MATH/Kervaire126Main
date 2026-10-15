module

public import KIP126.Main.Literature.HopfCofiber.Data
public import KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] public section


namespace KIP126.Computation.Near126
open KIP126 KIP126.SpectralSequence

/-- Semantic two-fact slice used by the paper's near-126 argument.  This is a
Main-stage conditional statement about explicitly supplied Cν classes, not an
external literature axiom and not another stage witness. -/
structure HopfCofiberFacts (E : SpectralSequence (ModuleCat ℤ) (ℤ × ℤ))
    (xbar : E.Page 2 (8, 134)) (ybar : E.Page 2 (11, 136))
    (tbar : E.Page 2 (14, 139)) where
  /-- `lem:nuext125`, MainPaper/main.tex:2648. -/
  d3_xbar :
    (HasNonzeroDifferential E 3 (8, 134) (11, 136) xbar ybar)
  /-- `prop:state5false`, MainPaper/main.tex:2776; Table:Cnu126.
  Universal quantification includes arbitrary linear combinations of sources. -/
  tbar_short_incoming :
    (∀ r : ℤ, 2 ≤ r → r ≤ 5 → ¬ HitOnPage E r (14, 139) tbar)

end KIP126.Computation.Near126

namespace KIP126.Classical.Adams
open CategoryTheory KIP126.StableHomotopy

/-- A stable map has a specified filtration-one E₂ representative. This does
not claim a canonical choice of Hopf map or identification with a classical
geometric model. It ties the map and class through the actual sphere tower. -/
def SphereFiltrationOneRepresents (f : SphereThreeMap)
    (x : sphereAdamsSequence.sequence.Page 2 (1, 4)) : Prop :=
  ∃ a : HomotopyGroup 3 (adamsTower standardFoundation.hf2.unit SphereSpectrum 1),
    a ≫ adamsTowerStep standardFoundation.hf2.unit SphereSpectrum 0 = f ∧
      sphereFiltrationOneClass a = x

end KIP126.Classical.Adams
