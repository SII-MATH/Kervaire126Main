module

public import KIP126.Computation.Tmf.Presentation.Algebra.Data
public import KIP126.Def.SpectralSequence.Computation.Predicates

@[expose] public section

/-! The exact target notation of BR21 Table 5.4 / Theorem 5.18.
This is a statement on supplied model coordinates, not a theorem about an
arbitrary algebra object or an identification of such an object with tmf. -/
namespace KIP126.Classical.Adams
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
universe u v

/-- BR21, author's preliminary book, PDF p.213 / printed p.196:
d₃(w₂²)=βg⁴. The source realization must identify the supplied comparison
with the actual tmf Adams tower. The separate quotient identity converts
this target to the selected β⁵g expression without a name-based inference. -/
def TmfAdamsPresentation.BrunerRognesD3 {C : Type u} [StableHomotopyCategory.{u,v} C]
    [HasFunctorialCofiber (C := C)] {H : Mod2EilenbergMacLane (C := C)}
    (model : TmfAdamsPresentation H) : Prop :=
  HasDifferential (adamsTowerInternalSpectralSequence H.unit model.target.X) 3
    (16, 112) (19, 114) model.coordinates.v2Sixteen model.coordinates.betaGFour

end KIP126.Classical.Adams

