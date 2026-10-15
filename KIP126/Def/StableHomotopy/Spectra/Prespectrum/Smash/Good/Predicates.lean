module

public import KIP126.Def.StableHomotopy.Spectra.Generators

@[expose] public section

namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

/-- Levelwise compactly generated, well-based objects of based CW homotopy type. -/
def IsGood (X : Prespectrum.{0}) : Prop := ∀ n, (X.level n).IsGood

end Prespectrum
end KIP126.StableHomotopy.Spectra
