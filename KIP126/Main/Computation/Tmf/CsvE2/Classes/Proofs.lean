module

public import KIP126.Computation.Tmf.CsvE2.Classes.Data
public import KIP126.Main.Computation.Tmf.CsvE2.Proofs

@[expose] public section

namespace KIP126.Classical.Adams.Tmf.CsvE2
theorem betaGFour_eq_betaFiveG : betaGFour = betaFiveG :=
  Subtype.ext betaGFourValue_eq_betaFiveGValue


end KIP126.Classical.Adams.Tmf.CsvE2
