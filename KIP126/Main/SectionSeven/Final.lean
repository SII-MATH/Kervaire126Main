module

import all KIP126.Main.SectionSeven.NuTarget
import all KIP126.Main.SectionSeven.CofiberRigidity
/-! The proved final logical step of LWX Proposition 7.9.
Adapted from Kervaire126 bbac1fc05843,
Main/Solution/Route/Section7/Final.lean:35-42 (MIT; see the retained source LICENSE).
Fixed upstream facts are called directly. Local paper proof-port obligations
remain in the corresponding SectionSeven stages, not in upstream result packs. -/

@[expose] section
namespace KIP126.Main.SectionSeven

private theorem eta_extension_excluded_of_d6_vanishes (hc3 : Stem126D6Vanishes) : ¬ EtaExtensionDetection := by
  intro hc5
  obtain ⟨r, hr, hr', hhit⟩ :=
    target_divisibility_forces_cnu_incoming (target_nu_divisible hc3 hc5)
  exact KIP126.Computation.Standard.cofiber_target_not_hit_through5.2.2 r hr hr' hhit

end KIP126.Main.SectionSeven
