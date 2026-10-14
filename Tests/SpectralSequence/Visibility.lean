module

-- Even direct ordinary imports of implementation files do not expose helpers.
import KIP126.Def.SpectralSequence.ModuleQuotient.Proofs
import KIP126.Def.SpectralSequence.FilteredDifferential.Helpers
import KIP126.Def.SpectralSequence.Completion.UniversalProperty.Proofs

#check_failure KIP126.Core.SpectralSequence.submoduleCokernelIso
#check_failure KIP126.Core.SpectralSequence.subobject_mem_iff_of_inverse
#check_failure KIP126.Core.SpectralSequence.FilteredComplex.DifferentialHelpers.kernelSubobject_epiDesc'
#check_failure KIP126.Core.SpectralSequence.Filtration.completionLift
