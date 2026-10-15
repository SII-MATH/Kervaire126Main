module
import all KIP126.Main.Internal.NuThree.Assembly
import all KIP126.Main.Internal.NuNinth.Lift
/-! The final fixed ν₉ interface, NuNinth:1944–1961 at
bbac1fc05843 (MIT). It consumes the actual ν₃→ν₅→ν₉ proof chain. -/
@[expose] section
namespace KIP126.Main.Internal.NuNinth
open KIP126.Main.SectionSeven
private theorem nu_extension_in_ninth_quotient :
    NuExtension9 KIP126.Computation.Standard.X KIP126.Computation.Standard.Y hopfNu :=
  nu_ninth_of_fifth_complete hopfNu NuThree.nu_extension_in_fifth_quotient
end KIP126.Main.Internal.NuNinth
