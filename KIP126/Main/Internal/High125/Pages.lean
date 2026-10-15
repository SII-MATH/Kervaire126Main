module
public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Selected.NormalizedTable
import all KIP126.Main.Internal.PageCalculus
/-! Original finite-page proofs from the pinned Main/Solution/Computation
baseline bbac1fc05843 (MIT), transported along a proved equality with the
same actual Adams sequence. No additional mathematical input. -/
@[expose] section
namespace KIP126.Main.Internal.High125
open CategoryTheory CategoryTheory.Limits KIP126.Core.Algebra
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Main.Internal KIP126.Computation.Table.Raw
open KIP126.Main.Internal.Selected.Normalized
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private theorem page_subsingleton_of_le (E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ))
    (r t s u : ℤ) (hr : 2 ≤ r) (hrt : r ≤ t)
    (hp : Subsingleton (E.Page r (s,u))) : Subsingleton (E.Page t (s,u)) := by
  have hall (a : E.Page t (s,u)) : a=0 := by
    obtain ⟨x,hx⟩ := page_has_initial_representative (by omega) a
    obtain ⟨xr,hxr⟩ := KIP126.Main.Internal.reaches_before hr hrt ⟨a,hx⟩
    have hz : xr=0 := hp.elim _ _
    rw [hz] at hxr
    exact represents_later_zero hrt hxr hx
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

end
end KIP126.Main.Internal.High125
