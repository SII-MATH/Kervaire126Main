module
import all KIP126.Main.SectionSeven.NuTargetFrame
import all KIP126.Main.Internal.Selected.Classical

/-! The later-page frame argument from Selected/ClassicalData:264–311,
sharing the complete E₆ finite calculation with Section Seven. -/
@[expose] section
namespace KIP126.Main.Internal.Selected
open CategoryTheory KIP126.Core.SpectralSequence
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.AdamsSynthetic.Standard (model)
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem later_page_frame_of_earlier
    {E : KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
    {r t : ℤ} {p : ℤ×ℤ} {x : E.Page 2 p} (hr : 2≤r) (hrt : r≤t)
    (hframe : ∃ a : E.Page r p, RepresentsOnPage E r p x a ∧ ∀ y:E.Page r p,y=0∨y=a)
    (ht : ReachesPage E t p x) :
    ∃ a : E.Page t p, RepresentsOnPage E t p x a ∧ ∀ y:E.Page t p,y=0∨y=a := by
  obtain ⟨a,ha,hall⟩ := hframe
  obtain ⟨b,hb⟩ := ht
  refine ⟨b,hb,?_⟩
  intro y
  obtain ⟨x',hy⟩ := page_has_initial_representative (by omega : 2≤t) y
  obtain ⟨a',ha'⟩ := reaches_before hr hrt ⟨y,hy⟩
  rcases hall a' with h0|h1
  · left
    rw [h0] at ha'
    exact represents_later_zero hrt ha' hy
  · right
    have hs := represents_sub ha' ha
    rw [h1,sub_self] at hs
    exact sub_eq_zero.mp (represents_later_zero hrt hs (represents_sub hy hb))

private theorem target_page_twelve_frame :
    ∃ a : model.classical.sphere.Page 12 (14,139),
      RepresentsOnPage model.classical.sphere 12 (14,139) KIP126.Computation.Standard.T a ∧
      ∀ y : model.classical.sphere.Page 12 (14,139), y=0 ∨ y=a := by
  apply later_page_frame_of_earlier (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤12)
    KIP126.Main.SectionSeven.Internal.target_page_six_frame
  exact permanent_reaches .sphere 12 (by decide) (14,139) _
    ((permanent_cycle_iff_mem .sphere (14,139) _).mp KIP126.Computation.Standard.t_permanent_cycle)

end
end KIP126.Main.Internal.Selected
