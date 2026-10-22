module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.Pushout.RealFunctions.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.SequentialColimit.RealFunctions.Proofs

@[expose] section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology HomotopicalAlgebra

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every stage of an actual relative CW complex has real functions that
separate points, provided they separate points in the original base. -/
theorem relativeCWComplex_stage_real_functions_separate_points
    {X Y : TopCat.{u}} {i : X ⟶ Y} (c : TopCat.RelativeCWComplex i)
    (hX : ∀ x y : X, x ≠ y → ∃ f : C(X, ℝ), f x ≠ f y) :
    ∀ n, ∀ x y : c.F.obj n, x ≠ y → ∃ f : C(c.F.obj n, ℝ), f x ≠ f y := by
  intro n
  induction n with
  | zero =>
    intro x y hxy
    obtain ⟨f,hf⟩ := hX (c.isoBot.hom x) (c.isoBot.hom y)
      ((TopCat.homeoOfIso c.isoBot).injective.ne hxy)
    exact ⟨f.comp c.isoBot.hom.hom,hf⟩
  | succ n ih =>
    let a := c.attachCells n (by simp)
    letI : NormalSpace (TopCat.disk.{u} n) :=
      inferInstanceAs (NormalSpace (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))
    letI : T2Space (TopCat.disk.{u} n) :=
      inferInstanceAs (T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)))
    letI : NormalSpace (Σ _ : a.ι, TopCat.disk.{u} n) := normalSpace_sigma _
    letI : NormalSpace (TopCat.sigmaCofan (fun _ : a.ι => TopCat.disk.{u} n)).pt :=
      inferInstanceAs (NormalSpace (Σ _ : a.ι, TopCat.disk.{u} n))
    letI : T2Space (TopCat.sigmaCofan (fun _ : a.ι => TopCat.disk.{u} n)).pt :=
      inferInstanceAs (T2Space (Σ _ : a.ι, TopCat.disk.{u} n))
    let e := a.isColimit₂.coconePointUniqueUpToIso
      (TopCat.sigmaCofanIsColimit (fun _ : a.ι => TopCat.disk.{u} n))
    letI : NormalSpace a.cofan₂.pt := (TopCat.homeoOfIso e).isClosedEmbedding.normalSpace
    letI : T2Space a.cofan₂.pt := (TopCat.homeoOfIso e).isEmbedding.t2Space
    apply pushout_real_functions_separate_points a.isPushout.flip
      (isClosedEmbedding_of_coproduct _ (fun _ => diskBoundaryInclusion_isClosedEmbedding n)
        _ _ a.isColimit₁ a.isColimit₂ a.m a.hm)
      (HomotopyExtension.hasHomotopyExtension_of_coproduct _
        (fun _ => HomotopyExtension.diskBoundaryInclusion_hasHomotopyExtension n)
        _ _ a.isColimit₁ a.isColimit₂ a.m a.hm)
    exact ih

/-- Every real-valued function on a stage extends to its successor by the
actual disk-boundary HEP and pushout universal property. -/
theorem relativeCWComplex_stage_exists_real_extension
    {X Y : TopCat.{u}} {i : X ⟶ Y} (c : TopCat.RelativeCWComplex i)
    (n : ℕ) (f : C(c.F.obj n, ℝ)) :
    ∃ g : C(c.F.obj (n+1), ℝ),
      ∀ x, g (c.F.map (homOfLE (Nat.le_succ n)) x) = f x := by
  let a := c.attachCells n (by simp)
  have ha := HomotopyExtension.hasHomotopyExtension_of_coproduct _
    (fun _ => HomotopyExtension.diskBoundaryInclusion_hasHomotopyExtension n)
    _ _ a.isColimit₁ a.isColimit₂ a.m a.hm
  obtain ⟨fa,hfa⟩ := exists_real_extension_of_homotopyExtension ha (f.comp a.g₁.hom)
  obtain ⟨g,hga,hgb⟩ := exists_real_map_of_pushout a.isPushout.flip fa f hfa
  exact ⟨g,hgb⟩

/-- Real-valued continuous functions separate points throughout an actual
relative CW complex, including its genuine sequential colimit. -/
theorem relativeCWComplex_real_functions_separate_points
    {X Y : TopCat.{u}} {i : X ⟶ Y} (c : TopCat.RelativeCWComplex i)
    (hX : ∀ x y : X, x ≠ y → ∃ f : C(X, ℝ), f x ≠ f y) :
    ∀ x y : Y, x ≠ y → ∃ f : C(Y, ℝ), f x ≠ f y :=
  real_functions_separate_points_nat_colimit c.F (Cocone.mk Y c.incl) c.isColimit
    (relativeCWComplex_stage_exists_real_extension c)
    (relativeCWComplex_stage_real_functions_separate_points c hX)

/-- An actual CW complex is Hausdorff; this follows from real separating
functions constructed across its cells, rather than an additional axiom. -/
theorem cwComplex_t2Space {X : TopCat.{u}} (c : TopCat.CWComplex X) : T2Space X :=
  t2Space_of_real_functions_separate_points
    (relativeCWComplex_real_functions_separate_points c
      (fun x => PEmpty.elim (TopCat.initialIsoPEmpty.hom x)))

end KIP126.Topology
