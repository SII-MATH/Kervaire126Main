module

public import KIP126.Main.Computation.LinCoordinates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Main.Computation.SphereAndCofiber.Bounds
public import KIP126.Def.SpectralSequence.Computation.PageThree.Proofs
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

/-! The staircase conclusions in the Adams filtration 14 and 15 correction
spaces, interpreted through the same comparison as `c.sphereAndCofiber`. -/

@[expose] public section

namespace KIP126.Computation.SphereAndCofiber
open CategoryTheory
open KIP126.SpectralSequence KIP126.SpectralSequence.FinitePageCalculus
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.ExternalHypotheses
open KIP126.LinE2 KIP126.Computation.LinCalculations
noncomputable section
attribute [local irreducible] KIP126.LinE2.homogeneousPart
set_option maxRecDepth 10000

set_option maxRecDepth 100000 in
private theorem full_basis_three_unique :
    (∀ r ∈ basisRows, r.s=14 → r.t=138 → r.index=2 → r.monomial="23,1,190,1") ∧
    (∀ r ∈ basisRows, r.s=15 → r.t=139 → r.index=1 → r.monomial="3,2,287,1") ∧
    (∀ r ∈ basisRows, r.s=15 → r.t=139 → r.index=3 → r.monomial="0,1,439,1") := by
  classical
  have h := KIP126.LinE2.BasisCertificates.ThreeCoordinates.three_coordinates

  exact h

private theorem full_staircase_high_cycles_full_staircase_af14 {literature : LiteratureHypotheses}
    (c : ComputationHypotheses literature) :
    ∃ x : E2At 14 138, HasCoordinates x [2] ∧
      ReachesPage sphereAdamsData 1000 (14,138)
        (c.interpretation.sphereAndCofiberCoordinates.sphere 14 138 x) := by
  classical
  let row : Raw.StaircaseRow := ⟨3005, some 14, some 138, some "2", none, some 9000⟩
  have hl : StaircaseData.lookup 23 61 = some row := by decide
  have hd : Staircase.decode row = some (.reaches 1000 14 138 [2]) := by
    have hs : "2".splitOn "," = ["2"] := by
      simp +decide [String.splitOn, String.splitOnAux]
    have hp : Staircase.parseCoordinates "2" = some [2] := by
      simp only [Staircase.parseCoordinates, show "2".isEmpty = false from rfl,
        Bool.false_eq_true, ↓reduceIte, hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    change (Staircase.parseCoordinates "2").bind (fun x => some (Staircase.Claim.reaches 1000 14 138 x)) = _
    rw [hp]
    rfl
  obtain ⟨claim,hclaim,h⟩ := c.theorems.sphereStaircase.rows_sound 23 61 row hl
  rw [hd] at hclaim
  cases Option.some.inj hclaim
  obtain ⟨ht,x,hx,h⟩ := h
  refine ⟨x,hx,?_⟩
  rw [c.theorems.sphere_comparison_eq 14 138 ht x]
  exact h


private theorem full_staircase_high_cycles_full_staircase_af15 {literature : LiteratureHypotheses}
    (c : ComputationHypotheses literature) :
    ∃ x : E2At 15 139, HasCoordinates x [1,3] ∧
      ReachesPage sphereAdamsData 1000 (15,139)
        (c.interpretation.sphereAndCofiberCoordinates.sphere 15 139 x) := by
  classical
  let row : Raw.StaircaseRow := ⟨3076, some 15, some 139, some "1,3", none, some 9000⟩
  have hl : StaircaseData.lookup 24 4 = some row := by decide
  have hd : Staircase.decode row = some (.reaches 1000 15 139 [1,3]) := by
    have hs : "1,3".splitOn "," = ["1", "3"] := by
      simp +decide [String.splitOn, String.splitOnAux]
    have hp : Staircase.parseCoordinates "1,3" = some [1,3] := by
      simp only [Staircase.parseCoordinates, show "1,3".isEmpty = false from rfl,
        Bool.false_eq_true, ↓reduceIte, hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]; first | decide | exact (List.mergeSort_of_pairwise (by decide)).symm
    change (Staircase.parseCoordinates "1,3").bind (fun x => some (Staircase.Claim.reaches 1000 15 139 x)) = _
    rw [hp]
    rfl
  obtain ⟨claim,hclaim,h⟩ := c.theorems.sphereStaircase.rows_sound 24 4 row hl
  rw [hd] at hclaim
  cases Option.some.inj hclaim
  obtain ⟨ht,x,hx,h⟩ := h
  refine ⟨x,hx,?_⟩
  rw [c.theorems.sphere_comparison_eq 15 139 ht x]
  exact h



private theorem full_staircase_high_cycles_af14_coordinates_to_basis {literature : LiteratureHypotheses}
    (c : ComputationHypotheses literature)
    (hu : ∀ r ∈ basisRows, r.s = 14 → r.t = 138 → r.index = 2 → r.monomial = "23,1,190,1")
    (x : E2At 14 138) (hx : HasCoordinates x [2]) :
    c.interpretation.sphereAndCofiberCoordinates.sphere 14 138 x = c.sphereAndCofiber.interpretation.basis .sphere 14 138 2 := by
  classical
  obtain ⟨rows,hi,hr,hx⟩ := hx
  have hl : rows.length = 1 := by simpa using congrArg List.length hi
  obtain ⟨r,rfl⟩ := List.length_eq_one_iff.mp hl
  have hi' : r.index = 2 := by simpa using hi
  have hrs := hr r (by simp)
  have hm := hu r hrs.1 hrs.2.1 hrs.2.2 hi'
  have hv : x.val = projection (monomialOfString "23,1,190,1") := by
    simpa [basisValue,hm] using hx
  have hc := c.sphereAndCofiber.monomials ⟨.sphere,14,138,["440,1", "439,1", "23,1,190,1", "1,1,418,1", "1,1,417,1"]⟩ (by
    exact List.mem_of_getElem? (i := 216) (by rfl)) rfl
  obtain ⟨y,hy,he⟩ := hc (2 : Fin 5)
  change y.val = projection (monomialOfString "23,1,190,1") at hy
  have hxy : x = y := Subtype.ext (hv.trans hy.symm)
  rw [hxy]
  exact he


private theorem full_staircase_high_cycles_af15_coordinates_to_basis {literature : LiteratureHypotheses}
    (c : ComputationHypotheses literature)
    (hu1 : ∀ r ∈ basisRows, r.s = 15 → r.t = 139 → r.index = 1 → r.monomial = "3,2,287,1")
    (hu3 : ∀ r ∈ basisRows, r.s = 15 → r.t = 139 → r.index = 3 → r.monomial = "0,1,439,1")
    (x : E2At 15 139) (hx : HasCoordinates x [1,3]) :
    c.interpretation.sphereAndCofiberCoordinates.sphere 15 139 x = c.sphereAndCofiber.interpretation.basis .sphere 15 139 1 +
      c.sphereAndCofiber.interpretation.basis .sphere 15 139 3 := by
  classical
  obtain ⟨rows,hi,hr,hx⟩ := hx
  have hl : rows.length = 2 := by simpa using congrArg List.length hi
  obtain ⟨r1,r3,rfl⟩ := List.length_eq_two.mp hl
  have hi' : r1.index = 1 ∧ r3.index = 3 := by simpa using hi
  have hr1 := hr r1 (by simp)
  have hr3 := hr r3 (by simp)
  have hm1 := hu1 r1 hr1.1 hr1.2.1 hr1.2.2 hi'.1
  have hm3 := hu3 r3 hr3.1 hr3.2.1 hr3.2.2 hi'.2
  have hv : x.val = projection (monomialOfString "3,2,287,1") + projection (monomialOfString "0,1,439,1") := by
    simpa [basisValue,hm1,hm3] using hx
  have hc := c.sphereAndCofiber.monomials ⟨.sphere,15,139,["448,1", "3,2,287,1", "0,1,440,1", "0,1,439,1"]⟩ (by
    exact List.mem_of_getElem? (i := 223) (by rfl)) rfl
  obtain ⟨y1,hy1,he1⟩ := hc (1 : Fin 4)
  obtain ⟨y3,hy3,he3⟩ := hc (3 : Fin 4)
  change y1.val = projection (monomialOfString "3,2,287,1") at hy1
  change y3.val = projection (monomialOfString "0,1,439,1") at hy3
  have hxy : x = y1+y3 := by
    apply Subtype.ext
    exact hv.trans (congrArg₂ (· + ·) hy1.symm hy3.symm)
  rw [hxy,map_add]
  exact congrArg₂ (· + ·) he1 he3


/-- Staircase row 3005 in the specified sphere basis. -/
theorem staircase_af14_reaches1000 {literature : LiteratureHypotheses}
    (c : ComputationHypotheses literature) :
    ReachesPage (sequence standardAdamsComparison .sphere) 1000 (14,138)
      (c.sphereAndCofiber.interpretation.basis .sphere 14 138 2) := by
  obtain ⟨hu14,_,_⟩ := full_basis_three_unique
  obtain ⟨x,hx,hp⟩ := full_staircase_high_cycles_full_staircase_af14 c
  rw [full_staircase_high_cycles_af14_coordinates_to_basis c hu14 x hx] at hp
  exact hp

/-- Staircase row 3076 in the specified sphere basis. -/
theorem staircase_af15_reaches1000 {literature : LiteratureHypotheses}
    (c : ComputationHypotheses literature) :
    ReachesPage (sequence standardAdamsComparison .sphere) 1000 (15,139)
      (c.sphereAndCofiber.interpretation.basis .sphere 15 139 1 +
        c.sphereAndCofiber.interpretation.basis .sphere 15 139 3) := by
  obtain ⟨_,hu15a,hu15b⟩ := full_basis_three_unique
  obtain ⟨x,hx,hp⟩ := full_staircase_high_cycles_full_staircase_af15 c
  rw [full_staircase_high_cycles_af15_coordinates_to_basis c hu15a hu15b x hx] at hp
  exact hp

/-- Reaching E3 forces the remaining AF14 d2 column to vanish. -/
theorem staircase_af14_d2_eq_zero {literature : LiteratureHypotheses}
    (c : ComputationHypotheses literature) :
    (sequence standardAdamsComparison .sphere).d 2 (14,138)
      (c.sphereAndCofiber.interpretation.basis .sphere 14 138 2) = 0 := by
  have hp3 : ReachesPage (sequence standardAdamsComparison .sphere) 3 (14,138)
      (c.sphereAndCofiber.interpretation.basis .sphere 14 138 2) :=
    reaches_before (by decide) (by decide : (3 : ℤ) ≤ 1000)
      (staircase_af14_reaches1000 c)
  exact (PageThree.reachesPage_iff_d2_eq_zero
    (by change (2 : ℤ) ≤ 2; omega) (14,138) _).mp hp3

end
end KIP126.Computation.SphereAndCofiber
