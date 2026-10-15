module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates
public import KIP126.Computation.LinCoordinates.Certificates.SphereAndCofiber
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Legacy

@[expose] public section

/-! Filtration and representative calculations for Proposition 7.8 and
Lemma 7.14 (`lem:x_123_9`). The complete bases, products and differential
calculations refer to the same standard sphere as the literature hypotheses.
These lemmas derive the required homotopy relations from those inputs. -/
namespace KIP126.Main.SectionSeven
open KIP126.SpectralSequence.FinitePageCalculus
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic
noncomputable section

section
open CategoryTheory.Limits KIP126.Algebra KIP126.Computation.SphereAndCofiber
open KIP126.LinE2 KIP126.Computation.Near126
universe u v w
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD

/-- Exhaustion of the four AF13 basis directions by actual page representatives.
The nonzero outgoing d3 and correction's nonzero infinite representative use
`sphere_facts` on this same input. The two incoming equations then remove
all other kernel directions, including every linear combination. -/
private theorem stem124_af13_exhaustion_af13_labels
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G) :
    I.interpretation.sphere 13 137 correction = I.interpretation.basis .sphere 13 137 1 ∧
    I.interpretation.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12)) = I.interpretation.basis .sphere 13 137 2 := by
  classical
  have hmem : (⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ : Raw.Degree) ∈ Raw.degrees := by
    exact List.mem_of_getElem? (i := 208) (by rfl)
  have hc := I.monomials _ hmem rfl
  constructor
  · obtain ⟨z,hz,he⟩ := hc (1 : Fin 4)
    have heq : correction = z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨9, by decide⟩ * generator ⟨251, by decide⟩ = projection (monomialOfString "9,1,251,1")
      have hs : "9,1,251,1" ≠ "" := by decide
      have hp : (("9,1,251,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [9,1,251,1] := by
        have split : "9,1,251,1".splitOn "," = ["9", "1", "251", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString, if_neg hs, hp]
      norm_num [polynomialOfPowers, RawData.generatorCount, generator, map_mul]
    rw [heq]
    exact he
  · obtain ⟨z,hz,he⟩ := hc (2 : Fin 4)
    have heq : mulAt (atom .h4) (atom .x_109_12) = z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨7, by decide⟩ * generator ⟨275, by decide⟩ = projection (monomialOfString "7,1,275,1")
      have hs : "7,1,275,1" ≠ "" := by decide
      have hp : (("7,1,275,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [7,1,275,1] := by
        have split : "7,1,275,1".splitOn "," = ["7", "1", "275", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?, String.Slice.toNat?, String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList, String.Slice.foldl_eq_foldl_toList]
      simp only [monomialOfString, if_neg hs, hp]
      norm_num [polynomialOfPowers, RawData.generatorCount, generator, map_mul]
    rw [heq]
    exact he

private theorem stem124_af13_exhaustion
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M : MilnorCooperations H} {D : AdamsComparison H M Syn}
    {L : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D L G)
    (facts : Derived.SphereFacts I.interpretation) :
    KIP126.AdamsSynthetic.SectionSeven.ClassicalInfinityGenerated 13 137
      (I.interpretation.sphere 13 137 correction) := by
  classical
  let E := sequence D .sphere
  let A := E.ssData (13,137)
  obtain ⟨hl1,hl2⟩ := stem124_af13_exhaustion_af13_labels I
  obtain ⟨z,hz,hzn⟩ := facts.correction_permanent
  change (Subobject.ofLE (A.Z ⊤) (A.Z 0) (A.Z_anti le_top) ≫ A.pageπ 0) z = _ at hz
  change A.pageπ ⊤ z ≠ 0 at hzn
  have h321 : HasDifferential E 2 (11,136) (13,137)
      (I.interpretation.basis .sphere 11 136 4) (I.interpretation.basis .sphere 13 137 3) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,136,[4],13,137,[3],"S0_AdamsE2_ss",2914⟩ (by
      exact List.mem_of_getElem? (i := 321) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 2 (11,136) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 11 136 [4] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [3] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  have h322 : HasDifferential E 3 (10,135) (13,137)
      (I.interpretation.basis .sphere 10 135 0) (I.interpretation.basis .sphere 13 137 0) := by
    have hrow := I.adamsStatements ⟨.sphere,.equation,3,10,135,[0],13,137,[0],"S0_AdamsE2_ss",2915⟩ (by
      exact List.mem_of_getElem? (i := 322) (by rfl))
    dsimp only [AdamsStatement] at hrow
    obtain ⟨a,ha,b,hb,h⟩ := hrow
    change HasDifferential E 3 (10,135) (13,137) a b at h
    have vx : Raw.coordinatesValid Raw.degrees .sphere 10 135 [0] = true := rfl
    have vy : Raw.coordinatesValid Raw.degrees .sphere 13 137 [0] = true := rfl
    simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
    rw [←ha,←hb] at h
    exact h
  obtain ⟨_,incoming,a,hincoming,ha,hda⟩ := h322
  have hd2 := facts.d3_h4_x_109_12
  change HasNonzeroDifferential E 3 (13,137) (16,139)
    (I.interpretation.sphere 13 137 (mulAt (atom .h4) (atom .x_109_12))) _ at hd2
  rw [hl2] at hd2
  obtain ⟨_,c,t,hc,ht,hdc,htn⟩ := hd2
  have hdc' : E.d 3 (13,137) c = t := hdc
  have hda' : E.d 3 (10,135) incoming = a := hda
  let down (r : ℤ) := Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-2).toNat) (A.Z_anti le_top)
  let val (r : ℤ) := down r ≫ A.pageπ ↑(r-2).toNat
  have rep (r : ℤ) (hr : 2 ≤ r) (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat.{v} ℤ)) :
      RepresentsOnPage E r (13,137) (val 2 q) (val r q) := by
    refine ⟨hr, down r q, ?_, rfl⟩
    change (Subobject.ofLE _ _ _ ≫ A.pageπ 0) ((down r) q) = val 2 q
    dsimp only [val, down]
    rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
    rfl
  let b : E.Page 3 (13,137) := val 3 z
  have hb : RepresentsOnPage E 3 (13,137) (I.interpretation.basis .sphere 13 137 1) b := by
    have h := rep 3 (by decide) z
    change val 2 z = _ at hz
    rw [hz,hl1] at h
    exact h
  have hthree : RepresentsOnPage E 3 (13,137) (I.interpretation.basis .sphere 13 137 3) 0 :=
    differential_target_later_zero (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3) h321
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,13,137,["76,1,82,1", "9,1,251,1", "7,1,275,1", "0,5,367,1"]⟩ (by
    exact List.mem_of_getElem? (i := 208) (by rfl))
  change E.Page 2 (13,137) ≃ₗ[ℤ] (Fin 4 →₀ F2) at e
  change ∀i : Fin 4, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 137 i.val at he
  have hbzero : E.d 3 (13,137) b = 0 := by
    apply represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4) (rep 3 (by decide) z)
    exact ⟨val 4 z,rep 4 (by decide) z⟩
  have hazero : E.d 3 (13,137) a = 0 := by
    exact IsPageBoundary.d_eq_zero (E:=E) (r:=3) (p:=(10,135)) ⟨incoming,hda'⟩
  have hkernel (q : E.Page 3 (13,137)) (hq : E.d 3 (13,137) q=0) :
      q=0 ∨ q=a ∨ q=b ∨ q=a+b := by
    let vv : Fin 4 → E.Page 3 (13,137) := ![a,b,c,0]
    have hv (i : Fin 4) : RepresentsOnPage E 3 (13,137) (e.symm (Finsupp.single i 1)) (vv i) := by
      rw [he i]
      fin_cases i
      · exact ha
      · exact hb
      · exact hc
      · exact hthree
    obtain ⟨coef,hcoef⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e vv hv q
    simp only [Fin.sum_univ_succ] at hcoef
    change q = (if coef 0=0 then 0 else a) + ((if coef 1=0 then 0 else b) + ((if coef 2=0 then 0 else c) + ((if coef 3=0 then 0 else 0) + 0))) at hcoef
    have hczero : coef 2 = 0 := by
      by_contra hh
      have hd := congrArg (E.d 3 (13,137)) hcoef
      simp only [hq,map_add,apply_ite,map_zero,hazero,hbzero,hdc',hh,ite_false,ite_self,zero_add,add_zero] at hd
      exact htn hd.symm
    by_cases h0 : coef 0=0 <;> by_cases h1 : coef 1=0
    all_goals simp only [h0,h1,hczero,ite_true,ite_false,ite_self,add_zero,zero_add] at hcoef
    · exact Or.inl hcoef
    · exact Or.inr (Or.inr (Or.inl hcoef))
    · exact Or.inr (Or.inl hcoef)
    · exact Or.inr (Or.inr (Or.inr hcoef))
  have kill (q : (Subobject.underlying.obj (A.Z ⊤) : ModuleCat.{v} ℤ)) (hq : val 3 q=0 ∨ val 3 q=a) : A.pageπ ⊤ q=0 := by
    have hfour : A.pageπ 2 (down 4 q)=0 := by
      apply (next_projection_zero_iff_incoming E 3 (by change (2:ℤ)≤3; omega) (10,135) (down 4 q)).mpr
      have hdown : (Subobject.ofLE (A.Z 2) (A.Z 1) (A.Z_anti (by decide : (1:WithTop ℕ)≤2)) ≫ A.pageπ 1) (down 4 q) = val 3 q := by
        change (Subobject.ofLE (A.Z 2) (A.Z 1) _ ≫ A.pageπ 1)
          ((Subobject.ofLE (A.Z ⊤) (A.Z 2) _) q) =
          (Subobject.ofLE (A.Z ⊤) (A.Z 1) _ ≫ A.pageπ 1) q
        rw [← CategoryTheory.comp_apply, ← Category.assoc, Subobject.ofLE_comp_ofLE]
      change ∃ x, E.d 3 (10,135) x = (Subobject.ofLE (A.Z 2) (A.Z 1) _ ≫ A.pageπ 1) (down 4 q)
      rw [hdown]
      rcases hq with hq|hq
      · exact ⟨0, by rw [hq,map_zero]⟩
      · exact ⟨incoming, hda'.trans hq.symm⟩
    change (A.pageπ 2) ((Subobject.ofLE (A.Z ⊤) (A.Z 2) _) q)=0 at hfour
    have heq := A.infinity_projection_eq_of_page_projection_eq 2 q 0 (by simpa only [CategoryTheory.comp_apply,map_zero] using hfour)
    simpa only [map_zero] using heq
  refine ⟨z,hz,hzn,?_⟩
  intro y
  haveI : Epi (A.pageπ ⊤) := inferInstanceAs (Epi (cokernel.π _))
  obtain ⟨q,rfl⟩ := (ModuleCat.epi_iff_surjective (A.pageπ ⊤)).mp inferInstance y
  have hqzero : E.d 3 (13,137) (val 3 q)=0 := by
    exact represents_d_zero_of_later (by change (2:ℤ)≤3; omega) (by decide : (3:ℤ)<4)
      (rep 3 (by decide) q) ⟨val 4 q,rep 4 (by decide) q⟩
  rcases hkernel (val 3 q) hqzero with hq|hq|hq|hq
  · exact Or.inl (kill q (Or.inl hq))
  · exact Or.inl (kill q (Or.inr hq))
  · apply Or.inr
    change A.pageπ ⊤ q = A.pageπ ⊤ z
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill (q-z)
    left
    simp only [map_sub,hq,b,sub_self]
  · apply Or.inr
    change A.pageπ ⊤ q = A.pageπ ⊤ z
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill (q-z)
    right
    simp only [map_sub,hq,b,add_sub_cancel_right]

end

end
end KIP126.Main.SectionSeven
