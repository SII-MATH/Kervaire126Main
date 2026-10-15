module

public import KIP126.Main.Computation.LinCoordinates.Model.E2.Proofs

public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Main.Computation.LinCoordinates.Certificates.Relations.ThetaMassey
public import KIP126.Main.SectionSeven.SphereClasses

-- The CSV coordinate calculations use the defining string and list equations.
import all Init.Data.List.SplitOn.Basic
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

@[expose] public section

namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Main.AdamsSynthetic
noncomputable section

local notation "D" => adamsComparison
local notation "M" => standardMilnorCooperations
local notation "L" => sphereClasses
local notation "I" => computationTheorems
local notation "η" => etaClass
local notation "h₀" => literatureTheorems.toda.h0

abbrev ThetaBMasseyCycles : Prop :=
    IsPageCycle
        (adamsTowerInternalSpectralSequence
          standardFoundation.hf2.unit SphereSpectrum)
        2 (2, 64) (Sphere.Internal.hiSquare standardFoundation.hf2 M 5) ∧
    IsPageCycle
        (adamsTowerInternalSpectralSequence
          standardFoundation.hf2.unit SphereSpectrum)
        2 (1, 1) (Sphere.Internal.hi standardFoundation.hf2 M 0) ∧
    IsPageCycle
        (adamsTowerInternalSpectralSequence
          standardFoundation.hf2.unit SphereSpectrum)
        2 (8, 70) eB

abbrev ThetaBMasseyD2H6 : Prop :=
    (adamsTowerInternalSpectralSequence
        standardFoundation.hf2.unit SphereSpectrum).d 2 (1, 64)
        (Sphere.Internal.hi standardFoundation.hf2 M 6) =
      Sphere.Internal.product standardFoundation.hf2 M
        (s := 2) (t := 64) (s' := 1) (t' := 1)
        (Sphere.Internal.hiSquare standardFoundation.hf2 M 5)
        (Sphere.Internal.hi standardFoundation.hf2 M 0)

abbrev ThetaBMasseyD2Second : Prop :=
    ∃ b : (adamsTowerInternalSpectralSequence
      standardFoundation.hf2.unit SphereSpectrum).Page 2 (7, 70),
      (adamsTowerInternalSpectralSequence
        standardFoundation.hf2.unit SphereSpectrum).d 2 (7, 70) b =
        Sphere.Internal.product standardFoundation.hf2 M
          (s := 1) (t := 1) (s' := 8) (t' := 70)
          (Sphere.Internal.hi standardFoundation.hf2 M 0) eB


section ThetaBMasseyProof
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Synthetic.Context KIP126.AdamsSynthetic
open KIP126.SpectralSequence KIP126.Algebra KIP126.Computation.SphereAndCofiber
open KIP126.LinE2 KIP126.Computation.Near126
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem h5_square_times_entire_770_zero
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
    {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H} (I' : AdamsComputationTheorems D' L' G) :
    ∀ b : E2 H SphereSpectrum 7 70,
      Sphere.Internal.product H M' (s := 2) (t := 64) (s' := 7) (t' := 70)
        (Sphere.Internal.hiSquare H M' 5) b = 0 := by
  classical
  have expand {A : Type v} [AddCommGroup A] [Module ℤ A] {N : ℕ}
      (e : A ≃ₗ[ℤ] (Fin N →₀ F2)) (a : A) :
      a=∑ i : Fin N, if (e a) i=0 then 0 else e.symm (Finsupp.single i 1) := by
    apply e.injective
    rw [map_sum]
    ext i
    simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · generalize (e a) i=b
      fin_cases b <;> simp
    · intro j hj hji
      by_cases hc : (e a) j=0
      · simp [hc]
      · simp [hc,hji]
    · simp
  obtain ⟨e,he⟩ := I'.basis ⟨.sphere,7,70,["85,1","84,1","0,6,69,1"]⟩ (by
    unfold Raw.degrees
    iterate 143 apply List.mem_cons_of_mem
    exact List.mem_cons_self)
  change E2 H SphereSpectrum 7 70 ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 7 70 i.val at he
  have hcsv := I'.monomials ⟨.sphere,7,70,["85,1","84,1","0,6,69,1"]⟩ (by
    unfold Raw.degrees
    iterate 143 apply List.mem_cons_of_mem
    exact List.mem_cons_self) rfl
  let z : Fin 3 → E2At 7 70 := fun i => (hcsv i).choose
  have hz (i : Fin 3) : (z i).val =
      projection (monomialOfString (["85,1", "84,1", "0,6,69,1"] : List String)[i]) :=
    (hcsv i).choose_spec.1
  have hez (i : Fin 3) :
      I'.interpretation.sphere 7 70 (z i) = I'.interpretation.basis .sphere 7 70 i.val :=
    (hcsv i).choose_spec.2
  have zv0 : (z (0:Fin 3)).val = generator ⟨85,by decide⟩ := by
    rw [hz]
    change projection (monomialOfString "85,1") = generator ⟨85,by decide⟩
    have hp0 : "85,1" ≠ "" := by decide
    have hp : (("85,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [85,1] := by
      have hs : "85,1".splitOn "," = ["85","1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [monomialOfString,hp,hp0,polynomialOfPowers,
      RawData.generatorCount,generator,map_mul,map_pow,mul_assoc]
  have zv1 : (z (1:Fin 3)).val = generator ⟨84,by decide⟩ := by
    rw [hz]
    change projection (monomialOfString "84,1") = generator ⟨84,by decide⟩
    have hp0 : "84,1" ≠ "" := by decide
    have hp : (("84,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [84,1] := by
      have hs : "84,1".splitOn "," = ["84","1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [monomialOfString,hp,hp0,polynomialOfPowers,
      RawData.generatorCount,generator,map_mul,map_pow,mul_assoc]
  have zv2 : (z (2:Fin 3)).val = generator ⟨0,by decide⟩^6*generator ⟨69,by decide⟩ := by
    rw [hz]
    change projection (monomialOfString "0,6,69,1") = generator ⟨0,by decide⟩^6*generator ⟨69,by decide⟩
    have hp0 : "0,6,69,1" ≠ "" := by decide
    have hp : (("0,6,69,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0,6,69,1] := by
      have hs : "0,6,69,1".splitOn "," = ["0","6","69","1"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      rw [hs]
      simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
        String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
    norm_num [monomialOfString,hp,hp0,polynomialOfPowers,
      RawData.generatorCount,generator,map_mul,map_pow,mul_assoc]
  let f : E2 H SphereSpectrum 7 70 →ₗ[ℤ] E2 H SphereSpectrum 9 134 :=
    (MilnorCohomology.comparison H M' 9 134).toLinearMap.comp
      (((MilnorCohomology.cup H M' ((MilnorCohomology.comparison H M' 2 64).symm
        (Sphere.Internal.hiSquare H M' 5))).restrictScalars ℤ).comp
          (MilnorCohomology.comparison H M' 7 70).symm.toLinearMap)
  have hf (a : E2 H SphereSpectrum 7 70) : f a = Sphere.Internal.product H M'
      (s := 2) (t := 64) (s' := 7) (t' := 70) (Sphere.Internal.hiSquare H M' 5) a := rfl
  have hprod (i : Fin 3) : f (I'.interpretation.basis .sphere 7 70 i.val) =
      I'.interpretation.sphere 9 134 (mulAt h5Sq (z i)) := by
    rw [←hez i,hf,←I'.distinguishedClasses.h5_square]
    exact (I'.products ⟨2,64,7,70⟩ (by simp [Raw.products]) h5Sq (z i)).symm
  have hzero0 : mulAt h5Sq (z (0:Fin 3))=0 := by
    apply Subtype.ext
    change (generator ⟨18,by decide⟩*generator ⟨18,by decide⟩)*(z (0:Fin 3)).val=0
    rw [zv0,mul_assoc,RelationCertificates.theta_massey_h5_mul_85_zero,mul_zero]
  have hzero1 : mulAt h5Sq (z (1:Fin 3))=0 := by
    apply Subtype.ext
    change (generator ⟨18,by decide⟩*generator ⟨18,by decide⟩)*(z (1:Fin 3)).val=0
    rw [zv1,mul_assoc,RelationCertificates.theta_massey_h5_mul_84_zero,mul_zero]
  have hzero2 : mulAt h5Sq (z (2:Fin 3))=0 := by
    apply Subtype.ext
    change (generator ⟨18,by decide⟩*generator ⟨18,by decide⟩)*(z (2:Fin 3)).val=0
    rw [zv2]
    calc
      _ = generator ⟨0,by decide⟩^6*generator ⟨18,by decide⟩*
        (generator ⟨18,by decide⟩*generator ⟨69,by decide⟩) := by ring
      _ = 0 := by rw [RelationCertificates.theta_massey_h5_mul_69_zero,mul_zero]
  have hzero (i : Fin 3) : mulAt h5Sq (z i)=0 := by
    fin_cases i
    · exact hzero0
    · exact hzero1
    · exact hzero2
  have hb (i : Fin 3) : f (e.symm (Finsupp.single i 1))=0 := by
    rw [he,hprod,hzero,map_zero]
  intro a
  rw [←hf,expand e a,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with hc
  · exact map_zero _
  · exact hb i

private theorem theta_b_massey_from_inputs
    {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
    {L' : SphereAdamsClasses H} {G : KIP126.Literature.AdamsSynthetic.TmfDetectionClasses H}
    {η' : BiHom 1 2 (S_0_0 : Syn)} (I' : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G)
    (A : KIP126.Literature.AdamsSynthetic.ClassicalTheorems D' η') :
    let eB := I'.interpretation.sphere 8 70 B
    let eHB := Sphere.Internal.product H M' (s := 1) (t := 64) (s' := 8) (t' := 70)
      (Sphere.Internal.hi H M' 6) eB
    ((∃ z, RepresentsOnPage (sequence D' .sphere) 3 (9,134) eHB z ∧
      z ∈ ThetaBMassey M' eB) ∧ ThetaBMasseyZeroIndeterminacy M' eB) ∧
    IsPageCycle (sequence D' .sphere) 2 (2,64) (Sphere.Internal.hiSquare H M' 5) ∧
    IsPageCycle (sequence D' .sphere) 2 (1,1) (Sphere.Internal.hi H M' 0) ∧
    IsPageCycle (sequence D' .sphere) 2 (8,70) eB ∧
    (sequence D' .sphere).d 2 (1,64) (Sphere.Internal.hi H M' 6) =
      Sphere.Internal.product H M' (s := 2) (t := 64) (s' := 1) (t' := 1)
        (Sphere.Internal.hiSquare H M' 5) (Sphere.Internal.hi H M' 0) ∧
    ∃ b : E2 H SphereSpectrum 7 70,
      (sequence D' .sphere).d 2 (7,70) b =
        Sphere.Internal.product H M' (s := 1) (t := 1) (s' := 8) (t' := 70)
          (Sphere.Internal.hi H M' 0) eB := by
  classical
  let E := sequence D' .sphere
  let eB := I'.interpretation.sphere 8 70 B
  let eHB := Sphere.Internal.product H M' (s := 1) (t := 64) (s' := 8) (t' := 70)
    (Sphere.Internal.hi H M' 6) eB
  have permanent_reaches {E : KIP126.SpectralSequence (ModuleCat.{v} ℤ) (ℤ×ℤ)}
      {p : ℤ×ℤ} {x : E.Page 2 p} (hx : IsPermanentCycle E p x)
      (r : ℤ) (hr : 2≤r) : ReachesPage E r p x := by
    obtain ⟨z,hz⟩ := hx
    let A := E.ssData p
    let zr := (Subobject.ofLE (A.Z ⊤) (A.Z ↑(r-E.r₀).toNat) (A.Z_anti le_top)) z
    refine ⟨A.pageπ _ zr,hr,zr,?_,rfl⟩
    dsimp only [zr]
    rw [← CategoryTheory.comp_apply,← Category.assoc,Subobject.ofLE_comp_ofLE]
    exact hz
  have hd2h6 : Derived.Differential I'.interpretation 2 dataH6 (mulAt dataH0 h5Sq) := by
    let E := sequence D' .sphere
    have hs : I'.interpretation.sphere 1 64 (dataH6) = I'.interpretation.basis .sphere 1 64 0 := by
      have hc := I'.monomials (⟨.sphere,1,64,["69,1"]⟩ : Raw.Degree) (by
        unfold Raw.degrees
        iterate 85 apply List.mem_cons_of_mem
        exact List.mem_cons_self) rfl
      obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
      have heq : (dataH6)=z := by
        apply Subtype.ext
        rw [hz]
        change generator ⟨69,by decide⟩ = projection (monomialOfString "69,1")
        have hp : (("69,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69, 1] := by
          have split : "69,1".splitOn "," = ["69", "1"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [split]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        simp only [monomialOfString,show "69,1"≠"" by decide,if_false,hp]
        norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
      rw [heq]
      exact he
    have ht : I'.interpretation.sphere 3 65 (mulAt dataH0 h5Sq) = I'.interpretation.basis .sphere 3 65 0 := by
      have hc := I'.monomials (⟨.sphere,3,65,["0,1,18,2"]⟩ : Raw.Degree) (by
        unfold Raw.degrees
        iterate 102 apply List.mem_cons_of_mem
        exact List.mem_cons_self) rfl
      obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
      have heq : (mulAt dataH0 h5Sq)=z := by
        apply Subtype.ext
        rw [hz]
        change generator ⟨0,by decide⟩ * (generator ⟨18,by decide⟩*generator ⟨18,by decide⟩) = projection (monomialOfString "0,1,18,2")
        have hp : (("0,1,18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 1, 18, 2] := by
          have split : "0,1,18,2".splitOn "," = ["0", "1", "18", "2"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [split]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        simp only [monomialOfString,show "0,1,18,2"≠"" by decide,if_false,hp]
        norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
      rw [heq]
      exact he
    have h142 : HasDifferential E 2 (1,64) (3,65)
        (I'.interpretation.basis .sphere 1 64 0) (I'.interpretation.basis .sphere 3 65 0) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,1,64,[0],3,65,[0],"S0_AdamsE2_ss",401⟩ (by
        unfold Raw.claims
        iterate 142 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (1,64) (3,65) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 1 64 [0] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 3 65 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,3,65,["0,1,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 102 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (3,65) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 3 65 i.val at he
    have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I'.interpretation.basis .sphere 3 65 0 := he 0
    change HasNonzeroDifferential E 2 (1,64) (3,65) _ _
    rw [hs,ht]
    obtain ⟨hd,x,y,hx,hy,hxy⟩ := h142
    refine ⟨hd,x,y,hx,hy,hxy,?_⟩
    rw [←hy.eq_on_page_two,←he0]
    intro h
    have hh := congrArg (fun x => e x 0) h
    simp at hh
  have hD2H0six : Derived.Differential I'.interpretation 2 (mulAt h0Six dataH6) (mulAt dataH0 B) := by
    have hmem := RelationCertificates.relation_member5
    let E := sequence D' .sphere
    have hs : I'.interpretation.sphere 7 70 (mulAt h0Six dataH6) = I'.interpretation.basis .sphere 7 70 2 := by
      have hc := I'.monomials (⟨.sphere,7,70,["85,1", "84,1", "0,6,69,1"]⟩ : Raw.Degree) (by
        unfold Raw.degrees
        iterate 143 apply List.mem_cons_of_mem
        exact List.mem_cons_self) rfl
      obtain ⟨z,hz,he⟩ := hc (2:Fin 3)
      have heq : (mulAt h0Six dataH6)=z := by
        apply Subtype.ext
        rw [hz]
        change ((generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩))*generator ⟨69,by decide⟩ = projection (monomialOfString "0,6,69,1")
        have hp : (("0,6,69,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 6, 69, 1] := by
          have split : "0,6,69,1".splitOn "," = ["0", "6", "69", "1"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [split]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        simp only [monomialOfString,show "0,6,69,1"≠"" by decide,if_false,hp]
        norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
      rw [heq]
      exact he
    have ht0 : I'.interpretation.sphere 9 71 (mulAt (mulAt h0Six dataH0) h5Sq) = I'.interpretation.basis .sphere 9 71 0 := by
      have hc := I'.monomials (⟨.sphere,9,71,["0,7,18,2"]⟩ : Raw.Degree) (by
        unfold Raw.degrees
        iterate 167 apply List.mem_cons_of_mem
        exact List.mem_cons_self) rfl
      obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
      have heq : (mulAt (mulAt h0Six dataH0) h5Sq)=z := by
        apply Subtype.ext
        rw [hz]
        change (((generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩)*(generator ⟨0,by decide⟩*generator ⟨0,by decide⟩))*generator ⟨0,by decide⟩)*(generator ⟨18,by decide⟩*generator ⟨18,by decide⟩) = projection (monomialOfString "0,7,18,2")
        have hp : (("0,7,18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 7, 18, 2] := by
          have split : "0,7,18,2".splitOn "," = ["0", "7", "18", "2"] := by
            simp +decide [String.splitOn,String.splitOnAux]
          rw [split]
          simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
            String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
        simp only [monomialOfString,show "0,7,18,2"≠"" by decide,if_false,hp]
        norm_num [polynomialOfPowers,RawData.generatorCount,generator,map_mul,pow_succ,mul_assoc]
      rw [heq]
      exact he
    have hrel : mulAt dataH0 B = mulAt (mulAt h0Six dataH0) h5Sq := by
      apply Subtype.ext
      have hz := csv_relation_zero "0,1,82,1;0,7,18,2" hmem
      have hsplit : "0,1,82,1;0,7,18,2".splitOn ";" = ["0,1,82,1","0,7,18,2"] := by
        simp +decide [String.splitOn,String.splitOnAux]
      have hp0 : (("0,1,82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 1, 82, 1] := by
        have split : "0,1,82,1".splitOn "," = ["0", "1", "82", "1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      have hp1 : (("0,7,18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [0, 7, 18, 2] := by
        have split : "0,7,18,2".splitOn "," = ["0", "7", "18", "2"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [split]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      have hneg (x : KIP126.LinE2.E2) : -x = x := by
        obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
        change -(projection p)=projection p
        rw [←map_neg]
        exact congrArg projection (CharTwo.neg_eq p)
      norm_num [relationPolynomial,hsplit,monomialOfString,hp0,hp1,polynomialOfPowers,
        RawData.generatorCount,generator,map_mul,map_add,pow_succ,mul_assoc] at hz
      have heq := (eq_neg_of_add_eq_zero_left hz).trans (hneg _)
      simpa [mulAt,dataH0,B,atom,h0Six,h0Sq,h5Sq,generator,h0,RawData.generatorCount,
        pow_succ,mul_assoc,map_mul] using heq
    have ht : I'.interpretation.sphere 9 71 (mulAt dataH0 B) = I'.interpretation.basis .sphere 9 71 0 := by
      rw [hrel]
      exact ht0
    have h180 : HasDifferential E 2 (7,70) (9,71)
        (I'.interpretation.basis .sphere 7 70 2) (I'.interpretation.basis .sphere 9 71 0) := by
      have hrow := I'.adamsStatements ⟨.sphere,.equation,2,7,70,[2],9,71,[0],"S0_AdamsE2_ss",513⟩ (by
        unfold Raw.claims
        iterate 180 apply List.mem_cons_of_mem
        exact List.mem_cons_self)
      dsimp only [AdamsStatement] at hrow
      obtain ⟨x,hx,y,hy,hd⟩ := hrow
      change HasDifferential E 2 (7,70) (9,71) x y at hd
      have vx : Raw.coordinatesValid Raw.degrees .sphere 7 70 [2] = true := rfl
      have vy : Raw.coordinatesValid Raw.degrees .sphere 9 71 [0] = true := rfl
      simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
      rw [←hx,←hy] at hd
      simpa only [add_assoc] using hd
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,9,71,["0,7,18,2"]⟩ (by
      unfold Raw.degrees
      iterate 167 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E.Page 2 (9,71) ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1) = I'.interpretation.basis .sphere 9 71 i.val at he
    have he0 : e.symm (Finsupp.single (0:Fin 1) 1) = I'.interpretation.basis .sphere 9 71 0 := he 0
    change HasNonzeroDifferential E 2 (7,70) (9,71) _ _
    rw [hs,ht]
    obtain ⟨hd,x,y,hx,hy,hxy⟩ := h180
    refine ⟨hd,x,y,hx,hy,hxy,?_⟩
    rw [←hy.eq_on_page_two,←he0]
    intro h
    have hh := congrArg (fun x => e x 0) h
    simp at hh
  have h5label : I'.interpretation.sphere 2 64 (h5Sq) = I'.interpretation.basis .sphere 2 64 0 := by
    have hc := I'.monomials (⟨.sphere, 2, 64, ["18,2"]⟩ : Raw.Degree) (by
      unfold Raw.degrees
      iterate 94 apply List.mem_cons_of_mem
      exact List.mem_cons_self) rfl
    obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
    have heq : (h5Sq)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨18,by decide⟩*generator ⟨18,by decide⟩ = projection (monomialOfString "18,2")
      have hp : (("18,2".splitOn ",").map (fun n => n.toNat?.getD 0)) = [18,2] := by
        have hs : "18,2".splitOn "," = ["18","2"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [hs]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      norm_num [monomialOfString,show "18,2"≠"" by decide,hp,polynomialOfPowers,
        RawData.generatorCount,generator,map_mul,map_pow,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have bLabel : I'.interpretation.sphere 8 70 (B) = I'.interpretation.basis .sphere 8 70 1 := by
    have hc := I'.monomials (⟨.sphere, 8, 70, ["83,1", "82,1", "0,6,18,2"]⟩ : Raw.Degree) (by
      unfold Raw.degrees
      iterate 155 apply List.mem_cons_of_mem
      exact List.mem_cons_self) rfl
    obtain ⟨z,hz,he⟩ := hc (1:Fin 3)
    have heq : (B)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨82,by decide⟩ = projection (monomialOfString "82,1")
      have hp : (("82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [82,1] := by
        have hs : "82,1".splitOn "," = ["82","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [hs]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      norm_num [monomialOfString,show "82,1"≠"" by decide,hp,polynomialOfPowers,
        RawData.generatorCount,generator,map_mul,map_pow,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have h6Label : I'.interpretation.sphere 1 64 (dataH6) = I'.interpretation.basis .sphere 1 64 0 := by
    have hc := I'.monomials (⟨.sphere, 1, 64, ["69,1"]⟩ : Raw.Degree) (by
      unfold Raw.degrees
      iterate 85 apply List.mem_cons_of_mem
      exact List.mem_cons_self) rfl
    obtain ⟨z,hz,he⟩ := hc (0:Fin 1)
    have heq : (dataH6)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨69,by decide⟩ = projection (monomialOfString "69,1")
      have hp : (("69,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69,1] := by
        have hs : "69,1".splitOn "," = ["69","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [hs]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      norm_num [monomialOfString,show "69,1"≠"" by decide,hp,polynomialOfPowers,
        RawData.generatorCount,generator,map_mul,map_pow,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have hbLabel : I'.interpretation.sphere 9 134 (mulAt dataH6 B) = I'.interpretation.basis .sphere 9 134 2 := by
    have hc := I'.monomials (⟨.sphere, 9, 134, ["391,1", "390,1", "69,1,82,1", "18,1,190,1", "0,1,375,1"]⟩ : Raw.Degree) (by
      unfold Raw.degrees
      iterate 173 apply List.mem_cons_of_mem
      exact List.mem_cons_self) rfl
    obtain ⟨z,hz,he⟩ := hc (2:Fin 5)
    have heq : (mulAt dataH6 B)=z := by
      apply Subtype.ext
      rw [hz]
      change generator ⟨69,by decide⟩*generator ⟨82,by decide⟩ = projection (monomialOfString "69,1,82,1")
      have hp : (("69,1,82,1".splitOn ",").map (fun n => n.toNat?.getD 0)) = [69,1,82,1] := by
        have hs : "69,1,82,1".splitOn "," = ["69","1","82","1"] := by
          simp +decide [String.splitOn,String.splitOnAux]
        rw [hs]
        simp +decide [String.toNat?,String.Slice.toNat?,String.Slice.isNat,
          String.Slice.forIn_eq_forIn_toList,String.Slice.foldl_eq_foldl_toList]
      norm_num [monomialOfString,show "69,1,82,1"≠"" by decide,hp,polynomialOfPowers,
        RawData.generatorCount,generator,map_mul,map_pow,pow_succ,mul_assoc]
    rw [heq]
    exact he
  have rH5 : ReachesPage E 1000 (2,64) (I'.interpretation.basis .sphere 2 64 0) := by
    have hrow := I'.adamsStatements ⟨.sphere, .reaches, 1000, 2, 64, [0], 2, 64, [], "S0_AdamsE2_ss", 400⟩ (by
      unfold Raw.claims
      iterate 144 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 2 64 [0]=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at h
    exact h
  have rB : ReachesPage E 1000 (8,70) (I'.interpretation.basis .sphere 8 70 1) := by
    have hrow := I'.adamsStatements ⟨.sphere, .reaches, 1000, 8, 70, [1], 8, 70, [], "S0_AdamsE2_ss", 509⟩ (by
      unfold Raw.claims
      iterate 193 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 8 70 [1]=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at h
    exact h
  have rHB : ReachesPage E 1000 (9,134) (I'.interpretation.basis .sphere 9 134 2) := by
    have hrow := I'.adamsStatements ⟨.sphere, .reaches, 1000, 9, 134, [2], 9, 134, [], "S0_AdamsE2_ss", 2695⟩ (by
      unfold Raw.claims
      iterate 224 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    dsimp only [AdamsStatement] at hrow
    obtain ⟨x,hx,h⟩ := hrow
    have vx : Raw.coordinatesValid Raw.degrees .sphere 9 134 [2]=true := rfl
    simp only [E2Interpretation.coordinateSum,vx,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx
    rw [←hx] at h
    exact h
  have hcycle5 : IsPageCycle E 2 (2,64) (Sphere.Internal.hiSquare H M' 5) := by
    apply FinitePageCalculus.represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000) (FinitePageCalculus.represents_two_self _)
    rwa [←I'.distinguishedClasses.h5_square,h5label]
  have hcycleB : IsPageCycle E 2 (8,70) eB := by
    apply FinitePageCalculus.represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<1000) (FinitePageCalculus.represents_two_self _)
    change ReachesPage E 1000 (8,70) (I'.interpretation.sphere 8 70 B)
    rwa [bLabel]
  have hcycle0 : IsPageCycle E 2 (1,1) (Sphere.Internal.hi H M' 0) := by
    have hp : IsPermanentCycle E (1,1) (Sphere.Internal.hi H M' 0) := by
      obtain ⟨z,hz,rest⟩ := A.two_detection
      exact ⟨z,hz⟩
    exact FinitePageCalculus.represents_d_zero_of_later (by change (2:ℤ)≤2; omega) (by decide : (2:ℤ)<3)
      (FinitePageCalculus.represents_two_self _) (permanent_reaches hp 3 (by decide))
  have hdA : E.d 2 (1,64) (Sphere.Internal.hi H M' 6) =
      Sphere.Internal.product H M' (s := 2) (t := 64) (s' := 1) (t' := 1)
        (Sphere.Internal.hiSquare H M' 5) (Sphere.Internal.hi H M' 0) := by
    have h := hd2h6.toHasDifferential.eq_on_page_two.choose_spec
    change E.d 2 (1,64) (I'.interpretation.sphere 1 64 dataH6)=I'.interpretation.sphere 3 65 (mulAt dataH0 h5Sq) at h
    rw [←I'.distinguishedClasses.h6,←I'.distinguishedClasses.h5_square,←I'.distinguishedClasses.h0]
    rw [h,←I'.products ⟨2,64,1,1⟩ (by simp [Raw.products]) h5Sq dataH0]
    congr 1
    apply Subtype.ext
    exact mul_comm _ _
  have hdB : E.d 2 (7,70) (I'.interpretation.sphere 7 70 (mulAt h0Six dataH6)) =
      Sphere.Internal.product H M' (s := 1) (t := 1) (s' := 8) (t' := 70)
        (Sphere.Internal.hi H M' 0) eB := by
    have h := hD2H0six.toHasDifferential.eq_on_page_two.choose_spec
    change E.d 2 (7,70) (I'.interpretation.sphere 7 70 (mulAt h0Six dataH6)) =
      I'.interpretation.sphere 9 71 (mulAt dataH0 B) at h
    rw [h]
    exact (I'.products ⟨1,1,8,70⟩ (by simp [Raw.products]) dataH0 B).trans (by rw [I'.distinguishedClasses.h0])
  have allProd := h5_square_times_entire_770_zero I'
  have hdef : ThetaBMasseyDefiningSystem M' eB eHB := by
    refine ⟨hcycle5,hcycle0,hcycleB,Sphere.Internal.hi H M' 6,
      I'.interpretation.sphere 7 70 (mulAt h0Six dataH6),hdA,hdB,?_⟩
    rw [allProd,add_zero]
  have uniqueA (a : E2 H SphereSpectrum 1 64)
      (ha : E.d 2 (1,64) a = Sphere.Internal.product H M' (s := 2) (t := 64) (s' := 1) (t' := 1)
        (Sphere.Internal.hiSquare H M' 5) (Sphere.Internal.hi H M' 0)) : a = Sphere.Internal.hi H M' 6 := by
    obtain ⟨e,he⟩ := I'.basis ⟨.sphere,1,64,["69,1"]⟩ (by
      unfold Raw.degrees
      iterate 85 apply List.mem_cons_of_mem
      exact List.mem_cons_self)
    change E2 H SphereSpectrum 1 64 ≃ₗ[ℤ] (Fin 1 →₀ F2) at e
    change ∀ i : Fin 1, e.symm (Finsupp.single i 1)=I'.interpretation.basis .sphere 1 64 i.val at he
    have heq : e a = Finsupp.single 0 (e a 0) := by
      apply Finsupp.ext
      intro i
      fin_cases i
      simp
    have hxe : a=e.symm (Finsupp.single 0 (e a 0)) := by rw [←heq,LinearEquiv.symm_apply_apply]
    generalize hc : e a 0=c at hxe
    fin_cases c
    · simp only [show (⟨0,by decide⟩:F2)=0 from rfl,Finsupp.single_zero,map_zero] at hxe
      have hz : I'.interpretation.sphere 3 65 (mulAt dataH0 h5Sq)=0 := by
        have h := hd2h6.toHasDifferential.eq_on_page_two.choose_spec
        change E.d 2 (1,64) (I'.interpretation.sphere 1 64 dataH6)=I'.interpretation.sphere 3 65 (mulAt dataH0 h5Sq) at h
        rw [I'.distinguishedClasses.h6,hdA] at h
        rw [hxe,map_zero] at ha
        exact h.symm.trans ha.symm
      obtain ⟨z,hzrep,hzne⟩ := hd2h6.target_survives
      exact (hzne (hzrep.eq_on_page_two.symm.trans hz)).elim
    · change a=e.symm (Finsupp.single 0 1) at hxe
      exact hxe.trans ((he 0).trans (h6Label.symm.trans I'.distinguishedClasses.h6))
  have uniqueValue (x : E2 H SphereSpectrum 9 134) (hx : ThetaBMasseyDefiningSystem M' eB x) : x=eHB := by
    obtain ⟨_,_,_,a,b,ha,hb,hx⟩ := hx
    rw [uniqueA a ha,allProd,add_zero] at hx
    exact hx
  have reachHB : ReachesPage E 3 (9,134) eHB := by
    apply FinitePageCalculus.reaches_earlier (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤1000)
    have hprod := I'.products ⟨1,64,8,70⟩ (by simp [Raw.products]) dataH6 B
    rw [I'.distinguishedClasses.h6] at hprod
    change I'.interpretation.sphere 9 134 (mulAt dataH6 B)=eHB at hprod
    rw [←hprod,hbLabel]
    exact rHB
  refine ⟨?_,hcycle5,hcycle0,hcycleB,hdA,⟨I'.interpretation.sphere 7 70 (mulAt h0Six dataH6),hdB⟩⟩
  · obtain ⟨z,hz⟩ := reachHB
    refine ⟨⟨z,hz,eHB,hdef,hz⟩,⟨z,eHB,hdef,hz⟩,?_⟩
    intro x hx y hy
    obtain ⟨a,ha,hax⟩ := hx
    obtain ⟨b,hb,hby⟩ := hy
    rw [uniqueValue a ha] at hax
    rw [uniqueValue b hb] at hby
    exact FinitePageCalculus.represents_unique hax hby

end

end ThetaBMasseyProof

/-- `lem:toda2ext`: both the specified E3 value and the whole Massey
set are constrained. Two d2 equations alone do not remove indeterminacy.
The proof must reconstruct the two full cycle spaces and their product
images from I's bounded basis, staircase and multiplication comparisons. -/
theorem theta_b_massey_value_and_indeterminacy :
    (∃ z, RepresentsOnPage
      (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      3 (9,134) eH6B z ∧ z ∈ ThetaBMassey M eB) ∧
    ThetaBMasseyZeroIndeterminacy M eB := by
  exact (theta_b_massey_from_inputs computationTheorems literatureTheorems.classical).1


/-- The three page-two cycles in the same fixed Massey defining system. -/
theorem theta_b_massey_cycles : ThetaBMasseyCycles := by
  have h := (theta_b_massey_from_inputs computationTheorems literatureTheorems.classical).2
  exact ⟨h.1,h.2.1,h.2.2.1⟩

/-- The supplied B label is a page-two cycle. -/
theorem theta_b_massey_eB_cycle :
    IsPageCycle (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      2 (8,70) eB := theta_b_massey_cycles.2.2

/-- The first nullhomotopy, with its original order of factors. -/
theorem theta_b_massey_d2_h6 : ThetaBMasseyD2H6 := by
  exact (theta_b_massey_from_inputs computationTheorems literatureTheorems.classical).2.2.2.2.1

/-- The second nullhomotopy uses the same B label and actual Adams differential. -/
theorem theta_b_massey_d2_second_nullhomotopy : ThetaBMasseyD2Second := by
  exact (theta_b_massey_from_inputs computationTheorems literatureTheorems.classical).2.2.2.2.2

/-- The zero indeterminacy is already proved for the entire Massey subset. -/
theorem theta_b_massey_zero_indeterminacy : ThetaBMasseyZeroIndeterminacy M eB :=
  theta_b_massey_value_and_indeterminacy.2

/-- The left indeterminacy image vanishes on the entire displayed E2 space. -/
theorem theta_b_massey_left_indeterminacy_product
    (c : E2 standardFoundation.hf2 SphereSpectrum 7 70)
    (_hc : IsPageCycle (adamsTowerInternalSpectralSequence standardFoundation.hf2.unit SphereSpectrum)
      2 (7,70) c) :
    Sphere.Internal.product standardFoundation.hf2 M (s := 2) (t := 64) (s' := 7) (t' := 70)
      (Sphere.Internal.hiSquare standardFoundation.hf2 M 5) c = 0 :=
  h5_square_times_entire_770_zero computationTheorems c

end
end KIP126.Main.SectionSeven
