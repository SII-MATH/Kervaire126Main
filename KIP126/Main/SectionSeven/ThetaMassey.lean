module

public import KIP126.Computation.LinCoordinates.Certificates.Model.E2.Proofs
public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Computation.LinCoordinates.Certificates.Relations.ThetaMassey
public import KIP126.Main.SectionSeven.SphereClasses
import all Init.Data.List.SplitOn.Basic
import all Init.Data.String.Legacy
import all Init.Data.String.Search
import all Init.Data.String.Slice

-- The CSV coordinate calculations use the defining string and list equations.

@[expose] public section

namespace KIP126.Main.SectionSeven
open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.SpectralSequence
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.SectionSeven
open KIP126.Literature.AdamsSynthetic KIP126.Main.AdamsSynthetic
noncomputable section

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

end

end ThetaBMasseyProof

end
end KIP126.Main.SectionSeven
