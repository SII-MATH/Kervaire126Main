module

public import KIP126.Def.AdamsSynthetic.SectionSeven.AlphaOne
public import KIP126.Def.SpectralSequence.Basic.Category.Proofs
public import KIP126.Def.SpectralSequence.FinitePageCalculus.Proofs
public import KIP126.Def.Synthetic.Detection.Vanishing.Proofs
public import KIP126.Def.Synthetic.Sphere.Homotopy.Proofs
public import KIP126.Computation.Hypotheses
public import KIP126.Computation.LinCoordinates.Certificates.Model.BasisCatalogue.FiniteCertificates

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

section AlphaH0FiniteWindow
open CategoryTheory.Limits KIP126.Algebra KIP126.Computation.SphereAndCofiber
open KIP126.Classical.Adams.PageRepresentatives KIP126.Algebra
open KIP126.LinE2 KIP126.Computation.Near126
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C] [HasFunctorialCofiber (C:=C)]
    {Syn : Type w} [SyntheticCategory.{w,v} Syn] [HasFunctorialCofiber (C:=Syn)]
    {H : Mod2EilenbergMacLane (C:=C)} {M' : MilnorCooperations H} {D' : AdamsComparison H M' Syn}
    {L' : SphereAdamsClasses H} {G : TmfDetectionClasses H}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local irreducible] KIP126.LinE2.homogeneousPart adamsTowerSSData adamsTowerInternalD
private theorem stem123_differentials_d3_s13_t137_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 13, 137, [2], 16, 139, [0], "S0_AdamsE2_ss", 2917⟩ (by
    exact List.mem_of_getElem? (i := 324) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (13,137) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d2_s14_t138_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 14, 138, [1], 16, 139, [1, 2], "S0_AdamsE2_ss", 3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d2_s14_t138_basis0_add_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 14, 138, [0, 1], 16, 139, [2], "S0_AdamsE2_ss", 3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d3_s15_t138_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (15,138) (18,140) (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 15, 138, [2], 18, 140, [2], "proofs.db/log", 462481⟩ (by
    exact List.mem_of_getElem? (i := 654) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (15,138) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 15 138 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d7_s11_t134_basis0_add_basis1_add_basis3 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 7 (11,134) (18,140) (I.interpretation.basis .sphere 11 134 0 + I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 18 140 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 7, 11, 134, [0, 1, 3], 18, 140, [1], "proofs.db/log", 2671068⟩ (by
    exact List.mem_of_getElem? (i := 656) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 7 (11,134) (18,140) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 134 [0, 1, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 18 140 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d5_s10_t134_basis3 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 5 (10,134) (15,138) (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 5, 10, 134, [3], 15, 138, [1], "S0_AdamsE2_ss", 2694⟩ (by
    exact List.mem_of_getElem? (i := 250) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 5 (10,134) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d4_s11_t135_basis1_add_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 4 (11,135) (15,138) (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 4, 11, 135, [1, 2], 15, 138, [0], "S0_AdamsE2_ss", 2781⟩ (by
    exact List.mem_of_getElem? (i := 277) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 4 (11,135) (15,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d3_s14_t137_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (14,137) (17,139) (I.interpretation.basis .sphere 14 137 1) (I.interpretation.basis .sphere 17 139 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 14, 137, [1], 17, 139, [1], "S0_AdamsE2_ss", 2912⟩ (by
    exact List.mem_of_getElem? (i := 339) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d3_s14_t137_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (14,137) (17,139) (I.interpretation.basis .sphere 14 137 0) (I.interpretation.basis .sphere 17 139 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 14, 137, [0], 17, 139, [0], "S0_AdamsE2_ss", 2913⟩ (by
    exact List.mem_of_getElem? (i := 340) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (14,137) (17,139) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 137 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 17 139 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d2_s12_t136_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (12,136) (14,137) (I.interpretation.basis .sphere 12 136 2) (I.interpretation.basis .sphere 14 137 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 12, 136, [2], 14, 137, [2], "S0_AdamsE2_ss", 2849⟩ (by
    exact List.mem_of_getElem? (i := 304) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (12,136) (14,137) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 12 136 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 137 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d3_s13_t136_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (13,136) (16,138) (I.interpretation.basis .sphere 13 136 1) (I.interpretation.basis .sphere 16 138 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 13, 136, [1], 16, 138, [1], "S0_AdamsE2_ss", 2843⟩ (by
    exact List.mem_of_getElem? (i := 319) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (13,136) (16,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 136 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d3_s13_t136_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (13,136) (16,138) (I.interpretation.basis .sphere 13 136 0) (I.interpretation.basis .sphere 16 138 0 + I.interpretation.basis .sphere 16 138 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 13, 136, [0], 16, 138, [0, 2], "S0_AdamsE2_ss", 2844⟩ (by
    exact List.mem_of_getElem? (i := 320) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (13,136) (16,138) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 136 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 138 [0, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d2_s11_t135_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (11,135) (13,136) (I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 13 136 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 2, 11, 135, [2], 13, 136, [2], "S0_AdamsE2_ss", 2782⟩ (by
    exact List.mem_of_getElem? (i := 278) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (11,135) (13,136) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 136 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d3_s9_t133_basis1_add_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) (I.interpretation.basis .sphere 9 133 1 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 9, 133, [1, 2], 12, 135, [0], "S0_AdamsE2_ss", 2775⟩ (by
    exact List.mem_of_getElem? (i := 297) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d3_s9_t133_basis0_add_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) (I.interpretation.basis .sphere 9 133 0 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 1 + I.interpretation.basis .sphere 12 135 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 3, 9, 133, [0, 2], 12, 135, [1, 2], "S0_AdamsE2_ss", 2776⟩ (by
    exact List.mem_of_getElem? (i := 298) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_differentials_d5_s7_t131_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 5 (7,131) (12,135) (I.interpretation.basis .sphere 7 131 1) (I.interpretation.basis .sphere 12 135 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere, .equation, 5, 7, 131, [1], 12, 135, [2], "S0_AdamsE2_ss", 2777⟩ (by
    exact List.mem_of_getElem? (i := 299) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨a,ha,b,hb,h⟩ := hrow
  change HasDifferential (sequence D' .sphere) 5 (7,131) (12,135) a b at h
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at ha hb
  rw [←ha,←hb] at h
  simpa only [add_assoc] using h

private theorem stem123_middle_low_pages
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
    Subsingleton ((sequence D' .sphere).Page 6 (12,135)) ∧
    Subsingleton ((sequence D' .sphere).Page 4 (13,136)) ∧
    Subsingleton ((sequence D' .sphere).Page 4 (14,137)) := by
  classical
  let E := sequence D' .sphere
  obtain ⟨e16_139,he16_139⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
  change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 139 i.val at he16_139
  obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 140 i.val at he18_140
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 138 i.val at he15_138
  obtain ⟨e14_137,he14_137⟩ := I.basis ⟨.sphere, 14, 137, ["23,1,181,1", "0,1,418,1", "0,3,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 215) (by rfl))
  change E.Page 2 (14,137) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e14_137
  change ∀i : Fin 3, e14_137.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 137 i.val at he14_137
  obtain ⟨e13_136,he13_136⟩ := I.basis ⟨.sphere, 13, 136, ["418,1", "417,1", "0,2,386,1"]⟩ (by
    exact List.mem_of_getElem? (i := 207) (by rfl))
  change E.Page 2 (13,136) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e13_136
  change ∀i : Fin 3, e13_136.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 136 i.val at he13_136
  obtain ⟨e12_135,he12_135⟩ := I.basis ⟨.sphere, 12, 135, ["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e12_135
  change ∀i : Fin 3, e12_135.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 135 i.val at he12_135
  obtain ⟨e17_139,he17_139⟩ := I.basis ⟨.sphere, 17, 139, ["13,3,76,1", "0,1,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 237) (by rfl))
  change E.Page 2 (17,139) ≃ₗ[ℤ] (Fin 2 →₀ F2) at e17_139
  change ∀i : Fin 2, e17_139.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 17 139 i.val at he17_139
  obtain ⟨e16_138,he16_138⟩ := I.basis ⟨.sphere, 16, 138, ["437,1", "23,1,189,1", "0,1,424,1"]⟩ (by
    exact List.mem_of_getElem? (i := 229) (by rfl))
  change E.Page 2 (16,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_138
  change ∀i : Fin 3, e16_138.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 138 i.val at he16_138
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := stem123_differentials_d3_s13_t137_basis2 I
  have h366 : HasDifferential E 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := stem123_differentials_d2_s14_t138_basis1 I
  have h367 : HasDifferential E 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := stem123_differentials_d2_s14_t138_basis0_add_basis1 I
  have h654 : HasDifferential E 3 (15,138) (18,140) (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := stem123_differentials_d3_s15_t138_basis2 I
  have h656 : HasDifferential E 7 (11,134) (18,140) (I.interpretation.basis .sphere 11 134 0 + I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 18 140 1) := stem123_differentials_d7_s11_t134_basis0_add_basis1_add_basis3 I
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := stem123_differentials_d5_s10_t134_basis3 I
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := stem123_differentials_d4_s11_t135_basis1_add_basis2 I
  have h339 : HasDifferential E 3 (14,137) (17,139) (I.interpretation.basis .sphere 14 137 1) (I.interpretation.basis .sphere 17 139 1) := stem123_differentials_d3_s14_t137_basis1 I
  have h340 : HasDifferential E 3 (14,137) (17,139) (I.interpretation.basis .sphere 14 137 0) (I.interpretation.basis .sphere 17 139 0) := stem123_differentials_d3_s14_t137_basis0 I
  have h304 : HasDifferential E 2 (12,136) (14,137) (I.interpretation.basis .sphere 12 136 2) (I.interpretation.basis .sphere 14 137 2) := stem123_differentials_d2_s12_t136_basis2 I
  have h319 : HasDifferential E 3 (13,136) (16,138) (I.interpretation.basis .sphere 13 136 1) (I.interpretation.basis .sphere 16 138 1) := stem123_differentials_d3_s13_t136_basis1 I
  have h320 : HasDifferential E 3 (13,136) (16,138) (I.interpretation.basis .sphere 13 136 0) (I.interpretation.basis .sphere 16 138 0 + I.interpretation.basis .sphere 16 138 2) := stem123_differentials_d3_s13_t136_basis0 I
  have h278 : HasDifferential E 2 (11,135) (13,136) (I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 13 136 2) := stem123_differentials_d2_s11_t135_basis2 I
  have h297 : HasDifferential E 3 (9,133) (12,135) (I.interpretation.basis .sphere 9 133 1 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 0) := stem123_differentials_d3_s9_t133_basis1_add_basis2 I
  have h298 : HasDifferential E 3 (9,133) (12,135) (I.interpretation.basis .sphere 9 133 0 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 1 + I.interpretation.basis .sphere 12 135 2) := stem123_differentials_d3_s9_t133_basis0_add_basis2 I
  have h299 : HasDifferential E 5 (7,131) (12,135) (I.interpretation.basis .sphere 7 131 1) (I.interpretation.basis .sphere 12 135 2) := stem123_differentials_d5_s7_t131_basis1 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have d2_16 : E.d 2 (16,139)=0 := by
    obtain ⟨_,_,y0,_,hy0,_⟩ := h324
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2;omega)
      (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
    have d12 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2)=0 := by
      have hd := h366.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d2 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 2)=0 := by
      have hd := h367.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d1 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 1)=0 := by
      simpa only [map_add,d2,add_zero] using d12
    ext a
    change E.d 2 (16,139) a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e16_139
      (fun i => e16_139.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    fin_cases i <;> simp only [apply_ite,map_zero,he16_139,d0,d1,d2,ite_self]
  have hadd {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x+y) (a+b) := by
    exact represents_add_tail (by assumption) (by assumption)
  have hsub {r : ℤ} {p : ℤ × ℤ} {x y : E.Page 2 p} {a b : E.Page r p}
      (hx : RepresentsOnPage E r p x a) (hy : RepresentsOnPage E r p y b) :
      RepresentsOnPage E r p (x-y) (a-b) := by
    exact represents_sub_tail (by assumption) (by assumption)
  have hif {r : ℤ} {p : ℤ × ℤ} {x : E.Page 2 p} {a : E.Page r p}
      (c : F2) (h : RepresentsOnPage E r p x a) :
      RepresentsOnPage E r p (if c=0 then 0 else x) (if c=0 then 0 else a) := by
    split
    · exact RepresentsOnPage.zero h.1
    · exact h
  have e2_map_zero {p : ℤ × ℤ} {N : ℕ}
      (e : E.Page 2 p ≃ₗ[ℤ] (Fin N →₀ F2))
      (h : ∀ i, E.d 2 p (e.symm (Finsupp.single i 1))=0) : E.d 2 p=0 := by
    ext a
    change E.d 2 p a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e
      (fun i => e.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [apply_ite,map_zero,h,ite_self]
  have d2_15 : E.d 2 (15,138)=0 := by
    obtain ⟨_,_,b0,_,hb0,_⟩ := h277
    obtain ⟨_,_,b1,_,hb1,_⟩ := h250
    obtain ⟨_,b2,_,hb2,_,_⟩ := h654
    apply e2_map_zero e15_138
    intro i
    fin_cases i
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<4) (hrep2 _) ⟨b0,hb0⟩
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<5) (hrep2 _) ⟨b1,hb1⟩
    · rw [he15_138]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b2,hb2⟩
  have d2_14 : E.d 2 (14,137)=0 := by
    obtain ⟨_,b0,_,hb0,_,_⟩ := h340
    obtain ⟨_,b1,_,hb1,_,_⟩ := h339
    apply e2_map_zero e14_137
    intro i
    fin_cases i
    · rw [he14_137]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b0,hb0⟩
    · rw [he14_137]
      exact represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (hrep2 _) ⟨b1,hb1⟩
    · rw [he14_137]
      have hd := h304.eq_on_page_two.2
      change E.d 2 (12,136) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (12,136)) _
  have source14 : Subsingleton (E.Page 4 (14,137)) := by
    apply fourth_zero_of_three_basis (by change (2:ℤ)≤2; omega) e14_137 (I.interpretation.basis .sphere 17 139 0) (I.interpretation.basis .sphere 17 139 1)
    · rw [he14_137]
      exact h340
    · rw [he14_137]
      exact h339
    · rw [he14_137]
      exact differential_target_later_zero (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) h304
    · exact d2_15
    all_goals intro hz; have hh := congrArg e17_139 hz
    all_goals simp only [map_add,show I.interpretation.basis .sphere 17 139 0=e17_139.symm (Finsupp.single 0 1) from (he17_139 0).symm,
      show I.interpretation.basis .sphere 17 139 1=e17_139.symm (Finsupp.single 1 1) from (he17_139 1).symm,
      LinearEquiv.apply_symm_apply,map_zero] at hh
    · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 1) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 2 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
  have source13 : Subsingleton (E.Page 4 (13,136)) := by
    apply fourth_zero_of_three_basis (by change (2:ℤ)≤2; omega) e13_136 (I.interpretation.basis .sphere 16 138 0+I.interpretation.basis .sphere 16 138 2)
      (I.interpretation.basis .sphere 16 138 1)
    · rw [he13_136]
      exact h320
    · rw [he13_136]
      exact h319
    · rw [he13_136]
      exact differential_target_later_zero (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) h278
    · exact d2_14
    all_goals intro hz; have hh := congrArg e16_138 hz
    all_goals simp only [map_add,show I.interpretation.basis .sphere 16 138 0=e16_138.symm (Finsupp.single 0 1) from (he16_138 0).symm,
      show I.interpretation.basis .sphere 16 138 1=e16_138.symm (Finsupp.single 1 1) from (he16_138 1).symm,
      show I.interpretation.basis .sphere 16 138 2=e16_138.symm (Finsupp.single 2 1) from (he16_138 2).symm,
      LinearEquiv.apply_symm_apply,map_zero] at hh
    · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
    · have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 0) hh
      norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'
  have source12 : Subsingleton (E.Page 6 (12,135)) := by
    have z0 := differential_target_later_zero (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h297
    have z12 := differential_target_later_zero (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h298
    have z2 := differential_target_later_zero (by change (2:ℤ)≤5;omega) (by decide : (5:ℤ)<6) h299
    have z1 : RepresentsOnPage E 6 (12,135) (I.interpretation.basis .sphere 12 135 1) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using hsub z12 z2
    have hv (i : Fin 3) : RepresentsOnPage E 6 (12,135) (e12_135.symm (Finsupp.single i 1)) 0 := by
      fin_cases i
      · simpa only [he12_135] using z0
      · simpa only [he12_135] using z1
      · simpa only [he12_135] using z2
    have all (a : E.Page 6 (12,135)) : a=0 := by
      obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤6) e12_135 (fun _ => 0) hv a
      simpa only [ite_self,Finset.sum_const_zero] using hc
    exact ⟨fun x y => (all x).trans (all y).symm⟩
  exact ⟨source12,source13,source14⟩

private theorem stem123_middle_nonzero7_target_page_four_nonzero_d2_16
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : (sequence D' .sphere).d 2 (16,139)=0  := by
  classical
  let E := sequence D' .sphere
  obtain ⟨e16_139,he16_139⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
  change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 139 i.val at he16_139
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := stem123_differentials_d3_s13_t137_basis2 I
  have h366 : HasDifferential E 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := stem123_differentials_d2_s14_t138_basis1 I
  have h367 : HasDifferential E 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := stem123_differentials_d2_s14_t138_basis0_add_basis1 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _

  obtain ⟨_,_,y0,_,hy0,_⟩ := h324
  have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2;omega)
    (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
  have d12 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2)=0 := by
    have hd := h366.eq_on_page_two.2
    change E.d 2 (14,138) _ = _ at hd
    rw [←hd]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
  have d2 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 2)=0 := by
    have hd := h367.eq_on_page_two.2
    change E.d 2 (14,138) _ = _ at hd
    rw [←hd]
    exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
  have d1 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 1)=0 := by
    simpa only [map_add,d2,add_zero] using d12
  ext a
  change E.d 2 (16,139) a=0
  obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e16_139
    (fun i => e16_139.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
  rw [hc,map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  fin_cases i <;> simp only [apply_ite,map_zero,he16_139,d0,d1,d2,ite_self]

private theorem stem123_middle_nonzero7_target_page_four_nonzero_bne
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : I.interpretation.basis .sphere 18 140 1 ≠ 0  := by
  classical
  let E := sequence D' .sphere
  obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 140 i.val at he18_140

  rw [show I.interpretation.basis .sphere 18 140 1=e18_140.symm (Finsupp.single 1 1) from (he18_140 1).symm]
  intro h
  have hh := congrArg e18_140 h
  simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
  have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
  norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'

private theorem stem123_middle_nonzero7_target_page_four_nonzero_bdne
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : I.interpretation.basis .sphere 18 140 1-I.interpretation.basis .sphere 18 140 2 ≠ 0  := by
  classical
  let E := sequence D' .sphere
  obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 140 i.val at he18_140

  intro h
  have hh := congrArg e18_140 h
  simp only [map_sub,
    show I.interpretation.basis .sphere 18 140 1=e18_140.symm (Finsupp.single 1 1) from (he18_140 1).symm,
    show I.interpretation.basis .sphere 18 140 2=e18_140.symm (Finsupp.single 2 1) from (he18_140 2).symm,
    LinearEquiv.apply_symm_apply,map_zero] at hh
  have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 1) hh
  norm_num [Finsupp.single_apply, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide] at hh'

private theorem stem123_middle_nonzero7_target_page_four_nonzero_third_image (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
    ∃ b : (sequence D' .sphere).Page 3 (18,140),
    RepresentsOnPage (sequence D' .sphere) 3 (18,140)
      (I.interpretation.basis .sphere 18 140 2) b ∧
    (∀ v : (sequence D' .sphere).Page 3 (15,138),
      (sequence D' .sphere).d 3 (15,138) v=0 ∨ (sequence D' .sphere).d 3 (15,138) v=b) := by

  classical
  let E := sequence D' .sphere
  obtain ⟨e15_138,he15_138⟩ := I.basis ⟨.sphere, 15, 138, ["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e15_138
  change ∀i : Fin 3, e15_138.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 138 i.val at he15_138
  have h654 : HasDifferential E 3 (15,138) (18,140) (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := stem123_differentials_d3_s15_t138_basis2 I
  have h250 : HasDifferential E 5 (10,134) (15,138) (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := stem123_differentials_d5_s10_t134_basis3 I
  have h277 : HasDifferential E 4 (11,135) (15,138) (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := stem123_differentials_d4_s11_t135_basis1_add_basis2 I
  obtain ⟨_,s0,t0,hs0,ht0,_⟩ := h277
  obtain ⟨_,s1,t1,hs1,ht1,_⟩ := h250
  obtain ⟨_,a2,b2,ha2,hb2,hd2⟩ := h654
  change E.d 3 (15,138) a2=b2 at hd2
  obtain ⟨a0,ha0⟩ := represents_before (E := E) (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) ht0
  obtain ⟨a1,ha1⟩ := represents_before (E := E) (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤5) ht1
  have d0 : E.d 3 (15,138) a0=0 := represents_d_zero_of_later (by change (2:ℤ)≤3;omega)
    (by decide : (3:ℤ)<4) ha0 ⟨t0,ht0⟩
  have d1 : E.d 3 (15,138) a1=0 := represents_d_zero_of_later (by change (2:ℤ)≤3;omega)
    (by decide : (3:ℤ)<5) ha1 ⟨t1,ht1⟩
  have image3 (v : E.Page 3 (15,138)) : E.d 3 (15,138) v=0 ∨ E.d 3 (15,138) v=b2 := by
    let vv : Fin 3 → E.Page 3 (15,138) := ![a0,a1,a2]
    have hv (i : Fin 3) : RepresentsOnPage E 3 (15,138) (e15_138.symm (Finsupp.single i 1)) (vv i) := by
      fin_cases i
      · change RepresentsOnPage E 3 (15,138) _ a0
        rw [he15_138]
        exact ha0
      · change RepresentsOnPage E 3 (15,138) _ a1
        rw [he15_138]
        exact ha1
      · change RepresentsOnPage E 3 (15,138) _ a2
        rw [he15_138]
        exact ha2
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤3) e15_138 vv hv v
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hc
    change v=(if c 0=0 then 0 else a0)+((if c 1=0 then 0 else a1)+(if c 2=0 then 0 else a2)) at hc
    rw [hc]
    simp only [map_add,apply_ite,map_zero,d0,d1,hd2,ite_self,zero_add]
    by_cases hc2 : c 2=0
    · exact Or.inl (by simp only [hc2,ite_true])
    · exact Or.inr (by simp only [hc2,ite_false])
  exact ⟨b2,hb2,image3⟩

private theorem stem123_middle_nonzero7_target_page_four_nonzero (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G)
    {y4 : (sequence D' .sphere).Page 4 (18,140)}
    (hy4 : RepresentsOnPage (sequence D' .sphere) 4 (18,140)
      (I.interpretation.basis .sphere 18 140 1) y4) : y4 ≠ 0 := by
  classical
  let E := sequence D' .sphere
  have d2_16 : E.d 2 (16,139)=0 := stem123_middle_nonzero7_target_page_four_nonzero_d2_16 I
  obtain ⟨b2,hb2,image3⟩ := stem123_middle_nonzero7_target_page_four_nonzero_third_image I
  obtain ⟨y3,hy3⟩ := represents_before (by decide : (2:ℤ)≤3) (by decide : (3:ℤ)≤4) hy4
  have bne : I.interpretation.basis .sphere 18 140 1 ≠ 0  := stem123_middle_nonzero7_target_page_four_nonzero_bne I
  have bdne : I.interpretation.basis .sphere 18 140 1-I.interpretation.basis .sphere 18 140 2 ≠ 0  := stem123_middle_nonzero7_target_page_four_nonzero_bdne I
  have y3ne : y3≠0 := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 2) (p := (18,140)) (by change (2:ℤ)≤2;omega)
    (by decide) d2_16 hy3 (represents_two_self _) bne
  have y3diff : y3-b2≠0 := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 2) (p := (18,140)) (by change (2:ℤ)≤2;omega)
    (by decide) d2_16 (represents_sub_tail hy3 hb2) (represents_two_self _) bdne

  apply represents_next_nonzero_of_incoming_two_cases_at
    (r := 3) (p := (18,140)) (q := (15,138)) (by rfl)
    (by change (2:ℤ)≤3; omega) (by decide : (2:ℤ)≤3) hy4 hy3 ?_ y3ne y3diff
  intro v
  change E.d 3 (15,138) v=0 ∨ E.d 3 (15,138) v=b2
  exact image3 v

private theorem stem123_middle_nonzero7
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
    HasNonzeroDifferential (sequence D' .sphere) 7 (11,134) (18,140)
      (I.interpretation.basis .sphere 11 134 0 + I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 18 140 1) := by
  classical
  let E := sequence D' .sphere
  have h656 : HasDifferential E 7 (11,134) (18,140) (I.interpretation.basis .sphere 11 134 0 + I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 18 140 1) := stem123_differentials_d7_s11_t134_basis0_add_basis1_add_basis3 I
  obtain ⟨source12,source13,source14⟩ := stem123_middle_low_pages I
  obtain ⟨hdeg,x7,y7,hx7,hy7,hd7⟩ := h656
  obtain ⟨y4,hy4⟩ := represents_before (E := E) (by decide : (2:ℤ)≤4) (by decide : (4:ℤ)≤7) hy7
  have y4ne : y4≠0 := stem123_middle_nonzero7_target_page_four_nonzero I hy4
  have incoming4 : E.d 4 (14,137)=0 := by
    ext v
    change E.d 4 (14,137) v=0
    rw [source14.elim v 0,map_zero]
  have incoming5 : E.d 5 (13,136)=0 := by
    have hz := adamsTowerInternal_page_subsingleton_of_le H.unit SphereSpectrum 4 5 13 136
      (by decide) (by decide) source13
    ext v
    change E.d 5 (13,136) v=0
    rw [hz.elim v 0,map_zero]
  have incoming6 : E.d 6 (12,135)=0 := by
    ext v
    change E.d 6 (12,135) v=0
    rw [source12.elim v 0,map_zero]
  obtain ⟨y5,hy5⟩ := represents_before (E := E) (by decide : (2:ℤ)≤5) (by decide : (5:ℤ)≤7) hy7
  obtain ⟨y6,hy6⟩ := represents_before (E := E) (by decide : (2:ℤ)≤6) (by decide : (6:ℤ)≤7) hy7
  have y5ne := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 4) (p := (18,140)) (by change (2:ℤ)≤4;omega) (by decide) incoming4 hy5 hy4 y4ne
  have y6ne := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 5) (p := (18,140)) (by change (2:ℤ)≤5;omega) (by decide) incoming5 hy6 hy5 y5ne
  have y7ne := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 6) (p := (18,140)) (by change (2:ℤ)≤6;omega) (by decide) incoming6 hy7 hy6 y6ne
  exact ⟨hdeg,x7,y7,hx7,hy7,hd7,y7ne⟩

private theorem stem123_middle_nonzero3
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
    HasNonzeroDifferential (sequence D' .sphere) 3 (15,138) (18,140)
      (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := by
  classical
  let E := sequence D' .sphere
  obtain ⟨e16_139,he16_139⟩ := I.basis ⟨.sphere, 16, 139, ["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e16_139
  change ∀i : Fin 3, e16_139.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 139 i.val at he16_139
  obtain ⟨e18_140,he18_140⟩ := I.basis ⟨.sphere, 18, 140, ["8,1,279,1", "1,1,436,1", "0,2,437,1"]⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  change E.Page 2 (18,140) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e18_140
  change ∀i : Fin 3, e18_140.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 18 140 i.val at he18_140
  have h324 : HasDifferential E 3 (13,137) (16,139) (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := stem123_differentials_d3_s13_t137_basis2 I
  have h366 : HasDifferential E 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := stem123_differentials_d2_s14_t138_basis1 I
  have h367 : HasDifferential E 2 (14,138) (16,139) (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := stem123_differentials_d2_s14_t138_basis0_add_basis1 I
  have h654 : HasDifferential E 3 (15,138) (18,140) (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := stem123_differentials_d3_s15_t138_basis2 I
  have hrep2 {p : ℤ × ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    exact represents_two_self _
  have d2_16 : E.d 2 (16,139)=0 := by
    obtain ⟨_,_,y0,_,hy0,_⟩ := h324
    have d0 := represents_d_zero_of_later (by change (2:ℤ)≤2;omega)
      (by decide : (2:ℤ)<3) (hrep2 _) ⟨y0,hy0⟩
    have d12 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2)=0 := by
      have hd := h366.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d2 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 2)=0 := by
      have hd := h367.eq_on_page_two.2
      change E.d 2 (14,138) _ = _ at hd
      rw [←hd]
      exact ConcreteCategory.congr_hom (E.d_comp_d 2 (14,138)) _
    have d1 : E.d 2 (16,139) (I.interpretation.basis .sphere 16 139 1)=0 := by
      simpa only [map_add,d2,add_zero] using d12
    ext a
    change E.d 2 (16,139) a=0
    obtain ⟨c,hc⟩ := page_generated_from_representatives (by decide : (2:ℤ)≤2) e16_139
      (fun i => e16_139.symm (Finsupp.single i 1)) (fun i => hrep2 _) a
    rw [hc,map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    fin_cases i <;> simp only [apply_ite,map_zero,he16_139,d0,d1,d2,ite_self]
  obtain ⟨_,a2,b2,ha2,hb2,hd2⟩ := h654
  change E.d 3 (15,138) a2=b2 at hd2
  have b2base : I.interpretation.basis .sphere 18 140 2 ≠ 0 := by
    intro h
    rw [show I.interpretation.basis .sphere 18 140 2=e18_140.symm (Finsupp.single 2 1) from (he18_140 2).symm] at h
    have hh := congrArg e18_140 h
    simp only [LinearEquiv.apply_symm_apply,map_zero] at hh
    have hh' := congrArg (fun f : Fin 3 →₀ F2 => f 2) hh
    norm_num [Finsupp.single_apply] at hh'
  have b2ne : b2≠0 := represents_next_nonzero_of_incoming_zero_at (E := E) (r := 2) (p := (18,140))
    (by change (2:ℤ)≤2;omega) (by decide) d2_16 hb2 (hrep2 _) b2base
  exact ⟨by rfl,a2,b2,ha2,hb2,hd2,b2ne⟩

private theorem stem123_filtration_bounds
    (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
    Subsingleton ((sequence D' .sphere).Page 6 (12,135)) ∧
    Subsingleton ((sequence D' .sphere).Page 4 (13,136)) ∧
    Subsingleton ((sequence D' .sphere).Page 4 (14,137)) ∧
    HasNonzeroDifferential (sequence D' .sphere) 7 (11,134) (18,140)
      (I.interpretation.basis .sphere 11 134 0 + I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 18 140 1) ∧
    HasNonzeroDifferential (sequence D' .sphere) 3 (15,138) (18,140)
      (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2) := by
  obtain ⟨source12,source13,source14⟩ := stem123_middle_low_pages I
  exact ⟨source12,source13,source14,stem123_middle_nonzero7 I,stem123_middle_nonzero3 I⟩

private theorem stem123_weight130_finite_quotients_d3_s13_t137_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (13,137) (16,139)
    (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,13,137,[2],16,139,[0],"S0_AdamsE2_ss",3074⟩ (by
    exact List.mem_of_getElem? (i := 368) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (13,137) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 13 137 [2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d2_s14_t138_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (14,138) (16,139)
    (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,138,[1],16,139,[1, 2],"S0_AdamsE2_ss",3072⟩ (by
    exact List.mem_of_getElem? (i := 366) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d2_s14_t138_basis0_add_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (14,138) (16,139)
    (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,14,138,[0, 1],16,139,[2],"S0_AdamsE2_ss",3073⟩ (by
    exact List.mem_of_getElem? (i := 367) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (14,138) (16,139) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 14 138 [0, 1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 16 139 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d2_s10_t133_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (10,133) (12,134)
    (I.interpretation.basis .sphere 10 133 1) (I.interpretation.basis .sphere 12 134 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,133,[1],12,134,[2],"S0_AdamsE2_ss",2625⟩ (by
    exact List.mem_of_getElem? (i := 245) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (10,133) (12,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d2_s10_t133_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (10,133) (12,134)
    (I.interpretation.basis .sphere 10 133 0) (I.interpretation.basis .sphere 12 134 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,10,133,[0],12,134,[2],"S0_AdamsE2_ss",2682⟩ (by
    exact List.mem_of_getElem? (i := 294) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (10,133) (12,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 134 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d3_s7_t131_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (7,131) (10,133)
    (I.interpretation.basis .sphere 7 131 0) (I.interpretation.basis .sphere 10 133 0 + I.interpretation.basis .sphere 10 133 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,7,131,[0],10,133,[0, 1],"S0_AdamsE2_ss",2624⟩ (by
    exact List.mem_of_getElem? (i := 244) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (7,131) (10,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [0, 1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d2_s8_t132_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (8,132) (10,133)
    (I.interpretation.basis .sphere 8 132 0) (I.interpretation.basis .sphere 10 133 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,8,132,[0],10,133,[2],"S0_AdamsE2_ss",2623⟩ (by
    exact List.mem_of_getElem? (i := 243) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (8,132) (10,133) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 8 132 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 10 133 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d4_s11_t135_basis1_add_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 4 (11,135) (15,138)
    (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,4,11,135,[1, 2],15,138,[0],"S0_AdamsE2_ss",3000⟩ (by
    exact List.mem_of_getElem? (i := 351) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 4 (11,135) (15,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 135 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d5_s10_t134_basis3 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 5 (10,134) (15,138)
    (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,5,10,134,[3],15,138,[1],"S0_AdamsE2_ss",3001⟩ (by
    exact List.mem_of_getElem? (i := 352) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 5 (10,134) (15,138) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 10 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 15 138 [1] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d3_s11_t134_basis1_add_basis3 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (11,134) (14,136)
    (I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 14 136 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,11,134,[1, 3],14,136,[0],"S0_AdamsE2_ss",2688⟩ (by
    exact List.mem_of_getElem? (i := 272) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (11,134) (14,136) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 134 [1, 3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 14 136 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d2_s11_t134_basis3 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (11,134) (13,135)
    (I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 13 135 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,11,134,[3],13,135,[2],"S0_AdamsE2_ss",2689⟩ (by
    exact List.mem_of_getElem? (i := 273) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (11,134) (13,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 11 134 [3] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 13 135 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d5_s6_t130_basis0 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 5 (6,130) (11,134)
    (I.interpretation.basis .sphere 6 130 0) (I.interpretation.basis .sphere 11 134 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,5,6,130,[0],11,134,[2],"S0_AdamsE2_ss",2686⟩ (by
    exact List.mem_of_getElem? (i := 270) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 5 (6,130) (11,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 6 130 [0] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d2_s9_t133_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 2 (9,133) (11,134)
    (I.interpretation.basis .sphere 9 133 1) (I.interpretation.basis .sphere 11 134 4) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,2,9,133,[1],11,134,[4],"S0_AdamsE2_ss",2685⟩ (by
    exact List.mem_of_getElem? (i := 269) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 2 (9,133) (11,134) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 11 134 [4] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d3_s9_t133_basis1_add_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (9,133) (12,135)
    (I.interpretation.basis .sphere 9 133 1 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 0) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,133,[1, 2],12,135,[0],"S0_AdamsE2_ss",2775⟩ (by
    exact List.mem_of_getElem? (i := 297) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [1, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [0] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d3_s9_t133_basis0_add_basis2 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 3 (9,133) (12,135)
    (I.interpretation.basis .sphere 9 133 0 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 1 + I.interpretation.basis .sphere 12 135 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,3,9,133,[0, 2],12,135,[1, 2],"S0_AdamsE2_ss",2776⟩ (by
    exact List.mem_of_getElem? (i := 298) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 3 (9,133) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 9 133 [0, 2] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [1, 2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_d5_s7_t131_basis1 (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) : HasDifferential (sequence D' .sphere) 5 (7,131) (12,135)
    (I.interpretation.basis .sphere 7 131 1) (I.interpretation.basis .sphere 12 135 2) := by
  classical
  have hrow := I.adamsStatements ⟨.sphere,.equation,5,7,131,[1],12,135,[2],"S0_AdamsE2_ss",2777⟩ (by
    exact List.mem_of_getElem? (i := 299) (by rfl))
  dsimp only [AdamsStatement] at hrow
  obtain ⟨x,hx,y,hy,hd⟩ := hrow
  change HasDifferential (sequence D' .sphere) 5 (7,131) (12,135) x y at hd
  have vx : Raw.coordinatesValid Raw.degrees .sphere 7 131 [1] = true := rfl
  have vy : Raw.coordinatesValid Raw.degrees .sphere 12 135 [2] = true := rfl
  simp only [E2Interpretation.coordinateSum,vx,vy,if_true,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero,Option.some.injEq] at hx hy
  rw [←hx,←hy] at hd
  simpa only [add_assoc] using hd

private theorem stem123_weight130_finite_quotients_boundary_of_zero_representative
    {r : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
    (hx : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x 0) :
    x ∈ boundaries H SphereSpectrum (r-1) p := by
  classical
  let E := adamsTowerInternalSpectralSequence H.unit SphereSpectrum
  let P := E.ssData p
  obtain ⟨hr,z,hz,hzero⟩ := hx
  change (Subobject.ofLE (P.Z ↑(r-2).toNat) (P.Z 0) _ ≫ P.pageπ 0) z=x at hz
  change P.pageπ ↑(r-2).toNat z=0 at hzero
  obtain ⟨y,hy⟩ := (cokernel_π_eq_zero_iff_mem_range
    (Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _)) z).mp hzero
  have hrindex : r-1-1=r-2 := by omega
  change ∃ y, boundaryMap H SphereSpectrum ↑(r-1-1).toNat p y=x
  rw [hrindex]
  refine ⟨y,?_⟩
  have hf : Subobject.ofLE (P.B ↑(r-2).toNat) (P.Z ↑(r-2).toNat) (P.B_le_Z _) ≫
      cycleMap H SphereSpectrum ↑(r-2).toNat p = boundaryMap H SphereSpectrum ↑(r-2).toNat p := by
    dsimp only [boundaryMap,cycleMap,P,E]
    rw [←Category.assoc,Subobject.ofLE_comp_ofLE]
  rw [←hf,CategoryTheory.comp_apply,hy]
  exact hz

private theorem stem123_weight130_finite_quotients_cycle_quotient_zero_of_page
    (r c b : ℤ) (p : ℤ×ℤ) (hr : 2≤r) (hc : r≤c+1) (hb : r-1≤b)
    (hz : Subsingleton ((adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r p)) :
    Subsingleton (CycleQuotient H SphereSpectrum c b p) := by
  classical
  have hall (x : cycles H SphereSpectrum c p) : NestedQuotient.projection _ (boundaries H SphereSpectrum b p) x=0 := by
    obtain ⟨x',hx'⟩ := (isCycle_iff_represents H SphereSpectrum (c+1) (by omega) p x.val).mp ⟨by omega,by simp⟩
    obtain ⟨xr,hxr⟩ := represents_before hr hc hx'
    rw [hz.elim xr 0] at hxr
    exact (NestedQuotient.projection_eq_zero x).mpr
      (boundaries_monotone H SphereSpectrum p hb (stem123_weight130_finite_quotients_boundary_of_zero_representative hxr))
  have hz' (x : CycleQuotient H SphereSpectrum c b p) : x=0 := by
    obtain ⟨x⟩ := x
    exact hall x
  exact ⟨fun x y=>(hz' x).trans (hz' y).symm⟩

private theorem stem123_weight130_finite_quotients_cycle_differential_zero
    {r c : ℤ} {p : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2}
    {a : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page r p}
    (hr : 2≤r) (hc : r≤c)
    (hx : x∈cycles H SphereSpectrum c p)
    (ha : RepresentsOnPage (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p x a) :
    (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d r p a=0 := by
  classical
  obtain ⟨y,hy⟩ := (isCycle_iff_represents H SphereSpectrum (c+1) (by omega) p x).mp
    ⟨by omega,by simpa using hx⟩
  exact represents_d_zero_of_later hr (by omega : r<c+1) ha ⟨y,hy⟩

private theorem stem123_weight130_finite_quotients_nonzero_differential_not_cycle
    {r c : ℤ} {p q : ℤ×ℤ} {x : E2 H SphereSpectrum p.1 p.2} {y : E2 H SphereSpectrum q.1 q.2}
    (hr : 2≤r) (hc : r≤c)
    (hd : HasNonzeroDifferential (adamsTowerInternalSpectralSequence H.unit SphereSpectrum) r p q x y) :
    x∉cycles H SphereSpectrum c p := by
  classical
  intro hx
  obtain ⟨rfl,a,b,ha,hb,hd,hne⟩ := hd
  simp only [eqToHom_refl,Category.comp_id] at hd
  exact hne (hd.symm.trans (stem123_weight130_finite_quotients_cycle_differential_zero hr hc hx ha))

private theorem stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
    {c b : ℤ} {p : ℤ×ℤ}
    (h : cycles H SphereSpectrum c p ≤ boundaries H SphereSpectrum b p) :
    Subsingleton (CycleQuotient H SphereSpectrum c b p) := by
  classical
  have hz (x : CycleQuotient H SphereSpectrum c b p) : x=0 := by
    obtain ⟨x⟩ := x
    exact (NestedQuotient.projection_eq_zero x).mpr (h x.property)
  exact ⟨fun x y=>(hz x).trans (hz y).symm⟩

private theorem stem123_weight130_finite_quotients_basis_mem_submodule
    {V : Type v} [AddCommGroup V] [Module ℤ V] {N : ℕ}
    (e : V ≃ₗ[ℤ] (Fin N →₀ F2)) (B : Submodule ℤ V)
    (h : ∀ i, e.symm (Finsupp.single i 1)∈B) (x : V) : x∈B := by
  classical
  have all (f : Fin N →₀ F2) : e.symm f∈B := by
    induction f using Finsupp.induction with
    | zero => simpa only [map_zero] using B.zero_mem
    | @single_add i a f hi ha ih =>
      rw [map_add]
      apply B.add_mem _ ih
      fin_cases a
      · change e.symm (Finsupp.single i (0:F2))∈B
        simpa only [Finsupp.single_zero,map_zero] using B.zero_mem
      · change e.symm (Finsupp.single i (1:F2))∈B
        exact h i
  simpa only [LinearEquiv.symm_apply_apply] using all (e x)

private theorem stem123_weight130_finite_quotients_stem123_af16_quotient (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
    Subsingleton (CycleQuotient H SphereSpectrum 2 10 (16,139)) := by
  classical
  let E := sequence D' .sphere
  have h368 : HasDifferential E 3 (13,137) (16,139)
      (I.interpretation.basis .sphere 13 137 2) (I.interpretation.basis .sphere 16 139 0) := stem123_weight130_finite_quotients_d3_s13_t137_basis2 I
  have h366 : HasDifferential E 2 (14,138) (16,139)
      (I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 1 + I.interpretation.basis .sphere 16 139 2) := stem123_weight130_finite_quotients_d2_s14_t138_basis1 I
  have h367 : HasDifferential E 2 (14,138) (16,139)
      (I.interpretation.basis .sphere 14 138 0 + I.interpretation.basis .sphere 14 138 1) (I.interpretation.basis .sphere 16 139 2) := stem123_weight130_finite_quotients_d2_s14_t138_basis0_add_basis1 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,16,139,["1,1,424,1", "0,1,438,1", "0,3,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 230) (by rfl))
  change E.Page 2 (16,139) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 16 139 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 16 139 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 16 139 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 16 139 2 := he 2
  let B := boundaries H SphereSpectrum 10 (16,139)
  have b0 : I.interpretation.basis .sphere 16 139 0∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=11)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤3;omega) (by decide) h368)
  have b2 : I.interpretation.basis .sphere 16 139 2∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=11)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h367)
  have b12 : I.interpretation.basis .sphere 16 139 1+I.interpretation.basis .sphere 16 139 2∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=11)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h366)
  have b1 : I.interpretation.basis .sphere 16 139 1∈B := by
    simpa only [add_sub_cancel_right] using B.sub_mem b12 b2
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  apply stem123_weight130_finite_quotients_basis_mem_submodule e B _ x
  intro i
  fin_cases i
  · simpa only [he] using b0
  · simpa only [he] using b1
  · simpa only [he] using b2

private theorem stem123_weight130_finite_quotients_stem123_af10_quotient (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
    Subsingleton (CycleQuotient H SphereSpectrum 8 4 (10,133)) := by
  classical
  let E := sequence D' .sphere
  have h245 : HasDifferential E 2 (10,133) (12,134)
      (I.interpretation.basis .sphere 10 133 1) (I.interpretation.basis .sphere 12 134 2) := stem123_weight130_finite_quotients_d2_s10_t133_basis1 I
  have h294 : HasDifferential E 2 (10,133) (12,134)
      (I.interpretation.basis .sphere 10 133 0) (I.interpretation.basis .sphere 12 134 2) := stem123_weight130_finite_quotients_d2_s10_t133_basis0 I
  have h244 : HasDifferential E 3 (7,131) (10,133)
      (I.interpretation.basis .sphere 7 131 0) (I.interpretation.basis .sphere 10 133 0 + I.interpretation.basis .sphere 10 133 1) := stem123_weight130_finite_quotients_d3_s7_t131_basis0 I
  have h243 : HasDifferential E 2 (8,132) (10,133)
      (I.interpretation.basis .sphere 8 132 0) (I.interpretation.basis .sphere 10 133 2) := stem123_weight130_finite_quotients_d2_s8_t132_basis0 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,10,133,["372,1", "69,1,80,1", "0,1,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 180) (by rfl))
  change E.Page 2 (10,133) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 10 133 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 10 133 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 10 133 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 10 133 2 := he 2
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,12,134,["18,1,188,1", "0,1,371,1", "0,1,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 198) (by rfl))
  change E.Page 2 (12,134) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 134 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 12 134 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 12 134 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 12 134 2 := hf 2
  let B := boundaries H SphereSpectrum 4 (10,133)
  have b01 : I.interpretation.basis .sphere 10 133 0+I.interpretation.basis .sphere 10 133 1∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=5) (p:=(10,133))
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤3;omega) (by decide) h244)
  have z2 : RepresentsOnPage E 5 (10,133) (I.interpretation.basis .sphere 10 133 2) 0 :=
      differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h243
  have b2 : I.interpretation.basis .sphere 10 133 2∈B := stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=5) (p:=(10,133)) z2
  have rep2 (x : E.Page 2 (10,133)) : RepresentsOnPage E 2 (10,133) x x := by
    haveI : Epi ((E.ssData (10,133)).pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective ((E.ssData (10,133)).pageπ 0)).mp inferInstance x
    exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩
  have hd0 : E.d 2 (10,133) (I.interpretation.basis .sphere 10 133 0)=I.interpretation.basis .sphere 12 134 2 := h294.eq_on_page_two.2
  have hd1 : E.d 2 (10,133) (I.interpretation.basis .sphere 10 133 1)=I.interpretation.basis .sphere 12 134 2 := h245.eq_on_page_two.2
  have hd2 : E.d 2 (10,133) (I.interpretation.basis .sphere 10 133 2)=0 :=
    represents_d_zero_of_later (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z2⟩
  have ne : I.interpretation.basis .sphere 12 134 2≠0 := by
    intro hh
    rw [show I.interpretation.basis .sphere 12 134 2=f.symm (Finsupp.single 2 1) from (hf 2).symm] at hh
    have hh' := congrArg (fun x=>f x 2) hh
    norm_num [Finsupp.single_apply] at hh'
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  have hd : E.d 2 (10,133) x=0 := stem123_weight130_finite_quotients_cycle_differential_zero  (r:=2) (c:=8) (p:=(10,133)) (x:=x) (by decide) (by decide) hx (rep2 x)
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0 at hxe
  generalize hc1 : e x 1=c1 at hxe
  generalize hc2 : e x 2=c2 at hxe
  fin_cases c0 <;> fin_cases c1 <;> fin_cases c2
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [Finsupp.single_zero,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact b2
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he1,add_zero,zero_add] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [hd1] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,zero_add] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2,add_zero] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he0,add_zero] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [hd0] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,add_zero] at hxe
    rw [hxe]
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,add_zero] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,add_zero] at hxe
    rw [hxe]
    exact b01
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,he0,he1,he2] at hxe
    rw [hxe]
    exact B.add_mem b01 b2

private theorem stem123_weight130_finite_quotients_stem123_af15_quotient (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G)
    (h3 : HasNonzeroDifferential (sequence D' .sphere) 3 (15,138) (18,140)
      (I.interpretation.basis .sphere 15 138 2) (I.interpretation.basis .sphere 18 140 2)) :
    Subsingleton (CycleQuotient H SphereSpectrum 3 9 (15,138)) := by
  classical
  let E := sequence D' .sphere
  have h351 : HasDifferential E 4 (11,135) (15,138)
      (I.interpretation.basis .sphere 11 135 1 + I.interpretation.basis .sphere 11 135 2) (I.interpretation.basis .sphere 15 138 0) := stem123_weight130_finite_quotients_d4_s11_t135_basis1_add_basis2 I
  have h352 : HasDifferential E 5 (10,134) (15,138)
      (I.interpretation.basis .sphere 10 134 3) (I.interpretation.basis .sphere 15 138 1) := stem123_weight130_finite_quotients_d5_s10_t134_basis3 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,15,138,["438,1", "7,1,279,1", "0,2,418,1"]⟩ (by
    exact List.mem_of_getElem? (i := 222) (by rfl))
  change E.Page 2 (15,138) ≃ₗ[ℤ] (Fin 3 →₀ F2) at e
  change ∀ i : Fin 3, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 15 138 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 15 138 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 15 138 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 15 138 2 := he 2
  let B := boundaries H SphereSpectrum 9 (15,138)
  let C := cycles H SphereSpectrum 3 (15,138)
  have b0 : I.interpretation.basis .sphere 15 138 0∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=10)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤4;omega) (by decide) h351)
  have b1 : I.interpretation.basis .sphere 15 138 1∈B := by
    exact stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=10)
      (differential_target_later_zero (E:=E) (by change (2:ℤ)≤5;omega) (by decide) h352)
  have c0 : I.interpretation.basis .sphere 15 138 0∈C := boundaries_le_cycles H SphereSpectrum (15,138) 9 3 b0
  have c1 : I.interpretation.basis .sphere 15 138 1∈C := boundaries_le_cycles H SphereSpectrum (15,138) 9 3 b1
  have bad : I.interpretation.basis .sphere 15 138 2∉C := stem123_weight130_finite_quotients_nonzero_differential_not_cycle (by decide) (by decide) h3
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=c0' at hxe
  generalize hc1 : e x 1=c1' at hxe
  generalize hc2 : e x 2=c2' at hxe
  fin_cases c0' <;> fin_cases c1' <;> fin_cases c2'
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [Finsupp.single_zero,he2,add_zero,zero_add] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (C.zero_mem)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he1,add_zero,zero_add] at hxe
    rw [hxe]
    exact b1
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,zero_add] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (c1)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he0,add_zero] at hxe
    rw [hxe]
    exact b0
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,add_zero] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (c0)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,add_zero] at hxe
    rw [hxe]
    exact B.add_mem b0 b1
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)) at hxe
    simp only [map_add,he0,he1,he2] at hxe
    exfalso
    apply bad
    have hh := C.sub_mem hx (C.add_mem c0 c1)
    rw [hxe] at hh
    simpa only [add_sub_cancel_left,add_sub_cancel_right,sub_zero] using hh

private theorem stem123_weight130_finite_quotients_stem123_af11_quotient (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G)
    (h7 : HasNonzeroDifferential (sequence D' .sphere) 7 (11,134) (18,140)
      (I.interpretation.basis .sphere 11 134 0 + I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3)
      (I.interpretation.basis .sphere 18 140 1)) :
    Subsingleton (CycleQuotient H SphereSpectrum 7 5 (11,134)) := by
  classical
  let E := sequence D' .sphere
  have h272 : HasDifferential E 3 (11,134) (14,136)
      (I.interpretation.basis .sphere 11 134 1 + I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 14 136 0) := stem123_weight130_finite_quotients_d3_s11_t134_basis1_add_basis3 I
  have h273 : HasDifferential E 2 (11,134) (13,135)
      (I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 13 135 2) := stem123_weight130_finite_quotients_d2_s11_t134_basis3 I
  have h270 : HasDifferential E 5 (6,130) (11,134)
      (I.interpretation.basis .sphere 6 130 0) (I.interpretation.basis .sphere 11 134 2) := stem123_weight130_finite_quotients_d5_s6_t130_basis0 I
  have h269 : HasDifferential E 2 (9,133) (11,134)
      (I.interpretation.basis .sphere 9 133 1) (I.interpretation.basis .sphere 11 134 4) := stem123_weight130_finite_quotients_d2_s9_t133_basis1 I
  have h297 : HasDifferential E 3 (9,133) (12,135)
      (I.interpretation.basis .sphere 9 133 1 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 0) := stem123_weight130_finite_quotients_d3_s9_t133_basis1_add_basis2 I
  have h298 : HasDifferential E 3 (9,133) (12,135)
      (I.interpretation.basis .sphere 9 133 0 + I.interpretation.basis .sphere 9 133 2) (I.interpretation.basis .sphere 12 135 1 + I.interpretation.basis .sphere 12 135 2) := stem123_weight130_finite_quotients_d3_s9_t133_basis0_add_basis2 I
  have h299 : HasDifferential E 5 (7,131) (12,135)
      (I.interpretation.basis .sphere 7 131 1) (I.interpretation.basis .sphere 12 135 2) := stem123_weight130_finite_quotients_d5_s7_t131_basis1 I
  obtain ⟨e,he⟩ := I.basis ⟨.sphere,11,134,["387,1", "386,1", "18,1,189,1", "0,1,69,1,80,1", "0,2,366,1"]⟩ (by
    exact List.mem_of_getElem? (i := 190) (by rfl))
  change E.Page 2 (11,134) ≃ₗ[ℤ] (Fin 5 →₀ F2) at e
  change ∀ i : Fin 5, e.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 11 134 i.val at he
  have he0 : e.symm (Finsupp.single (0:Fin 5) 1) = I.interpretation.basis .sphere 11 134 0 := he 0
  have he1 : e.symm (Finsupp.single (1:Fin 5) 1) = I.interpretation.basis .sphere 11 134 1 := he 1
  have he2 : e.symm (Finsupp.single (2:Fin 5) 1) = I.interpretation.basis .sphere 11 134 2 := he 2
  have he3 : e.symm (Finsupp.single (3:Fin 5) 1) = I.interpretation.basis .sphere 11 134 3 := he 3
  have he4 : e.symm (Finsupp.single (4:Fin 5) 1) = I.interpretation.basis .sphere 11 134 4 := he 4
  obtain ⟨f,hf⟩ := I.basis ⟨.sphere,13,135,["407,1", "1,2,351,1", "0,2,69,1,79,1"]⟩ (by
    exact List.mem_of_getElem? (i := 206) (by rfl))
  change E.Page 2 (13,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at f
  change ∀ i : Fin 3, f.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 13 135 i.val at hf
  have hf0 : f.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 13 135 0 := hf 0
  have hf1 : f.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 13 135 1 := hf 1
  have hf2 : f.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 13 135 2 := hf 2
  obtain ⟨a,ha⟩ := I.basis ⟨.sphere,12,135,["408,1", "0,1,386,1", "0,2,69,1,80,1"]⟩ (by
    exact List.mem_of_getElem? (i := 199) (by rfl))
  change E.Page 2 (12,135) ≃ₗ[ℤ] (Fin 3 →₀ F2) at a
  change ∀ i : Fin 3, a.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 12 135 i.val at ha
  have ha0 : a.symm (Finsupp.single (0:Fin 3) 1) = I.interpretation.basis .sphere 12 135 0 := ha 0
  have ha1 : a.symm (Finsupp.single (1:Fin 3) 1) = I.interpretation.basis .sphere 12 135 1 := ha 1
  have ha2 : a.symm (Finsupp.single (2:Fin 3) 1) = I.interpretation.basis .sphere 12 135 2 := ha 2
  obtain ⟨g,hg⟩ := I.basis ⟨.sphere,14,136,["0,1,407,1"]⟩ (by
    exact List.mem_of_getElem? (i := 214) (by rfl))
  change E.Page 2 (14,136) ≃ₗ[ℤ] (Fin 1 →₀ F2) at g
  change ∀ i : Fin 1, g.symm (Finsupp.single i 1) = I.interpretation.basis .sphere 14 136 i.val at hg
  have hg0 : g.symm (Finsupp.single (0:Fin 1) 1) = I.interpretation.basis .sphere 14 136 0 := hg 0
  have rep2 {p : ℤ×ℤ} (x : E.Page 2 p) : RepresentsOnPage E 2 p x x := by
    haveI : Epi ((E.ssData p).pageπ 0) := inferInstanceAs (Epi (cokernel.π _))
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective ((E.ssData p).pageπ 0)).mp inferInstance x
    exact ⟨by decide,z,by simp only [Subobject.ofLE_refl,Category.id_comp]; rfl,rfl⟩
  have incoming : E.d 2 (12,135)=0 := by
    have z0 := differential_target_later_zero (E:=E) (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h297
    have z12 := differential_target_later_zero (E:=E) (by change (2:ℤ)≤3;omega) (by decide : (3:ℤ)<6) h298
    have z2 := differential_target_later_zero (E:=E) (by change (2:ℤ)≤5;omega) (by decide : (5:ℤ)<6) h299
    have z1 : RepresentsOnPage E 6 (12,135) (I.interpretation.basis .sphere 12 135 1) 0 := by
      simpa only [add_sub_cancel_right,sub_self] using represents_sub_tail (E:=E) z12 z2
    have hd (i : Fin 3) : E.d 2 (12,135) (a.symm (Finsupp.single i 1))=0 := by
      rw [ha i]
      fin_cases i
      · exact represents_d_zero_of_later (E:=E) (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z0⟩
      · exact represents_d_zero_of_later (E:=E) (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z1⟩
      · exact represents_d_zero_of_later (E:=E) (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z2⟩
    ext x
    exact stem123_weight130_finite_quotients_basis_mem_submodule a (LinearMap.ker (E.d 2 (12,135)).hom) hd x
  have hnA : HasNonzeroDifferential E 3 (11,134) (14,136)
      (I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3) (I.interpretation.basis .sphere 14 136 0) := by
    obtain ⟨hdeg,a3,b3,ha3,hb3,hd3⟩ := h272
    refine ⟨hdeg,a3,b3,ha3,hb3,hd3,?_⟩
    apply represents_next_nonzero_of_incoming_zero_at (E:=E) (r:=2) (p:=(14,136))
      (by change (2:ℤ)≤2;omega) (by decide) incoming hb3 (rep2 _)
    intro hh
    rw [show I.interpretation.basis .sphere 14 136 0=g.symm (Finsupp.single 0 1) from (hg 0).symm] at hh
    have h := congrArg (fun x=>g x 0) hh
    norm_num [Finsupp.single_apply] at h
  let B := boundaries H SphereSpectrum 5 (11,134)
  let C := cycles H SphereSpectrum 7 (11,134)
  have z2 : RepresentsOnPage E 6 (11,134) (I.interpretation.basis .sphere 11 134 2) 0 :=
    differential_target_later_zero (E:=E) (by change (2:ℤ)≤5;omega) (by decide) h270
  have z4 : RepresentsOnPage E 6 (11,134) (I.interpretation.basis .sphere 11 134 4) 0 :=
    differential_target_later_zero (E:=E) (by change (2:ℤ)≤2;omega) (by decide) h269
  have b2 : I.interpretation.basis .sphere 11 134 2∈B := stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=6) (p:=(11,134)) z2
  have b4 : I.interpretation.basis .sphere 11 134 4∈B := stem123_weight130_finite_quotients_boundary_of_zero_representative  (r:=6) (p:=(11,134)) z4
  have c2 : I.interpretation.basis .sphere 11 134 2∈C := boundaries_le_cycles H SphereSpectrum (11,134) 5 7 b2
  have c4 : I.interpretation.basis .sphere 11 134 4∈C := boundaries_le_cycles H SphereSpectrum (11,134) 5 7 b4
  have badA : I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3∉C :=
    stem123_weight130_finite_quotients_nonzero_differential_not_cycle  (p:=(11,134)) (c:=7) (by decide) (by decide) hnA
  have badW : I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3∉C :=
    stem123_weight130_finite_quotients_nonzero_differential_not_cycle  (p:=(11,134)) (c:=7) (by decide) (by decide) h7
  have bad0 : I.interpretation.basis .sphere 11 134 0∉C := by
    intro hx
    apply stem123_weight130_finite_quotients_nonzero_differential_not_cycle  (p:=(11,134)) (c:=3) (by decide) (by decide) hnA
    obtain ⟨_,a7,_,ha7,_,_,_⟩ := h7
    have hw := (isCycle_iff_represents H SphereSpectrum 7 (by decide) (11,134) _).mpr ⟨a7,ha7⟩
    have hw3 := cycles_antitone H SphereSpectrum (11,134) (by decide : (3:ℤ)≤7-1) hw.2
    have hx3 := cycles_antitone H SphereSpectrum (11,134) (by decide : (3:ℤ)≤7) hx
    have hh := (cycles H SphereSpectrum 3 (11,134)).sub_mem hw3 hx3
    convert hh using 1; first | rfl | abel
  have hd3 : E.d 2 (11,134) (I.interpretation.basis .sphere 11 134 3)=I.interpretation.basis .sphere 13 135 2 := h273.eq_on_page_two.2
  have hdA : E.d 2 (11,134) (I.interpretation.basis .sphere 11 134 1)+E.d 2 (11,134) (I.interpretation.basis .sphere 11 134 3)=0 := by
    obtain ⟨_,a3,_,ha3,_,_⟩ := h272
    simpa only [map_add] using represents_d_zero_of_later (E:=E) (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<3) (rep2 _) ⟨a3,ha3⟩
  have hd1 : E.d 2 (11,134) (I.interpretation.basis .sphere 11 134 1)= -I.interpretation.basis .sphere 13 135 2 := by
    rw [hd3] at hdA
    exact eq_neg_of_add_eq_zero_left hdA
  have hd0 : E.d 2 (11,134) (I.interpretation.basis .sphere 11 134 0)=0 := by
    obtain ⟨_,a7,_,ha7,_,_,_⟩ := h7
    have hd := represents_d_zero_of_later (E:=E) (by change (2:ℤ)≤2;omega) (by decide : (2:ℤ)<7) (rep2 _) ⟨a7,ha7⟩
    simpa only [map_add,add_assoc,hdA,add_zero] using hd
  have hd2 : E.d 2 (11,134) (I.interpretation.basis .sphere 11 134 2)=0 := represents_d_zero_of_later (E:=E)
    (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z2⟩
  have hd4 : E.d 2 (11,134) (I.interpretation.basis .sphere 11 134 4)=0 := represents_d_zero_of_later (E:=E)
    (by change (2:ℤ)≤2;omega) (by decide) (rep2 _) ⟨0,z4⟩
  have ne : I.interpretation.basis .sphere 13 135 2≠0 := by
    intro hh
    rw [show I.interpretation.basis .sphere 13 135 2=f.symm (Finsupp.single 2 1) from (hf 2).symm] at hh
    have h := congrArg (fun x=>f x 2) hh
    norm_num [Finsupp.single_apply] at h
  apply stem123_weight130_finite_quotients_cycle_quotient_zero_of_le
  intro x hx
  have hd : E.d 2 (11,134) x=0 := stem123_weight130_finite_quotients_cycle_differential_zero  (r:=2) (c:=7) (p:=(11,134)) (x:=x) (by decide) (by decide) hx (rep2 x)
  have heq : e x=Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4) := by
    ext i
    fin_cases i <;> simp
  have hxe : x=e.symm (Finsupp.single 0 (e x 0)+Finsupp.single 1 (e x 1)+Finsupp.single 2 (e x 2)+Finsupp.single 3 (e x 3)+Finsupp.single 4 (e x 4)) := by
    rw [←heq,LinearEquiv.symm_apply_apply]
  generalize hc0 : e x 0=v0 at hxe
  generalize hc1 : e x 1=v1 at hxe
  generalize hc2 : e x 2=v2 at hxe
  generalize hc3 : e x 3=v3 at hxe
  generalize hc4 : e x 4=v4 at hxe
  fin_cases v0 <;> fin_cases v1 <;> fin_cases v2 <;> fin_cases v3 <;> fin_cases v4
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,map_zero,add_zero] at hxe
    rw [hxe]
    exact B.zero_mem
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [Finsupp.single_zero,he4,add_zero,zero_add] at hxe
    rw [hxe]
    exact b4
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [hd3] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd3,hd4,add_zero] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he2,add_zero,zero_add] at hxe
    rw [hxe]
    exact b2
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he2,he4,add_zero,zero_add] at hxe
    rw [hxe]
    exact B.add_mem b2 b4
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he2,he3,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd2,hd3,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he2,he3,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he1,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [hd1] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd4,add_zero] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he3,add_zero,zero_add] at hxe
    exfalso
    apply badA
    have hh := C.sub_mem hx (C.zero_mem)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3)-(0) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3) := by abel
    change ((I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3)-(0) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he3,he4,add_zero,zero_add] at hxe
    exfalso
    apply badA
    have hh := C.sub_mem hx (c4)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3) := by abel
    change ((I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2,add_zero] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,he4,add_zero,zero_add] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd1,hd2,hd4,add_zero] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,he3,add_zero,zero_add] at hxe
    exfalso
    apply badA
    have hh := C.sub_mem hx (c2)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 3)-(I.interpretation.basis .sphere 11 134 2) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3) := by abel
    change ((I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 3)-(I.interpretation.basis .sphere 11 134 2) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (0:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he1,he2,he3,he4,zero_add] at hxe
    exfalso
    apply badA
    have hh := C.sub_mem hx (C.add_mem c2 c4)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 3+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3) := by abel
    change ((I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 3+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [Finsupp.single_zero,he0,add_zero] at hxe
    exfalso
    apply bad0
    have hh := C.sub_mem hx (C.zero_mem)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 0)-(0) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 0) := by abel
    change ((I.interpretation.basis .sphere 11 134 0)-(0) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he4,add_zero] at hxe
    exfalso
    apply bad0
    have hh := C.sub_mem hx (c4)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 0) := by abel
    change ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he3,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd3,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he3,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,add_zero] at hxe
    exfalso
    apply bad0
    have hh := C.sub_mem hx (c2)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 2)-(I.interpretation.basis .sphere 11 134 2) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 0) := by abel
    change ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 2)-(I.interpretation.basis .sphere 11 134 2) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,he4,add_zero] at hxe
    exfalso
    apply bad0
    have hh := C.sub_mem hx (C.add_mem c2 c4)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 0) := by abel
    change ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,he3,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,hd3,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (0:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he2,he3,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd2,hd3,hd4,add_zero,zero_add] at hd
    exact ne hd
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd4,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he3,add_zero] at hxe
    exfalso
    apply badW
    have hh := C.sub_mem hx (C.zero_mem)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3)-(0) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3) := by abel
    change ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3)-(0) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (0:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he3,he4,add_zero] at hxe
    exfalso
    apply badW
    have hh := C.sub_mem hx (c4)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3) := by abel
    change ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he2,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (0:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he2,he4,add_zero] at hxe
    exfalso
    rw [hxe] at hd
    simp only [map_add,hd0,hd1,hd2,hd4,add_zero,zero_add] at hd
    exact ne (neg_eq_zero.mp hd)
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (0:F2)) at hxe
    simp only [map_add,Finsupp.single_zero,he0,he1,he2,he3,add_zero] at hxe
    exfalso
    apply badW
    have hh := C.sub_mem hx (c2)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 3)-(I.interpretation.basis .sphere 11 134 2) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3) := by abel
    change ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 3)-(I.interpretation.basis .sphere 11 134 2) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh
  · change x=e.symm (Finsupp.single 0 (1:F2)+Finsupp.single 1 (1:F2)+Finsupp.single 2 (1:F2)+Finsupp.single 3 (1:F2)+Finsupp.single 4 (1:F2)) at hxe
    simp only [map_add,he0,he1,he2,he3,he4] at hxe
    exfalso
    apply badW
    have hh := C.sub_mem hx (C.add_mem c2 c4)
    rw [hxe] at hh
    have cancel : ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 3+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))=(I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 3) := by abel
    change ((I.interpretation.basis .sphere 11 134 0+I.interpretation.basis .sphere 11 134 1+I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 3+I.interpretation.basis .sphere 11 134 4)-(I.interpretation.basis .sphere 11 134 2+I.interpretation.basis .sphere 11 134 4) : E.Page 2 (11,134))∈C at hh
    rw [cancel] at hh
    exact hh

private theorem stem123_weight130_finite_quotients (I : KIP126.Computation.SphereAndCofiber.AdamsComputationTheorems D' L' G) :
    ∀ s : ℤ, 10≤s → s≤16 → Subsingleton
      (CycleQuotient H SphereSpectrum (18-s) (s-6) (s,s+123)) := by
  classical
  intro s hs hs'
  obtain ⟨p12,p13,p14,d7,d3⟩ := stem123_filtration_bounds I
  interval_cases s
  · exact stem123_weight130_finite_quotients_stem123_af10_quotient I
  · exact stem123_weight130_finite_quotients_stem123_af11_quotient I d7
  · exact stem123_weight130_finite_quotients_cycle_quotient_zero_of_page 6 6 6 (12,135) (by decide) (by decide) (by decide) p12
  · exact stem123_weight130_finite_quotients_cycle_quotient_zero_of_page 4 5 7 (13,136) (by decide) (by decide) (by decide) p13
  · exact stem123_weight130_finite_quotients_cycle_quotient_zero_of_page 4 4 8 (14,137) (by decide) (by decide) (by decide) p14
  · exact stem123_weight130_finite_quotients_stem123_af15_quotient I d3
  · exact stem123_weight130_finite_quotients_stem123_af16_quotient I
end AlphaH0FiniteWindow

end
end KIP126.Main.SectionSeven
