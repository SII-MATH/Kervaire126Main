module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Free.Data
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.HomotopyFunctor.Proofs
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Representatives.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Spectra.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u

theorem freeStabilization_stableEquivalence (n : ℕ) (A : BasedSpace.{u}) :
    stableEquivalences (freeStabilization n A) := by
  induction n with
  | zero =>
    apply (stableEquivalence_iff_source_isIso _).mpr
    change IsIso (sourceLocalization.map (_ ≫ paddedTailInclusion (suspensionSpectrum A)))
    rw [Functor.map_comp]
    haveI := stableEquivalences.Q_inverts _ (paddedTailInclusion_stableEquivalence (suspensionSpectrum A))
    infer_instance
  | succ n ih =>
    apply (stableEquivalence_iff_source_isIso _).mpr
    change IsIso (sourceLocalization.map (_ ≫ desuspensionMap (freeStabilization n A) ≫ _))
    rw [Functor.map_comp,Functor.map_comp]
    haveI := stableEquivalences.Q_inverts _ (desuspensionMap_stableEquivalence _ ih)
    infer_instance

theorem free_level_next (n : ℕ) (A : BasedSpace.{u}) :
    (free n A).level (n+1) = A.suspension := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [free_succ]
    exact ih

theorem freeStabilization_evaluation (n : ℕ) (A : BasedSpace.{u}) :
    (evaluationFunctor (n+1)).map (freeStabilization n A) =
      eqToHom ((free_level (n+1) A.suspension).trans (free_level_next n A).symm) := by
  induction n with
  | zero =>
    change (evaluationFunctor 1).map
      (eqToHom _ ≫ paddedTailInclusion (suspensionSpectrum A)) = _
    rw [Functor.map_comp,eqToHom_map]
    change eqToHom _ ≫ 𝟙 _ = _
    rw [Category.comp_id]
    rfl
  | succ n ih =>
    change (evaluationFunctor (n+1+1)).map
      (eqToHom _ ≫ desuspensionMap (freeStabilization n A) ≫ eqToHom _) = _
    rw [Functor.map_comp,Functor.map_comp,eqToHom_map,eqToHom_map,
      evaluationFunctor_desuspensionMap,ih]
    change eqToHom _ ≫ eqToHom _ ≫ eqToHom _ = _
    simp only [eqToHom_trans]
    rfl

theorem freeEvaluation_id (n : ℕ) (A : BasedSpace.{u}) :
    freeEvaluation n A (free n A) (𝟙 _) = eqToHom (free_level n A).symm := by
  apply BasedSpace.Hom.ext
  have h := (freeEvaluation_exists n A (free n A)).choose_spec (𝟙 _)
  have hc (B : BasedSpace.{u}) (hB : B = A) :
      HEq (ContinuousMap.id B) (BasedSpace.Hom.map (eqToHom hB.symm)) := by
    subst B
    rfl
  exact eq_of_heq (h.trans (hc _ (free_level n A)))

theorem free_bond_at_generator (n : ℕ) (A : BasedSpace.{u}) :
    ∀ (h₀ : (free n A).level n = A) (h₁ : (free n A).level (n+1) = A.suspension)
      (a : A) (t : I),
      (free n A).bond n ((BasedSpace.Hom.map (eqToHom h₀.symm)) a,t) =
        (BasedSpace.Hom.map (eqToHom h₁.symm)) (A.suspensionProjection (a,t)) := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    rw [free_succ]
    exact ih

theorem freeStabilization_freeSphereLoop (n r : ℕ) (t : Fin (r+1) → I) :
    (freeStabilization n (sphereLevel r)).level (n+1) (freeSphereLoop (n+1) (r+1) t) =
      stabilizeLoop (free n (sphereLevel r)) n r (freeSphereLoop n r) t := by
  have hl : freeEvaluation (n+1) (sphereLevel r).suspension (free (n+1) (sphereLevel r).suspension) (𝟙 _) ≫
      (evaluationFunctor (n+1)).map (freeStabilization n (sphereLevel r)) =
        eqToHom (free_level_next n (sphereLevel r)).symm := by
    rw [freeEvaluation_id,freeStabilization_evaluation]
    change eqToHom _ ≫ eqToHom _ = _
    simp only [eqToHom_trans]
    rfl
  have hh := congrArg (fun f : sphereLevel (r+1) ⟶ (free n (sphereLevel r)).level (n+1) =>
    f.map (sphereCube (r+1) t)) hl
  have hh' : (freeStabilization n (sphereLevel r)).level (n+1) (freeSphereLoop (n+1) (r+1) t) =
      (BasedSpace.Hom.map (eqToHom (free_level_next n (sphereLevel r)).symm)) (sphereCube (r+1) t) := hh
  rw [hh']
  change _ = (free n (sphereLevel r)).bond n
    ((freeEvaluation n (sphereLevel r) (free n (sphereLevel r)) (𝟙 _)).map
      (sphereCube r (fun i => t i.succ)),t 0)
  rw [freeEvaluation_id,free_bond_at_generator n (sphereLevel r) (free_level n (sphereLevel r)) (free_level_next n (sphereLevel r))]
  rfl

end KIP126.StableHomotopy.Spectra.Prespectrum
