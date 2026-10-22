module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.HomotopyEquivalence.Proofs
import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.MappingCylinder.Diagram.Contraction.Proofs

@[expose] section

namespace KIP126.Topology.HomotopyExtension
open CategoryTheory CategoryTheory.Limits Set _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- A homotopy whose restriction traverses a specified path and its reverse
can be made stationary on a closed homotopy-extension subspace. -/
theorem HasHomotopyExtension.homotopicRel_of_canceling_restriction
    {A B Y : TopCat.{u}} {i : A ⟶ B} (hi : HasHomotopyExtension i)
    (he : IsClosedEmbedding i) {f g : C(B,Y)} {k : C(A,Y)}
    (L : (f.comp i.hom).Homotopy k) (K : f.Homotopy g)
    (hK : ∀ t a, K (t,i a) = (L.trans L.symm) (t,a)) :
    f.HomotopicRel g (Set.range i) := by
  let γ (a : A) : Path (f (i a)) (k a) := {
    toFun := fun t => L (t,a)
    continuous_toFun := L.continuous.comp (continuous_id.prodMk continuous_const)
    source' := L.apply_zero a
    target' := L.apply_one a }
  let p : C((A × I) × I,Y) := ⟨fun z =>
    (Path.Homotopy.reflTransSymm (γ z.1.1)).symm (z.2,z.1.2),by
      change Continuous (fun z : (A × I) × I =>
        L (⟨Path.Homotopy.reflTransSymmAux (unitInterval.symm z.2,z.1.2),_⟩,z.1.1))
      fun_prop⟩
  have hp (a : A) (t : I) : p ((a,t),0) = K (t,i a) := by
    change (Path.Homotopy.reflTransSymm (γ a)).symm (0,t) = _
    rw [(Path.Homotopy.reflTransSymm (γ a)).symm.apply_zero,hK]
    change (γ a |>.trans (γ a).symm) t = _
    rw [Path.trans_apply,ContinuousMap.Homotopy.trans_apply]
    split_ifs <;> rfl
  have hfg (a : A) : f (i a) = g (i a) := by
    calc
      f (i a) = p ((a,1),0) := ((Path.Homotopy.reflTransSymm (γ a)).symm.eval 0).target.symm
      _ = K (1,i a) := hp a 1
      _ = g (i a) := K.apply_one (i a)
  obtain ⟨Q,hQ,hQa,hQ0,hQ1⟩ := hi.exists_endpoint_extension he Y
    (K.toContinuousMap.comp ContinuousMap.prodSwap) p hp
    (fun a s => ((Path.Homotopy.reflTransSymm (γ a)).symm.eval s).source.trans
      (K.apply_zero (i a)).symm)
    (fun a s => ((Path.Homotopy.reflTransSymm (γ a)).symm.eval s).target.trans
      ((hfg a).trans (K.apply_one (i a)).symm))
  let T : f.Homotopy g := {
    toContinuousMap := Q.comp ⟨fun z => ((z.2,z.1),1),
      (continuous_snd.prodMk continuous_fst).prodMk continuous_const⟩
    map_zero_left := fun b => (hQ0 b 1).trans (K.apply_zero b)
    map_one_left := fun b => (hQ1 b 1).trans (K.apply_one b) }
  refine ⟨{ toHomotopy := T, prop' := ?_ }⟩
  rintro t _ ⟨a,rfl⟩
  exact (hQa a t 1).trans ((Path.Homotopy.reflTransSymm (γ a)).symm.apply_one t)

/-- A fiber-preserving deformation retraction rectifies to an equivalence
under any specified closed HEP subspace of its source and HEP subspace of its target. -/
theorem exists_relative_inverse_of_fiber_deformation
    {S M B : TopCat.{u}} (jM : S ⟶ M) (jB : S ⟶ B)
    (hM : HasHomotopyExtension jM) (hcM : IsClosedEmbedding jM)
    (hB : HasHomotopyExtension jB) (p : C(M,B)) (s : C(B,M))
    (hps : p.comp s = ContinuousMap.id B)
    (hpj : ∀ z, p (jM z) = jB z)
    (H : (ContinuousMap.id M).Homotopy (s.comp p))
    (hH : ∀ t x, p (H (t,x)) = p x) :
    ∃ r : C(B,M), (∀ z, r (jB z) = jM z) ∧
      (r.comp p).HomotopicRel (ContinuousMap.id M) (Set.range jM) ∧
      (p.comp r).HomotopicRel (ContinuousMap.id B) (Set.range jB) := by
  let q : C(S × I,M) := H.symm.toContinuousMap.comp
    ⟨fun z => (z.2,jM z.1),continuous_snd.prodMk (jM.hom.continuous.comp continuous_fst)⟩
  obtain ⟨Q,hQ,hQj⟩ := hB M s q (fun z => by
    change H.symm (0,jM z) = s (jB z)
    rw [H.symm.apply_zero]
    exact congrArg s (hpj z))
  let r : C(B,M) := Q.comp ((ContinuousMap.id B).prodMk (ContinuousMap.const B 1))
  have hr (z : S) : r (jB z) = jM z := by
    exact (hQj z 1).trans (H.symm.apply_one (jM z))
  let E : s.Homotopy r := {
    toContinuousMap := Q.comp ContinuousMap.prodSwap
    map_zero_left := hQ
    map_one_left := fun _ => rfl }
  have hE (t : I) (z : S) : E (t,jB z) = H.symm (t,jM z) := hQj z t
  let L := H.compContinuousMap jM.hom
  let K := H.trans (E.compContinuousMap p)
  have hK (t : I) (z : S) : K (t,jM z) = (L.trans L.symm) (t,z) := by
    dsimp only [K]
    rw [ContinuousMap.Homotopy.trans_apply,ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · rfl
    · change E (_,p (jM z)) = H.symm (_,jM z)
      rw [hpj,hE]
  have hleft := (hM.homotopicRel_of_canceling_restriction hcM L K hK).symm
  let R : (ContinuousMap.id B).Homotopy (p.comp r) :=
    ((ContinuousMap.Homotopy.refl p).comp E).cast hps rfl
  have hright : (ContinuousMap.id B).HomotopicRel (p.comp r) (Set.range jB) := by
    refine ⟨{ toHomotopy := R, prop' := ?_ }⟩
    rintro t _ ⟨z,rfl⟩
    change p (E (t,jB z)) = jB z
    rw [hE]
    exact (hH (unitInterval.symm t) (jM z)).trans (hpj z)
  exact ⟨r,hr,hleft,hright.symm⟩

/-- An actual homotopy equivalence under closed HEP subspaces admits an
inverse under the same subspace and both actual relative homotopies. -/
theorem exists_relative_inverse_of_homotopyEquiv
    {S A B : TopCat.{u}} (jA : S ⟶ A) (jB : S ⟶ B)
    (hA : HasHomotopyExtension jA) (hcA : IsClosedEmbedding jA)
    (hB : HasHomotopyExtension jB) (f : A ⟶ B)
    (hf : jA ≫ f = jB) (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = f.hom) :
    ∃ g : C(B,A), (∀ z, g (jB z) = jA z) ∧
      (g.comp f.hom).HomotopicRel (ContinuousMap.id A) (Set.range jA) ∧
      (f.hom.comp g).HomotopicRel (ContinuousMap.id B) (Set.range jB) := by
  let F : ℕ ⥤ TopCat.{u} := (Functor.const ℕ).obj A
  let G : ℕ ⥤ TopCat.{u} := (Functor.const ℕ).obj B
  let η : F ⟶ G := (Functor.const ℕ).map f
  let M := (MappingCylinder.diagram η).obj 0
  let i : A ⟶ M := (MappingCylinder.sourceInclusion η).app 0
  let p : M ⟶ B := (MappingCylinder.projection η).app 0
  let s : B ⟶ M := (MappingCylinder.targetInclusion η).app 0
  obtain ⟨HH,hsrc,htgt,hcyl,_⟩ := MappingCylinder.exists_natural_contraction η
  let H := HH 0
  have hpi (x : A) : p (i x) = f x := MappingCylinder.projection_vertex η 0 (Sum.inl x)
  have hps (x : B) : p (s x) = x := MappingCylinder.projection_vertex η 0 (Sum.inr x)
  have hpsCM : p.hom.comp s.hom = ContinuousMap.id B := by ext x; exact hps x
  have hfiber (t : I) (x : M) : p (H (t,x)) = p x := by
    obtain ⟨z,rfl⟩ | ⟨⟨a,v⟩,rfl⟩ := Types.eq_or_eq_of_isPushout
      ((MappingCylinder.diagram_isPushout η 0).map (forget TopCat)) x
    · cases z with
      | inl a =>
        change p (HH 0 (t,(MappingCylinder.sourceInclusion η).app 0 a)) = p (i a)
        rw [hsrc]
        exact (MappingCylinder.projection_cylinder η 0 a t).trans (hpi a).symm
      | inr b =>
        change p (HH 0 (t,(MappingCylinder.targetInclusion η).app 0 b)) = p (s b)
        rw [htgt]
        rfl
    · change p (HH 0 (t,(MappingCylinder.cylinderInclusion η).app 0 (a,v))) =
        p ((MappingCylinder.cylinderInclusion η).app 0 (a,v))
      rw [hcyl]
      exact (MappingCylinder.projection_cylinder η 0 a _).trans
        (MappingCylinder.projection_cylinder η 0 a v).symm
  let ep : ContinuousMap.HomotopyEquiv M B := {
    toFun := p.hom
    invFun := s.hom
    left_inv := ⟨H.symm⟩
    right_inv := by rw [hpsCM] }
  let ei' := e.trans ep.symm
  have hif : i.hom.Homotopic ei'.toFun := by
    have hh : (s.hom.comp p.hom).comp i.hom = ei'.toFun := by
      ext x
      change s (p (i x)) = s (e.toFun x)
      rw [hpi,he]
    exact ⟨(H.compContinuousMap i.hom).cast rfl hh⟩
  let ei : ContinuousMap.HomotopyEquiv A M := {
    toFun := i.hom
    invFun := ei'.invFun
    left_inv := ((ContinuousMap.Homotopic.refl ei'.invFun).comp hif).trans ei'.left_inv
    right_inv := (hif.comp (ContinuousMap.Homotopic.refl ei'.invFun)).trans ei'.right_inv }
  have hi : HasHomotopyExtension i := MappingCylinder.sourceInclusion_hasHomotopyExtension η 0
  have hci : IsClosedEmbedding i := MappingCylinder.sourceInclusion_isClosedEmbedding η 0
  obtain ⟨r,hri,J,hJ⟩ := hi.exists_strong_deformation_retraction hci ei rfl
  have hriv (x : A) : r (i x) = x := ContinuousMap.congr_fun hri x
  have hfj (z : S) : f (jA z) = jB z := ConcreteCategory.congr_hom hf z
  obtain ⟨v,hvj,⟨L⟩,⟨R⟩⟩ := exists_relative_inverse_of_fiber_deformation
    (jA ≫ i) jB (hA.comp hi) (hci.comp hcA) hB p.hom s.hom hpsCM
    (fun z => (hpi (jA z)).trans (hfj z)) H hfiber
  let g := r.comp v
  have hgj (z : S) : g (jB z) = jA z := by
    change r (v (jB z)) = jA z
    rw [hvj]
    exact hriv (jA z)
  have hl0 : r.comp ((v.comp p.hom).comp i.hom) = g.comp f.hom := by
    ext x
    change r (v (p (i x))) = r (v (f x))
    rw [hpi]
  let L' : (g.comp f.hom).Homotopy (ContinuousMap.id A) :=
    ((ContinuousMap.Homotopy.refl r).comp (L.toHomotopy.compContinuousMap i.hom)).cast hl0 hri
  have hleft : (g.comp f.hom).HomotopicRel (ContinuousMap.id A) (Set.range jA) := by
    refine ⟨{ toHomotopy := L', prop' := ?_ }⟩
    rintro t _ ⟨z,rfl⟩
    change r (L (t,i (jA z))) = g (f (jA z))
    have hL : L (t,i (jA z)) = i (jA z) := L.eq_snd t (Set.mem_range_self z)
    rw [hL]
    change r (i (jA z)) = g (f (jA z))
    rw [hriv,hfj,hgj]
  have hr0 : p.hom.comp ((i.hom.comp r).comp v) = f.hom.comp g := by
    ext x
    exact hpi (r (v x))
  let T : (f.hom.comp g).Homotopy (p.hom.comp v) :=
    ((ContinuousMap.Homotopy.refl p.hom).comp (J.symm.compContinuousMap v)).cast hr0 rfl
  have hT : (f.hom.comp g).HomotopicRel (p.hom.comp v) (Set.range jB) := by
    refine ⟨{ toHomotopy := T, prop' := ?_ }⟩
    rintro t _ ⟨z,rfl⟩
    change p (J.symm (t,v (jB z))) = f (g (jB z))
    rw [hvj]
    change p (J (unitInterval.symm t,i (jA z))) = f (g (jB z))
    rw [hJ,hpi,hgj]
  exact ⟨g,hgj,hleft,hT.trans ⟨R⟩⟩

end KIP126.Topology.HomotopyExtension

