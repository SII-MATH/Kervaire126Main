module

public import KIP126.Def.Topology.Pushout.Collar.Coproduct.Data
public import KIP126.Def.Topology.Pushout.Collar.Proofs
public import Mathlib.Topology.Category.TopCat.Limits.Products

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- An actual boundary retraction on an open neighborhood transports
along a homeomorphism of the boundary inclusion. -/
theorem exists_open_boundary_retraction_of_homeomorph
    {S A S' A' : Type*} [TopologicalSpace S] [TopologicalSpace A]
    [TopologicalSpace S'] [TopologicalSpace A'] (i : C(S, A)) (i' : C(S', A'))
    (eS : S ≃ₜ S') (eA : A ≃ₜ A') (hi : ∀ s, eA (i s) = i' (eS s))
    (W : Set A') (hW : IsOpen W) (hiW : ∀ s, i' s ∈ W)
    (r : C(W, S')) (hri : ∀ s, r ⟨i' s, hiW s⟩ = s) :
    ∃ V : Set A, ∃ _ : IsOpen V, ∃ hiV : ∀ s, i s ∈ V,
      ∃ q : C(V, S), ∀ s, q ⟨i s, hiV s⟩ = s := by
  let V := eA ⁻¹' W
  have hiV (s : S) : i s ∈ V := by change eA (i s) ∈ W; rw [hi]; exact hiW _
  let q : C(V, S) := ⟨fun x => eS.symm (r ⟨eA x.val, x.property⟩),
    eS.symm.continuous.comp (r.continuous.comp
      ((eA.continuous.comp continuous_subtype_val).subtype_mk _))⟩
  refine ⟨V, hW.preimage eA.continuous, hiV, q, ?_⟩
  intro s
  change eS.symm (r ⟨eA (i s), hiV s⟩) = s
  have hz : (⟨eA (i s), hiV s⟩ : W) = ⟨i' (eS s), hiW (eS s)⟩ :=
    Subtype.ext (hi s)
  rw [hz, hri, Homeomorph.symm_apply_apply]

/-- Open boundary neighborhoods and their retractions assemble across
any actual topological coproduct, preserving the full boundary map. -/
theorem exists_coproduct_open_boundary_retraction
    {ι : Type u} {S A : ι → TopCat.{u}} (i : ∀ k, S k ⟶ A k)
    (cS : Cofan S) (cA : Cofan A) (hS : IsColimit cS) (hA : IsColimit cA)
    (m : cS.pt ⟶ cA.pt) (hm : ∀ k, cS.inj k ≫ m = i k ≫ cA.inj k)
    (W : ∀ k, Set (A k)) (hW : ∀ k, IsOpen (W k)) (hiW : ∀ k s, i k s ∈ W k)
    (r : ∀ k, C(W k, S k)) (hri : ∀ k s, r k ⟨i k s, hiW k s⟩ = s) :
    ∃ V : Set cA.pt, ∃ _ : IsOpen V, ∃ hmV : ∀ s, m s ∈ V,
      ∃ q : C(V, cS.pt), ∀ s, q ⟨m s, hmV s⟩ = s := by
  let sIso := hS.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit S)
  let aIso := hA.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit A)
  let eS := TopCat.homeoOfIso sIso
  let eA := TopCat.homeoOfIso aIso
  have hs (k : ι) (x : S k) : eS (cS.inj k x) = ⟨k, x⟩ :=
    ConcreteCategory.congr_hom (IsColimit.comp_coconePointUniqueUpToIso_hom hS
      (TopCat.sigmaCofanIsColimit S) (Discrete.mk k)) x
  have ha (k : ι) (x : A k) : eA (cA.inj k x) = ⟨k, x⟩ :=
    ConcreteCategory.congr_hom (IsColimit.comp_coconePointUniqueUpToIso_hom hA
      (TopCat.sigmaCofanIsColimit A) (Discrete.mk k)) x
  have hex (s : cS.pt) : ∃ k x, s = cS.inj k x := by
    refine ⟨(eS s).1, (eS s).2, eS.injective ?_⟩
    exact (hs _ _).symm
  have hm' (k : ι) (x : S k) : m (cS.inj k x) = cA.inj k (i k x) :=
    ConcreteCategory.congr_hom (hm k) x
  let Vsum : Set (Σ k, A k) := {x | x.2 ∈ W x.1}
  let V : Set cA.pt := eA ⁻¹' Vsum
  have hVsum : IsOpen Vsum := isOpen_sigma_iff.mpr (fun k => hW k)
  have hV : IsOpen V := hVsum.preimage eA.continuous
  have hmV (s : cS.pt) : m s ∈ V := by
    obtain ⟨k, x, rfl⟩ := hex s
    change (eA (m (cS.inj k x))).2 ∈ W (eA (m (cS.inj k x))).1
    rw [hm', ha]
    exact hiW k x
  let qsum : C((Σ k, W k), Σ k, S k) :=
    ⟨fun x => ⟨x.1, r x.1 x.2⟩,
      continuous_sigma (fun k => continuous_sigmaMk.comp (r k).continuous)⟩
  let eV : V ≃ₜ Vsum := eA.subtype (fun _ => Iff.rfl)
  let d := sigmaSubtypeHomeomorph (fun k => A k) W
  let q : C(V, cS.pt) :=
    ⟨fun x => eS.symm (qsum (d.symm (eV x))), eS.symm.continuous.comp
      (qsum.continuous.comp (d.symm.continuous.comp eV.continuous))⟩
  refine ⟨V, hV, hmV, q, ?_⟩
  intro s
  obtain ⟨k, x, rfl⟩ := hex s
  have hz : eV ⟨m (cS.inj k x), hmV (cS.inj k x)⟩ =
      d ⟨k, ⟨i k x, hiW k x⟩⟩ := by
    apply Subtype.ext
    exact (congrArg eA (hm' k x)).trans (ha k (i k x))
  change eS.symm (qsum (d.symm (eV ⟨m (cS.inj k x), hmV (cS.inj k x)⟩))) = _
  rw [hz, Homeomorph.symm_apply_apply]
  change eS.symm ⟨k, r k ⟨i k x, hiW k x⟩⟩ = _
  rw [hri]
  apply eS.injective
  rw [Homeomorph.apply_symm_apply, hs]

end KIP126.Topology
