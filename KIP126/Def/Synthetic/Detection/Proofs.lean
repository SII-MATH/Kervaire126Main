module

public import KIP126.Def.Synthetic.Detection.Predicates
public import KIP126.Def.SpectralSequence.Permanence.Proofs

@[expose] public section

/-! Associated-graded consequences for the same actual tower filtration.
The quotient-zero criterion keeps all higher-filtration indeterminacy. -/
namespace KIP126.Synthetic.SpectralSequence
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.SpectralSequence
universe u v

/-- Zero has a common zero representative on every meaningful page. -/
theorem HasInfinityRepresentative.zero (A : SyntheticAdamsSS.{v})
    (r : ℤ) (hr : 2 ≤ r) (i : Tridegree) :
    HasInfinityRepresentative A r i 0 0 :=
  ⟨hr, 0, map_zero _, map_zero _⟩

/-- A fixed finite-page label determines at most one infinity-page class.
The chosen cycle representatives themselves need not be unique. -/
theorem HasInfinityRepresentative.unique {A : SyntheticAdamsSS.{v}}
    {r : ℤ} {i : Tridegree} {x : A.Page r i}
    {e e' : (A.sequence.ssData i).eInfty}
    (h : HasInfinityRepresentative A r i x e)
    (h' : HasInfinityRepresentative A r i x e') : e = e' := by
  obtain ⟨_, z, hz, he⟩ := h
  obtain ⟨_, z', hz', he'⟩ := h'
  exact he.symm.trans
    (((A.sequence.ssData i).infinity_projection_eq_of_page_projection_eq
      (↑(r - 2).toNat) z z' (hz.trans hz'.symm)).trans he')

variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {F : SyntheticAdamsFamily Syn} {X : Syn}
  (c : TowerConvergence unit F X) (i : Tridegree)

set_option backward.isDefEq.respectTransparency false in
/-- Addition is taken in the actual homotopy group and in the same E₂
page. Its compatibility only asserts equality of associated-graded terms. -/
theorem detects_add
    {x y : (F.obj X).E₂ i} {a b : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a) (hb : Detects c i y b) :
    Detects c i (x+y) (a+b) := by
  obtain ⟨e, ⟨hr, z, hz, he⟩, a', ha', hga⟩ := ha
  obtain ⟨e', ⟨_, z', hz', he'⟩, b', hb', hgb⟩ := hb
  refine ⟨e + e', ⟨hr, z + z', ?_, ?_⟩, a' + b', ?_, ?_⟩
  · rw [map_add, hz, hz']
  · rw [map_add, he, he']
  · rw [map_add, ha', hb']
  · rw [map_add, map_add, hga, hgb]

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing of the actual associated-graded class means membership in
one higher actual tower filtration, by the defining quotient. -/
private theorem filtrationAtLeast_of_graded_eq_zero (s m w : ℤ)
    (a : (Subobject.underlying.obj
      ((towerFiltration unit X).F s (m, w)) : ModuleCat ℤ))
    (ha : (towerFiltration unit X).toAssociatedGraded s (m, w) a = 0) :
    FiltrationAtLeast unit (s + 1) (((towerFiltration unit X).F s (m, w)).arrow a) := by
  have hmem := (subobject_cokernel_π_eq_zero_iff
    ((towerFiltration unit X).F (s + 1) (m, w))
    ((towerFiltration unit X).F s (m, w))
    ((towerFiltration unit X).mono s (m, w)) a).mp ha
  change _ ∈ towerFiltrationSubmodule unit X (s + 1) (m, w)
  simpa only [towerFiltration, OrderIso.apply_symm_apply] using hmem

/-- A label representing zero at infinity detects a class one filtration
higher. Nonzero E2 is deliberately irrelevant to this implication. -/
theorem detects_zero_infinity_filtration
    {x : (F.obj X).E₂ i} {a : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a)
    (hx : HasInfinityRepresentative (F.obj X) 2 i x 0) :
    FiltrationAtLeast unit (i.1+1) a := by
  obtain ⟨e, he, a', ha', hgr⟩ := ha
  have he0 := he.unique hx
  rw [he0, map_zero] at hgr
  rw [← ha']
  exact filtrationAtLeast_of_graded_eq_zero i.1 (i.2.1-i.1) i.2.2 a' hgr.symm

/-- A zero leading E₂ class detects only a higher-filtration class, not
necessarily the zero homotopy class. -/
theorem detects_zero_filtration
    {a : BiHom (i.2.1-i.1) i.2.2 X} (ha : Detects c i 0 a) :
    FiltrationAtLeast unit (i.1+1) a :=
  detects_zero_infinity_filtration c i ha
    (HasInfinityRepresentative.zero (F.obj X) 2 (by omega) i)

set_option backward.isDefEq.respectTransparency false in
/-- Equality of leading terms fixes only the associated graded: two
representatives differ by one higher step of the SAME actual filtration. -/
theorem detects_sub_filtration
    {x : (F.obj X).E₂ i}
    {a b : BiHom (i.2.1-i.1) i.2.2 X}
    (ha : Detects c i x a) (hb : Detects c i x b) :
    FiltrationAtLeast unit (i.1+1) (a-b) := by
  obtain ⟨e, he, a', ha', hga⟩ := ha
  obtain ⟨e', he', b', hb', hgb⟩ := hb
  have heq := he.unique he'
  have hzero : (towerFiltration unit X).toAssociatedGraded
      i.1 (i.2.1-i.1, i.2.2) (a' - b') = 0 := by
    rw [map_sub, ← hga, ← hgb, heq, sub_self]
  have h := filtrationAtLeast_of_graded_eq_zero
    i.1 (i.2.1-i.1) i.2.2 (a' - b') hzero
  simpa only [map_sub, ha', hb'] using h

end KIP126.Synthetic.SpectralSequence
