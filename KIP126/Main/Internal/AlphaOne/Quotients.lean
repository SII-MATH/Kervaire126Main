module
public import KIP126.Main.Conditions
import all KIP126.Main.Internal.Selected.NormalizedFacts
import all KIP126.Main.Internal.Choice.Filtration

/-! Original cycle and boundary quotient calculations transported to the equal
private page presentation (bbac1fc05843, MIT). -/
@[expose] section
namespace KIP126.Main.Internal.AlphaOne
open CategoryTheory CategoryTheory.Limits KIP126.Core.SpectralSequence
open KIP126.Main.Internal.Selected KIP126.Literature
open KIP126.AdamsSynthetic.Standard (model)
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def cycleMapFor (E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
    (hr : E.r₀=2) (n : WithTop ℕ) (p : ℤ×ℤ) :
    Subobject.underlying.obj ((E.ssData p).Z n) ⟶ E.Page 2 p :=
  Subobject.ofLE ((E.ssData p).Z n) ((E.ssData p).Z 0) ((E.ssData p).Z_anti bot_le) ≫
    (E.ssData p).pageπ 0 ≫ eqToHom (by simp only [Page,hr,sub_self,Int.toNat_zero,Nat.cast_zero])
private def boundaryMapFor (E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
    (hr : E.r₀=2) (n : WithTop ℕ) (p : ℤ×ℤ) :
    Subobject.underlying.obj ((E.ssData p).B n) ⟶ E.Page 2 p :=
  Subobject.ofLE ((E.ssData p).B n) ((E.ssData p).Z 0)
    (((E.ssData p).B_le_Z n).trans ((E.ssData p).Z_anti bot_le)) ≫
    (E.ssData p).pageπ 0 ≫ eqToHom (by simp only [Page,hr,sub_self,Int.toNat_zero,Nat.cast_zero])
private abbrev cycleMap := cycleMapFor Normalized.sphere rfl
private abbrev boundaryMap := boundaryMapFor Normalized.sphere rfl
private def cycles (c : ℤ) (p : ℤ×ℤ) := LinearMap.range (cycleMap (↑(c-1).toNat) p).hom
private def boundaries (b : ℤ) (p : ℤ×ℤ) := LinearMap.range (boundaryMap (↑(b-1).toNat) p).hom
private abbrev CycleQuotient (c b : ℤ) (p : ℤ×ℤ) := E2Subquotient (cycles c p) (boundaries b p)

private theorem quotient_vanishing_actual (c b : ℤ) (p : ℤ×ℤ)
    (hz : Subsingleton (CycleQuotient c b p)) :
    Subsingleton (KIP126.Literature.CycleQuotient model .sphere c b p) := by
  let Q (E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (hr : E.r₀=2) :=
    E2Subquotient (LinearMap.range (cycleMapFor E hr (↑(c-1).toNat) p).hom)
      (LinearMap.range (boundaryMapFor E hr (↑(b-1).toNat) p).hom)
  have transport (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
      (he : E=E') (hr : E.r₀=2) (hr' : E'.r₀=2) (h : Subsingleton (Q E hr)) :
      Subsingleton (Q E' hr') := by
    subst E'
    exact h
  exact transport _ _ (Normalized.sequence_eq .sphere) rfl (model.classical.firstPage _) hz

private theorem boundaries_monotone (p : ℤ×ℤ) : Monotone (fun b => boundaries b p) := by
  intro b b' h x hx
  obtain ⟨z,rfl⟩ := hx
  let E := Normalized.sphere.ssData p
  have hn : (↑(b-1).toNat : WithTop ℕ)≤↑(b'-1).toNat := by
    exact_mod_cast Int.toNat_le_toNat (by omega : b-1≤b'-1)
  refine ⟨(Subobject.ofLE _ _ (E.B_mono hn)) z,?_⟩
  change (Subobject.ofLE _ _ (E.B_mono hn) ≫ boundaryMap (↑(b'-1).toNat) p) z=_
  simp only [boundaryMap,boundaryMapFor,E,←Category.assoc,Subobject.ofLE_comp_ofLE]

private theorem cycles_reaches (c : ℤ) (p : ℤ×ℤ) (hc : 1≤c)
    (x : Normalized.sphere.Page 2 p) :
    x∈cycles c p ↔ ReachesPage Normalized.sphere (c+1) p x := by
  have hn : c+1-2=c-1 := by omega
  change (∃ z, cycleMap (↑(c-1).toNat) p z=x) ↔ _
  change (∃ z, cycleMap (↑(c-1).toNat) p z=x) ↔
    ∃ y : (Normalized.sphere.ssData p).page ↑(c+1-2).toNat,
      ∃ _ : 2≤c+1,
        ∃ z : (Subobject.underlying.obj ((Normalized.sphere.ssData p).Z ↑(c+1-2).toNat) : ModuleCat ℤ),
          (Subobject.ofLE ((Normalized.sphere.ssData p).Z ↑(c+1-2).toNat)
            ((Normalized.sphere.ssData p).Z 0) ((Normalized.sphere.ssData p).Z_anti bot_le) ≫
            (Normalized.sphere.ssData p).pageπ 0) z=x ∧
            (Normalized.sphere.ssData p).pageπ ↑(c+1-2).toNat z=y
  rw [hn]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨_,by omega,z,?_,rfl⟩
    change ((Subobject.ofLE ((Normalized.sphere.ssData p).Z ↑(c-1).toNat)
      ((Normalized.sphere.ssData p).Z 0) _) ≫ (Normalized.sphere.ssData p).pageπ 0 ≫ 𝟙 _) z=x at hz
    erw [Category.comp_id] at hz
    exact hz
  · rintro ⟨_,hr,z,hz,_⟩
    refine ⟨z,?_⟩
    change ((Subobject.ofLE ((Normalized.sphere.ssData p).Z ↑(c-1).toNat)
      ((Normalized.sphere.ssData p).Z 0) _) ≫ (Normalized.sphere.ssData p).pageπ 0 ≫ 𝟙 _) z=x
    erw [Category.comp_id]
    exact hz


private theorem cycles_antitone (p : ℤ×ℤ) : Antitone (fun c => cycles c p) := by
  intro c c' h x hx
  obtain ⟨z,rfl⟩ := hx
  let E := Normalized.sphere.ssData p
  have hn : (↑(c-1).toNat : WithTop ℕ)≤↑(c'-1).toNat := by
    exact_mod_cast Int.toNat_le_toNat (by omega : c-1≤c'-1)
  refine ⟨(Subobject.ofLE _ _ (E.Z_anti hn)) z,?_⟩
  change (Subobject.ofLE _ _ (E.Z_anti hn) ≫ cycleMap (↑(c-1).toNat) p) z=_
  simp only [cycleMap,cycleMapFor,E,←Category.assoc,Subobject.ofLE_comp_ofLE]

private theorem boundaries_le_cycles (p : ℤ×ℤ) (b c : ℤ) : boundaries b p≤cycles c p := by
  rintro x ⟨z,rfl⟩
  let E := Normalized.sphere.ssData p
  have h : E.B (↑(b-1).toNat)≤E.Z (↑(c-1).toNat) :=
    (E.B_mono le_top).trans ((E.B_le_Z ⊤).trans (E.Z_anti le_top))
  refine ⟨(Subobject.ofLE _ _ h) z,?_⟩
  change (Subobject.ofLE _ _ h ≫ cycleMap (↑(c-1).toNat) p) z=_
  simp only [cycleMap,cycleMapFor,boundaryMap,boundaryMapFor,E,
    ←Category.assoc,Subobject.ofLE_comp_ofLE]

private theorem quotient_subsingleton_of_le {c b : ℤ} {p : ℤ×ℤ}
    (h : cycles c p ≤ boundaries b p) : Subsingleton (CycleQuotient c b p) :=
  KIP126.Main.Internal.Choice.subquotient_subsingleton_of_le _ _ h

set_option maxHeartbeats 2000000 in
private theorem frame_actual (c b : ℤ) (p : ℤ×ℤ)
    (x : model.classical.sphere.Page 2 p)
    (h : ∃ z : cycles c p, z.val=Normalized.label p x ∧
      ∀ q : CycleQuotient c b p, q=0 ∨ q=subquotientClass (cycles c p) (boundaries b p) z) :
    ∃ z : KIP126.Literature.cycles model .sphere c p, z.val=x ∧
      ∀ q : KIP126.Literature.CycleQuotient model .sphere c b p,
        q=0 ∨ q=subquotientClass (KIP126.Literature.cycles model .sphere c p) (KIP126.Literature.boundaries model .sphere b p) z := by
  let Z (E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (hr : E.r₀=2) :=
    LinearMap.range (cycleMapFor E hr (↑(c-1).toNat) p).hom
  let B (E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ)) (hr : E.r₀=2) :=
    LinearMap.range (boundaryMapFor E hr (↑(b-1).toNat) p).hom
  let Frame (E : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
      (hr : E.r₀=2) (x : E.Page 2 p) : Prop :=
    ∃ z : Z E hr, z.val=x ∧ ∀ q : E2Subquotient (Z E hr) (B E hr),
      q=0 ∨ q=subquotientClass (Z E hr) (B E hr) z
  have tr (E E' : KIP126.Core.SpectralSequence (ModuleCat ℤ) (ℤ×ℤ))
      (he : E=E') (hr : E.r₀=2) (x : E.Page 2 p)
      (h : Frame E' (he ▸ hr) ((eqToHom (congrArg (fun A => A.Page 2 p) he)) x)) :
      Frame E hr x := by
    cases he
    exact h
  exact tr _ _ Normalized.sphere_eq.symm (model.classical.firstPage _) x h

end
end KIP126.Main.Internal.AlphaOne
end
