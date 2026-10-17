module

public import KIP126.ProofTools.Operations
import all KIP126.ProofTools.GeneralizedLeibniz.Filtration

/-! Representative form of AimPaper Proposition 2.10.  All labels and
filtrations belong to the same convergent map.  The proof uses only a finite
filtration interval and does not assume an additional completion theorem. -/

@[expose] section
namespace KIP126.ProofTools.Paper
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.ProofTools.Operations
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {E : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit E} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

/-- The homotopy class has the prescribed E∞ label under this convergence. -/
public def RepresentsInfinityClass (c : SyntheticTowerConvergence P X)
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (a : BiHom p.1 p.2 X) : Prop :=
  ∃ ar : (Subobject.underlying.obj ((P.filtration X).F s p) : ModuleCat.{v} ℤ),
    ((P.filtration X).F s p).arrow ar = a ∧
    (P.filtration X).toAssociatedGraded s p ar =
      (infinityGradedIso c p s).hom x

/-- No higher-source extension with nonzero target lands between the specified threshold
and the original target filtration. -/
public def ExtensionNoCrossingRange
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n threshold : ℤ) : Prop :=
  ∀ a b : ℤ, s < a → a ≤ b → threshold ≤ b → b ≤ s+n →
    ∀ x y, TowerExtensionEquation M p a (b-a) x y → y = 0

private theorem image_correction_in_next
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n threshold : ℤ) (hthreshold : threshold ≤ s+n)
    (hcross : ExtensionNoCrossingRange M p s n threshold)
    (a : BiHom p.1 p.2 X)
    (ha : a ∈ P.filtrationSubmodule X (s+1) p)
    (hga : a ≫ g ∈ P.filtrationSubmodule Y threshold p) :
    a ≫ g ∈ P.filtrationSubmodule Y (s+n+1) p := by
  let F : ℤ → AddSubgroup (BiHom p.1 p.2 X) :=
    fun k => (P.filtrationSubmodule X k p).toAddSubgroup
  let G : ℤ → AddSubgroup (BiHom p.1 p.2 Y) :=
    fun k => (P.filtrationSubmodule Y k p).toAddSubgroup
  let f : BiHom p.1 p.2 X →+ BiHom p.1 p.2 Y :=
    (syntheticHomotopyMap g p).hom.toAddMonoidHom
  by_contra hnot
  have hnot' : f a ∉ G (threshold + (s+n+1-threshold).toNat) := by
    have hindex : threshold + ((s+n+1-threshold).toNat : ℤ) = s+n+1 := by
      rw [Int.toNat_of_nonneg (show 0 ≤ s+n+1-threshold by omega)]
      omega
    rw [hindex]
    change ¬ a ≫ g ∈ P.filtrationSubmodule Y (s+n+1) p
    exact hnot
  obtain ⟨b,hb,hbn,hgb,hgbnext⟩ :=
    first_nonzero_filtration_grade G threshold (s+n+1-threshold).toNat (f a)
      hga hnot'
  by_cases hbs : b ≤ s
  · apply hgbnext
    exact P.filtrationSubmodule_antitone Y p (by omega)
      (map_preserves_filtration M p (s+1) a ha)
  · apply hgbnext
    exact Internal.Leibniz.higher_source_image_of_nonessential f F G
      (fun i j hij z hz => P.filtrationSubmodule_antitone Y p hij hz)
      (fun k z hz => map_preserves_filtration M p k z hz) s b (by omega)
      (fun k hsk hkb z hz hgz => by
        change z ≫ g ∈ P.filtrationSubmodule Y b p at hgz
        have hno : ∀ x y, ¬TowerEssentialExtension M p k (b-k) x y := by
          intro x y hess
          have hy := hcross k b hsk hkb hb (by omega) x y hess.1
          subst y
          exact (Internal.Leibniz.tower_essential_iff_no_zero M p k (b-k) x 0 hess.1).mp hess hess.1
        have hh := Internal.Leibniz.tower_correction_of_nonessential M p k (b-k)
          (by omega) hno z hz (by
            simpa only [add_sub_cancel] using hgz)
        change ∃ b', b' ∈ P.filtrationSubmodule X k p ∧
          z-b' ∈ P.filtrationSubmodule X (k+1) p ∧
          b' ≫ g ∈ P.filtrationSubmodule Y (b+1) p
        simpa only [add_sub_cancel] using hh) a ha hgb

private theorem represents_mem
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (a : BiHom p.1 p.2 X) (ha : RepresentsInfinityClass cx p s x a) :
    a ∈ P.filtrationSubmodule X s p := by
  obtain ⟨ar,har,_⟩ := ha
  rw [←har]
  have h : ((P.filtration X).F s p).arrow ar ∈
      ModuleCat.subobjectModule _ ((P.filtration X).F s p) := ⟨ar,rfl⟩
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using h

private theorem representatives_difference
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (a b : BiHom p.1 p.2 X)
    (ha : RepresentsInfinityClass cx p s x a)
    (hb : RepresentsInfinityClass cx p s x b) :
    a-b ∈ P.filtrationSubmodule X (s+1) p := by
  obtain ⟨ar,har,hax⟩ := ha
  obtain ⟨br,hbr,hbx⟩ := hb
  have h := (Internal.element_grade_equal_iff (P.filtration X) s p ar br).mp
    (hax.trans hbx.symm)
  rw [har,hbr] at h
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using h

private theorem represents_of_difference
    (p : ℤ × ℤ) (s : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (a b : BiHom p.1 p.2 X)
    (hb : RepresentsInfinityClass cx p s x b)
    (hdiff : a-b ∈ P.filtrationSubmodule X (s+1) p) :
    RepresentsInfinityClass cx p s x a := by
  have ha : a ∈ P.filtrationSubmodule X s p := by
    have hh := (P.filtrationSubmodule X s p).add_mem
      (P.filtrationSubmodule_antitone X p (show s ≤ s+1 by omega) hdiff)
      (represents_mem p s x b hb)
    simpa only [sub_add_cancel] using hh
  obtain ⟨ar,har⟩ := filtration_representative_exists P X p s a ha
  obtain ⟨br,hbr,hbx⟩ := hb
  refine ⟨ar,har,?_⟩
  apply Eq.trans ?_ hbx
  apply (Internal.element_grade_equal_iff (P.filtration X) s p ar br).mpr
  rw [har,hbr]
  simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using hdiff

/-- AimPaper Proposition 2.10: absence of crossings in the prescribed target
range is equivalent to independence of all source representatives whose image
has the required filtration.  This is the representative formulation for the
same actual map and the same two convergences. -/
public theorem extension_noCrossingRange_iff
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n threshold : ℤ) (hthreshold : threshold ≤ s+n)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation M p s n x y) :
    ExtensionNoCrossingRange M p s n threshold ↔
      ∀ a : BiHom p.1 p.2 X, RepresentsInfinityClass cx p s x a →
        a ≫ g ∈ P.filtrationSubmodule Y threshold p →
        RepresentsInfinityClass cy p (s+n) y (a ≫ g) := by
  obtain ⟨hn,ar₀,br₀,he₀,hx₀,hy₀⟩ := (tower_extension_iff M p s n x y).mp he
  let a₀ : BiHom p.1 p.2 X := ((P.filtration X).F s p).arrow ar₀
  let b₀ : BiHom p.1 p.2 Y := ((P.filtration Y).F (s+n) p).arrow br₀
  have hx : RepresentsInfinityClass cx p s x a₀ := ⟨ar₀,rfl,hx₀⟩
  have hy : RepresentsInfinityClass cy p (s+n) y b₀ := ⟨br₀,rfl,hy₀⟩
  have hbase : a₀ ≫ g = b₀ := he₀
  constructor
  · intro hc a ha hga
    have hdiff := representatives_difference p s x a a₀ ha hx
    have himage : (a-a₀) ≫ g ∈ P.filtrationSubmodule Y threshold p := by
      rw [Preadditive.sub_comp,hbase]
      exact (P.filtrationSubmodule Y threshold p).sub_mem hga
        (P.filtrationSubmodule_antitone Y p hthreshold (represents_mem p (s+n) y b₀ hy))
    have hh := image_correction_in_next M p s n threshold hthreshold hc (a-a₀) hdiff himage
    apply represents_of_difference p (s+n) y (a≫g) b₀ hy
    simpa only [Preadditive.sub_comp,hbase] using hh
  · intro hall u v hsu huv htv hvs xx yy he'
    obtain ⟨_,ar,br,heq,hxx,hyy⟩ := (tower_extension_iff M p u (v-u) xx yy).mp he'
    let a : BiHom p.1 p.2 X := ((P.filtration X).F u p).arrow ar
    have ha : a ∈ P.filtrationSubmodule X u p := by
      have h : a ∈ ModuleCat.subobjectModule _ ((P.filtration X).F u p) := ⟨ar,rfl⟩
      simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply] using h
    have hfa : a≫g ∈ P.filtrationSubmodule Y v p := by
      have h : a≫g ∈ ModuleCat.subobjectModule _ ((P.filtration Y).F (u+(v-u)) p) :=
        ⟨br,heq.symm⟩
      simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
        add_sub_cancel] using h
    have hsum : RepresentsInfinityClass cx p s x (a₀+a) := by
      apply represents_of_difference p s x (a₀+a) a₀ hx
      simpa only [add_sub_cancel_left] using
        (P.filtrationSubmodule_antitone X p (show s+1 ≤ u by omega) ha)
    have hsumg : (a₀+a)≫g ∈ P.filtrationSubmodule Y threshold p := by
      rw [Preadditive.add_comp,hbase]
      exact (P.filtrationSubmodule Y threshold p).add_mem
        (P.filtrationSubmodule_antitone Y p hthreshold (represents_mem p (s+n) y b₀ hy))
        (P.filtrationSubmodule_antitone Y p htv hfa)
    have hdet := hall (a₀+a) hsum hsumg
    have hdiff := representatives_difference p (s+n) y ((a₀+a)≫g) b₀ hdet hy
    have hnext : a≫g ∈ P.filtrationSubmodule Y (v+1) p := by
      have h : a≫g ∈ P.filtrationSubmodule Y (s+n+1) p := by
        simpa only [Preadditive.add_comp,hbase,add_sub_cancel_left] using hdiff
      exact P.filtrationSubmodule_antitone Y p (by omega) h
    have hzero := (Internal.element_grade_equal_iff (P.filtration Y) (u+(v-u)) p br 0).mpr
      (by
        rw [←heq,map_zero,sub_zero]
        simpa only [SyntheticTowerPresentation.filtration,OrderIso.apply_symm_apply,
          add_sub_cancel, a] using hnext)
    apply (ModuleCat.mono_iff_injective (infinityGradedIso cy p (u+(v-u))).hom).mp inferInstance
    rw [map_zero]
    rw [map_zero] at hzero
    exact hyy.symm.trans hzero

/-- Proposition 2.10(1).  Higher-source crossings automatically have target
filtration at least s+1; the threshold s therefore excludes every crossing. -/
public theorem extension_noCrossing_iff
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation M p s n x y) :
    ExtensionNoCrossingRange M p s n s ↔
      ∀ a : BiHom p.1 p.2 X, RepresentsInfinityClass cx p s x a →
        RepresentsInfinityClass cy p (s+n) y (a ≫ g) := by
  have hn := ((tower_extension_iff M p s n x y).mp he).1
  have h := extension_noCrossingRange_iff M p s n s (by omega) x y he
  constructor
  · intro hc a ha
    exact h.mp hc a ha (map_preserves_filtration M p s a (represents_mem p s x a ha))
  · intro hall
    exact h.mpr (fun a ha _ => hall a ha)

private theorem represents_zero_iff (p : ℤ × ℤ) (s : ℤ) (a : BiHom p.1 p.2 X) :
    RepresentsInfinityClass cx p s 0 a ↔ a ∈ P.filtrationSubmodule X (s+1) p := by
  have hzero : RepresentsInfinityClass cx p s 0 (0 : BiHom p.1 p.2 X) :=
    ⟨0,by simp only [map_zero],by simp only [map_zero]⟩
  constructor
  · intro ha
    simpa only [sub_zero] using representatives_difference p s 0 a 0 ha hzero
  · intro ha
    exact represents_of_difference p s 0 a 0 hzero (by simpa only [sub_zero] using ha)

/-- Proposition 2.10(2): the zero target means strictly higher filtration,
uniformly for every representative of the specified source label. -/
public theorem extension_zero_noCrossing_iff
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (he : TowerExtensionEquation M p s n x 0) :
    ExtensionNoCrossingRange M p s n s ↔
      ∀ a : BiHom p.1 p.2 X, RepresentsInfinityClass cx p s x a →
        a ≫ g ∈ P.filtrationSubmodule Y (s+n+1) p := by
  rw [extension_noCrossing_iff M p s n x 0 he]
  constructor
  · intro hall a ha
    exact (represents_zero_iff p (s+n) (a≫g)).mp (hall a ha)
  · intro hall a ha
    exact (represents_zero_iff p (s+n) (a≫g)).mpr (hall a ha)

/-- Proposition 2.10(3).  An actual filtration-n map has no length-n
crossing.  Only the filtration lower bound is needed, so the statement also
applies when the actual filtration is larger. -/
public theorem extension_noCrossing_of_filtration_bound
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation M p s n x y)
    (hmap : ∀ k : ℤ, ∀ a : BiHom p.1 p.2 X,
      a ∈ P.filtrationSubmodule X k p →
      a ≫ g ∈ P.filtrationSubmodule Y (k+n) p) :
    ExtensionNoCrossingRange M p s n s := by
  apply (extension_noCrossing_iff M p s n x y he).mpr
  obtain ⟨_,ar₀,br₀,he₀,hx₀,hy₀⟩ := (tower_extension_iff M p s n x y).mp he
  let a₀ : BiHom p.1 p.2 X := ((P.filtration X).F s p).arrow ar₀
  let b₀ : BiHom p.1 p.2 Y := ((P.filtration Y).F (s+n) p).arrow br₀
  have hx : RepresentsInfinityClass cx p s x a₀ := ⟨ar₀,rfl,hx₀⟩
  have hy : RepresentsInfinityClass cy p (s+n) y b₀ := ⟨br₀,rfl,hy₀⟩
  have hbase : a₀ ≫ g = b₀ := he₀
  intro a ha
  apply represents_of_difference p (s+n) y (a≫g) b₀ hy
  have hdiff := hmap (s+1) (a-a₀) (representatives_difference p s x a a₀ ha hx)
  simpa only [Preadditive.sub_comp,hbase,add_assoc,add_comm,add_left_comm] using hdiff

end

section Additive
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Crossing in ordinary filtered homotopy groups, with all nonzero target
grades retained.  A represents any leading source class in filtration u. -/
public def FilteredNoCrossingRange (f : A →+ B)
    (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B)
    (s n threshold : ℤ) : Prop :=
  ∀ u v : ℤ, s < u → u ≤ v → threshold ≤ v → v ≤ s+n →
    ∀ a : A, a ∈ F u → f a ∈ G v → f a ∈ G (v+1)

private theorem filtered_correction_in_next (f : A →+ B)
    (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B) (hG : Antitone G)
    (hf : ∀ u a, a ∈ F u → f a ∈ G u)
    (s n threshold : ℤ) (ht : threshold ≤ s+n)
    (hc : FilteredNoCrossingRange f F G s n threshold)
    (a : A) (ha : a ∈ F (s+1)) (hfa : f a ∈ G threshold) :
    f a ∈ G (s+n+1) := by
  by_contra hnot
  have hi : threshold + ((s+n+1-threshold).toNat : ℤ) = s+n+1 := by
    rw [Int.toNat_of_nonneg (show 0 ≤ s+n+1-threshold by omega)]
    omega
  obtain ⟨v,hv,hvn,hfv,hfvn⟩ := first_nonzero_filtration_grade G threshold
    (s+n+1-threshold).toNat (f a) hfa (by rwa [hi])
  apply hfvn
  by_cases hvs : v ≤ s
  · exact hG (show v+1 ≤ s+1 by omega) (hf (s+1) a ha)
  · exact hc (s+1) v (by omega) (by omega) hv (by omega) a ha hfv

/-- Proposition 2.10 for arbitrary filtered abelian groups.  Equality of source
labels is a-a0 ∈ F^(s+1); equality of target labels is f(a)-f(a0) ∈ G^(s+n+1).
Thus this formulation applies to classical homotopy groups as well as to the
synthetic representative version above.  a0 is a witness of the given extension. -/
public theorem filtered_extension_noCrossingRange_iff (f : A →+ B)
    (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B)
    (hF : Antitone F) (hG : Antitone G)
    (hf : ∀ u a, a ∈ F u → f a ∈ G u)
    (s n threshold : ℤ) (ht : threshold ≤ s+n)
    (a0 : A) (ha0 : a0 ∈ F s) (hfa0 : f a0 ∈ G (s+n)) :
    FilteredNoCrossingRange f F G s n threshold ↔
      ∀ a : A, a ∈ F s → a-a0 ∈ F (s+1) → f a ∈ G threshold →
        f a ∈ G (s+n) ∧ f a-f a0 ∈ G (s+n+1) := by
  constructor
  · intro hc a _ hd hfa
    have hh := filtered_correction_in_next f F G hG hf s n threshold ht hc
      (a-a0) hd (by rw [map_sub]; exact (G threshold).sub_mem hfa (hG ht hfa0))
    have hdiff : f a-f a0 ∈ G (s+n+1) := by simpa only [map_sub] using hh
    refine ⟨?_,hdiff⟩
    have h := (G (s+n)).add_mem (hG (show s+n ≤ s+n+1 by omega) hdiff) hfa0
    simpa only [sub_add_cancel] using h
  · intro hall u v hsu huv htv hvs a ha hfa
    have ha' : a ∈ F (s+1) := hF (by omega) ha
    have hsum : a0+a ∈ F s := (F s).add_mem ha0 (hF (by omega) ha)
    have hdiff : a0+a-a0 ∈ F (s+1) := by simpa only [add_sub_cancel_left] using ha'
    have hsumf : f (a0+a) ∈ G threshold := by
      rw [map_add]
      exact (G threshold).add_mem (hG ht hfa0) (hG htv hfa)
    have hh := (hall (a0+a) hsum hdiff hsumf).2
    have hh' : f a ∈ G (s+n+1) := by simpa only [map_add,add_sub_cancel_left] using hh
    exact hG (by omega) hh'

/-- Proposition 2.10(1), with all representatives and no target threshold. -/
public theorem filtered_extension_noCrossing_iff (f : A →+ B)
    (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B)
    (hF : Antitone F) (hG : Antitone G)
    (hf : ∀ u a, a ∈ F u → f a ∈ G u)
    (s n : ℤ) (hn : 0 ≤ n) (a0 : A)
    (ha0 : a0 ∈ F s) (hfa0 : f a0 ∈ G (s+n)) :
    FilteredNoCrossingRange f F G s n s ↔
      ∀ a : A, a ∈ F s → a-a0 ∈ F (s+1) →
        f a ∈ G (s+n) ∧ f a-f a0 ∈ G (s+n+1) := by
  have h := filtered_extension_noCrossingRange_iff f F G hF hG hf s n s (by omega) a0 ha0 hfa0
  constructor
  · intro hc a ha hd
    exact h.mp hc a ha hd (hf s a ha)
  · intro hall
    exact h.mpr (fun a ha hd _ => hall a ha hd)

/-- Proposition 2.10(2): zero target label is precisely strictly higher
filtration for the image of every source representative. -/
public theorem filtered_zero_extension_noCrossing_iff (f : A →+ B)
    (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B)
    (hF : Antitone F) (hG : Antitone G)
    (hf : ∀ u a, a ∈ F u → f a ∈ G u)
    (s n : ℤ) (hn : 0 ≤ n) (a0 : A)
    (ha0 : a0 ∈ F s) (hfa0 : f a0 ∈ G (s+n+1)) :
    FilteredNoCrossingRange f F G s n s ↔
      ∀ a : A, a ∈ F s → a-a0 ∈ F (s+1) → f a ∈ G (s+n+1) := by
  rw [filtered_extension_noCrossing_iff f F G hF hG hf s n hn a0 ha0
    (hG (show s+n ≤ s+n+1 by omega) hfa0)]
  constructor
  · intro hall a ha hd
    have h := (G (s+n+1)).add_mem (hall a ha hd).2 hfa0
    simpa only [sub_add_cancel] using h
  · intro hall a ha hd
    have h := hall a ha hd
    exact ⟨hG (show s+n ≤ s+n+1 by omega) h,(G (s+n+1)).sub_mem h hfa0⟩

/-- Proposition 2.10(3) in ordinary filtered groups.  The actual filtration-n
bound excludes every crossing of an n-extension, without a boundedness premise. -/
public theorem filtered_extension_noCrossing_of_filtration_bound (f : A →+ B)
    (F : ℤ → AddSubgroup A) (G : ℤ → AddSubgroup B) (hG : Antitone G)
    (s n : ℤ) (hf : ∀ u a, a ∈ F u → f a ∈ G (u+n)) :
    FilteredNoCrossingRange f F G s n s := by
  intro u v hsu huv hsv hvs a ha hfa
  exact hG (show v+1 ≤ u+n by omega) (hf u a ha)

end Additive
end KIP126.ProofTools.Paper
