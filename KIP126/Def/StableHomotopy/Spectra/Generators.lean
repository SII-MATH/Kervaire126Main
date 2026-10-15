module

public import KIP126.Def.StableHomotopy.Spectra.PointSet
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Analysis.Normed.Module.Connected

@[expose] public section

/-! Suspension spectra and free sequential prespectra. These give the
point-set generators used in the smash-product comparison and telescope construction. -/
namespace KIP126.StableHomotopy.Spectra
open CategoryTheory Topology
open scoped unitInterval
universe u

namespace BasedSpace

@[ext] structure Hom (X Y : BasedSpace.{u}) where
  map : C(X,Y)
  point : map X.point = Y.point

instance : Category BasedSpace.{u} where
  Hom := Hom
  id X := ⟨ContinuousMap.id _, rfl⟩
  comp f g := ⟨g.map.comp f.map, by simp [f.point, g.point]⟩
  id_comp := by intros; ext; rfl
  comp_id := by intros; ext; rfl
  assoc := by intros; ext; rfl

def suspendMap {X Y : BasedSpace.{u}} (f : X ⟶ Y) : X.suspension ⟶ Y.suspension where
  map := suspensionMap X Y f.map f.point
  point := suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))

def iterateSuspension (X : BasedSpace.{u}) : ℕ → BasedSpace.{u}
  | 0 => X
  | n+1 => (iterateSuspension X n).suspension

def iterateSuspensionMap {X Y : BasedSpace.{u}} (f : X ⟶ Y) :
    ∀ n, iterateSuspension X n ⟶ iterateSuspension Y n
  | 0 => f
  | n+1 => suspendMap (iterateSuspensionMap f n)

def SmashRelation (X Y : BasedSpace.{u}) (p q : X × Y) : Prop :=
  (p.1 = X.point ∨ p.2 = Y.point) ∧ (q.1 = X.point ∨ q.2 = Y.point)

/-- Reduced smash in compactly generated spaces: k-ify the product before
collapsing its wedge. -/
def smash (X Y : BasedSpace.{u}) : BasedSpace.{u} where
  space := by
    letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
    exact TopCat.of (Quot (SmashRelation X Y))
  point := Quot.mk _ (X.point,Y.point)

def smashPoint (X Y : BasedSpace.{u}) (x : X) (y : Y) : X.smash Y := Quot.mk _ (x,y)

theorem smashPoint_base_left (X Y : BasedSpace.{u}) (y : Y) :
    smashPoint X Y X.point y = (X.smash Y).point := Quot.sound ⟨Or.inl rfl, Or.inl rfl⟩

theorem smashPoint_base_right (X Y : BasedSpace.{u}) (x : X) :
    smashPoint X Y x Y.point = (X.smash Y).point := Quot.sound ⟨Or.inr rfl, Or.inl rfl⟩

/-- The representative formulas uniquely determine the induced based maps.
Only their continuous quotient extension is a construction obligation. -/
theorem smashMap_exists {X Y X' Y' : BasedSpace.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    ∃! h : X.smash Y ⟶ X'.smash Y', ∀ x y,
      h.map (smashPoint X Y x y) = smashPoint X' Y' (f.map x) (g.map y) := by
  have hc : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),
      TopologicalSpace.compactlyGenerated.{u} (X' × Y')]
      (fun p : X × Y => (f.map p.1,g.map p.2)) := by
    refine @continuous_from_compactlyGenerated (X × Y) (X' × Y') _
      (TopologicalSpace.compactlyGenerated.{u} (X' × Y')) _ ?_
    intro S k
    let l : C(S, X' × Y') :=
      ⟨fun s => (f.map (k s).1,g.map (k s).2),
        (f.map.continuous.comp k.continuous.fst).prodMk
          (g.map.continuous.comp k.continuous.snd)⟩
    let ev : (Σ i : (T : CompHaus.{u}) × C(T, X' × Y'), i.fst) → X' × Y' :=
      fun q => q.1.2 q.2
    have hi : Continuous (fun s : S => (⟨⟨S,l⟩,s⟩ :
        Σ i : (T : CompHaus.{u}) × C(T, X' × Y'), i.fst)) :=
      @continuous_sigmaMk _ (fun i : (T : CompHaus.{u}) × C(T, X' × Y') => i.fst)
        (fun _ => inferInstance) ⟨S,l⟩
    letI : TopologicalSpace (X' × Y') := TopologicalSpace.coinduced ev inferInstance
    exact (show Continuous ev from continuous_coinduced_rng).comp hi
  let raw : X × Y → X'.smash Y' := fun p => smashPoint X' Y' (f.map p.1) (g.map p.2)
  have collapsed (p : X × Y) (hp : p.1 = X.point ∨ p.2 = Y.point) :
      raw p = (X'.smash Y').point := by
    rcases hp with h | h
    · dsimp [raw]
      rw [h, f.point]
      exact smashPoint_base_left _ _ _
    · dsimp [raw]
      rw [h, g.point]
      exact smashPoint_base_right _ _ _
  have hr : ∀ a b, SmashRelation X Y a b → raw a = raw b :=
    fun a b h => (collapsed a h.1).trans (collapsed b h.2).symm
  letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
  letI : TopologicalSpace (X' × Y') := TopologicalSpace.compactlyGenerated.{u} (X' × Y')
  let h : X.smash Y ⟶ X'.smash Y' :=
    { map := ⟨Quot.lift raw hr, continuous_quot_lift hr (continuous_quot_mk.comp hc)⟩
      point := collapsed _ (Or.inl rfl) }
  refine ⟨h, fun _ _ => rfl, ?_⟩
  intro h' hh'
  apply Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  intro p
  exact hh' p.1 p.2

noncomputable def smashMap {X Y X' Y' : BasedSpace.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    X.smash Y ⟶ X'.smash Y' := (smashMap_exists f g).exists.choose

theorem smashCoherence_exists :
    (∀ X Y Z : BasedSpace.{u}, ∃! a : (X.smash Y).smash Z ⟶ X.smash (Y.smash Z),
      ∀ x y z, a.map (smashPoint _ Z (smashPoint X Y x y) z) =
        smashPoint X _ x (smashPoint Y Z y z)) ∧
    (∀ X Y : BasedSpace.{u}, ∃! b : X.smash Y ⟶ Y.smash X,
      ∀ x y, b.map (smashPoint X Y x y) = smashPoint Y X y x) := by
  have into_k {T : Type u} [TopologicalSpace T] (K : CompHaus.{u}) (g : C(K,T)) :
      Continuous[inferInstance,TopologicalSpace.compactlyGenerated.{u} T] g := by
    let ev : (Σ i : (S : CompHaus.{u}) × C(S,T),i.fst) → T := fun q => q.1.2 q.2
    have hi : Continuous (fun k : K => (⟨⟨K,g⟩,k⟩ :
        Σ i : (S : CompHaus.{u}) × C(S,T),i.fst)) :=
      @continuous_sigmaMk _ (fun i : (S : CompHaus.{u}) × C(S,T) => i.fst)
        (fun _ => inferInstance) ⟨K,g⟩
    letI : TopologicalSpace T := TopologicalSpace.coinduced ev inferInstance
    exact (show Continuous ev from continuous_coinduced_rng).comp hi
  have smashK (P Q : BasedSpace.{u}) (K : CompHaus.{u}) (g : C(K,P × Q)) :
      Continuous (fun k => smashPoint P Q (g k).1 (g k).2) := by
    have h := into_k K g
    letI : TopologicalSpace (P × Q) := TopologicalSpace.compactlyGenerated.{u} (P × Q)
    exact continuous_quot_mk.comp h
  constructor
  · intro X Y Z
    have nestedK (K : CompHaus.{u}) (α : C(K,X)) (β : C(K,Y)) (γ : C(K,Z)) :
        Continuous (fun k => smashPoint X (Y.smash Z) (α k) (smashPoint Y Z (β k) (γ k))) := by
      exact smashK X (Y.smash Z) K
        ⟨_,α.continuous.prodMk (smashK Y Z K ⟨_,β.continuous.prodMk γ.continuous⟩)⟩
    have inner_collapsed (z : Z) (p : X × Y) (hp : p.1 = X.point ∨ p.2 = Y.point) :
        smashPoint X (Y.smash Z) p.1 (smashPoint Y Z p.2 z) = (X.smash (Y.smash Z)).point := by
      rcases hp with h | h
      · rw [h,smashPoint_base_left]
      · rw [h,smashPoint_base_left,smashPoint_base_right]
    let raw : X.smash Y × Z → X.smash (Y.smash Z) := fun p =>
      Quot.lift (fun q : X × Y => smashPoint X (Y.smash Z) q.1 (smashPoint Y Z q.2 p.2))
        (fun q r h => (inner_collapsed p.2 q h.1).trans (inner_collapsed p.2 r h.2).symm) p.1
    have rawK (K : CompHaus.{u}) (γ : C(K,Z)) :
        Continuous (fun p : X.smash Y × K => raw (p.1,γ p.2)) := by
      let F : X × Y → C(K,X.smash (Y.smash Z)) := fun p =>
        ⟨_,nestedK K (ContinuousMap.const K p.1) (ContinuousMap.const K p.2) γ⟩
      have hF : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),inferInstance] F := by
        apply continuous_from_compactlyGenerated
        intro S g
        have hg : Continuous (fun p : S × K =>
            smashPoint X (Y.smash Z) (g p.1).1 (smashPoint Y Z (g p.1).2 (γ p.2))) :=
          nestedK (CompHaus.of (S × K))
            ⟨_,g.continuous.fst.comp continuous_fst⟩
            ⟨_,g.continuous.snd.comp continuous_fst⟩
            ⟨_,γ.continuous.comp continuous_snd⟩
        exact (ContinuousMap.curry ⟨_,hg⟩).continuous
      letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact ContinuousMap.continuous_uncurry_of_continuous ⟨F,hF⟩
    have hc : Continuous[TopologicalSpace.compactlyGenerated.{u} (X.smash Y × Z),inferInstance] raw := by
      apply continuous_from_compactlyGenerated
      intro K g
      exact (rawK K ⟨fun k => (g k).2,g.continuous.snd⟩).comp
        (g.continuous.fst.prodMk continuous_id)
    have collapsed (p : X.smash Y × Z) (hp : p.1 = (X.smash Y).point ∨ p.2 = Z.point) :
        raw p = (X.smash (Y.smash Z)).point := by
      rcases p with ⟨a,z⟩
      rcases hp with h | h
      · dsimp only [Prod.fst] at h
        subst a
        exact inner_collapsed z (X.point,Y.point) (Or.inl rfl)
      · dsimp only [Prod.snd] at h
        subst z
        refine Quot.inductionOn a ?_
        rintro ⟨x,y⟩
        change smashPoint X (Y.smash Z) x (smashPoint Y Z y Z.point) = _
        rw [smashPoint_base_right,smashPoint_base_right]
    have respects : ∀ p q, SmashRelation (X.smash Y) Z p q → raw p = raw q :=
      fun p q h => (collapsed p h.1).trans (collapsed q h.2).symm
    letI : TopologicalSpace (X.smash Y × Z) :=
      TopologicalSpace.compactlyGenerated.{u} (X.smash Y × Z)
    let a : (X.smash Y).smash Z ⟶ X.smash (Y.smash Z) :=
      { map := ⟨Quot.lift raw respects,continuous_quot_lift respects hc⟩
        point := collapsed ((X.smash Y).point,Z.point) (Or.inl rfl) }
    refine ⟨a,fun _ _ _ => rfl,?_⟩
    intro b hb
    apply Hom.ext
    apply ContinuousMap.ext
    intro p
    refine Quot.inductionOn p ?_
    rintro ⟨q,z⟩
    refine Quot.inductionOn q ?_
    rintro ⟨x,y⟩
    exact hb x y z
  · intro X Y
    let raw : X × Y → Y.smash X := fun p => smashPoint Y X p.2 p.1
    have hc : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),inferInstance] raw := by
      apply continuous_from_compactlyGenerated
      intro K g
      exact smashK Y X K ⟨_,g.continuous.snd.prodMk g.continuous.fst⟩
    have collapsed (p : X × Y) (hp : p.1 = X.point ∨ p.2 = Y.point) :
        raw p = (Y.smash X).point := by
      rcases hp with h | h
      · dsimp [raw]
        rw [h,smashPoint_base_right]
      · dsimp [raw]
        rw [h,smashPoint_base_left]
    have respects : ∀ p q, SmashRelation X Y p q → raw p = raw q :=
      fun p q h => (collapsed p h.1).trans (collapsed q h.2).symm
    letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
    let b : X.smash Y ⟶ Y.smash X :=
      { map := ⟨Quot.lift raw respects,continuous_quot_lift respects hc⟩
        point := collapsed (X.point,Y.point) (Or.inl rfl) }
    refine ⟨b,fun _ _ => rfl,?_⟩
    intro c hc
    apply Hom.ext
    apply ContinuousMap.ext
    intro p
    refine Quot.inductionOn p ?_
    rintro ⟨x,y⟩
    exact hc x y

noncomputable def smashAssoc (X Y Z : BasedSpace.{u}) :
    (X.smash Y).smash Z ⟶ X.smash (Y.smash Z) :=
  (smashCoherence_exists.1 X Y Z).exists.choose

noncomputable def smashSwap (X Y : BasedSpace.{u}) : X.smash Y ⟶ Y.smash X :=
  (smashCoherence_exists.2 X Y).exists.choose

/-- Actual based CW homotopy type, using characteristic cells and weak
CW topology from Mathlib, and homotopies fixed at the specified basepoint. -/
def HasCWType (A : BasedSpace.{u}) : Prop :=
  ∃ Y : BasedSpace.{u}, T2Space Y ∧
    Nonempty (Topology.CWComplex (Set.univ : Set Y)) ∧ Y.IsWellBased ∧
    ∃ (f : A ⟶ Y) (g : Y ⟶ A),
      (g.map.comp f.map).HomotopicRel (ContinuousMap.id A) {A.point} ∧
      (f.map.comp g.map).HomotopicRel (ContinuousMap.id Y) {Y.point}

/-- The derived-smash comparison is restricted to compactly generated,
well-based spaces of actual CW homotopy type. Merely being well-based does
not supply the flatness hypothesis used in MMSS, Proposition 11.7. -/
def IsGood (A : BasedSpace.{u}) : Prop :=
  UCompactlyGeneratedSpace.{u} A ∧ A.IsWellBased ∧ A.HasCWType

def zeroSphere : BasedSpace.{0} := Prespectrum.sphereLevel 0

-- Retain the named hypotheses in the statement of this theorem.
set_option linter.unusedVariables false in
theorem smashUnit_exists (A : BasedSpace.{0}) (hA : A.IsGood) :
    ∃! f : zeroSphere.smash A ⟶ A,
      ∀ a, f.map (smashPoint zeroSphere A (show zeroSphere from (1 : Fin 2)) a) = a := by
  classical
  letI : DiscreteTopology zeroSphere := inferInstanceAs (DiscreteTopology (Fin 2))
  let raw : zeroSphere × A → A := fun p => if p.1 = zeroSphere.point then A.point else p.2
  have hc : Continuous raw := by
    apply continuous_prod_of_discrete_left.mpr
    intro x
    dsimp [raw]
    split_ifs
    · exact continuous_const
    · exact continuous_id
  have collapsed (p : zeroSphere × A)
      (hp : p.1 = zeroSphere.point ∨ p.2 = A.point) : raw p = A.point := by
    rcases hp with h | h
    · simp [raw, h]
    · simp [raw, h]
  have hr : ∀ a b, SmashRelation zeroSphere A a b → raw a = raw b :=
    fun a b h => (collapsed a h.1).trans (collapsed b h.2).symm
  have hck : Continuous[TopologicalSpace.compactlyGenerated.{0} (zeroSphere × A),
      inferInstance] raw :=
    continuous_from_compactlyGenerated raw (fun _ k => hc.comp k.continuous)
  letI : TopologicalSpace (zeroSphere × A) :=
    TopologicalSpace.compactlyGenerated.{0} (zeroSphere × A)
  let f : zeroSphere.smash A ⟶ A :=
    { map := ⟨Quot.lift raw hr, continuous_quot_lift hr hck⟩
      point := collapsed _ (Or.inl rfl) }
  refine ⟨f, ?_, ?_⟩
  · intro a
    change raw ((1 : Fin 2), a) = a
    simp [raw, zeroSphere, Prespectrum.sphereLevel]
  · intro g hg
    apply Hom.ext
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro ⟨x,a⟩
    change g.map (smashPoint zeroSphere A x a) = raw (x,a)
    change Fin 2 at x
    fin_cases x
    · change g.map (smashPoint zeroSphere A zeroSphere.point a) = raw (zeroSphere.point,a)
      rw [smashPoint_base_left, g.point]
      simp [raw]
    · simpa [raw, zeroSphere, Prespectrum.sphereLevel] using hg a

noncomputable def smashUnit (A : BasedSpace.{0}) (hA : A.IsGood) :
    zeroSphere.smash A ⟶ A := (smashUnit_exists A hA).exists.choose

theorem good_zeroSphere : zeroSphere.IsGood := by
  classical
  letI : DiscreteTopology zeroSphere := inferInstanceAs (DiscreteTopology (Fin 2))
  have hwb : zeroSphere.IsWellBased := by
    refine ⟨isClosed_singleton, ?_⟩
    intro Y f p hp
    let H : C(zeroSphere × I,Y) := ContinuousMap.uncurry
      ⟨fun x => if x = zeroSphere.point then p else ContinuousMap.const I (f x),
        continuous_of_discreteTopology⟩
    refine ⟨H, ?_, ?_⟩
    · intro x
      by_cases hx : x = zeroSphere.point
      · simpa [H, hx] using hp
      · simp [H, hx]
    · intro t
      simp [H]
  refine ⟨inferInstance, hwb, zeroSphere, inferInstance, ⟨inferInstance⟩, hwb,
    𝟙 _, 𝟙 _, ?_, ?_⟩
  all_goals exact ContinuousMap.HomotopicRel.refl _

open Set in
/-- The fixed k-smash is compactly generated, and its specified point has
an actual cylinder retraction when the two input points do. -/
private theorem smash_point_set (X Y : BasedSpace.{u})
    (hX : X.IsWellBased) (hY : Y.IsWellBased) :
    UCompactlyGeneratedSpace.{u} (X.smash Y) ∧ (X.smash Y).IsWellBased := by
  have cylinder_retraction_of_wellBased (X : BasedSpace.{u}) (hX : X.IsWellBased) :
      ∃ r : C(X × I, X × I),
        (∀ x, r (x,0) = (x,0)) ∧
        (∀ t, r (X.point,t) = (X.point,t)) ∧
        (∀ q, (r q).2 = 0 ∨ (r q).1 = X.point) := by
    let S := {q : X × I // q.2 = 0 ∨ q.1 = X.point}
    let f : C(X,S) := ⟨fun x => ⟨(x,0),Or.inl rfl⟩,
      (continuous_id.prodMk continuous_const).subtype_mk _⟩
    let p : C(I,S) := ⟨fun t => ⟨(X.point,t),Or.inr rfl⟩,
      (continuous_const.prodMk continuous_id).subtype_mk _⟩
    obtain ⟨H,hH,hp⟩ := hX.2 (TopCat.of S) f p rfl
    refine ⟨⟨fun q => (H q).val,continuous_subtype_val.comp H.continuous⟩,?_,?_,?_⟩
    · intro x
      exact congrArg Subtype.val (hH x)
    · intro t
      exact congrArg Subtype.val (hp t)
    · intro q
      exact (H q).property
  have wellBased_of_cylinder_retraction (X : BasedSpace.{u})
      (hc : IsClosed ({X.point} : Set X)) (r : C(X × I, X × I))
      (hzero : ∀ x, r (x,0) = (x,0))
      (hpoint : ∀ t, r (X.point,t) = (X.point,t))
      (hr : ∀ q, (r q).2 = 0 ∨ (r q).1 = X.point) : X.IsWellBased := by
    classical
    refine ⟨hc, ?_⟩
    intro Y f p hp
    let U : Set (X × I) := {q | (r q).2 = 0}
    let V : Set (X × I) := {q | (r q).1 = X.point}
    have hU : IsClosed U := isClosed_eq r.continuous.snd continuous_const
    have hV : IsClosed V := hc.preimage r.continuous.fst
    have hUV : U ∪ V = Set.univ := by
      ext q
      exact iff_true_intro (hr q)
    let F : X × I → Y := fun q => if (r q).2 = 0 then f (r q).1 else p (r q).2
    have hu : ContinuousOn F U := (f.continuous.comp r.continuous.fst).continuousOn.congr
      (fun q hq => if_pos hq)
    have hv : ContinuousOn F V := (p.continuous.comp r.continuous.snd).continuousOn.congr (by
      intro q hq
      by_cases ht : (r q).2 = 0
      · change (if (r q).2 = 0 then f (r q).1 else p (r q).2) = p (r q).2
        rw [if_pos ht, ht, show (r q).1 = X.point from hq, hp]
      · exact if_neg ht)
    have hF : Continuous F := continuousOn_univ.mp (hUV ▸ hu.union_of_isClosed hv hU hV)
    refine ⟨⟨F,hF⟩,?_,?_⟩
    · intro x
      simp [F,hzero]
    · intro t
      change F (X.point,t) = p t
      simp only [F,hpoint]
      by_cases ht : t=0
      · simp [ht,hp]
      · simp [ht]
  have compactlyGenerated_kification (T : Type u) [t : TopologicalSpace T] :
      @UCompactlyGeneratedSpace.{u} T (TopologicalSpace.compactlyGenerated.{u} T) := by
    let ev : (Σ i : (S : CompHaus.{u}) × C(S,T), i.fst) → T := fun p => p.1.2 p.2
    letI : TopologicalSpace T := TopologicalSpace.coinduced ev inferInstance
    exact uCompactlyGeneratedSpace_of_coinduced
      (show Continuous ev from continuous_coinduced_rng) rfl
  have cg_prod_interval (T : Type u) [TopologicalSpace T]
      [UCompactlyGeneratedSpace.{u} T] : UCompactlyGeneratedSpace.{u} (T × I) := by
    apply uCompactlyGeneratedSpace_of_continuous_maps
    intro Y _ f hf
    let F : T → C(I,Y) := fun a => ⟨fun t => f (a,t),by
      have hc := hf (CompHaus.of (ULift.{u} I))
        ⟨fun t => (a,t.down),continuous_const.prodMk continuous_uliftDown⟩
      exact hc.comp continuous_uliftUp⟩
    have hF : Continuous F := by
      apply continuous_from_uCompactlyGeneratedSpace
      intro S g
      have hg : Continuous (fun p : S × I => f (g p.1,p.2)) :=
        hf (CompHaus.of (S × I)) ⟨fun p => (g p.1,p.2),
          (g.continuous.comp continuous_fst).prodMk continuous_snd⟩
      exact (ContinuousMap.curry ⟨_,hg⟩).continuous
    exact ContinuousMap.continuous_uncurry_of_continuous ⟨F,hF⟩
  have smash_compactlyGenerated (X Y : BasedSpace.{u}) :
      UCompactlyGeneratedSpace.{u} (X.smash Y) := by
    have hcg := compactlyGenerated_kification (X × Y)
    letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
    letI : UCompactlyGeneratedSpace.{u} (X × Y) := hcg
    exact uCompactlyGeneratedSpace_of_coinduced
      (show Continuous (Quot.mk (SmashRelation X Y)) from continuous_quot_mk) rfl
  have smash_wellBased (X Y : BasedSpace.{u})
      (hX : X.IsWellBased) (hY : Y.IsWellBased) : (X.smash Y).IsWellBased := by
    classical
    obtain ⟨rX,hX0,hXp,hXr⟩ := cylinder_retraction_of_wellBased X hX
    obtain ⟨rY,hY0,hYp,hYr⟩ := cylinder_retraction_of_wellBased Y hY
    have into_k {T : Type u} [TopologicalSpace T] (K : CompHaus.{u}) (g : C(K,T)) :
        Continuous[inferInstance,TopologicalSpace.compactlyGenerated.{u} T] g := by
      let ev : (Σ i : (S : CompHaus.{u}) × C(S,T),i.fst) → T := fun q => q.1.2 q.2
      have hi : Continuous (fun k : K => (⟨⟨K,g⟩,k⟩ :
          Σ i : (S : CompHaus.{u}) × C(S,T),i.fst)) :=
        @continuous_sigmaMk _ (fun i : (S : CompHaus.{u}) × C(S,T) => i.fst)
          (fun _ => inferInstance) ⟨K,g⟩
      letI : TopologicalSpace T := TopologicalSpace.coinduced ev inferInstance
      exact (show Continuous ev from continuous_coinduced_rng).comp hi
    have qcompact (S : CompHaus.{u}) (gx : C(S,X)) (gy : C(S,Y)) :
        Continuous (fun s => smashPoint X Y (gx s) (gy s)) := by
      have hc := into_k S (⟨fun s => (gx s,gy s),gx.continuous.prodMk gy.continuous⟩ : C(S,X × Y))
      letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
      exact continuous_quot_mk.comp hc
    let tag : X.smash Y → Prop := Quot.lift (fun p : X × Y => p.1 = X.point ∨ p.2 = Y.point)
      (fun p q hpq => propext ⟨fun _ => hpq.2,fun _ => hpq.1⟩)
    have hmem (p : X × Y) : smashPoint X Y p.1 p.2 = (X.smash Y).point ↔
        p.1 = X.point ∨ p.2 = Y.point := by
      constructor
      · intro h
        have he := congrArg tag h
        change (p.1=X.point ∨ p.2=Y.point) = (X.point=X.point ∨ Y.point=Y.point) at he
        exact he.mpr (Or.inl rfl)
      · intro h
        exact Quot.sound ⟨h,Or.inl rfl⟩
    have hw : IsClosed {p : X × Y | p.1=X.point ∨ p.2=Y.point} :=
      (hX.1.preimage continuous_fst).union (hY.1.preimage continuous_snd)
    have hid : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),inferInstance]
        (id : X × Y → X × Y) :=
      continuous_from_compactlyGenerated id (fun S g => g.continuous)
    have hwk : @IsClosed (X × Y) (TopologicalSpace.compactlyGenerated.{u} (X × Y))
        {p | p.1=X.point ∨ p.2=Y.point} :=
      @IsClosed.preimage (X × Y) (X × Y) (TopologicalSpace.compactlyGenerated.{u} (X × Y))
        inferInstance id hid _ hw
    have hfst : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),inferInstance]
        (Prod.fst : X × Y → X) :=
      @Continuous.comp (X × Y) (X × Y) X (TopologicalSpace.compactlyGenerated.{u} (X × Y))
        inferInstance inferInstance id Prod.fst continuous_fst hid
    have hsnd : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),inferInstance]
        (Prod.snd : X × Y → Y) :=
      @Continuous.comp (X × Y) (X × Y) Y (TopologicalSpace.compactlyGenerated.{u} (X × Y))
        inferInstance inferInstance id Prod.snd continuous_snd hid
    have hcg := compactlyGenerated_kification (X × Y)
    letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
    letI : UCompactlyGeneratedSpace.{u} (X × Y) := hcg
    letI : UCompactlyGeneratedSpace.{u} ((X × Y) × I) := cg_prod_interval (X × Y)
    have hpclosed : IsClosed ({(X.smash Y).point} : Set (X.smash Y)) := by
      apply isQuotientMap_quot_mk.isCoinducing.isClosed_preimage.mp
      change IsClosed {p : X × Y | smashPoint X Y p.1 p.2 = (X.smash Y).point}
      have he : {p : X × Y | smashPoint X Y p.1 p.2 = (X.smash Y).point} =
          {p : X × Y | p.1 = X.point ∨ p.2 = Y.point} := Set.ext hmem
      rw [he]
      exact hwk
    have hrX : Continuous (fun p : (X × Y) × I => rX (p.1.1,p.2)) :=
      rX.continuous.comp ((hfst.comp continuous_fst).prodMk continuous_snd)
    have hrY : Continuous (fun p : (X × Y) × I => rY (p.1.2,p.2)) :=
      rY.continuous.comp ((hsnd.comp continuous_fst).prodMk continuous_snd)
    let raw (p : (X × Y) × I) : (X.smash Y) × I :=
      (smashPoint X Y (rX (p.1.1,p.2)).1 (rY (p.1.2,p.2)).1,
        max (min (rX (p.1.1,p.2)).2 p.2) (min (rY (p.1.2,p.2)).2 p.2))
    have hraw : Continuous raw := by
      apply Continuous.prodMk
      · apply continuous_from_uCompactlyGeneratedSpace
        intro S g
        exact qcompact S ⟨_,hrX.fst.comp g.continuous⟩ ⟨_,hrY.fst.comp g.continuous⟩
      · exact (hrX.snd.min continuous_snd).max (hrY.snd.min continuous_snd)
    have collapsed (p : X × Y) (t : I) (hp : p.1=X.point ∨ p.2=Y.point) :
        raw (p,t) = ((X.smash Y).point,t) := by
      rcases hp with h | h
      · dsimp [raw]
        rw [h,hXp,smashPoint_base_left]
        simp
      · dsimp [raw]
        rw [h,hYp,smashPoint_base_right]
        simp
    have respects (t : I) : ∀ a b, SmashRelation X Y a b → raw (a,t)=raw (b,t) :=
      fun a b hab => (collapsed a t hab.1).trans (collapsed b t hab.2).symm
    let r : C((X.smash Y) × I,(X.smash Y) × I) :=
      ⟨fun p => Quot.lift (fun a => raw (a,p.2)) (respects p.2) p.1,by
        apply isQuotientMap_quot_mk.continuous_lift_prod_left
        exact hraw⟩
    apply wellBased_of_cylinder_retraction (X.smash Y) hpclosed r
    · intro z
      refine Quot.inductionOn z ?_
      intro p
      change raw (p,0) = _
      dsimp [raw]
      rw [hX0,hY0]
      simp [smashPoint]
    · intro t
      exact collapsed (X.point,Y.point) t (Or.inl rfl)
    · rintro ⟨z,t⟩
      refine Quot.inductionOn z ?_
      intro p
      change (raw (p,t)).2 = 0 ∨ (raw (p,t)).1 = (X.smash Y).point
      rcases hXr (p.1,t) with hx | hx
      · rcases hYr (p.2,t) with hy | hy
        · left
          dsimp [raw]
          rw [hx,hy]
          simp
        · right
          dsimp [raw]
          rw [hy,smashPoint_base_right]
      · right
        dsimp [raw]
        rw [hx,smashPoint_base_left]
  exact ⟨smash_compactlyGenerated X Y,smash_wellBased X Y hX hY⟩

open Set Metric in
/-- Construct the actual k-product CW structure, then collapse its wedge.
The chosen product CW witness also supplies the cell saturation proof. -/
private theorem smash_vertex_cw (X Y : BasedSpace.{u}) [T2Space X] [T2Space Y]
    [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
    (ix : RelCWComplex.cell (Set.univ : Set X) 0)
    (iy : RelCWComplex.cell (Set.univ : Set Y) 0)
    (hx : X.point=RelCWComplex.map 0 ix 0) (hy : Y.point=RelCWComplex.map 0 iy 0) :
    T2Space (X.smash Y) ∧ Nonempty (CWComplex (Set.univ : Set (X.smash Y))) := by
  have cw_compact_finite_closedCell {X : Type u} [TopologicalSpace X] [T2Space X]
      [CWComplex (Set.univ : Set X)] (K : Set X) (hK : IsCompact K) :
      ∃ F : Finset (Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n),
        K ⊆ ⋃ a ∈ F, RelCWComplex.closedCell a.1 a.2 := by
    classical
    let Cells := Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n
    let J : Set Cells := {a | (K ∩ RelCWComplex.openCell a.1 a.2).Nonempty}
    choose p hp using (fun a : J => a.2)
    have hlabel (a : J) (b : Cells) (h : p a ∈ RelCWComplex.openCell b.1 b.2) :
        a.1 = b := by
      by_contra hn
      exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hn) (hp a).2 h
    have hinj : Function.Injective p := by
      intro a b h
      apply Subtype.ext
      apply hlabel a b.1
      rw [h]
      exact (hp b).2
    have hclosed (T : Set X) (hT : T ⊆ Set.range p) : IsClosed T := by
      apply CWComplex.isClosed_of_isClosed_inter_openCell_or_isClosed_inter_closedCell
        (Set.subset_univ T)
      intro n hn i
      left
      have hs : (T ∩ RelCWComplex.openCell n i).Subsingleton := by
        intro x hx y hy
        obtain ⟨a,rfl⟩ := hT hx.1
        obtain ⟨b,rfl⟩ := hT hy.1
        have hab : a = b := Subtype.ext ((hlabel a ⟨n,i⟩ hx.2).trans
          (hlabel b ⟨n,i⟩ hy.2).symm)
        exact congrArg p hab
      exact hs.finite.isClosed
    have hcompact : IsCompact (Set.range p) :=
      hK.of_isClosed_subset (hclosed _ Set.Subset.rfl) (by
        rintro _ ⟨a,rfl⟩
        exact (hp a).1)
    have hdiscrete : IsDiscrete (Set.range p) :=
      isDiscrete_iff_forall_mem_exists_isClosed.mpr (by
        intro T hT
        exact ⟨T,hclosed T hT,Set.inter_eq_left.mpr hT⟩)
    have hfinite : Finite J := (Set.finite_range_iff hinj).mp (hcompact.finite hdiscrete)
    have hJ : J.Finite := Set.finite_coe_iff.mp hfinite
    refine ⟨hJ.toFinset,?_⟩
    intro x hx
    have hcover : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
        RelCWComplex.openCell n i := by
      rw [CWComplex.iUnion_openCell_eq_complex]
      trivial
    obtain ⟨n,i,hi⟩ := by simpa only [Set.mem_iUnion] using hcover
    refine Set.mem_iUnion.mpr ⟨⟨n,i⟩,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩
    · exact hJ.mem_toFinset.mpr ⟨x,hx,hi⟩
    · exact RelCWComplex.openCell_subset_closedCell n i hi
  have cw_kproduct_closed
      {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
      [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)] (F : Set (X × Y))
      (hF : ∀ n (i : RelCWComplex.cell (Set.univ : Set X) n)
        m (j : RelCWComplex.cell (Set.univ : Set Y) m),
        IsClosed ((fun p : (Metric.closedBall (0 : Fin n → ℝ) 1) ×
            (Metric.closedBall (0 : Fin m → ℝ) 1) =>
          (RelCWComplex.map n i p.1,RelCWComplex.map m j p.2)) ⁻¹' F)) :
      @IsClosed (X × Y) (TopologicalSpace.compactlyGenerated.{u} (X × Y)) F := by
    classical
    have hpiece (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
        (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set Y) m) :
        IsClosed (F ∩ (RelCWComplex.closedCell n i ×ˢ RelCWComplex.closedCell m j)) := by
      let c : C((Metric.closedBall (0 : Fin n → ℝ) 1) ×
          (Metric.closedBall (0 : Fin m → ℝ) 1),X × Y) :=
        ⟨fun p => (RelCWComplex.map n i p.1,RelCWComplex.map m j p.2),
          (RelCWComplex.continuousOn n i).restrict.prodMap
            (RelCWComplex.continuousOn m j).restrict⟩
      have hc : IsClosed (c ⁻¹' F) := hF n i m j
      have him : c '' (c ⁻¹' F) =
          F ∩ (RelCWComplex.closedCell n i ×ˢ RelCWComplex.closedCell m j) := by
        ext p
        constructor
        · rintro ⟨⟨z,w⟩,hz,rfl⟩
          exact ⟨hz,⟨z,z.2,rfl⟩,⟨w,w.2,rfl⟩⟩
        · rintro ⟨hp,⟨z,hz,hzx⟩,⟨w,hw,hwy⟩⟩
          refine ⟨(⟨z,hz⟩,⟨w,hw⟩),?_,?_⟩
          · change (RelCWComplex.map n i z,RelCWComplex.map m j w) ∈ F
            simpa only [hzx,hwy,Prod.mk.eta] using hp
          · exact Prod.ext hzx hwy
      rw [← him]
      exact (hc.isCompact.image c.continuous).isClosed
    have htest (S : CompHaus.{u}) (g : C(S,X × Y)) : IsClosed (g ⁻¹' F) := by
      have hKX : IsCompact (Set.range (fun s : S => (g s).1)) :=
        isCompact_range g.continuous.fst
      have hKY : IsCompact (Set.range (fun s : S => (g s).2)) :=
        isCompact_range g.continuous.snd
      obtain ⟨A,hA⟩ := cw_compact_finite_closedCell _ hKX
      obtain ⟨B,hB⟩ := cw_compact_finite_closedCell _ hKY
      have heq : g ⁻¹' F =
          ⋃ a ∈ A, ⋃ b ∈ B,
            g ⁻¹' (F ∩ (RelCWComplex.closedCell a.1 a.2 ×ˢ
              RelCWComplex.closedCell b.1 b.2)) := by
        ext s
        constructor
        · intro hs
          have hx := hA (show (g s).1 ∈ Set.range (fun t : S => (g t).1) from ⟨s,rfl⟩)
          have hy := hB (show (g s).2 ∈ Set.range (fun t : S => (g t).2) from ⟨s,rfl⟩)
          obtain ⟨a,ha,hsa⟩ := by simpa only [Set.mem_iUnion,exists_prop] using hx
          obtain ⟨b,hb,hsb⟩ := by simpa only [Set.mem_iUnion,exists_prop] using hy
          exact Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨ha,Set.mem_iUnion.mpr
            ⟨b,Set.mem_iUnion.mpr ⟨hb,hs,hsa,hsb⟩⟩⟩⟩
        · intro hs
          obtain ⟨a,ha,b,hb,h⟩ := by simpa only [Set.mem_iUnion,exists_prop] using hs
          exact h.1
      rw [heq]
      apply isClosed_biUnion_finset
      intro a ha
      apply isClosed_biUnion_finset
      intro b hb
      exact (hpiece a.1 a.2 b.1 b.2).preimage g.continuous
    change @IsClosed (X × Y) (TopologicalSpace.coinduced
      (fun p : (Σ i : (S : CompHaus.{u}) × C(S,X × Y), i.fst) => p.1.2 p.2)
      inferInstance) F
    rw [isClosed_coinduced]
    apply isClosed_sigma_iff.mpr
    rintro ⟨S,g⟩
    exact htest S g
  have partialEquiv_isEmbedding_source {α : Type} {β : Type u}
      [TopologicalSpace α] [TopologicalSpace β] (e : PartialEquiv α β)
      (hf : ContinuousOn e e.source) (hg : ContinuousOn e.symm e.target) :
      IsEmbedding (fun x : e.source => e x.1) := by
    let E : e.source ≃ₜ e.target :=
      { toEquiv := e.toEquiv
        continuous_toFun := hf.restrict.subtype_mk _
        continuous_invFun := hg.restrict.subtype_mk _ }
    exact IsEmbedding.subtypeVal.comp E.isEmbedding
  have cw_cell_isEmbedding (X : Type u) [TopologicalSpace X]
      [CWComplex (Set.univ : Set X)] (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n) :
      IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 => RelCWComplex.map n i x.1) := by
    have h := partialEquiv_isEmbedding_source (RelCWComplex.map n i)
      ((RelCWComplex.continuousOn n i).mono (by rw [RelCWComplex.source_eq]; exact Metric.ball_subset_closedBall))
      (RelCWComplex.continuousOn_symm n i)
    exact h.comp (Homeomorph.setCongr (RelCWComplex.source_eq n i)).symm.isEmbedding
  have cw_product_characteristic
      {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
      (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
      (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set Y) m) :
      let f (z : Fin (n+m) → ℝ) : X × Y :=
        (RelCWComplex.map n i (fun a => z (Fin.castAdd m a)),
          RelCWComplex.map m j (fun b => z (Fin.natAdd n b)))
      ContinuousOn f (Metric.closedBall 0 1) ∧
        f '' Metric.closedBall 0 1 =
          RelCWComplex.closedCell n i ×ˢ RelCWComplex.closedCell m j ∧
        f '' Metric.ball 0 1 =
          RelCWComplex.openCell n i ×ˢ RelCWComplex.openCell m j ∧
        InjOn f (Metric.ball 0 1) := by
    classical
    dsimp only
    let f (z : Fin (n+m) → ℝ) : X × Y :=
      (RelCWComplex.map n i (fun a => z (Fin.castAdd m a)),
        RelCWComplex.map m j (fun b => z (Fin.natAdd n b)))
    change ContinuousOn f (Metric.closedBall 0 1) ∧
      f '' Metric.closedBall 0 1 =
        RelCWComplex.closedCell n i ×ˢ RelCWComplex.closedCell m j ∧
      f '' Metric.ball 0 1 =
        RelCWComplex.openCell n i ×ˢ RelCWComplex.openCell m j ∧
      InjOn f (Metric.ball 0 1)
    have hc (k : ℕ) (v : Fin k → ℝ) :
        v ∈ Metric.closedBall 0 1 ↔ ∀ a, -1 ≤ v a ∧ v a ≤ 1 := by
      rw [closedBall_pi _ (by norm_num : (0:ℝ) ≤ 1)]
      simp [Real.closedBall_eq_Icc,Pi.le_def,forall_and]
    have hb (k : ℕ) (v : Fin k → ℝ) :
        v ∈ Metric.ball 0 1 ↔ ∀ a, -1 < v a ∧ v a < 1 := by
      rw [ball_pi _ (by norm_num : (0:ℝ) < 1)]
      simp only [Set.mem_pi,Set.mem_univ,forall_const,Real.ball_eq_Ioo,Pi.zero_apply,
        zero_sub,zero_add,Set.mem_Ioo]
    have hcl : MapsTo (fun z : Fin (n+m) → ℝ => fun a => z (Fin.castAdd m a))
        (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
      intro z hz
      exact (hc _ _).mpr (fun a => (hc _ _).mp hz (Fin.castAdd m a))
    have hcr : MapsTo (fun z : Fin (n+m) → ℝ => fun b => z (Fin.natAdd n b))
        (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
      intro z hz
      exact (hc _ _).mpr (fun b => (hc _ _).mp hz (Fin.natAdd n b))
    have hbl : MapsTo (fun z : Fin (n+m) → ℝ => fun a => z (Fin.castAdd m a))
        (Metric.ball 0 1) (Metric.ball 0 1) := by
      intro z hz
      exact (hb _ _).mpr (fun a => (hb _ _).mp hz (Fin.castAdd m a))
    have hbr : MapsTo (fun z : Fin (n+m) → ℝ => fun b => z (Fin.natAdd n b))
        (Metric.ball 0 1) (Metric.ball 0 1) := by
      intro z hz
      exact (hb _ _).mpr (fun b => (hb _ _).mp hz (Fin.natAdd n b))
    refine ⟨?_,?_,?_,?_⟩
    · exact ((RelCWComplex.continuousOn n i).comp
        ((continuous_pi (fun a => continuous_apply (Fin.castAdd m a))).continuousOn) hcl).prodMk
        ((RelCWComplex.continuousOn m j).comp
          ((continuous_pi (fun b => continuous_apply (Fin.natAdd n b))).continuousOn) hcr)
    · ext p
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact ⟨⟨_,hcl hz,rfl⟩,⟨_,hcr hz,rfl⟩⟩
      · rintro ⟨⟨v,hv,hvx⟩,⟨w,hw,hwy⟩⟩
        refine ⟨Fin.append v w,?_,?_⟩
        · apply (hc _ _).mpr
          intro a
          induction a using Fin.addCases with
          | left a => simpa only [Fin.append_left] using (hc _ _).mp hv a
          | right b => simpa only [Fin.append_right] using (hc _ _).mp hw b
        · simpa only [f,Fin.append_left,Fin.append_right] using Prod.ext hvx hwy
    · ext p
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact ⟨⟨_,hbl hz,rfl⟩,⟨_,hbr hz,rfl⟩⟩
      · rintro ⟨⟨v,hv,hvx⟩,⟨w,hw,hwy⟩⟩
        refine ⟨Fin.append v w,?_,?_⟩
        · apply (hb _ _).mpr
          intro a
          induction a using Fin.addCases with
          | left a => simpa only [Fin.append_left] using (hb _ _).mp hv a
          | right b => simpa only [Fin.append_right] using (hb _ _).mp hw b
        · simpa only [f,Fin.append_left,Fin.append_right] using Prod.ext hvx hwy
    · intro v hv w hw heq
      have hl : (fun a => v (Fin.castAdd m a)) = (fun a => w (Fin.castAdd m a)) :=
        (RelCWComplex.map n i).injOn
          (by rw [RelCWComplex.source_eq]; exact hbl hv)
          (by rw [RelCWComplex.source_eq]; exact hbl hw) (congrArg Prod.fst heq)
      have hr : (fun b => v (Fin.natAdd n b)) = (fun b => w (Fin.natAdd n b)) :=
        (RelCWComplex.map m j).injOn
          (by rw [RelCWComplex.source_eq]; exact hbr hv)
          (by rw [RelCWComplex.source_eq]; exact hbr hw) (congrArg Prod.snd heq)
      ext a
      induction a using Fin.addCases with
      | left a => exact congrFun hl a
      | right b => exact congrFun hr b
  have cw_product_boundary
      {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
      (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
      (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set Y) m) :
      let f (z : Fin (n+m) → ℝ) : X × Y :=
        (RelCWComplex.map n i (fun a => z (Fin.castAdd m a)),
          RelCWComplex.map m j (fun b => z (Fin.natAdd n b)))
      ∃ A : Finset (Σ a, RelCWComplex.cell (Set.univ : Set X) a),
      ∃ B : Finset (Σ b, RelCWComplex.cell (Set.univ : Set Y) b),
        (∀ a ∈ A, a.1 < n) ∧ (∀ b ∈ B, b.1 < m) ∧
        MapsTo f (Metric.sphere 0 1)
          ((⋃ a ∈ A, RelCWComplex.closedCell a.1 a.2 ×ˢ RelCWComplex.closedCell m j) ∪
            ⋃ b ∈ B, RelCWComplex.closedCell n i ×ˢ RelCWComplex.closedCell b.1 b.2) := by
    classical
    dsimp only
    let f (z : Fin (n+m) → ℝ) : X × Y :=
      (RelCWComplex.map n i (fun a => z (Fin.castAdd m a)),
        RelCWComplex.map m j (fun b => z (Fin.natAdd n b)))
    change ∃ A : Finset (Σ a, RelCWComplex.cell (Set.univ : Set X) a),
      ∃ B : Finset (Σ b, RelCWComplex.cell (Set.univ : Set Y) b),
        (∀ a ∈ A, a.1 < n) ∧ (∀ b ∈ B, b.1 < m) ∧
        MapsTo f (Metric.sphere 0 1)
          ((⋃ a ∈ A, RelCWComplex.closedCell a.1 a.2 ×ˢ RelCWComplex.closedCell m j) ∪
            ⋃ b ∈ B, RelCWComplex.closedCell n i ×ˢ RelCWComplex.closedCell b.1 b.2)
    have hc (k : ℕ) (v : Fin k → ℝ) :
        v ∈ Metric.closedBall 0 1 ↔ ∀ a, -1 ≤ v a ∧ v a ≤ 1 := by
      rw [closedBall_pi _ (by norm_num : (0:ℝ) ≤ 1)]
      simp [Real.closedBall_eq_Icc,Pi.le_def,forall_and]
    have hb (k : ℕ) (v : Fin k → ℝ) :
        v ∈ Metric.ball 0 1 ↔ ∀ a, -1 < v a ∧ v a < 1 := by
      rw [ball_pi _ (by norm_num : (0:ℝ) < 1)]
      simp only [Set.mem_pi,Set.mem_univ,forall_const,Real.ball_eq_Ioo,Pi.zero_apply,
        zero_sub,zero_add,Set.mem_Ioo]
    obtain ⟨J,hJ⟩ := CWComplex.mapsTo (C := (Set.univ : Set X)) n i
    obtain ⟨K,hK⟩ := CWComplex.mapsTo (C := (Set.univ : Set Y)) m j
    refine ⟨(Finset.range n).sigma J,(Finset.range m).sigma K,?_,?_,?_⟩
    · intro a ha
      exact Finset.mem_range.mp (Finset.mem_sigma.mp ha).1
    · intro b hb
      exact Finset.mem_range.mp (Finset.mem_sigma.mp hb).1
    · intro z hz
      have hzclosed : z ∈ Metric.closedBall 0 1 := Metric.sphere_subset_closedBall hz
      have hcl : (fun a => z (Fin.castAdd m a)) ∈ Metric.closedBall 0 1 :=
        (hc _ _).mpr (fun a => (hc _ _).mp hzclosed (Fin.castAdd m a))
      have hcr : (fun b => z (Fin.natAdd n b)) ∈ Metric.closedBall 0 1 :=
        (hc _ _).mpr (fun b => (hc _ _).mp hzclosed (Fin.natAdd n b))
      have hs : (fun a => z (Fin.castAdd m a)) ∈ Metric.sphere 0 1 ∨
          (fun b => z (Fin.natAdd n b)) ∈ Metric.sphere 0 1 := by
        by_cases hl : (fun a => z (Fin.castAdd m a)) ∈ Metric.ball 0 1
        · right
          rw [← Metric.closedBall_sdiff_ball]
          refine ⟨hcr,?_⟩
          intro hr
          have hball : z ∈ Metric.ball 0 1 := by
            apply (hb _ _).mpr
            intro a
            induction a using Fin.addCases with
            | left a => exact (hb _ _).mp hl a
            | right b => exact (hb _ _).mp hr b
          exact Metric.sphere_disjoint_ball.le_bot ⟨hz,hball⟩
        · left
          rw [← Metric.closedBall_sdiff_ball]
          exact ⟨hcl,hl⟩
      rcases hs with hl | hr
      · left
        have hh := hJ hl
        simp only [Set.mem_iUnion,exists_prop] at hh ⊢
        obtain ⟨a,ha,k,hk,hcell⟩ := hh
        exact ⟨⟨a,k⟩,Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr ha,hk⟩,
          hcell,⟨_,hcr,rfl⟩⟩
      · right
        have hh := hK hr
        simp only [Set.mem_iUnion,exists_prop] at hh ⊢
        obtain ⟨b,hb,k,hk,hcell⟩ := hh
        exact ⟨⟨b,k⟩,Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hb,hk⟩,
          ⟨_,hcl,rfl⟩,hcell⟩
  have cw_kproduct_compact_map {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      {D : Type} [TopologicalSpace D] [CompactSpace D] [T2Space D] (f : C(D,X × Y)) :
      @Continuous D (X × Y) inferInstance (TopologicalSpace.compactlyGenerated.{u} (X × Y)) f := by
    let S : CompHaus.{u} := CompHaus.of (ULift.{u} D)
    let g : C(S,X × Y) := ⟨fun z => f z.down,f.continuous.comp continuous_uliftDown⟩
    apply (@continuous_iff_isClosed D (X × Y) inferInstance
      (TopologicalSpace.compactlyGenerated.{u} (X × Y)) f).mpr
    intro F hF
    change @IsClosed (X × Y) (TopologicalSpace.coinduced
      (fun p : (Σ i : (S : CompHaus.{u}) × C(S,X × Y), i.fst) => p.1.2 p.2)
      inferInstance) F at hF
    rw [isClosed_coinduced,isClosed_sigma_iff] at hF
    exact (hF ⟨S,g⟩).preimage continuous_uliftUp
  have cw_kproduct_chart_isEmbedding
      {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
      (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
      (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set Y) m) :
      @IsEmbedding (Metric.ball (0 : Fin (n+m) → ℝ) 1) (X × Y)
        inferInstance (TopologicalSpace.compactlyGenerated.{u} (X × Y))
        (fun z : Metric.ball (0 : Fin (n+m) → ℝ) 1 =>
        (RelCWComplex.map n i (fun a => z.1 (Fin.castAdd m a)),
          RelCWComplex.map m j (fun b => z.1 (Fin.natAdd n b)))) := by
    let f (z : Fin (n+m) → ℝ) : X × Y :=
      (RelCWComplex.map n i (fun a => z (Fin.castAdd m a)),
        RelCWComplex.map m j (fun b => z (Fin.natAdd n b)))
    have hb (k : ℕ) (z : Fin k → ℝ) :
        z ∈ Metric.ball 0 1 ↔ ∀ a, -1 < z a ∧ z a < 1 := by
      rw [ball_pi _ (by norm_num : (0:ℝ) < 1)]
      simp only [Set.mem_pi,Set.mem_univ,forall_const,Real.ball_eq_Ioo,Pi.zero_apply,
        zero_sub,zero_add,Set.mem_Ioo]
    have hc (k : ℕ) (z : Fin k → ℝ) :
        z ∈ Metric.closedBall 0 1 ↔ ∀ a, -1 ≤ z a ∧ z a ≤ 1 := by
      rw [closedBall_pi _ (by norm_num : (0:ℝ) ≤ 1)]
      simp [Real.closedBall_eq_Icc,Pi.le_def,forall_and]
    let b : Metric.ball (0 : Fin (n+m) → ℝ) 1 →
        (Metric.ball (0 : Fin n → ℝ) 1) × (Metric.ball (0 : Fin m → ℝ) 1) := fun z =>
      (⟨fun a => z.1 (Fin.castAdd m a),(hb _ _).mpr (fun a => (hb _ _).mp z.2 _)⟩,
       ⟨fun a => z.1 (Fin.natAdd n a),(hb _ _).mpr (fun a => (hb _ _).mp z.2 _)⟩)
    have hbcont : Continuous b := by
      apply Continuous.prodMk
      · apply Continuous.subtype_mk
        exact continuous_pi fun a => (continuous_apply (Fin.castAdd m a)).comp continuous_subtype_val
      · apply Continuous.subtype_mk
        exact continuous_pi fun a => (continuous_apply (Fin.natAdd n a)).comp continuous_subtype_val
    let G : (Metric.ball (0 : Fin n → ℝ) 1) × (Metric.ball (0 : Fin m → ℝ) 1) →
        (Fin (n+m) → ℝ) := fun p => Fin.append p.1.1 p.2.1
    have hG : Continuous G := by
      apply continuous_pi
      intro a
      induction a using Fin.addCases
      · rename_i a
        simp only [G, Fin.append_left]
        exact (continuous_apply a).comp (continuous_subtype_val.comp continuous_fst)
      · rename_i a
        simp only [G, Fin.append_right]
        exact (continuous_apply a).comp (continuous_subtype_val.comp continuous_snd)
    have hGb : G ∘ b = Subtype.val := by
      funext z
      exact Fin.append_castAdd_natAdd
    have hbemb : IsEmbedding b :=
      IsEmbedding.of_comp hbcont hG (hGb.symm ▸ IsEmbedding.subtypeVal)
    have hOrd : IsEmbedding (fun z : Metric.ball (0 : Fin (n+m) → ℝ) 1 => f z.1) :=
      ((cw_cell_isEmbedding X n i).prodMap (cw_cell_isEmbedding Y m j)).comp hbemb
    have hf : ContinuousOn f (Metric.closedBall 0 1) := by
      apply ContinuousOn.prodMk
      · apply (RelCWComplex.continuousOn n i).comp
          (continuous_pi fun a => continuous_apply (Fin.castAdd m a)).continuousOn
        intro z hz
        exact (hc _ _).mpr (fun a => (hc _ _).mp hz _)
      · apply (RelCWComplex.continuousOn m j).comp
          (continuous_pi fun a => continuous_apply (Fin.natAdd n a)).continuousOn
        intro z hz
        exact (hc _ _).mpr (fun a => (hc _ _).mp hz _)
    have hclosed : @Continuous (Metric.closedBall (0 : Fin (n+m) → ℝ) 1) (X × Y)
        inferInstance (TopologicalSpace.compactlyGenerated.{u} (X × Y)) (fun z => f z.1) :=
      cw_kproduct_compact_map ⟨_,hf.restrict⟩
    have hk : @Continuous (Metric.ball (0 : Fin (n+m) → ℝ) 1) (X × Y)
        inferInstance (TopologicalSpace.compactlyGenerated.{u} (X × Y)) (fun z => f z.1) :=
      @Continuous.comp _ _ _ inferInstance inferInstance
        (TopologicalSpace.compactlyGenerated.{u} (X × Y)) _ _ hclosed
        (continuous_subtype_val.subtype_mk (fun z => Metric.ball_subset_closedBall z.2))
    have hforget : @Continuous (X × Y) (X × Y)
        (TopologicalSpace.compactlyGenerated.{u} (X × Y)) instTopologicalSpaceProd id :=
      continuous_from_compactlyGenerated id (fun _ g => g.continuous)
    exact @IsEmbedding.of_comp _ _ _ _ id inferInstance
      (TopologicalSpace.compactlyGenerated.{u} (X × Y)) instTopologicalSpaceProd hk hforget hOrd
  have cw_kproduct_chart_family
      {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)] :
      let cells (k : ℕ) := {p : (Σ n, RelCWComplex.cell (Set.univ : Set X) n) ×
        (Σ m, RelCWComplex.cell (Set.univ : Set Y) m) // p.1.1 + p.2.1 = k}
      letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
      ∃ c : ∀ k, cells k → PartialEquiv (Fin k → ℝ) (X × Y),
        (∀ k a, (c k a).source = Metric.ball 0 1) ∧
        (∀ k a, ContinuousOn (c k a) (Metric.closedBall 0 1)) ∧
        (∀ k a, ContinuousOn (c k a).symm (c k a).target) ∧
        (∀ k a, c k a '' Metric.ball 0 1 =
          RelCWComplex.openCell a.1.1.1 a.1.1.2 ×ˢ RelCWComplex.openCell a.1.2.1 a.1.2.2) ∧
        (∀ k a, c k a '' Metric.closedBall 0 1 =
          RelCWComplex.closedCell a.1.1.1 a.1.1.2 ×ˢ RelCWComplex.closedCell a.1.2.1 a.1.2.2) ∧
        (∀ n i m j z, c (n+m) ⟨(⟨n,i⟩,⟨m,j⟩),rfl⟩ z =
          (RelCWComplex.map n i (fun a => z (Fin.castAdd m a)),
            RelCWComplex.map m j (fun b => z (Fin.natAdd n b)))) := by
    classical
    let cells (k : ℕ) := {p : (Σ n, RelCWComplex.cell (Set.univ : Set X) n) ×
        (Σ m, RelCWComplex.cell (Set.univ : Set Y) m) // p.1.1 + p.2.1 = k}
    let f (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
        (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set Y) m) (z : Fin (n+m) → ℝ) :=
      (RelCWComplex.map n i (fun a => z (Fin.castAdd m a)),
        RelCWComplex.map m j (fun b => z (Fin.natAdd n b)))
    have hchar := @cw_product_characteristic X Y _ _ _ _
    have hE := @cw_kproduct_chart_isEmbedding X Y _ _ _ _
    have hcont (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
        (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set Y) m) :
        @Continuous (Metric.closedBall (0 : Fin (n+m) → ℝ) 1) (X × Y) inferInstance
          (TopologicalSpace.compactlyGenerated.{u} (X × Y)) (fun z => f n i m j z.1) :=
      cw_kproduct_compact_map ⟨_,(hchar n i m j).1.restrict⟩
    letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
    let e (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
        (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set Y) m) :=
      (hchar n i m j).2.2.2.toPartialEquiv (f n i m j) (Metric.ball 0 1)
    let c (k : ℕ) (a : cells k) : PartialEquiv (Fin k → ℝ) (X × Y) := by
      rcases a with ⟨⟨⟨n,i⟩,⟨m,j⟩⟩,h⟩
      subst k
      exact e n i m j
    change ∃ c : ∀ k, cells k → PartialEquiv (Fin k → ℝ) (X × Y), _
    refine ⟨c,?_,?_,?_,?_,?_,?_⟩
    · rintro k ⟨⟨⟨n,i⟩,⟨m,j⟩⟩,h⟩
      subst k
      rfl
    · rintro k ⟨⟨⟨n,i⟩,⟨m,j⟩⟩,h⟩
      subst k
      exact continuousOn_iff_continuous_restrict.mpr (hcont n i m j)
    · rintro k ⟨⟨⟨n,i⟩,⟨m,j⟩⟩,h⟩
      subst k
      change ContinuousOn (e n i m j).symm (e n i m j).target
      let E := e n i m j
      have hi : IsEmbedding (fun x : E.source => E x.1) := hE n i m j
      let inv : E.target → E.source := fun y => ⟨E.symm y.1,E.map_target y.2⟩
      have hv : Continuous inv := hi.continuous_iff.mpr (by
        convert (continuous_subtype_val : Continuous (fun y : E.target => y.1)) using 1
        apply funext
        intro y
        exact E.right_inv y.2)
      exact continuousOn_iff_continuous_restrict.mpr (continuous_subtype_val.comp hv)
    · rintro k ⟨⟨⟨n,i⟩,⟨m,j⟩⟩,h⟩
      subst k
      exact (hchar n i m j).2.2.1
    · rintro k ⟨⟨⟨n,i⟩,⟨m,j⟩⟩,h⟩
      subst k
      exact (hchar n i m j).2.1
    · intro n i m j z
      rfl
  have cw_kproduct {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      [T2Space X] [T2Space Y]
      [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)] :
      letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
      ∃ H : CWComplex (Set.univ : Set (X × Y)),
        letI := H
        ∀ k (a : RelCWComplex.cell (Set.univ : Set (X × Y)) k),
          ∃ (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
            (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set Y) m),
            k = n+m ∧ RelCWComplex.openCell k a =
              RelCWComplex.openCell n i ×ˢ RelCWComplex.openCell m j := by
    classical
    let CX := Σ n, RelCWComplex.cell (Set.univ : Set X) n
    let CY := Σ m, RelCWComplex.cell (Set.univ : Set Y) m
    let cells (k : ℕ) := {p : CX × CY // p.1.1+p.2.1=k}
    have hboundary := @cw_product_boundary X Y _ _ _ _
    have hcrit := @cw_kproduct_closed X Y _ _ _ _ _ _
    have hcont (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
        (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set Y) m) :
        @Continuous ((Metric.closedBall (0 : Fin n → ℝ) 1) ×
          (Metric.closedBall (0 : Fin m → ℝ) 1)) (X × Y) inferInstance
          (TopologicalSpace.compactlyGenerated.{u} (X × Y))
          (fun z => (RelCWComplex.map n i z.1.1,RelCWComplex.map m j z.2.1)) :=
      cw_kproduct_compact_map ⟨_,
        ((RelCWComplex.continuousOn n i).restrict.comp continuous_fst).prodMk
        ((RelCWComplex.continuousOn m j).restrict.comp continuous_snd)⟩
    obtain ⟨c,hsource,hcontinuous,hinverse,hopen,hclosed,hformula⟩ :=
      @cw_kproduct_chart_family X Y _ _ _ _
    letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
    change (∀ k (a : cells k), (c k a).source=Metric.ball 0 1) at hsource
    let label (a : Σ k, cells k) : CX × CY := a.2.1
    have hlabel : Function.Injective label := by
      rintro ⟨k,⟨p,hp⟩⟩ ⟨l,⟨q,hq⟩⟩ h
      change p=q at h
      subst q
      subst k
      subst l
      rfl
    let idx (p : CX × CY) : Σ k, cells k := ⟨p.1.1+p.2.1,⟨p,rfl⟩⟩
    let H : CWComplex (Set.univ : Set (X × Y)) := {
      cell := cells
      map := c
      source_eq := hsource
      continuousOn := hcontinuous
      continuousOn_symm := hinverse
      pairwiseDisjoint' := by
        rintro a _ b _ hab
        change Disjoint (c a.1 a.2 '' Metric.ball 0 1)
          (c b.1 b.2 '' Metric.ball 0 1)
        rw [hopen,hopen]
        apply Set.disjoint_left.mpr
        intro z hza hzb
        apply hab
        apply hlabel
        apply Prod.ext
        · by_contra h
          exact (RelCWComplex.disjoint_openCell_of_ne h).le_bot ⟨hza.1,hzb.1⟩
        · by_contra h
          exact (RelCWComplex.disjoint_openCell_of_ne h).le_bot ⟨hza.2,hzb.2⟩
      mapsTo' := by
        rintro k ⟨⟨⟨n,i⟩,⟨m,j⟩⟩,h⟩
        subst k
        obtain ⟨A,B,hA,hB,hmap⟩ := hboundary n i m j
        let F : Finset (Σ k, cells k) :=
          A.image (fun a => idx (a,⟨m,j⟩)) ∪ B.image (fun b => idx (⟨n,i⟩,b))
        let L (k : ℕ) : Finset (cells k) := F.preimage (Sigma.mk k) sigma_mk_injective.injOn
        refine ⟨L,?_⟩
        intro z hz
        rw [hformula]
        rcases hmap hz with hleft | hright
        · obtain ⟨a,ha,hz⟩ := by simpa only [Set.mem_iUnion,exists_prop] using hleft
          refine Set.mem_iUnion.mpr ⟨a.1+m,Set.mem_iUnion.mpr ⟨Nat.add_lt_add_right (hA a ha) m,
            Set.mem_iUnion.mpr ⟨⟨(a,⟨m,j⟩),rfl⟩,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩⟩⟩
          · apply Finset.mem_preimage.mpr
            exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
          · rw [hclosed]
            exact hz
        · obtain ⟨b,hb,hz⟩ := by simpa only [Set.mem_iUnion,exists_prop] using hright
          refine Set.mem_iUnion.mpr ⟨n+b.1,Set.mem_iUnion.mpr ⟨Nat.add_lt_add_left (hB b hb) n,
            Set.mem_iUnion.mpr ⟨⟨(⟨n,i⟩,b),rfl⟩,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩⟩⟩
          · apply Finset.mem_preimage.mpr
            exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
          · rw [hclosed]
            exact hz
      closed' := by
        intro A _ hA
        apply hcrit A
        intro n i m j
        have hmem (z : (Metric.closedBall (0 : Fin n → ℝ) 1) ×
            (Metric.closedBall (0 : Fin m → ℝ) 1)) :
            (RelCWComplex.map n i z.1.1,RelCWComplex.map m j z.2.1) ∈
              c (n+m) ⟨(⟨n,i⟩,⟨m,j⟩),rfl⟩ '' Metric.closedBall 0 1 := by
          rw [hclosed]
          exact ⟨⟨z.1.1,z.1.2,rfl⟩,⟨z.2.1,z.2.2,rfl⟩⟩
        have hh := (hA (n+m) ⟨(⟨n,i⟩,⟨m,j⟩),rfl⟩).preimage (hcont n i m j)
        convert hh using 1
        ext z
        exact ⟨fun h => ⟨h,hmem z⟩,fun h => h.1⟩
      union' := by
        apply Set.eq_univ_of_forall
        rintro ⟨x,y⟩
        have hx : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
            RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
        have hy : y ∈ ⋃ m : ℕ, ⋃ j : RelCWComplex.cell (Set.univ : Set Y) m,
            RelCWComplex.closedCell m j := by rw [CWComplex.union]; trivial
        obtain ⟨n,i,hx⟩ := by simpa only [Set.mem_iUnion] using hx
        obtain ⟨m,j,hy⟩ := by simpa only [Set.mem_iUnion] using hy
        refine Set.mem_iUnion.mpr ⟨n+m,Set.mem_iUnion.mpr ⟨⟨(⟨n,i⟩,⟨m,j⟩),rfl⟩,?_⟩⟩
        rw [hclosed]
        exact ⟨hx,hy⟩ }
    refine ⟨H,?_⟩
    rintro k ⟨⟨⟨n,i⟩,⟨m,j⟩⟩,h⟩
    refine ⟨n,i,m,j,h.symm,?_⟩
    exact hopen k ⟨(⟨n,i⟩,⟨m,j⟩),h⟩
  have cw_collapse (X : Type u) [TopologicalSpace X] [T2Space X]
      [CWComplex (Set.univ : Set X)] (C : Set X) (c : X) (hc : c ∈ C)
      (hC : IsClosed C)
      (hcell : ∀ n (i : RelCWComplex.cell (Set.univ : Set X) n),
        RelCWComplex.openCell n i ⊆ C ∨ Disjoint (RelCWComplex.openCell n i) C) :
      let R (x y : X) : Prop := x ∈ C ∧ y ∈ C
      T2Space (Quot R) → Nonempty (CWComplex (Set.univ : Set (Quot R))) := by
    classical
    dsimp only
    let R (x y : X) : Prop := x ∈ C ∧ y ∈ C
    intro hT
    letI : T2Space (Quot R) := hT
    let q : X → Quot R := Quot.mk R
    have heq (x y : X) : q x=q y ↔ x=y ∨ (x ∈ C ∧ y ∈ C) := by
      constructor
      · intro h
        have h' := Quot.eqvGen_exact h
        clear h
        induction h' with
        | rel a b h => exact Or.inr h
        | refl a => exact Or.inl rfl
        | symm a b _ ih => exact ih.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.2,h.1⟩)
        | trans a b c _ _ ih₁ ih₂ =>
          rcases ih₁ with rfl | h₁
          · exact ih₂
          · rcases ih₂ with rfl | h₂
            · exact Or.inr h₁
            · exact Or.inr ⟨h₁.1,h₂.2⟩
      · rintro (rfl | h)
        · rfl
        · exact Quot.sound h
    have hbase (x : X) (hx : x ∈ C) : q x=q c := Quot.sound ⟨hx,hc⟩
    have hopen : IsOpenEmbedding (fun x : (Cᶜ : Set X) => q x.1) := by
      apply IsOpenEmbedding.of_continuous_injective_isOpenMap
      · exact continuous_quot_mk.comp continuous_subtype_val
      · intro x y h
        apply Subtype.ext
        rcases (heq x y).mp h with h | h
        · exact h
        · exact False.elim (x.2 h.1)
      · intro S hS
        have hV : IsOpen (Subtype.val '' S : Set X) := hC.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap S hS
        apply isQuotientMap_quot_mk.isOpen_preimage.mp
        convert hV using 1
        ext x
        constructor
        · rintro ⟨y,hy,he⟩
          rcases (heq y.1 x).mp he with rfl | h
          · exact ⟨y,hy,rfl⟩
          · exact False.elim (y.2 h.1)
        · rintro ⟨y,hy,rfl⟩
          exact ⟨y,hy,rfl⟩
    let K (n : ℕ) := {i : RelCWComplex.cell (Set.univ : Set X) n // ¬ RelCWComplex.openCell n i ⊆ C}
    have hdisj (n : ℕ) (i : K n) : Disjoint (RelCWComplex.openCell n i.1) C :=
      (hcell n i.1).resolve_left i.2
    have hclosed (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
        (hi : RelCWComplex.openCell n i ⊆ C) : RelCWComplex.closedCell n i ⊆ C := by
      rw [← RelCWComplex.closure_openCell_eq_closedCell]
      exact hC.closure_subset_iff.mpr hi
    let raw (n : ℕ) (i : K n) (z : Fin n → ℝ) : Quot R := q (RelCWComplex.map n i.1 z)
    have hemb (n : ℕ) (i : K n) : IsEmbedding (fun z : ball (0 : Fin n → ℝ) 1 => raw n i z) := by
      let e := RelCWComplex.map n i.1
      let E : e.source ≃ₜ e.target :=
        { toEquiv := e.toEquiv
          continuous_toFun := ((RelCWComplex.continuousOn n i.1).mono
            (by rw [RelCWComplex.source_eq]; exact ball_subset_closedBall)).restrict.subtype_mk _
          continuous_invFun := (RelCWComplex.continuousOn_symm n i.1).restrict.subtype_mk _ }
      have he : IsEmbedding (fun z : ball (0 : Fin n → ℝ) 1 => RelCWComplex.map n i.1 z.1) := by
        exact (IsEmbedding.subtypeVal.comp E.isEmbedding).comp
          (Homeomorph.setCongr (RelCWComplex.source_eq n i.1)).symm.isEmbedding
      have hout (z : ball (0 : Fin n → ℝ) 1) : RelCWComplex.map n i.1 z.1 ∈ Cᶜ := by
        intro h
        exact Set.disjoint_left.mp (hdisj n i) ⟨z,z.2,rfl⟩ h
      exact hopen.isEmbedding.comp (he.codRestrict Cᶜ hout)
    have hinj (n : ℕ) (i : K n) : InjOn (raw n i) (ball 0 1) := by
      intro x hx y hy h
      have he : (⟨x,hx⟩ : ball (0 : Fin n → ℝ) 1)=⟨y,hy⟩ := (hemb n i).injective h
      exact congrArg Subtype.val he
    let kept (n : ℕ) (i : K n) : PartialEquiv (Fin n → ℝ) (Quot R) :=
      (hinj n i).toPartialEquiv (raw n i) (ball 0 1)
    have kept_inv (n : ℕ) (i : K n) : ContinuousOn (kept n i).symm (kept n i).target := by
      let e := kept n i
      let inv : e.target → e.source := fun y => ⟨e.symm y.1,e.map_target y.2⟩
      have hi : Continuous inv := (hemb n i).continuous_iff.mpr (by
        convert (continuous_subtype_val : Continuous (fun y : e.target => y.1)) using 1
        ext y
        exact e.right_inv y.2)
      exact continuousOn_iff_continuous_restrict.mpr (continuous_subtype_val.comp hi)
    let cells : ℕ → Type u
      | 0 => Option (K 0)
      | n+1 => K (n+1)
    let incl : ∀ n, K n → cells n
      | 0,i => some i
      | _+1,i => i
    let chart : ∀ n, cells n → PartialEquiv (Fin n → ℝ) (Quot R)
      | 0,none =>
        { toFun := fun _ => q c
          invFun := fun _ => 0
          source := ball 0 1
          target := {q c}
          map_source' := by intro _ _; rfl
          map_target' := by intro _ _; simp
          left_inv' := by intro _ _; exact Subsingleton.elim _ _
          right_inv' := by intro _ h; exact h.symm }
      | 0,some i => kept 0 i
      | n+1,i => kept (n+1) i
    have hinc (n : ℕ) (i : K n) : chart n (incl n i)=kept n i := by cases n <;> rfl
    have hco (n : ℕ) (i : K n) : chart n (incl n i) '' ball 0 1 = q '' RelCWComplex.openCell n i.1 := by
      rw [hinc]
      change (fun z => q (RelCWComplex.map n i.1 z)) '' _ = q '' (RelCWComplex.map n i.1 '' _)
      exact (Set.image_image _ _ _).symm
    have hcc (n : ℕ) (i : K n) : chart n (incl n i) '' closedBall 0 1 = q '' RelCWComplex.closedCell n i.1 := by
      rw [hinc]
      change (fun z => q (RelCWComplex.map n i.1 z)) '' _ = q '' (RelCWComplex.map n i.1 '' _)
      exact (Set.image_image _ _ _).symm
    have hvo : chart 0 none '' ball 0 1 = {q c} :=
      (Metric.nonempty_ball.mpr zero_lt_one).image_const (q c)
    have hvc : chart 0 none '' closedBall 0 1 = {q c} :=
      (Metric.nonempty_closedBall.mpr zero_le_one).image_const (q c)
    have hvdis (n : ℕ) (i : K n) : Disjoint (q '' RelCWComplex.openCell n i.1) {q c} := by
      apply Set.disjoint_left.mpr
      rintro z ⟨x,hx,rfl⟩ hz
      rcases (heq x c).mp (Set.mem_singleton_iff.mp hz) with h | h
      · exact Set.disjoint_left.mp (hdisj n i) hx (h ▸ hc)
      · exact Set.disjoint_left.mp (hdisj n i) hx h.1
    have hpair (n m : ℕ) (i : K n) (j : K m)
        (h : (⟨n,i.1⟩ : Σ k,RelCWComplex.cell (Set.univ : Set X) k) ≠ ⟨m,j.1⟩) :
        Disjoint (q '' RelCWComplex.openCell n i.1) (q '' RelCWComplex.openCell m j.1) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
      rcases (heq x y).mp (hxz.trans hyz.symm) with he | he
      · exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne h) hx (he ▸ hy)
      · exact Set.disjoint_left.mp (hdisj n i) hx he.1
    refine ⟨{ cell := cells
              map := chart
              source_eq := ?_
              continuousOn := ?_
              continuousOn_symm := ?_
              pairwiseDisjoint' := ?_
              mapsTo' := ?_
              closed' := ?_
              union' := ?_ }⟩
    · intro n i
      cases n with
      | zero => cases i <;> rfl
      | succ n => rfl
    · intro n i
      cases n with
      | zero =>
        cases i with
        | none => exact continuousOn_const
        | some i => exact continuous_quot_mk.comp_continuousOn (RelCWComplex.continuousOn 0 i.1)
      | succ n => exact continuous_quot_mk.comp_continuousOn (RelCWComplex.continuousOn (n+1) i.1)
    · intro n i
      cases n with
      | zero => cases i with
        | none => exact continuousOn_const
        | some i => exact kept_inv 0 i
      | succ n => exact kept_inv (n+1) i
    · rintro ⟨n,i⟩ _ ⟨m,j⟩ _ hij
      change Disjoint (chart n i '' ball 0 1) (chart m j '' ball 0 1)
      have hk (n m : ℕ) (i : K n) (j : K m)
          (hij : (⟨n,incl n i⟩ : Σ k,cells k) ≠ ⟨m,incl m j⟩) :
          Disjoint (chart n (incl n i) '' ball 0 1) (chart m (incl m j) '' ball 0 1) := by
        rw [hco,hco]
        apply hpair
        intro h
        have hn : n=m := congrArg Sigma.fst h
        subst m
        have he : i.1=j.1 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
        have he' : i=j := Subtype.ext he
        subst j
        exact hij rfl
      cases n with
      | zero =>
        cases m with
        | zero =>
          cases i with
          | none =>
            cases j with
            | none => exact False.elim (hij rfl)
            | some j => simpa only [← hvo,← hco 0 j] using (hvdis 0 j).symm
          | some i =>
            cases j with
            | none => simpa only [← hvo,← hco 0 i] using hvdis 0 i
            | some j => exact hk 0 0 i j hij
        | succ m =>
          cases i with
          | none => simpa only [← hvo,← hco (m+1) j] using (hvdis (m+1) j).symm
          | some i => exact hk 0 (m+1) i j hij
      | succ n =>
        cases m with
        | zero =>
          cases j with
          | none => simpa only [← hvo,← hco (n+1) i] using hvdis (n+1) i
          | some j => exact hk (n+1) 0 i j hij
        | succ m => exact hk (n+1) (m+1) i j hij
    · intro n i
      cases n with
      | zero =>
        refine ⟨fun _ => ∅,?_⟩
        rw [Metric.sphere_eq_empty_of_subsingleton (by norm_num : (1:ℝ) ≠ 0)]
        exact Set.mapsTo_empty _ _
      | succ n =>
        obtain ⟨J,hJ⟩ := CWComplex.mapsTo (C := (Set.univ : Set X)) (n+1) i.1
        let J' (m : ℕ) : Finset (K m) := (J m).subtype (fun a => ¬ RelCWComplex.openCell m a ⊆ C)
        let L : ∀ m, Finset (cells m)
          | 0 => insert none ((J' 0).image some)
          | m+1 => J' (m+1)
        refine ⟨L,?_⟩
        intro z hz
        obtain ⟨m,hm,j,hj,hx⟩ := by simpa only [Set.mem_iUnion,exists_prop] using hJ hz
        by_cases hjC : RelCWComplex.openCell m j ⊆ C
        · refine Set.mem_iUnion.mpr ⟨0,Set.mem_iUnion.mpr ⟨Nat.zero_lt_succ n,
            Set.mem_iUnion.mpr ⟨none,Set.mem_iUnion.mpr ⟨by simp [L],?_⟩⟩⟩⟩
          rw [hvc]
          exact hbase _ (hclosed m j hjC hx)
        · refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,
            Set.mem_iUnion.mpr ⟨incl m ⟨j,hjC⟩,Set.mem_iUnion.mpr ⟨?_,?_⟩⟩⟩⟩
          · cases m with
            | zero =>
              change some (⟨j,hjC⟩ : K 0) ∈ insert none ((J' 0).image some)
              apply Finset.mem_insert_of_mem
              apply Finset.mem_image.mpr
              refine ⟨⟨j,hjC⟩,?_,rfl⟩
              exact Finset.mem_subtype.mpr hj
            | succ m => exact Finset.mem_subtype.mpr hj
          · rw [hcc]
            exact ⟨_,hx,rfl⟩
    · intro A _ hA
      apply isQuotientMap_quot_mk.isClosed_preimage.mp
      apply (CWComplex.closed (Set.univ : Set X) (q ⁻¹' A) (Set.subset_univ _)).mpr
      intro n i
      by_cases hi : RelCWComplex.openCell n i ⊆ C
      · by_cases hv : q c ∈ A
        · have he : q ⁻¹' A ∩ RelCWComplex.closedCell n i=RelCWComplex.closedCell n i := by
            apply Set.inter_eq_right.mpr
            intro x hx
            change q x ∈ A
            rw [hbase x (hclosed n i hi hx)]
            exact hv
          rw [he]
          exact RelCWComplex.isClosed_closedCell
        · have he : q ⁻¹' A ∩ RelCWComplex.closedCell n i=∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            rintro x ⟨hx,hxc⟩
            apply hv
            rwa [← hbase x (hclosed n i hi hxc)]
          rw [he]
          exact isClosed_empty
      · have hh := ((hA n (incl n ⟨i,hi⟩)).preimage (continuous_quot_mk : Continuous q)).inter
          (RelCWComplex.isClosed_closedCell (n := n) (i := i))
        convert hh using 1
        rw [hcc]
        ext x
        exact ⟨fun h => ⟨⟨h.1,⟨x,h.2,rfl⟩⟩,h.2⟩,fun h => ⟨h.1.1,h.2⟩⟩
    · apply Set.eq_univ_of_forall
      intro z
      obtain ⟨x,rfl⟩ := Quot.exists_rep z
      have hx : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
          RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
      obtain ⟨n,i,hx⟩ := by simpa only [Set.mem_iUnion] using hx
      by_cases hi : RelCWComplex.openCell n i ⊆ C
      · refine Set.mem_iUnion.mpr ⟨0,Set.mem_iUnion.mpr ⟨none,?_⟩⟩
        rw [hvc]
        exact hbase x (hclosed n i hi hx)
      · refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨incl n ⟨i,hi⟩,?_⟩⟩
        rw [hcc]
        exact ⟨x,hx,rfl⟩
  have cw_product_wedge_saturated
      {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)]
      (ix : RelCWComplex.cell (Set.univ : Set X) 0)
      (iy : RelCWComplex.cell (Set.univ : Set Y) 0) :
      let W : Set (X × Y) := {p | p.1 = RelCWComplex.map 0 ix 0 ∨
        p.2 = RelCWComplex.map 0 iy 0}
      ∀ n (i : RelCWComplex.cell (Set.univ : Set X) n)
        m (j : RelCWComplex.cell (Set.univ : Set Y) m),
        (RelCWComplex.openCell n i ×ˢ RelCWComplex.openCell m j ⊆ W) ∨
          Disjoint (RelCWComplex.openCell n i ×ˢ RelCWComplex.openCell m j) W := by
    intro W n i m j
    classical
    have hzero : (![] : Fin 0 → ℝ) = 0 := Subsingleton.elim _ _
    by_cases hx : (⟨n,i⟩ : Σ n, RelCWComplex.cell (Set.univ : Set X) n) = ⟨0,ix⟩
    · left
      have he : RelCWComplex.openCell n i = RelCWComplex.openCell 0 ix :=
        congrArg (fun a : Σ n, RelCWComplex.cell (Set.univ : Set X) n =>
          RelCWComplex.openCell a.1 a.2) hx
      intro p hp
      left
      have hp' := hp.1
      rw [he,RelCWComplex.openCell_zero_eq_singleton,hzero] at hp'
      exact Set.mem_singleton_iff.mp hp'
    by_cases hy : (⟨m,j⟩ : Σ m, RelCWComplex.cell (Set.univ : Set Y) m) = ⟨0,iy⟩
    · left
      have he : RelCWComplex.openCell m j = RelCWComplex.openCell 0 iy :=
        congrArg (fun a : Σ m, RelCWComplex.cell (Set.univ : Set Y) m =>
          RelCWComplex.openCell a.1 a.2) hy
      intro p hp
      right
      have hp' := hp.2
      rw [he,RelCWComplex.openCell_zero_eq_singleton,hzero] at hp'
      exact Set.mem_singleton_iff.mp hp'
    · right
      apply Set.disjoint_left.mpr
      intro p hp hw
      rcases hw with hw | hw
      · apply Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hx) hp.1
        rw [hw]
        exact RelCWComplex.map_zero_mem_openCell 0 ix
      · apply Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hy) hp.2
        rw [hw]
        exact RelCWComplex.map_zero_mem_openCell 0 iy
  have smash_t2 (X Y : BasedSpace.{u}) [T2Space X] [T2Space Y] :
      T2Space (X.smash Y) := by
    classical
    let q : X × Y → X.smash Y := Quot.mk (SmashRelation X Y)
    let W (p : X × Y) : Prop := p.1=X.point ∨ p.2=Y.point
    have heq (p p' : X × Y) : q p=q p' ↔ p=p' ∨ (W p ∧ W p') := by
      constructor
      · intro h
        have h' := Quot.eqvGen_exact h
        clear h
        induction h' with
        | rel a b hab => exact Or.inr hab
        | refl a => exact Or.inl rfl
        | symm a b hab ih =>
          rcases ih with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨h.2,h.1⟩
        | trans a b c hab hbc ih₁ ih₂ =>
          rcases ih₁ with rfl | h₁
          · exact ih₂
          · rcases ih₂ with rfl | h₂
            · exact Or.inr h₁
            · exact Or.inr ⟨h₁.1,h₂.2⟩
      · rintro (rfl | h)
        · rfl
        · exact Quot.sound h
    have qbase (p : X × Y) (hp : W p) : q p=(X.smash Y).point :=
      Quot.sound ⟨hp,Or.inl rfl⟩
    have hid : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),inferInstance]
        (id : X × Y → X × Y) :=
      continuous_from_compactlyGenerated id (fun S g => g.continuous)
    have hopen (S : Set (X × Y)) (hS : IsOpen S)
        (hsat : (∀ p, W p → p ∈ S) ∨ (∀ p ∈ S, ¬ W p)) : IsOpen (q '' S) := by
      have hSk : @IsOpen (X × Y) (TopologicalSpace.compactlyGenerated.{u} (X × Y)) S :=
        @IsOpen.preimage (X × Y) (X × Y) (TopologicalSpace.compactlyGenerated.{u} (X × Y))
          inferInstance id hid S hS
      letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
      apply isQuotientMap_quot_mk.isOpen_preimage.mp
      convert hSk using 1
      ext p
      constructor
      · rintro ⟨p',hp',he⟩
        rcases (heq p' p).mp he with rfl | h
        · exact hp'
        · rcases hsat with hs | hs
          · exact hs p h.2
          · exact False.elim (hs p' hp' h.1)
      · intro hp
        exact ⟨p,hp,rfl⟩
    have hdisj {S T : Set (X × Y)} (hS : ∀ p ∈ S, ¬ W p) (hST : Disjoint S T) :
        Disjoint (q '' S) (q '' T) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨p,hp,hpz⟩ ⟨p',hp',hpz'⟩
      rcases (heq p p').mp (hpz.trans hpz'.symm) with rfl | h
      · exact Set.disjoint_left.mp hST hp hp'
      · exact hS p hp h.1
    have sep_base (p : X × Y) (hp : ¬ W p) :
        ∃ S T : Set (X.smash Y), IsOpen S ∧ IsOpen T ∧
          (X.smash Y).point ∈ S ∧ q p ∈ T ∧ Disjoint S T := by
      have hpx : p.1 ≠ X.point := fun h => hp (Or.inl h)
      have hpy : p.2 ≠ Y.point := fun h => hp (Or.inr h)
      obtain ⟨Ox,Vx,hOx,hVx,hxp,hxb,hXV⟩ := t2_separation hpx
      obtain ⟨Oy,Vy,hOy,hVy,hyp,hyb,hYV⟩ := t2_separation hpy
      let S : Set (X × Y) := (Vx ×ˢ Set.univ) ∪ (Set.univ ×ˢ Vy)
      let T : Set (X × Y) := Ox ×ˢ Oy
      have hS : IsOpen S := (hVx.prod isOpen_univ).union (isOpen_univ.prod hVy)
      have hT : IsOpen T := hOx.prod hOy
      have hSW (z : X × Y) (hz : W z) : z ∈ S := by
        rcases hz with hz | hz
        · left
          exact ⟨hz ▸ hxb,Set.mem_univ _⟩
        · right
          exact ⟨Set.mem_univ _,hz ▸ hyb⟩
      have hTW (z : X × Y) (hz : z ∈ T) : ¬ W z := by
        intro h
        rcases h with h | h
        · exact Set.disjoint_left.mp hXV hz.1 (h ▸ hxb)
        · exact Set.disjoint_left.mp hYV hz.2 (h ▸ hyb)
      have hTS : Disjoint T S := by
        apply Set.disjoint_left.mpr
        rintro z hz (hs | hs)
        · exact Set.disjoint_left.mp hXV hz.1 hs.1
        · exact Set.disjoint_left.mp hYV hz.2 hs.2
      refine ⟨q '' S,q '' T,hopen S hS (Or.inl hSW),hopen T hT (Or.inr hTW),?_,?_,
        (hdisj hTW hTS).symm⟩
      · exact ⟨(X.point,Y.point),hSW _ (Or.inl rfl),rfl⟩
      · exact ⟨p,⟨hxp,hyp⟩,rfl⟩
    have hO : IsOpen {p : X × Y | ¬ W p} :=
      ((isClosed_singleton.preimage continuous_fst).union
        (isClosed_singleton.preimage continuous_snd)).isOpen_compl
    constructor
    intro a b hab
    obtain ⟨p,rfl⟩ := Quot.exists_rep a
    obtain ⟨p',rfl⟩ := Quot.exists_rep b
    by_cases hp : W p
    · have hp' : ¬ W p' := fun h => hab ((qbase p hp).trans (qbase p' h).symm)
      obtain ⟨S,T,hS,hT,hSb,hTp',hST⟩ := sep_base p' hp'
      refine ⟨S,T,hS,hT,?_,hTp',hST⟩
      change q p ∈ S
      rw [qbase p hp]
      exact hSb
    · by_cases hp' : W p'
      · obtain ⟨S,T,hS,hT,hSb,hTp,hST⟩ := sep_base p hp
        refine ⟨T,S,hT,hS,hTp,?_,hST.symm⟩
        change q p' ∈ S
        rw [qbase p' hp']
        exact hSb
      · have hne : p ≠ p' := fun h => hab (congrArg q h)
        obtain ⟨S,T,hS,hT,hSp,hTp',hST⟩ := t2_separation hne
        refine ⟨q '' (S ∩ {p | ¬ W p}),q '' (T ∩ {p | ¬ W p}),
          hopen _ (hS.inter hO) (Or.inr (fun _ h => h.2)),
          hopen _ (hT.inter hO) (Or.inr (fun _ h => h.2)),
          ⟨p,⟨hSp,hp⟩,rfl⟩,⟨p',⟨hTp',hp'⟩,rfl⟩,
          hdisj (fun _ h => h.2) (hST.mono Set.inter_subset_left Set.inter_subset_left)⟩
  let W : Set (X × Y) := {p | p.1=X.point ∨ p.2=Y.point}
  have hW : IsClosed W := (isClosed_singleton.preimage continuous_fst).union
    (isClosed_singleton.preimage continuous_snd)
  have hforget : @Continuous (X × Y) (X × Y)
      (TopologicalSpace.compactlyGenerated.{u} (X × Y)) instTopologicalSpaceProd id :=
    continuous_from_compactlyGenerated id (fun _ g => g.continuous)
  have hWk : @IsClosed (X × Y) (TopologicalSpace.compactlyGenerated.{u} (X × Y)) W :=
    @IsClosed.preimage (X × Y) (X × Y) (TopologicalSpace.compactlyGenerated.{u} (X × Y))
      instTopologicalSpaceProd id hforget W hW
  have htk : @T2Space (X × Y) (TopologicalSpace.compactlyGenerated.{u} (X × Y)) :=
    t2Space_antitone (continuous_id_iff_le.mp hforget) inferInstance
  have hsat (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
      (m : ℕ) (j : RelCWComplex.cell (Set.univ : Set Y) m) :
      RelCWComplex.openCell n i ×ˢ RelCWComplex.openCell m j ⊆ W ∨
      Disjoint (RelCWComplex.openCell n i ×ˢ RelCWComplex.openCell m j) W := by
    simpa only [← hx,← hy] using cw_product_wedge_saturated ix iy n i m j
  have hProd := @cw_kproduct X Y _ _ _ _ _ _
  have hT : T2Space (X.smash Y) := smash_t2 X Y
  letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
  letI : T2Space (X × Y) := htk
  obtain ⟨H,hH⟩ := hProd
  letI := H
  have hCWsat (k : ℕ) (a : RelCWComplex.cell (Set.univ : Set (X × Y)) k) :
      RelCWComplex.openCell k a ⊆ W ∨ Disjoint (RelCWComplex.openCell k a) W := by
    obtain ⟨n,i,m,j,_,he⟩ := hH k a
    rw [he]
    exact hsat n i m j
  exact ⟨hT,cw_collapse (X × Y) W (X.point,Y.point) (Or.inl rfl) hWk hCWsat hT⟩

open Set Metric in
/-- Move the input basepoints to actual vertices by homotopy extension,
construct their smash CW model, and transport its based homotopy type. -/
private theorem smash_hasCWType (A B : BasedSpace.{u})
    (hA : A.HasCWType) (hB : B.HasCWType) : (A.smash B).HasCWType := by
  have cw_based_vertex_model (X : BasedSpace.{u}) [T2Space X]
      [CWComplex (Set.univ : Set X)] (hX : X.IsWellBased) :
      ∃ i : RelCWComplex.cell (Set.univ : Set X) 0,
        let Y : BasedSpace.{u} := ⟨X.space,RelCWComplex.map 0 i 0⟩
        Y.IsWellBased ∧ ∃ (f : X ⟶ Y) (g : Y ⟶ X),
          (g.map.comp f.map).HomotopicRel (ContinuousMap.id X) {X.point} ∧
          (f.map.comp g.map).HomotopicRel (ContinuousMap.id Y) {Y.point} := by
    have cw_vertex_wellBased (X : BasedSpace.{u}) [T2Space X]
        [CWComplex (Set.univ : Set X)] (i : RelCWComplex.cell (Set.univ : Set X) 0) :
        let Y : BasedSpace.{u} := ⟨X.space,RelCWComplex.map 0 i 0⟩
        Y.IsWellBased := by
      have cube_boundary_retraction (n : ℕ) :
          ∃ r : C((Fin n → I) × I,(Fin n → I) × I),
            (∀ x, r (x,0)=(x,0)) ∧
            (∀ x, x ∈ Cube.boundary (Fin n) → ∀ t, r (x,t)=(x,t)) ∧
            (∀ q, (r q).2=0 ∨ (r q).1 ∈ Cube.boundary (Fin n)) := by
        let v (x : Fin n → I) (i : Fin n) : ℝ := (x i:ℝ)-1/2
        let m (q : (Fin n → I) × I) : ℝ := max ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
        have hb (x : Fin n → I) : 2*‖v x‖ ≤ 1 := by
          have hh : ‖v x‖ ≤ (1/2:ℝ) := by
            apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
            intro i
            rw [Real.norm_eq_abs]
            apply abs_le.mpr
            constructor <;> dsimp [v] <;> linarith [(x i).property.1,(x i).property.2]
          linarith
        have hm (q : (Fin n → I) × I) : 0 < m q ∧ m q ≤ 1 := by
          constructor
          · have h := le_max_left ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
            change 0 < max _ _
            linarith [q.2.property.2]
          · exact max_le (by linarith [q.2.property.1]) (hb q.1)
        have hcoord (q : (Fin n → I) × I) (i : Fin n) : 2*|(q.1 i:ℝ)-1/2| ≤ m q := by
          have h := norm_le_pi_norm (v q.1) i
          rw [Real.norm_eq_abs] at h
          have he := le_max_right ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
          change 2*‖v q.1‖ ≤ m q at he
          dsimp [v] at h
          linarith
        have hx (q : (Fin n → I) × I) (i : Fin n) :
            1/2+((q.1 i:ℝ)-1/2)/m q ∈ Set.Icc (0:ℝ) 1 := by
          have hl : -(1/2:ℝ) ≤ ((q.1 i:ℝ)-1/2)/m q := by
            apply (le_div_iff₀ (hm q).1).mpr
            linarith [hcoord q i,neg_abs_le ((q.1 i:ℝ)-1/2)]
          have hu : ((q.1 i:ℝ)-1/2)/m q ≤ (1/2:ℝ) := by
            apply (div_le_iff₀ (hm q).1).mpr
            linarith [hcoord q i,le_abs_self ((q.1 i:ℝ)-1/2)]
          constructor <;> linarith
        have hy (q : (Fin n → I) × I) : 2+((q.2:ℝ)-2)/m q ∈ Set.Icc (0:ℝ) 1 := by
          have hl : -(2:ℝ) ≤ ((q.2:ℝ)-2)/m q := by
            apply (le_div_iff₀ (hm q).1).mpr
            have h := le_max_left ((2-(q.2:ℝ))/2) (2*‖v q.1‖)
            change (2-(q.2:ℝ))/2 ≤ m q at h
            linarith
          have hu : ((q.2:ℝ)-2)/m q ≤ (q.2:ℝ)-2 := by
            apply (div_le_iff₀ (hm q).1).mpr
            nlinarith [(hm q).2,q.2.property.2]
          constructor <;> linarith [q.2.property.2]
        have hv : Continuous v := continuous_pi fun i =>
          (continuous_subtype_val.comp (continuous_apply i)).sub continuous_const
        have hmcont : Continuous m :=
          ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).div_const 2).max
            (continuous_const.mul (hv.comp continuous_fst).norm)
        let r : C((Fin n → I) × I,(Fin n → I) × I) := ⟨fun q => (fun i => ⟨_,hx q i⟩,⟨_,hy q⟩),
          (continuous_pi fun i => (continuous_const.add
            (((continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)).sub continuous_const).div hmcont
              (fun q => ne_of_gt (hm q).1))).subtype_mk _).prodMk
            ((continuous_const.add
              (((continuous_subtype_val.comp continuous_snd).sub continuous_const).div hmcont
                (fun q => ne_of_gt (hm q).1))).subtype_mk _)⟩
        have hmzero (x : Fin n → I) : m (x,0)=1 := by
          dsimp [m]
          norm_num only [show ((0:I):ℝ)=0 from rfl,sub_zero,show (2:ℝ)/2=1 by norm_num]
          exact max_eq_left (hb x)
        have hmbound (x : Fin n → I) (hx : x ∈ Cube.boundary (Fin n)) (t : I) : m (x,t)=1 := by
          obtain ⟨i,hi⟩ := hx
          have h : 1 ≤ m (x,t) := by
            have hh := hcoord (x,t) i
            change 2*|(x i:ℝ)-1/2| ≤ m (x,t) at hh
            rcases hi with hi | hi <;> rw [hi] at hh <;> norm_num at hh ⊢ <;> linarith
          exact le_antisymm (hm (x,t)).2 h
        refine ⟨r,?_,?_,?_⟩
        · intro x
          apply Prod.ext
          · funext i
            apply Subtype.ext
            simp [r,hmzero]
          · apply Subtype.ext
            simp [r,hmzero]
        · intro x hx t
          apply Prod.ext
          · funext i
            apply Subtype.ext
            simp [r,hmbound x hx t]
          · apply Subtype.ext
            simp [r,hmbound x hx t]
        · intro q
          by_cases h : 2*‖v q.1‖ ≤ (2-(q.2:ℝ))/2
          · left
            apply Subtype.ext
            change 2+((q.2:ℝ)-2)/m q = 0
            have hd : ((q.2:ℝ)-2)/m q = -2 := by
              apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
              dsimp [m]
              rw [max_eq_left h]
              ring
            rw [hd]
            norm_num
          · have hmax : m q=2*‖v q.1‖ := max_eq_right (le_of_not_ge h)
            have hn : Nonempty (Fin n) := by
              by_contra he
              haveI : IsEmpty (Fin n) := not_nonempty_iff.mp he
              have hv0 : v q.1=0 := Subsingleton.elim _ _
              have := (hm q).1
              rw [hmax,hv0,norm_zero,mul_zero] at this
              exact (lt_irrefl _ this)
            letI := hn
            obtain ⟨i,hi⟩ := (IsGreatest.pi_norm (v q.1)).1
            change ‖v q.1 i‖=‖v q.1‖ at hi
            rw [Real.norm_eq_abs] at hi
            have hmax' : m q=2*|(q.1 i:ℝ)-1/2| := by
              rw [hmax,← hi]
            right
            refine ⟨i,?_⟩
            by_cases ht : 0 ≤ (q.1 i:ℝ)-1/2
            · right
              apply Subtype.ext
              change 1/2+((q.1 i:ℝ)-1/2)/m q = 1
              have hd : ((q.1 i:ℝ)-1/2)/m q = 1/2 := by
                apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
                rw [hmax',abs_of_nonneg ht]
                ring
              rw [hd]
              norm_num
            · left
              apply Subtype.ext
              change 1/2+((q.1 i:ℝ)-1/2)/m q = 0
              have hd : ((q.1 i:ℝ)-1/2)/m q = -(1/2) := by
                apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
                rw [hmax',abs_of_neg (lt_of_not_ge ht)]
                ring
              rw [hd]
              norm_num
      have cube_boundary_hep_general (n : ℕ) {Y : Type u} [TopologicalSpace Y]
          (f : C((Fin n → I),Y))
          (g : C((Cube.boundary (Fin n)) × I,Y))
          (hg : ∀ x : Cube.boundary (Fin n), g (x,0)=f x.1) :
          ∃ H : C((Fin n → I) × I,Y), (∀ x, H (x,0)=f x) ∧
            (∀ (x : Cube.boundary (Fin n)) t, H (x.1,t)=g (x,t)) := by
        classical
        obtain ⟨r,hzero,hboundary,hr⟩ := cube_boundary_retraction n
        have hc : IsClosed (Cube.boundary (Fin n)) := by
          have he : Cube.boundary (Fin n)=⋃ i : Fin n, {x : Fin n → I | x i=0 ∨ x i=1} := by
            ext x
            simp [Cube.boundary]
          rw [he]
          apply isClosed_iUnion_of_finite
          intro i
          exact (isClosed_eq (continuous_apply i) continuous_const).union
            (isClosed_eq (continuous_apply i) continuous_const)
        let U : Set ((Fin n → I) × I) := {q | (r q).2=0}
        let V : Set ((Fin n → I) × I) := {q | (r q).1 ∈ Cube.boundary (Fin n)}
        have hU : IsClosed U := isClosed_eq r.continuous.snd continuous_const
        have hV : IsClosed V := hc.preimage r.continuous.fst
        have hUV : U ∪ V=Set.univ := by ext q; exact iff_true_intro (hr q)
        let F (q : (Fin n → I) × I) :=
          if h : (r q).1 ∈ Cube.boundary (Fin n) then g (⟨(r q).1,h⟩,(r q).2) else f (r q).1
        have hu : ContinuousOn F U := (f.continuous.comp r.continuous.fst).continuousOn.congr (by
          intro q hq
          dsimp only [F]
          split_ifs with hb
          · change g (⟨(r q).1,hb⟩,(r q).2)=f (r q).1
            rw [show (r q).2=0 from hq,hg]
          · rfl)
        have hv : ContinuousOn F V := by
          apply continuousOn_iff_continuous_restrict.mpr
          let h : V → (Cube.boundary (Fin n)) × I := fun q =>
            (⟨(r q.1).1,q.property⟩,(r q.1).2)
          have hh : Continuous h :=
            ((r.continuous.comp continuous_subtype_val).fst.subtype_mk _).prodMk
              (r.continuous.comp continuous_subtype_val).snd
          apply (g.continuous.comp hh).congr
          intro q
          change g (⟨(r q.1).1,q.property⟩,(r q.1).2)=F q.1
          dsimp only [F]
          rw [dif_pos (show (r q.1).1 ∈ Cube.boundary (Fin n) from q.property)]
        have hF : Continuous F := continuousOn_univ.mp (hUV ▸ hu.union_of_isClosed hv hU hV)
        refine ⟨⟨F,hF⟩,?_,?_⟩
        · intro x
          change F (x,0)=f x
          dsimp only [F]
          simp only [hzero]
          split_ifs with hx
          · exact hg ⟨x,hx⟩
          · rfl
        · intro x t
          change F (x.1,t)=g (x,t)
          dsimp only [F]
          simp only [hboundary x.1 x.property t,dif_pos x.property]
      have closedBall_boundary_hep (n : ℕ) {Y : Type u} [TopologicalSpace Y]
          (f : C(Metric.closedBall (0 : Fin n → ℝ) 1,Y))
          (g : C((Metric.sphere (0 : Fin n → ℝ) 1) × I,Y))
          (hg : ∀ x : Metric.sphere (0 : Fin n → ℝ) 1,
            g (x,0)=f ⟨x.1,Metric.sphere_subset_closedBall x.2⟩) :
          ∃ H : C((Metric.closedBall (0 : Fin n → ℝ) 1) × I,Y),
            (∀ x, H (x,0)=f x) ∧
            (∀ (x : Metric.sphere (0 : Fin n → ℝ) 1) t,
              H (⟨x.1,Metric.sphere_subset_closedBall x.2⟩,t)=g (x,t)) := by
        have hc (z : Fin n → ℝ) : z ∈ Metric.closedBall 0 1 ↔
            ∀ i, -1≤z i ∧ z i≤1 := by
          rw [closedBall_pi _ (by norm_num : (0:ℝ)≤1)]
          simp [Real.closedBall_eq_Icc,Pi.le_def,forall_and]
        have hb (z : Fin n → ℝ) : z ∈ Metric.ball 0 1 ↔ ∀ i, -1<z i ∧ z i<1 := by
          rw [ball_pi _ (by norm_num : (0:ℝ)<1)]
          simp only [Set.mem_pi,Set.mem_univ,forall_const,Real.ball_eq_Ioo,Pi.zero_apply,
            zero_sub,zero_add,Set.mem_Ioo]
        let E : (Metric.closedBall (0 : Fin n → ℝ) 1) ≃ₜ (Fin n → I) :=
          { toFun := fun z i => ⟨(z.1 i+1)/2,by
              have h := (hc _).mp z.2 i
              constructor <;> linarith⟩
            invFun := fun t => ⟨fun i => 2*(t i:ℝ)-1,by
              apply (hc _).mpr
              intro i
              constructor <;> linarith [(t i).property.1,(t i).property.2]⟩
            left_inv := by intro z; apply Subtype.ext; funext i; dsimp; ring
            right_inv := by intro t; funext i; apply Subtype.ext; dsimp; ring
            continuous_toFun := by
              apply continuous_pi
              intro i
              apply Continuous.subtype_mk
              exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2
            continuous_invFun := by
              apply Continuous.subtype_mk
              apply continuous_pi
              intro i
              exact (continuous_const.mul (continuous_subtype_val.comp (continuous_apply i))).sub continuous_const }
        have hEb (z : Metric.closedBall (0 : Fin n → ℝ) 1) :
            z.1 ∈ Metric.sphere 0 1 ↔ E z ∈ Cube.boundary (Fin n) := by
          constructor
          · intro hz
            by_contra hn
            have hzball : z.1 ∈ Metric.ball 0 1 := by
              apply (hb _).mpr
              intro i
              have h0 : E z i≠0 := fun h => hn ⟨i,Or.inl h⟩
              have h1 : E z i≠1 := fun h => hn ⟨i,Or.inr h⟩
              have hi := (hc _).mp z.2 i
              constructor
              · apply lt_of_le_of_ne hi.1
                intro h
                apply h0
                apply Subtype.ext
                change (z.1 i+1)/2=0
                rw [← h]
                norm_num
              · apply lt_of_le_of_ne hi.2
                intro h
                apply h1
                apply Subtype.ext
                change (z.1 i+1)/2=1
                rw [h]
                norm_num
            exact Metric.sphere_disjoint_ball.le_bot ⟨hz,hzball⟩
          · rintro ⟨i,hi⟩
            rw [← Metric.closedBall_sdiff_ball]
            refine ⟨z.2,?_⟩
            intro hz
            have hzi := (hb _).mp hz i
            rcases hi with hi | hi
            · have hh := congrArg Subtype.val hi
              change (z.1 i+1)/2=0 at hh
              linarith
            · have hh := congrArg Subtype.val hi
              change (z.1 i+1)/2=1 at hh
              linarith
        let f' : C((Fin n → I),Y) := f.comp ⟨E.symm,E.symm.continuous⟩
        let g' : C((Cube.boundary (Fin n)) × I,Y) :=
          ⟨fun p => g (⟨(E.symm p.1.1).1,(hEb _).mpr (by simpa only [E.apply_symm_apply] using p.1.2)⟩,p.2),
            g.continuous.comp
              (((continuous_subtype_val.comp (E.symm.continuous.comp
                (continuous_subtype_val.comp continuous_fst))).subtype_mk _).prodMk continuous_snd)⟩
        obtain ⟨F,hF0,hFb⟩ := cube_boundary_hep_general n f' g' (by
          intro x
          exact hg ⟨(E.symm x.1).1,(hEb _).mpr (by simpa only [E.apply_symm_apply] using x.2)⟩)
        refine ⟨F.comp ⟨fun p => (E p.1,p.2),(E.continuous.comp continuous_fst).prodMk continuous_snd⟩,
          ?_,?_⟩
        · intro x
          change F (E x,0)=f x
          rw [hF0]
          change f (E.symm (E x))=f x
          rw [E.symm_apply_apply]
        · intro x t
          let z : Metric.closedBall (0 : Fin n → ℝ) 1 := ⟨x.1,Metric.sphere_subset_closedBall x.2⟩
          change F (E z,t)=g (x,t)
          rw [hFb ⟨E z,(hEb z).mp x.2⟩]
          change g (⟨(E.symm (E z)).1,_⟩,t)=g (x,t)
          simp only [E.symm_apply_apply]
          rfl
      have cw_boundary_continuous (X : Type u) [TopologicalSpace X] [T2Space X]
          [CWComplex (Set.univ : Set X)] (Z : Type u) [TopologicalSpace Z]
          (F : X × I → Z) (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
          (hF : ∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
            Continuous (fun p : (closedBall (0 : Fin m → ℝ) 1) × I =>
              F (RelCWComplex.map m j p.1,p.2))) :
          Continuous (fun p : (sphere (0 : Fin n → ℝ) 1) × I =>
            F (RelCWComplex.map n i p.1,p.2)) := by
        classical
        have hcell (m : ℕ) (hm : m < n) (j : RelCWComplex.cell (Set.univ : Set X) m) :
            ContinuousOn F ((RelCWComplex.closedCell m j) ×ˢ (Set.univ : Set I)) := by
          let c : C(closedBall (0 : Fin m → ℝ) 1,RelCWComplex.closedCell m j) :=
            ⟨fun z => ⟨RelCWComplex.map m j z,⟨z,z.property,rfl⟩⟩,
              (RelCWComplex.continuousOn m j).restrict.subtype_mk _⟩
          have hc : IsQuotientMap c := IsQuotientMap.of_surjective_continuous (by
            rintro ⟨x,z,hz,rfl⟩
            exact ⟨⟨z,hz⟩,rfl⟩) c.continuous
          have h : Continuous (fun p : (RelCWComplex.closedCell m j) × I => F (p.1,p.2)) :=
            hc.continuous_lift_prod_left (hF m hm j)
          apply continuousOn_iff_continuous_restrict.mpr
          exact h.comp (((continuous_fst.comp continuous_subtype_val).subtype_mk
            (fun p => p.2.1)).prodMk (continuous_snd.comp continuous_subtype_val))
        obtain ⟨J,hJ⟩ := CWComplex.mapsTo (C := (Set.univ : Set X)) n i
        let A := Σ m : Fin n, ↥(J m)
        let S (a : A) : Set (X × I) := (RelCWComplex.closedCell a.1 a.2.1) ×ˢ Set.univ
        have hS : ∀ a, IsClosed (S a) := fun _ =>
          RelCWComplex.isClosed_closedCell.prod isClosed_univ
        have hcont : ContinuousOn F (⋃ a : A, S a) :=
          (locallyFinite_of_finite S).continuousOn_iUnion hS (fun a => hcell a.1 a.1.2 a.2.1)
        let g : (sphere (0 : Fin n → ℝ) 1) × I → X × I :=
          fun p => (RelCWComplex.map n i p.1,p.2)
        have hg : Continuous g :=
          (((RelCWComplex.continuousOn n i).mono sphere_subset_closedBall).restrict.comp
            continuous_fst).prodMk continuous_snd
        have hmap : MapsTo g Set.univ (⋃ a : A, S a) := by
          intro p _
          have h := hJ p.1.2
          simp only [Set.mem_iUnion,exists_prop] at h
          obtain ⟨m,hm,j,hj,hx⟩ := h
          exact Set.mem_iUnion.mpr ⟨⟨⟨m,hm⟩,⟨j,hj⟩⟩,hx,trivial⟩
        exact continuousOn_univ.mp (hcont.comp hg.continuousOn hmap)
      have cw_extend_dimension
          (X : Type u) [TopologicalSpace X] [T2Space X]
          [CWComplex (Set.univ : Set X)] (Z : Type u) [TopologicalSpace Z]
          (f : C(X,Z)) (n : ℕ) (F : X × I → Z)
          (hF0 : ∀ x, F (x,0)=f x)
          (hF : ∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
            Continuous (fun p : (closedBall (0 : Fin m → ℝ) 1) × I =>
              F (RelCWComplex.map m j p.1,p.2))) :
          ∃ G : X × I → Z,
            (∀ x, G (x,0)=f x) ∧
            (∀ m < n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
              ∀ x ∈ RelCWComplex.closedCell m j, ∀ t, G (x,t)=F (x,t)) ∧
            (∀ i : RelCWComplex.cell (Set.univ : Set X) n,
              Continuous (fun p : (closedBall (0 : Fin n → ℝ) 1) × I =>
                G (RelCWComplex.map n i p.1,p.2))) := by
        classical
        have hExt (i : RelCWComplex.cell (Set.univ : Set X) n) :
            ∃ E : C((closedBall (0 : Fin n → ℝ) 1) × I,Z),
              (∀ z, E (z,0)=f (RelCWComplex.map n i z)) ∧
              (∀ (z : sphere (0 : Fin n → ℝ) 1) t,
                E (⟨z.1,sphere_subset_closedBall z.2⟩,t)=F (RelCWComplex.map n i z,t)) := by
          apply closedBall_boundary_hep n
            ⟨fun z => f (RelCWComplex.map n i z),
              f.continuous.comp (RelCWComplex.continuousOn n i).restrict⟩
            ⟨fun p => F (RelCWComplex.map n i p.1,p.2),cw_boundary_continuous X Z F n i hF⟩
          exact fun z => hF0 _
        choose E hE0 hEb using hExt
        let New (x : X) := ∃ i : RelCWComplex.cell (Set.univ : Set X) n,
          x ∈ RelCWComplex.openCell n i
        have hinv (i : RelCWComplex.cell (Set.univ : Set X) n) {x : X}
            (hx : x ∈ RelCWComplex.openCell n i) :
            (RelCWComplex.map n i).symm x ∈ closedBall (0 : Fin n → ℝ) 1 := by
          have ht : x ∈ (RelCWComplex.map n i).target := by
            rw [← PartialEquiv.image_source_eq_target,RelCWComplex.source_eq]
            exact hx
          have hs := (RelCWComplex.map n i).map_target ht
          rw [RelCWComplex.source_eq] at hs
          exact ball_subset_closedBall hs
        let G : X × I → Z := fun p => if h : New p.1 then
          E (Classical.choose h) (⟨(RelCWComplex.map n (Classical.choose h)).symm p.1,
            hinv _ (Classical.choose_spec h)⟩,p.2) else F p
        have hopen {x : X} (i : RelCWComplex.cell (Set.univ : Set X) n)
            (hx : x ∈ RelCWComplex.openCell n i) (t : I) :
            G (x,t)=E i (⟨(RelCWComplex.map n i).symm x,hinv i hx⟩,t) := by
          have hnew : New x := ⟨i,hx⟩
          have hi : Classical.choose hnew=i := by
            by_contra h
            have hd := RelCWComplex.disjoint_openCell_of_ne
              (C := (Set.univ : Set X)) (n := n) (m := n)
              (i := Classical.choose hnew) (j := i) (by simpa using h)
            exact hd.le_bot ⟨Classical.choose_spec hnew,hx⟩
          dsimp only [G]
          rw [dif_pos hnew]
          subst hi
          rfl
        have hnone {x : X} (hx : x ∈ RelCWComplex.skeletonLT (Set.univ : Set X) n) :
            ¬New x := by
          rintro ⟨i,hi⟩
          exact (RelCWComplex.disjoint_skeletonLT_openCell (C := (Set.univ : Set X))
            (j := i) (le_refl (n : ℕ∞))).le_bot ⟨hx,hi⟩
        refine ⟨G,?_,?_,?_⟩
        · intro x
          by_cases hx : New x
          · rw [hopen (Classical.choose hx) (Classical.choose_spec hx) 0,hE0]
            have ht : x ∈ (RelCWComplex.map n (Classical.choose hx)).target := by
              rw [← PartialEquiv.image_source_eq_target,RelCWComplex.source_eq]
              exact Classical.choose_spec hx
            rw [PartialEquiv.right_inv _ ht]
          · simp only [G,dif_neg hx,hF0]
        · intro m hm j x hx t
          have hn : ¬New x := by
            rintro ⟨i,hi⟩
            exact (RelCWComplex.disjoint_skeleton_openCell (C := (Set.univ : Set X))
              (j := i) (ENat.coe_lt_coe.mpr hm)).le_bot
              ⟨RelCWComplex.closedCell_subset_skeleton m j hx,hi⟩
          exact dif_neg hn
        · intro i
          apply (E i).continuous.congr
          intro p
          by_cases hp : p.1.1 ∈ ball (0 : Fin n → ℝ) 1
          · have hx : RelCWComplex.map n i p.1 ∈ RelCWComplex.openCell n i :=
              ⟨p.1,hp,rfl⟩
            rw [hopen i hx p.2]
            have he : (RelCWComplex.map n i).symm (RelCWComplex.map n i p.1)=p.1 :=
              (RelCWComplex.map n i).left_inv (by rw [RelCWComplex.source_eq]; exact hp)
            exact congrArg (fun z : closedBall (0 : Fin n → ℝ) 1 => E i (z,p.2))
              (Subtype.ext he.symm)
          · have hs : p.1.1 ∈ sphere (0 : Fin n → ℝ) 1 := by
              rw [← closedBall_sdiff_ball]
              exact ⟨p.1.2,hp⟩
            have hx : RelCWComplex.map n i p.1 ∈
                RelCWComplex.skeletonLT (Set.univ : Set X) n :=
              RelCWComplex.cellFrontier_subset_skeletonLT n i ⟨p.1,hs,rfl⟩
            change E i p = G (RelCWComplex.map n i p.1,p.2)
            rw [show G (RelCWComplex.map n i p.1,p.2)=F (RelCWComplex.map n i p.1,p.2)
              from dif_neg (hnone hx)]
            exact hEb i ⟨p.1,hs⟩ p.2
      have cw_cylinder_closed (X : Type u) [TopologicalSpace X] [T2Space X]
          [CWComplex (Set.univ : Set X)] (F : Set (X × I))
          (hF : ∀ n (i : RelCWComplex.cell (Set.univ : Set X) n),
            IsClosed ((fun p : (closedBall (0 : Fin n → ℝ) 1) × I =>
              (RelCWComplex.map n i p.1,p.2)) ⁻¹' F)) : IsClosed F := by
        let A := Σ n : ℕ, Σ i : RelCWComplex.cell (Set.univ : Set X) n,
          closedBall (0 : Fin n → ℝ) 1
        let π : A → X := fun a => RelCWComplex.map a.1 a.2.1 a.2.2
        have hπcont : Continuous π := by
          apply continuous_sigma
          intro n
          apply continuous_sigma
          intro i
          exact (RelCWComplex.continuousOn n i).restrict
        have hπsurj : Function.Surjective π := by
          intro x
          have h : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
              RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
          obtain ⟨n,i,z,hz,hx⟩ := by simpa only [Set.mem_iUnion,RelCWComplex.closedCell,Set.mem_image] using h
          exact ⟨⟨n,i,z,hz⟩,hx⟩
        have hπ : IsQuotientMap π := by
          apply isQuotientMap_iff_isClosed.mpr
          refine ⟨hπsurj,fun S => ⟨fun hS => hS.preimage hπcont,?_⟩⟩
          intro hS
          apply (CWComplex.closed (Set.univ : Set X) S (Set.subset_univ S)).mpr
          intro n i
          let c : C(closedBall (0 : Fin n → ℝ) 1,X) :=
            ⟨fun z => RelCWComplex.map n i z,(RelCWComplex.continuousOn n i).restrict⟩
          have hc : IsClosed (c ⁻¹' S) := by
            exact hS.preimage (continuous_sigmaMk.comp continuous_sigmaMk)
          have him : c '' (c ⁻¹' S)=S ∩ RelCWComplex.closedCell n i := by
            ext x
            constructor
            · rintro ⟨z,hz,rfl⟩
              exact ⟨hz,⟨z,z.property,rfl⟩⟩
            · rintro ⟨hx,z,hz,rfl⟩
              exact ⟨⟨z,hz⟩,hx,rfl⟩
          rw [← him]
          exact (hc.isCompact.image c.continuous).isClosed
        have hprod : IsClosed ((fun p : A × I => (π p.1,p.2)) ⁻¹' F) := by
          let e : A × I ≃ₜ Σ n : ℕ,
              (Σ i : RelCWComplex.cell (Set.univ : Set X) n,
                closedBall (0 : Fin n → ℝ) 1) × I := Homeomorph.sigmaProdDistrib
          apply e.symm.isQuotientMap.isCoinducing.isClosed_preimage.mp
          apply isClosed_sigma_iff.mpr
          intro n
          let e' : (Σ i : RelCWComplex.cell (Set.univ : Set X) n,
              closedBall (0 : Fin n → ℝ) 1) × I ≃ₜ
              Σ i : RelCWComplex.cell (Set.univ : Set X) n,
                (closedBall (0 : Fin n → ℝ) 1) × I := Homeomorph.sigmaProdDistrib
          apply e'.symm.isQuotientMap.isCoinducing.isClosed_preimage.mp
          apply isClosed_sigma_iff.mpr
          intro i
          exact hF n i
        let liftπ : A × I → ULift.{u} (X × I) := fun p => ⟨π p.1,p.2⟩
        letI : TopologicalSpace (ULift.{u} (X × I)) := TopologicalSpace.coinduced liftπ inferInstance
        have hs : IsClosed {q : ULift.{u} (X × I) | q.down ∈ F} := by
          rw [isClosed_coinduced]
          exact hprod
        have hc : Continuous (fun p : X × I => (⟨p⟩ : ULift.{u} (X × I))) := by
          apply hπ.continuous_lift_prod_left
          exact continuous_coinduced_rng
        exact hs.preimage hc
      have cw_vertex_hep
          (X : Type u) [TopologicalSpace X] [T2Space X]
          [CWComplex (Set.univ : Set X)] (Z : Type u) [TopologicalSpace Z]
          (i₀ : RelCWComplex.cell (Set.univ : Set X) 0)
          (f : C(X,Z)) (p : C(I,Z)) (hp : p 0=f (RelCWComplex.map 0 i₀ 0)) :
          ∃ H : C(X × I,Z), (∀ x, H (x,0)=f x) ∧
            (∀ t, H (RelCWComplex.map 0 i₀ 0,t)=p t) := by
        classical
        let v : X := RelCWComplex.map 0 i₀ 0
        let Pack (n : ℕ) := {F : X × I → Z //
          (∀ x, F (x,0)=f x) ∧ (∀ t, F (v,t)=p t) ∧
          (∀ m ≤ n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
            Continuous (fun q : (closedBall (0 : Fin m → ℝ) 1) × I =>
              F (RelCWComplex.map m j q.1,q.2)))}
        let F0 : X × I → Z := fun q => if q.1=v then p q.2 else f q.1
        have hzero : ∀ z : Fin 0 → ℝ, z=0 := fun _ => Subsingleton.elim _ _
        have hF00 : ∀ x, F0 (x,0)=f x := by
          intro x
          dsimp only [F0]
          split_ifs with h
          · subst x; exact hp
          · rfl
        have hF0v : ∀ t, F0 (v,t)=p t := by intro t; exact if_pos rfl
        have hF0c (i : RelCWComplex.cell (Set.univ : Set X) 0) :
            Continuous (fun q : (closedBall (0 : Fin 0 → ℝ) 1) × I =>
              F0 (RelCWComplex.map 0 i q.1,q.2)) := by
          by_cases h : RelCWComplex.map 0 i 0=v
          · apply (p.continuous.comp continuous_snd).congr
            intro q
            dsimp only [F0]
            rw [hzero q.1,h,if_pos rfl]
            rfl
          · apply continuous_const.congr
            intro q
            dsimp only [F0]
            rw [hzero q.1,if_neg h]
        let init : Pack 0 := ⟨F0,hF00,hF0v,by
          intro m hm i
          have hm0 : m=0 := Nat.eq_zero_of_le_zero hm
          subst m
          exact hF0c i⟩
        have hstep (n : ℕ) (P : Pack n) : ∃ Q : Pack (n+1),
            ∀ m ≤ n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
              ∀ x ∈ RelCWComplex.closedCell m j, ∀ t, Q.1 (x,t)=P.1 (x,t) := by
          obtain ⟨G,hG0,hGold,hGc⟩ := cw_extend_dimension X Z f (n+1) P.1 P.2.1
            (fun m hm j => P.2.2.2 m (Nat.le_of_lt_succ hm) j)
          have hv : v ∈ RelCWComplex.closedCell 0 i₀ :=
            ⟨0,by simp,rfl⟩
          refine ⟨⟨G,hG0,?_,?_⟩,?_⟩
          · intro t
            exact (hGold 0 (Nat.zero_lt_succ n) i₀ v hv t).trans (P.2.2.1 t)
          · intro m hm j
            rcases Nat.lt_or_eq_of_le hm with hm | rfl
            · apply (P.2.2.2 m (Nat.le_of_lt_succ hm) j).congr
              intro q
              exact (hGold m hm j _ ⟨q.1,q.1.2,rfl⟩ q.2).symm
            · exact hGc j
          · intro m hm j x hx t
            exact hGold m (Nat.lt_succ_of_le hm) j x hx t
        let next (n : ℕ) (P : Pack n) : Pack (n+1) := Classical.choose (hstep n P)
        have hnext (n : ℕ) (P : Pack n) :
            ∀ m ≤ n, ∀ j : RelCWComplex.cell (Set.univ : Set X) m,
              ∀ x ∈ RelCWComplex.closedCell m j, ∀ t, (next n P).1 (x,t)=P.1 (x,t) :=
          Classical.choose_spec (hstep n P)
        let seq : (n : ℕ) → Pack n := fun n => Nat.rec init (fun n P => next n P) n
        have hseq (n : ℕ) : seq (n+1)=next n (seq n) := rfl
        have hstable (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) m)
            (x : X) (hx : x ∈ RelCWComplex.closedCell m i) (t : I)
            (a b : ℕ) (hma : m ≤ a) (hab : a ≤ b) : (seq b).1 (x,t)=(seq a).1 (x,t) := by
          induction b,hab using Nat.le_induction with
          | base => rfl
          | succ b hab ih =>
            rw [hseq]
            exact (hnext b (seq b) m (hma.trans hab) i x hx t).trans ih
        have hcover (x : X) : ∃ n : ℕ, ∃ i : RelCWComplex.cell (Set.univ : Set X) n,
            x ∈ RelCWComplex.closedCell n i := by
          have hx : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
              RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
          simpa only [mem_iUnion] using hx
        choose dim cell hcell using hcover
        let H : X × I → Z := fun q => (seq (dim q.1)).1 q
        have hHcell (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) m)
            (x : X) (hx : x ∈ RelCWComplex.closedCell m i) (t : I) :
            H (x,t)=(seq m).1 (x,t) := by
          rcases le_total m (dim x) with h | h
          · exact hstable m i x hx t m (dim x) (le_refl _) h
          · exact (hstable (dim x) (cell x) x (hcell x) t (dim x) m (le_refl _) h).symm
        have hH : Continuous H := by
          apply continuous_iff_isClosed.mpr
          intro S hS
          apply cw_cylinder_closed X
          intro n i
          have hc : Continuous (fun q : (closedBall (0 : Fin n → ℝ) 1) × I =>
              H (RelCWComplex.map n i q.1,q.2)) := by
            apply ((seq n).2.2.2 n (le_refl _) i).congr
            intro q
            exact (hHcell n i _ ⟨q.1,q.1.2,rfl⟩ q.2).symm
          exact hS.preimage hc
        exact ⟨⟨H,hH⟩,fun x => (seq (dim x)).2.1 x,fun t => (seq (dim v)).2.2.1 t⟩
      refine ⟨isClosed_singleton,?_⟩
      intro Z f p hp
      exact cw_vertex_hep X Z i f p hp
    have cw_point_joined_vertex (X : Type u) [TopologicalSpace X]
        [CWComplex (Set.univ : Set X)] (x : X) :
        ∃ i : RelCWComplex.cell (Set.univ : Set X) 0,
          Joined x (RelCWComplex.map 0 i 0) := by
      have hpc (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n) :
          IsPathConnected (RelCWComplex.closedCell n i) := by
        exact (Metric.isPathConnected_closedBall (x := (0 : Fin n → ℝ)) (by norm_num : (0:ℝ) ≤ 1)).image'
          (RelCWComplex.continuousOn n i)
      have hcell : ∀ n (i : RelCWComplex.cell (Set.univ : Set X) n),
          ∀ y ∈ RelCWComplex.closedCell n i,
            ∃ j : RelCWComplex.cell (Set.univ : Set X) 0,
              Joined y (RelCWComplex.map 0 j 0) := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n ih =>
          intro i y hy
          by_cases hn : n=0
          · subst n
            have he : (![] : Fin 0 → ℝ)=0 := Subsingleton.elim _ _
            rw [RelCWComplex.closedCell_zero_eq_singleton,he] at hy
            obtain rfl := Set.mem_singleton_iff.mp hy
            exact ⟨i,Joined.refl _⟩
          · obtain ⟨z,hz⟩ := RelCWComplex.nonempty_cellFrontier (C := (Set.univ : Set X)) hn i
            obtain ⟨J,hJ⟩ := CWComplex.cellFrontier_subset_finite_closedCell
              (C := (Set.univ : Set X)) n i
            have hzlow := hJ hz
            simp only [Set.mem_iUnion,exists_prop] at hzlow
            obtain ⟨m,hm,j,_,hzj⟩ := hzlow
            obtain ⟨v,hv⟩ := ih m hm j z hzj
            have hyz : Joined y z := ((hpc n i).joinedIn y hy z
              (RelCWComplex.cellFrontier_subset_closedCell n i hz)).joined
            exact ⟨v,hyz.trans hv⟩
      have hx : x ∈ ⋃ n, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
          RelCWComplex.closedCell n i := by
        rw [CWComplex.union]
        exact Set.mem_univ x
      simp only [Set.mem_iUnion] at hx
      obtain ⟨n,i,hi⟩ := hx
      exact hcell n i x hi
    have basedPointChange (X : BasedSpace.{u}) (y : X) (γ : Path X.point y)
        (hX : X.IsWellBased) (hY : (⟨X.space,y⟩ : BasedSpace.{u}).IsWellBased) :
        let Y : BasedSpace.{u} := ⟨X.space,y⟩
        ∃ (f : X ⟶ Y) (g : Y ⟶ X),
          (g.map.comp f.map).HomotopicRel (ContinuousMap.id X) {X.point} ∧
          (f.map.comp g.map).HomotopicRel (ContinuousMap.id Y) {Y.point} := by
      have rectify (A B : BasedSpace.{u}) (hA : A.IsWellBased) (p p' : A ⟶ B)
          (W : p.map.Homotopy p'.map) (δ : Path B.point B.point)
          (hW : ∀ t, W (t,A.point)=δ t)
          (hδ : δ.Homotopic (Path.refl B.point)) :
          p.map.HomotopicRel p'.map {A.point} := by
        obtain ⟨D⟩ := hδ
        let initial : C(A,C(I,B)) :=
          (W.toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩).curry
        obtain ⟨F,hF0,hFp⟩ := hA.2 (TopCat.of C(I,B)) initial D.toHomotopy.toContinuousMap.curry (by
          ext t
          change D (0,t)=W (t,A.point)
          rw [D.apply_zero,hW]
          rfl)
        let a : C(A,B) := ⟨fun x => F (x,1) 0,by fun_prop⟩
        let b : C(A,B) := ⟨fun x => F (x,1) 1,by fun_prop⟩
        have hpa : p.map.HomotopicRel a {A.point} := by
          refine ⟨{ toFun := fun z => F (z.2,z.1) 0
                    continuous_toFun := by fun_prop
                    map_zero_left := ?_
                    map_one_left := fun _ => rfl
                    prop' := ?_ }⟩
          · intro x
            rw [hF0]
            exact W.apply_zero x
          · intro t x hx
            obtain rfl := Set.mem_singleton_iff.mp hx
            change F (A.point,t) 0=p.map A.point
            rw [hFp]
            exact (D.source t).trans p.point.symm
        have hab : a.HomotopicRel b {A.point} := by
          refine ⟨{ toFun := fun z => F (z.2,1) z.1
                    continuous_toFun := by fun_prop
                    map_zero_left := fun _ => rfl
                    map_one_left := fun _ => rfl
                    prop' := ?_ }⟩
          intro t x hx
          obtain rfl := Set.mem_singleton_iff.mp hx
          change F (A.point,1) t=F (A.point,1) 0
          rw [hFp]
          change D (1,t)=D (1,0)
          rw [D.apply_one,D.apply_one]
          rfl
        have hpb : p'.map.HomotopicRel b {A.point} := by
          refine ⟨{ toFun := fun z => F (z.2,z.1) 1
                    continuous_toFun := by fun_prop
                    map_zero_left := ?_
                    map_one_left := fun _ => rfl
                    prop' := ?_ }⟩
          · intro x
            rw [hF0]
            exact W.apply_one x
          · intro t x hx
            obtain rfl := Set.mem_singleton_iff.mp hx
            change F (A.point,t) 1=p'.map A.point
            rw [hFp]
            exact (D.target t).trans p'.point.symm
        exact hpa.trans (hab.trans hpb.symm)
      let Y : BasedSpace.{u} := ⟨X.space,y⟩
      change ∃ (f : X ⟶ Y) (g : Y ⟶ X),
        (g.map.comp f.map).HomotopicRel (ContinuousMap.id X) {X.point} ∧
        (f.map.comp g.map).HomotopicRel (ContinuousMap.id Y) {Y.point}
      obtain ⟨H,hH0,hHp⟩ := hX.2 X.space (ContinuousMap.id X) γ.toContinuousMap γ.source
      obtain ⟨K,hK0,hKp⟩ := hY.2 Y.space (ContinuousMap.id Y) γ.symm.toContinuousMap γ.symm.source
      let f : X ⟶ Y :=
        ⟨⟨fun x => H (x,1),H.continuous.comp (continuous_id.prodMk continuous_const)⟩,
          (hHp 1).trans γ.target⟩
      let g : Y ⟶ X :=
        ⟨⟨fun x => K (x,1),K.continuous.comp (continuous_id.prodMk continuous_const)⟩,
          (hKp 1).trans γ.symm.target⟩
      let HX : (ContinuousMap.id X).Homotopy f.map :=
        { toFun := fun z => H (z.2,z.1)
          continuous_toFun := H.continuous.comp continuous_swap
          map_zero_left := hH0
          map_one_left := fun _ => rfl }
      let KY : (ContinuousMap.id Y).Homotopy g.map :=
        { toFun := fun z => K (z.2,z.1)
          continuous_toFun := K.continuous.comp continuous_swap
          map_zero_left := hK0
          map_one_left := fun _ => rfl }
      let WX : (ContinuousMap.id X).Homotopy (g.map.comp f.map) :=
        HX.trans (KY.compContinuousMap f.map)
      let WY : (ContinuousMap.id Y).Homotopy (f.map.comp g.map) :=
        KY.trans (HX.compContinuousMap g.map)
      have hWX (t : I) : WX (t,X.point)=(γ.trans γ.symm) t := by
        have ha (s : I) : HX (s,X.point)=γ s := hHp s
        have hb (s : I) : (KY.compContinuousMap f.map) (s,X.point)=γ.symm s := by
          change K (f.map X.point,s)=γ.symm s
          rw [f.point]
          exact hKp s
        change (HX.trans (KY.compContinuousMap f.map)) (t,X.point)=(γ.trans γ.symm) t
        rw [ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
        split_ifs <;> first | exact ha _ | exact hb _
      have hWY (t : I) : WY (t,Y.point)=(γ.symm.trans γ) t := by
        have ha (s : I) : KY (s,Y.point)=γ.symm s := hKp s
        have hb (s : I) : (HX.compContinuousMap g.map) (s,Y.point)=γ s := by
          change H (g.map Y.point,s)=γ s
          rw [g.point]
          exact hHp s
        change (KY.trans (HX.compContinuousMap g.map)) (t,Y.point)=(γ.symm.trans γ) t
        rw [ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
        split_ifs <;> first | exact ha _ | exact hb _
      refine ⟨f,g,?_,?_⟩
      · exact (rectify X X hX (𝟙 X) (f ≫ g) WX (γ.trans γ.symm) hWX
          (Path.Homotopic.trans_symm γ)).symm
      · have hδ : (γ.symm.trans γ).Homotopic (Path.refl Y.point) := by
          simpa only [Path.symm_symm] using Path.Homotopic.trans_symm γ.symm
        exact (rectify Y Y hY (𝟙 Y) (g ≫ f) WY (γ.symm.trans γ) hWY hδ).symm
    obtain ⟨i,⟨γ⟩⟩ := cw_point_joined_vertex X X.point
    have hY := cw_vertex_wellBased X i
    refine ⟨i,hY,?_⟩
    exact basedPointChange X (RelCWComplex.map 0 i 0) γ hX hY
  have compactlyGenerated_kification (T : Type u) [t : TopologicalSpace T] :
      @UCompactlyGeneratedSpace.{u} T (TopologicalSpace.compactlyGenerated.{u} T) := by
    let ev : (Σ i : (S : CompHaus.{u}) × C(S,T), i.fst) → T := fun p => p.1.2 p.2
    letI : TopologicalSpace T := TopologicalSpace.coinduced ev inferInstance
    exact uCompactlyGeneratedSpace_of_coinduced
      (show Continuous ev from continuous_coinduced_rng) rfl
  have cg_prod_interval (T : Type u) [TopologicalSpace T]
      [UCompactlyGeneratedSpace.{u} T] : UCompactlyGeneratedSpace.{u} (T × I) := by
    apply uCompactlyGeneratedSpace_of_continuous_maps
    intro Y _ f hf
    let F : T → C(I,Y) := fun a => ⟨fun t => f (a,t),by
      have hc := hf (CompHaus.of (ULift.{u} I))
        ⟨fun t => (a,t.down),continuous_const.prodMk continuous_uliftDown⟩
      exact hc.comp continuous_uliftUp⟩
    have hF : Continuous F := by
      apply continuous_from_uCompactlyGeneratedSpace
      intro S g
      have hg : Continuous (fun p : S × I => f (g p.1,p.2)) :=
        hf (CompHaus.of (S × I)) ⟨fun p => (g p.1,p.2),
          (g.continuous.comp continuous_fst).prodMk continuous_snd⟩
      exact (ContinuousMap.curry ⟨_,hg⟩).continuous
    exact ContinuousMap.continuous_uncurry_of_continuous ⟨F,hF⟩
  have smash_family {X Y X' Y' : BasedSpace.{u}}
      (f : C(X × I,X')) (g : C(Y × I,Y'))
      (hf : ∀ t, f (X.point,t)=X'.point) (hg : ∀ t, g (Y.point,t)=Y'.point) :
      ∃ H : C((X.smash Y) × I,X'.smash Y'),
        (∀ x y t, H (smashPoint X Y x y,t)=smashPoint X' Y' (f (x,t)) (g (y,t))) ∧
        (∀ t, H ((X.smash Y).point,t)=(X'.smash Y').point) := by
    have into_k {T : Type u} [TopologicalSpace T] (K : CompHaus.{u}) (v : C(K,T)) :
        Continuous[inferInstance,TopologicalSpace.compactlyGenerated.{u} T] v := by
      let ev : (Σ i : (S : CompHaus.{u}) × C(S,T),i.fst) → T := fun q => q.1.2 q.2
      have hi : Continuous (fun k : K => (⟨⟨K,v⟩,k⟩ :
          Σ i : (S : CompHaus.{u}) × C(S,T),i.fst)) :=
        @continuous_sigmaMk _ (fun i : (S : CompHaus.{u}) × C(S,T) => i.fst)
          (fun _ => inferInstance) ⟨K,v⟩
      letI : TopologicalSpace T := TopologicalSpace.coinduced ev inferInstance
      exact (show Continuous ev from continuous_coinduced_rng).comp hi
    have qcompact (S : CompHaus.{u}) (gx : C(S,X')) (gy : C(S,Y')) :
        Continuous (fun s => smashPoint X' Y' (gx s) (gy s)) := by
      have hc := into_k S (⟨fun s => (gx s,gy s),gx.continuous.prodMk gy.continuous⟩ : C(S,X' × Y'))
      letI : TopologicalSpace (X' × Y') := TopologicalSpace.compactlyGenerated.{u} (X' × Y')
      exact continuous_quot_mk.comp hc
    have hid : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),inferInstance]
        (id : X × Y → X × Y) :=
      continuous_from_compactlyGenerated id (fun S v => v.continuous)
    have hfst : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),inferInstance]
        (Prod.fst : X × Y → X) :=
      @Continuous.comp (X × Y) (X × Y) X (TopologicalSpace.compactlyGenerated.{u} (X × Y))
        inferInstance inferInstance id Prod.fst continuous_fst hid
    have hsnd : Continuous[TopologicalSpace.compactlyGenerated.{u} (X × Y),inferInstance]
        (Prod.snd : X × Y → Y) :=
      @Continuous.comp (X × Y) (X × Y) Y (TopologicalSpace.compactlyGenerated.{u} (X × Y))
        inferInstance inferInstance id Prod.snd continuous_snd hid
    have hcg := compactlyGenerated_kification (X × Y)
    letI : TopologicalSpace (X × Y) := TopologicalSpace.compactlyGenerated.{u} (X × Y)
    letI : UCompactlyGeneratedSpace.{u} (X × Y) := hcg
    letI : UCompactlyGeneratedSpace.{u} ((X × Y) × I) := cg_prod_interval (X × Y)
    let raw (p : (X × Y) × I) := smashPoint X' Y' (f (p.1.1,p.2)) (g (p.1.2,p.2))
    have hraw : Continuous raw := by
      apply continuous_from_uCompactlyGeneratedSpace
      intro S v
      exact qcompact S
        ⟨_,f.continuous.comp ((hfst.comp v.continuous.fst).prodMk v.continuous.snd)⟩
        ⟨_,g.continuous.comp ((hsnd.comp v.continuous.fst).prodMk v.continuous.snd)⟩
    have collapsed (p : X × Y) (t : I) (hp : p.1=X.point ∨ p.2=Y.point) :
        raw (p,t)=(X'.smash Y').point := by
      dsimp [raw]
      rcases hp with h | h
      · rw [h,hf,smashPoint_base_left]
      · rw [h,hg,smashPoint_base_right]
    have respects (t : I) : ∀ a b, SmashRelation X Y a b → raw (a,t)=raw (b,t) :=
      fun a b hab => (collapsed a t hab.1).trans (collapsed b t hab.2).symm
    let H : C((X.smash Y) × I,X'.smash Y') :=
      ⟨fun p => Quot.lift (fun a => raw (a,p.2)) (respects p.2) p.1,by
        apply isQuotientMap_quot_mk.continuous_lift_prod_left
        exact hraw⟩
    exact ⟨H,fun _ _ _ => rfl,fun t => collapsed (X.point,Y.point) t (Or.inl rfl)⟩
  have smash_homotopicRel {A B A' B' : BasedSpace.{u}}
      (f f' : A ⟶ A') (g g' : B ⟶ B')
      (hA : f.map.HomotopicRel f'.map {A.point})
      (hB : g.map.HomotopicRel g'.map {B.point}) :
      (smashMap f g).map.HomotopicRel (smashMap f' g').map {(A.smash B).point} := by
    have hm {P Q P' Q' : BasedSpace.{u}} (a : P ⟶ P') (b : Q ⟶ Q') (x : P) (y : Q) :
        (smashMap a b).map (smashPoint P Q x y)=smashPoint P' Q' (a.map x) (b.map y) :=
      (smashMap_exists a b).exists.choose_spec x y
    obtain ⟨H⟩ := hA
    obtain ⟨K⟩ := hB
    let hf : C(A × I,A') := ⟨fun p => H (p.2,p.1),H.continuous.comp continuous_swap⟩
    let hg : C(B × I,B') := ⟨fun p => K (p.2,p.1),K.continuous.comp continuous_swap⟩
    obtain ⟨L,hL,hLp⟩ := smash_family hf hg
      (fun t => (H.eq_fst t (Set.mem_singleton _)).trans f.point)
      (fun t => (K.eq_fst t (Set.mem_singleton _)).trans g.point)
    refine ⟨{ toFun := fun p => L (p.2,p.1)
              continuous_toFun := L.continuous.comp continuous_swap
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro z
      refine Quot.inductionOn z ?_
      rintro ⟨a,b⟩
      change L (smashPoint A B a b,0)=(smashMap f g).map (smashPoint A B a b)
      rw [hL,hm]
      change smashPoint A' B' (H (0,a)) (K (0,b))=smashPoint A' B' (f.map a) (g.map b)
      rw [H.apply_zero,K.apply_zero]
    · intro z
      refine Quot.inductionOn z ?_
      rintro ⟨a,b⟩
      change L (smashPoint A B a b,1)=(smashMap f' g').map (smashPoint A B a b)
      rw [hL,hm]
      change smashPoint A' B' (H (1,a)) (K (1,b))=smashPoint A' B' (f'.map a) (g'.map b)
      rw [H.apply_one,K.apply_one]
    · intro t z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact (hLp t).trans (smashMap f g).point.symm
  have hasCWType_of_based_equivalence {A B : BasedSpace.{u}}
      (f : A ⟶ B) (g : B ⟶ A)
      (hA : (g.map.comp f.map).HomotopicRel (ContinuousMap.id A) {A.point})
      (hB : (f.map.comp g.map).HomotopicRel (ContinuousMap.id B) {B.point})
      (hCW : B.HasCWType) : A.HasCWType := by
    have precomp {P Q R : BasedSpace.{u}} (a b : Q ⟶ R)
        (h : a.map.HomotopicRel b.map {Q.point}) (c : P ⟶ Q) :
        (a.map.comp c.map).HomotopicRel (b.map.comp c.map) {P.point} := by
      obtain ⟨H⟩ := h
      refine ⟨{ toHomotopy := H.toHomotopy.compContinuousMap c.map, prop' := ?_ }⟩
      intro t p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      change H (t,c.map P.point) = a.map (c.map P.point)
      rw [c.point]
      exact H.eq_fst t (Set.mem_singleton _)
    obtain ⟨Z,hT,hC,hZ,p,q,h₁,h₂⟩ := hCW
    refine ⟨Z,hT,hC,hZ,f ≫ p,q ≫ g,?_,?_⟩
    · have h := (precomp (p ≫ q) (𝟙 B) h₁ f).comp_continuousMap g.map
      have hh : ((q ≫ g).map.comp (f ≫ p).map).HomotopicRel
          (g.map.comp f.map) {A.point} := by
        convert h using 1 <;> ext z <;> rfl
      exact hh.trans hA
    · have h := (precomp (g ≫ f) (𝟙 B) hB q).comp_continuousMap p.map
      have hh : ((f ≫ p).map.comp (q ≫ g).map).HomotopicRel
          (p.map.comp q.map) {Z.point} := by
        convert h using 1 <;> ext z <;> rfl
      exact hh.trans h₂
  have smash_preserves_based_equivalence {A B X Y : BasedSpace.{u}}
      (f : A ⟶ X) (f' : X ⟶ A) (g : B ⟶ Y) (g' : Y ⟶ B)
      (hA : (f'.map.comp f.map).HomotopicRel (ContinuousMap.id A) {A.point})
      (hX : (f.map.comp f'.map).HomotopicRel (ContinuousMap.id X) {X.point})
      (hB : (g'.map.comp g.map).HomotopicRel (ContinuousMap.id B) {B.point})
      (hY : (g.map.comp g'.map).HomotopicRel (ContinuousMap.id Y) {Y.point}) :
      ((smashMap f' g').map.comp (smashMap f g).map).HomotopicRel
        (ContinuousMap.id (A.smash B)) {(A.smash B).point} ∧
      ((smashMap f g).map.comp (smashMap f' g').map).HomotopicRel
        (ContinuousMap.id (X.smash Y)) {(X.smash Y).point} := by
    have hm {P Q P' Q' : BasedSpace.{u}} (a : P ⟶ P') (b : Q ⟶ Q') (x : P) (y : Q) :
        (smashMap a b).map (smashPoint P Q x y)=smashPoint P' Q' (a.map x) (b.map y) :=
      (smashMap_exists a b).exists.choose_spec x y
    have hcomp {P Q P' Q' P'' Q'' : BasedSpace.{u}}
        (a : P ⟶ P') (b : Q ⟶ Q') (c : P' ⟶ P'') (d : Q' ⟶ Q'') :
        (smashMap (a ≫ c) (b ≫ d)).map=(smashMap c d).map.comp (smashMap a b).map := by
      ext z
      refine Quot.inductionOn z ?_
      rintro ⟨x,y⟩
      change (smashMap (a ≫ c) (b ≫ d)).map (smashPoint P Q x y)=
        (smashMap c d).map ((smashMap a b).map (smashPoint P Q x y))
      rw [hm,hm,hm]
      rfl
    have hid (P Q : BasedSpace.{u}) :
        (smashMap (𝟙 P) (𝟙 Q)).map=ContinuousMap.id (P.smash Q) := by
      ext z
      refine Quot.inductionOn z ?_
      rintro ⟨x,y⟩
      exact hm (𝟙 P) (𝟙 Q) x y
    constructor
    · simpa only [hcomp,hid] using smash_homotopicRel (f ≫ f') (𝟙 A) (g ≫ g') (𝟙 B) hA hB
    · simpa only [hcomp,hid] using smash_homotopicRel (f' ≫ f) (𝟙 X) (g' ≫ g) (𝟙 Y) hX hY
  have smash_hasCWType_of_actual_cw_smash
      (hCW : ∀ (X Y : BasedSpace.{u}) [T2Space X] [T2Space Y]
        [CWComplex (Set.univ : Set X)] [CWComplex (Set.univ : Set Y)],
        X.IsWellBased → Y.IsWellBased → (X.smash Y).HasCWType)
      (A B : BasedSpace.{u}) (hA : A.HasCWType) (hB : B.HasCWType) :
      (A.smash B).HasCWType := by
    obtain ⟨X,hTX,⟨hCX⟩,hX,f,f',hA,hX'⟩ := hA
    obtain ⟨Y,hTY,⟨hCY⟩,hY,g,g',hB,hY'⟩ := hB
    letI := hTX
    letI := hTY
    letI := hCX
    letI := hCY
    have h := smash_preserves_based_equivalence f f' g g' hA hX' hB hY'
    exact hasCWType_of_based_equivalence (smashMap f g) (smashMap f' g') h.1 h.2
      (hCW X Y hX hY)
  apply smash_hasCWType_of_actual_cw_smash ?_ A B hA hB
  intro X Y _ _ _ _ hX hY
  obtain ⟨ix,hVX⟩ := cw_based_vertex_model X hX
  obtain ⟨iy,hVY⟩ := cw_based_vertex_model Y hY
  let VX : BasedSpace.{u} := ⟨X.space,RelCWComplex.map 0 ix 0⟩
  let VY : BasedSpace.{u} := ⟨Y.space,RelCWComplex.map 0 iy 0⟩
  change VX.IsWellBased ∧ ∃ (f : X ⟶ VX) (g : VX ⟶ X),
    (g.map.comp f.map).HomotopicRel (ContinuousMap.id X) {X.point} ∧
    (f.map.comp g.map).HomotopicRel (ContinuousMap.id VX) {VX.point} at hVX
  change VY.IsWellBased ∧ ∃ (f : Y ⟶ VY) (g : VY ⟶ Y),
    (g.map.comp f.map).HomotopicRel (ContinuousMap.id Y) {Y.point} ∧
    (f.map.comp g.map).HomotopicRel (ContinuousMap.id VY) {VY.point} at hVY
  obtain ⟨hVX,f,f',hX₀,hVX₀⟩ := hVX
  obtain ⟨hVY,g,g',hY₀,hVY₀⟩ := hVY
  have hactual : (VX.smash VY).HasCWType := by
    refine ⟨VX.smash VY,(smash_vertex_cw VX VY ix iy rfl rfl).1,(smash_vertex_cw VX VY ix iy rfl rfl).2,
      (smash_point_set VX VY hVX hVY).2,𝟙 _,𝟙 _,?_,?_⟩
    all_goals exact ContinuousMap.HomotopicRel.refl _
  have hh := smash_preserves_based_equivalence f f' g g' hX₀ hVX₀ hY₀ hVY₀
  exact hasCWType_of_based_equivalence (smashMap f g) (smashMap f' g') hh.1 hh.2 hactual

theorem good_smash {A B : BasedSpace.{u}} (hA : A.IsGood) (hB : B.IsGood) :
    (A.smash B).IsGood := by
  have hp := smash_point_set A B hA.2.1 hB.2.1
  exact ⟨hp.1,hp.2,smash_hasCWType A B hA.2.2 hB.2.2⟩

/-- The quotient representative [a;t₀,…,tₙ₋₁] in an iterated suspension. -/
def iteratedPoint (A : BasedSpace.{u}) : ∀ n, A → (Fin n → I) → A.iterateSuspension n
  | 0, a, _ => a
  | n+1, a, t => suspensionProjection _ (iteratedPoint A n a (fun i => t i.succ), t 0)

open Set Metric in
/-- The actual unreduced suspension has two vertices and one suspended cell
for each original cell. All characteristic maps and the weak topology are
constructed inside the proof. -/
private theorem suspension_cw_model (X : BasedSpace.{u}) [T2Space X]
    [CWComplex (Set.univ : Set X)] :
    let R (p q : X × I) : Prop := (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
    let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (X.point,0)⟩
    T2Space U ∧ Nonempty (CWComplex (Set.univ : Set U)) := by
  have unreduced_t2 (X : BasedSpace.{u}) [T2Space X] :
      let R (p q : X × I) : Prop :=
        (p.2 = 0 ∧ q.2 = 0) ∨ (p.2 = 1 ∧ q.2 = 1)
      let U : BasedSpace.{u} := ⟨TopCat.of (Quot R), Quot.mk R (X.point, 0)⟩
      T2Space U := by
    classical
    dsimp only
    let R (p q : X × I) : Prop :=
      (p.2 = 0 ∧ q.2 = 0) ∨ (p.2 = 1 ∧ q.2 = 1)
    let U : BasedSpace.{u} := ⟨TopCat.of (Quot R), Quot.mk R (X.point, 0)⟩
    change T2Space U
    let q : X × I → U := Quot.mk R
    have heq (p p' : X × I) : q p = q p' ↔ p = p' ∨ R p p' := by
      constructor
      · intro h
        have h' := Quot.eqvGen_exact h
        clear h
        induction h' with
        | rel a b hab => exact Or.inr hab
        | refl a => exact Or.inl rfl
        | symm a b hab ih =>
          rcases ih with h | (h | h)
          · exact Or.inl h.symm
          · exact Or.inr (Or.inl ⟨h.2,h.1⟩)
          · exact Or.inr (Or.inr ⟨h.2,h.1⟩)
        | trans a b c hab hbc ih₁ ih₂ =>
          rcases ih₁ with rfl | (h₁ | h₁)
          · exact ih₂
          · rcases ih₂ with rfl | (h₂ | h₂)
            · exact Or.inr (Or.inl h₁)
            · exact Or.inr (Or.inl ⟨h₁.1,h₂.2⟩)
            · exact False.elim (zero_ne_one (h₁.2.symm.trans h₂.1))
          · rcases ih₂ with rfl | (h₂ | h₂)
            · exact Or.inr (Or.inr h₁)
            · exact False.elim (zero_ne_one (h₂.1.symm.trans h₁.2))
            · exact Or.inr (Or.inr ⟨h₁.1,h₂.2⟩)
      · rintro (rfl | h)
        · rfl
        · exact Quot.sound h
    let height : U → I := Quot.lift Prod.snd (by
      intro p p' h
      rcases h with h | h
      · exact h.1.trans h.2.symm
      · exact h.1.trans h.2.symm)
    have hheight : Continuous height := continuous_quot_lift _ continuous_snd
    have hopen (S : Set (X × I)) (hS : IsOpen S)
        (hS₀ : ∀ p ∈ S, p.2 ≠ 0) (hS₁ : ∀ p ∈ S, p.2 ≠ 1) :
        IsOpen (q '' S) := by
      rw [← isQuotientMap_quot_mk.isOpen_preimage]
      convert hS using 1
      ext p
      constructor
      · rintro ⟨p',hp',hh⟩
        rcases (heq p' p).mp hh with rfl | (h | h)
        · exact hp'
        · exact False.elim (hS₀ p' hp' h.1)
        · exact False.elim (hS₁ p' hp' h.1)
      · intro hp
        exact ⟨p,hp,rfl⟩
    constructor
    intro a b hab
    obtain ⟨p,rfl⟩ := Quot.exists_rep a
    obtain ⟨p',rfl⟩ := Quot.exists_rep b
    by_cases ht : p.2 = p'.2
    · have h₀ : p.2 ≠ 0 := by
        intro h
        exact hab (Quot.sound (Or.inl ⟨h,ht.symm.trans h⟩))
      have h₁ : p.2 ≠ 1 := by
        intro h
        exact hab (Quot.sound (Or.inr ⟨h,ht.symm.trans h⟩))
      have hx : p.1 ≠ p'.1 := by
        intro h
        exact hab (congrArg q (Prod.ext h ht))
      obtain ⟨V,W,hV,hW,hp,hp',hVW⟩ := t2_separation hx
      let J : Set I := {t | t ≠ 0 ∧ t ≠ 1}
      have hJ : IsOpen J := (isClosed_singleton.isOpen_compl).inter
        (isClosed_singleton.isOpen_compl)
      refine ⟨q '' (V ×ˢ J), q '' (W ×ˢ J),
        hopen _ (hV.prod hJ) (fun z hz => hz.2.1) (fun z hz => hz.2.2),
        hopen _ (hW.prod hJ) (fun z hz => hz.2.1) (fun z hz => hz.2.2),
        ⟨p,⟨hp,h₀,h₁⟩,rfl⟩, ⟨p',⟨hp',ht ▸ h₀,ht ▸ h₁⟩,rfl⟩, ?_⟩
      apply Set.disjoint_left.mpr
      rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
      rcases (heq x y).mp (hxz.trans hyz.symm) with rfl | (h | h)
      · exact Set.disjoint_left.mp hVW hx.1 hy.1
      · exact hx.2.1 h.1
      · exact hx.2.2 h.1
    · obtain ⟨V,W,hV,hW,hp,hp',hVW⟩ := t2_separation ht
      refine ⟨height ⁻¹' V,height ⁻¹' W,hV.preimage hheight,hW.preimage hheight,
        hp,hp',hVW.preimage height⟩
  have unreduced_characteristic (X : BasedSpace.{u})
      [CWComplex (Set.univ : Set X)] (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n) :
      let R (p q : X × I) : Prop :=
        (p.2 = 0 ∧ q.2 = 0) ∨ (p.2 = 1 ∧ q.2 = 1)
      let T (s : ℝ) : I := Set.projIcc 0 1 zero_le_one ((s+1)/2)
      let f (z : Fin (n+1) → ℝ) : Quot R :=
        Quot.mk R (RelCWComplex.map n i (fun j => z j.succ),T (z 0))
      ContinuousOn f (Metric.closedBall 0 1) ∧
        f '' Metric.closedBall 0 1 =
          Quot.mk R '' ((RelCWComplex.map n i '' Metric.closedBall 0 1) ×ˢ Set.univ) ∧
        f '' Metric.ball 0 1 =
          Quot.mk R '' ((RelCWComplex.map n i '' Metric.ball 0 1) ×ˢ Set.Ioo 0 1) ∧
        Set.InjOn f (Metric.ball 0 1) := by
    classical
    dsimp only
    let R (p q : X × I) : Prop :=
      (p.2 = 0 ∧ q.2 = 0) ∨ (p.2 = 1 ∧ q.2 = 1)
    let T (s : ℝ) : I := Set.projIcc 0 1 zero_le_one ((s+1)/2)
    let f (z : Fin (n+1) → ℝ) : Quot R :=
      Quot.mk R (RelCWComplex.map n i (fun j => z j.succ),T (z 0))
    change ContinuousOn f _ ∧ f '' _ = _ ∧ f '' _ = _ ∧ Set.InjOn f _
    have hc (k : ℕ) (v : Fin k → ℝ) :
        v ∈ Metric.closedBall 0 1 ↔ ∀ j, -1 ≤ v j ∧ v j ≤ 1 := by
      rw [closedBall_pi _ (by norm_num : (0 : ℝ) ≤ 1)]
      simp [Real.closedBall_eq_Icc, Pi.le_def, forall_and]
    have hb (k : ℕ) (v : Fin k → ℝ) :
        v ∈ Metric.ball 0 1 ↔ ∀ j, -1 < v j ∧ v j < 1 := by
      rw [ball_pi _ (by norm_num : (0 : ℝ) < 1)]
      simp only [Set.mem_pi,Set.mem_univ,forall_const,Real.ball_eq_Ioo,Pi.zero_apply,
        zero_sub,zero_add,Set.mem_Ioo]
    have hT (s : ℝ) (h : -1 ≤ s ∧ s ≤ 1) : ((T s : I) : ℝ) = (s+1)/2 := by
      have hh : (s+1)/2 ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith
      exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hh)
    have hTi (s : ℝ) (h : -1 < s ∧ s < 1) : T s ∈ Set.Ioo (0:I) 1 := by
      have ht := hT s ⟨h.1.le,h.2.le⟩
      change 0 < (T s : ℝ) ∧ (T s : ℝ) < 1
      rw [ht]
      constructor <;> linarith
    have hTr (t : I) : T (2*(t:ℝ)-1) = t := by
      apply Subtype.ext
      rw [hT _ (by
        have h : (0:ℝ) ≤ t ∧ (t:ℝ) ≤ 1 := t.property
        constructor <;> linarith)]
      ring
    have hcons (v : Fin n → ℝ) (hv : v ∈ Metric.closedBall 0 1) (t : I) :
        (Fin.cons (2*(t:ℝ)-1) v : Fin (n+1) → ℝ) ∈ Metric.closedBall 0 1 := by
      apply (hc _ _).mpr
      intro j
      induction j using Fin.cases with
      | zero =>
        change -1 ≤ 2*(t:ℝ)-1 ∧ 2*(t:ℝ)-1 ≤ 1
        have h : (0:ℝ) ≤ t ∧ (t:ℝ) ≤ 1 := t.property
        constructor <;> linarith
      | succ j => exact (hc _ _).mp hv j
    have hcons' (v : Fin n → ℝ) (hv : v ∈ Metric.ball 0 1) (t : I)
        (ht : t ∈ Set.Ioo (0:I) 1) :
        (Fin.cons (2*(t:ℝ)-1) v : Fin (n+1) → ℝ) ∈ Metric.ball 0 1 := by
      apply (hb _ _).mpr
      intro j
      induction j using Fin.cases with
      | zero =>
        change -1 < 2*(t:ℝ)-1 ∧ 2*(t:ℝ)-1 < 1
        have h : (0:ℝ) < t ∧ (t:ℝ) < 1 := ht
        constructor <;> linarith
      | succ j => exact (hb _ _).mp hv j
    have hfcons (v : Fin n → ℝ) (t : I) :
        f (Fin.cons (2*(t:ℝ)-1) v) = Quot.mk R (RelCWComplex.map n i v,t) := by
      change Quot.mk R (RelCWComplex.map n i v,T (2*(t:ℝ)-1)) = _
      rw [hTr]
    refine ⟨?_,?_,?_,?_⟩
    · apply continuous_quot_mk.comp_continuousOn
      apply ContinuousOn.prodMk
      · apply (RelCWComplex.continuousOn n i).comp
          (continuous_pi fun j => continuous_apply j.succ).continuousOn
        intro z hz
        exact (hc _ _).mpr (fun j => (hc _ _).mp hz j.succ)
      · exact (continuous_projIcc.comp
          (((continuous_apply 0).add continuous_const).div_const 2)).continuousOn
    · ext z
      constructor
      · rintro ⟨v,hv,rfl⟩
        exact ⟨_,⟨⟨_,(hc _ _).mpr (fun j => (hc _ _).mp hv j.succ),rfl⟩,trivial⟩,rfl⟩
      · rintro ⟨⟨x,t⟩,⟨⟨v,hv,rfl⟩,_⟩,rfl⟩
        exact ⟨_,hcons v hv t,hfcons v t⟩
    · ext z
      constructor
      · rintro ⟨v,hv,rfl⟩
        exact ⟨_,⟨⟨_,(hb _ _).mpr (fun j => (hb _ _).mp hv j.succ),rfl⟩,
          hTi _ ((hb _ _).mp hv 0)⟩,rfl⟩
      · rintro ⟨⟨x,t⟩,⟨⟨v,hv,rfl⟩,ht⟩,rfl⟩
        exact ⟨_,hcons' v hv t ht,hfcons v t⟩
    · intro v hv w hw he
      have hinj : Set.InjOn (Quot.mk R)
          {p : X × I | p.2 ≠ 0 ∧ p.2 ≠ 1} := by
        intro p hp p' hp' h
        have h' := Quot.eqvGen_exact h
        clear h
        have hrel : ∀ a b, Relation.EqvGen R a b → a=b ∨ R a b := by
          intro a b hab
          induction hab with
          | rel a b h => exact Or.inr h
          | refl a => exact Or.inl rfl
          | symm a b h ih =>
            rcases ih with h | (h | h)
            · exact Or.inl h.symm
            · exact Or.inr (Or.inl ⟨h.2,h.1⟩)
            · exact Or.inr (Or.inr ⟨h.2,h.1⟩)
          | trans a b c hab hbc ih₁ ih₂ =>
            rcases ih₁ with rfl | (h₁ | h₁)
            · exact ih₂
            · rcases ih₂ with rfl | (h₂ | h₂)
              · exact Or.inr (Or.inl h₁)
              · exact Or.inr (Or.inl ⟨h₁.1,h₂.2⟩)
              · exact False.elim (zero_ne_one (h₁.2.symm.trans h₂.1))
            · rcases ih₂ with rfl | (h₂ | h₂)
              · exact Or.inr (Or.inr h₁)
              · exact False.elim (zero_ne_one (h₂.1.symm.trans h₁.2))
              · exact Or.inr (Or.inr ⟨h₁.1,h₂.2⟩)
        rcases hrel _ _ h' with h | (h | h)
        · exact h
        · exact False.elim (hp.1 h.1)
        · exact False.elim (hp.2 h.1)
      have hpair := hinj
        (show (RelCWComplex.map n i (fun j => v j.succ),T (v 0)) ∈
          {p : X × I | p.2 ≠ 0 ∧ p.2 ≠ 1} from
          ⟨(hTi _ ((hb _ _).mp hv 0)).1.ne', (hTi _ ((hb _ _).mp hv 0)).2.ne⟩)
        (show (RelCWComplex.map n i (fun j => w j.succ),T (w 0)) ∈
          {p : X × I | p.2 ≠ 0 ∧ p.2 ≠ 1} from
          ⟨(hTi _ ((hb _ _).mp hw 0)).1.ne', (hTi _ ((hb _ _).mp hw 0)).2.ne⟩) he
      have htail : (fun j : Fin n => v j.succ) = (fun j : Fin n => w j.succ) :=
        (RelCWComplex.map n i).injOn
          (by rw [RelCWComplex.source_eq]; exact (hb _ _).mpr (fun j => (hb _ _).mp hv j.succ))
          (by rw [RelCWComplex.source_eq]; exact (hb _ _).mpr (fun j => (hb _ _).mp hw j.succ))
          (congrArg Prod.fst hpair)
      have htime := congrArg (fun p : X × I => (p.2 : ℝ)) hpair
      rw [hT _ ⟨((hb _ _).mp hv 0).1.le,((hb _ _).mp hv 0).2.le⟩,
        hT _ ⟨((hb _ _).mp hw 0).1.le,((hb _ _).mp hw 0).2.le⟩] at htime
      funext j
      induction j using Fin.cases with
      | zero => linarith
      | succ j => exact congrFun htail j
  have cw_cylinder_closed (X : Type u) [TopologicalSpace X] [T2Space X]
      [CWComplex (Set.univ : Set X)] (F : Set (X × I))
      (hF : ∀ n (i : RelCWComplex.cell (Set.univ : Set X) n),
        IsClosed ((fun p : (closedBall (0 : Fin n → ℝ) 1) × I =>
          (RelCWComplex.map n i p.1,p.2)) ⁻¹' F)) : IsClosed F := by
    let A := Σ n : ℕ, Σ i : RelCWComplex.cell (Set.univ : Set X) n,
      closedBall (0 : Fin n → ℝ) 1
    let π : A → X := fun a => RelCWComplex.map a.1 a.2.1 a.2.2
    have hπcont : Continuous π := by
      apply continuous_sigma
      intro n
      apply continuous_sigma
      intro i
      exact (RelCWComplex.continuousOn n i).restrict
    have hπsurj : Function.Surjective π := by
      intro x
      have h : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
          RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
      obtain ⟨n,i,z,hz,hx⟩ := by simpa only [Set.mem_iUnion,RelCWComplex.closedCell,Set.mem_image] using h
      exact ⟨⟨n,i,z,hz⟩,hx⟩
    have hπ : IsQuotientMap π := by
      apply isQuotientMap_iff_isClosed.mpr
      refine ⟨hπsurj,fun S => ⟨fun hS => hS.preimage hπcont,?_⟩⟩
      intro hS
      apply (CWComplex.closed (Set.univ : Set X) S (Set.subset_univ S)).mpr
      intro n i
      let c : C(closedBall (0 : Fin n → ℝ) 1,X) :=
        ⟨fun z => RelCWComplex.map n i z,(RelCWComplex.continuousOn n i).restrict⟩
      have hc : IsClosed (c ⁻¹' S) := by
        exact hS.preimage (continuous_sigmaMk.comp continuous_sigmaMk)
      have him : c '' (c ⁻¹' S)=S ∩ RelCWComplex.closedCell n i := by
        ext x
        constructor
        · rintro ⟨z,hz,rfl⟩
          exact ⟨hz,⟨z,z.property,rfl⟩⟩
        · rintro ⟨hx,z,hz,rfl⟩
          exact ⟨⟨z,hz⟩,hx,rfl⟩
      rw [← him]
      exact (hc.isCompact.image c.continuous).isClosed
    have hprod : IsClosed ((fun p : A × I => (π p.1,p.2)) ⁻¹' F) := by
      let e : A × I ≃ₜ Σ n : ℕ,
          (Σ i : RelCWComplex.cell (Set.univ : Set X) n,
            closedBall (0 : Fin n → ℝ) 1) × I := Homeomorph.sigmaProdDistrib
      apply e.symm.isQuotientMap.isCoinducing.isClosed_preimage.mp
      apply isClosed_sigma_iff.mpr
      intro n
      let e' : (Σ i : RelCWComplex.cell (Set.univ : Set X) n,
          closedBall (0 : Fin n → ℝ) 1) × I ≃ₜ
          Σ i : RelCWComplex.cell (Set.univ : Set X) n,
            (closedBall (0 : Fin n → ℝ) 1) × I := Homeomorph.sigmaProdDistrib
      apply e'.symm.isQuotientMap.isCoinducing.isClosed_preimage.mp
      apply isClosed_sigma_iff.mpr
      intro i
      exact hF n i
    let liftπ : A × I → ULift.{u} (X × I) := fun p => ⟨π p.1,p.2⟩
    letI : TopologicalSpace (ULift.{u} (X × I)) := TopologicalSpace.coinduced liftπ inferInstance
    have hs : IsClosed {q : ULift.{u} (X × I) | q.down ∈ F} := by
      rw [isClosed_coinduced]
      exact hprod
    have hc : Continuous (fun p : X × I => (⟨p⟩ : ULift.{u} (X × I))) := by
      apply hπ.continuous_lift_prod_left
      exact continuous_coinduced_rng
    exact hs.preimage hc
  have unreduced_cell_partition (X : BasedSpace.{u})
      [CWComplex (Set.univ : Set X)] :
      let R (p q : X × I) : Prop :=
        (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
      let q : X × I → Quot R := Quot.mk R
      let D (a : Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n) : Set (Quot R) :=
        q '' ((RelCWComplex.map a.1 a.2 '' Metric.ball 0 1) ×ˢ Set.Ioo 0 1)
      Pairwise (fun a b => Disjoint (D a) (D b)) ∧
        (∀ a, Disjoint (D a) {q (X.point,0),q (X.point,1)}) ∧
        q (X.point,0) ≠ q (X.point,1) := by
    classical
    dsimp only
    let R (p q : X × I) : Prop :=
      (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
    let q : X × I → Quot R := Quot.mk R
    let D (a : Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n) : Set (Quot R) :=
      q '' ((RelCWComplex.map a.1 a.2 '' Metric.ball 0 1) ×ˢ Set.Ioo 0 1)
    change Pairwise (fun a b => Disjoint (D a) (D b)) ∧
        (∀ a, Disjoint (D a) {q (X.point,0),q (X.point,1)}) ∧
        q (X.point,0) ≠ q (X.point,1)
    have heq (p p' : X × I) : q p = q p' ↔ p = p' ∨ R p p' := by
      constructor
      · intro h
        have h' := Quot.eqvGen_exact h
        clear h
        induction h' with
        | rel a b hab => exact Or.inr hab
        | refl a => exact Or.inl rfl
        | symm a b hab ih =>
          rcases ih with h | (h | h)
          · exact Or.inl h.symm
          · exact Or.inr (Or.inl ⟨h.2,h.1⟩)
          · exact Or.inr (Or.inr ⟨h.2,h.1⟩)
        | trans a b c hab hbc ih₁ ih₂ =>
          rcases ih₁ with rfl | (h₁ | h₁)
          · exact ih₂
          · rcases ih₂ with rfl | (h₂ | h₂)
            · exact Or.inr (Or.inl h₁)
            · exact Or.inr (Or.inl ⟨h₁.1,h₂.2⟩)
            · exact False.elim (zero_ne_one (h₁.2.symm.trans h₂.1))
          · rcases ih₂ with rfl | (h₂ | h₂)
            · exact Or.inr (Or.inr h₁)
            · exact False.elim (zero_ne_one (h₂.1.symm.trans h₁.2))
            · exact Or.inr (Or.inr ⟨h₁.1,h₂.2⟩)
      · rintro (rfl | h)
        · rfl
        · exact Quot.sound h
    let height : Quot R → I := Quot.lift Prod.snd (by
      intro p p' h
      rcases h with h | h
      · exact h.1.trans h.2.symm
      · exact h.1.trans h.2.symm)
    refine ⟨?_,?_,?_⟩
    · intro a b hab
      apply Set.disjoint_left.mpr
      rintro z ⟨p,hp,hpz⟩ ⟨p',hp',hp'z⟩
      rcases (heq p p').mp (hpz.trans hp'z.symm) with h | (h | h)
      · subst p'
        exact Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hab) hp.1 hp'.1
      · exact hp.2.1.ne' h.1
      · exact hp.2.2.ne h.1
    · intro a
      apply Set.disjoint_left.mpr
      rintro z ⟨p,hp,hpz⟩ hz
      rcases Set.mem_insert_iff.mp hz with h0 | h1
      · have ht : p.2=0 := congrArg height (hpz.trans h0)
        exact hp.2.1.ne' ht
      · have ht : p.2=1 := congrArg height (hpz.trans (Set.mem_singleton_iff.mp h1))
        exact hp.2.2.ne ht
    · intro h
      exact zero_ne_one (congrArg height h)
  have unreduced_boundary (X : BasedSpace.{u})
      [CWComplex (Set.univ : Set X)] (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n) :
      let R (p q : X × I) : Prop := (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
      let T (s : ℝ) : I := Set.projIcc 0 1 zero_le_one ((s+1)/2)
      let f (z : Fin (n+1) → ℝ) : Quot R :=
        Quot.mk R (RelCWComplex.map n i (fun j => z j.succ),T (z 0))
      ∃ J : ∀ m, Finset (RelCWComplex.cell (Set.univ : Set X) m),
        MapsTo f (Metric.sphere 0 1)
          ({Quot.mk R (X.point,0),Quot.mk R (X.point,1)} ∪
            ⋃ (m < n) (j ∈ J m),
              Quot.mk R '' ((RelCWComplex.map m j '' Metric.closedBall 0 1) ×ˢ Set.univ)) := by
    classical
    dsimp only
    let R (p q : X × I) : Prop := (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
    let T (s : ℝ) : I := Set.projIcc 0 1 zero_le_one ((s+1)/2)
    let f (z : Fin (n+1) → ℝ) : Quot R :=
      Quot.mk R (RelCWComplex.map n i (fun j => z j.succ),T (z 0))
    change ∃ J : ∀ m, Finset (RelCWComplex.cell (Set.univ : Set X) m),
      MapsTo f (Metric.sphere 0 1)
        ({Quot.mk R (X.point,0),Quot.mk R (X.point,1)} ∪
          ⋃ (m < n) (j ∈ J m),
            Quot.mk R '' ((RelCWComplex.map m j '' Metric.closedBall 0 1) ×ˢ Set.univ))
    have hc (k : ℕ) (v : Fin k → ℝ) :
        v ∈ Metric.closedBall 0 1 ↔ ∀ j, -1 ≤ v j ∧ v j ≤ 1 := by
      rw [closedBall_pi _ (by norm_num : (0:ℝ) ≤ 1)]
      simp [Real.closedBall_eq_Icc,Pi.le_def,forall_and]
    have hb (k : ℕ) (v : Fin k → ℝ) :
        v ∈ Metric.ball 0 1 ↔ ∀ j, -1 < v j ∧ v j < 1 := by
      rw [ball_pi _ (by norm_num : (0:ℝ) < 1)]
      simp only [Set.mem_pi,Set.mem_univ,forall_const,Real.ball_eq_Ioo,Pi.zero_apply,
        zero_sub,zero_add,Set.mem_Ioo]
    have hT (s : ℝ) (h : -1 ≤ s ∧ s ≤ 1) : ((T s : I) : ℝ)=(s+1)/2 := by
      have hh : (s+1)/2 ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith
      exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hh)
    obtain ⟨J,hJ⟩ := CWComplex.mapsTo (C := (Set.univ : Set X)) n i
    refine ⟨J,?_⟩
    intro z hz
    by_cases ht0 : T (z 0)=0
    · left
      apply Set.mem_insert_iff.mpr
      left
      exact Quot.sound (Or.inl ⟨ht0,rfl⟩)
    by_cases ht1 : T (z 0)=1
    · left
      apply Set.mem_insert_iff.mpr
      right
      apply Set.mem_singleton_iff.mpr
      exact Quot.sound (Or.inr ⟨ht1,rfl⟩)
    have hzclosed : z ∈ Metric.closedBall 0 1 := Metric.sphere_subset_closedBall hz
    have hzhead : -1 < z 0 ∧ z 0 < 1 := by
      have hh := hT (z 0) ((hc _ _).mp hzclosed 0)
      have htpos : 0 < (T (z 0):ℝ) := lt_of_le_of_ne (T (z 0)).property.1
        (fun h => ht0 (Subtype.ext h.symm))
      have htlt : (T (z 0):ℝ) < 1 := lt_of_le_of_ne (T (z 0)).property.2
        (fun h => ht1 (Subtype.ext h))
      constructor <;> linarith
    have htail : (fun j : Fin n => z j.succ) ∈ Metric.sphere 0 1 := by
      rw [← Metric.closedBall_sdiff_ball]
      refine ⟨(hc _ _).mpr (fun j => (hc _ _).mp hzclosed j.succ),?_⟩
      intro ht
      have hzball : z ∈ Metric.ball 0 1 := by
        apply (hb _ _).mpr
        intro j
        induction j using Fin.cases with
        | zero => exact hzhead
        | succ j => exact (hb _ _).mp ht j
      exact Metric.sphere_disjoint_ball.le_bot ⟨hz,hzball⟩
    right
    have hh := hJ htail
    simp only [Set.mem_iUnion,exists_prop] at hh ⊢
    obtain ⟨m,hm,j,hj,hcell⟩ := hh
    exact ⟨m,hm,j,hj,_,⟨hcell,Set.mem_univ _⟩,rfl⟩
  have unreduced_interior_openEmbedding (X : BasedSpace.{u}) :
      let R (p q : X × I) : Prop :=
        (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
      let S : Set (X × I) := {p | p.2≠0 ∧ p.2≠1}
      IsOpenEmbedding (fun p : S => Quot.mk R p.1) := by
    classical
    dsimp only
    let R (p q : X × I) : Prop :=
      (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
    let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (X.point,0)⟩
    let q : X × I → U := Quot.mk R
    let S : Set (X × I) := {p | p.2≠0 ∧ p.2≠1}
    change IsOpenEmbedding (fun p : S => q p.1)
    have heq (p p' : X × I) : q p = q p' ↔ p = p' ∨ R p p' := by
      constructor
      · intro h
        have h' := Quot.eqvGen_exact h
        clear h
        induction h' with
        | rel a b hab => exact Or.inr hab
        | refl a => exact Or.inl rfl
        | symm a b hab ih =>
          rcases ih with h | (h | h)
          · exact Or.inl h.symm
          · exact Or.inr (Or.inl ⟨h.2,h.1⟩)
          · exact Or.inr (Or.inr ⟨h.2,h.1⟩)
        | trans a b c hab hbc ih₁ ih₂ =>
          rcases ih₁ with rfl | (h₁ | h₁)
          · exact ih₂
          · rcases ih₂ with rfl | (h₂ | h₂)
            · exact Or.inr (Or.inl h₁)
            · exact Or.inr (Or.inl ⟨h₁.1,h₂.2⟩)
            · exact False.elim (zero_ne_one (h₁.2.symm.trans h₂.1))
          · rcases ih₂ with rfl | (h₂ | h₂)
            · exact Or.inr (Or.inr h₁)
            · exact False.elim (zero_ne_one (h₂.1.symm.trans h₁.2))
            · exact Or.inr (Or.inr ⟨h₁.1,h₂.2⟩)
      · rintro (rfl | h)
        · rfl
        · exact Quot.sound h
    have hopen (S : Set (X × I)) (hS : IsOpen S)
        (hS₀ : ∀ p ∈ S, p.2 ≠ 0) (hS₁ : ∀ p ∈ S, p.2 ≠ 1) :
        IsOpen (q '' S) := by
      rw [← isQuotientMap_quot_mk.isOpen_preimage]
      convert hS using 1
      ext p
      constructor
      · rintro ⟨p',hp',hh⟩
        rcases (heq p' p).mp hh with rfl | (h | h)
        · exact hp'
        · exact False.elim (hS₀ p' hp' h.1)
        · exact False.elim (hS₁ p' hp' h.1)
      · intro hp
        exact ⟨p,hp,rfl⟩

    have hS : IsOpen S :=
      ((isClosed_singleton.isOpen_compl).inter (isClosed_singleton.isOpen_compl)).preimage continuous_snd
    apply IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact continuous_quot_mk.comp continuous_subtype_val
    · intro p p' h
      apply Subtype.ext
      rcases (heq p.1 p'.1).mp h with h | (h | h)
      · exact h
      · exact False.elim (p.2.1 h.1)
      · exact False.elim (p.2.2 h.1)
    · intro T hT
      have hV : IsOpen (Subtype.val '' T : Set (X × I)) :=
        hS.isOpenEmbedding_subtypeVal.isOpenMap T hT
      have h := hopen (Subtype.val '' T) hV
        (by rintro _ ⟨p,hp,rfl⟩; exact p.2.1)
        (by rintro _ ⟨p,hp,rfl⟩; exact p.2.2)
      simpa only [Set.image_image,Function.comp_def] using h
  have partialEquiv_isEmbedding_source {α : Type} {β : Type u}
      [TopologicalSpace α] [TopologicalSpace β] (e : PartialEquiv α β)
      (hf : ContinuousOn e e.source) (hg : ContinuousOn e.symm e.target) :
      IsEmbedding (fun x : e.source => e x.1) := by
    let E : e.source ≃ₜ e.target :=
      { toEquiv := e.toEquiv
        continuous_toFun := hf.restrict.subtype_mk _
        continuous_invFun := hg.restrict.subtype_mk _ }
    exact IsEmbedding.subtypeVal.comp E.isEmbedding
  have cw_cell_isEmbedding (X : Type u) [TopologicalSpace X]
      [CWComplex (Set.univ : Set X)] (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n) :
      IsEmbedding (fun x : Metric.ball (0 : Fin n → ℝ) 1 => RelCWComplex.map n i x.1) := by
    have h := partialEquiv_isEmbedding_source (RelCWComplex.map n i)
      ((RelCWComplex.continuousOn n i).mono (by rw [RelCWComplex.source_eq]; exact Metric.ball_subset_closedBall))
      (RelCWComplex.continuousOn_symm n i)
    exact h.comp (Homeomorph.setCongr (RelCWComplex.source_eq n i)).symm.isEmbedding
  have unreduced_characteristic_isEmbedding (X : BasedSpace.{u})
      [CWComplex (Set.univ : Set X)] (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n) :
      let R (p q : X × I) : Prop :=
        (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
      let T (s : ℝ) : I := Set.projIcc 0 1 zero_le_one ((s+1)/2)
      let f (z : Fin (n+1) → ℝ) : Quot R :=
        Quot.mk R (RelCWComplex.map n i (fun j => z j.succ),T (z 0))
      IsEmbedding (fun z : Metric.ball (0 : Fin (n+1) → ℝ) 1 => f z.1) := by
    classical
    dsimp only
    let R (p q : X × I) : Prop :=
      (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
    let T (s : ℝ) : I := Set.projIcc 0 1 zero_le_one ((s+1)/2)
    let f (z : Fin (n+1) → ℝ) : Quot R :=
      Quot.mk R (RelCWComplex.map n i (fun j => z j.succ),T (z 0))
    change IsEmbedding (fun z : Metric.ball (0 : Fin (n+1) → ℝ) 1 => f z.1)
    have hb (k : ℕ) (v : Fin k → ℝ) :
        v ∈ Metric.ball 0 1 ↔ ∀ j, -1 < v j ∧ v j < 1 := by
      rw [ball_pi _ (by norm_num : (0 : ℝ) < 1)]
      simp only [Set.mem_pi,Set.mem_univ,forall_const,Real.ball_eq_Ioo,Pi.zero_apply,
        zero_sub,zero_add,Set.mem_Ioo]
    have hT (s : ℝ) (h : -1 ≤ s ∧ s ≤ 1) : ((T s : I) : ℝ)=(s+1)/2 := by
      have hh : (s+1)/2 ∈ Set.Icc (0:ℝ) 1 := by constructor <;> linarith
      exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hh)
    have hTi (s : ℝ) (h : -1 < s ∧ s < 1) : T s ∈ Set.Ioo (0:I) 1 := by
      have ht := hT s ⟨h.1.le,h.2.le⟩
      change 0 < (T s : ℝ) ∧ (T s : ℝ) < 1
      rw [ht]
      constructor <;> linarith
    let b : (Metric.ball (0 : Fin (n+1) → ℝ) 1) →
        (Metric.ball (0 : Fin n → ℝ) 1) × I := fun z =>
      (⟨fun j => z.1 j.succ,(hb _ _).mpr (fun j => (hb _ _).mp z.2 j.succ)⟩,T (z.1 0))
    have hbcont : Continuous b :=
      ((continuous_pi fun j => (continuous_apply j.succ).comp continuous_subtype_val).subtype_mk _).prodMk
        (continuous_projIcc.comp ((((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2))
    let G : (Metric.ball (0 : Fin n → ℝ) 1) × I → (Fin (n+1) → ℝ) :=
      fun p => Fin.cons (2*(p.2:ℝ)-1) p.1.1
    have hG : Continuous G := by
      apply continuous_pi
      intro j
      induction j using Fin.cases with
      | zero => exact (continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const
      | succ j => exact (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)
    have hGb : G ∘ b=Subtype.val := by
      funext z j
      induction j using Fin.cases with
      | zero =>
        change 2*(T (z.1 0):ℝ)-1=z.1 0
        rw [hT _ ⟨((hb _ _).mp z.2 0).1.le,((hb _ _).mp z.2 0).2.le⟩]
        ring
      | succ j => rfl
    have hbemb : IsEmbedding b :=
      IsEmbedding.of_comp hbcont hG (hGb.symm ▸ IsEmbedding.subtypeVal)
    have hemb : IsEmbedding (fun z : Metric.ball (0 : Fin (n+1) → ℝ) 1 =>
        (RelCWComplex.map n i (fun j => z.1 j.succ),T (z.1 0))) :=
      ((cw_cell_isEmbedding X n i).prodMap IsEmbedding.id).comp hbemb
    let S : Set (X × I) := {p | p.2≠0 ∧ p.2≠1}
    have hi (z : Metric.ball (0 : Fin (n+1) → ℝ) 1) :
        (RelCWComplex.map n i (fun j => z.1 j.succ),T (z.1 0)) ∈ S :=
      ⟨(hTi _ ((hb _ _).mp z.2 0)).1.ne',(hTi _ ((hb _ _).mp z.2 0)).2.ne⟩
    exact (unreduced_interior_openEmbedding X).isEmbedding.comp (hemb.codRestrict S hi)
  have unreduced_cw_chart_family (X : BasedSpace.{u})
      [CWComplex (Set.univ : Set X)]
      (hE : ∀ n (i : RelCWComplex.cell (Set.univ : Set X) n),
        let R (p q : X × I) : Prop := (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
        let T (s : ℝ) : I := Set.projIcc 0 1 zero_le_one ((s+1)/2)
        IsEmbedding (fun z : Metric.ball (0 : Fin (n+1) → ℝ) 1 =>
          Quot.mk R (RelCWComplex.map n i (fun j => z.1 j.succ),T (z.1 0)))) :
      let R (p q : X × I) : Prop := (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
      let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (X.point,0)⟩
      let cells : ℕ → Type u
        | 0 => ULift.{u} Bool
        | n+1 => RelCWComplex.cell (Set.univ : Set X) n
      ∃ c : ∀ n, cells n → PartialEquiv (Fin n → ℝ) U,
        (∀ n i, (c n i).source = Metric.ball 0 1) ∧
        (∀ n i, ContinuousOn (c n i) (Metric.closedBall 0 1)) ∧
        (∀ n i, ContinuousOn (c n i).symm (c n i).target) ∧
        (∀ b, c 0 b =
          { toFun := fun _ => Quot.mk R (X.point,if b.down then 1 else 0)
            invFun := fun _ => 0
            source := Metric.ball 0 1
            target := {Quot.mk R (X.point,if b.down then 1 else 0)}
            map_source' := by intro _ _; rfl
            map_target' := by intro _ _; simp
            left_inv' := by intro _ _; exact Subsingleton.elim _ _
            right_inv' := by intro _ h; exact h.symm }) ∧
        (∀ n i z, c (n+1) i z =
          Quot.mk R (RelCWComplex.map n i (fun j => z j.succ),
            Set.projIcc 0 1 zero_le_one ((z 0+1)/2))) := by
    classical
    dsimp only
    let R (p q : X × I) : Prop := (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
    let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (X.point,0)⟩
    let cells : ℕ → Type u
      | 0 => ULift.{u} Bool
      | n+1 => RelCWComplex.cell (Set.univ : Set X) n
    let f (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n)
        (z : Fin (n+1) → ℝ) : U :=
      Quot.mk R (RelCWComplex.map n i (fun j => z j.succ),
        Set.projIcc 0 1 zero_le_one ((z 0+1)/2))
    have hchar := unreduced_characteristic X
    let c : ∀ n, cells n → PartialEquiv (Fin n → ℝ) U
      | 0,b =>
          { toFun := fun _ => Quot.mk R (X.point,if b.down then 1 else 0)
            invFun := fun _ => 0
            source := Metric.ball 0 1
            target := {Quot.mk R (X.point,if b.down then 1 else 0)}
            map_source' := by intro _ _; rfl
            map_target' := by intro _ _; simp
            left_inv' := by intro _ _; exact Subsingleton.elim _ _
            right_inv' := by intro _ h; exact h.symm }
      | n+1,i => (hchar n i).2.2.2.toPartialEquiv (f n i) (Metric.ball 0 1)
    refine ⟨c,?_,?_,?_,?_,?_⟩
    · intro n i
      cases n <;> rfl
    · intro n i
      cases n with
      | zero => exact continuousOn_const
      | succ n => exact (hchar n i).1
    · intro n i
      cases n with
      | zero => exact continuousOn_const
      | succ n =>
        let e := c (n+1) i
        have hi : IsEmbedding (fun x : e.source => e x.1) := hE n i
        let inv : e.target → e.source := fun y => ⟨e.symm y.1,e.map_target y.2⟩
        have hv : Continuous inv := hi.continuous_iff.mpr (by
          convert (continuous_subtype_val : Continuous (fun y : e.target => y.1)) using 1
          ext y
          exact e.right_inv y.2)
        exact continuousOn_iff_continuous_restrict.mpr (continuous_subtype_val.comp hv)
    · intro b; rfl
    · intro n i z; rfl
  have unreduced_cw_of_embedding (X : BasedSpace.{u}) [T2Space X]
      [CWComplex (Set.univ : Set X)]
      (hE : ∀ n (i : RelCWComplex.cell (Set.univ : Set X) n),
        let R (p q : X × I) : Prop := (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
        let T (s : ℝ) : I := Set.projIcc 0 1 zero_le_one ((s+1)/2)
        IsEmbedding (fun z : Metric.ball (0 : Fin (n+1) → ℝ) 1 =>
          Quot.mk R (RelCWComplex.map n i (fun j => z.1 j.succ),T (z.1 0)))) :
      let R (p q : X × I) : Prop := (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
      let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (X.point,0)⟩
      T2Space U ∧ Nonempty (CWComplex (Set.univ : Set U)) := by
    classical
    dsimp only
    let R (p q : X × I) : Prop := (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
    let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (X.point,0)⟩
    let q : X × I → U := Quot.mk R
    let cells : ℕ → Type u
      | 0 => ULift.{u} Bool
      | n+1 => RelCWComplex.cell (Set.univ : Set X) n
    let v (b : ULift.{u} Bool) : U := q (X.point,if b.down then 1 else 0)
    let D (a : Σ n : ℕ, RelCWComplex.cell (Set.univ : Set X) n) : Set U :=
      q '' ((RelCWComplex.map a.1 a.2 '' Metric.ball 0 1) ×ˢ Set.Ioo 0 1)
    change T2Space U ∧ Nonempty (CWComplex (Set.univ : Set U))
    letI : T2Space U := unreduced_t2 X
    obtain ⟨c,hsource,hcontinuous,hinverse,hzero,hsucc⟩ := unreduced_cw_chart_family X hE
    change (∀ n (i : cells n), (c n i).source=Metric.ball 0 1) at hsource
    have hzo (b : ULift.{u} Bool) : c 0 b '' Metric.ball 0 1 = {v b} := by
      rw [hzero]
      change (fun _ : Fin 0 → ℝ => v b) '' Metric.ball 0 1 = {v b}
      exact (Metric.nonempty_ball.mpr zero_lt_one).image_const (v b)
    have hzc (b : ULift.{u} Bool) : c 0 b '' Metric.closedBall 0 1 = {v b} := by
      rw [hzero]
      change (fun _ : Fin 0 → ℝ => v b) '' Metric.closedBall 0 1 = {v b}
      exact (Metric.nonempty_closedBall.mpr zero_le_one).image_const (v b)
    have hso (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n) :
        c (n+1) i '' Metric.ball 0 1 = D ⟨n,i⟩ := by
      have hh : (c (n+1) i : (Fin (n+1) → ℝ) → U) =
          (fun z => q (RelCWComplex.map n i (fun j => z j.succ),
            Set.projIcc 0 1 zero_le_one ((z 0+1)/2))) := funext (hsucc n i)
      rw [hh]
      exact (unreduced_characteristic X n i).2.2.1
    have hsc (n : ℕ) (i : RelCWComplex.cell (Set.univ : Set X) n) :
        c (n+1) i '' Metric.closedBall 0 1 =
          q '' ((RelCWComplex.map n i '' Metric.closedBall 0 1) ×ˢ Set.univ) := by
      have hh : (c (n+1) i : (Fin (n+1) → ℝ) → U) =
          (fun z => q (RelCWComplex.map n i (fun j => z j.succ),
            Set.projIcc 0 1 zero_le_one ((z 0+1)/2))) := funext (hsucc n i)
      rw [hh]
      exact (unreduced_characteristic X n i).2.1
    have hpartition : Pairwise (fun a b => Disjoint (D a) (D b)) ∧
        (∀ a, Disjoint (D a) {q (X.point,0),q (X.point,1)}) ∧
        q (X.point,0) ≠ q (X.point,1) := unreduced_cell_partition X
    have hv : Function.Injective v := by
      rintro ⟨a⟩ ⟨b⟩ h
      cases a <;> cases b
      · rfl
      · exact False.elim (hpartition.2.2 h)
      · exact False.elim (hpartition.2.2 h.symm)
      · rfl
    have hv_mem (b : ULift.{u} Bool) :
        v b ∈ ({q (X.point,0),q (X.point,1)} : Set U) := by
      rcases b with ⟨b⟩
      cases b <;> simp [v]
    refine ⟨inferInstance,⟨{
      cell := cells
      map := c
      source_eq := hsource
      continuousOn := hcontinuous
      continuousOn_symm := hinverse
      pairwiseDisjoint' := ?_
      mapsTo' := ?_
      closed' := ?_
      union' := ?_ }⟩⟩
    · rintro ⟨n,i⟩ _ ⟨m,j⟩ _ hij
      change Disjoint (c n i '' Metric.ball 0 1) (c m j '' Metric.ball 0 1)
      cases n with
      | zero =>
        cases m with
        | zero =>
          rw [hzo,hzo]
          apply Set.disjoint_singleton.mpr
          intro h
          exact hij (congrArg (fun b => (⟨0,b⟩ : Σ k, cells k)) (hv h))
        | succ m =>
          rw [hzo,hso]
          exact ((hpartition.2.1 ⟨m,j⟩).mono_right (Set.singleton_subset_iff.mpr (hv_mem i))).symm
      | succ n =>
        cases m with
        | zero =>
          rw [hso,hzo]
          exact (hpartition.2.1 ⟨n,i⟩).mono_right (Set.singleton_subset_iff.mpr (hv_mem j))
        | succ m =>
          rw [hso,hso]
          apply hpartition.1
          intro h
          apply hij
          exact congrArg (fun a : Σ k, RelCWComplex.cell (Set.univ : Set X) k =>
            (⟨a.1+1,a.2⟩ : Σ k, cells k)) h
    · intro k i
      cases k with
      | zero =>
        refine ⟨fun _ => ∅,?_⟩
        rw [Metric.sphere_eq_empty_of_subsingleton (by norm_num : (1:ℝ) ≠ 0)]
        exact Set.mapsTo_empty _ _
      | succ n =>
        obtain ⟨J,hJ⟩ := unreduced_boundary X n i
        let L : ∀ k, Finset (cells k)
          | 0 => Finset.univ
          | m+1 => J m
        refine ⟨L,?_⟩
        intro z hz
        have hh := hJ hz
        rw [hsucc]
        rcases hh with hv | hc
        · rcases Set.mem_insert_iff.mp hv with h0 | h1
          · refine Set.mem_iUnion.mpr ⟨0,Set.mem_iUnion.mpr ⟨Nat.zero_lt_succ n,
              Set.mem_iUnion.mpr ⟨(⟨false⟩ : ULift.{u} Bool),Set.mem_iUnion.mpr ⟨by simp [L],?_⟩⟩⟩⟩
            rw [hzc]
            exact h0
          · refine Set.mem_iUnion.mpr ⟨0,Set.mem_iUnion.mpr ⟨Nat.zero_lt_succ n,
              Set.mem_iUnion.mpr ⟨(⟨true⟩ : ULift.{u} Bool),Set.mem_iUnion.mpr ⟨by simp [L],?_⟩⟩⟩⟩
            rw [hzc]
            exact h1
        · obtain ⟨m,hm,j,hj,hx⟩ := by
            simpa only [Set.mem_iUnion,exists_prop] using hc
          refine Set.mem_iUnion.mpr ⟨m+1,Set.mem_iUnion.mpr ⟨Nat.succ_lt_succ hm,
            Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,?_⟩⟩⟩⟩
          rw [hsc]
          exact hx
    · intro A _ hA
      apply isQuotientMap_quot_mk.isClosed_preimage.mp
      apply cw_cylinder_closed X
      intro n i
      let g : Metric.closedBall (0 : Fin n → ℝ) 1 × I → U :=
        fun p => q (RelCWComplex.map n i p.1,p.2)
      have hg : Continuous g := continuous_quot_mk.comp
        (((RelCWComplex.continuousOn n i).restrict.comp continuous_fst).prodMk continuous_snd)
      have hmem (p : Metric.closedBall (0 : Fin n → ℝ) 1 × I) :
          g p ∈ c (n+1) i '' Metric.closedBall 0 1 := by
        rw [hsc]
        exact ⟨_,⟨⟨p.1,p.1.2,rfl⟩,trivial⟩,rfl⟩
      have hh := (hA (n+1) i).preimage hg
      convert hh using 1
      ext p
      exact ⟨fun h => ⟨h,hmem p⟩,fun h => h.1⟩
    · apply Set.eq_univ_of_forall
      intro z
      obtain ⟨⟨x,t⟩,rfl⟩ := Quot.exists_rep z
      have hx : x ∈ ⋃ n : ℕ, ⋃ i : RelCWComplex.cell (Set.univ : Set X) n,
          RelCWComplex.closedCell n i := by rw [CWComplex.union]; trivial
      obtain ⟨n,i,hx⟩ := by simpa only [Set.mem_iUnion] using hx
      apply Set.mem_iUnion.mpr
      refine ⟨n+1,Set.mem_iUnion.mpr ⟨i,?_⟩⟩
      rw [hsc]
      exact ⟨(x,t),⟨hx,trivial⟩,rfl⟩
  exact unreduced_cw_of_embedding X (unreduced_characteristic_isEmbedding X)

open Set in
/-- Transport the actual CW model through based homotopies. The original
basepoint need not be a zero-dimensional cell. -/
private theorem suspension_hasCWType (A : BasedSpace.{u}) (hA : A.HasCWType) :
    A.suspension.HasCWType := by
  have suspension_homotopicRel {A B : BasedSpace.{u}}
      (f g : A ⟶ B) (h : f.map.HomotopicRel g.map {A.point}) :
      (suspendMap f).map.HomotopicRel (suspendMap g).map {A.suspension.point} := by
    obtain ⟨H⟩ := h
    let K : C(A × I,B) := ⟨fun p => H (p.2,p.1),H.continuous.comp continuous_swap⟩
    have hK : ∀ t, K (A.point,t) = B.point := by
      intro t
      exact (H.eq_fst t (Set.mem_singleton _)).trans f.point
    refine ⟨{ toFun := fun p => suspensionFamily A B K hK (p.2,p.1)
              continuous_toFun := (continuous_suspensionFamily A B K hK).comp continuous_swap
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro z
      refine Quot.inductionOn z ?_
      intro p
      change suspensionProjection B (H (0,p.1),p.2) = suspensionProjection B (f.map p.1,p.2)
      rw [H.apply_zero]
    · intro z
      refine Quot.inductionOn z ?_
      intro p
      change suspensionProjection B (H (1,p.1),p.2) = suspensionProjection B (g.map p.1,p.2)
      rw [H.apply_one]
    · intro t z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      change suspensionProjection B (K (A.point,t),0) =
        suspensionProjection B (f.map A.point,0)
      rw [hK t,f.point]
  have suspension_preserves_based_equivalence {A B : BasedSpace.{u}}
      (f : A ⟶ B) (g : B ⟶ A)
      (hA : (g.map.comp f.map).HomotopicRel (ContinuousMap.id A) {A.point})
      (hB : (f.map.comp g.map).HomotopicRel (ContinuousMap.id B) {B.point}) :
      ((suspendMap g).map.comp (suspendMap f).map).HomotopicRel
        (ContinuousMap.id A.suspension) {A.suspension.point} ∧
      ((suspendMap f).map.comp (suspendMap g).map).HomotopicRel
        (ContinuousMap.id B.suspension) {B.suspension.point} := by
    have hcomp {P Q R : BasedSpace.{u}} (a : P ⟶ Q) (b : Q ⟶ R) :
        (suspendMap (a ≫ b)).map = (suspendMap b).map.comp (suspendMap a).map := by
      ext z
      refine Quot.inductionOn z ?_
      intro p
      rfl
    have hid (P : BasedSpace.{u}) : (suspendMap (𝟙 P)).map = ContinuousMap.id P.suspension := by
      ext z
      refine Quot.inductionOn z ?_
      intro p
      rfl
    constructor
    · simpa only [hcomp,hid] using suspension_homotopicRel (f ≫ g) (𝟙 A) hA
    · simpa only [hcomp,hid] using suspension_homotopicRel (g ≫ f) (𝟙 B) hB
  have hasCWType_of_based_equivalence {A B : BasedSpace.{u}}
      (f : A ⟶ B) (g : B ⟶ A)
      (hA : (g.map.comp f.map).HomotopicRel (ContinuousMap.id A) {A.point})
      (hB : (f.map.comp g.map).HomotopicRel (ContinuousMap.id B) {B.point})
      (hCW : B.HasCWType) : A.HasCWType := by
    have precomp {P Q R : BasedSpace.{u}} (a b : Q ⟶ R)
        (h : a.map.HomotopicRel b.map {Q.point}) (c : P ⟶ Q) :
        (a.map.comp c.map).HomotopicRel (b.map.comp c.map) {P.point} := by
      obtain ⟨H⟩ := h
      refine ⟨{ toHomotopy := H.toHomotopy.compContinuousMap c.map, prop' := ?_ }⟩
      intro t p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      change H (t,c.map P.point) = a.map (c.map P.point)
      rw [c.point]
      exact H.eq_fst t (Set.mem_singleton _)
    obtain ⟨Z,hT,hC,hZ,p,q,h₁,h₂⟩ := hCW
    refine ⟨Z,hT,hC,hZ,f ≫ p,q ≫ g,?_,?_⟩
    · have h := (precomp (p ≫ q) (𝟙 B) h₁ f).comp_continuousMap g.map
      have hh : ((q ≫ g).map.comp (f ≫ p).map).HomotopicRel
          (g.map.comp f.map) {A.point} := by
        convert h using 1 <;> ext z <;> rfl
      exact hh.trans hA
    · have h := (precomp (g ≫ f) (𝟙 B) hB q).comp_continuousMap p.map
      have hh : ((f ≫ p).map.comp (q ≫ g).map).HomotopicRel
          (p.map.comp q.map) {Z.point} := by
        convert h using 1 <;> ext z <;> rfl
      exact hh.trans h₂
  have suspension_arc_equivalence (X : BasedSpace.{u}) (hX : X.IsWellBased) :
      let R : (X × I) → (X × I) → Prop := fun p q =>
        (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
      let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (X.point,0)⟩
      ∃ (f : X.suspension ⟶ U) (g : U ⟶ X.suspension),
        (g.map.comp f.map).HomotopicRel (ContinuousMap.id X.suspension) {X.suspension.point} ∧
        (f.map.comp g.map).HomotopicRel (ContinuousMap.id U) {U.point} ∧
        ∀ x t, g.map (Quot.mk R (x,t))=suspensionProjection X (x,t) := by
    classical
    let R : (X × I) → (X × I) → Prop := fun p q =>
      (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
    let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (X.point,0)⟩
    change ∃ (f : X.suspension ⟶ U) (g : U ⟶ X.suspension), _
    let π : C(X × I,U) := ⟨Quot.mk R,continuous_quot_mk⟩
    let γ : C(I,U) := π.comp ⟨fun t => (X.point,t),continuous_const.prodMk continuous_id⟩
    have hπ0 (x : X) : π (x,0)=U.point := Quot.sound (Or.inl ⟨rfl,rfl⟩)
    have hπ1 (x : X) : π (x,1)=γ 1 := Quot.sound (Or.inr ⟨rfl,rfl⟩)
    have hg : ∀ p q, R p q → suspensionProjection X p=suspensionProjection X q := by
      intro p q hpq
      rcases hpq with ⟨hp,hq⟩ | ⟨hp,hq⟩
      · exact (suspensionProjection_collapsed X p (Or.inr (Or.inl hp))).trans
          (suspensionProjection_collapsed X q (Or.inr (Or.inl hq))).symm
      · exact (suspensionProjection_collapsed X p (Or.inr (Or.inr hp))).trans
          (suspensionProjection_collapsed X q (Or.inr (Or.inr hq))).symm
    let g : U ⟶ X.suspension :=
      ⟨⟨Quot.lift (suspensionProjection X) hg,
        continuous_quot_lift hg (suspensionProjection X).continuous⟩,rfl⟩
    have hgγ (s : I) : g.map (γ s)=X.suspension.point :=
      suspensionProjection_collapsed X (X.point,s) (Or.inl rfl)
    let a (p : I × I) : ℝ := (1+(p.2:ℝ))*(p.1:ℝ)
    have ha (p : I × I) : 0 ≤ a p ∧ a p ≤ 2 := by
      dsimp [a]
      constructor <;> nlinarith [p.1.property.1,p.1.property.2,p.2.property.1,p.2.property.2]
    let l (p : I × I) : I := ⟨min (a p) 1,(le_min (ha p).1 (by norm_num)),min_le_right _ _⟩
    let r (p : I × I) : I := ⟨min (2-a p) 1,le_min (by linarith [(ha p).2]) (by norm_num),min_le_right _ _⟩
    have hac : Continuous a :=
      (continuous_const.add (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_subtype_val.comp continuous_fst)
    have hlc : Continuous l := (hac.min continuous_const).subtype_mk _
    have hrc : Continuous r := ((continuous_const.sub hac).min continuous_const).subtype_mk _
    let rawA (p : (X × I) × I) : U :=
      if a (p.1.2,p.2) ≤ 1 then π (p.1.1,l (p.1.2,p.2)) else γ (r (p.1.2,p.2))
    have hrawA : Continuous rawA := by
      apply continuous_if_le (hac.comp (continuous_fst.snd.prodMk continuous_snd)) continuous_const
        (π.continuous.comp (continuous_fst.fst.prodMk
          (hlc.comp (continuous_fst.snd.prodMk continuous_snd)))).continuousOn
        (γ.continuous.comp (hrc.comp (continuous_fst.snd.prodMk continuous_snd))).continuousOn
      intro p hp
      change a (p.1.2,p.2)=1 at hp
      have hl : l (p.1.2,p.2)=1 := by apply Subtype.ext; simp [l,hp]
      have hr : r (p.1.2,p.2)=1 := by apply Subtype.ext; norm_num [r,hp]
      change π (_,l _)=γ (r _)
      rw [hl,hr,hπ1]
    have rawA_zero (x : X) (s : I) : rawA ((x,s),0)=π (x,s) := by
      have he : a (s,0)=(s:ℝ) := by simp [a]
      have hl : l (s,0)=s := by apply Subtype.ext; simp [l,he,min_eq_left s.property.2]
      simp [rawA,he,s.property.2,hl]
    have rawA_bottom (x : X) (t : I) : rawA ((x,0),t)=U.point := by
      have he : a (0,t)=0 := by simp [a]
      have hl : l (0,t)=0 := by apply Subtype.ext; simp [l,he]
      simp [rawA,he,hl,hπ0]
    have rawA_top (x : X) (t : I) : rawA ((x,1),t)=γ (σ t) := by
      have he : a (1,t)=1+(t:ℝ) := by simp [a]
      by_cases ht : t=0
      · subst t
        rw [rawA_zero,hπ1]
        simp
      · have htp : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun h => ht (Subtype.ext h.symm))
        have hr : r (1,t)=σ t := by
          apply Subtype.ext
          change min (2-a (1,t)) 1=1-(t:ℝ)
          rw [he,min_eq_left (by linarith [t.property.1])]
          ring
        simp only [rawA,he,if_neg (by linarith : ¬ 1+(t:ℝ) ≤ 1),hr]
    have hArel (t : I) : ∀ p q, R p q → rawA (p,t)=rawA (q,t) := by
      rintro ⟨x,s⟩ ⟨y,v⟩ (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · rw [rawA_bottom,rawA_bottom]
      · rw [rawA_top,rawA_top]
    let A : C(U × I,U) := ⟨fun p => Quot.lift (fun q => rawA (q,p.2)) (hArel p.2) p.1,by
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact hrawA⟩
    have hA0 (z : U) : A (z,0)=z := by
      refine Quot.inductionOn z ?_
      rintro ⟨x,s⟩
      exact rawA_zero x s
    have hAp (t : I) : A (U.point,t)=U.point := rawA_bottom X.point t
    have hgAγ (s t : I) : g.map (A (γ s,t))=X.suspension.point := by
      change g.map (rawA ((X.point,s),t))=_
      dsimp only [rawA]
      split
      · exact hgγ _
      · exact hgγ _
    let tent (s : I) : I := ⟨min (2*(s:ℝ)) (2-2*(s:ℝ)),by
      constructor
      · apply le_min <;> linarith [s.property.1,s.property.2]
      · by_cases h : (s:ℝ) ≤ 1/2
        · exact (min_le_left _ _).trans (by linarith)
        · exact (min_le_right _ _).trans (by linarith)⟩
    have htent : Continuous tent :=
      ((continuous_const.mul continuous_subtype_val).min
        (continuous_const.sub (continuous_const.mul continuous_subtype_val))).subtype_mk _
    have tent0 : tent 0=0 := by apply Subtype.ext; norm_num [tent]
    have tent1 : tent 1=0 := by apply Subtype.ext; norm_num [tent]
    have hA1γ (s : I) : A (γ s,1)=γ (tent s) := by
      change rawA ((X.point,s),1)=_
      have he : a (s,1)=2*(s:ℝ) := by norm_num [a]
      by_cases hs : 2*(s:ℝ) ≤ 1
      · have hl : l (s,1)=tent s := by
          apply Subtype.ext
          dsimp [l,tent]
          rw [he,min_eq_left hs,min_eq_left (by linarith)]
        simp only [rawA,he,if_pos hs,hl]
        rfl
      · have hr : r (s,1)=tent s := by
          apply Subtype.ext
          dsimp [r,tent]
          rw [he,min_eq_left (by linarith : 2-2*(s:ℝ) ≤ 1),min_eq_right (by linarith)]
        simp only [rawA,he,if_neg hs,hr]
    let L := {k : C(I,U) // k 0=U.point ∧ k 1=U.point}
    let Fc : C(X,C(I,U)) := ContinuousMap.curry
      ⟨fun p : X × I => A (π p,1),A.continuous.comp (π.continuous.prodMk continuous_const)⟩
    have hFc0 (x : X) : Fc x 0=U.point := rawA_bottom x 1
    have hFc1 (x : X) : Fc x 1=U.point := by
      change rawA ((x,1),1)=_
      rw [rawA_top]
      simp only [unitInterval.symm_one]
      rfl
    let F : C(X,L) := ⟨fun x => ⟨Fc x,hFc0 x,hFc1 x⟩,Fc.continuous.subtype_mk _⟩
    let shrink (p : I × I) : I := ⟨(1-(p.1:ℝ))*(tent p.2:ℝ),by
      constructor
      · exact mul_nonneg (by linarith [p.1.property.2]) (tent p.2).property.1
      · nlinarith [p.1.property.1,p.1.property.2,(tent p.2).property.1,(tent p.2).property.2]⟩
    have hshrink : Continuous shrink :=
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp (htent.comp continuous_snd))).subtype_mk _
    have shrink_bottom (t : I) : shrink (t,0)=0 := by apply Subtype.ext; simp [shrink,tent0]
    have shrink_top (t : I) : shrink (t,1)=0 := by apply Subtype.ext; simp [shrink,tent1]
    have shrink_zero (s : I) : shrink (0,s)=tent s := by apply Subtype.ext; simp [shrink]
    have shrink_one (s : I) : shrink (1,s)=0 := by apply Subtype.ext; simp [shrink]
    let Pc : C(I,C(I,U)) := ContinuousMap.curry ⟨fun p => γ (shrink p),γ.continuous.comp hshrink⟩
    have hPc (t : I) : Pc t 0=U.point ∧ Pc t 1=U.point := by
      constructor
      · change γ (shrink (t,0))=U.point
        rw [shrink_bottom]
        rfl
      · change γ (shrink (t,1))=U.point
        rw [shrink_top]
        rfl
    let P : C(I,L) := ⟨fun t => ⟨Pc t,hPc t⟩,Pc.continuous.subtype_mk hPc⟩
    have hPF : P 0=F X.point := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro s
      change γ (shrink (0,s))=A (γ s,1)
      rw [shrink_zero,hA1γ]
    obtain ⟨K,hK0,hKp⟩ := hX.2 (TopCat.of L) F P hPF
    let rawB (p : (X × I) × I) : U := (K (p.1.1,p.2)).1 p.1.2
    have hrawB : Continuous rawB := continuous_eval.comp
      ((continuous_subtype_val.comp (K.continuous.comp
        (continuous_fst.fst.prodMk continuous_snd))).prodMk continuous_fst.snd)
    have rawB_bottom (x : X) (t : I) : rawB ((x,0),t)=U.point := (K (x,t)).2.1
    have rawB_top (x : X) (t : I) : rawB ((x,1),t)=U.point := (K (x,t)).2.2
    have rawB_zero (x : X) (s : I) : rawB ((x,s),0)=A (π (x,s),1) := by
      change (K (x,0)).1 s=_
      rw [hK0]
      rfl
    have rawB_point (s t : I) : rawB ((X.point,s),t)=γ (shrink (t,s)) := by
      change (K (X.point,t)).1 s=_
      rw [hKp]
      rfl
    have hBrel (t : I) : ∀ p q, R p q → rawB (p,t)=rawB (q,t) := by
      rintro ⟨x,s⟩ ⟨y,v⟩ (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · rw [rawB_bottom,rawB_bottom]
      · rw [rawB_top,rawB_top]
    let B : C(U × I,U) := ⟨fun p => Quot.lift (fun q => rawB (q,p.2)) (hBrel p.2) p.1,by
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact hrawB⟩
    have hB0 (z : U) : B (z,0)=A (z,1) := by
      refine Quot.inductionOn z ?_
      rintro ⟨x,s⟩
      exact rawB_zero x s
    have hBp (t : I) : B (U.point,t)=U.point := rawB_bottom X.point t
    have hgBγ (s t : I) : g.map (B (γ s,t))=X.suspension.point := by
      change g.map (rawB ((X.point,s),t))=_
      rw [rawB_point]
      exact hgγ _
    have fcollapsed (p : X × I) (hp : SuspensionCollapsed X p) : rawB (p,1)=U.point := by
      rcases hp with hp | hp | hp
      · rcases p with ⟨x,s⟩
        change x=X.point at hp
        subst x
        rw [rawB_point,shrink_one]
        rfl
      · rcases p with ⟨x,s⟩
        change s=0 at hp
        subst s
        exact rawB_bottom x 1
      · rcases p with ⟨x,s⟩
        change s=1 at hp
        subst s
        exact rawB_top x 1
    have frel : ∀ p q, SuspensionRelation X p q → rawB (p,1)=rawB (q,1) :=
      fun p q h => (fcollapsed p h.1).trans (fcollapsed q h.2).symm
    let f : X.suspension ⟶ U :=
      ⟨⟨Quot.lift (fun p => rawB (p,1)) frel,
        continuous_quot_lift frel (hrawB.comp (continuous_id.prodMk continuous_const))⟩,
        rawB_bottom X.point 1⟩
    have hB1 (z : U) : B (z,1)=f.map (g.map z) := by
      refine Quot.inductionOn z ?_
      intro p
      rfl
    let A1 : C(U,U) := A.comp ⟨fun z => (z,1),continuous_id.prodMk continuous_const⟩
    have hAU : (ContinuousMap.id U).HomotopicRel A1 {U.point} := by
      refine ⟨{ toFun := fun p => A (p.2,p.1)
                continuous_toFun := A.continuous.comp continuous_swap
                map_zero_left := hA0
                map_one_left := fun _ => rfl
                prop' := ?_ }⟩
      intro t z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact hAp t
    have hBU : A1.HomotopicRel (f.map.comp g.map) {U.point} := by
      refine ⟨{ toFun := fun p => B (p.2,p.1)
                continuous_toFun := B.continuous.comp continuous_swap
                map_zero_left := hB0
                map_one_left := hB1
                prop' := ?_ }⟩
      intro t z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact (hBp t).trans (hAp 1).symm
    have projected_family (D : C(U × I,U))
        (hp : ∀ t, D (U.point,t)=U.point)
        (hγ : ∀ s t, g.map (D (γ s,t))=X.suspension.point) :
        ∃ E : C(X.suspension × I,X.suspension),
          (∀ x s t, E (suspensionProjection X (x,s),t)=g.map (D (π (x,s),t))) ∧
          ∀ t, E (X.suspension.point,t)=X.suspension.point := by
      let raw (p : (X × I) × I) := g.map (D (π p.1,p.2))
      have hc : Continuous raw := g.map.continuous.comp
        (D.continuous.comp ((π.continuous.comp continuous_fst).prodMk continuous_snd))
      have collapsed (p : X × I) (t : I) (h : SuspensionCollapsed X p) :
          raw (p,t)=X.suspension.point := by
        rcases p with ⟨x,s⟩
        change x=X.point ∨ s=0 ∨ s=1 at h
        rcases h with rfl | rfl | rfl
        · exact hγ s t
        · change g.map (D (π (x,0),t))=_
          rw [hπ0,hp,g.point]
        · change g.map (D (π (x,1),t))=_
          rw [hπ1]
          exact hγ 1 t
      have respects (t : I) : ∀ p q, SuspensionRelation X p q → raw (p,t)=raw (q,t) :=
        fun p q h => (collapsed p t h.1).trans (collapsed q t h.2).symm
      refine ⟨⟨fun p => Quot.lift (fun q => raw (q,p.2)) (respects p.2) p.1,by
        apply isQuotientMap_quot_mk.continuous_lift_prod_left
        exact hc⟩,fun _ _ _ => rfl,fun t => collapsed (X.point,0) t (Or.inl rfl)⟩
    obtain ⟨AS,hAS,hASp⟩ := projected_family A hAp hgAγ
    obtain ⟨BS,hBS,hBSp⟩ := projected_family B hBp hgBγ
    let AS1 : C(X.suspension,X.suspension) :=
      AS.comp ⟨fun z => (z,1),continuous_id.prodMk continuous_const⟩
    have hAShom : (ContinuousMap.id X.suspension).HomotopicRel AS1 {X.suspension.point} := by
      refine ⟨{ toFun := fun p => AS (p.2,p.1)
                continuous_toFun := AS.continuous.comp continuous_swap
                map_zero_left := ?_
                map_one_left := fun _ => rfl
                prop' := ?_ }⟩
      · intro z
        refine Quot.inductionOn z ?_
        rintro ⟨x,s⟩
        change AS (suspensionProjection X (x,s),0)=_
        rw [hAS,hA0]
        rfl
      · intro t z hz
        obtain rfl := Set.mem_singleton_iff.mp hz
        exact hASp t
    have hBShom : AS1.HomotopicRel (g.map.comp f.map) {X.suspension.point} := by
      refine ⟨{ toFun := fun p => BS (p.2,p.1)
                continuous_toFun := BS.continuous.comp continuous_swap
                map_zero_left := ?_
                map_one_left := ?_
                prop' := ?_ }⟩
      · intro z
        refine Quot.inductionOn z ?_
        rintro ⟨x,s⟩
        change BS (suspensionProjection X (x,s),0)=AS (suspensionProjection X (x,s),1)
        rw [hBS,hAS,hB0]
      · intro z
        refine Quot.inductionOn z ?_
        rintro ⟨x,s⟩
        change BS (suspensionProjection X (x,s),1)=_
        rw [hBS,hB1]
        rfl
      · intro t z hz
        obtain rfl := Set.mem_singleton_iff.mp hz
        exact (hBSp t).trans (hASp 1).symm
    exact ⟨f,g,(hAShom.trans hBShom).symm,(hAU.trans hBU).symm,fun _ _ => rfl⟩
  have unreducedSuspension_wellBased (X : BasedSpace.{u}) :
      let R : (X × I) → (X × I) → Prop :=
        fun p q => (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
      let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (X.point,0)⟩
      U.IsWellBased := by
    classical
    dsimp only
    let R : (X × I) → (X × I) → Prop :=
      fun p q => (p.2=0 ∧ q.2=0) ∨ (p.2=1 ∧ q.2=1)
    let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (X.point,0)⟩
    change U.IsWellBased
    let π : C(X × I,U) := ⟨Quot.mk R,continuous_quot_mk⟩
    have north (x : X) : π (x,0)=U.point := Quot.sound (Or.inl ⟨rfl,rfl⟩)
    have south (x y : X) : π (x,1)=π (y,1) := Quot.sound (Or.inr ⟨rfl,rfl⟩)
    let ht : C(U,I) := ⟨Quot.lift Prod.snd (by
      intro p q hpq
      rcases hpq with ⟨hp,hq⟩ | ⟨hp,hq⟩ <;> exact hp.trans hq.symm),
      continuous_quot_lift _ continuous_snd⟩
    have hn : {U.point} = ht ⁻¹' {0} := by
      ext z
      refine Quot.inductionOn z ?_
      intro p
      change π p=U.point ↔ p.2=0
      constructor
      · intro h
        exact congrArg ht h
      · intro h
        exact Quot.sound (Or.inl ⟨h,rfl⟩)
    refine ⟨hn ▸ isClosed_singleton.preimage ht.continuous,?_⟩
    intro Y f p hp
    let l (b : I × I) : I := ⟨max ((b.2:ℝ)-2*(b.1:ℝ)) 0,
      le_max_right _ _,max_le (by linarith [b.1.property.1,b.2.property.2]) (by norm_num)⟩
    let r (b : I × I) : I := ⟨max (2*(b.1:ℝ)-(b.2:ℝ)) 0/(2-(b.2:ℝ)),by
      have hd : 0 < 2-(b.2:ℝ) := by linarith [b.2.property.2]
      constructor
      · exact div_nonneg (le_max_right _ _) hd.le
      · apply (div_le_one hd).mpr
        exact max_le (by linarith [b.1.property.2]) (by linarith [b.2.property.2])⟩
    have hl : Continuous l :=
      (((continuous_subtype_val.comp continuous_snd).sub
        (continuous_const.mul (continuous_subtype_val.comp continuous_fst))).max continuous_const).subtype_mk _
    have hr : Continuous r :=
      ((((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
        (continuous_subtype_val.comp continuous_snd)).max continuous_const).div
          (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
            (fun b => by change 2-(b.2:ℝ)≠0; linarith [b.2.property.2])).subtype_mk _
    let raw (b : (X × I) × I) : Y :=
      if 2*(b.1.2:ℝ) ≤ (b.2:ℝ) then p (l (b.1.2,b.2))
      else f (π (b.1.1,r (b.1.2,b.2)))
    have hraw : Continuous raw := by
      apply continuous_if_le
        (continuous_const.mul (continuous_subtype_val.comp continuous_fst.snd))
        (continuous_subtype_val.comp continuous_snd)
        (p.continuous.comp (hl.comp (continuous_fst.snd.prodMk continuous_snd))).continuousOn
        (f.continuous.comp (π.continuous.comp (continuous_fst.fst.prodMk
          (hr.comp (continuous_fst.snd.prodMk continuous_snd))))).continuousOn
      intro b hb
      change 2*(b.1.2:ℝ)=(b.2:ℝ) at hb
      change p (l (b.1.2,b.2))=f (π (b.1.1,r (b.1.2,b.2)))
      have hl0 : l (b.1.2,b.2)=0 := by apply Subtype.ext; simp [l,← hb]
      have hr0 : r (b.1.2,b.2)=0 := by apply Subtype.ext; simp [r,← hb]
      rw [hl0,hr0,north,hp]
    have hbot (x : X) (t : I) : raw ((x,0),t)=p t := by
      have hl0 : l (0,t)=t := by
        apply Subtype.ext
        simp [l,max_eq_left t.property.1]
      dsimp only [raw]
      rw [if_pos (by simpa using t.property.1),hl0]
    have htop (x : X) (t : I) : raw ((x,1),t)=f (π (x,1)) := by
      have hn : ¬ 2*(1:ℝ) ≤ (t:ℝ) := by linarith [t.property.2]
      have hr1 : r (1,t)=1 := by
        apply Subtype.ext
        change max (2*1-(t:ℝ)) 0/(2-(t:ℝ))=1
        rw [max_eq_left (by linarith [t.property.2])]
        simp only [mul_one]
        exact div_self (by linarith [t.property.2])
      dsimp only [raw]
      simp only [show ((1:I):ℝ)=1 from rfl]
      rw [if_neg hn,hr1]
    have respects (t : I) : ∀ a b, R a b → raw (a,t)=raw (b,t) := by
      intro a b hab
      rcases hab with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · have ha' : a=(a.1,0) := Prod.ext rfl ha
        have hb' : b=(b.1,0) := Prod.ext rfl hb
        rw [ha',hb',hbot,hbot]
      · have ha' : a=(a.1,1) := Prod.ext rfl ha
        have hb' : b=(b.1,1) := Prod.ext rfl hb
        rw [ha',hb',htop,htop,south a.1 b.1]
    let F : C(U × I,Y) := ⟨fun b => Quot.lift (fun a => raw (a,b.2)) (respects b.2) b.1,by
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact hraw⟩
    refine ⟨F,?_,?_⟩
    · intro z
      refine Quot.inductionOn z ?_
      intro a
      change raw (a,0)=f (π a)
      dsimp only [raw]
      simp only [show ((0:I):ℝ)=0 from rfl]
      by_cases ha : 2*(a.2:ℝ) ≤ 0
      · have ha0 : a.2=0 := Subtype.ext (by change (a.2:ℝ)=0; linarith [a.2.property.1])
        rw [if_pos ha]
        have hl0 : l (a.2,0)=0 := by
          apply Subtype.ext
          simp [l,ha0]
        rw [hl0,hp]
        apply congrArg f
        have he : π a=U.point := Quot.sound (Or.inl ⟨ha0,rfl⟩)
        exact he.symm
      · rw [if_neg ha]
        have hr0 : r (a.2,0)=a.2 := by
          apply Subtype.ext
          dsimp [r]
          rw [max_eq_left (by linarith [a.2.property.1])]
          ring
        rw [hr0]
    · intro t
      exact hbot X.point t
  obtain ⟨Y,hT,⟨hC⟩,hY,p,q,h₁,h₂⟩ := hA
  letI := hT
  letI := hC
  let R (a b : Y × I) : Prop := (a.2=0 ∧ b.2=0) ∨ (a.2=1 ∧ b.2=1)
  let U : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (Y.point,0)⟩
  have hTU : T2Space U := (suspension_cw_model Y).1
  have hCU : Nonempty (CWComplex (Set.univ : Set U)) := (suspension_cw_model Y).2
  have hWU : U.IsWellBased := unreducedSuspension_wellBased Y
  obtain ⟨f,g,hf,hg,_⟩ := suspension_arc_equivalence Y hY
  have hYcw : Y.suspension.HasCWType := ⟨U,hTU,hCU,hWU,f,g,hf,hg⟩
  have h := suspension_preserves_based_equivalence p q h₁ h₂
  exact hasCWType_of_based_equivalence (suspendMap p) (suspendMap q) h.1 h.2 hYcw

open Set in
/-- The specified suspension basepoint inherits the homotopy extension property. -/
private theorem suspension_wellBased_of_wellBased (X : BasedSpace.{u}) (hX : X.IsWellBased) :
    X.suspension.IsWellBased := by
  classical
  have cylinder_retraction_of_wellBased (X : BasedSpace.{u}) (hX : X.IsWellBased) :
      ∃ r : C(X × I, X × I),
        (∀ x, r (x,0) = (x,0)) ∧
        (∀ t, r (X.point,t) = (X.point,t)) ∧
        (∀ q, (r q).2 = 0 ∨ (r q).1 = X.point) := by
    let S := {q : X × I // q.2 = 0 ∨ q.1 = X.point}
    let f : C(X,S) := ⟨fun x => ⟨(x,0),Or.inl rfl⟩,
      (continuous_id.prodMk continuous_const).subtype_mk _⟩
    let p : C(I,S) := ⟨fun t => ⟨(X.point,t),Or.inr rfl⟩,
      (continuous_const.prodMk continuous_id).subtype_mk _⟩
    obtain ⟨H,hH,hp⟩ := hX.2 (TopCat.of S) f p rfl
    refine ⟨⟨fun q => (H q).val,continuous_subtype_val.comp H.continuous⟩,?_,?_,?_⟩
    · intro x
      exact congrArg Subtype.val (hH x)
    · intro t
      exact congrArg Subtype.val (hp t)
    · intro q
      exact (H q).property

  have wellBased_of_cylinder_retraction (X : BasedSpace.{u})
      (hc : IsClosed ({X.point} : Set X)) (r : C(X × I, X × I))
      (hzero : ∀ x, r (x,0) = (x,0))
      (hpoint : ∀ t, r (X.point,t) = (X.point,t))
      (hr : ∀ q, (r q).2 = 0 ∨ (r q).1 = X.point) : X.IsWellBased := by
    classical
    refine ⟨hc, ?_⟩
    intro Y f p hp
    let U : Set (X × I) := {q | (r q).2 = 0}
    let V : Set (X × I) := {q | (r q).1 = X.point}
    have hU : IsClosed U := isClosed_eq r.continuous.snd continuous_const
    have hV : IsClosed V := hc.preimage r.continuous.fst
    have hUV : U ∪ V = Set.univ := by
      ext q
      exact iff_true_intro (hr q)
    let F : X × I → Y := fun q => if (r q).2 = 0 then f (r q).1 else p (r q).2
    have hu : ContinuousOn F U := (f.continuous.comp r.continuous.fst).continuousOn.congr
      (fun q hq => if_pos hq)
    have hv : ContinuousOn F V := (p.continuous.comp r.continuous.snd).continuousOn.congr (by
      intro q hq
      by_cases ht : (r q).2 = 0
      · change (if (r q).2 = 0 then f (r q).1 else p (r q).2) = p (r q).2
        rw [if_pos ht, ht, show (r q).1 = X.point from hq, hp]
      · exact if_neg ht)
    have hF : Continuous F := continuousOn_univ.mp (hUV ▸ hu.union_of_isClosed hv hU hV)
    refine ⟨⟨F,hF⟩,?_,?_⟩
    · intro x
      simp [F,hzero]
    · intro t
      change F (X.point,t) = p t
      simp only [F,hpoint]
      by_cases ht : t=0
      · simp [ht,hp]
      · simp [ht]
  have suspension_point_isClosed (X : BasedSpace.{u})
      (hc : IsClosed ({X.point} : Set X)) : IsClosed ({X.suspension.point} : Set X.suspension) := by
    let tag : X.suspension → Prop := Quot.lift (SuspensionCollapsed X)
      (fun p q hpq => propext ⟨fun _ => hpq.2, fun _ => hpq.1⟩)
    have hmem (p : X × I) : suspensionProjection X p = X.suspension.point ↔
        SuspensionCollapsed X p := by
      constructor
      · intro h
        have he := congrArg tag h
        change SuspensionCollapsed X p = SuspensionCollapsed X (X.point,0) at he
        exact he.mpr (Or.inl rfl)
      · exact suspensionProjection_collapsed X p
    apply isQuotientMap_quot_mk.isCoinducing.isClosed_preimage.mp
    change IsClosed {p : X × I | suspensionProjection X p = X.suspension.point}
    have hset : {p : X × I | suspensionProjection X p = X.suspension.point} =
        {p : X × I | p.1 = X.point} ∪ ({p : X × I | p.2 = 0} ∪ {p : X × I | p.2 = 1}) := by
      ext p
      exact hmem p
    rw [hset]
    exact (hc.preimage continuous_fst).union
      ((isClosed_eq continuous_snd continuous_const).union (isClosed_eq continuous_snd continuous_const))
  have interval_boundary_retraction :
      ∃ r : C(I × I,I × I),
        (∀ t, r (t,0) = (t,0)) ∧
        (∀ s, r (0,s) = (0,s)) ∧
        (∀ s, r (1,s) = (1,s)) ∧
        (∀ q, (r q).2 = 0 ∨ (r q).1 = 0 ∨ (r q).1 = 1) := by
    let m (q : I × I) : ℝ := max ((2-(q.2:ℝ))/2) (2*|(q.1:ℝ)-1/2|)
    have hb (t : I) : 2*|(t:ℝ)-1/2| ≤ 1 := by
      have h := abs_le.mpr (show -(1/2:ℝ) ≤ (t:ℝ)-1/2 ∧ (t:ℝ)-1/2 ≤ 1/2 from
        ⟨by linarith [t.property.1],by linarith [t.property.2]⟩)
      linarith
    have hm (q : I × I) : 0 < m q ∧ m q ≤ 1 := by
      constructor
      · have h := le_max_left ((2-(q.2:ℝ))/2) (2*|(q.1:ℝ)-1/2|)
        change 0 < max _ _
        linarith [q.2.property.2]
      · exact max_le (by linarith [q.2.property.1]) (hb q.1)
    have hx (q : I × I) : 1/2+((q.1:ℝ)-1/2)/m q ∈ Set.Icc (0:ℝ) 1 := by
      have hl : -(1/2:ℝ) ≤ ((q.1:ℝ)-1/2)/m q := by
        apply (le_div_iff₀ (hm q).1).mpr
        have h := le_max_right ((2-(q.2:ℝ))/2) (2*|(q.1:ℝ)-1/2|)
        change 2*|(q.1:ℝ)-1/2| ≤ m q at h
        linarith [neg_abs_le ((q.1:ℝ)-1/2)]
      have hu : ((q.1:ℝ)-1/2)/m q ≤ (1/2:ℝ) := by
        apply (div_le_iff₀ (hm q).1).mpr
        have h := le_max_right ((2-(q.2:ℝ))/2) (2*|(q.1:ℝ)-1/2|)
        change 2*|(q.1:ℝ)-1/2| ≤ m q at h
        linarith [le_abs_self ((q.1:ℝ)-1/2)]
      constructor <;> linarith
    have hy (q : I × I) : 2+((q.2:ℝ)-2)/m q ∈ Set.Icc (0:ℝ) 1 := by
      have hl : -(2:ℝ) ≤ ((q.2:ℝ)-2)/m q := by
        apply (le_div_iff₀ (hm q).1).mpr
        have h := le_max_left ((2-(q.2:ℝ))/2) (2*|(q.1:ℝ)-1/2|)
        change (2-(q.2:ℝ))/2 ≤ m q at h
        linarith
      have hu : ((q.2:ℝ)-2)/m q ≤ (q.2:ℝ)-2 := by
        apply (div_le_iff₀ (hm q).1).mpr
        nlinarith [(hm q).2,q.2.property.2]
      constructor <;> linarith [q.2.property.2]
    have hmcont : Continuous m :=
      ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).div_const 2).max
        (continuous_const.mul (((continuous_subtype_val.comp continuous_fst).sub continuous_const).abs))
    let r : C(I × I,I × I) := ⟨fun q => (⟨_,hx q⟩,⟨_,hy q⟩),
      ((continuous_const.add
        (((continuous_subtype_val.comp continuous_fst).sub continuous_const).div hmcont
          (fun q => ne_of_gt (hm q).1))).subtype_mk _).prodMk
        ((continuous_const.add
          (((continuous_subtype_val.comp continuous_snd).sub continuous_const).div hmcont
            (fun q => ne_of_gt (hm q).1))).subtype_mk _)⟩
    have hmzero (t : I) : m (t,0) = 1 := by
      dsimp [m]
      norm_num only [show ((0:I):ℝ)=0 from rfl,sub_zero,show (2:ℝ)/2=1 by norm_num]
      exact max_eq_left (hb t)
    have hmleft (s : I) : m (0,s) = 1 := by
      dsimp [m]
      norm_num only [show ((0:I):ℝ)=0 from rfl,zero_sub,abs_neg,abs_of_pos (by norm_num : (0:ℝ)<1/2),show (2:ℝ)*(1/2)=1 by norm_num]
      exact max_eq_right (by linarith [s.property.1])
    have hmright (s : I) : m (1,s) = 1 := by
      dsimp [m]
      norm_num only [show ((1:I):ℝ)=1 from rfl,show (1:ℝ)-1/2=1/2 by norm_num,abs_of_pos (by norm_num : (0:ℝ)<1/2),show (2:ℝ)*(1/2)=1 by norm_num]
      exact max_eq_right (by linarith [s.property.1])
    refine ⟨r,?_,?_,?_,?_⟩
    · intro t
      apply Prod.ext <;> apply Subtype.ext <;> simp [r,hmzero]
    · intro s
      apply Prod.ext <;> apply Subtype.ext <;> simp [r,hmleft]
    · intro s
      apply Prod.ext <;> apply Subtype.ext <;> simp [r,hmright]
    · intro q
      by_cases h : 2*|(q.1:ℝ)-1/2| ≤ (2-(q.2:ℝ))/2
      · left
        apply Subtype.ext
        change 2+((q.2:ℝ)-2)/m q = 0
        have hd : ((q.2:ℝ)-2)/m q = -2 := by
          apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
          dsimp [m]
          rw [max_eq_left h]
          ring
        rw [hd]
        norm_num
      · have hmax : m q = 2*|(q.1:ℝ)-1/2| := max_eq_right (le_of_not_ge h)
        by_cases ht : 0 ≤ (q.1:ℝ)-1/2
        · right; right
          apply Subtype.ext
          change 1/2+((q.1:ℝ)-1/2)/m q = 1
          have hd : ((q.1:ℝ)-1/2)/m q = 1/2 := by
            apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
            rw [hmax,abs_of_nonneg ht]
            ring
          rw [hd]
          norm_num
        · right; left
          apply Subtype.ext
          change 1/2+((q.1:ℝ)-1/2)/m q = 0
          have hd : ((q.1:ℝ)-1/2)/m q = -(1/2) := by
            apply (div_eq_iff (ne_of_gt (hm q).1)).mpr
            rw [hmax,abs_of_neg (lt_of_not_ge ht)]
            ring
          rw [hd]
          norm_num
  obtain ⟨rX,hrXzero,hrXpoint,hrX⟩ := cylinder_retraction_of_wellBased X hX
  obtain ⟨rI,hrIzero,hrIleft,hrIright,hrI⟩ := interval_boundary_retraction
  let raw : (X × I) × I → X.suspension × I := fun q =>
    (suspensionProjection X ((rX (q.1.1,q.2)).1,(rI (q.1.2,q.2)).1),
      max (min (rX (q.1.1,q.2)).2 q.2) (min (rI (q.1.2,q.2)).2 q.2))
  have raw_cont : Continuous raw := by
    have hxc : Continuous (fun q : (X × I) × I => rX (q.1.1,q.2)) :=
      rX.continuous.comp (continuous_fst.fst.prodMk continuous_snd)
    have hic : Continuous (fun q : (X × I) × I => rI (q.1.2,q.2)) :=
      rI.continuous.comp (continuous_fst.snd.prodMk continuous_snd)
    exact ((suspensionProjection X).continuous.comp (hxc.fst.prodMk hic.fst)).prodMk
      ((hxc.snd.min continuous_snd).max (hic.snd.min continuous_snd))
  have collapsed (p : X × I) (s : I) (hp : SuspensionCollapsed X p) :
      raw (p,s) = (X.suspension.point,s) := by
    rcases hp with hp | hp | hp
    · change (suspensionProjection X ((rX (p.1,s)).1,(rI (p.2,s)).1),
        max (min (rX (p.1,s)).2 s) (min (rI (p.2,s)).2 s)) = _
      rw [hp,hrXpoint]
      simp only [min_self,max_eq_left (min_le_right _ _)]
      exact Prod.ext (suspensionProjection_collapsed X _ (Or.inl rfl)) rfl
    · change (suspensionProjection X ((rX (p.1,s)).1,(rI (p.2,s)).1),
        max (min (rX (p.1,s)).2 s) (min (rI (p.2,s)).2 s)) = _
      rw [hp,hrIleft]
      simp only [min_self,max_eq_right (min_le_right _ _)]
      exact Prod.ext (suspensionProjection_collapsed X _ (Or.inr (Or.inl rfl))) rfl
    · change (suspensionProjection X ((rX (p.1,s)).1,(rI (p.2,s)).1),
        max (min (rX (p.1,s)).2 s) (min (rI (p.2,s)).2 s)) = _
      rw [hp,hrIright]
      simp only [min_self,max_eq_right (min_le_right _ _)]
      exact Prod.ext (suspensionProjection_collapsed X _ (Or.inr (Or.inr rfl))) rfl
  let rf : X.suspension × I → X.suspension × I := fun q =>
    Quot.lift (fun p : X × I => raw (p,q.2))
      (fun p p' h => (collapsed p q.2 h.1).trans (collapsed p' q.2 h.2).symm) q.1
  have hrf : Continuous rf := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    exact raw_cont
  let r : C(X.suspension × I,X.suspension × I) := ⟨rf,hrf⟩
  apply wellBased_of_cylinder_retraction X.suspension (suspension_point_isClosed X hX.1) r
  · intro z
    refine Quot.inductionOn z ?_
    intro p
    change raw (p,0) = (suspensionProjection X p,0)
    simp [raw,hrXzero,hrIzero]
  · intro s
    exact collapsed (X.point,0) s (Or.inl rfl)
  · rintro ⟨z,s⟩
    refine Quot.inductionOn z ?_
    intro p
    change (raw (p,s)).2 = 0 ∨ (raw (p,s)).1 = X.suspension.point
    rcases hrX (p.1,s) with hx | hx
    · rcases hrI (p.2,s) with hi | hi | hi
      · left
        change max (min (rX (p.1,s)).2 s) (min (rI (p.2,s)).2 s) = 0
        rw [hx,hi]
        simp
      · right
        apply suspensionProjection_collapsed
        exact Or.inr (Or.inl hi)
      · right
        apply suspensionProjection_collapsed
        exact Or.inr (Or.inr hi)
    · right
      apply suspensionProjection_collapsed
      exact Or.inl hx

theorem good_suspension {A : BasedSpace.{u}} (hA : A.IsGood) : A.suspension.IsGood := by
  have suspension_compactlyGenerated (A : BasedSpace.{u})
      [UCompactlyGeneratedSpace.{u} A] : UCompactlyGeneratedSpace.{u} A.suspension := by
    letI : UCompactlyGeneratedSpace.{u} (A × I) := by
      apply uCompactlyGeneratedSpace_of_continuous_maps
      intro Y _ f hf
      let F : A → C(I,Y) := fun a => ⟨fun t => f (a,t),by
        have hc := hf (CompHaus.of (ULift.{u} I))
          ⟨fun t => (a,t.down),continuous_const.prodMk continuous_uliftDown⟩
        exact hc.comp continuous_uliftUp⟩
      have hF : Continuous F := by
        apply continuous_from_uCompactlyGeneratedSpace
        intro S g
        have hg : Continuous (fun p : S × I => f (g p.1,p.2)) :=
          hf (CompHaus.of (S × I)) ⟨fun p => (g p.1,p.2),
            (g.continuous.comp continuous_fst).prodMk continuous_snd⟩
        exact (ContinuousMap.curry ⟨_,hg⟩).continuous
      exact ContinuousMap.continuous_uncurry_of_continuous ⟨F,hF⟩
    exact uCompactlyGeneratedSpace_of_coinduced (suspensionProjection A).continuous rfl
  letI : UCompactlyGeneratedSpace.{u} A := hA.1
  exact ⟨suspension_compactlyGenerated A,
    suspension_wellBased_of_wellBased A hA.2.1,suspension_hasCWType A hA.2.2⟩

-- Retain the named hypotheses in the statement of this theorem.
set_option linter.unusedVariables false in
/-- Moving the suspension coordinate past the second smash factor. The
formula fixes the comparison and its sign before stable localization. -/
theorem suspensionSmash_exists (A B : BasedSpace.{0})
    (hA : A.IsGood) (hB : B.IsGood) :
    ∃! f : A.suspension.smash B ⟶ (A.smash B).suspension, ∀ a b t,
      f.map (smashPoint _ B (suspensionProjection A (a,t)) b) =
        suspensionProjection (A.smash B) (smashPoint A B a b,t) := by
  letI : UCompactlyGeneratedSpace.{0} A := hA.1
  have product_k (K : CompHaus.{0}) : UCompactlyGeneratedSpace.{0} (A × K) := by
    apply uCompactlyGeneratedSpace_of_continuous_maps
    intro Y _ f hf
    let F : A → C(K,Y) := fun a =>
      ⟨fun k => f (a,k),hf K ⟨fun k => (a,k),continuous_const.prodMk continuous_id⟩⟩
    have hF : Continuous F := by
      apply continuous_from_uCompactlyGeneratedSpace
      intro S g
      have hg : Continuous (fun p : S × K => f (g p.1,p.2)) :=
        hf (CompHaus.of (S × K)) ⟨fun p => (g p.1,p.2),(g.continuous.comp continuous_fst).prodMk continuous_snd⟩
      exact (ContinuousMap.curry ⟨_,hg⟩).continuous
    exact ContinuousMap.continuous_uncurry_of_continuous ⟨F,hF⟩
  have into_k (K : CompHaus.{0}) (g : C(K,A × B)) :
      Continuous[inferInstance,TopologicalSpace.compactlyGenerated.{0} (A × B)] g := by
    let ev : (Σ i : (T : CompHaus.{0}) × C(T,A × B),i.fst) → A × B :=
      fun q => q.1.2 q.2
    have hi : Continuous (fun k : K => (⟨⟨K,g⟩,k⟩ :
        Σ i : (T : CompHaus.{0}) × C(T,A × B),i.fst)) :=
      @continuous_sigmaMk _ (fun i : (T : CompHaus.{0}) × C(T,A × B) => i.fst)
        (fun _ => inferInstance) ⟨K,g⟩
    letI : TopologicalSpace (A × B) := TopologicalSpace.coinduced ev inferInstance
    exact (show Continuous ev from continuous_coinduced_rng).comp hi
  have smashK (K : CompHaus.{0}) (β : C(K,B)) :
      Continuous (fun p : A × K => smashPoint A B p.1 (β p.2)) := by
    letI : UCompactlyGeneratedSpace.{0} (A × K) := product_k K
    have hk : Continuous[inferInstance,TopologicalSpace.compactlyGenerated.{0} (A × B)]
        (fun p : A × K => (p.1,β p.2)) := by
      refine @continuous_from_uCompactlyGeneratedSpace.{0} (A × K) (A × B)
        inferInstance (TopologicalSpace.compactlyGenerated.{0} (A × B)) inferInstance _ ?_
      intro S g
      exact into_k S ⟨fun s => ((g s).1,β (g s).2),
        g.continuous.fst.prodMk (β.continuous.comp g.continuous.snd)⟩
    letI : TopologicalSpace (A × B) := TopologicalSpace.compactlyGenerated.{0} (A × B)
    exact continuous_quot_mk.comp hk
  have inner_collapsed (b : B) (p : A × I) (hp : SuspensionCollapsed A p) :
      suspensionProjection (A.smash B) (smashPoint A B p.1 b,p.2) = (A.smash B).suspension.point := by
    rcases hp with h | h | h
    · rw [h,smashPoint_base_left]
      exact suspensionProjection_collapsed _ _ (Or.inl rfl)
    · exact suspensionProjection_collapsed _ _ (Or.inr (Or.inl h))
    · exact suspensionProjection_collapsed _ _ (Or.inr (Or.inr h))
  let raw : A.suspension × B → (A.smash B).suspension := fun p =>
    Quot.lift (fun q : A × I => suspensionProjection (A.smash B) (smashPoint A B q.1 p.2,q.2))
      (fun q r h => (inner_collapsed p.2 q h.1).trans (inner_collapsed p.2 r h.2).symm) p.1
  have rawK (K : CompHaus.{0}) (β : C(K,B)) :
      Continuous (fun p : A.suspension × K => raw (p.1,β p.2)) := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_left
    change Continuous (fun p : (A × I) × K =>
      suspensionProjection (A.smash B) (smashPoint A B p.1.1 (β p.2),p.1.2))
    exact (suspensionProjection (A.smash B)).continuous.comp
      (((smashK K β).comp (continuous_fst.fst.prodMk continuous_snd)).prodMk continuous_fst.snd)
  have hc : Continuous[TopologicalSpace.compactlyGenerated.{0} (A.suspension × B),inferInstance] raw := by
    apply continuous_from_compactlyGenerated
    intro K g
    exact (rawK K ⟨fun k => (g k).2,g.continuous.snd⟩).comp
      (g.continuous.fst.prodMk continuous_id)
  have collapsed (p : A.suspension × B) (hp : p.1 = A.suspension.point ∨ p.2 = B.point) :
      raw p = (A.smash B).suspension.point := by
    rcases hp with h | h
    · rcases p with ⟨a,b⟩
      dsimp only [Prod.fst] at h
      subst a
      exact inner_collapsed b (A.point,0) (Or.inl rfl)
    · rcases p with ⟨a,b⟩
      dsimp only [Prod.snd] at h
      subst b
      refine Quot.inductionOn a ?_
      intro p
      change suspensionProjection (A.smash B) (smashPoint A B p.1 B.point,p.2) = _
      rw [smashPoint_base_right]
      exact suspensionProjection_collapsed _ _ (Or.inl rfl)
  have respects : ∀ p q, SmashRelation A.suspension B p q → raw p = raw q :=
    fun p q h => (collapsed p h.1).trans (collapsed q h.2).symm
  letI : TopologicalSpace (A.suspension × B) :=
    TopologicalSpace.compactlyGenerated.{0} (A.suspension × B)
  let f : A.suspension.smash B ⟶ (A.smash B).suspension :=
    { map := ⟨Quot.lift raw respects,continuous_quot_lift respects hc⟩
      point := collapsed (A.suspension.point,B.point) (Or.inl rfl) }
  refine ⟨f,fun _ _ _ => rfl,?_⟩
  intro g hg
  apply Hom.ext
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,b⟩
  refine Quot.inductionOn a ?_
  rintro ⟨a,t⟩
  exact hg a b t

noncomputable def suspensionSmash (A B : BasedSpace.{0})
    (hA : A.IsGood) (hB : B.IsGood) : A.suspension.smash B ⟶ (A.smash B).suspension :=
  (suspensionSmash_exists A B hA hB).exists.choose

end BasedSpace

namespace Prespectrum

def suspensionSpectrum (A : BasedSpace.{u}) : Prespectrum.{u} where
  level := A.iterateSuspension
  bond _n := BasedSpace.suspensionProjection _
  bond_point _ _ := BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
  bond_zero _ _ := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond_one _ _ := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))

theorem suspensionSpectrum_good (A : BasedSpace.{u}) (hA : A.IsGood) :
    (suspensionSpectrum A).IsWellBased := by
  intro n
  have hg : ∀ n, (A.iterateSuspension n).IsGood := by
    intro n
    induction n with
    | zero => exact hA
    | succ n ih => exact BasedSpace.good_suspension ih
  exact (hg n).2.1

theorem suspensionSpectrum_zeroSphere :
    suspensionSpectrum BasedSpace.zeroSphere = sphere := by
  have h : BasedSpace.iterateSuspension BasedSpace.zeroSphere = sphereLevel := by
    funext n
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg BasedSpace.suspension ih
  have ext (X Y : Prespectrum.{0}) (hlevel : X.level = Y.level)
      (hbond : ∀ n, HEq (X.bond n) (Y.bond n)) : X = Y := by
    cases X
    cases Y
    cases hlevel
    have hb := funext fun n => eq_of_heq (hbond n)
    cases hb
    rfl
  apply ext _ _ h
  intro n
  have hp (A B : BasedSpace.{0}) (hab : A = B) :
      HEq A.suspensionProjection B.suspensionProjection := by
    cases hab
    rfl
  exact hp _ _ (congrFun h n)

def suspensionSpectrumMap {A B : BasedSpace.{u}} (f : A ⟶ B) :
    suspensionSpectrum A ⟶ suspensionSpectrum B where
  level n := (BasedSpace.iterateSuspensionMap f n).map
  point n := (BasedSpace.iterateSuspensionMap f n).point
  bond := by intros; rfl

/-- Rotate the original suspension coordinate to the outside. Unlike an
unjustified levelwise identity, this formula commutes with the bonds. -/
theorem suspensionSpectrumSuspensionIso_exists (A : BasedSpace.{0}) :
    ∃ e : suspensionSpectrum A.suspension ≅ (suspensionSpectrum A).suspension,
      ∀ n a s (t : Fin n → I), e.hom.level n
        (BasedSpace.iteratedPoint A.suspension n (BasedSpace.suspensionProjection A (a,s)) t) =
          BasedSpace.suspensionProjection (A.iterateSuspension n)
            (BasedSpace.iteratedPoint A n a t,s) := by
  let swapIso (A : BasedSpace.{0}) : A.suspension.suspension ≅ A.suspension.suspension := by
    let hf : ∀ t, A.suspensionProjection (A.point,t) = A.suspension.point :=
      fun _ => BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
    let raw : C(A.suspension × I,A.suspension.suspension) :=
      ⟨BasedSpace.suspensionFamily A A.suspension A.suspensionProjection hf,
        BasedSpace.continuous_suspensionFamily A A.suspension A.suspensionProjection hf⟩
    have collapse (p : A.suspension × I)
        (hp : BasedSpace.SuspensionCollapsed A.suspension p) :
        raw p = A.suspension.suspension.point := by
      rcases p with ⟨b,t⟩
      rcases hp with h | h | h
      · change b = A.suspension.point at h
        subst b
        exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
      · change t = 0 at h
        subst t
        refine Quot.inductionOn b ?_
        rintro ⟨a,s⟩
        change A.suspension.suspensionProjection (A.suspensionProjection (a,0),s) = _
        rw [BasedSpace.suspensionProjection_collapsed A (a,0) (Or.inr (Or.inl rfl))]
        exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
      · change t = 1 at h
        subst t
        refine Quot.inductionOn b ?_
        rintro ⟨a,s⟩
        change A.suspension.suspensionProjection (A.suspensionProjection (a,1),s) = _
        rw [BasedSpace.suspensionProjection_collapsed A (a,1) (Or.inr (Or.inr rfl))]
        exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
    have hr : ∀ a b, BasedSpace.SuspensionRelation A.suspension a b → raw a = raw b :=
      fun a b h => (collapse a h.1).trans (collapse b h.2).symm
    let f : A.suspension.suspension ⟶ A.suspension.suspension :=
      { map := ⟨Quot.lift raw hr, continuous_quot_lift hr raw.continuous⟩
        point := by
          change raw (A.suspension.point,0) = _
          exact collapse _ (Or.inl rfl) }
    have hinv : f ≫ f = 𝟙 _ := by
      apply BasedSpace.Hom.ext
      apply ContinuousMap.ext
      intro x
      refine Quot.inductionOn x ?_
      rintro ⟨b,t⟩
      refine Quot.inductionOn b ?_
      rintro ⟨a,s⟩
      rfl
    exact ⟨f,f,hinv,hinv⟩
  let liftIso {A B : BasedSpace.{0}} (e : A ≅ B) : A.suspension ≅ B.suspension := by
    refine ⟨BasedSpace.suspendMap e.hom, BasedSpace.suspendMap e.inv, ?_, ?_⟩
    · apply BasedSpace.Hom.ext
      apply ContinuousMap.ext
      intro x
      refine Quot.inductionOn x ?_
      rintro ⟨a,t⟩
      change A.suspensionProjection (e.inv.map (e.hom.map a),t) = A.suspensionProjection (a,t)
      have h := congrArg (fun f : A ⟶ A => f.map a) e.hom_inv_id
      exact congrArg (fun a => A.suspensionProjection (a,t)) h
    · apply BasedSpace.Hom.ext
      apply ContinuousMap.ext
      intro x
      refine Quot.inductionOn x ?_
      rintro ⟨b,t⟩
      change B.suspensionProjection (e.hom.map (e.inv.map b),t) = B.suspensionProjection (b,t)
      have h := congrArg (fun f : B ⟶ B => f.map b) e.inv_hom_id
      exact congrArg (fun b => B.suspensionProjection (b,t)) h
  let levels : ∀ n, A.suspension.iterateSuspension n ≅ (A.iterateSuspension n).suspension :=
    fun n => Nat.rec (Iso.refl _) (fun n e => liftIso e ≪≫ swapIso (A.iterateSuspension n)) n
  let f : suspensionSpectrum A.suspension ⟶ (suspensionSpectrum A).suspension :=
    { level n := (levels n).hom.map
      point n := (levels n).hom.point
      bond n x t := rfl }
  have hleft (n : ℕ) (x : A.suspension.iterateSuspension n) :
      (levels n).inv.map ((levels n).hom.map x) = x :=
    congrArg (fun h => BasedSpace.Hom.map h x) (levels n).hom_inv_id
  have hright (n : ℕ) (x : (A.iterateSuspension n).suspension) :
      (levels n).hom.map ((levels n).inv.map x) = x :=
    congrArg (fun h => BasedSpace.Hom.map h x) (levels n).inv_hom_id
  let g : (suspensionSpectrum A).suspension ⟶ suspensionSpectrum A.suspension :=
    { level n := (levels n).inv.map
      point n := (levels n).inv.point
      bond n x t := by
        apply (Function.LeftInverse.injective (hleft (n+1)))
        change (levels (n+1)).hom.map ((levels (n+1)).inv.map
          (((suspensionSpectrum A).suspension.bond n) (x,t))) =
          f.level (n+1) ((suspensionSpectrum A.suspension).bond n
            ((levels n).inv.map x,t))
        exact (hright (n+1) _).trans
          ((f.bond n ((levels n).inv.map x) t).trans
            (congrArg (fun z => ((suspensionSpectrum A).suspension.bond n) (z,t))
              (hright n x))).symm }
  refine ⟨⟨f,g,?_,?_⟩, ?_⟩
  · apply Prespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    exact hleft n
  · apply Prespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    exact hright n
  · intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro a s t
      change (levels (n+1)).hom.map (BasedSpace.suspensionProjection _
        (BasedSpace.iteratedPoint A.suspension n (BasedSpace.suspensionProjection A (a,s))
          (fun i => t i.succ), t 0)) = _
      change (swapIso (A.iterateSuspension n)).hom.map (BasedSpace.suspensionProjection _
        ((levels n).hom.map (BasedSpace.iteratedPoint A.suspension n
          (BasedSpace.suspensionProjection A (a,s)) (fun i => t i.succ)),t 0)) = _
      rw [show (levels n).hom.map (BasedSpace.iteratedPoint A.suspension n
        (BasedSpace.suspensionProjection A (a,s)) (fun i => t i.succ)) =
        BasedSpace.suspensionProjection _ (BasedSpace.iteratedPoint A n a
          (fun i => t i.succ),s) from ih a s (fun i => t i.succ)]
      rfl

noncomputable def suspensionSpectrumSuspensionIso (A : BasedSpace.{0}) :
    suspensionSpectrum A.suspension ≅ (suspensionSpectrum A).suspension :=
  (suspensionSpectrumSuspensionIso_exists A).choose

/-- Padding with one zero level gives an actual desuspension prespectrum. -/
def desuspension (X : Prespectrum.{u}) : Prespectrum.{u} where
  level
    | 0 => { space := TopCat.of PUnit, point := PUnit.unit }
    | n+1 => X.level n
  bond
    | 0 => ContinuousMap.const _ (X.level 0).point
    | n+1 => X.bond n
  bond_point := by intro n t; cases n <;> simp [X.bond_point]
  bond_zero := by intro n x; cases n <;> simp [X.bond_zero]
  bond_one := by intro n x; cases n <;> simp [X.bond_one]

def free (n : ℕ) (A : BasedSpace.{u}) : Prespectrum.{u} :=
  (desuspension^[n]) (suspensionSpectrum A)

/-- The free/evaluation adjunction pins down maps from free prespectra;
it is not an independently chosen assignment of stable maps. -/
theorem freeEvaluation_exists (n : ℕ) (A : BasedSpace.{u}) (X : Prespectrum.{u}) :
    ∃ e : (free n A ⟶ X) ≃ (A ⟶ X.level n),
      ∀ f, HEq ((e f).map) (f.level n) := by
  have freeBase (A : BasedSpace.{u}) (X : Prespectrum.{u}) :
      ∃ e : (suspensionSpectrum A ⟶ X) ≃ (A ⟶ X.level 0),
        ∀ f, (e f).map = f.level 0 := by
    let ev : (suspensionSpectrum A ⟶ X) → (A ⟶ X.level 0) :=
      fun f => ⟨f.level 0, f.point 0⟩
    have hinj : Function.Injective ev := by
      intro f g he
      apply Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      induction n with
      | zero => exact congrArg (fun h : A ⟶ X.level 0 => h.map x) he
      | succ n ih =>
        refine Quot.inductionOn x ?_
        rintro ⟨y,t⟩
        exact (f.bond n y t).trans ((congrArg (fun z => X.bond n (z,t)) (ih y)).trans
          (g.bond n y t).symm)
    have hsurj : Function.Surjective ev := by
      intro g
      let levels : ∀ n, A.iterateSuspension n ⟶ X.level n := by
        intro n
        induction n with
        | zero => exact g
        | succ n ih =>
          let raw : C(A.iterateSuspension n × I, X.level (n+1)) :=
            (X.bond n).comp ⟨fun p => (ih.map p.1,p.2),
              (ih.map.continuous.comp continuous_fst).prodMk continuous_snd⟩
          have collapse (p : A.iterateSuspension n × I)
              (hp : BasedSpace.SuspensionCollapsed (A.iterateSuspension n) p) :
              raw p = (X.level (n+1)).point := by
            rcases hp with h | h | h
            · change X.bond n (ih.map p.1,p.2) = _
              rw [h, ih.point, X.bond_point]
            · change X.bond n (ih.map p.1,p.2) = _
              rw [h, X.bond_zero]
            · change X.bond n (ih.map p.1,p.2) = _
              rw [h, X.bond_one]
          have hr : ∀ a b, BasedSpace.SuspensionRelation (A.iterateSuspension n) a b →
              raw a = raw b := fun a b h => (collapse a h.1).trans (collapse b h.2).symm
          exact ⟨⟨Quot.lift raw hr, continuous_quot_lift hr raw.continuous⟩,
            collapse _ (Or.inl rfl)⟩
      let f : suspensionSpectrum A ⟶ X :=
        { level n := (levels n).map
          point n := (levels n).point
          bond n x t := rfl }
      exact ⟨f, rfl⟩
    exact ⟨Equiv.ofBijective ev ⟨hinj, hsurj⟩, fun _ => rfl⟩
  induction n generalizing X with
  | zero =>
    obtain ⟨e, he⟩ := freeBase A X
    exact ⟨e, fun f => heq_of_eq (he f)⟩
  | succ n ih =>
    have hfree : free (n+1) A = desuspension (free n A) :=
      Function.iterate_succ_apply' desuspension n (suspensionSpectrum A)
    rw [hfree]
    let T : Prespectrum.{u} :=
      { level k := X.level (k+1)
        bond k := X.bond (k+1)
        bond_point k := X.bond_point (k+1)
        bond_zero k := X.bond_zero (k+1)
        bond_one k := X.bond_one (k+1) }
    let eD : (desuspension (free n A) ⟶ X) ≃ (free n A ⟶ T) :=
      { toFun f :=
          { level k := f.level (k+1)
            point k := f.point (k+1)
            bond k := f.bond (k+1) }
        invFun g :=
          { level
              | 0 => ContinuousMap.const _ (X.level 0).point
              | k+1 => g.level k
            point := by
              intro k
              cases k with
              | zero => rfl
              | succ k => exact g.point k
            bond := by
              intro k x t
              cases k with
              | zero =>
                change g.level 0 ((free n A).level 0).point = X.bond 0 ((X.level 0).point,t)
                rw [g.point, X.bond_point]
              | succ k => exact g.bond k x t }
        left_inv f := by
          apply Hom.ext
          funext k
          apply ContinuousMap.ext
          intro x
          cases k with
          | zero =>
            cases x
            exact (f.point 0).symm
          | succ k => rfl
        right_inv g := by
          apply Hom.ext
          rfl }
    obtain ⟨e, he⟩ := ih T
    exact ⟨eD.trans e, fun f => he (eD f)⟩

noncomputable def freeEvaluation (n : ℕ) (A : BasedSpace.{u}) (X : Prespectrum.{u}) :
    (free n A ⟶ X) ≃ (A ⟶ X.level n) :=
  (freeEvaluation_exists n A X).choose

noncomputable def freeCounit (X : Prespectrum.{u}) (n : ℕ) : free n (X.level n) ⟶ X :=
  (freeEvaluation n (X.level n) X).symm (𝟙 _)

end Prespectrum
end KIP126.StableHomotopy.Spectra
