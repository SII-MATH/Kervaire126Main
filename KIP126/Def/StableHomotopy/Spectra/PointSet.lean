module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum
public import Mathlib.Topology.Piecewise
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity

@[expose] public section

/-! Explicit point-set spheres, suspension, and mapping cones. All quotient
relations and maps are fixed below; unfinished obligations are continuity,
well-definedness, and compatibility proofs, not unspecified operations. -/

namespace KIP126.StableHomotopy.Spectra

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace BasedSpace

/-- The actual basepoint inclusion is a closed Hurewicz cofibration: its
homotopy extension property is quantified over continuous maps of spaces.
This condition is needed when using the ordinary reduced cone as a derived
cofiber; arbitrary based spaces are not silently assumed cofibrant. -/
def IsWellBased (X : BasedSpace.{u}) : Prop :=
  IsClosed ({X.point} : Set X) ∧
    ∀ (Y : TopCat.{u}) (f : C(X,Y)) (p : C(I,Y)), p 0 = f X.point →
      ∃ H : C(X × I,Y), (∀ x, H (x,0) = f x) ∧ (∀ t, H (X.point,t) = p t)

def SuspensionCollapsed (X : BasedSpace.{u}) (p : X × I) : Prop :=
  p.1 = X.point ∨ p.2 = 0 ∨ p.2 = 1

def SuspensionRelation (X : BasedSpace.{u}) (p q : X × I) : Prop :=
  SuspensionCollapsed X p ∧ SuspensionCollapsed X q

def suspension (X : BasedSpace.{u}) : BasedSpace.{u} where
  space := TopCat.of (Quot (SuspensionRelation X))
  point := Quot.mk _ (X.point, 0)

def suspensionProjection (X : BasedSpace.{u}) : C(X × I, X.suspension) :=
  ⟨Quot.mk _, continuous_quot_mk⟩

theorem suspensionProjection_collapsed (X : BasedSpace.{u}) (p : X × I)
    (h : SuspensionCollapsed X p) : suspensionProjection X p = X.suspension.point :=
  Quot.sound ⟨h, Or.inl rfl⟩

/-- Pointwise suspension of a based continuous family of maps. -/
def suspensionFamily (X Y : BasedSpace.{u}) (f : C(X × I, Y))
    (hf : ∀ t, f (X.point,t) = Y.point) (p : X.suspension × I) : Y.suspension :=
  Quot.lift (fun q : X × I => suspensionProjection Y (f (q.1,p.2),q.2))
    (by
      intro a b hab
      apply Eq.trans _ (suspensionProjection_collapsed Y _ ?_).symm
      · apply suspensionProjection_collapsed
        rcases hab.1 with h | h | h
        · exact Or.inl (h ▸ hf p.2)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases hab.2 with h | h | h
        · exact Or.inl (h ▸ hf p.2)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)) p.1

theorem continuous_suspensionFamily (X Y : BasedSpace.{u}) (f : C(X × I, Y))
    (hf : ∀ t, f (X.point,t) = Y.point) : Continuous (suspensionFamily X Y f hf) := by
  apply isQuotientMap_quot_mk.continuous_lift_prod_left
  exact (suspensionProjection Y).continuous.comp
    ((f.continuous.comp ((continuous_fst.fst).prodMk continuous_snd)).prodMk
      continuous_fst.snd)

def suspensionMap (X Y : BasedSpace.{u}) (f : C(X,Y)) (hf : f X.point = Y.point) :
    C(X.suspension,Y.suspension) := by
  let raw : C(X × I,Y.suspension) :=
    (suspensionProjection Y).comp ⟨fun p => (f p.1,p.2),
      (f.continuous.comp continuous_fst).prodMk continuous_snd⟩
  have respects : ∀ a b, SuspensionRelation X a b → raw a = raw b := by
    intro a b hab
    have collapsed : ∀ p, SuspensionCollapsed X p → raw p = Y.suspension.point := by
      intro p hp
      apply suspensionProjection_collapsed
      rcases hp with h | h | h
      · left
        change f p.1 = Y.point
        rw [h]
        exact hf
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    exact (collapsed a hab.1).trans (collapsed b hab.2).symm
  exact ⟨Quot.lift raw respects, continuous_quot_lift respects raw.continuous⟩

/-- The fixed reduced suspension preserves the actual point homotopy extension
property, using continuous retractions of the two cylinder pairs. -/
private theorem suspension_wellBased (X : BasedSpace.{u}) (hX : X.IsWellBased) :
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

section
universe v

/-- A deformation inverse whose basepoint follows a displayed path induces
a bijection on based cubical homotopy classes, including dimension zero. -/
private theorem loops_equivalence_of_deformation {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (x₀ : X) (y₀ : Y)
    (q : C(Y,X)) (hq : q y₀=x₀) (j : C(X,Y))
    (hqj : q.comp j=ContinuousMap.id X) (γ : C(I,Y))
    (hγ0 : γ 0=y₀) (hγ1 : γ 1=j x₀) (hqγ : ∀ t, q (γ t)=x₀)
    (H : (ContinuousMap.id Y).Homotopy (j.comp q))
    (hH : ∀ t, H (t,y₀)=γ t) :
    (∀ n (p p' : GenLoop (Fin n) Y y₀),
      GenLoop.Homotopic
        (⟨q.comp p.val,fun t ht => (congrArg q (p.property t ht)).trans hq⟩ :
          GenLoop (Fin n) X x₀)
        ⟨q.comp p'.val,fun t ht => (congrArg q (p'.property t ht)).trans hq⟩ →
      GenLoop.Homotopic p p') ∧
    (∀ n (p : GenLoop (Fin n) X x₀),
      ∃ l : GenLoop (Fin n) Y y₀,
        GenLoop.Homotopic
          (⟨q.comp l.val,fun t ht => (congrArg q (l.property t ht)).trans hq⟩ :
            GenLoop (Fin n) X x₀) p) := by
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

  have cube_boundary_hep (n : ℕ) {Y : Type v} [TopologicalSpace Y]
      (f : C((Fin n → I),Y)) (p : C(I,Y))
      (hp : ∀ x, x ∈ Cube.boundary (Fin n) → f x=p 0) :
      ∃ H : C((Fin n → I) × I,Y), (∀ x, H (x,0)=f x) ∧
        (∀ x, x ∈ Cube.boundary (Fin n) → ∀ t, H (x,t)=p t) := by
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
    have hUV : U ∪ V=Set.univ := by
      ext q
      exact iff_true_intro (hr q)
    let F (q : (Fin n → I) × I) := if (r q).2=0 then f (r q).1 else p (r q).2
    have hu : ContinuousOn F U := (f.continuous.comp r.continuous.fst).continuousOn.congr
      (fun q hq => if_pos hq)
    have hv : ContinuousOn F V := (p.continuous.comp r.continuous.snd).continuousOn.congr (by
      intro q hq
      by_cases ht : (r q).2=0
      · change (if (r q).2=0 then f (r q).1 else p (r q).2)=p (r q).2
        rw [if_pos ht,ht,hp (r q).1 hq]
      · exact if_neg ht)
    have hF : Continuous F := continuousOn_univ.mp (hUV ▸ hu.union_of_isClosed hv hU hV)
    refine ⟨⟨F,hF⟩,?_,?_⟩
    · intro x
      simp [F,hzero]
    · intro x hx t
      change F (x,t)=p t
      dsimp only [F]
      rw [hboundary x hx t]
      by_cases ht : t=0
      · simp [ht,hp x hx]
      · simp [ht]

  have loops_surj_of_deformation {X : Type u} {Y : Type v}
      [TopologicalSpace X] [TopologicalSpace Y] (x₀ : X) (y₀ : Y)
      (q : C(Y,X)) (hq : q y₀=x₀) (j : C(X,Y))
      (hqj : q.comp j=ContinuousMap.id X) (γ : Path y₀ (j x₀))
      (hqγ : ∀ t, q (γ t)=x₀) (n : ℕ)
      (p : GenLoop (Fin n) X x₀) :
      ∃ l : GenLoop (Fin n) Y y₀,
        GenLoop.Homotopic
          (⟨q.comp l.val,fun t ht => (congrArg q (l.property t ht)).trans hq⟩ :
            GenLoop (Fin n) X x₀) p := by
    obtain ⟨F,hF0,hFb⟩ := cube_boundary_hep n (j.comp p.val) γ.symm.toContinuousMap (by
      intro x hx
      change j (p x)=γ.symm 0
      exact (congrArg j (p.property x hx)).trans γ.symm.source.symm)
    let l : GenLoop (Fin n) Y y₀ := ⟨⟨fun x => F (x,1),
      F.continuous.comp (continuous_id.prodMk continuous_const)⟩,by
        intro x hx
        change F (x,1)=y₀
        rw [hFb x hx 1]
        exact γ.symm.target⟩
    refine ⟨l,GenLoop.Homotopic.symm ?_⟩
    refine ⟨{ toFun := fun z => q (F (z.2,z.1))
              continuous_toFun := q.continuous.comp (F.continuous.comp continuous_swap)
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro x
      rw [hF0]
      exact DFunLike.congr_fun hqj (p x)
    · intro x
      rfl
    · intro t x hx
      change q (F (x,t))=p x
      rw [hFb x hx t]
      exact (hqγ _).trans (p.property x hx).symm


  have loops_homotopic_of_null_boundary {Y : Type v} [TopologicalSpace Y]
      (y₀ : Y) (n : ℕ) (p p' : GenLoop (Fin n) Y y₀)
      (W : p.val.Homotopy p'.val) (δ : Path y₀ y₀)
      (hW : ∀ t x, x ∈ Cube.boundary (Fin n) → W (t,x)=δ t)
      (hδ : δ.Homotopic (Path.refl y₀)) : GenLoop.Homotopic p p' := by
    obtain ⟨D⟩ := hδ
    let f : C((Fin n → I),C(I,Y)) :=
      (W.toContinuousMap.comp ⟨Prod.swap,continuous_swap⟩).curry
    obtain ⟨F,hF0,hFb⟩ := cube_boundary_hep n f D.toHomotopy.toContinuousMap.curry (by
      intro x hx
      ext t
      change W (t,x)=D (0,t)
      rw [D.apply_zero]
      exact hW t x hx)
    let a : GenLoop (Fin n) Y y₀ := ⟨⟨fun x => F (x,1) 0,by fun_prop⟩,by
      intro x hx
      change F (x,1) 0=y₀
      rw [hFb x hx 1]
      exact D.source 1⟩
    let b : GenLoop (Fin n) Y y₀ := ⟨⟨fun x => F (x,1) 1,by fun_prop⟩,by
      intro x hx
      change F (x,1) 1=y₀
      rw [hFb x hx 1]
      exact D.target 1⟩
    have hpa : GenLoop.Homotopic p a := by
      refine ⟨{ toFun := fun z => F (z.2,z.1) 0
                continuous_toFun := by fun_prop
                map_zero_left := ?_
                map_one_left := fun _ => rfl
                prop' := ?_ }⟩
      · intro x
        rw [hF0]
        exact W.apply_zero x
      · intro t x hx
        change F (x,t) 0=p x
        rw [hFb x hx t]
        exact (D.source t).trans (p.property x hx).symm
    have hab : GenLoop.Homotopic a b := by
      refine ⟨{ toFun := fun z => F (z.2,1) z.1
                continuous_toFun := by fun_prop
                map_zero_left := fun _ => rfl
                map_one_left := fun _ => rfl
                prop' := ?_ }⟩
      intro t x hx
      change F (x,1) t=F (x,1) 0
      rw [hFb x hx 1]
      change D (1,t)=D (1,0)
      rw [D.apply_one,D.apply_one]
      rfl
    have hpb : GenLoop.Homotopic p' b := by
      refine ⟨{ toFun := fun z => F (z.2,z.1) 1
                continuous_toFun := by fun_prop
                map_zero_left := ?_
                map_one_left := fun _ => rfl
                prop' := ?_ }⟩
      · intro x
        rw [hF0]
        exact W.apply_one x
      · intro t x hx
        change F (x,t) 1=p' x
        rw [hFb x hx t]
        exact (D.target t).trans (p'.property x hx).symm
    exact hpa.trans (hab.trans hpb.symm)

  have loops_inj_of_deformation {X : Type u} {Y : Type v}
      [TopologicalSpace X] [TopologicalSpace Y] (x₀ : X) (y₀ : Y)
      (q : C(Y,X)) (hq : q y₀=x₀) (j : C(X,Y))
      (γ : Path y₀ (j x₀))
      (H : (ContinuousMap.id Y).Homotopy (j.comp q))
      (hH : ∀ t, H (t,y₀)=γ t) (n : ℕ)
      (p p' : GenLoop (Fin n) Y y₀)
      (h : GenLoop.Homotopic
        (⟨q.comp p.val,fun t ht => (congrArg q (p.property t ht)).trans hq⟩ :
          GenLoop (Fin n) X x₀)
        ⟨q.comp p'.val,fun t ht => (congrArg q (p'.property t ht)).trans hq⟩) :
      GenLoop.Homotopic p p' := by
    obtain ⟨K⟩ := h
    let A : p.val.Homotopy (j.comp (q.comp p.val)) :=
      { toFun := fun z => H (z.1,p z.2)
        continuous_toFun := by fun_prop
        map_zero_left := fun x => H.apply_zero (p x)
        map_one_left := fun x => H.apply_one (p x) }
    let B : (j.comp (q.comp p.val)).Homotopy (j.comp (q.comp p'.val)) :=
      { toFun := fun z => j (K z)
        continuous_toFun := by fun_prop
        map_zero_left := fun x => congrArg j (K.apply_zero x)
        map_one_left := fun x => congrArg j (K.apply_one x) }
    let C : p'.val.Homotopy (j.comp (q.comp p'.val)) :=
      { toFun := fun z => H (z.1,p' z.2)
        continuous_toFun := by fun_prop
        map_zero_left := fun x => H.apply_zero (p' x)
        map_one_left := fun x => H.apply_one (p' x) }
    let W := (A.trans B).trans C.symm
    let δ := (γ.trans (Path.refl (j x₀))).trans γ.symm
    have hW : ∀ t x, x ∈ Cube.boundary (Fin n) → W (t,x)=δ t := by
      intro t x hx
      have ha (s : I) : A (s,x)=γ s := by
        change H (s,p x)=γ s
        have hp : p x=y₀ := p.property x hx
        rw [hp,hH]
      have hb (s : I) : B (s,x)=j x₀ := by
        change j (K (s,x))=j x₀
        apply congrArg j
        exact (K.eq_fst s hx).trans ((congrArg q (p.property x hx)).trans hq)
      have hc (s : I) : C.symm (s,x)=γ.symm s := by
        change H (unitInterval.symm s,p' x)=γ (unitInterval.symm s)
        have hp : p' x=y₀ := p'.property x hx
        rw [hp,hH]
      change ((A.trans B).trans C.symm) (t,x) =
        ((γ.trans (Path.refl (j x₀))).trans γ.symm) t
      rw [ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
      split_ifs with ht
      · rw [ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
        split_ifs <;> first | exact ha _ | exact hb _
      · exact hc _
    have hδ : δ.Homotopic (Path.refl y₀) :=
      ((Path.Homotopic.trans_refl γ).hcomp (Path.Homotopic.refl γ.symm)).trans
        (Path.Homotopic.trans_symm γ)
    exact loops_homotopic_of_null_boundary y₀ n p p' W δ hW hδ


  let γ' : Path y₀ (j x₀) := ⟨γ,hγ0,hγ1⟩
  exact ⟨fun n p p' hp => loops_inj_of_deformation x₀ y₀ q hq j γ' H hH n p p' hp,
    fun n p => loops_surj_of_deformation x₀ y₀ q hq j hqj γ' hqγ n p⟩

end

end BasedSpace

namespace Prespectrum

def IsWellBased (X : Prespectrum.{u}) : Prop := ∀ n, (X.level n).IsWellBased

/-- The sphere prespectrum has level Sⁿ, formed by iterated actual reduced
suspension of the discrete based two-point space. -/
def sphereLevel : ℕ → BasedSpace
  | 0 => { space := TopCat.of (Fin 2), point := 0 }
  | n + 1 => (sphereLevel n).suspension

def sphere : Prespectrum where
  level := sphereLevel
  bond n := BasedSpace.suspensionProjection (sphereLevel n)
  bond_point _n _t := BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)
  bond_zero _n _x := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond_one _n _x := BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))

/-- The positive generator of π₀ of the ordinary sphere: the non-basepoint
of S⁰, viewed as a zero-dimensional cubical loop. -/
def sphereGenerator : StableHomotopy sphere 0 :=
  loopClass sphere 0 0 0 (by norm_num)
    ⟨ContinuousMap.const _ (show sphere.level 0 from (1 : Fin 2)), by
      intro t ht
      obtain ⟨i, _⟩ := ht
      exact Fin.elim0 i⟩

theorem sphere_wellBased : sphere.IsWellBased := by
  classical
  intro n
  change (sphereLevel n).IsWellBased
  induction n with
  | zero =>
    letI : DiscreteTopology (sphereLevel 0) := inferInstanceAs (DiscreteTopology (Fin 2))
    refine ⟨isClosed_singleton, ?_⟩
    intro Y f p hp
    let H : C(sphereLevel 0 × I,Y) := ContinuousMap.uncurry
      ⟨fun x => if x = (sphereLevel 0).point then p else ContinuousMap.const I (f x),
        continuous_of_discreteTopology⟩
    refine ⟨H, ?_, ?_⟩
    · intro x
      by_cases hx : x = (sphereLevel 0).point
      · simpa [H,hx] using hp
      · simp [H,hx]
    · intro t
      simp [H]
  | succ n hn => exact BasedSpace.suspension_wellBased (sphereLevel n) hn

/-- Mapping cylinders recursively replace the levels while retaining strict
compatibility with the original prespectrum bonds. -/
private theorem wellBased_replacement_with_deformation (X : Prespectrum.{u}) :
    ∃ (Y : Prespectrum.{u}) (_ : Y.IsWellBased) (q : Y ⟶ X),
      ∀ n, ∃ (j : C(X.level n,Y.level n)) (γ : C(I,Y.level n)),
        (q.level n).comp j=ContinuousMap.id (X.level n) ∧
        γ 0=(Y.level n).point ∧ γ 1=j (X.level n).point ∧
        (∀ t, q.level n (γ t)=(X.level n).point) ∧
        ∃ H : (ContinuousMap.id (Y.level n)).Homotopy (j.comp (q.level n)),
          (∀ t, H (t,(Y.level n).point)=γ t) ∧ (∀ t x, H (t,j x)=j x) ∧
          (∀ t y, q.level n (H (t,y))=q.level n y) := by
  have mappingCylinder_exists (A X : BasedSpace.{u}) (hA : A.IsWellBased)
      (f : C(A,X)) (hf : f A.point=X.point) :
      ∃ Y : BasedSpace.{u}, Y.IsWellBased ∧
        ∃ (i : C(A,Y)) (q : C(Y,X)) (j : C(X,Y)) (γ : C(I,Y)),
          i A.point=Y.point ∧ q Y.point=X.point ∧ q.comp i=f ∧
          q.comp j=ContinuousMap.id X ∧ γ 0=Y.point ∧ γ 1=j X.point ∧
          (∀ t, q (γ t)=X.point) ∧
          ∃ H : (ContinuousMap.id Y).Homotopy (j.comp q),
            (∀ t, H (t,Y.point)=γ t) ∧ (∀ t x, H (t,j x)=j x) ∧
            (∀ t y, q (H (t,y))=q y) := by
    classical
    let R : ((A × I) ⊕ X) → ((A × I) ⊕ X) → Prop :=
      fun p q => ∃ a : A, p=Sum.inl (a,1) ∧ q=Sum.inr (f a)
    let Y : BasedSpace.{u} := ⟨TopCat.of (Quot R),Quot.mk R (.inl (A.point,0))⟩
    let π : C((A × I) ⊕ X,Y) := ⟨Quot.mk R,continuous_quot_mk⟩
    have glue (a : A) : π (.inl (a,1))=π (.inr (f a)) := Quot.sound ⟨a,rfl,rfl⟩
    let i : C(A,Y) := π.comp ⟨fun a => .inl (a,0),continuous_inl.comp (continuous_id.prodMk continuous_const)⟩
    let j : C(X,Y) := π.comp ⟨Sum.inr,continuous_inr⟩
    let rawq : (A × I) ⊕ X → X := Sum.elim (fun p => f p.1) id
    have hq : ∀ p r, R p r → rawq p=rawq r := by
      rintro _ _ ⟨a,rfl,rfl⟩
      rfl
    let q : C(Y,X) := ⟨Quot.lift rawq hq,continuous_quot_lift hq
      (continuous_sum_dom.mpr ⟨f.continuous.comp continuous_fst,continuous_id⟩)⟩
    let γ : C(I,Y) := π.comp ⟨fun t => .inl (A.point,t),
      continuous_inl.comp (continuous_const.prodMk continuous_id)⟩
    have hclosed : IsClosed ({Y.point} : Set Y) := by
      let tag : Y → Prop := Quot.lift
        (Sum.elim (fun p : A × I => p.1=A.point ∧ p.2=0) (fun _ : X => False)) (by
          rintro _ _ ⟨a,rfl,rfl⟩
          apply propext
          simp)
      have hpre (p : (A × I) ⊕ X) : π p=Y.point ↔
          p=Sum.inl (A.point,0) := by
        constructor
        · intro hp
          have hh := congrArg tag hp
          cases p with
          | inl p =>
            change (p.1=A.point ∧ p.2=0) = (A.point=A.point ∧ (0:I)=0) at hh
            have h := hh.mpr ⟨rfl,rfl⟩
            exact congrArg Sum.inl (Prod.ext h.1 h.2)
          | inr x =>
            change False=(A.point=A.point ∧ (0:I)=0) at hh
            exact False.elim (hh.mpr ⟨rfl,rfl⟩)
        · rintro rfl
          rfl
      apply isQuotientMap_quot_mk.isCoinducing.isClosed_preimage.mp
      change IsClosed {p : (A × I) ⊕ X | π p=Y.point}
      have he : {p : (A × I) ⊕ X | π p=Y.point}={Sum.inl (A.point,0)} := by
        ext p
        exact hpre p
      rw [he]
      apply isClosed_sum_iff.mpr
      constructor
      · change IsClosed {p : A × I | Sum.inl p = Sum.inl (A.point,0)}
        have he : {p : A × I | Sum.inl p = (Sum.inl (A.point,0) : (A × I) ⊕ X)} =
            ({A.point} : Set A) ×ˢ ({0} : Set I) := by ext p; simp
        rw [he]
        exact hA.1.prod isClosed_singleton
      · have he : Sum.inr ⁻¹' ({Sum.inl (A.point,0)} : Set ((A × I) ⊕ X)) = (∅ : Set X) := by
          ext x
          simp
        rw [he]
        exact isClosed_empty
    have hwell : Y.IsWellBased := by
      refine ⟨hclosed,?_⟩
      intro Z F p hp
      obtain ⟨H,hH,hP⟩ := hA.2 Z (F.comp i) p hp
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
      let V : (A × I) × I → Z := fun b =>
        if 2*(b.1.2:ℝ) ≤ (b.2:ℝ) then H (b.1.1,l (b.1.2,b.2))
        else F (π (.inl (b.1.1,r (b.1.2,b.2))))
      have hV : Continuous V := by
        apply continuous_if_le
          (continuous_const.mul (continuous_subtype_val.comp continuous_fst.snd))
          (continuous_subtype_val.comp continuous_snd)
          (H.continuous.comp (continuous_fst.fst.prodMk
            (hl.comp (continuous_fst.snd.prodMk continuous_snd)))).continuousOn
          (F.continuous.comp (π.continuous.comp (continuous_inl.comp
            (continuous_fst.fst.prodMk (hr.comp (continuous_fst.snd.prodMk continuous_snd)))))).continuousOn
        intro b hb
        change 2*(b.1.2:ℝ)=(b.2:ℝ) at hb
        change H (b.1.1,l (b.1.2,b.2))=F (π (.inl (b.1.1,r (b.1.2,b.2))))
        have hl0 : l (b.1.2,b.2)=0 := by apply Subtype.ext; simp [l,← hb]
        have hr0 : r (b.1.2,b.2)=0 := by apply Subtype.ext; simp [r,← hb]
        rw [hl0,hr0,hH]
        rfl
      have hVtop (a : A) (t : I) : V ((a,1),t)=F (j (f a)) := by
        have ht : ¬ 2*(1:ℝ) ≤ (t:ℝ) := by linarith [t.property.2]
        have hr1 : r (1,t)=1 := by
          apply Subtype.ext
          change max (2*1-(t:ℝ)) 0/(2-(t:ℝ))=1
          rw [max_eq_left (by linarith [t.property.2])]
          simp only [mul_one]
          exact div_self (by linarith [t.property.2])
        dsimp only [V]
        simp only [show ((1:I):ℝ)=1 from rfl]
        rw [if_neg ht,hr1,glue]
        rfl
      let raw (b : ((A × I) ⊕ X) × I) : Z :=
        Sum.elim (fun a => V (a,b.2)) (fun x => F (j x)) b.1
      have hraw : Continuous raw := by
        let v : C(A × I,C(I,Z)) := ContinuousMap.curry ⟨V,hV⟩
        let w : C(X,C(I,Z)) := ContinuousMap.curry
          ⟨fun b : X × I => F (j b.1),F.continuous.comp (j.continuous.comp continuous_fst)⟩
        refine (ContinuousMap.continuous_uncurry_of_continuous
          ⟨Sum.elim v w,continuous_sum_dom.mpr ⟨v.continuous,w.continuous⟩⟩).congr ?_
        rintro ⟨a,t⟩
        cases a <;> rfl
      have respects (t : I) : ∀ a b, R a b → raw (a,t)=raw (b,t) := by
        rintro _ _ ⟨a,rfl,rfl⟩
        exact hVtop a t
      let out : C(Y × I,Z) := ⟨fun b => Quot.lift (fun a => raw (a,b.2)) (respects b.2) b.1,by
        apply isQuotientMap_quot_mk.continuous_lift_prod_left
        exact hraw⟩
      refine ⟨out,?_,?_⟩
      · intro y
        refine Quot.inductionOn y ?_
        intro b
        cases b with
        | inr x => rfl
        | inl a =>
          change V (a,0)=F (π (.inl a))
          dsimp only [V]
          simp only [show ((0:I):ℝ)=0 from rfl]
          by_cases ha : 2*(a.2:ℝ) ≤ 0
          · have ha0 : a.2=0 := Subtype.ext (by change (a.2:ℝ)=0; linarith [a.2.property.1])
            rw [ha0]
            simp only [show ((0:I):ℝ)=0 from rfl,mul_zero,le_refl,if_true]
            have hl0 : l (0,0)=0 := by apply Subtype.ext; norm_num [l]
            rw [hl0,hH]
            change F (π (.inl (a.1,0)))=F (π (.inl a))
            rw [← ha0]
          · rw [if_neg ha]
            have hr0 : r (a.2,0)=a.2 := by
              apply Subtype.ext
              dsimp [r]
              rw [max_eq_left (by linarith [a.2.property.1])]
              ring
            rw [hr0]
      · intro t
        change V ((A.point,0),t)=p t
        have hl0 : l (0,t)=t := by
          apply Subtype.ext
          simp [l,max_eq_left t.property.1]
        dsimp only [V]
        rw [if_pos (by simpa using t.property.1),hl0,hP]
    let push (b : I × I) : I := ⟨(b.1:ℝ)+(b.2:ℝ)*(1-(b.1:ℝ)),by
      constructor
      · nlinarith [b.1.property.1,b.2.property.1,b.1.property.2]
      · nlinarith [b.1.property.2,b.2.property.2,
          mul_nonneg (sub_nonneg.mpr b.1.property.2) (sub_nonneg.mpr b.2.property.2)]⟩
    have hpcont : Continuous push :=
      ((continuous_subtype_val.comp continuous_fst).add
        ((continuous_subtype_val.comp continuous_snd).mul
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))).subtype_mk _
    have push_zero (h : I) : push (h,0)=h := by apply Subtype.ext; simp [push]
    have push_one (h : I) : push (h,1)=1 := by apply Subtype.ext; simp [push]
    have push_top (t : I) : push (1,t)=1 := by apply Subtype.ext; simp [push]
    have push_bottom (t : I) : push (0,t)=t := by apply Subtype.ext; simp [push]
    let rawD (b : ((A × I) ⊕ X) × I) : Y :=
      Sum.elim (fun a => π (.inl (a.1,push (a.2,b.2)))) j b.1
    have hrawD : Continuous rawD := by
      let v : C(A × I,C(I,Y)) := ContinuousMap.curry
        ⟨fun b : (A × I) × I => π (.inl (b.1.1,push (b.1.2,b.2))),
          π.continuous.comp (continuous_inl.comp (continuous_fst.fst.prodMk
            (hpcont.comp (continuous_fst.snd.prodMk continuous_snd))))⟩
      let w : C(X,C(I,Y)) := ContinuousMap.curry
        ⟨fun b : X × I => j b.1,j.continuous.comp continuous_fst⟩
      refine (ContinuousMap.continuous_uncurry_of_continuous
        ⟨Sum.elim v w,continuous_sum_dom.mpr ⟨v.continuous,w.continuous⟩⟩).congr ?_
      rintro ⟨a,t⟩
      cases a <;> rfl
    have hD (t : I) : ∀ a b, R a b → rawD (a,t)=rawD (b,t) := by
      rintro _ _ ⟨a,rfl,rfl⟩
      change π (.inl (a,push (1,t)))=j (f a)
      rw [push_top,glue]
      rfl
    let D : C(Y × I,Y) := ⟨fun b => Quot.lift (fun a => rawD (a,b.2)) (hD b.2) b.1,by
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact hrawD⟩
    let H : (ContinuousMap.id Y).Homotopy (j.comp q) :=
      { toFun := fun b => D (b.2,b.1)
        continuous_toFun := D.continuous.comp continuous_swap
        map_zero_left := by
          intro y
          refine Quot.inductionOn y ?_
          intro a
          cases a with
          | inl a =>
            change π (.inl (a.1,push (a.2,0)))=π (.inl a)
            rw [push_zero]
          | inr x => rfl
        map_one_left := by
          intro y
          refine Quot.inductionOn y ?_
          intro a
          cases a with
          | inl a =>
            change π (.inl (a.1,push (a.2,1)))=j (f a.1)
            rw [push_one,glue]
            rfl
          | inr x => rfl }
    refine ⟨Y,hwell,i,q,j,γ,rfl,hf,?_,?_,rfl,?_,?_,H,?_,?_,?_⟩
    · rfl
    · rfl
    · change π (.inl (A.point,1))=π (.inr X.point)
      rw [glue,hf]
    · intro t
      exact hf
    · intro t
      change π (.inl (A.point,push (0,t)))=π (.inl (A.point,t))
      rw [push_bottom]
    · intro t x
      rfl
    · intro t y
      refine Quot.inductionOn y ?_
      intro a
      cases a <;> rfl
  classical
  let LocalData (n : ℕ) (Y : BasedSpace.{u}) (q : C(Y,X.level n)) : Prop :=
    ∃ (j : C(X.level n,Y)) (γ : C(I,Y)), q.comp j=ContinuousMap.id (X.level n) ∧
      γ 0=Y.point ∧ γ 1=j (X.level n).point ∧
      (∀ t, q (γ t)=(X.level n).point) ∧
      ∃ H : (ContinuousMap.id Y).Homotopy (j.comp q),
        (∀ t, H (t,Y.point)=γ t) ∧ (∀ t x, H (t,j x)=j x) ∧
        (∀ t y, q (H (t,y))=q y)
  let Pack (n : ℕ) := Σ Y : BasedSpace.{u}, {q : C(Y,X.level n) //
    Y.IsWellBased ∧ q Y.point=(X.level n).point ∧ LocalData n Y q}
  have base_exists : Nonempty (Pack 0) := by
    let A : BasedSpace.{u} := ⟨TopCat.of PUnit.{u+1},PUnit.unit⟩
    have hA : A.IsWellBased := by
      refine ⟨isClosed_singleton,?_⟩
      intro Z f p hp
      refine ⟨⟨fun b : A × I => p b.2,p.continuous.comp continuous_snd⟩,?_,?_⟩
      · intro a
        exact hp.trans (congrArg f (Subsingleton.elim A.point a))
      · intro t
        rfl
    obtain ⟨Y,hY,i,q,j,γ,_,hqp,_,hqj,hγ0,hγ1,hqγ,H,hH,hj,hqH⟩ :=
      mappingCylinder_exists A (X.level 0) hA (ContinuousMap.const _ (X.level 0).point) rfl
    exact ⟨⟨Y,q,hY,hqp,j,γ,hqj,hγ0,hγ1,hqγ,H,hH,hj,hqH⟩⟩
  have desc (n : ℕ) (Y : BasedSpace.{u}) (q : C(Y,X.level n)) (hq : q Y.point=(X.level n).point) :
      ∃ b : C(Y.suspension,X.level (n+1)), b Y.suspension.point=(X.level (n+1)).point ∧
        ∀ y t, b (BasedSpace.suspensionProjection Y (y,t))=X.bond n (q y,t) := by
    let raw : C(Y × I,X.level (n+1)) :=
      ⟨fun p => X.bond n (q p.1,p.2),
        (X.bond n).continuous.comp ((q.continuous.comp continuous_fst).prodMk continuous_snd)⟩
    have collapsed (p : Y × I) (hp : BasedSpace.SuspensionCollapsed Y p) :
        raw p=(X.level (n+1)).point := by
      rcases hp with hp | hp | hp
      · change X.bond n (q p.1,p.2)=_
        rw [hp,hq,X.bond_point]
      · change X.bond n (q p.1,p.2)=_
        rw [hp,X.bond_zero]
      · change X.bond n (q p.1,p.2)=_
        rw [hp,X.bond_one]
    have respects : ∀ p r, BasedSpace.SuspensionRelation Y p r → raw p=raw r :=
      fun p r h => (collapsed p h.1).trans (collapsed r h.2).symm
    refine ⟨⟨Quot.lift raw respects,continuous_quot_lift respects raw.continuous⟩,?_,?_⟩
    · exact collapsed (Y.point,0) (Or.inl rfl)
    · intro y t
      rfl
  let bondSource (n : ℕ) (p : Pack n) := (desc n p.1 p.2.1 p.2.2.2.1).choose
  have bondSource_point (n : ℕ) (p : Pack n) :
      bondSource n p p.1.suspension.point=(X.level (n+1)).point :=
    (desc n p.1 p.2.1 p.2.2.2.1).choose_spec.1
  have bondSource_apply (n : ℕ) (p : Pack n) (y : p.1) (t : I) :
      bondSource n p (BasedSpace.suspensionProjection p.1 (y,t))=X.bond n (p.2.1 y,t) :=
    (desc n p.1 p.2.1 p.2.2.2.1).choose_spec.2 y t
  have step_exists (n : ℕ) (p : Pack n) :
      ∃ p' : Pack (n+1), ∃ i : C(p.1.suspension,p'.1),
        i p.1.suspension.point=p'.1.point ∧ p'.2.1.comp i=bondSource n p := by
    obtain ⟨Y,hY,i,q,j,γ,hip,hqp,hqi,hqj,hγ0,hγ1,hqγ,H,hH,hj,hqH⟩ :=
      mappingCylinder_exists p.1.suspension (X.level (n+1))
        (BasedSpace.suspension_wellBased p.1 p.2.2.1) (bondSource n p) (bondSource_point n p)
    exact ⟨⟨Y,q,hY,hqp,j,γ,hqj,hγ0,hγ1,hqγ,H,hH,hj,hqH⟩,i,hip,hqi⟩
  let step (n : ℕ) (p : Pack n) : Pack (n+1) := (step_exists n p).choose
  let inclusion (n : ℕ) (p : Pack n) : C(p.1.suspension,(step n p).1) :=
    (step_exists n p).choose_spec.choose
  have inclusion_point (n : ℕ) (p : Pack n) :
      inclusion n p p.1.suspension.point=(step n p).1.point :=
    (step_exists n p).choose_spec.choose_spec.1
  have inclusion_comp (n : ℕ) (p : Pack n) :
      (step n p).2.1.comp (inclusion n p)=bondSource n p :=
    (step_exists n p).choose_spec.choose_spec.2
  let stages : ∀ n, Pack n := Nat.rec base_exists.some step
  let Y : Prespectrum.{u} :=
    { level n := (stages n).1
      bond n := (inclusion n (stages n)).comp (BasedSpace.suspensionProjection (stages n).1)
      bond_point n t := by
        change inclusion n (stages n) (BasedSpace.suspensionProjection _ (_,t))=_
        rw [BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)]
        exact inclusion_point n (stages n)
      bond_zero n y := by
        change inclusion n (stages n) (BasedSpace.suspensionProjection _ (y,0))=_
        rw [BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))]
        exact inclusion_point n (stages n)
      bond_one n y := by
        change inclusion n (stages n) (BasedSpace.suspensionProjection _ (y,1))=_
        rw [BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))]
        exact inclusion_point n (stages n) }
  let q : Y ⟶ X :=
    { level n := (stages n).2.1
      point n := (stages n).2.2.2.1
      bond n y t := by
        have h := congrArg (fun k : C((stages n).1.suspension,X.level (n+1)) =>
          k (BasedSpace.suspensionProjection (stages n).1 (y,t))) (inclusion_comp n (stages n))
        exact h.trans (bondSource_apply n (stages n) y t) }
  exact ⟨Y,(fun n => (stages n).2.2.1),q,(fun n => (stages n).2.2.2.2)⟩

/-- A point-set replacement obligation, not an additional condition on the
abstract stable category. Every prespectrum has a levelwise well-based model and
a map inducing the specified integer stable homotopy isomorphisms. -/
theorem wellBasedReplacement (X : Prespectrum.{u}) :
    ∃ (Y : Prespectrum.{u}) (_ : Y.IsWellBased) (q : Y ⟶ X),
      stableEquivalences q := by
  have stableEquivalence_of_levelwise_loops {X Y : Prespectrum.{u}} (f : X ⟶ Y)
      (hinj : ∀ n r (p q : GenLoop (Fin r) (X.level n) (X.level n).point),
        GenLoop.Homotopic
          (⟨(f.level n).comp p.val,fun t ht => (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩ :
            GenLoop (Fin r) (Y.level n) (Y.level n).point)
          ⟨(f.level n).comp q.val,fun t ht => (congrArg (f.level n) (q.property t ht)).trans (f.point n)⟩ →
        GenLoop.Homotopic p q)
      (hsurj : ∀ n r (p : GenLoop (Fin r) (Y.level n) (Y.level n).point),
        ∃ q : GenLoop (Fin r) (X.level n) (X.level n).point,
          GenLoop.Homotopic
            (⟨(f.level n).comp q.val,fun t ht => (congrArg (f.level n) (q.property t ht)).trans (f.point n)⟩ :
              GenLoop (Fin r) (Y.level n) (Y.level n).point) p) :
      stableEquivalences f := by
    have stabilizeLoop_homotopic (P : Prespectrum.{u}) (n r : ℕ)
        (p q : GenLoop (Fin r) (P.level n) (P.level n).point) (h : GenLoop.Homotopic p q) :
        GenLoop.Homotopic (stabilizeLoop P n r p) (stabilizeLoop P n r q) := by
      obtain ⟨H⟩ := h
      refine ⟨{ toFun := fun t => P.bond n (H (t.1,fun i => t.2 i.succ),t.2 0)
                continuous_toFun := (P.bond n).continuous.comp
                  ((H.continuous.comp (continuous_fst.prodMk
                    (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
                      ((continuous_apply 0).comp continuous_snd))
                map_zero_left := ?_
                map_one_left := ?_
                prop' := ?_ }⟩
      · intro t
        change P.bond n (H (0,_),_) = _
        rw [H.apply_zero]
        rfl
      · intro t
        change P.bond n (H (1,_),_) = _
        rw [H.apply_one]
        rfl
      · intro s t ht
        obtain ⟨i,hi⟩ := ht
        induction i using Fin.cases with
        | zero =>
          rcases hi with h | h
          · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
            rw [h,P.bond_zero,P.bond_zero]
          · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
            rw [h,P.bond_one,P.bond_one]
        | succ j =>
          change P.bond n (H (s,_),_) = P.bond n (p _,_)
          rw [H.eq_fst s ⟨j,hi⟩]
          rfl

    classical
    let F (n r : ℕ) (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
        GenLoop (Fin r) (Y.level n) (Y.level n).point :=
      ⟨(f.level n).comp p.val,fun t ht => (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩
    choose L hL using hsurj
    have hnext (n r : ℕ) (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
        F (n+1) (r+1) (stabilizeLoop X n r p)=stabilizeLoop Y n r (F n r p) := by
      apply GenLoop.ext
      intro t
      exact f.bond n _ _
    intro d
    let R (a : Representative Y d) : Representative X d :=
      ⟨a.stage,a.dimension,a.degree,L a.stage a.dimension a.loop⟩
    have respects : ∀ a b, StableRelation Y d a b → Quot.mk (StableRelation X d) (R a)=Quot.mk _ (R b) := by
      intro a b hab
      cases hab with
      | homotopy p hp =>
        apply Quot.sound
        apply StableRelation.homotopy (R a)
        apply hinj
        exact (hL a.stage a.dimension a.loop).trans (hp.trans (hL a.stage a.dimension p).symm)
      | stabilization =>
        apply (Quot.sound (StableRelation.stabilization (R a))).trans
        have hh : GenLoop.Homotopic (stabilizeLoop X a.stage a.dimension (L _ _ a.loop))
            (L _ _ (stabilizeLoop Y a.stage a.dimension a.loop)) := by
          apply hinj
          change GenLoop.Homotopic (F _ _ (stabilizeLoop X _ _ (L _ _ a.loop))) _
          rw [hnext]
          exact (stabilizeLoop_homotopic Y _ _ _ _ (hL _ _ a.loop)).trans
            (hL _ _ (stabilizeLoop Y _ _ a.loop)).symm
        exact Quot.sound (StableRelation.homotopy (R a).next _ hh)
    let G : StableHomotopy Y d → StableHomotopy X d := Quot.lift (fun a => Quot.mk _ (R a)) respects
    have hGF : Function.LeftInverse G (stableHomotopyMap f d) := by
      intro a
      refine Quot.inductionOn a ?_
      intro a
      change Quot.mk _ (R (a.map f))=Quot.mk _ a
      have h : GenLoop.Homotopic (L a.stage a.dimension (F _ _ a.loop)) a.loop :=
        hinj _ _ _ _ (hL _ _ (F _ _ a.loop))
      exact Quot.sound (StableRelation.homotopy (R (a.map f)) _ h)
    have hFG : Function.RightInverse G (stableHomotopyMap f d) := by
      intro a
      refine Quot.inductionOn a ?_
      intro a
      change Quot.mk _ ((R a).map f)=Quot.mk _ a
      exact Quot.sound (StableRelation.homotopy ((R a).map f) _ (hL _ _ a.loop))
    exact ⟨hGF.injective,hFG.surjective⟩
  obtain ⟨Y,hY,q,hq⟩ := wellBased_replacement_with_deformation X
  refine ⟨Y,hY,q,stableEquivalence_of_levelwise_loops q ?_ ?_⟩
  · intro n r p p' hp
    obtain ⟨j,γ,hqj,hγ0,hγ1,hqγ,H,hH,_,_⟩ := hq n
    exact (BasedSpace.loops_equivalence_of_deformation
      (X.level n).point (Y.level n).point (q.level n) (q.point n) j hqj γ hγ0 hγ1 hqγ H hH).1 r p p' hp
  · intro n r p
    obtain ⟨j,γ,hqj,hγ0,hγ1,hqγ,H,hH,_,_⟩ := hq n
    exact (BasedSpace.loops_equivalence_of_deformation
      (X.level n).point (Y.level n).point (q.level n) (q.point n) j hqj γ hγ0 hγ1 hqγ H hH).2 r p

/-- Levelwise reduced suspension with the displayed interchange of the two
interval variables. This is not an independently selected shift operation. -/
def suspension (X : Prespectrum.{u}) : Prespectrum.{u} where
  level n := (X.level n).suspension
  bond n := ⟨BasedSpace.suspensionFamily _ _ (X.bond n) (X.bond_point n),
    BasedSpace.continuous_suspensionFamily _ _ (X.bond n) (X.bond_point n)⟩
  bond_point := by
    intro n t
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond_zero := by
    intro n x
    refine Quot.inductionOn x ?_
    intro p
    change BasedSpace.suspensionProjection _ (X.bond n (p.1,0),p.2) = _
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl (X.bond_zero n _))
  bond_one := by
    intro n x
    refine Quot.inductionOn x ?_
    intro p
    change BasedSpace.suspensionProjection _ (X.bond n (p.1,1),p.2) = _
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl (X.bond_one n _))

def suspensionMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) : X.suspension ⟶ Y.suspension where
  level n := BasedSpace.suspensionMap _ _ (f.level n) (f.point n)
  point := by
    intro n
    change BasedSpace.suspensionProjection _ (f.level n (X.level n).point,0) = _
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  bond := by
    intro n x t
    refine Quot.inductionOn x ?_
    intro p
    change BasedSpace.suspensionProjection _ (f.level (n+1) (X.bond n (p.1,t)),p.2) =
      BasedSpace.suspensionProjection _ (Y.bond n (f.level n p.1,t),p.2)
    rw [f.bond]

/-- The reduced mapping-cone quotient at one level. -/
inductive ConeRelation {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    Y.level n ⊕ (X.level n × I) → Y.level n ⊕ (X.level n × I) → Prop
  | start (x : X.level n) : ConeRelation f n (.inr (x,0)) (.inl (f.level n x))
  | finish (x : X.level n) : ConeRelation f n (.inr (x,1)) (.inl (Y.level n).point)
  | point (t : I) : ConeRelation f n (.inr ((X.level n).point,t)) (.inl (Y.level n).point)

def coneLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) : BasedSpace.{u} where
  space := TopCat.of (Quot (ConeRelation f n))
  point := Quot.mk _ (.inl (Y.level n).point)

def coneBondRepresentative {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (t : I) : Y.level n ⊕ (X.level n × I) → coneLevel f (n + 1)
  | .inl y => Quot.mk _ (.inl (Y.bond n (y,t)))
  | .inr (x,s) => Quot.mk _ (.inr (X.bond n (x,t),s))

theorem coneBondRepresentative_respects {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (t : I) (a b) (h : ConeRelation f n a b) :
    coneBondRepresentative f n t a = coneBondRepresentative f n t b := by
  cases h with
  | start x =>
    change Quot.mk (ConeRelation f (n+1)) (.inr (X.bond n (x,t),0)) =
      Quot.mk (ConeRelation f (n+1)) (.inl (Y.bond n (f.level n x,t)))
    rw [← f.bond]
    exact Quot.sound (ConeRelation.start _)
  | finish x =>
    change Quot.mk (ConeRelation f (n+1)) (.inr (X.bond n (x,t),1)) =
      Quot.mk (ConeRelation f (n+1)) (.inl (Y.bond n ((Y.level n).point,t)))
    rw [Y.bond_point]
    exact Quot.sound (ConeRelation.finish _)
  | point s =>
    change Quot.mk (ConeRelation f (n+1)) (.inr (X.bond n ((X.level n).point,t),s)) =
      Quot.mk (ConeRelation f (n+1)) (.inl (Y.bond n ((Y.level n).point,t)))
    rw [X.bond_point, Y.bond_point]
    exact Quot.sound (ConeRelation.point s)

def coneBond {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (p : coneLevel f n × I) : coneLevel f (n + 1) :=
  Quot.lift (coneBondRepresentative f n p.2)
    (coneBondRepresentative_respects f n p.2) p.1

theorem continuous_coneBond {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    Continuous (coneBond f n) := by
  apply isQuotientMap_quot_mk.continuous_lift_prod_left
  have hleft : Continuous (fun p : Y.level n × I =>
      Quot.mk (ConeRelation f (n+1)) (.inl (Y.bond n p))) :=
    continuous_quot_mk.comp (continuous_inl.comp (Y.bond n).continuous)
  have hright : Continuous (fun p : (X.level n × I) × I =>
      Quot.mk (ConeRelation f (n+1)) (.inr (X.bond n (p.1.1,p.2),p.1.2))) :=
    continuous_quot_mk.comp (continuous_inr.comp
      (((X.bond n).continuous.comp (continuous_fst.fst.prodMk continuous_snd)).prodMk
        continuous_fst.snd))
  have hcont := (hleft.sumElim hright).comp
    (Homeomorph.sumProdDistrib (X := Y.level n) (Y := X.level n × I) (Z := I)).continuous
  apply hcont.congr
  rintro ⟨p,t⟩
  cases p <;> rfl

def cone {X Y : Prespectrum.{u}} (f : X ⟶ Y) : Prespectrum.{u} where
  level := coneLevel f
  bond n := ⟨coneBond f n, continuous_coneBond f n⟩
  bond_point := by intro n t; change Quot.mk (ConeRelation f (n+1)) (Sum.inl (Y.bond n (_,t))) = _; rw [Y.bond_point]; rfl
  bond_zero := by
    intro n x
    refine Quot.inductionOn x ?_
    rintro (y | ⟨x,t⟩)
    · change Quot.mk (ConeRelation f (n+1)) (Sum.inl (Y.bond n (y,0))) = _
      rw [Y.bond_zero]; rfl
    · change Quot.mk (ConeRelation f (n+1)) (Sum.inr (X.bond n (x,0),t)) = _
      rw [X.bond_zero]
      exact Quot.sound (ConeRelation.point t)
  bond_one := by
    intro n x
    refine Quot.inductionOn x ?_
    rintro (y | ⟨x,t⟩)
    · change Quot.mk (ConeRelation f (n+1)) (Sum.inl (Y.bond n (y,1))) = _
      rw [Y.bond_one]; rfl
    · change Quot.mk (ConeRelation f (n+1)) (Sum.inr (X.bond n (x,1),t)) = _
      rw [X.bond_one]
      exact Quot.sound (ConeRelation.point t)

def coneInclusion {X Y : Prespectrum.{u}} (f : X ⟶ Y) : Y ⟶ cone f where
  level _n := ⟨fun y => Quot.mk _ (.inl y), continuous_quot_mk.comp continuous_inl⟩
  point := fun _ => rfl
  bond := fun _ _ _ => rfl

-- Retain the named hypotheses in the statement of this theorem.
set_option linter.unusedVariables false in
def coneBoundaryRepresentative {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    Y.level n ⊕ (X.level n × I) → (X.level n).suspension
  | .inl _ => (X.level n).suspension.point
  | .inr p => BasedSpace.suspensionProjection _ p

theorem coneBoundaryRepresentative_respects {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (a b) (h : ConeRelation f n a b) :
    coneBoundaryRepresentative f n a = coneBoundaryRepresentative f n b := by
  cases h with
  | start x =>
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))
  | finish x =>
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inr rfl))
  | point t =>
    exact BasedSpace.suspensionProjection_collapsed _ _ (Or.inl rfl)

def coneBoundaryLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    coneLevel f n → (X.level n).suspension :=
  Quot.lift (coneBoundaryRepresentative f n) (coneBoundaryRepresentative_respects f n)

theorem continuous_coneBoundaryLevel {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    Continuous (coneBoundaryLevel f n) := by
  exact continuous_quot_lift _ (continuous_sum_dom.mpr
    ⟨continuous_const, (BasedSpace.suspensionProjection (X.level n)).continuous⟩)

def coneBoundary {X Y : Prespectrum.{u}} (f : X ⟶ Y) : cone f ⟶ X.suspension where
  level n := ⟨coneBoundaryLevel f n, continuous_coneBoundaryLevel f n⟩
  point := fun _ => rfl
  bond := by
    intro n x t
    refine Quot.inductionOn x ?_
    rintro (y | ⟨x,s⟩)
    · change (X.level (n+1)).suspension.point =
        BasedSpace.suspensionProjection _ (X.bond n ((X.level n).point,t),0)
      exact (BasedSpace.suspensionProjection_collapsed _ _ (Or.inr (Or.inl rfl))).symm
    · rfl

end Prespectrum

end KIP126.StableHomotopy.Spectra
