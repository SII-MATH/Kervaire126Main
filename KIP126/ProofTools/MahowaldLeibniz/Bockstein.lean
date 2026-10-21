module

import all KIP126.ProofTools.GeneralizedLeibniz.Reverse
import all KIP126.ProofTools.GeneralizedMahowald.BoundaryDetection
import all KIP126.ProofTools.GeneralizedMahowald.ClassicalLift

/-! Specified-label finite Bockstein comparison in the selected model.
The lift and both of its labels are constructed from the given classical
differential; the reverse implication applies to that same lift.
All declarations are internal, and no new model premise is introduced. -/

@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.ProofTools.Internal.Mahowald KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

/-- The native first-quotient label, with the selected zero-shift comparison
removed. This is an actual sphere map, not a freely chosen E₂ operation. -/
private def nativeFirstLabel (X : ClassicalObject) (s t : ℤ)
    (x : Ambient model X (s,t)) :
    BiHom (t-s) t (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) :=
  firstLabel model X s t x ≫
    XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1

/-- The first-quotient label of the actual absolute boundary of a finite
lift, in the exact bidegree of its adjacent classical differential. -/
private def adjacentBoundaryLabel (X : ClassicalObject) (q : ℕ) (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    BiHom ((t+q)-(s+q+1)) (t+q)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) :=
  boundaryRepresentative X q s t a ≫ XModLambdaN.incl _ 1

/-- The selected adjacent finite-quotient boundary, with its ordinary
suspension and weight shift transported by the fixed comparison. -/
private def adjacentFiniteBoundary (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    BiHom ((t+q)-(s+q+1)) (t+q)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let δ : XModLambdaN A q ⟶
      ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧ := by
    simpa only [show q+1-q=1 by omega] using
      ((model.quotients.tower A).triangle hq (Nat.lt_succ_self q)).delta
  exact homotopyRegrade (by omega) rfl
    (biSuspensionHomEquiv (t-s) t q (XModLambdaN A 1) (a ≫ δ))

/-- The actual adjacent finite boundary agrees with the projected absolute
boundary on every specified lift; no choice of target label is involved. -/
private theorem adjacentFiniteBoundary_eq (X : ClassicalObject) (q : ℕ) (hq : 0 < q)
    (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q)) :
    adjacentFiniteBoundary X q hq s t a = adjacentBoundaryLabel X q s t a := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have h := cofiber_boundary_projection X q (q+1) hq (Nat.lt_succ_self q) (t-s) t a
  have transport (n : ℕ) (hn : n=1)
      (δ : XModLambdaN A q ⟶
        ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (he : (XModLambdaN A q ⟶
          ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧) =
        (XModLambdaN A q ⟶
          ((SyntheticCategory.biShift (0,-(q:ℤ))).obj (XModLambdaN A 1))⟦(1:ℤ)⟧))
      (hd : biSuspensionHomEquiv (t-s) t q (XModLambdaN A n) (a ≫ δ) =
        biSuspensionHomEquiv (t-s) t q A (a ≫ XModLambdaN.proj A q) ≫
          XModLambdaN.incl A n) :
      biSuspensionHomEquiv (t-s) t q (XModLambdaN A 1) (a ≫ he.mp δ) =
        biSuspensionHomEquiv (t-s) t q A (a ≫ XModLambdaN.proj A q) ≫
          XModLambdaN.incl A 1 := by
    subst n
    exact hd
  have hp := transport (q+1-q) (by omega) _ (by rw [show q+1-q=1 by omega]) h
  have hc := congrArg (homotopyRegrade (show t-s-1=(t+q)-(s+q+1) by omega) rfl) hp
  simpa only [adjacentFiniteBoundary,adjacentBoundaryLabel,boundaryRepresentative,
    regrade_precomp,Category.assoc] using hc

/-- A given classical differential is equivalent to the existence of one
finite lift with the specified source and target labels. The specified target
is retained exactly in Q₁, even when it is an earlier boundary. -/
private theorem differential_iff_specified_adjacent_lift
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+q+1,t+q)) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
        (q+1) (s,t) (s+q+1,t+q) x y ↔
      ∃ a : BiHom (t-s) t
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
        a ≫ (model.quotients.tower _).rho 1 q hq = nativeFirstLabel X s t x ∧
        adjacentBoundaryLabel X q s t a = nativeFirstLabel X (s+q+1) (t+q) y := by
  constructor
  · intro hd
    obtain ⟨a,ha,hy⟩ := adjacent_absolute_boundary X q hq s t x y hd
    exact ⟨a,ha,hy⟩
  · rintro ⟨a,ha,hy⟩
    exact adjacent_boundary_differential X q hq s t x y a ha hy

/-- The complete adjacent finite-quotient Bockstein comparison, using the
actual finite delta map and both specified Q₁ labels. -/
private theorem differential_iff_specified_finite_lift
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+q+1,t+q)) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
        (q+1) (s,t) (s+q+1,t+q) x y ↔
      ∃ a : BiHom (t-s) t
          (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q),
        a ≫ (model.quotients.tower _).rho 1 q hq = nativeFirstLabel X s t x ∧
        adjacentFiniteBoundary X q hq s t a = nativeFirstLabel X (s+q+1) (t+q) y := by
  simp only [adjacentFiniteBoundary_eq]
  exact differential_iff_specified_adjacent_lift X q hq s t x y

/-- The same witness supplies the required cycle qualification; it is a
consequence of the actual lift rather than an extra input to the producer. -/
private theorem specified_adjacent_lift_cycles
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t))
    (a : BiHom (t-s) t
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (ha : a ≫ (model.quotients.tower _).rho 1 q hq = nativeFirstLabel X s t x) :
    IsCycle model X q (s,t) x := by
  exact ⟨by omega, first_label_lift_cycles X q hq s t x a ha⟩

/-- At the last finite layer, an actual representative with the specified
label vanishes precisely when that label belongs to B_q. This retains the
last denominator and does not use target permanence as an assumption. -/
private theorem finite_top_detected_zero_iff_boundary
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (y : Ambient model X (s,t))
    (b : BiHom (t-s) (t-(q-1:ℕ))
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hb : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-(q-1:ℕ))
      (finiteTargetLabel model X q s t (q-1) y) b) :
    b = 0 ↔ y ∈ boundaries model X q (s,t) := by
  have hycycle : IsCycle model X 1 (s,t) y := by
    exact (isCycle_iff_reaches model X 2 (by decide) (s,t) y).mpr
      ⟨y,represents_two_self y⟩
  let yc : cycles model X ((q:ℤ)-t+(t-(q-1:ℕ))) (s,t) := ⟨y,by
    have hi : (q:ℤ)-t+(t-(q-1:ℕ)) = 1 := by omega
    rw [hi]
    exact hycycle.2⟩
  constructor
  · intro hz
    have hb0 : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-(q-1:ℕ))
        (finiteTargetLabel model X q s t (q-1) y) 0 := by simpa only [hz] using hb
    have he := detected_zero_infinity (.quotient q (.nu X)) (s,t,t-(q-1:ℕ)) _ hb0
    have hw := (finite_target_label_iff X q hq s t (q-1) (by omega) yc 0).mp he
    rw [map_zero] at hw
    have hmem := (CrossingLabels.subquotient_zero_iff _ _ yc).mp hw.symm
    have hi : 1+t-(t-(q-1:ℕ)) = (q:ℤ) := by omega
    simpa only [hi] using hmem
  · intro hy
    exact finite_top_detection_unique X q hq s t (t-(q-1:ℕ)) (by omega)
      _ b 0 hb (finite_top_boundary_detects_zero X q hq s t y hy)

/-- Equality of two specified highest-layer representatives is precisely
congruence of their classical labels modulo B_q. -/
private theorem finite_top_detected_eq_iff_boundary
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (y z : Ambient model X (s,t))
    (b c : BiHom (t-s) (t-(q-1:ℕ))
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hb : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-(q-1:ℕ))
      (finiteTargetLabel model X q s t (q-1) y) b)
    (hc : Detects (model.convergence (.quotient q (.nu X))) (s,t,t-(q-1:ℕ))
      (finiteTargetLabel model X q s t (q-1) z) c) :
    b = c ↔ y-z ∈ boundaries model X q (s,t) := by
  have hsub := detects_sub (.quotient q (.nu X)) (s,t,t-(q-1:ℕ)) hb hc
  rw [←finiteTargetLabel_sub] at hsub
  exact sub_eq_zero.symm.trans
    (finite_top_detected_zero_iff_boundary X q hq s t (y-z) (b-c) hsub)

/-- The exact terminal boundary comparison preserves the specified output
of an adjacent classical differential. -/
private theorem differential_of_equal_top_representatives
    (X : ClassicalObject) (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (x : Ambient model X (s,t)) (y z : Ambient model X (s+q+1,t+q))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) x z)
    (b c : BiHom ((t+q)-(s+q+1)) ((t+q)-(q-1:ℕ))
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) q))
    (hb : Detects (model.convergence (.quotient q (.nu X)))
      (s+q+1,t+q,(t+q)-(q-1:ℕ))
      (finiteTargetLabel model X q (s+q+1) (t+q) (q-1) y) b)
    (hc : Detects (model.convergence (.quotient q (.nu X)))
      (s+q+1,t+q,(t+q)-(q-1:ℕ))
      (finiteTargetLabel model X q (s+q+1) (t+q) (q-1) z) c)
    (heq : b=c) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (q+1) (s,t) (s+q+1,t+q) x y := by
  have hcong := (finite_top_detected_eq_iff_boundary X q hq
    (s+q+1) (t+q) y z b c hb hc).mp heq
  exact (differentialAt_of_congruent model X
    (⟨by omega,hd⟩ : DifferentialAt model X (q+1) (s,t) (s+q+1,t+q) x z)
    ⟨by omega,by simpa only [add_sub_cancel_right] using hcong⟩).2

/-- In the retained finite window, detection of the projection of an actual
full class reflects to detection of that same full class. Permanence of the
specified label is derived from its actual full lift. -/
private theorem finite_projection_detects_reflect
    (X : ClassicalObject) (N : ℕ) (hN : 0 < N) (s t w : ℤ)
    (hw : 0 ≤ t-w ∧ t-w < N) (y : Ambient model X (s,t))
    (β : BiHom (t-s) w (model.nu.functor.obj (X.obj model.auxiliary)))
    (hfinite : Detects (model.convergence (.quotient N (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w (by omega) y))
      (β ≫ XModLambdaN.incl _ N)) :
    Detects (model.convergence (.nu X)) (s,t,w)
      (nuWeightLabel model X s t w (by omega) y) β := by
  have hp := KIP126.ProofTools.finite_target_from_full_lift_is_permanent
    X N hN s t w hw y β hfinite
  have hfull := KIP126.ProofTools.full_projection_reflects_filtration
    X N hN s (t-s) w (by omega) β
    (detects_filtration (.quotient N (.nu X)) (s,t,w) _ _ hfinite)
  let e := (KIP126.Literature.Standard.infinityNuWindow X (s,t) w (by omega)).symm
    (subquotientClass (permanentCycles model X (s,t))
      (boundaries model X (1+t-w) (s,t)) ⟨y,hp⟩)
  have he : HasInfinityRepresentative _ 2 (s,t,w)
      (nuWeightLabel model X s t w (by omega) y) e := by
    apply (KIP126.Literature.Standard.eInfinity_nu_labels X s t w (by omega) y e).mpr
    exact ⟨hp,(KIP126.Literature.Standard.infinityNuWindow X (s,t) w (by omega)).apply_symm_apply _⟩
  exact detects_reflect (.nu X) (.quotient N (.nu X)) (XModLambdaN.incl _ N)
    (s,t,w) (KIP126.ProofTools.Internal.Leibniz.nu_projection_infinity_injective
      X N hN s t w hw) _ e he β hfull hfinite

/-- Finite detection of the actual absolute boundary is enough to recover
the specified classical differential. The finite window condition retains
the exact boundary denominator; no full synthetic detection is assumed. -/
private theorem finite_boundary_detects_differential
    (X : ClassicalObject) (i k N : ℕ) (hi : 0 < i) (hik : i ≤ k)
    (hN : 0 < N) (hwindow : k-i < N) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (a : BiHom (t-s) t
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : a ≫ (model.quotients.tower _).rho 1 i hi = nativeFirstLabel X s t x)
    (hy : Detects (model.convergence (.quotient N (.nu X))) (s+k+1,t+k,t+i)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s+k+1,t+k,t+i)
        (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) y))
      ((homotopyRegrade (by dsimp; omega) rfl
        (biSuspensionHomEquiv (t-s) t i (model.nu.functor.obj (X.obj model.auxiliary))
          (a ≫ XModLambdaN.proj _ i))) ≫ XModLambdaN.incl _ N)) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  exact boundary_detects_differential X i k hi hik s t x y a ha
    (finite_projection_detects_reflect X N hN (s+k+1) (t+k) (t+i)
      (by omega) y _ hy)


/-- The actual boundary of the finite tower triangle Qi → Q(i+N), in
unsuspended sphere coordinates. -/
private def finiteTowerBoundary (X : ClassicalObject) (i N : ℕ)
    (hi : 0 < i) (hN : 0 < N) (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i)) :
    BiHom (t-s-1) (t+i)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) N) := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  let δ : XModLambdaN A i ⟶
      ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A N))⟦(1:ℤ)⟧ := by
    simpa only [show i+N-i=N by omega] using
      ((model.quotients.tower A).triangle hi (show i < i + N by omega)).delta
  exact biSuspensionHomEquiv (t-s) t i (XModLambdaN A N) (a ≫ δ)

/-- The chosen finite delta equals the actual absolute boundary followed
by the chosen projection to the complementary finite quotient. -/
private theorem finiteTowerBoundary_eq (X : ClassicalObject) (i N : ℕ)
    (hi : 0 < i) (hN : 0 < N) (s t : ℤ)
    (a : BiHom (t-s) t
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i)) :
    finiteTowerBoundary X i N hi hN s t a =
      biSuspensionHomEquiv (t-s) t i (model.nu.functor.obj (X.obj model.auxiliary))
        (a ≫ XModLambdaN.proj _ i) ≫ XModLambdaN.incl _ N := by
  let A := model.nu.functor.obj (X.obj model.auxiliary)
  have h := cofiber_boundary_projection X i (i+N) hi (by omega) (t-s) t a
  have transport (n : ℕ) (hn : n=N)
      (δ : XModLambdaN A i ⟶
        ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧)
      (he : (XModLambdaN A i ⟶
          ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A n))⟦(1:ℤ)⟧) =
        (XModLambdaN A i ⟶
          ((SyntheticCategory.biShift (0,-(i:ℤ))).obj (XModLambdaN A N))⟦(1:ℤ)⟧))
      (hd : biSuspensionHomEquiv (t-s) t i (XModLambdaN A n) (a ≫ δ) =
        biSuspensionHomEquiv (t-s) t i A (a ≫ XModLambdaN.proj A i) ≫
          XModLambdaN.incl A n) :
      biSuspensionHomEquiv (t-s) t i (XModLambdaN A N) (a ≫ he.mp δ) =
        biSuspensionHomEquiv (t-s) t i A (a ≫ XModLambdaN.proj A i) ≫
          XModLambdaN.incl A N := by
    subst n
    exact hd
  exact transport (i+N-i) (by omega) _ (by rw [show i+N-i=N by omega]) h

/-- The finite tower Bockstein detects the specified classical target if
and only if its projected absolute boundary does. Hence its actual leading
term already implies the classical differential. -/
private theorem finiteTowerBoundary_detects_differential
    (X : ClassicalObject) (i k N : ℕ) (hi : 0 < i) (hik : i ≤ k)
    (hN : 0 < N) (hwindow : k-i < N) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (a : BiHom (t-s) t
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) i))
    (ha : a ≫ (model.quotients.tower _).rho 1 i hi = nativeFirstLabel X s t x)
    (hy : Detects (model.convergence (.quotient N (.nu X))) (s+k+1,t+k,t+i)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s+k+1,t+k,t+i)
        (nuWeightLabel model X (s+k+1) (t+k) (t+i) (by omega) y))
      (homotopyRegrade (by dsimp; omega) rfl
        (finiteTowerBoundary X i N hi hN s t a))) :
    HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y := by
  apply finite_boundary_detects_differential X i k N hi hik hN hwindow s t x y a ha
  simpa only [finiteTowerBoundary_eq,regrade_precomp,Category.assoc] using hy

/-- Complete terminal decoder. The equality δ₁,ₚ₊₁(x)=b, with b carrying
the specified highest-layer label y, forces both x∈Zp and dₚ₊₁x=y. The
nontrivial highest-layer denominator is Bp, as proved above. -/
private theorem finite_bockstein_terminal_decode
    (X : ClassicalObject) (p : ℕ) (hp : 0 < p) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+p+1,t+p))
    (b : BiHom ((t+p)-(s+p+1)) (t+(1:ℕ))
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) p))
    (hb : Detects (model.convergence (.quotient p (.nu X))) (s+p+1,t+p,t+(1:ℕ))
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) p).pageMap
        2 (s+p+1,t+p,t+(1:ℕ))
        (nuWeightLabel model X (s+p+1) (t+p) (t+(1:ℕ)) (by omega) y)) b)
    (heq : homotopyRegrade (by omega) rfl
      (finiteTowerBoundary X 1 p (by decide) hp s t (nativeFirstLabel X s t x)) = b) :
    IsCycle model X p (s,t) x ∧
      HasDifferential (model.classical.obj (X.obj model.auxiliary))
        (p+1) (s,t) (s+p+1,t+p) x y := by
  have hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (p+1) (s,t) (s+p+1,t+p) x y := by
    apply finiteTowerBoundary_detects_differential X 1 p p (by decide) (by omega)
      hp (by omega) s t x y (nativeFirstLabel X s t x)
    · simp only [(model.quotients.tower _).rho_id,Category.comp_id]
    · simpa only [heq] using hb
  refine ⟨?_,hd⟩
  obtain ⟨_,a,_,ha,_,_⟩ := hd
  have hx := (isCycle_iff_reaches model X (p+1) (by omega) (s,t) x).mpr ⟨a,ha⟩
  simpa only [add_sub_cancel_right] using hx


/-- The first classical input produces the actual finite connecting
representative with its specified target label. For d_R x=u, take k=R−1;
the resulting weight difference is R−2. The target's permanence is proved
from its adjacent Bockstein lift, rather than requested as input. -/
private theorem differential_detects_first_finite_boundary
    (X : ClassicalObject) (k N : ℕ) (hk : 0 < k) (hN : 0 < N) (s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model X (s+k+1,t+k))
    (hd : HasDifferential (model.classical.obj (X.obj model.auxiliary))
      (k+1) (s,t) (s+k+1,t+k) x y) :
    Detects (model.convergence (.quotient N (.nu X))) (s+k+1,t+k,t+(1:ℕ))
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
        2 (s+k+1,t+k,t+(1:ℕ))
        (nuWeightLabel model X (s+k+1) (t+k) (t+(1:ℕ)) (by omega) y))
      (homotopyRegrade (by dsimp; omega) rfl
        (finiteTowerBoundary X 1 N (by decide) hN s t (nativeFirstLabel X s t x))) := by
  obtain ⟨a,_,hay⟩ := adjacent_absolute_boundary X k hk s t x y hd
  have hy := first_label_lift_permanent X (s+k+1) (t+k) y
    (boundaryRepresentative X k s t a) hay
  obtain ⟨b,hb,hbd⟩ := differential_absolute_boundary X 1 k (by decide) (by omega)
    s t x y hd hy
  have hb' : b = nativeFirstLabel X s t x := by
    simpa only [nativeFirstLabel,(model.quotients.tower _).rho_id,Category.comp_id] using hb
  have hf := detects_map (.nu X) (.quotient N (.nu X)) (XModLambdaN.incl _ N)
    (s+k+1,t+k,t+(1:ℕ)) _ _ hbd
  change Detects (model.convergence (.quotient N (.nu X))) (s+k+1,t+k,t+(1:ℕ))
    ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) N).pageMap
      2 (s+k+1,t+k,t+(1:ℕ))
      (nuWeightLabel model X (s+k+1) (t+k) (t+(1:ℕ)) (by omega) y))
    ((homotopyRegrade (by dsimp; omega) rfl
      (biSuspensionHomEquiv (t-s) t (1:ℕ) (model.nu.functor.obj (X.obj model.auxiliary))
        (b ≫ XModLambdaN.proj _ 1))) ≫ XModLambdaN.incl _ N) at hf
  simpa only [finiteTowerBoundary_eq,regrade_precomp,Category.assoc,hb'] using hf

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
