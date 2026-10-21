module

import all KIP126.ProofTools.GeneralizedMahowald.CommonEdgeLabels
import all KIP126.ProofTools.MahowaldLeibniz.PositiveBranches
import all KIP126.ProofTools.MahowaldLeibniz.PositiveHBranch
import all KIP126.ProofTools.MahowaldLeibniz.MayTarget
import all KIP126.ProofTools.MahowaldLeibniz.ClassicalStatements
import all KIP126.ProofTools.MahowaldLeibniz.TerminalOrdinary
import all KIP126.ProofTools.MahowaldLeibniz.PositiveGCore
import all KIP126.ProofTools.MahowaldLeibniz.OrdinaryImageSquare

/-! The positive second-exponent classical NC corollary, assembled from
actual finite quotient representatives and the ordinary first-arrow criterion. -/
@[expose] section
namespace KIP126.ProofTools.Internal.MahowaldLeibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000

private theorem positive_g_regrade_self {A : SyntheticSpectrum} {m w : ℤ}
    (hm : m=m) (hw : w=w) (a : BiHom m w A) : homotopyRegrade hm hw a=a := by rfl

private theorem finite_may_signed_target_at_level_coordinates
    (X : ClassicalObject) (c q : ℕ) (hq : 0<q) (s t S V m w : ℤ)
    (hS : S=s+q+1) (hV : V=t+q) (hm : m=t-s) (hw : w=t)
    (v : Ambient model X (S,V))
    (en : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (q+1) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q+1))⟦(1:ℤ)⟧)
    (eN : XModLambdaN ((model.nu.functor.obj (X.obj model.auxiliary))⟦(1:ℤ)⟧) (c+(q+1)) ≅
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1)))⟦(1:ℤ)⟧)
    (hen : XModLambdaN.incl _ (q+1)≫en.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (q+1)))
    (heN : XModLambdaN.incl _ (c+(q+1))≫eN.hom=
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ (c+(q+1)))) :
    let b := (biSuspensionHomEquiv m w (q:ℤ)
      (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1)).symm
        (homotopyRegrade (show V-S=m-1 by omega) (show V=w+q by omega)
          (nativeFirstLabel X S V v))
    let ly : (SyntheticCategory.biShift (0,-(q:ℤ))).obj
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) 1) ⟶
        XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q+1) := by
      simpa only [show q.succ-q=1 by omega] using
        ((model.quotients.tower _).triangle hq (Nat.lt_succ_self q)).lambdaMap
    ∃ bN : BiHom (m-1) (w-c)
        (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1))),
      Detects (model.convergence (.quotient (c+(q+1)) (.nu X))) (S,V,w-c)
        ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (c+(q+1))).pageMap
          2 (S,V,w-c) (nuWeightLabel model X S V (w-c) (by omega) v))
        (homotopyRegrade (by dsimp; omega) rfl bN) ∧
      finiteCoefficientInsert _ c (q+1) (by omega) m w
        ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map ly))≫en.inv)≫eN.hom =
      ordinarySuspendedRepresentative _ m (w-c) bN := by
  subst S V m w
  exact finite_may_signed_target_at_level X c q hq s t v en eN hen heN


private theorem normalized_second_positive_map_eq
    (T : TriangleData model.auxiliary)
    (hg : normalizedExponent model.classicalTower T.g=1) :
    normalizedSecondPositiveMap T hg = normalizedClassicalPositiveMap T.Y T.Z T.g hg := by
  have cast {A B : SyntheticSpectrum} (k : ℕ) (hk : k=1)
      (M : (SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B)
      (h : ((SyntheticCategory.biShift (0,(k:ℤ))).obj A ⟶ B) =
        ((SyntheticCategory.biShift (0,1)).obj A ⟶ B)) :
      eqToHom (congrArg (fun j : ℕ => (SyntheticCategory.biShift (0,(j:ℤ))).obj A) hk.symm) ≫ M =
        h.mp M := by
    subst k
    simp only [eqToHom_refl,Category.id_comp]
    rfl
  unfold normalizedSecondPositiveMap normalizedClassicalPositiveMap
  exact cast _ hg _ _

private theorem ordinary_boundary_image_decode_coordinates
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (p : ℕ) (hp : 0<p) (s t S V m w : ℤ)
    (hS : S=s+p+1) (hV : V=t+p) (hm : m=t-s) (hw : w=t+1)
    (x : Ambient model T.X (s,t)) (v : Ambient model T.Y (S,V))
    (ex : XModLambdaN ((model.nu.functor.obj (T.X.obj model.auxiliary))⟦(1:ℤ)⟧) p ≅
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) p)⟦(1:ℤ)⟧)
    (ey : XModLambdaN ((model.nu.functor.obj (T.Y.obj model.auxiliary))⟦(1:ℤ)⟧) p ≅
      (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) p)⟦(1:ℤ)⟧)
    (hex : XModLambdaN.incl _ p ≫ ex.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ p))
    (hey : XModLambdaN.incl _ p ≫ ey.hom =
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl _ p))
    (b : BiHom (m-1) w (XModLambdaN (model.nu.functor.obj (T.Y.obj model.auxiliary)) p))
    (hb : Detects (model.convergence (.quotient p (.nu T.Y))) (S,V,w)
      ((model.family.quotientProjection (model.nu.functor.obj (T.Y.obj model.auxiliary)) p).pageMap
        2 (S,V,w) (nuWeightLabel model T.Y S V w (by omega) v))
      (homotopyRegrade (by dsimp; omega) rfl b))
    (himage : ordinaryNormalizedFirstFiniteBoundary T he hf p hp s t ex x ≫
      XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (normalizedTriangle model T he).mor₁) p ≫ ey.hom =
      homotopyRegrade hm hw (ordinarySuspendedRepresentative _ m w b)) :
    let y := (model.classical.map T.f).pageMap 2 (s,t) x
    IsCycle model T.Y p (s,t) y ∧ DifferentialAt model T.Y (p+1) (s,t) (S,V) y v := by
  subst S V m w
  exact ordinary_normalized_boundary_image_decode T he hf p hp s t x v ex ey hex hey b hb himage


private theorem positive_g_pdf_classical_corollary
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=1)
    (hh : normalizedExponent model.classicalTower T.h=0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (u : Ambient model T.X ((s+(c+1))+1,t+(c+1)))
    (z : Ambient model T.Z ((s+(c+1))+1,(t+(c+1))+1))
    (v : Ambient model T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : (model.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
      ((model.classical.map T.h).pageMap 2 ((s+(c+1))+1,(t+(c+1))+1) z) (by simpa using u))
    (hdx : HasDifferential (model.classical.obj (T.X.obj model.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u)
    (hdz : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) ((s+(c+1))+1,(t+(c+1))+1)
      (((s+(c+1))+q+1)+1,((t+(c+1))+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+(c+1))+q+1) ((t+(c+1))+q) v))
    (hNC1 : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      cycles model T.X (((q+1:ℕ):ℤ)-j)
        ((s+(c+1))+1+j,(t+(c+1))+j) ≤
      boundaries model T.X ((c:ℤ)+j+1)
        ((s+(c+1))+1+j,(t+(c+1))+j))
    (hNC2 : ∀ a : Ambient model T.X
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1),
      (model.classical.map T.f).pageMap 2
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1) a ∈
      boundaries model T.Y (c+(q+1))
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1)) :
    let y := (model.classical.map T.f).pageMap 2 (s,t) x
    IsCycle model T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt model T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  let N := c+(q+1)
  have hN : 0<N := by dsimp [N]; omega
  let B := s+(c+1)
  let W := t+(c+1)
  obtain ⟨ex,hex⟩ := quotient_suspension_inclusion_exists
    (model.nu.functor.obj (T.X.obj model.auxiliary)) N
  obtain ⟨ey,hey⟩ := quotient_suspension_inclusion_exists
    (model.nu.functor.obj (T.Y.obj model.auxiliary)) (q+1)
  obtain ⟨eY,heY⟩ := quotient_suspension_inclusion_exists
    (model.nu.functor.obj (T.Y.obj model.auxiliary)) N
  letI := model.exactness.shiftCommShift (1,0)
  letI := model.exactness.shiftExact (1,0)
  obtain ⟨ε,hε,_⟩ := quotient_shift_exists model.quotients.coherence (1,0) N
    (model.nu.functor.obj (T.X.obj model.auxiliary))
  let d := homotopyRegrade (show t-s=W-B by dsimp [B,W]; omega)
    (show t+1=W-c by dsimp [W]; omega)
    (ordinaryNormalizedFirstFiniteBoundary T he hf N hN s t ex x)
  have hd := ordinary_first_finite_boundary_source_detects T he hf (c+1) N c
    (by omega) hN (by omega) s t x u hdx ex hex ε hε
  obtain ⟨_,a,ha,hi,hall⟩ := positive_second_finite_core T he hT hf hg hh
    c q hq B W z u v hu hdz ey hey ε hε
  have hkill : ∀ b : BiHom (W-(B+1)) (W-c)
      (XModLambdaN (model.nu.functor.obj (T.X.obj model.auxiliary)) N),
      FiltrationAtLeast model.syntheticTower (B+2) b →
        b ≫ XModLambdaN.map (model.nu.functor.map T.f) N=0 := by
    intro b hb
    exact ordinary_map_pdf_annihilation T.X T.Y T.f c (q+1) (by omega)
      (B+1) W hNC1 hNC2 b (by simpa only [add_assoc,show (1:ℤ)+1=2 by norm_num] using hb)
  have himage := hall hkill d hd
  obtain ⟨b,hb,hbimage⟩ := finite_may_signed_target_at_level T.Y c q hq B W
    v ey eY hey heY
  apply ordinary_boundary_image_decode_coordinates T he hf N hN s t (B+q+1) (W+q)
    (W-B) (W-c) (by dsimp [B,N]; omega) (by dsimp [W,N]; omega)
    (by dsimp [B,W]; omega) (by dsimp [W]; omega) x v ex eY hex heY b hb
  apply homotopy_regrade_injective (show t-s=W-B by dsimp [B,W]; omega)
    (show t+1=W-c by dsimp [W]; omega)
  have h := congrArg (fun k => k ≫ eY.hom) himage
  erw [hbimage] at h
  simpa only [d,regrade_comp,regrade_transitive,positive_g_regrade_self,Category.assoc] using h

private theorem positive_g_pdf_classical_corollary_heq
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f=0)
    (hg : normalizedExponent model.classicalTower T.g=1)
    (hh : normalizedExponent model.classicalTower T.h=0)
    (c q : ℕ) (hq : 0<q) (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (u : Ambient model T.X ((s+(c+1))+1,t+(c+1)))
    (z : Ambient model T.Z ((s+(c+1))+1,(t+(c+1))+1))
    (v : Ambient model T.Y ((s+(c+1))+q+1,(t+(c+1))+q))
    (hu : ∃ u' : Ambient model T.X ((s+(c+1))+1,((t+(c+1))+1)-1),
      (model.classicalSuspension T.X).DesuspendsClass ((s+(c+1))+1) ((t+(c+1))+1)
        ((model.classical.map T.h).pageMap 2 ((s+(c+1))+1,(t+(c+1))+1) z) u' ∧ HEq u' u)
    (hdx : HasDifferential (model.classical.obj (T.X.obj model.auxiliary))
      ((c+1)+1) (s,t) ((s+(c+1))+1,t+(c+1)) x u)
    (hdz : HasDifferential (model.classical.obj (T.Z.obj model.auxiliary))
      (q+1) ((s+(c+1))+1,(t+(c+1))+1)
      (((s+(c+1))+q+1)+1,((t+(c+1))+q)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        ((s+(c+1))+q+1) ((t+(c+1))+q) v))
    (hNC1 : ∀ j : ℕ, 1≤j → j<(q+1)-1 →
      cycles model T.X (((q+1:ℕ):ℤ)-j)
        ((s+(c+1))+1+j,(t+(c+1))+j) ≤
      boundaries model T.X ((c:ℤ)+j+1)
        ((s+(c+1))+1+j,(t+(c+1))+j))
    (hNC2 : ∀ a : Ambient model T.X
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1),
      (model.classical.map T.f).pageMap 2
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1) a ∈
      boundaries model T.Y (c+(q+1))
        ((s+(c+1))+1+(q+1:ℕ)-1,(t+(c+1))+(q+1:ℕ)-1)) :
    let y := (model.classical.map T.f).pageMap 2 (s,t) x
    IsCycle model T.Y (c+(q+1)) (s,t) y ∧
      DifferentialAt model T.Y (c+(q+1)+1) (s,t)
        ((s+(c+1))+q+1,(t+(c+1))+q) y v := by
  obtain ⟨u',hu',hU⟩ := hu
  apply positive_g_pdf_classical_corollary T he hT hf hg hh c q hq s t x u z v ?_ hdx hdz hNC1 hNC2
  let uc : Ambient model T.X (s+(c+1)+1,((t+(c+1))+1)-1) := by simpa using u
  have hc : HEq uc u := cast_heq _ _
  have heq : u'=uc := eq_of_heq (hU.trans hc.symm)
  change (model.classicalSuspension T.X).DesuspendsClass (s+(c+1)+1) ((t+(c+1))+1)
    ((model.classical.map T.h).pageMap 2 (s+(c+1)+1,(t+(c+1))+1) z) uc
  rw [←heq]
  exact hu'

private theorem positive_g_pdf_classical_corollary_RK
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hT : NormalizedTriangleCompatible model T he)
    (hf : normalizedExponent model.classicalTower T.f = 0)
    (hg : normalizedExponent model.classicalTower T.g = 1)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (R K : ℕ) (hR : 2≤R) (hK : 2≤K) (s t : ℤ)
    (x : Ambient model T.X (s,t)) (u : Ambient model T.X (s+R,t+R-1))
    (z : Ambient model T.Z (s+R,t+R))
    (v : Ambient model T.Y (s+R+K-1,t+R+K-2))
    (hu : (model.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
      ((model.classical.map T.h).pageMap 2 (s+R,t+R) z) u)
    (hdx : DifferentialAt model T.X R (s,t) (s+R,t+R-1) x u)
    (hdz : DifferentialAt model T.Z K (s+R,t+R) ((s+R+K-1)+1,(t+R+K-2)+1) z
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+R+K-1) (t+R+K-2) v))
    (hNC1 : ∀ j : ℕ, 1≤j → j<K-1 →
      cycles model T.X ((K:ℤ)-j) (s+R+j,t+R+j-1) ≤
        boundaries model T.X ((R:ℤ)+j-1) (s+R+j,t+R+j-1))
    (hNC2 : ∀ a : Ambient model T.X (s+R+K-1,t+R+K-2),
      (model.classical.map T.f).pageMap 2 (s+R+K-1,t+R+K-2) a ∈
      boundaries model T.Y ((R:ℤ)+K-2) (s+R+K-1,t+R+K-2)) :
    let y := (model.classical.map T.f).pageMap 2 (s,t) x
    IsCycle model T.Y ((R:ℤ)+K-2) (s,t) y ∧
      DifferentialAt model T.Y ((R:ℤ)+K-1) (s,t) (s+R+K-1,t+R+K-2) y v := by
  obtain ⟨c,rfl⟩ : ∃c,R=c+2 := ⟨R-2,by omega⟩
  obtain ⟨q,rfl⟩ : ∃q,K=q+1 := ⟨K-1,by omega⟩
  have Hst := positive_g_pdf_classical_corollary_heq T he hT hf hg hh c q (by omega) s t
  rw [show (s+((c:ℤ)+1))+q+1=s+(c+2:ℕ)+(q+1:ℕ)-1 by omega,
    show (t+((c:ℤ)+1))+q=t+(c+2:ℕ)+(q+1:ℕ)-2 by omega,
    show (t+((c:ℤ)+1))+1=t+(c+2:ℕ) by omega,
    show s+((c:ℤ)+1)+1=s+(c+2:ℕ) by omega,
    show t+((c:ℤ)+1)=t+(c+2:ℕ)-1 by omega] at Hst
  rw [show ((c:ℤ)+1)+1=(c+2:ℕ) by omega,
    show ((c:ℤ)+((q:ℤ)+1)+1)=(c+2:ℕ)+(q+1:ℕ)-1 by omega,
    show ((c:ℤ)+((q:ℤ)+1))=(c+2:ℕ)+(q+1:ℕ)-2 by omega,
    show (t+(c+2:ℕ)-1)+(q+1:ℕ)-1=t+(c+2:ℕ)+(q+1:ℕ)-2 by omega] at Hst
  have HNC := Hst x u z v ⟨u,hu,HEq.rfl⟩ hdx.2 hdz.2
  apply HNC ?_ hNC2
  intro j hj hjq
  rw [show (t+(c+2:ℕ)-1)+j=t+(c+2:ℕ)+j-1 by omega,
    show (c:ℤ)+j+1=(c+2:ℕ)+j-1 by omega]
  exact hNC1 j hj hjq

private theorem positive_g_classical_label_regrade_heq {X : ClassicalObject} {p q : ℤ×ℤ}
    (h : p=q) (x : Ambient model X p) : HEq (classicalLabelRegrade h x) x := by
  subst q
  rfl

private theorem positive_g_classical_map_label_heq (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    {p q : ℤ×ℤ} (hp : p=q) (a : Ambient model X p) (b : Ambient model X q)
    (hab : HEq a b) :
    HEq ((model.classical.map f).pageMap 2 p a)
      ((model.classical.map f).pageMap 2 q b) := by
  subst q
  cases eq_of_heq hab
  rfl

private theorem positive_g_classical_cycle_heq (X : ClassicalObject) (r : ℤ)
    {p q : ℤ×ℤ} (hp : p=q) (a : Ambient model X p) (b : Ambient model X q)
    (hab : HEq a b) (ha : IsCycle model X r p a) : IsCycle model X r q b := by
  subst q
  cases eq_of_heq hab
  exact ha

private theorem positive_g_classical_boundary_heq (X : ClassicalObject) (r : ℤ)
    {p q : ℤ×ℤ} (hp : p=q) (a : Ambient model X p) (b : Ambient model X q)
    (hab : HEq a b) (ha : a ∈ boundaries model X r p) : b ∈ boundaries model X r q := by
  subst q
  cases eq_of_heq hab
  exact ha

private theorem positive_g_classical_differential_heq (X : ClassicalObject) (r : ℤ)
    {p p' q q' : ℤ×ℤ} (hp : p=p') (hq : q=q')
    (a : Ambient model X p) (a' : Ambient model X p')
    (b : Ambient model X q) (b' : Ambient model X q')
    (ha : HEq a a') (hb : HEq b b')
    (hd : DifferentialAt model X r p q a b) :
    DifferentialAt model X r p' q' a' b' := by
  subst p' q'
  cases eq_of_heq ha
  cases eq_of_heq hb
  exact hd

private theorem positive_g_normalized_operation_zero_heq (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (hf : normalizedExponent model.classicalTower f = 0)
    (s t : ℤ) (x : Ambient model X (s,t)) :
    HEq (normalizedClassicalOperation X Y f s t x)
      ((model.classical.map f).pageMap 2 (s,t) x) :=
  (positive_g_classical_label_regrade_heq _ _).symm.trans
    (heq_of_eq (normalized_classical_operation_zero X Y f hf s t x))

private theorem positive_g_operation_label_heq (X Y : ClassicalObject)
    (F : (SyntheticCategory.biShift (0,1)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)) ⟶
        model.nu.functor.obj (Y.obj model.auxiliary))
    {p q : ℤ×ℤ} (hp : p=q) (a : Ambient model X p) (b : Ambient model X q)
    (hab : HEq a b) :
    HEq (positiveFirstQuotientOperation X Y F p.1 p.2 a)
      (positiveFirstQuotientOperation X Y F q.1 q.2 b) := by
  subst q
  cases eq_of_heq hab
  rfl

private theorem positive_g_normalized_operation_one_heq
    (T : TriangleData model.auxiliary)
    (hg : normalizedExponent model.classicalTower T.g=1)
    (s t : ℤ) (x : Ambient model T.Y (s,t)) :
    HEq (normalizedClassicalOperation T.Y T.Z T.g s t x)
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg) s t x) := by
  have h := normalized_classical_operation_one T.Y T.Z T.g hg s t x
  rw [←normalized_second_positive_map_eq T hg] at h
  exact (positive_g_classical_label_regrade_heq _ _).symm.trans (heq_of_eq h)

private theorem positive_g_classical_nc_statement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1)
    (hf : normalizedExponent model.classicalTower T.f = 0)
    (hg : normalizedExponent model.classicalTower T.g = 1)
    (hh : normalizedExponent model.classicalTower T.h = 0) :
    ClassicalNCCompositionStatement T he := by
  intro hT R K hR hK s t x z v hx hz hu hdz hNC1 hNC2
  have hzdeg : (s+R-normalizedExponent model.classicalTower T.h,
      t+R-normalizedExponent model.classicalTower T.h)=(s+R,t+R) := by simp [hh]
  have hvdeg : (s+R+normalizedExponent model.classicalTower T.f+K-1,
      t+R+normalizedExponent model.classicalTower T.f+K-2)=(s+R+K-1,t+R+K-2) := by
    simp only [hf,Nat.cast_zero,add_zero]
  let z0 := classicalLabelRegrade hzdeg z
  let v0 := classicalLabelRegrade hvdeg v
  have hz0 : HEq z z0 := (positive_g_classical_label_regrade_heq hzdeg z).symm
  have hv0 : HEq v v0 := (positive_g_classical_label_regrade_heq hvdeg v).symm
  obtain ⟨u,hu,hdx⟩ := hu
  have hhu : HEq
      (classicalLabelRegrade (X := .shift 1 T.X) (q := (s+R,t+R))
        (by ext <;> dsimp <;> omega)
        (normalizedClassicalOperation T.Z (.shift 1 T.X) T.h
          (s+R-normalizedExponent model.classicalTower T.h)
          (t+R-normalizedExponent model.classicalTower T.h) z))
      ((model.classical.map T.h).pageMap 2 (s+R,t+R) z0) :=
    (positive_g_classical_label_regrade_heq _ _).trans
      ((positive_g_normalized_operation_zero_heq T.Z (.shift 1 T.X) T.h hh _ _ z).trans
        (positive_g_classical_map_label_heq T.Z (.shift 1 T.X) T.h hzdeg z z0 hz0))
  rw [eq_of_heq hhu] at hu
  have htarget : HEq
      (classicalLabelRegrade (X := T.Z)
        (q := (s+R-normalizedExponent model.classicalTower T.h+K,
          t+R-normalizedExponent model.classicalTower T.h+K-1))
        (by ext <;> dsimp <;> omega)
        (normalizedClassicalOperation T.Y T.Z T.g
          (s+R+normalizedExponent model.classicalTower T.f+K-1)
          (t+R+normalizedExponent model.classicalTower T.f+K-2) v))
      (positiveFirstQuotientOperation T.Y T.Z (normalizedSecondPositiveMap T hg)
        (s+R+K-1) (t+R+K-2) v0) :=
    (positive_g_classical_label_regrade_heq _ _).trans
      ((positive_g_normalized_operation_one_heq T hg _ _ v).trans
        (positive_g_operation_label_heq T.Y T.Z (normalizedSecondPositiveMap T hg)
          hvdeg v v0 hv0))
  have hdz0 := positive_g_classical_differential_heq T.Z K hzdeg
    (show (s+R-normalizedExponent model.classicalTower T.h+K,
      t+R-normalizedExponent model.classicalTower T.h+K-1)=
      ((s+R+K-1)+1,(t+R+K-2)+1) by
        simp only [hh,Nat.cast_zero,sub_zero]
        ext <;> dsimp <;> omega)
    z z0 _ _ hz0 htarget hdz
  have hNC2' : ∀ a : Ambient model T.X (s+R+K-1,t+R+K-2),
      (model.classical.map T.f).pageMap 2 (s+R+K-1,t+R+K-2) a ∈
      boundaries model T.Y ((R:ℤ)+K-2) (s+R+K-1,t+R+K-2) := by
    intro a
    exact positive_g_classical_boundary_heq T.Y ((R:ℤ)+K-2)
      (by simp only [hf,Nat.cast_zero,add_zero]) _ _
      (positive_g_normalized_operation_zero_heq T.X T.Y T.f hf _ _ a) (hNC2 a)
  obtain ⟨hy,hdy⟩ := positive_g_pdf_classical_corollary_RK T he hT hf hg hh
    R K hR hK s t x u z0 v0 hu hdx hdz0 hNC1 hNC2'
  let y := normalizedClassicalOperation T.X T.Y T.f s t x
  let y0 := (model.classical.map T.f).pageMap 2 (s,t) x
  have hydeg : (s,t)=(s+normalizedExponent model.classicalTower T.f,
      t+normalizedExponent model.classicalTower T.f) := by simp [hf]
  have hyy : HEq y0 y := (positive_g_normalized_operation_zero_heq T.X T.Y T.f hf s t x).symm
  exact ⟨positive_g_classical_cycle_heq T.Y ((R:ℤ)+K-2) hydeg y0 y hyy hy,
    positive_g_classical_differential_heq T.Y ((R:ℤ)+K-1) hydeg hvdeg.symm
      y0 y v0 v hyy hv0.symm hdy⟩

end
end KIP126.ProofTools.Internal.MahowaldLeibniz
