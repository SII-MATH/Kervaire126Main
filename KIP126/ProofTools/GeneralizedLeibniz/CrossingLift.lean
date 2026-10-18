module
import all KIP126.ProofTools.GeneralizedLeibniz.Boundary
import all KIP126.ProofTools.GeneralizedLeibniz.BottomTarget
import all KIP126.ProofTools.GeneralizedMahowald.ShortSource
import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision
import all KIP126.ProofTools.GeneralizedMahowald.ExtensionImage

/-! The smaller-quotient witness and boundary tests in AimPaper Proposition
`prop:cross-f-Er`, including the untruncated boundary test.
Once the divided source has an image in the required target filtration,
the fixed finite-window comparisons supply both classical cycle labels
and an actual extension witness, at any allowed length. The unconditional
simultaneous-lifting assertion has an actual-spectrum counterexample in
the paper's generality; see MEMO.md and the 20261018 GL/crossing review.
These conditional lemmas do not assert such a lift in the fixed model. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Leibniz
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
set_option Elab.async false

/-- The actual map on infinity classes in the finite lambda square. The
same construction is used for a normalized source and an unshifted target. -/
private def finiteLambdaInfinity (A : SyntheticObject) (q i : ℕ)
    (hi : 0 < i) (hiq : i < q) (p : ℤ × ℤ) (s : ℤ)
    (x : ((model.family.obj ((SyntheticObject.quotient (q-i) A).obj
      model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty) :
    ((model.family.obj ((SyntheticObject.quotient q A).obj model.nu model.auxiliary)).sequence.ssData
      (s,(p+(0,-(i:ℤ))).1+s,(p+(0,-(i:ℤ))).2)).eInfty := by
  let B := SyntheticObject.quotient (q-i) A
  let δ : ℤ × ℤ := (0,-(i:ℤ))
  let L : ((SyntheticObject.shift δ B).obj model.nu model.auxiliary) ⟶
      ((SyntheticObject.quotient q A).obj model.nu model.auxiliary) :=
    ((model.quotients.tower (A.obj model.nu model.auxiliary)).triangle hi hiq).lambdaMap
  let I : ((model.family.obj (B.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty ≅
      ((model.family.obj ((SyntheticObject.shift δ B).obj model.nu model.auxiliary)).sequence.ssData
        (s,(p+δ).1+s,(p+δ).2)).eInfty :=
    towerInfinityIso (model.convergence B) (model.convergence (.shift δ B))
      ((essShift δ).filtered B p) s
  exact (model.family.map L).eInftyMap (s,(p+δ).1+s,(p+δ).2) (I.hom x)

private theorem finite_lambda_infinity_nu_heq (X : ClassicalObject)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (p : ℤ × ℤ) (s : ℤ)
    (x : ((model.family.obj ((SyntheticObject.quotient (q-i) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty) :
    HEq (finiteLambdaInfinity (.nu X) q i hi hiq p s x)
      (KIP126.Literature.Standard.infinityFiniteLambda X q i hiq (s,p.1+s) p.2 x) := by
  have hmap {U V : SyntheticSpectrum} (f : U ⟶ V) (a b : Tridegree) (hab : a=b)
      (x : ((model.family.obj U).sequence.ssData a).eInfty)
      (y : ((model.family.obj U).sequence.ssData b).eInfty) (hxy : HEq x y) :
      HEq ((model.family.functor.map f).eInftyMap a x)
        ((model.family.functor.map f).eInftyMap b y) := by
    subst b
    cases hxy
    rfl
  rcases p with ⟨m,w⟩
  simp only [finiteLambdaInfinity,KIP126.Literature.Standard.infinityFiniteLambda,
    InfinityShiftCoordinates.finiteLambdaMap,show i ≠ 0 by omega,↓reduceDIte,ModuleCat.comp_apply]
  exact hmap _ _ _ (by ext <;> dsimp <;> omega) _ _
    (infinityShift_stem_heq (.quotient (q-i) (.nu X)) i m w s x).symm

private theorem finite_lambda_infinity_nonzero_iff_boundary (X : ClassicalObject)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (p : ℤ × ℤ) (s : ℤ)
    (hw : 0 ≤ p.1+s-p.2 ∧ p.1+s-p.2 < (q-i:ℕ))
    (y : Ambient model X (s,p.1+s))
    (e : ((model.family.obj ((SyntheticObject.quotient (q-i) (.nu X)).obj
      model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (he : HasInfinityRepresentative _ 2 (s,p.1+s,p.2)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (q-i)).pageMap
        2 (s,p.1+s,p.2) (nuWeightLabel model X s (p.1+s) p.2 (by omega) y)) e) :
    finiteLambdaInfinity (.nu X) q i hi hiq p s e ≠ 0 ↔
      y ∉ boundaries model X (1+(p.1+s)-(p.2-i)) (s,p.1+s) := by
  let E (a : Tridegree) := ((model.family.obj ((SyntheticObject.quotient q (.nu X)).obj
    model.nu model.auxiliary)).sequence.ssData a).eInfty
  have hp : (s,(p+(0,-(i:ℤ))).1+s,(p+(0,-(i:ℤ))).2) =
      (s,p.1+s,p.2-i) := by ext <;> simp [sub_eq_add_neg]
  let J := eqToHom (congrArg E hp)
  have hEq : J (finiteLambdaInfinity (.nu X) q i hi hiq p s e) =
      KIP126.Literature.Standard.infinityFiniteLambda X q i hiq (s,p.1+s) p.2 e :=
    eq_of_heq ((eqToHom_apply_heq (congrArg E hp) _).trans
      (finite_lambda_infinity_nu_heq X q i hi hiq p s e))
  have hzero : finiteLambdaInfinity (.nu X) q i hi hiq p s e = 0 ↔
      KIP126.Literature.Standard.infinityFiniteLambda X q i hiq (s,p.1+s) p.2 e = 0 := by
    constructor
    · intro hz
      rw [←hEq,hz,map_zero]
    · intro hz
      apply (ModuleCat.mono_iff_injective J).mp inferInstance
      rw [hEq,hz,map_zero]
  exact (not_congr hzero).trans
    (CrossingLabels.lambda_finite_label_nonzero X q i hiq s (p.1+s) p.2 hw y e he)

set_option backward.defeqAttrib.useBackward false in
/-- In the actual finite lambda square, an essential extension from the
mapped source forces a known preimage extension to be essential and its
lambda target to be nonzero. No preservation of essentiality is assumed. -/
private theorem finite_extension_essential_of_lambda_source
    (A B : SyntheticObject) (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (p : ℤ × ℤ) (s n : ℤ)
    (x : ((model.family.obj ((SyntheticObject.quotient (q-i) A).obj
      model.nu model.auxiliary)).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((model.family.obj ((SyntheticObject.quotient (q-i) B).obj
      model.nu model.auxiliary)).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (z : ((model.family.obj ((SyntheticObject.quotient q B).obj model.nu model.auxiliary)).sequence.ssData
      (s+n,(p+((0:ℤ),-(i:ℤ))).1+(s+n),(p+((0:ℤ),-(i:ℤ))).2)).eInfty)
    (he : TowerExtensionEquation (F := model.family) (P := model.syntheticTower)
      (cx := model.convergence (.quotient (q-i) A)) (cy := model.convergence (.quotient (q-i) B))
      (model.convergentMap
      (.quotient (q-i) A) (.quotient (q-i) B) (XModLambdaN.map g (q-i))) p s n x y)
    (hess : TowerEssentialExtension (F := model.family) (P := model.syntheticTower)
      (X := (SyntheticObject.quotient q A).obj model.nu model.auxiliary)
      (Y := (SyntheticObject.quotient q B).obj model.nu model.auxiliary)
      (g := XModLambdaN.map g q)
      (cx := model.convergence (.quotient q A)) (cy := model.convergence (.quotient q B))
      (model.convergentMap
      (.quotient q A) (.quotient q B) (XModLambdaN.map g q)) (p+((0:ℤ),-(i:ℤ))) s n
      (finiteLambdaInfinity A q i hi hiq p s x) z) :
    TowerEssentialExtension (F := model.family) (P := model.syntheticTower)
      (cx := model.convergence (.quotient (q-i) A)) (cy := model.convergence (.quotient (q-i) B))
      (model.convergentMap
      (.quotient (q-i) A) (.quotient (q-i) B) (XModLambdaN.map g (q-i))) p s n x y ∧
      finiteLambdaInfinity B q i hi hiq p (s+n) y ≠ 0 := by
  let δ : ℤ × ℤ := (0,-(i:ℤ))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) δ
  let LA := ((model.quotients.tower (A.obj model.nu model.auxiliary)).triangle hi hiq).lambdaMap
  let LB := ((model.quotients.tower (B.obj model.nu model.auxiliary)).triangle hi hiq).lambdaMap
  let M := model.convergentMap (.quotient (q-i) A) (.quotient (q-i) B)
    (XModLambdaN.map g (q-i))
  let MS := model.convergentMap (.shift δ (.quotient (q-i) A))
    (.shift δ (.quotient (q-i) B)) (F.map (XModLambdaN.map g (q-i)))
  let ML := model.convergentMap (.quotient q A) (.quotient q B)
    (XModLambdaN.map g q)
  have hcomm := (model.quotients.natural g).lambda_naturality hi hiq
  change F.map (XModLambdaN.map g (q-i)) ≫ LB = LA ≫ XModLambdaN.map g q at hcomm
  have hs := ((essShift δ).towerExtensionEquation_iff
    (.quotient (q-i) A) (.quotient (q-i) B) (XModLambdaN.map g (q-i))
    p s n x y).mp he
  obtain ⟨hsmall,hne⟩ := tower_essential_of_mapped_source MS ML
    (model.convergentMap (.shift δ (.quotient (q-i) A)) (.quotient q A) LA)
    (model.convergentMap (.shift δ (.quotient (q-i) B)) (.quotient q B) LB)
    hcomm (p+δ) s n _ _ z hs hess
  refine ⟨?_,hne⟩
  apply (tower_essential_iff_no_zero M p s n x y he).mpr
  intro hzero
  have hs0 := ((essShift δ).towerExtensionEquation_iff
    (.quotient (q-i) A) (.quotient (q-i) B) (XModLambdaN.map g (q-i))
    p s n x 0).mp hzero
  simp only [map_zero] at hs0
  exact ((tower_essential_iff_no_zero MS (p+δ) s n _ _ hsmall.1).mp hsmall) hs0

private theorem finite_weight_label_heq (X : ClassicalObject) (q : ℕ)
    (s t w s' t' w' : ℤ) (hs : s=s') (ht : t=t') (hw : w=w')
    (hwt : w ≤ t) (hwt' : w' ≤ t')
    (y : Ambient model X (s,t)) (y' : Ambient model X (s',t')) (hy : HEq y y') :
    HEq ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap
      2 (s,t,w) (nuWeightLabel model X s t w hwt y))
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap
        2 (s',t',w') (nuWeightLabel model X s' t' w' hwt' y')) := by
  subst s'
  subst t'
  subst w'
  cases hy
  rfl

/-- For a smaller finite witness, nonvanishing of its actual lambda target
is exactly the boundary exclusion appearing in the paper's crossing
definition, with the larger lambda layer retained. -/
private theorem finite_witness_lambda_target_nonzero_iff
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i : ℕ) (hi : 0 < i) (hiq : i < q) (n s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f ((q-i)+1) n s t x y) :
    finiteLambdaInfinity (.nu Y) q i hi hiq
        (t-s,t+normalizedExponent model.classicalTower f) (s+n) W.target ≠ 0 ↔
      y ∉ boundaries model Y (1+n+i-normalizedExponent model.classicalTower f) (s+n,t+n) := by
  let e : ℤ := normalizedExponent model.classicalTower f
  let p : ℤ × ℤ := (t-s,t+e)
  have hl := W.length_lower
  have hu := W.length_upper
  have ht : t+n=p.1+(s+n) := by dsimp [p]; omega
  have hp : (s+n,t+n)=(s+n,p.1+(s+n)) := congrArg (fun v => (s+n,v)) ht
  let yn : Ambient model Y (s+n,p.1+(s+n)) :=
    (eqToHom (congrArg (fun a => Ambient model Y a) hp)) y
  have hyn : HEq yn y := eqToHom_apply_heq (congrArg (fun a => Ambient model Y a) hp) y
  have hwt : t+e ≤ t+n := by dsimp [e]; omega
  have hwtn : p.2 ≤ p.1+(s+n) := by dsimp [p,e]; omega
  have hlabel : HEq (finiteTargetForExtension model X Y f (q-i) n s t hl y)
      ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) (q-i)).pageMap
        2 (s+n,p.1+(s+n),p.2)
          (nuWeightLabel model Y (s+n) (p.1+(s+n)) p.2 hwtn yn)) := by
    have H := finite_extension_target_weight_label X Y f (q-i) n s t hl y
    exact (regradeE2_heq _ _).symm.trans ((heq_of_eq H).trans
      (finite_weight_label_heq Y (q-i) (s+n) (t+n) (t+e)
        (s+n) (p.1+(s+n)) p.2 rfl ht rfl hwt hwtn y yn hyn.symm))
  have he : HasInfinityRepresentative _ 2 (s+n,p.1+(s+n),p.2)
      ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) (q-i)).pageMap
        2 (s+n,p.1+(s+n),p.2)
          (nuWeightLabel model Y (s+n) (p.1+(s+n)) p.2 hwtn yn)) W.target := by
    rw [←eq_of_heq hlabel]
    exact W.target_rep
  have H := finite_lambda_infinity_nonzero_iff_boundary Y q i hi hiq p (s+n)
    (by dsimp [p,e]; constructor <;> omega) yn W.target he
  have transport (v : ℤ) (hv : v=t+n) (z : Ambient model Y (s+n,v)) (hz : HEq z y) :
      z ∉ boundaries model Y (1+v-((t+e)-i)) (s+n,v) ↔
        y ∉ boundaries model Y (1+n+i-e) (s+n,t+n) := by
    subst v
    cases hz
    rw [show 1+(t+n)-((t+e)-i)=1+n+i-e by omega]
  exact H.trans (transport (p.1+(s+n)) ht.symm yn hyn)

/-- Once a smaller-quotient witness lifts the prescribed crossing source,
the actual large-quotient essential extension supplies all remaining paper
crossing conditions: essentiality, the exact boundary exclusion, and the
page and length bounds. The missing existence of that witness is not
replaced by an assumption in the public generalized Leibniz law. -/
private theorem finite_crossing_of_lifted_witness
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q i b : ℕ) (hi : 0 < i) (hiq : i < q) (N s t : ℤ)
    (x : Ambient model X (s+i,t+i))
    (y : Ambient model Y (s+i+(N-i-b),t+i+(N-i-b)))
    (W : FiniteExtensionWitness model X Y f ((q-i)+1) (N-i-b) (s+i) (t+i) x y) :
    let p : ℤ × ℤ := ((t+i)-(s+i),(t+i)+normalizedExponent model.classicalTower f)
    ∀ z : ((model.family.obj ((SyntheticObject.quotient q (.nu Y)).obj
      model.nu model.auxiliary)).sequence.ssData
      (s+i+(N-i-b),(p+((0:ℤ),-(i:ℤ))).1+(s+i+(N-i-b)),
        (p+((0:ℤ),-(i:ℤ))).2)).eInfty,
      TowerEssentialExtension (model.convergentMap
        (.quotient q (extensionSourceObject model X Y f)) (.quotient q (.nu Y))
        (finiteExtensionMap model X Y f q)) (p+((0:ℤ),-(i:ℤ))) (s+i) (N-i-b)
        (finiteLambdaInfinity (extensionSourceObject model X Y f) q i hi hiq p (s+i) W.source) z →
      FiniteHasCrossing model X Y f (q+1) N s t := by
  intro p z hess
  obtain ⟨hsmall,hne⟩ := finite_extension_essential_of_lambda_source
    (extensionSourceObject model X Y f) (.nu Y) (model.normalizedMap X Y f).map
    q i hi hiq p (s+i) (N-i-b) W.source W.target z W.equation hess
  have hb := (finite_witness_lambda_target_nonzero_iff X Y f q i hi hiq
    (N-i-b) (s+i) (t+i) x y W).mp hne
  have hb' : y ∉ boundaries model Y
      (1+N-b-normalizedExponent model.classicalTower f)
      (s+i+(N-i-b),t+i+(N-i-b)) := by
    rwa [show 1+(N-i-b)+(i:ℤ)-normalizedExponent model.classicalTower f =
      1+N-b-normalizedExponent model.classicalTower f by omega] at hb
  refine ⟨i,b,hi,by omega,?_,x,y,?_⟩
  · have hl := W.length_lower
    omega
  · rw [show (q+1)-i=(q-i)+1 by omega]
    exact ⟨W,hsmall,hb'⟩

/-- An actual source with a sufficiently filtered image gives a finite
extension of arbitrary allowed length, retaining that very image as the
detecting representative of the target. -/
private theorem finite_witness_of_filtered_source_image
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) (hq : 0 < q) (n s t : ℤ)
    (hn : (normalizedExponent model.classicalTower f : ℤ) ≤ n)
    (hnq : n ≤ (q:ℤ)-1+normalizedExponent model.classicalTower f)
    (a : BiHom (t-s) (t+normalizedExponent model.classicalTower f)
      (XModLambdaN ((extensionSourceObject model X Y f).obj model.nu model.auxiliary) q))
    (himage : FiltrationAtLeast model.syntheticTower (s+n)
      (a ≫ finiteExtensionMap model X Y f q)) :
    ∃ (x : Ambient model X (s,t)) (y : Ambient model Y (s+n,t+n)),
      ∃ _W : FiniteExtensionWitness model X Y f (q+1) n s t x y,
        Detects (model.convergence (.quotient q (extensionSourceObject model X Y f)))
          (s,t,t+normalizedExponent model.classicalTower f)
          (regradeE2 (by simp) (finiteNuLabel model X q
            (normalizedExponent model.classicalTower f) s t 0 x)) a ∧
        Detects (model.convergence (.quotient q (.nu Y)))
          (s+n,t+n,t+normalizedExponent model.classicalTower f)
          ((model.family.quotientProjection (model.nu.functor.obj (Y.obj model.auxiliary)) q).pageMap
            2 (s+n,t+n,t+normalizedExponent model.classicalTower f)
            (nuWeightLabel model Y (s+n) (t+n)
              (t+normalizedExponent model.classicalTower f) (by omega) y))
          (homotopyRegrade (by dsimp; omega) rfl (a ≫ finiteExtensionMap model X Y f q)) := by
  let e : ℤ := normalizedExponent model.classicalTower f
  obtain ⟨x,hx,hax⟩ := normalized_finite_source_label_exists X Y f q hq s t a
  let b : BiHom ((t+n)-(s+n)) (t+e)
      (XModLambdaN (model.nu.functor.obj (Y.obj model.auxiliary)) q) :=
    homotopyRegrade (by omega) rfl (a ≫ finiteExtensionMap model X Y f q)
  have hb : FiltrationAtLeast model.syntheticTower (s+n) b :=
    (regrade_filtration_iff (by omega) rfl (s+n) _).mpr himage
  obtain ⟨y,hy,hby⟩ := finite_filtered_target_label Y q hq (s+n) (t+n) (t+e)
    (by dsimp [e]; constructor <;> omega) b hb
  have hsource := source_detects_reindex X q e s t x a hax
  let hp : (s+n,(t-s)+(s+n),t+e) = (s+n,t+n,t+e) := by
    ext <;> first | rfl | (dsimp; omega)
  have htarget' : Detects (model.convergence (.quotient q (.nu Y)))
      (s+n,(t-s)+(s+n),t+e)
      (finiteTargetForExtension model X Y f q n s t hn y)
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ finiteExtensionMap model X Y f q)) := by
    have Hback := detects_transport hp.symm _ _ hby
    convert Hback using 1
    · have H := congrArg (regradeE2 hp.symm)
        (finite_extension_target_weight_label X Y f q n s t hn y)
      rw [e2_regrade_trans] at H
      exact H
    · dsimp only [b]
      rw [homotopy_regrade_comp]
  obtain ⟨xx,yy,hxx,hyy,heq⟩ := extension_equation_of_detected_pair
    (model.convergentMap (.quotient q (extensionSourceObject model X Y f))
      (.quotient q (.nu Y)) (finiteExtensionMap model X Y f q))
      (t-s,t+e) s n (by dsimp [e] at *; omega) _ _ a
      (a ≫ finiteExtensionMap model X Y f q) hsource htarget' rfl
  have hxreach : ReachesPage (model.classical.obj (X.obj model.auxiliary))
      (q+1:ℕ) (s,t) x :=
    (isCycle_iff_reaches model X (q+1:ℕ) (by omega) (s,t) x).mp
      ⟨by omega,by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hx⟩
  have hyreach : ReachesPage (model.classical.obj (Y.obj model.auxiliary))
      ((q+1:ℕ)-n+normalizedExponent model.classicalTower f) (s+n,t+n) y := by
    apply (isCycle_iff_reaches model Y _ (by omega) (s+n,t+n) y).mp
    refine ⟨by omega,?_⟩
    convert hy using 1
    dsimp [e]
    congr 1
    omega
  refine ⟨x,y,?_,hax,hby⟩
  exact {
    page_ge_two := by omega
    length_lower := hn
    length_upper := by omega
    source_cycle := hxreach
    target_cycle := hyreach
    source := xx
    target := yy
    source_rep := hxx
    target_rep := hyy
    equation := heq }

/-- The exact boundary ambiguity in the paper's crossing lift. At any
lambda layer, disappearance of the mapped target grade is equivalent to
membership in the larger boundary submodule. This does not cancel lambda
on a homotopy representative. -/
private theorem finite_weighted_lambda_high_iff_boundary
    (X : ClassicalObject) (q k : ℕ) (hk : 0 < k) (hkq : k < q)
    (s t w : ℤ) (hw : 0 ≤ t-w ∧ t-w < (q-k:ℕ))
    (y : Ambient model X (s,t))
    (b : BiHom (t-s) w (XModLambdaN (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)))
    (hb : Detects (model.convergence (.quotient (q-k) (.nu X))) (s,t,w)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) (q-k)).pageMap
        2 (s,t,w) (nuWeightLabel model X s t w (by omega) y)) b) :
    FiltrationAtLeast model.syntheticTower (s+1)
        (finiteWeightedLambdaClass X q k hk hkq s t w b) ↔
      y ∈ boundaries model X (1+t-(w-k)) (s,t) := by
  have hmap := finite_weighted_lambda_detects X q k hk hkq s t w hw y b hb
  obtain ⟨e,he,_⟩ := hb
  have hy := ((KIP126.Literature.Standard.eInfinity_finite_labels X (q-k) (by omega)
    s t w hw y e).mp he).1
  have hy' : y ∈ cycles model X (q-t+(w-k)) (s,t) := by
    convert hy using 1
    congr 1
    omega
  have hzero : HasInfinityRepresentative _ 2 (s,t,w-k)
      ((model.family.quotientProjection (model.nu.functor.obj (X.obj model.auxiliary)) q).pageMap
        2 (s,t,w-k) (nuWeightLabel model X s t (w-k) (by omega) y)) 0 ↔
      y ∈ boundaries model X (1+t-(w-k)) (s,t) := by
    rw [KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
      s t (w-k) (by constructor <;> omega)]
    constructor
    · rintro ⟨hy0,hclass⟩
      apply (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hy0⟩).mp
      exact hclass.symm.trans (map_zero _)
    · intro hboundary
      refine ⟨hy',?_⟩
      rw [map_zero]
      exact ((CrossingLabels.subquotient_zero_iff _ _ ⟨y,hy'⟩).mpr hboundary).symm
  constructor
  · intro hhigh
    exact hzero.mp (detects_high_infinity_zero (.quotient q (.nu X)) (s,t,w-k)
      _ _ hmap hhigh)
  · intro hboundary
    exact detects_zero_infinity_filtration (model.convergence (.quotient q (.nu X)))
      (s,t,w-k) hmap (hzero.mpr hboundary)

/-- The untruncated boundary test for the infinite crossing comparison.
It allows any positive lambda exponent, without a finite-page upper bound. -/
private theorem nu_lambda_high_iff_boundary
    (X : ClassicalObject) (k : ℕ) (hk : 0 < k) (s t : ℤ)
    (y : Ambient model X (s,t)) (hy : y ∈ permanentCycles model X (s,t))
    (a : BiHom (t-s) t (model.nu.functor.obj (X.obj model.auxiliary)))
    (ha : a ≫ XModLambdaN.incl _ 1 = firstLabel model X s t y ≫
      XModLambdaN.map (SyntheticCategory.biShift_zero.hom.app _) 1) :
    FiltrationAtLeast model.syntheticTower (s+1) (lambdaMultiply k a) ↔
      y ∈ boundaries model X (k+1) (s,t) := by
  have hmap := nu_lambda_detects X k hk s t y hy a ha
  have hzero : HasInfinityRepresentative _ 2 (s,t,t-k)
      (nuWeightLabel model X s t (t-k) (by omega) y) 0 ↔
      y ∈ boundaries model X (1+t-(t-k)) (s,t) := by
    rw [KIP126.Literature.Standard.eInfinity_nu_labels X s t (t-k) (by omega)]
    constructor
    · rintro ⟨hy0,hclass⟩
      apply (CrossingLabels.subquotient_zero_iff _ _ ⟨y,hy0⟩).mp
      exact hclass.symm.trans (map_zero _)
    · intro hboundary
      refine ⟨hy,?_⟩
      rw [map_zero]
      exact ((CrossingLabels.subquotient_zero_iff _ _ ⟨y,hy⟩).mpr hboundary).symm
  have hindex : 1+t-(t-k)=(k:ℤ)+1 := by omega
  rw [hindex] at hzero
  constructor
  · intro hhigh
    exact hzero.mp (detects_high_infinity_zero (.nu X) (s,t,t-k) _ _ hmap hhigh)
  · intro hboundary
    exact detects_zero_infinity_filtration (model.convergence (.nu X)) (s,t,t-k)
      hmap (hzero.mpr hboundary)

end
end KIP126.ProofTools.Internal.Leibniz
