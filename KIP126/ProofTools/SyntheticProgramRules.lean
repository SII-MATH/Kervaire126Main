module

import all KIP126.ProofTools.Paper.ExtensionRepresentatives
import all KIP126.ProofTools.GeneralizedLeibniz.Square
import all KIP126.ProofTools.GeneralizedLeibnizAtLevel
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelAssembly

/-! Private proofs for the actual extension rules stated in the SS discussion.
The cutoff argument uses essential crossings with the complete shorter-image
indeterminacy of each actual map; no program-success hypothesis is substituted
for its mathematical premises. -/

@[expose] section
namespace KIP126.ProofTools.Internal.ProgramRules
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.AdamsSynthetic KIP126.Core.SpectralSequence
open KIP126.Kervaire.Route KIP126.Literature KIP126.AdamsSynthetic.Standard
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.Leibniz KIP126.ProofTools.Paper
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

section ActualFilteredSquare
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {E : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit E} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

/-- The complete finite triangle of essential crossings above a target cutoff.
The map and both convergences are those of the equation being controlled. -/
private def EssentialNoCrossingRange
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n threshold : ℤ) : Prop :=
  ∀ u v : ℤ, s < u → u ≤ v → threshold ≤ v → v ≤ s+n →
    ∀ x y, ¬TowerEssentialExtension M p u (v-u) x y

/-- The bounded representative correction argument for essential crossings.
This does not require each representative of an inessential target to be zero. -/
private theorem image_in_next_of_essential_range
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n threshold : ℤ) (ht : threshold ≤ s+n)
    (hc : EssentialNoCrossingRange M p s n threshold)
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
    have hi : threshold + ((s+n+1-threshold).toNat : ℤ) = s+n+1 := by
      rw [Int.toNat_of_nonneg (show 0 ≤ s+n+1-threshold by omega)]
      omega
    rw [hi]
    exact hnot
  obtain ⟨b,hb,hbn,hgb,hgbnext⟩ :=
    first_nonzero_filtration_grade G threshold (s+n+1-threshold).toNat (f a)
      hga hnot'
  apply hgbnext
  by_cases hbs : b ≤ s
  · exact P.filtrationSubmodule_antitone Y p (by omega)
      (map_preserves_filtration M p (s+1) a ha)
  · exact higher_source_image_of_nonessential f F G
      (fun i j hij z hz => P.filtrationSubmodule_antitone Y p hij hz)
      (fun k z hz => map_preserves_filtration M p k z hz) s b (by omega)
      (fun k hsk hkb z hz hgz => by
        change z ≫ g ∈ P.filtrationSubmodule Y b p at hgz
        change ∃ b', b' ∈ P.filtrationSubmodule X k p ∧
          z-b' ∈ P.filtrationSubmodule X (k+1) p ∧
          b' ≫ g ∈ P.filtrationSubmodule Y (b+1) p
        have hh := tower_correction_of_nonessential M p k (b-k)
          (by omega) (hc k b hsk hkb hb (by omega)) z hz
          (by simpa only [add_sub_cancel] using hgz)
        simpa only [add_sub_cancel] using hh) a ha hgb

private theorem target_of_source_in_essential_range
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n threshold : ℤ) (ht : threshold ≤ s+n)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation M p s n x y)
    (hc : EssentialNoCrossingRange M p s n threshold)
    (a : BiHom p.1 p.2 X) (ha : RepresentsInfinityClass cx p s x a)
    (hga : a ≫ g ∈ P.filtrationSubmodule Y threshold p) :
    RepresentsInfinityClass cy p (s+n) y (a ≫ g) := by
  obtain ⟨_,ar,br,hab,hx,hy⟩ := (tower_extension_iff M p s n x y).mp he
  let a₀ : BiHom p.1 p.2 X := ((P.filtration X).F s p).arrow ar
  let b₀ : BiHom p.1 p.2 Y := ((P.filtration Y).F (s+n) p).arrow br
  have ha₀ : RepresentsInfinityClass cx p s x a₀ := ⟨ar,rfl,hx⟩
  have hb₀ : RepresentsInfinityClass cy p (s+n) y b₀ := ⟨br,rfl,hy⟩
  have heq : a₀ ≫ g = b₀ := hab
  have hdiff := Paper.representatives_difference p s x a a₀ ha ha₀
  have himage : (a-a₀) ≫ g ∈ P.filtrationSubmodule Y threshold p := by
    rw [Preadditive.sub_comp,heq]
    exact (P.filtrationSubmodule Y threshold p).sub_mem hga
      (P.filtrationSubmodule_antitone Y p ht (Paper.represents_mem p (s+n) y b₀ hb₀))
  have hh := image_in_next_of_essential_range M p s n threshold ht hc
    (a-a₀) hdiff himage
  apply Paper.represents_of_difference p (s+n) y (a≫g) b₀ hb₀
  simpa only [Preadditive.sub_comp,heq] using hh

private theorem target_of_any_source
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n : ℤ)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+n,p.1+(s+n),p.2)).eInfty)
    (he : TowerExtensionEquation M p s n x y)
    (hc : TowerNoCrossing M p s n)
    (a : BiHom p.1 p.2 X) (ha : RepresentsInfinityClass cx p s x a) :
    RepresentsInfinityClass cy p (s+n) y (a ≫ g) := by
  obtain ⟨ar,har,hax⟩ := ha
  obtain ⟨br,hab,hby⟩ := tower_target_of_any_source_frame M p s n x y he hc ar hax
  exact ⟨br,by rw [←hab,har],hby⟩

/-- The actual four-edge cutoff theorem. All crossing hypotheses refer to
essential extensions in the exact map's ESS, including shorter-image data. -/
private theorem four_edge_cutoff
    {Z W : Syn} {cz : SyntheticTowerConvergence P Z} {cw : SyntheticTowerConvergence P W}
    {f : X ⟶ Y} {h : X ⟶ Z} {j : Z ⟶ W} {k : Y ⟶ W}
    (Mf : ConvergentMap E f cx.toConvergence cy.toConvergence)
    (Mh : ConvergentMap E h cx.toConvergence cz.toConvergence)
    (Mj : ConvergentMap E j cz.toConvergence cw.toConvergence)
    (Mk : ConvergentMap E k cy.toConvergence cw.toConvergence)
    (hcomm : f ≫ k = h ≫ j)
    (p : ℤ × ℤ) (s m r l c : ℤ)
    (_hm : 0 ≤ m) (_hr : 0 ≤ r) (_hl : 0 ≤ l)
    (hc : 0 < c) (hcD : c ≤ r+l-m)
    (x : ((E.obj X).sequence.ssData (s,p.1+s,p.2)).eInfty)
    (y : ((E.obj Y).sequence.ssData (s+m,p.1+(s+m),p.2)).eInfty)
    (z : ((E.obj Z).sequence.ssData (s+r,p.1+(s+r),p.2)).eInfty)
    (w : ((E.obj W).sequence.ssData (s+r+l,p.1+(s+r+l),p.2)).eInfty)
    (htop : TowerExtensionEquation Mf p s m x y)
    (hleft : TowerExtensionEquation Mh p s r x z)
    (hbottom : TowerExtensionEquation Mj p (s+r) l z w)
    (hsource : TowerNoCrossing Mf p s m ∨ TowerNoCrossing Mh p s r)
    (hbottomNC : EssentialNoCrossingRange Mj p (s+r) l (s+m+c))
    (hzero : TowerExtensionEquation Mk p (s+m) (c-1) y 0)
    (hzeroNC : TowerNoCrossing Mk p (s+m) (c-1)) :
    TowerExtensionEquation Mk p (s+m) (r+l-m) y
      ((eqToHom (congrArg (fun q => ((E.obj W).sequence.ssData q).eInfty)
        (show (s+r+l,p.1+(s+r+l),p.2) =
          (s+m+(r+l-m),p.1+(s+m+(r+l-m)),p.2) by ext <;> dsimp <;> omega))) w) := by
  have hcommon : ∃ a : BiHom p.1 p.2 X,
      RepresentsInfinityClass cy p (s+m) y (a ≫ f) ∧
      RepresentsInfinityClass cz p (s+r) z (a ≫ h) := by
    rcases hsource with hfnc | hhnc
    · obtain ⟨_,ar,br,hab,hax,hbz⟩ := (tower_extension_iff Mh p s r x z).mp hleft
      let a := ((P.filtration X).F s p).arrow ar
      have hax' : RepresentsInfinityClass cx p s x a := ⟨ar,rfl,hax⟩
      refine ⟨a,target_of_any_source Mf p s m x y htop hfnc a hax',?_⟩
      exact ⟨br,hab.symm,hbz⟩
    · obtain ⟨_,ar,br,hab,hax,hby⟩ := (tower_extension_iff Mf p s m x y).mp htop
      let a := ((P.filtration X).F s p).arrow ar
      have hax' : RepresentsInfinityClass cx p s x a := ⟨ar,rfl,hax⟩
      exact ⟨a,⟨br,hab.symm,hby⟩,target_of_any_source Mh p s r x z hleft hhnc a hax'⟩
  obtain ⟨a,hay,haz⟩ := hcommon
  have hqzero := target_of_any_source Mk p (s+m) (c-1) y 0 hzero hzeroNC (a≫f) hay
  have hhigh := (Paper.represents_zero_iff p (s+m+(c-1)) ((a≫f)≫k)).mp hqzero
  have hhigh' : (a≫h)≫j ∈ P.filtrationSubmodule W (s+m+c) p := by
    have hi : s+m+(c-1)+1=s+m+c := by omega
    rw [hi] at hhigh
    simpa only [Category.assoc,←hcomm] using hhigh
  have hw := target_of_source_in_essential_range Mj p (s+r) l (s+m+c)
    (by omega) z w hbottom hbottomNC (a≫h) haz hhigh'
  have hw' : RepresentsInfinityClass cw p (s+r+l) w ((a≫f)≫k) := by
    simpa only [Category.assoc,hcomm] using hw
  obtain ⟨br,hbr,hby⟩ := hay
  obtain ⟨dr,hdr,hdw⟩ := hw'
  have ht : s+r+l = s+m+(r+l-m) := by omega
  have transport_target (v v' : ℤ) (hv : v=v')
      (w₀ : ((E.obj W).sequence.ssData (v,p.1+v,p.2)).eInfty)
      (b : BiHom p.1 p.2 W) (hb : RepresentsInfinityClass cw p v w₀ b) :
      RepresentsInfinityClass cw p v'
        ((eqToHom (congrArg (fun q => ((E.obj W).sequence.ssData q).eInfty)
          (show (v,p.1+v,p.2)=(v',p.1+v',p.2) by rw [hv]))) w₀) b := by
    subst v'
    exact hb
  have hw'' := transport_target _ _ ht w ((a≫f)≫k) ⟨dr,hdr,hdw⟩
  obtain ⟨dr',hdr',hdw'⟩ := hw''
  apply (tower_extension_iff Mk p (s+m) (r+l-m) y _).mpr
  exact ⟨by omega,br,dr',by rw [hbr,hdr'],hby,hdw'⟩

end ActualFilteredSquare


/-- The exact quotient-boundary square, with its full four-edge cutoff data.
The stem and synthetic weight remain fixed in every crossing quantifier. -/
private def QuotientBoundaryCutoffStatement (A B : SyntheticObject)
    (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (q : ℕ) : Prop :=
  let QA : SyntheticObject := .quotient q A
  let QB : SyntheticObject := .quotient q B
  let SA : SyntheticObject := .shift (1,-(q:ℤ)) A
  let SB : SyntheticObject := .shift (1,-(q:ℤ)) B
  let top := model.convergentMap QA QB (XModLambdaN.map g q)
  let left := model.convergentMap QA SA (absoluteBoundary (A.obj model.nu model.auxiliary) q)
  let bottom := model.convergentMap SA SB ((SyntheticCategory.biShift (1,-(q:ℤ))).map g)
  let right := model.convergentMap QB SB (absoluteBoundary (B.obj model.nu model.auxiliary) q)
  ∀ (p : ℤ × ℤ) (s M b L κ : ℤ)
    (_hM : 0 ≤ M) (_hb : 0 ≤ b) (_hL : 0 ≤ L)
    (_hκ : 0 < κ) (_hκD : κ ≤ b+L-M)
    (ξ : ((model.family.obj (QA.obj model.nu model.auxiliary)).sequence.ssData
      (s,p.1+s,p.2)).eInfty)
    (η : ((model.family.obj (QB.obj model.nu model.auxiliary)).sequence.ssData
      (s+M,p.1+(s+M),p.2)).eInfty)
    (ζ : ((model.family.obj (SA.obj model.nu model.auxiliary)).sequence.ssData
      (s+b,p.1+(s+b),p.2)).eInfty)
    (ω : ((model.family.obj (SB.obj model.nu model.auxiliary)).sequence.ssData
      (s+b+L,p.1+(s+b+L),p.2)).eInfty),
  TowerExtensionEquation top p s M ξ η →
  TowerExtensionEquation left p s b ξ ζ →
  TowerExtensionEquation bottom p (s+b) L ζ ω →
  (TowerNoCrossing top p s M ∨ TowerNoCrossing left p s b) →
  EssentialNoCrossingRange bottom p (s+b) L (s+M+κ) →
  TowerExtensionEquation right p (s+M) (κ-1) η 0 →
  TowerNoCrossing right p (s+M) (κ-1) →
  TowerExtensionEquation right p (s+M) (b+L-M) η
    ((eqToHom (congrArg (fun q => ((model.family.obj
      (SB.obj model.nu model.auxiliary)).sequence.ssData q).eInfty)
      (show (s+b+L,p.1+(s+b+L),p.2) =
        (s+M+(b+L-M),p.1+(s+M+(b+L-M)),p.2) by ext <;> dsimp <;> omega))) ω)

/-- Complete content of the cutoff-square remark, valid for the actual
quotient and weight, rather than only for a classical abstract square. -/
private theorem quotientBoundaryCutoff (A B : SyntheticObject)
    (g : A.obj model.nu model.auxiliary ⟶ B.obj model.nu model.auxiliary)
    (q : ℕ) : QuotientBoundaryCutoffStatement A B g q := by
  unfold QuotientBoundaryCutoffStatement
  intro QA QB SA SB top left bottom right p s M b L κ hM hb hL hκ hκD
    ξ η ζ ω htop hleft hbottom hsource hbottomNC hzero hzeroNC
  exact four_edge_cutoff top left bottom right (absoluteBoundary_natural g q)
    p s M b L κ hM hb hL hκ hκD ξ η ζ ω
    htop hleft hbottom hsource hbottomNC hzero hzeroNC

/-- AimPaper Remark 6.5, in the actual normalized Leibniz square. -/
private theorem cutoffLeibnizSquare
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (q : ℕ) : QuotientBoundaryCutoffStatement
      (extensionSourceObject model X Y f) (.nu Y)
      (model.normalizedMap X Y f).map q :=
  quotientBoundaryCutoff _ _ _ q

/-- SS cutoff-square rule at an arbitrary retained lambda level.
Only the actual square conclusion is asserted; a classical decoder needs
its own qualified labels and boundary comparison. -/
private theorem ssCutoffSquareAtLevel
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page level : ℕ) (_hpage : 2 ≤ page) : QuotientBoundaryCutoffStatement
      (extensionSourceObject model X Y f) (.nu Y)
      (model.normalizedMap X Y f).map (page+level-1) :=
  cutoffLeibnizSquare X Y f (page+level-1)

/-- The exponent calculation accompanying the cutoff square; it does not
assert the label or boundary comparisons needed for classical decoding. -/
private theorem cutoff_boundary_exponents (n k b L M e : ℤ)
    (_hn : 2 ≤ n) (hnb : n ≤ b) (hk : 0 ≤ k)
    (heM : e ≤ M) (hM : M ≤ n-2+e) (heL : e ≤ L) :
    (b+L-M)-(n+k-1)-1+(k+M-e)=b-n+L-e ∧
    2 ≤ b+L-M ∧ 0 ≤ k+M-e ∧ k+M-e < n+k-1 := by
  omega

/-- The complete zero-input-level Leibniz specialization.  The output is a
classical differential, with both permanent labels and actual-map crossing
conditions retained. -/
private theorem ssLeibnizAtLevelZero
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (page : ℕ) (b M L s t : ℤ)
    (x : Ambient model X (s,t)) (y : Ambient model Y (s+M,t+M))
    (u : Ambient model X (s+b,t+b-1))
    (v : Ambient model Y (s+b+L,t+b-1+L))
    (hpage : 2 ≤ page) (hpageb : (page:ℤ) ≤ b)
    (hM : (normalizedExponent model.classicalTower f:ℤ) ≤ M)
    (hMUpper : M ≤ (page:ℤ)-2+normalizedExponent model.classicalTower f)
    (hL : (normalizedExponent model.classicalTower f:ℤ) ≤ L)
    (hu : IsPermanent model X (s+b,t+b-1) u)
    (hv : IsPermanent model Y (s+b+L,t+b-1+L) v)
    (hdx : DifferentialAt model X b (s,t) (s+b,t+b-1) x u)
    (hFinite : KIP126.ProofTools.Standard.LevelFiniteExtension X Y f page 0 M s t x y)
    (hInfinity : InfiniteExtension model X Y f L (s+b) (t+b-1) u v)
    (hsource : KIP126.ProofTools.Standard.LevelBoundaryNoCrossing X Y f page 0 b s t ∨
      KIP126.ProofTools.Standard.LevelFiniteNoCrossing X Y f page 0 M s t)
    (hbottom : KIP126.ProofTools.Standard.LevelBottomNoCrossing X Y f page 0 b L s t) :
    DifferentialAt model Y (b+L-M) (s+M,t+M) (s+b+L,t+b-1+L) y v :=
  KIP126.ProofTools.Standard.generalizedLeibnizAtLevel X Y f page 0 b M L s t
    x y u v hpage hpageb hM hMUpper hL hu hv hdx hFinite hInfinity hsource hbottom

/-- The full finite Mahowald proposition specialized at i=j=0.  Its
conclusion retains all three common representatives, signed image equations,
detections, cycle improvement and output relation; the output level is k. -/
private def FiniteMahowaldZeroInputStatement
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) : Prop :=
  let shiftFinitePageLabel (V : SyntheticObject) (δ : ℤ × ℤ)
      (q : Tridegree)
      (x : (model.family.obj (V.obj model.nu model.auxiliary)).E₂ q) :
      (model.family.obj ((SyntheticObject.shift δ V).obj model.nu model.auxiliary)).E₂
        (q.1,q.2.1+δ.1,q.2.2+δ.2) :=
    regradeE2 (by
      ext <;> dsimp
      omega)
      ((KIP126.AdamsSynthetic.Standard.shift_page δ V 2 (by decide)
        (q.2.1-q.1,q.2.2) q.1).hom (regradeE2 (by ext <;> simp) x))
  ∀ (_hT : NormalizedTriangleCompatible model T he)
    (n₁ m₁ k : ℕ) (_hn₁ : 0 < n₁) (s t : ℤ),
  let i : ℕ := 0
  let j : ℕ := 0
  let hj : j < n₁ := _hn₁
  let ef : ℤ := normalizedExponent model.classicalTower T.f
  let eg : ℤ := normalizedExponent model.classicalTower T.g
  let eh : ℤ := normalizedExponent model.classicalTower T.h
  let n : ℤ := n₁+ef
  let m : ℤ := m₁+eg
  let l : ℤ := k+eh
  let r : ℤ := n+m+l
  let A : ℕ := n₁+k+i-j
  let B : ℕ := m₁+j+1
  let N : ℕ := A+B
  let K : ℕ := i+k
  let J : ℕ := A+j
  let Q : ℕ := N-K
  let V := normalizedTriangle model T he
  let VX : SyntheticObject := .shift (0,ef) (.nu T.X)
  let VY : SyntheticObject := .nu T.Y
  let VZ : SyntheticObject := .shift (0,-eg) (.nu T.Z)
  let QA : SyntheticObject := .quotient A VZ
  let HA : SyntheticObject := .shift (1,0) (.quotient A VX)
  let DB : SyntheticObject := .shift (1,0) (.shift (0,-(A:ℤ)) (.quotient B VZ))
  let GB : SyntheticObject := .shift (1,0) (.shift (0,-(A:ℤ)) (.quotient B VY))
  let CN : SyntheticObject := .shift (1,0) (.quotient N VX)
  let FN : SyntheticObject := .shift (1,0) (.quotient N VY)
  let p : ℤ × ℤ := (t-s,t-i-eg)
  let hA : 0 < A := by dsimp [A]; omega
  let hAN : A < N := by dsimp [N,B]; omega
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(A:ℤ))
  let LZ := (model.quotients.tower V.obj₃).triangle hA hAN
  let LY := (model.quotients.tower V.obj₂).triangle hA hAN
  let delta : XModLambdaN V.obj₃ A ⟶ (F.obj (XModLambdaN V.obj₃ B))⟦(1:ℤ)⟧ := by
    simpa only [N,Nat.add_sub_cancel_left] using LZ.delta
  let lambdaY : F.obj (XModLambdaN V.obj₂ B) ⟶ XModLambdaN V.obj₂ N := by
    simpa only [N,Nat.add_sub_cancel_left] using LY.lambdaMap
  ∀ (exA : XModLambdaN (V.obj₁⟦(1:ℤ)⟧) A ≅
      (XModLambdaN V.obj₁ A)⟦(1:ℤ)⟧)
    (exN : XModLambdaN (V.obj₁⟦(1:ℤ)⟧) N ≅
      (XModLambdaN V.obj₁ N)⟦(1:ℤ)⟧)
    (eyN : XModLambdaN (V.obj₂⟦(1:ℤ)⟧) N ≅
      (XModLambdaN V.obj₂ N)⟦(1:ℤ)⟧),
  XModLambdaN.incl _ A ≫ exA.hom =
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₁ A) →
  XModLambdaN.incl _ N ≫ exN.hom =
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₁ N) →
  XModLambdaN.incl _ N ≫ eyN.hom =
    (shiftFunctor SyntheticSpectrum (1:ℤ)).map (XModLambdaN.incl V.obj₂ N) →
  let hmap : QA.obj model.nu model.auxiliary ⟶ HA.obj model.nu model.auxiliary :=
    XModLambdaN.map V.mor₃ A ≫ exA.hom ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _
  let dmap : QA.obj model.nu model.auxiliary ⟶ DB.obj model.nu model.auxiliary :=
    delta ≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _
  let gmap : GB.obj model.nu model.auxiliary ⟶ DB.obj model.nu model.auxiliary :=
    (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).hom.app _ ≫
      (shiftFunctor SyntheticSpectrum (1:ℤ)).map (F.map (XModLambdaN.map V.mor₂ B)) ≫
      (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _
  let Mh := model.convergentMap QA HA hmap
  let Md := model.convergentMap QA DB dmap
  let Mg := model.convergentMap GB DB gmap
  ∀ (xbar : Ambient model T.Z (s,t))
    (x : Ambient model T.X (s+l,t+l-1))
    (y : Ambient model T.Y (s+l+n,t+l+n-1))
    (ybar : Ambient model T.Z (s+r,t+r-1)),
  IsCycle model T.Z (r-1) (s,t) xbar →
  DifferentialAt model T.Z r (s,t) (s+r,t+r-1) xbar ybar →
  IsPermanent model T.Z (s+r,t+r-1) ybar →
  IsCycle model T.X (n₁-j) (s+l,t+l-1) x →
  IsCycle model T.Y (m₁+1) (s+l+n,t+l+n-1) y →
  let xbarA : (model.family.obj (QA.obj model.nu model.auxiliary)).E₂
      (s,p.1+s,p.2) :=
    regradeE2 (by
      ext <;> dsimp [p]
      omega)
      (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.Z A (-eg) s t i xbar)
  let xA : (model.family.obj (HA.obj model.nu model.auxiliary)).E₂
      (s+l,p.1+(s+l),p.2) :=
    regradeE2 (by
      ext <;> dsimp [p,l,K,ef,eg,eh] at * <;> omega)
      (shiftFinitePageLabel (.quotient A VX) (1,0) _
        (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.X A ef (s+l) (t+l-1) K x))
  let yB : (model.family.obj (GB.obj model.nu model.auxiliary)).E₂
      (s+l+n,p.1+(s+l+n),p.2) :=
    regradeE2 (by
      have hja : j ≤ n₁+k+i := by omega
      ext <;> dsimp [p,l,n,A,ef,eg,eh] at * <;>
        (try simp only [Nat.cast_sub hja,Nat.cast_add]) <;> omega)
      (shiftFinitePageLabel (.shift (0,-(A:ℤ)) (.quotient B VY)) (1,0) _
        (shiftFinitePageLabel (.quotient B VY) (0,-(A:ℤ)) _
          (finiteTargetLabel model T.Y B (s+l+n) (t+l+n-1) j y)))
  let ybarB : (model.family.obj (DB.obj model.nu model.auxiliary)).E₂
      (s+r,p.1+(s+r),p.2) :=
    regradeE2 (by
      have hja : j ≤ n₁+k+i := by omega
      ext <;> dsimp [p,r,l,n,m,A,B,ef,eg,eh] at * <;>
        (try simp only [Nat.cast_sub hja,Nat.cast_add]) <;> omega)
      (shiftFinitePageLabel (.shift (0,-(A:ℤ)) (.quotient B VZ)) (1,0) _
        (shiftFinitePageLabel (.quotient B VZ) (0,-(A:ℤ)) _
          (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.Z B (-eg) (s+r) (t+r-1) (B-1) ybar)))
  let xN : (model.family.obj (CN.obj model.nu model.auxiliary)).E₂
      (s+l,p.1+(s+l),p.2) :=
    regradeE2 (by
      ext <;> dsimp [p,l,K,ef,eg,eh] at * <;> omega)
      (shiftFinitePageLabel (.quotient N VX) (1,0) _
        (KIP126.ProofTools.Standard.levelFiniteSourceLabel T.X N ef (s+l) (t+l-1) K x))
  let yN : (model.family.obj (FN.obj model.nu model.auxiliary)).E₂
      (s+l+n,p.1+(s+l+n),p.2) :=
    regradeE2 (by
      have hja : j ≤ n₁+k+i := by omega
      ext <;> dsimp [p,l,n,A,J,ef,eg,eh] at * <;>
        (try simp only [Nat.cast_sub hja,Nat.cast_add]) <;> omega)
      (shiftFinitePageLabel (.quotient N VY) (1,0) _
        (finiteTargetLabel model T.Y N (s+l+n) (t+l+n-1) J y))
  ∀ (e0 : ((model.family.obj (QA.obj model.nu model.auxiliary)).sequence.ssData
        (s,p.1+s,p.2)).eInfty)
    (ex : ((model.family.obj (HA.obj model.nu model.auxiliary)).sequence.ssData
        (s+l,p.1+(s+l),p.2)).eInfty)
    (ey : ((model.family.obj (GB.obj model.nu model.auxiliary)).sequence.ssData
        (s+l+n,p.1+(s+l+n),p.2)).eInfty)
    (ez : ((model.family.obj (DB.obj model.nu model.auxiliary)).sequence.ssData
        (s+r,p.1+(s+r),p.2)).eInfty),
  HasInfinityRepresentative _ 2 _ xbarA e0 →
  HasInfinityRepresentative _ 2 _ xA ex →
  HasInfinityRepresentative _ 2 _ yB ey →
  HasInfinityRepresentative _ 2 _ ybarB ez →
  TowerExtensionEquation Mh p s l e0 ex →
  TowerExtensionEquation Md p s r e0 ez →
  TowerExtensionEquation Mg p (s+l+n) m ey
    ((eqToHom (congrArg (fun q =>
      ((model.family.obj (DB.obj model.nu model.auxiliary)).sequence.ssData q).eInfty)
      (show (s+r,p.1+(s+r),p.2)=(s+l+n+m,p.1+(s+l+n+m),p.2) by
        ext <;> dsimp [r] <;> omega))) ez) →
  (ActualNoCrossing Mh p s l ∨ ActualNoCrossing Md p s r) →
  ∃ (a : BiHom p.1 p.2 (XModLambdaN V.obj₃ A))
    (b : BiHom p.1 p.2 ((F.obj (XModLambdaN V.obj₂ B))⟦(1:ℤ)⟧))
    (c : BiHom p.1 p.2 (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) N)),
    Detects (model.convergence QA) (s,p.1+s,p.2) xbarA
      (homotopyRegrade (by dsimp [p]; omega) rfl a) ∧
    Detects (model.convergence HA) (s+l,p.1+(s+l),p.2) xA
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ hmap)) ∧
    Detects (model.convergence DB) (s+r,p.1+(s+r),p.2) ybarB
      (homotopyRegrade (by dsimp; omega) rfl (a ≫ dmap)) ∧
    Detects (model.convergence GB) (s+l+n,p.1+(s+l+n),p.2) yB
      (homotopyRegrade (by dsimp; omega) rfl
        (b ≫ (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    Detects (model.convergence DB) (s+r,p.1+(s+r),p.2) ybarB
      (homotopyRegrade (by dsimp; omega) rfl
        (b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          (F.map (XModLambdaN.map V.mor₂ B)) ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    a ≫ delta = b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
      (F.map (XModLambdaN.map V.mor₂ B)) ∧
    c ≫ (model.quotients.tower (V.obj₁⟦(1:ℤ)⟧)).rho A N hAN.le =
      a ≫ XModLambdaN.map V.mor₃ A ∧
    c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) N ≫
      eyN.hom = -(b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map lambdaY) ∧
    Detects (model.convergence CN) (s+l,p.1+(s+l),p.2) xN
      (homotopyRegrade (by dsimp; omega) rfl
        (c ≫ exN.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    Detects (model.convergence FN) (s+l+n,p.1+(s+l+n),p.2) yN
      (homotopyRegrade (by dsimp; omega) rfl
        (c ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) N ≫
          eyN.hom ≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) ∧
    IsCycle model T.X Q (s+l,t+l-1) x ∧
    KIP126.ProofTools.Standard.LevelFiniteExtension T.X T.Y T.f
      (Q+1) K n (s+l) (t+l-1) x
      ((eqToHom (congrArg (fun q => (model.classical.obj
          (T.Y.obj model.auxiliary)).Page 2 q)
        (show (s+l+n,t+l+n-1)=(s+l+n,t+l-1+n) by ext <;> omega))) y)


private theorem ssMahowaldZeroInputLevels (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    FiniteMahowaldZeroInputStatement T he := by
  unfold FiniteMahowaldZeroInputStatement
  intro shiftFinitePageLabel hT n₁ m₁ k hn₁ s t
  exact KIP126.ProofTools.Standard.generalizedMahowaldAtLevel T he
    hT n₁ m₁ k 0 0 hn₁ hn₁ s t

end
end KIP126.ProofTools.Internal.ProgramRules

end
