module
import all KIP126.ProofTools.GeneralizedMahowald.FinalDivision
import all KIP126.ProofTools.GeneralizedMahowald.ExtensionImage
import all KIP126.ProofTools.GeneralizedMahowald.PageCalculus
import KIP126.E2Computation.Table.Dimensions
import all KIP126.ProofTools.GeneralizedLeibniz.CrossingRange

/-!
Exact-source diagnostic for MH2 (not a counterexample theorem).

Write k=l-e(h). The h-target is detected at lambda layer k, so its
E-infinity label is unchanged on adding B_(k+1). The first three results
below prove this while retaining the same finite witness. In contrast,
a positive-length f-extension of an exact source forces its normalized
leading E2 image to vanish. The last three results prove that obstruction.
Neither result constructs the missing simultaneous filtration correction.

The low-stem counterexample formalized in StatementReview.lean is the rotated nu triangle
  S^0 -> Cnu -> S^4 -> S^1,
with (ef,eg,eh)=(0,0,1), (n,m,l,s,t)=(1,0,2,1,16),
x=d_2(h_4)=h_0*h_3^2 in Ext^(3,17), and xBar=y=yBar=0.
Here i=2,q=1,k=1,Q=2. AimPaper/main.tex lines 880--898 record this
nonzero differential target. RotatedNuTriangle proves compatibility of the
selected normalized rotation. RotatedNuPremises proves all actual premises,
and BottomNuInjection proves the required bottom leading image is nonzero
by a Hom snake argument. StatementReview combines them into the unconditional
negation of the locked law, without invoking generalizedMahowald. The
original MH2 source site is retained pending user review of its statement.
No such facts are added as axioms, assumptions of MH2, or new obligations.

For comparison, Wu, arXiv:2606.02779v2, Theorem 4.23 retains a (j+l)-layer
extension. Remark 4.25 separately requires f(x)=0 on E2 and boundary
conditions to lower the layer. Remarks 3.3--3.4 do not impose essentiality
on the original extension. These statements locate the issue; they are
not imported as a proof of the locked GeneralizedMahowaldLaw.
-/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal KIP126.ProofTools.Internal.Leibniz
open KIP126.Core.SpectralSequence.FinitePageCalculus
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3000000

private theorem cycle_add_boundary (X : ClassicalObject) (r k : ℤ)
    (p : ℤ × ℤ) (x b : Ambient model X p)
    (hx : IsCycle model X r p x) (hb : b∈boundaries model X k p) :
    IsCycle model X r p (x+b) := by
  exact ⟨hx.1,(cycles model X r p).add_mem hx.2 (boundaries_le_cycles model X p k r hb)⟩

private theorem finite_target_rep_add_boundary (X : ClassicalObject)
    (q k : ℕ) (hkq : k<q) (s t : ℤ) (x b : Ambient model X (s,t))
    (hb : b∈boundaries model X (k+1) (s,t))
    (e : ((model.family.quotient (model.nu.functor.obj (X.obj model.auxiliary)) q).sequence.ssData
      (s,t,t-k)).eInfty)
    (hx : HasInfinityRepresentative _ 2 (s,t,t-k) (finiteTargetLabel model X q s t k x) e) :
    HasInfinityRepresentative _ 2 (s,t,t-k) (finiteTargetLabel model X q s t k (x+b)) e := by
  have hlabel (z : Ambient model X (s,t)) : nuWeightLabel model X s t (t-k) (by omega) z =
      targetNuLabel model X s t k z := by
    have hk' : (t-(t-k)).toNat=k := by omega
    have transport (a b : ℕ) (hab : a=b)
        (h : (s,t,t-a)=(s,t,t-b)) :
        regradeE2 h (targetNuLabel model X s t a z) = targetNuLabel model X s t b z := by
      subst b; rfl
    exact transport _ k hk' _
  have hrep := KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
    s t (t-k) (by omega) x e
  rw [hlabel] at hrep
  obtain ⟨hxc,hxe⟩ := hrep.mp hx
  have hbc : b∈cycles model X (q-t+(t-k)) (s,t) :=
    boundaries_le_cycles model X (s,t) (k+1) _ hb
  have hxbc := (cycles model X (q-t+(t-k)) (s,t)).add_mem hxc hbc
  have hb' : b∈boundaries model X (1+t-(t-k)) (s,t) := by
    convert hb using 1; congr 1; omega
  have hbzero : subquotientClass (cycles model X (q-t+(t-k)) (s,t))
      (boundaries model X (1+t-(t-k)) (s,t)) ⟨b,hbc⟩=0 :=
    (CrossingLabels.subquotient_zero_iff _ _ _).mpr hb'
  have hclass : subquotientClass (cycles model X (q-t+(t-k)) (s,t))
      (boundaries model X (1+t-(t-k)) (s,t)) ⟨x+b,hxbc⟩=
      subquotientClass (cycles model X (q-t+(t-k)) (s,t))
        (boundaries model X (1+t-(t-k)) (s,t)) ⟨x,hxc⟩ := by
    change subquotientClass _ _ (⟨x,hxc⟩+⟨b,hbc⟩)=_
    rw [map_add,hbzero,add_zero]
  have hrep' := KIP126.Literature.Standard.eInfinity_finite_labels X q (by omega)
    s t (t-k) (by omega) (x+b) e
  rw [hlabel] at hrep'
  exact hrep'.mpr ⟨hxbc,hxe.trans hclass.symm⟩

private def finite_extension_target_add_boundary (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (x : Ambient model X (s,t))
    (y b : Ambient model Y (s+n,t+n))
    (W : FiniteExtensionWitness model X Y f r n s t x y)
    (hb : b∈boundaries model Y (1+n-normalizedExponent model.classicalTower f) (s+n,t+n)) :
    FiniteExtensionWitness model X Y f r n s t x (y+b) := by
  let k : ℕ := (n-normalizedExponent model.classicalTower f).toNat
  have hk : (k:ℤ)=n-normalizedExponent model.classicalTower f :=
    Int.toNat_of_nonneg (by have := W.length_lower; omega)
  have hkq : k<r-1 := by have := W.length_upper; have := W.page_ge_two; omega
  have hb' : b∈boundaries model Y (k+1) (s+n,t+n) := by
    convert hb using 1; congr 1; omega
  have hcycle : ReachesPage (model.classical.obj (Y.obj model.auxiliary))
      ((r:ℤ)-n+normalizedExponent model.classicalTower f) (s+n,t+n) (y+b) := by
    have hyr := (isCycle_iff_reaches model Y _ W.target_page_ge_two (s+n,t+n) y).mpr W.target_cycle
    exact (isCycle_iff_reaches model Y _ W.target_page_ge_two (s+n,t+n) (y+b)).mp
      (cycle_add_boundary Y _ _ _ y b hyr hb)
  have hp : (s+n,t+n,(t+n)-(k:ℤ))=
      (s+n,(t-s)+(s+n),t+normalizedExponent model.classicalTower f) := by
    ext <;> dsimp <;> omega
  have repr {A : SyntheticAdamsSS} {p p' : Tridegree} (h : p=p')
      (z : A.E₂ p) (e : (A.sequence.ssData p').eInfty) :
      HasInfinityRepresentative A 2 p' (regradeE2 h z) e ↔
        HasInfinityRepresentative A 2 p z
          ((eqToHom (congrArg (fun p => (A.sequence.ssData p).eInfty) h.symm)) e) := by
    subst p'
    simp only [regradeE2,eqToHom_refl,ModuleCat.id_apply]
  have hwrep := W.target_rep
  change HasInfinityRepresentative _ 2 _
    (regradeE2 hp (finiteTargetLabel model Y (r-1) (s+n) (t+n) k y)) W.target at hwrep
  have hnativ := (repr hp _ _).mp hwrep
  have hnew := finite_target_rep_add_boundary Y (r-1) k hkq (s+n) (t+n) y b hb' _ hnativ
  refine { W with target_cycle := hcycle, target_rep := ?_ }
  change HasInfinityRepresentative _ 2 _
    (regradeE2 hp (finiteTargetLabel model Y (r-1) (s+n) (t+n) k (y+b))) W.target
  exact (repr hp _ _).mpr hnew

private theorem suspension_desuspends_add (X : ClassicalObject) (s t : ℤ)
    (sx sb : Ambient model (.shift 1 X) (s,t))
    (x b : Ambient model X (s,t-1))
    (hx : (model.classicalSuspension X).DesuspendsClass s t sx x)
    (hb : (model.classicalSuspension X).DesuspendsClass s t sb b) :
    (model.classicalSuspension X).DesuspendsClass s t (sx+sb) (x+b) := by
  obtain ⟨a,c,ha,hc,hac⟩ := hx
  obtain ⟨a',c',ha',hc',hac'⟩ := hb
  refine ⟨a+a',c+c',?_,?_,?_⟩
  · rw [map_add,ha,ha']
  · rw [map_add,hc,hc']
  · simpa only [map_add,Submodule.coe_add] using congrArg₂ (fun x y => x+y) hac hac'

private theorem infinite_source_label_add (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) (s t : ℤ)
    (x b : Ambient model X (s,t)) :
    infiniteSourceForExtension model X Y f s t (x+b)=
      infiniteSourceForExtension model X Y f s t x+
        infiniteSourceForExtension model X Y f s t b := by
  simp only [infiniteSourceForExtension,regradeE2,map_add]

/-- If both source labels admitted a positive extension, the normalized
leading E2 image of their exact boundary difference would have to vanish. -/
private theorem positive_extensions_force_boundary_image_zero (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (hn : 0<n)
    (x b : Ambient model X (s,t))
    (y y' : Ambient model Y (s+n,t+n))
    (hx : FiniteExtension model X Y f r n s t x y)
    (hxb : FiniteExtension model X Y f r n s t (x+b) y') :
    familyPageMap model.family (model.normalizedMap X Y f).map 2
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
      (infiniteSourceForExtension model X Y f s t b)=0 := by
  have h0 := positive_extension_map_e2_zero X Y f r n s t hn x y (Classical.choice hx)
  have h1 := positive_extension_map_e2_zero X Y f r n s t hn (x+b) y' (Classical.choice hxb)
  rw [infinite_source_label_add,map_add,h0,zero_add] at h1
  exact h1

private theorem nonzero_leading_image_no_positive_extension (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (hn : 0<n) (x : Ambient model X (s,t))
    (hx : familyPageMap model.family (model.normalizedMap X Y f).map 2
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
      (infiniteSourceForExtension model X Y f s t x)≠0) :
    ¬∃ y : Ambient model Y (s+n,t+n), FiniteExtension model X Y f r n s t x y := by
  rintro ⟨y,hy⟩
  exact hx (positive_extension_map_e2_zero X Y f r n s t hn x y (Classical.choice hy))

private theorem nonzero_boundary_image_obstructs_translation (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (r : ℕ) (n s t : ℤ) (hn : 0<n)
    (x b : Ambient model X (s,t))
    (y : Ambient model Y (s+n,t+n))
    (hx : FiniteExtension model X Y f r n s t x y)
    (hb : familyPageMap model.family (model.normalizedMap X Y f).map 2
      (s,(t-s)+s,t+normalizedExponent model.classicalTower f)
      (infiniteSourceForExtension model X Y f s t b)≠0) :
    ¬∃ y' : Ambient model Y (s+n,t+n), FiniteExtension model X Y f r n s t (x+b) y' := by
  rintro ⟨y',hy'⟩
  exact hb (positive_extensions_force_boundary_image_zero X Y f r n s t hn x b y y' hx hy')

/- The low-stem boundary and source vanishing are consequences of existing
public Literature/Computation interfaces. The bottom-image comparison and
normalized rotation are proved in their separate private review modules. -/
private abbrev mh2BoundaryClass : Ambient model .sphere (3,17) := oneLineTarget model 4

private theorem mh2BoundaryClass_differential :
    HasNonzeroDifferential model.classical.sphere 2 (1,16) (3,17)
      (model.standardClasses.standardHi 4) mh2BoundaryClass := by
  exact KIP126.Literature.Standard.adamsOneLine_d2 4 (by decide)

private theorem mh2BoundaryClass_nonzero : mh2BoundaryClass ≠ 0 := by
  intro hz
  obtain ⟨_,_,yr,_,hyr,_,hne⟩ := mh2BoundaryClass_differential
  apply hne
  rw [hz] at hyr
  exact represents_unique hyr (RepresentsOnPage.zero (by decide))

private theorem mh2BoundaryClass_boundary :
    mh2BoundaryClass ∈ boundaries model .sphere 2 (3,17) := by
  have hd : HasDifferential model.classical.sphere 2 (1,16) (3,17)
      (model.standardClasses.standardHi 4) mh2BoundaryClass := by
    obtain ⟨h,xr,yr,hx,hy,he,_⟩ := mh2BoundaryClass_differential
    exact ⟨h,xr,yr,hx,hy,he⟩
  exact represents_zero_mem_boundary model .sphere 3 (3,17) mh2BoundaryClass
    (differential_target_later_zero (by rw [model.classical.firstPage]) (by decide) hd)

private theorem sphere_ext_two_thirteen_zero (x : Ambient model .sphere (2,13)) : x=0 := by
  let e := KIP126.Computation.Standard.coordinates 2 13 (by decide)
  have hn : KIP126.Computation.Standard.archive.basisCount 2 13 = 0 :=
    (KIP126.Computation.Table.archive_dimension 2 13 (by decide)).trans (by decide)
  haveI : Subsingleton (Fin (KIP126.Computation.Standard.archive.basisCount 2 13) →₀ ZMod 2) := by
    rw [hn]
    infer_instance
  apply e.injective
  exact Subsingleton.elim _ _


end
end KIP126.ProofTools.Internal.Mahowald
