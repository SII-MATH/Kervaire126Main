module
public import KIP126.Def.ProofTools.Standard
public import KIP126.Def.Computation
import all KIP126.Main.Internal.NuThree.ZeroExtensions
import all KIP126.Main.Internal.NuThree.Suspension
import all KIP126.Main.Internal.NuThree.ClassicalZero
/-! The Cν application of generalized Mahowald, NuFifth:1039–1168
at bbac1fc05843 (MIT). The finite calculation is the same actual d₃ and
connecting-arrow comparison delivered by Computation.Standard. -/
@[expose] section
namespace KIP126.Main.Internal.NuThree
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.AdamsSynthetic KIP126.Kervaire.Route
open KIP126.Core.SpectralSequence KIP126.Core.SpectralSequence.FinitePageCalculus
open KIP126.Literature KIP126.ProofTools KIP126.ProofTools.Operations
open KIP126.AdamsSynthetic.Standard (model)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

private theorem boundary_permanent (X : ClassicalObject) (p : ℤ×ℤ) (c : ℤ)
    (x : Ambient model X p) (hx : x∈boundaries model X c p) : IsPermanent model X p x := by
  obtain ⟨b,rfl⟩ := hx
  let D := (model.classical.obj (X.obj model.auxiliary)).ssData p
  have h : D.B (↑(c-1).toNat)≤D.Z ⊤ := (D.B_mono le_top).trans (D.B_le_Z ⊤)
  refine ⟨(Subobject.ofLE _ _ h) b,?_⟩
  change (Subobject.ofLE _ _ h ≫ cycleLabel model X ⊤ p) b=boundaryLabel model X _ p b
  simp only [cycleLabel,boundaryLabel,D,←Category.assoc,Subobject.ofLE_comp_ofLE]

private theorem differential_target_permanent (X : ClassicalObject)
    {r : ℤ} {p q : ℤ×ℤ} {x : Ambient model X p} {y : Ambient model X q}
    (h : DifferentialAt model X r p q x y) : IsPermanent model X q y := by
  have hz := differential_target_later_zero
    (by rw [model.classical.firstPage]; exact h.1) (by omega : r<r+1) h.2
  exact boundary_permanent X q (r+1-1) y (represents_zero_mem_boundary model X (r+1) q y hz)

private theorem classical_e2_comp_zero {X Y Z : KIP126.AdamsSynthetic.Standard.Spectrum}
    (f : X⟶Y) (g : Y⟶Z) (h : f≫g=0) (p : ℤ×ℤ)
    (x : (model.classical.obj X).Page 2 p) :
    model.classical.pageMap g 2 p (model.classical.pageMap f 2 p x)=0 := by
  change ((model.classical.map f).pageMap 2 p ≫ (model.classical.map g).pageMap 2 p) x=0
  rw [←SpectralSequenceMorphism.pageMap_comp,←model.classical.map_comp,h]
  exact classical_page_zero p x

private theorem cofiber_source_top :
    model.classical.pageMap (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 2 (8,134)
      KIP126.Computation.Standard.cofiberSource =
    model.classical.pageMap (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 2 (8,134)
      KIP126.Computation.Standard.topCell := by
  have hz : HasFunctorialCofiber.cofibι model.auxiliary.nuMap≫
      HasFunctorialCofiber.cofibδ model.auxiliary.nuMap=0 :=
    comp_distTriang_mor_zero₂₃ _ (HasFunctorialCofiber.cofib_distinguished model.auxiliary.nuMap)
  have kill (a : model.classical.sphere.Page 2 (8,134)) :
      model.classical.pageMap (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 2 (8,134)
        (KIP126.Computation.Standard.bottom 8 134 a)=0 :=
    classical_e2_comp_zero _ _ hz (8,134) a
  rw [KIP126.Computation.Standard.cofiberSource,map_add,map_add,kill,kill,add_zero,add_zero]

private theorem cnu_mahowald_finite :
    ∃ (x : (model.classical.obj (Sphere 3)).Page 2 (8,133))
      (y' : model.classical.sphere.Page 2 (11,136)),
      FiniteExtension model (.shift 3 .sphere) .sphere model.auxiliary.nuMap 4 3 8 133 x y' ∧
      Congruent model .sphere 3 (11,136) y' KIP126.Computation.Standard.Y := by
  let xb := KIP126.Computation.Standard.cofiberSource
  let y := KIP126.Computation.Standard.Y
  let yb := KIP126.Computation.Standard.bottom 11 136 y
  have hd : DifferentialAt model .nuCofiber 3 (8,134) (11,136) xb yb :=
    ⟨by decide,KIP126.Computation.Standard.cofiber_d3.toHasDifferential⟩
  obtain ⟨_,xr,yr,hxr,_,_⟩ := hd.2
  have hxbcycle : IsCycle model .nuCofiber 2 (8,134) xb :=
    (isCycle_iff_reaches model .nuCofiber 3 (by decide) (8,134) xb).mpr ⟨xr,hxr⟩
  have hybper := differential_target_permanent .nuCofiber hd
  obtain ⟨a3,a2,a1,hdesc,_⟩ := KIP126.Computation.Standard.top_comparison
  let sx := model.classical.pageMap (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 2 (8,134) xb
  have hdesc' : (model.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134 sx a3 := by
    dsimp only [sx,xb]
    rw [cofiber_source_top]
    exact hdesc
  have hsx : IsCycle model (.shift 1 (.shift 3 .sphere)) 2 (8,134) sx :=
    (isCycle_iff_reaches model (.shift 1 (.shift 3 .sphere)) 3 (by decide) (8,134) sx).mpr
      (classical_page_reaches .nuCofiber (.shift 1 (.shift 3 .sphere))
        (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 3 8 134 xb ⟨xr,hxr⟩)
  have ha3 := desuspendsClass_isCycle (.shift 3 .sphere) 2 8 134 sx a3 hdesc' hsx
  have top := finite_zero_extension_8 .nuCofiber (.shift 1 (.shift 3 .sphere))
    (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap)
    KIP126.Literature.Standard.nuCofiber_top_exponent xb hxbcycle.2
  have hycycle : IsCycle model .sphere 1 (11,136) y :=
    (isCycle_iff_reaches model .sphere 2 (by decide) (11,136) y).mpr ⟨y,represents_two_self y⟩
  have bot : FiniteExtension model .sphere .nuCofiber
      (HasFunctorialCofiber.cofibι model.auxiliary.nuMap) 2 0 11 136 y yb :=
    finite_zero_extension_11 .sphere .nuCofiber
      (HasFunctorialCofiber.cofibι model.auxiliary.nuMap)
      KIP126.Literature.Standard.nuCofiber_bottom_exponent y hycycle.2
  have hresult := KIP126.ProofTools.Standard.nuCofiberMahowaldZeroLayer a3 y xb yb sx
  have hnc : FiniteNoCrossing model .nuCofiber (.shift 1 (.shift 3 .sphere))
      (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 3 0 8 134 := by
    rintro ⟨a,b,ha,_,hb,_⟩
    have hnonneg : 0≤(normalizedExponent model.classicalTower
      (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap):ℤ) := Nat.cast_nonneg _
    omega
  obtain ⟨_,yy,hyy,hcong⟩ := hresult
    ha3 hycycle hxbcycle hybper hdesc' top hd (Or.inl hnc) bot
  exact ⟨a3,yy,hyy,hcong⟩
end
end KIP126.Main.Internal.NuThree
