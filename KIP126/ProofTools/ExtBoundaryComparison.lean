module

public import KIP126.ProofTools.MahowaldLeibniz
public import KIP126.ProofTools.BlueprintTheorems
public import KIP126.Literature.Standard.ExtBoundary
import KIP126.Literature.Standard.FiniteQuotientNormalized
import all KIP126.ProofTools.MahowaldLeibniz.Filtration
import all KIP126.ProofTools.MahowaldLeibniz.FixedModel
import all KIP126.ProofTools.MahowaldLeibniz.TerminalSquare
import all KIP126.ProofTools.GeneralizedMahowald.SuspensionClassLabels
import all KIP126.ProofTools.LastLayerComparison.ExactnessCoordinates
import all KIP126.ProofTools.ExtBoundaryComparison.HomologySES

/-! The actual normalized quotient boundary and its exactness.

These lemmas use the same normalized triangle as the composition theorem.
They do not identify its quotient boundary with a separately constructed
Steenrod-comodule Ext connecting homomorphism.
-/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route KIP126.Literature
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The normalized first-quotient operation is an actual additive map. -/
public def cofiberFirstQuotientBoundaryHom
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (s t : ℤ) :
    KIP126.ProofTools.Ambient model T.X (s,t) →+
      KIP126.ProofTools.Ambient model T.Y (s+1,t+1) where
  toFun := KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary T hf s t
  map_zero' := by
    simp only [KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary,
      map_zero, zero_comp]
    have zero_regrade {A : SyntheticSpectrum} {m m' w w' : ℤ}
        (hm : m=m') (hw : w=w') :
        homotopyRegrade hm hw (0 : BiHom m w A)=0 := by
      subst m'; subst w'; rfl
    rw [zero_regrade, map_zero]
  map_add' a b := by
    simp only [KIP126.ProofTools.Standard.cofiberFirstQuotientBoundary,
      map_add, Preadditive.add_comp]
    have add_regrade {A : SyntheticSpectrum} {m m' w w' : ℤ}
        (hm : m=m') (hw : w=w') (u v : BiHom m w A) :
        homotopyRegrade hm hw (u+v)=
          homotopyRegrade hm hw u+homotopyRegrade hm hw v := by
      subst m'; subst w'; rfl
    rw [add_regrade, map_add]

end
end KIP126.ProofTools.Standard



namespace KIP126.ProofTools.Internal.ExtBoundaryComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.MahowaldLeibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The classical desuspension is uniquely determined by the same tower
comparison; no independent E₂ isomorphism is selected. -/
private def classicalDesuspensionHom (X : ClassicalObject) (s t : ℤ) :
    KIP126.ProofTools.Ambient model (.shift 1 X) (s,t) →+
      KIP126.ProofTools.Ambient model X (s,t-1) where
  toFun sx := Classical.choose (exists_desuspendsClass X s t sx)
  map_zero' := (desuspendsClass_eq_zero_iff X s t 0 _
    (Classical.choose_spec (exists_desuspendsClass X s t 0))).mp rfl
  map_add' sx sy := by
    exact (desuspendsClass_eq_iff X s t (sx+sy) (sx+sy) _ _
      (Classical.choose_spec (exists_desuspendsClass X s t (sx+sy)))
      (suspension_desuspends_add X s t sx sy _ _
        (Classical.choose_spec (exists_desuspendsClass X s t sx))
        (Classical.choose_spec (exists_desuspendsClass X s t sy)))).mp rfl

private theorem classicalDesuspensionHom_spec (X : ClassicalObject) (s t : ℤ)
    (sx : KIP126.ProofTools.Ambient model (.shift 1 X) (s,t)) :
    (model.classicalSuspension X).DesuspendsClass s t sx
      (classicalDesuspensionHom X s t sx) :=
  Classical.choose_spec (exists_desuspendsClass X s t sx)

/-- The ordinary h₂ map followed by actual classical desuspension. -/
private def classicalTriangleHMapHom
    (T : TriangleData model.auxiliary) (s t : ℤ) :
    KIP126.ProofTools.Ambient model T.Z (s,t) →+
      KIP126.ProofTools.Ambient model T.X (s,t-1) where
  toFun z := classicalDesuspensionHom T.X s t
    ((model.classical.map T.h).pageMap 2 (s,t) z)
  map_zero' := by rw [map_zero, map_zero]
  map_add' a b := by rw [map_add, map_add]

private theorem classicalTriangleHMapHom_spec
    (T : TriangleData model.auxiliary) (s t : ℤ)
    (z : KIP126.ProofTools.Ambient model T.Z (s,t)) :
    (model.classicalSuspension T.X).DesuspendsClass s t
      ((model.classical.map T.h).pageMap 2 (s,t) z)
      (classicalTriangleHMapHom T s t z) :=
  classicalDesuspensionHom_spec T.X s t _

/-- Exactness retains the actual quotient connecting arrow, including its
sign and the selected inclusion-compatible suspension comparison. -/
private theorem normalized_quotient_boundary_exact
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+
      normalizedExponent model.classicalTower T.h=1)
    (hT : NormalizedTriangleCompatible model T he)
    (q : ℕ) (hq : 0<q) (m w : ℤ) :
    let N := normalizedTriangle model T he
    ∀ a : BiHom m w (XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q),
      a ≫ XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q=0 ↔
      ∃ b : BiHom m w (XModLambdaN N.obj₃ q),
        b ≫ XModLambdaN.map N.mor₃ q=a := by
  let N := normalizedTriangle model T he
  obtain ⟨esusp, _, hrow⟩ :=
    KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row T he hT q hq
  let R := Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
    (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q ≫ esusp.hom))
  dsimp only []
  intro a
  constructor
  · intro ha
    obtain ⟨b,hb⟩ := Triangle.coyoneda_exact₃ R hrow a (by
      change a ≫ (-(_ ≫ esusp.hom))=0
      rw [Preadditive.comp_neg, ←Category.assoc, ha, zero_comp, neg_zero])
    exact ⟨b,hb.symm⟩
  · rintro ⟨b,rfl⟩
    apply (cancel_mono esusp.hom).mp
    have hz := comp_distTriang_mor_zero₂₃ R hrow
    change XModLambdaN.map N.mor₃ q ≫ (-(_ ≫ esusp.hom))=0 at hz
    rw [Preadditive.comp_neg, neg_eq_zero] at hz
    simpa only [Category.assoc, comp_zero, zero_comp] using
      congrArg (fun f => b ≫ f) hz

end
end KIP126.ProofTools.Internal.ExtBoundaryComparison



namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route
noncomputable section

/-- The actual ordinary E₂ map of h followed by desuspension in the
selected classical Adams tower. -/
@[no_expose] public def classicalTriangleHMapHom
    (T : TriangleData model.auxiliary) (s t : ℤ) :
    Ambient model T.Z (s,t+1) →+ Ambient model T.X (s,t) := by
  exact (congrArg (fun u : ℤ => Ambient model T.Z (s,t+1) →+
      Ambient model T.X (s,u)) (show t+1-1=t by omega)).mp
    (Internal.ExtBoundaryComparison.classicalTriangleHMapHom T s (t+1))

/-- The additive map above retains the original representative-level
meaning of the selected desuspension comparison. -/
private theorem classicalTriangleHMapHom_spec
    (T : TriangleData model.auxiliary) (s t : ℤ)
    (z : Ambient model T.Z (s,t+1)) :
    (model.classicalSuspension T.X).DesuspendsClass s (t+1)
      ((model.classical.map T.h).pageMap 2 (s,t+1) z)
      (by simpa only [show t+1-1=t by omega] using classicalTriangleHMapHom T s t z) := by
  have undo (n n' : ℤ) (hn : n=n')
      (f : Ambient model T.Z (s,t+1) →+ Ambient model T.X (s,n)) :
      (congrArg (fun u : ℤ => (Ambient model T.X (s,u) : Type)) hn).mpr
        (((congrArg (fun u : ℤ => Ambient model T.Z (s,t+1) →+
          Ambient model T.X (s,u)) hn).mp f) z)=f z := by
    subst n'; rfl
  change (model.classicalSuspension T.X).DesuspendsClass s (t+1)
    ((model.classical.map T.h).pageMap 2 (s,t+1) z)
    ((congrArg (fun u : ℤ => (Ambient model T.X (s,u) : Type))
      (show t+1-1=t by omega)).mpr
      (((congrArg (fun u : ℤ => Ambient model T.Z (s,t+1) →+
        Ambient model T.X (s,u)) (show t+1-1=t by omega)).mp
        (Internal.ExtBoundaryComparison.classicalTriangleHMapHom T s (t+1))) z))
  rw [undo (t+1-1) t (by omega)]
  exact Internal.ExtBoundaryComparison.classicalTriangleHMapHom_spec T s (t+1) z

end
end KIP126.ProofTools.Standard

namespace KIP126.ProofTools.Internal.ExtBoundaryComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.MahowaldLeibniz
open KIP126.ProofTools.Internal.Leibniz
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem nativeFirstLabel_surjective (X : ClassicalObject) (s t : ℤ) :
    Function.Surjective (nativeFirstLabel X s t) := by
  intro a
  let V := model.nu.functor.obj (X.obj model.auxiliary)
  obtain ⟨x, hx⟩ := firstLabel_surjective X s t
    (a ≫ XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app V) 1)
  refine ⟨x, ?_⟩
  unfold nativeFirstLabel
  rw [hx, Category.assoc, ← model.quotients.functoriality.map_comp,
    Iso.inv_hom_id_app, model.quotients.functoriality.map_id]
  simp only [Functor.id_obj, V, Category.comp_id]

private theorem nativeFirstLabel_injective (X : ClassicalObject) (s t : ℤ) :
    Function.Injective (nativeFirstLabel X s t) := by
  intro x y h
  rw [nativeFirstLabel_eq_regrade, nativeFirstLabel_eq_regrade] at h
  have h' := congrArg (fun a => a ≫
    XModLambdaN.map (SyntheticCategory.biShift_zero.inv.app _) 1) h
  simp only [Category.assoc, ←model.quotients.functoriality.map_comp,
    Iso.hom_inv_id_app, model.quotients.functoriality.map_id, Category.comp_id] at h'
  apply (model.firstQuotient X 0 s t).symm.injective
  exact homotopy_regrade_injective rfl (Int.add_zero t) h'

/-- The exact row in the actual suspended classical E₂ coordinates.
No Ext operation or arbitrary connecting matrix is substituted here. -/
private theorem suspended_normalized_boundary_exact
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ)+
      normalizedExponent model.classicalTower T.g+
      normalizedExponent model.classicalTower T.h=1)
    (hf : normalizedExponent model.classicalTower T.f=1)
    (hg : normalizedExponent model.classicalTower T.g=0)
    (hh : normalizedExponent model.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible model T he)
    (s t : ℤ) (sx : KIP126.ProofTools.Ambient model (.shift 1 T.X) (s,t+1)) :
    let N := normalizedTriangle model T he
    let E := normalizedSuspensionNativeIso T he hf
    (nativeFirstLabel (.shift 1 T.X) s (t+1) sx ≫
      XModLambdaN.map E.inv 1) ≫
        XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) 1=0 ↔
    ∃ z : KIP126.ProofTools.Ambient model T.Z (s,t+1),
      (model.classical.map T.h).pageMap 2 (s,t+1) z=sx := by
  dsimp only []
  let N := normalizedTriangle model T he
  let E := normalizedSuspensionNativeIso T he hf
  let EZ := normalizedThirdZeroIso T he hg
  let Q := model.quotients.functoriality.functor 1
  have hmap : XModLambdaN.map N.mor₃ 1 ≫ XModLambdaN.map E.hom 1=
      XModLambdaN.map EZ.hom 1 ≫ XModLambdaN.map (model.nu.functor.map T.h) 1 := by
    rw [←model.quotients.functoriality.map_comp, ←model.quotients.functoriality.map_comp]
    exact congrArg (fun f => XModLambdaN.map f 1)
      (normalized_third_arrow_zero T he hf hg hh)
  constructor
  · intro hzero
    obtain ⟨b,hb⟩ := (normalized_quotient_boundary_exact T he hT 1 (by omega)
      ((t+1)-s) (t+1) _).mp hzero
    obtain ⟨z,hz⟩ := nativeFirstLabel_surjective T.Z s (t+1)
      (b ≫ XModLambdaN.map EZ.hom 1)
    refine ⟨z, nativeFirstLabel_injective (.shift 1 T.X) s (t+1) ?_⟩
    rw [←native_first_label_natural, hz, Category.assoc, ←hmap,
      ←Category.assoc, hb]
    simp only [E, Category.assoc, ←model.quotients.functoriality.map_comp,
      Iso.inv_hom_id, model.quotients.functoriality.map_id, Category.comp_id]
  · rintro ⟨z, rfl⟩
    apply (normalized_quotient_boundary_exact T he hT 1 (by omega)
      ((t+1)-s) (t+1) _).mpr
    refine ⟨nativeFirstLabel T.Z s (t+1) z ≫ XModLambdaN.map EZ.inv 1, ?_⟩
    apply (cancel_mono (Q.mapIso E).hom).mp
    change _ ≫ XModLambdaN.map E.hom 1=_ ≫ XModLambdaN.map E.hom 1
    rw [Category.assoc, Category.assoc, hmap]
    simp only [E, Category.assoc, ←model.quotients.functoriality.map_comp,
      Iso.inv_hom_id, Iso.inv_hom_id_assoc, model.quotients.functoriality.map_id,
      Category.comp_id]
    exact native_first_label_natural T.Z (.shift 1 T.X) T.h s (t+1) z

private theorem classical_h_image_iff_suspended
    (T : TriangleData model.auxiliary) (s t : ℤ)
    (x : KIP126.ProofTools.Ambient model T.X (s,t))
    (sx : KIP126.ProofTools.Ambient model (.shift 1 T.X) (s,t+1))
    (hsx : (model.classicalSuspension T.X).DesuspendsClass s (t+1) sx
      (by simpa only [show t+1-1=t by omega] using x)) :
    (∃ z : KIP126.ProofTools.Ambient model T.Z (s,t+1),
      (model.classical.map T.h).pageMap 2 (s,t+1) z=sx) ↔
    ∃ z : KIP126.ProofTools.Ambient model T.Z (s,t+1),
      KIP126.ProofTools.Standard.classicalTriangleHMapHom T s t z=x := by
  have cast_eq (n n' : ℤ) (hn : n=n')
      (a b : KIP126.ProofTools.Ambient model T.X (s,n')) :
      (congrArg (fun u : ℤ => (KIP126.ProofTools.Ambient model T.X (s,u) : Type)) hn).mpr a =
        (congrArg (fun u : ℤ => (KIP126.ProofTools.Ambient model T.X (s,u) : Type)) hn).mpr b ↔
      a=b := by
    subst n'; rfl
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z, ?_⟩
    have h := (desuspendsClass_eq_iff T.X s (t+1) _ sx _ _
      (KIP126.ProofTools.Standard.classicalTriangleHMapHom_spec T s t z) hsx).mp hz
    exact (cast_eq (t+1-1) t (by omega) _ _).mp h
  · rintro ⟨z,hz⟩
    refine ⟨z, (desuspendsClass_eq_iff T.X s (t+1) _ sx _ _
      (KIP126.ProofTools.Standard.classicalTriangleHMapHom_spec T s t z) hsx).mpr ?_⟩
    exact (cast_eq (t+1-1) t (by omega) _ _).mpr hz

end
end KIP126.ProofTools.Internal.ExtBoundaryComparison

namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.AdamsSynthetic.Standard
open KIP126.Kervaire.Route KIP126.Literature
open KIP126.ProofTools.Internal.Mahowald
open KIP126.ProofTools.Internal.ExtBoundaryComparison
open KIP126.ProofTools.Internal.LastLayerComparison
noncomputable section

/-- The actual E₂ kernel--image equation induced by the same compatible
normalized triangle. No exactness premise on arbitrary matrices is supplied.
This concerns the normalized quotient operation; it does not assert a
comparison with a separately constructed Steenrod-comodule Ext boundary. -/
private theorem cofiberFirstQuotientBoundary_exact
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f=1)
    (hg : normalizedExponent model.classicalTower T.g=0)
    (hh : normalizedExponent model.classicalTower T.h=0)
    (hT : NormalizedTriangleCompatible model T (by simp [hf,hg,hh]))
    (s t : ℤ) :
    (cofiberFirstQuotientBoundaryHom T hf s t).ker=
      (classicalTriangleHMapHom T s t).range := by
  ext x
  change cofiberFirstQuotientBoundary T hf s t x=0 ↔
    ∃ z, classicalTriangleHMapHom T s t z=x
  obtain ⟨sx,hsx⟩ := exists_suspendsClass T.X s (t+1)
    (by simpa only [show t+1-1=t by omega] using x)
  exact (cofiber_boundary_zero_iff_normalized_suspended_image
    T (by simp [hf,hg,hh]) hf s t x sx hsx).trans
    ((suspended_normalized_boundary_exact T (by simp [hf,hg,hh]) hf hg hh hT s t sx).trans
      (classical_h_image_iff_suspended T s t x sx hsx))

/-- The classical Ext-output finite-layer-surjectivity composition theorem.
The same homology SES is established from positive Adams filtration; it
is not an added caller premise. The local proof composes the already proved
finite-layer theorem with the registered upstream special-fiber comparison. -/
public theorem finiteLayerSurjectivityMahowaldLeibnizExt
    (T : TriangleData model.auxiliary)
    (hf : normalizedExponent model.classicalTower T.f = 1)
    (hg : normalizedExponent model.classicalTower T.g = 0)
    (hh : normalizedExponent model.classicalTower T.h = 0)
    (hT : NormalizedTriangleCompatible model T (by simp [hf,hg,hh]))
    (R K : ℕ) (hR : 2 ≤ R) (hK : 2 ≤ K) (s t : ℤ)
    (x : Ambient model T.X (s,t))
    (z : Ambient model T.Z (s+R,t+R))
    (v : Ambient model T.Y (s+R+K,t+R+K-1))
    (hx : IsCycle model T.X ((R:ℤ)-1) _ x)
    (hz : IsCycle model T.Z ((K:ℤ)-1) _ z)
    (hdx : ∃ u : Ambient model T.X (s+R,t+R-1),
      (model.classicalSuspension T.X).DesuspendsClass (s+R) (t+R)
        ((model.classical.functor.map T.h).pageMap 2 (s+R,t+R) z) u ∧
      DifferentialAt model T.X R (s,t) (s+R,t+R-1) x u)
    (hdz : DifferentialAt model T.Z K (s+R,t+R) (s+R+K,t+R+K-1) z
      ((model.classical.functor.map T.g).pageMap 2 (s+R+K,t+R+K-1) v))
    (hsurj : MahowaldLeibnizFiniteLayerSurjectivity T R K s t) :
    ∃ hH : HomologyShortExact coefficients
        (CategoryTheory.Pretriangulated.Triangle.mk T.f T.g T.h).rotate,
      let y := cofiberExtBoundary T hH s t x
      IsCycle model T.Y ((R:ℤ)+K-2) (s+1,t+1) y ∧
      DifferentialAt model T.Y ((R:ℤ)+K-1)
        (s+1,t+1) (s+R+K,t+R+K-1) y v := by
  have hH := HomologySES.positive_normalized_rotated_homology_short_exact T hf
  refine ⟨hH, ?_⟩
  have hout := finiteLayerSurjectivityMahowaldLeibniz T hf hg hh
    hT R K hR hK s t x z v hx hz hdx hdz hsurj
  have heq : cofiberFirstQuotientBoundary T hf s t x = cofiberExtBoundary T hH s t x :=
    KIP126.Literature.Standard.firstQuotient_ext_boundary T hf hg hh hT hH s t x
  simpa only [heq] using hout

end
end KIP126.ProofTools.Standard
