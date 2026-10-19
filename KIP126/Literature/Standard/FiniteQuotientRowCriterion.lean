module

import KIP126.Literature.Standard

/-! Exact cone criteria for the signed finite quotient row.
The two structure arrows are retained along with the cone isomorphism.
These private equivalences and transport lemmas do not construct the fixed
model's comparison or assert the horizontal-row theorem. -/

@[expose] section
namespace KIP126.Literature.Standard.Internal
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard

universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]

/-- Both cone structure arrows, rather than merely the third object, are
part of the exact criterion. No distinguishedness of the target is assumed
in the right-to-left implication. -/
private theorem distinguished_iff_exact_cone_iso
    {A B Z : C} (g : A ⟶ B) (h : B ⟶ Z) (k : Z ⟶ A⟦(1:ℤ)⟧) :
    Triangle.mk g h k ∈ distTriang C ↔
      ∃ e : HasFunctorialCofiber.cofib g ≅ Z,
        HasFunctorialCofiber.cofibι g ≫ e.hom = h ∧
        e.hom ≫ k = HasFunctorialCofiber.cofibδ g := by
  let K := Triangle.mk g (HasFunctorialCofiber.cofibι g)
    (HasFunctorialCofiber.cofibδ g)
  let R := Triangle.mk g h k
  constructor
  · intro hR
    let e := isoTriangleOfIso₁₂ K R (HasFunctorialCofiber.cofib_distinguished g)
      hR (Iso.refl A) (Iso.refl B) (by simp [K, R])
    refine ⟨Triangle.π₃.mapIso e, ?_, ?_⟩
    · have he := e.hom.comm₂
      change HasFunctorialCofiber.cofibι g ≫ e.hom.hom₃ = e.hom.hom₂ ≫ h at he
      change HasFunctorialCofiber.cofibι g ≫ e.hom.hom₃ = h
      have he₂ : e.hom.hom₂ = 𝟙 B := by
        simp only [e, isoTriangleOfIso₁₂_hom_hom₂, Iso.refl_hom]
      rw [he₂] at he
      exact he.trans (CategoryTheory.Category.id_comp h)
    · have he := e.hom.comm₃.symm
      change e.hom.hom₃ ≫ k = HasFunctorialCofiber.cofibδ g ≫
        (shiftFunctor C (1:ℤ)).map e.hom.hom₁ at he
      change e.hom.hom₃ ≫ k = HasFunctorialCofiber.cofibδ g
      simpa only [e, isoTriangleOfIso₁₂_hom_hom₁, Iso.refl_hom,
        CategoryTheory.Functor.map_id, CategoryTheory.Category.comp_id] using he
  · rintro ⟨e, heι, heδ⟩
    let E : K ≅ R := Triangle.isoMk _ _ (Iso.refl A) (Iso.refl B) e
      (by simp [K, R])
      (by simpa only [K, R, Triangle.mk, Iso.refl_hom, Category.id_comp] using heι)
      (by
        change HasFunctorialCofiber.cofibδ g ≫
          (shiftFunctor C (1:ℤ)).map (𝟙 A) = e.hom ≫ k
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Category.comp_id]
        exact heδ.symm)
    exact isomorphic_distinguished K
      (HasFunctorialCofiber.cofib_distinguished g) R E.symm

/-- A comparison of the selected cones for this one first arrow suffices.
No global suspension structure, exactness of Q, good-filling replacement,
or target-row distinguishedness is an input to this implication. -/
private theorem mapped_triangle_of_exact_selected_cone_diagram
    (Q : C ⥤ C) (T : Triangle C) (hT : T ∈ distTriang C)
    (esusp : Q.obj (T.obj₁⟦(1:ℤ)⟧) ≅ (Q.obj T.obj₁)⟦(1:ℤ)⟧)
    (omega : HasFunctorialCofiber.cofib (Q.map T.mor₁) ≅
      Q.obj (HasFunctorialCofiber.cofib T.mor₁))
    (hι : HasFunctorialCofiber.cofibι (Q.map T.mor₁) ≫ omega.hom =
      Q.map (HasFunctorialCofiber.cofibι T.mor₁))
    (hδ : omega.hom ≫ Q.map (HasFunctorialCofiber.cofibδ T.mor₁) ≫ esusp.hom =
      HasFunctorialCofiber.cofibδ (Q.map T.mor₁)) :
    Triangle.mk (Q.map T.mor₁) (Q.map T.mor₂) (Q.map T.mor₃ ≫ esusp.hom) ∈
      distTriang C := by
  obtain ⟨e, heι, heδ⟩ :=
    (distinguished_iff_exact_cone_iso T.mor₁ T.mor₂ T.mor₃).mp hT
  apply (distinguished_iff_exact_cone_iso _ _ _).mpr
  refine ⟨omega ≪≫ Q.mapIso e, ?_, ?_⟩
  · change HasFunctorialCofiber.cofibι (Q.map T.mor₁) ≫
      (omega.hom ≫ Q.map e.hom) = Q.map T.mor₂
    rw [←Category.assoc, hι, ←CategoryTheory.Functor.map_comp, heι]
  · change (omega.hom ≫ Q.map e.hom) ≫ (Q.map T.mor₃ ≫ esusp.hom) = _
    calc
      _ = omega.hom ≫ Q.map (e.hom ≫ T.mor₃) ≫ esusp.hom := by
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      _ = _ := by rw [heδ]; exact hδ

/-- The fixed row with its literal signed tail is equivalent to an exact
cone diagram. The assertion holds for a fixed esusp; it does not produce one
whose cone diagram exists. -/
private theorem fixed_row_iff_exact_cone_diagram
    (N : Triangle SyntheticSpectrum) (q : ℕ)
    (esusp : XModLambdaN (N.obj₂⟦(1:ℤ)⟧) q ≅
      (XModLambdaN N.obj₂ q)⟦(1:ℤ)⟧) :
    Triangle.mk (XModLambdaN.map N.mor₂ q) (XModLambdaN.map N.mor₃ q)
      (-(XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q ≫
        esusp.hom)) ∈ distTriang SyntheticSpectrum ↔
      ∃ e : HasFunctorialCofiber.cofib (XModLambdaN.map N.mor₂ q) ≅
          XModLambdaN (N.obj₁⟦(1:ℤ)⟧) q,
        HasFunctorialCofiber.cofibι (XModLambdaN.map N.mor₂ q) ≫ e.hom =
          XModLambdaN.map N.mor₃ q ∧
        e.hom ≫ (-(XModLambdaN.map
          ((shiftFunctor SyntheticSpectrum (1:ℤ)).map N.mor₁) q ≫ esusp.hom)) =
            HasFunctorialCofiber.cofibδ (XModLambdaN.map N.mor₂ q) := by
  exact distinguished_iff_exact_cone_iso _ _ _

end
end KIP126.Literature.Standard.Internal
