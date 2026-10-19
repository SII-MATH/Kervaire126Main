module

import KIP126.Literature.Standard

/-! Exact pure-category steps in the attempted fixed finite-quotient-row
construction. No ProofTools imports, new axioms, or proof holes occur here.
The unfinished public producer is not declared in this research file. -/

@[expose] section
namespace MHFixedRowConstruction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

section NaturalTransformation
variable (F : C ⥤ C) [F.CommShift ℤ] (α : F ⟶ 𝟭 C)

/-- Naturality is precisely the first two morphism-of-triangles squares.
The third square has the displayed, additional suspension discrepancy. -/
private theorem third_triangle_square_iff (T : Triangle C) :
    (F.map T.mor₃ ≫ (F.commShiftIso (1:ℤ)).hom.app T.obj₁) ≫
        (shiftFunctor C (1:ℤ)).map (α.app T.obj₁) = α.app T.obj₃ ≫ T.mor₃ ↔
      F.map T.mor₃ ≫ ((F.commShiftIso (1:ℤ)).hom.app T.obj₁ ≫
        (shiftFunctor C (1:ℤ)).map (α.app T.obj₁)) =
          F.map T.mor₃ ≫ α.app (T.obj₁⟦(1:ℤ)⟧) := by
  have h := α.naturality T.mor₃
  change F.map T.mor₃ ≫ α.app (T.obj₁⟦(1:ℤ)⟧) = α.app T.obj₃ ≫ T.mor₃ at h
  rw [Category.assoc, h]

/-- With the actual suspension compatibility, the natural transformation
is a morphism of these exact-functor triangles. The compatibility itself is
not asserted or derived from bare naturality. -/
private def triangle_map_of_suspension_square (T : Triangle C)
    (hα : (F.commShiftIso (1:ℤ)).hom.app T.obj₁ ≫
      (shiftFunctor C (1:ℤ)).map (α.app T.obj₁) = α.app (T.obj₁⟦(1:ℤ)⟧)) :
    F.mapTriangle.obj T ⟶ T where
  hom₁ := α.app T.obj₁
  hom₂ := α.app T.obj₂
  hom₃ := α.app T.obj₃
  comm₁ := α.naturality T.mor₁
  comm₂ := α.naturality T.mor₂
  comm₃ := (third_triangle_square_iff F α T).mpr (by rw [hα])

/-- If a separately chosen third filling agrees with the natural component
on the preceding edge, its entire defect factors through the boundary.
This identifies the exact remaining map rather than declaring it zero. -/
private theorem third_filling_defect (T : Triangle C) [F.IsTriangulated]
    (hT : T ∈ distTriang C)
    (l : F.obj T.obj₃ ⟶ T.obj₃)
    (hl : F.map T.mor₂ ≫ l = α.app T.obj₂ ≫ T.mor₂) :
    let a₃ : F.obj T.obj₃ ⟶ T.obj₃ := α.app T.obj₃
    ∃ z : (F.obj T.obj₁)⟦(1:ℤ)⟧ ⟶ T.obj₃,
      l - a₃ =
        (F.map T.mor₃ ≫ (F.commShiftIso (1:ℤ)).hom.app T.obj₁) ≫ z := by
  dsimp only
  let a₃ : F.obj T.obj₃ ⟶ T.obj₃ := α.app T.obj₃
  have hnat : F.map T.mor₂ ≫ a₃ = α.app T.obj₂ ≫ T.mor₂ := α.naturality T.mor₂
  have hz : F.map T.mor₂ ≫ (l - a₃) = 0 := by
    rw [Preadditive.comp_sub, hl, hnat, sub_self]
  obtain ⟨z,hz⟩ := (F.mapTriangle.obj T).yoneda_exact₃
    (F.map_distinguished T hT) (l - a₃) hz
  exact ⟨z,hz⟩

end NaturalTransformation

section SelectedConeMap
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- Both endpoint equations of a chosen cone square constrain, but do not
erase, its boundary factor relative to the fixed quotient map. -/
private theorem selected_quotient_map_defect {A B : Syn} (f : A ⟶ B) (q : ℕ)
    (u : XModLambdaN A q ⟶ XModLambdaN B q)
    (hι : XModLambdaN.incl A q ≫ u = f ≫ XModLambdaN.incl B q)
    (hδ : u ≫ XModLambdaN.proj B q = XModLambdaN.proj A q ≫
      (shiftFunctor Syn (1:ℤ)).map ((SyntheticCategory.biShift (0,-(q:ℤ))).map f)) :
    ∃ z : (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧) ⟶
        XModLambdaN B q,
      u - XModLambdaN.map f q = XModLambdaN.proj A q ≫ z ∧
      XModLambdaN.proj A q ≫ z ≫ XModLambdaN.proj B q = 0 := by
  have hz : XModLambdaN.incl A q ≫ (u - XModLambdaN.map f q) = 0 := by
    rw [Preadditive.comp_sub, hι, ← XModLambdaN.incl_naturality, sub_self]
  obtain ⟨z,hz⟩ := (XModLambdaN.cofiberTriangle A q).yoneda_exact₃
    (XModLambdaN.cofiberTriangle_distinguished A q) (u - XModLambdaN.map f q) hz
  change (((SyntheticCategory.biShift (0,-(q:ℤ))).obj A)⟦(1:ℤ)⟧) ⟶
    XModLambdaN B q at z
  change u - XModLambdaN.map f q = XModLambdaN.proj A q ≫ z at hz
  refine ⟨z,hz,?_⟩
  rw [←Category.assoc,←hz,Preadditive.sub_comp,hδ,XModLambdaN.proj_naturality,sub_self]

end SelectedConeMap

section GoodRow
variable [HasFunctorialCofiber (C := C)] [IsTriangulated C]

/-- Three octahedra give one good quotient filling and its complementary
distinguished row. This result retains every supplied endpoint square but
does not substitute the separately selected cone-map filling. -/
private theorem good_quotient_row
    {A B : C} (F : C ⥤ C) (α : F ⟶ 𝟭 C) (f : A ⟶ B) :
    let QA := HasFunctorialCofiber.cofib (α.app A)
    let QB := HasFunctorialCofiber.cofib (α.app B)
    ∃ u : QA ⟶ QB,
      HasFunctorialCofiber.cofibι (α.app A) ≫ u =
        f ≫ HasFunctorialCofiber.cofibι (α.app B) ∧
      u ≫ HasFunctorialCofiber.cofibδ (α.app B) =
        HasFunctorialCofiber.cofibδ (α.app A) ≫
          (shiftFunctor C (1:ℤ)).map (F.map f) ∧
      ∃ (l : HasFunctorialCofiber.cofib (F.map f) ⟶ HasFunctorialCofiber.cofib f)
        (v : HasFunctorialCofiber.cofib f ⟶ HasFunctorialCofiber.cofib u)
        (w : HasFunctorialCofiber.cofib u ⟶
          (HasFunctorialCofiber.cofib (F.map f))⟦(1:ℤ)⟧),
        HasFunctorialCofiber.cofibι (F.map f) ≫ l =
          α.app B ≫ HasFunctorialCofiber.cofibι f ∧
        l ≫ HasFunctorialCofiber.cofibδ f =
          HasFunctorialCofiber.cofibδ (F.map f) ≫ (shiftFunctor C (1:ℤ)).map (α.app A) ∧
        HasFunctorialCofiber.cofibι f ≫ v =
          HasFunctorialCofiber.cofibι (α.app B) ≫ HasFunctorialCofiber.cofibι u ∧
        v ≫ HasFunctorialCofiber.cofibδ u =
          HasFunctorialCofiber.cofibδ f ≫
            (shiftFunctor C (1:ℤ)).map (HasFunctorialCofiber.cofibι (α.app A)) ∧
        HasFunctorialCofiber.cofibι u ≫ w = HasFunctorialCofiber.cofibδ (α.app B) ≫
          (shiftFunctor C (1:ℤ)).map (HasFunctorialCofiber.cofibι (F.map f)) ∧
        Triangle.mk v w (-(shiftFunctor C (1:ℤ)).map l) ∈ distTriang C := by
  dsimp only
  let c := α.app A ≫ f
  let O := Triangulated.someOctahedron rfl
    (HasFunctorialCofiber.cofib_distinguished (α.app A))
    (HasFunctorialCofiber.cofib_distinguished f)
    (HasFunctorialCofiber.cofib_distinguished c)
  have hSquare : F.map f ≫ α.app B = c := α.naturality f
  let O' := Triangulated.someOctahedron hSquare
    (HasFunctorialCofiber.cofib_distinguished (F.map f))
    (HasFunctorialCofiber.cofib_distinguished (α.app B))
    (HasFunctorialCofiber.cofib_distinguished c)
  let u := O.m₁ ≫ O'.m₃
  let l := O'.m₁ ≫ O.m₃
  let O'' := Triangulated.someOctahedron rfl O.mem
    (rot_of_distTriang O'.triangle O'.mem)
    (HasFunctorialCofiber.cofib_distinguished u)
  refine ⟨u,?_,?_,l,O''.m₁,O''.m₃,?_,?_,?_,?_,?_,?_⟩
  · dsimp [u]
    rw [←Category.assoc,O.comm₁,Category.assoc,O'.comm₃]
  · dsimp [u]
    rw [Category.assoc,←O'.comm₄,←Category.assoc,O.comm₂]
  · dsimp [l]
    rw [←Category.assoc,O'.comm₁,Category.assoc,O.comm₃]
  · dsimp [l]
    rw [Category.assoc,←O.comm₄,←Category.assoc,O'.comm₂]
  · calc
      _ = (HasFunctorialCofiber.cofibι c ≫ O.m₃) ≫ O''.m₁ := by rw [O.comm₃]
      _ = _ := by
        rw [Category.assoc,O''.comm₁]
        change HasFunctorialCofiber.cofibι c ≫ O'.m₃ ≫ _ = _
        rw [←Category.assoc,O'.comm₃]
  · exact O''.comm₂
  · exact O''.comm₃
  · simpa only [Triangulated.Octahedron.triangle,Triangle.rotate,Triangle.mk,
      Preadditive.neg_comp,←Functor.map_comp] using O''.mem

end GoodRow

#print axioms third_triangle_square_iff
#print axioms triangle_map_of_suspension_square
#print axioms third_filling_defect
#print axioms selected_quotient_map_defect
#print axioms good_quotient_row
end
end MHFixedRowConstruction
