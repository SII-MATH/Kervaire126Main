module

public import KIP126.Def.StableHomotopy.Context.CofiberFactorization.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory Pretriangulated
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

/-- A prescribed lift of the connecting map gives a cofiber lift with both
its projection and its own connecting map specified. Exactness supplies
the needed correction without changing that connecting map. -/
theorem cofiberFactorizationMap_lift_of_boundary {A B D W : C}
    (f : A ⟶ D) (g : B ⟶ D) (a : A ⟶ B) (h : a ≫ g = f)
    (x : W ⟶ HasFunctorialCofiber.cofib g) (y : W ⟶ A⟦(1 : ℤ)⟧)
    (hy : y ≫ a⟦(1 : ℤ)⟧' = x ≫ HasFunctorialCofiber.cofibδ g) :
    ∃ z : W ⟶ HasFunctorialCofiber.cofib f,
      z ≫ cofiberFactorizationMap f g a h = x ∧ z ≫ HasFunctorialCofiber.cofibδ f = y := by
    have hg : HasFunctorialCofiber.cofibδ g ≫ g⟦(1 : ℤ)⟧' = 0 :=
      comp_distTriang_mor_zero₃₁
        (Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g))
        (HasFunctorialCofiber.cofib_distinguished g)
    have hf : y ≫ f⟦(1 : ℤ)⟧' = 0 := by
      rw [← h, Functor.map_comp, ← Category.assoc, hy, Category.assoc, hg, Limits.comp_zero]
    obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₁
      (Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f))
      (HasFunctorialCofiber.cofib_distinguished f) y hf
    change W ⟶ HasFunctorialCofiber.cofib f at z
    change y = z ≫ HasFunctorialCofiber.cofibδ f at hz
    have hz' : (z ≫ cofiberFactorizationMap f g a h) ≫ HasFunctorialCofiber.cofibδ g =
        x ≫ HasFunctorialCofiber.cofibδ g := by
      rw [Category.assoc, cofiberFactorizationMap_δ, ← Category.assoc, ← hz]
      exact hy
    have hk : (x - z ≫ cofiberFactorizationMap f g a h) ≫
        HasFunctorialCofiber.cofibδ g = 0 := by
      rw [Preadditive.sub_comp, hz', sub_self]
    obtain ⟨b, hb⟩ := Triangle.coyoneda_exact₃
      (Triangle.mk g (HasFunctorialCofiber.cofibι g) (HasFunctorialCofiber.cofibδ g))
      (HasFunctorialCofiber.cofib_distinguished g)
      (x - z ≫ cofiberFactorizationMap f g a h) hk
    change W ⟶ D at b
    change x - z ≫ cofiberFactorizationMap f g a h = b ≫ HasFunctorialCofiber.cofibι g at hb
    refine ⟨z + b ≫ HasFunctorialCofiber.cofibι f, ?_, ?_⟩
    · rw [Preadditive.add_comp, Category.assoc, cofiberFactorizationMap_ι,
        ← hb, add_comm, sub_add_cancel]
    · have hi : HasFunctorialCofiber.cofibι f ≫ HasFunctorialCofiber.cofibδ f = 0 :=
        comp_distTriang_mor_zero₂₃
          (Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f))
          (HasFunctorialCofiber.cofib_distinguished f)
      rw [Preadditive.add_comp, Category.assoc, hi, Limits.comp_zero, add_zero, ← hz]

/-- For an arbitrary source object, lifting a map through the chosen
cofiber comparison is equivalent to lifting its actual connecting map.
This concerns spectrum morphisms, not only sphere-represented classes. -/
theorem cofiberFactorizationMap_lift_iff {A B D W : C}
    (f : A ⟶ D) (g : B ⟶ D) (a : A ⟶ B) (h : a ≫ g = f)
    (x : W ⟶ HasFunctorialCofiber.cofib g) :
    (∃ z : W ⟶ HasFunctorialCofiber.cofib f, z ≫ cofiberFactorizationMap f g a h = x) ↔
      ∃ y : W ⟶ A⟦(1 : ℤ)⟧,
        y ≫ a⟦(1 : ℤ)⟧' = x ≫ HasFunctorialCofiber.cofibδ g := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z ≫ HasFunctorialCofiber.cofibδ f, ?_⟩
    rw [Category.assoc, Category.assoc, cofiberFactorizationMap_δ]
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := cofiberFactorizationMap_lift_of_boundary f g a h x y hy
    exact ⟨z, hz⟩

end KIP126.StableHomotopy
