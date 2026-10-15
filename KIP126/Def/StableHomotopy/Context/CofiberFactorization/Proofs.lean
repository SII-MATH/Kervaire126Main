module

public import KIP126.Def.StableHomotopy.Context.CofiberFactorization.Data
public import KIP126.Def.StableHomotopy.Context.Connecting.Proofs

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {A B D : C} (f : A ⟶ D) (g : B ⟶ D) (a : A ⟶ B) (h : a ≫ g = f)

theorem cofiberFactorizationMap_ι :
    HasFunctorialCofiber.cofibι f ≫ cofiberFactorizationMap f g a h =
      HasFunctorialCofiber.cofibι g := by
  exact (HasFunctorialCofiber.cofibMap_ι f g a (𝟙 D) _).symm.trans
    (Category.id_comp _)

theorem cofiberFactorizationMap_δ :
    cofiberFactorizationMap f g a h ≫ HasFunctorialCofiber.cofibδ g =
      HasFunctorialCofiber.cofibδ f ≫ a⟦(1 : ℤ)⟧' :=
  HasFunctorialCofiber.cofibMap_δ f g a (𝟙 D) _

theorem cofiberFactorizationMap_connecting (n : ℤ)
    (z : HomotopyGroup n (HasFunctorialCofiber.cofib f)) :
    connectingHomomorphism (HoCofiberSequence.ofMorphism g) n
        (inducedMap (cofiberFactorizationMap f g a h) n z) =
      inducedMap a (n - 1)
        (connectingHomomorphism (HoCofiberSequence.ofMorphism f) n z) :=
  connectingHomomorphism_naturality (HoCofiberSequence.ofMorphism f)
    (HoCofiberSequence.ofMorphism g) a (cofiberFactorizationMap f g a h)
    (cofiberFactorizationMap_δ f g a h) n z

/-- Exactness characterizes the image of a long-cofiber representative:
it consists exactly of classes whose connecting image lifts through `a`.
This uses only the two distinguished triangles and their comparison, not
an octahedron, a tensor product, or coherence of independently chosen maps. -/
theorem cofiberFactorizationMap_image_iff (n : ℤ)
    (x : HomotopyGroup n (HasFunctorialCofiber.cofib g)) :
    (∃ z : HomotopyGroup n (HasFunctorialCofiber.cofib f),
      inducedMap (cofiberFactorizationMap f g a h) n z = x) ↔
    ∃ y : HomotopyGroup (n - 1) A,
      inducedMap a (n - 1) y =
        connectingHomomorphism (HoCofiberSequence.ofMorphism g) n x := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, (cofiberFactorizationMap_connecting f g a h n z).symm⟩
  · rintro ⟨y, hy⟩
    have hg : inducedMap g (n - 1)
        (connectingHomomorphism (HoCofiberSequence.ofMorphism g) n x) = 0 :=
      (lesHomotopyExactH (HoCofiberSequence.ofMorphism g) n _).mpr ⟨x, rfl⟩
    have hf : inducedMap f (n - 1) y = 0 := by
      change y ≫ f = 0
      rw [← h, ← Category.assoc]
      change inducedMap g (n - 1) (inducedMap a (n - 1) y) = 0
      rw [hy]
      exact hg
    obtain ⟨z, hz⟩ := (lesHomotopyExactH (HoCofiberSequence.ofMorphism f) n y).mp hf
    change HomotopyGroup n (HasFunctorialCofiber.cofib f) at z
    let k : HomotopyGroup n (HasFunctorialCofiber.cofib g) →+
        HomotopyGroup (n - 1) B :=
      connectingHomomorphism (HoCofiberSequence.ofMorphism g) n
    have hz' : k (inducedMap (cofiberFactorizationMap f g a h) n z) = k x :=
      (cofiberFactorizationMap_connecting f g a h n z).trans
        ((congrArg (inducedMap a (n - 1)) hz).trans hy)
    have hk : connectingHomomorphism (HoCofiberSequence.ofMorphism g) n
        (x - inducedMap (cofiberFactorizationMap f g a h) n z) = 0 := by
      change k (x - _) = 0
      rw [map_sub, hz', sub_self]
    obtain ⟨b, hb⟩ := (les_homotopy_exact_g (HoCofiberSequence.ofMorphism g) n _).mp hk
    change HomotopyGroup n D at b
    change inducedMap (HasFunctorialCofiber.cofibι g) n b = _ at hb
    refine ⟨z + inducedMap (HasFunctorialCofiber.cofibι f) n b, ?_⟩
    rw [map_add]
    have hi : inducedMap (cofiberFactorizationMap f g a h) n
        (inducedMap (HasFunctorialCofiber.cofibι f) n b) =
        inducedMap (HasFunctorialCofiber.cofibι g) n b := by
      change (b ≫ _) ≫ _ = b ≫ _
      rw [Category.assoc, cofiberFactorizationMap_ι]
    rw [hi, hb, add_comm, sub_add_cancel]

end KIP126.StableHomotopy
