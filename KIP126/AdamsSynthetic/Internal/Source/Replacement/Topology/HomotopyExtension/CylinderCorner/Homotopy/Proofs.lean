module

import all KIP126.AdamsSynthetic.Internal.Source.Replacement.Topology.HomotopyExtension.CylinderCorner.Gluing.Proofs

@[expose] section

namespace KIP126.Topology.HomotopyExtension
open CategoryTheory Set _root_.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Compatible homotopies on all three faces of the actual closed cylinder
corner glue continuously, retaining their entire two-parameter values. -/
theorem exists_cylinderCorner_homotopy {A B : TopCat.{u}} (i : A ⟶ B)
    (hi : IsClosedEmbedding i) {Y : TopCat.{u}} (f g : C(B × I,Y))
    (Ha : (f.comp (i.hom.prodMap (ContinuousMap.id I))).Homotopy
      (g.comp (i.hom.prodMap (ContinuousMap.id I))))
    (H₀ : (f.comp ((ContinuousMap.id B).prodMk (ContinuousMap.const B 0))).Homotopy
      (g.comp ((ContinuousMap.id B).prodMk (ContinuousMap.const B 0))))
    (H₁ : (f.comp ((ContinuousMap.id B).prodMk (ContinuousMap.const B 1))).Homotopy
      (g.comp ((ContinuousMap.id B).prodMk (ContinuousMap.const B 1))))
    (h₀ : ∀ s a, Ha (s,(a,0)) = H₀ (s,i a))
    (h₁ : ∀ s a, Ha (s,(a,1)) = H₁ (s,i a)) :
    ∃ H : (f.comp (cylinderCornerMap i).hom).Homotopy (g.comp (cylinderCornerMap i).hom),
      (∀ s a t, H (s,⟨(i a,t),Or.inl ⟨a,rfl⟩⟩) = Ha (s,(a,t))) ∧
      (∀ s b, H (s,⟨(b,0),Or.inr (Or.inl rfl)⟩) = H₀ (s,b)) ∧
      (∀ s b, H (s,⟨(b,1),Or.inr (Or.inr rfl)⟩) = H₁ (s,b)) := by
  let a : C(A × I,C(I,Y)) := (Ha.toContinuousMap.comp ContinuousMap.prodSwap).curry
  let f₀ : C(B,C(I,Y)) := (H₀.toContinuousMap.comp ContinuousMap.prodSwap).curry
  let f₁ : C(B,C(I,Y)) := (H₁.toContinuousMap.comp ContinuousMap.prodSwap).curry
  obtain ⟨d,hd,hd0,hd1⟩ := exists_cylinderCorner_desc i hi (Y := TopCat.of C(I,Y)) a f₀ f₁
    (fun x => ContinuousMap.ext (fun s => h₀ s x))
    (fun x => ContinuousMap.ext (fun s => h₁ s x))
  have hd' (s : I) (x : A) (t : I) : d ⟨(i x,t),Or.inl ⟨x,rfl⟩⟩ s = Ha (s,(x,t)) :=
    ContinuousMap.congr_fun (hd x t) s
  have hd0' (s : I) (b : B) : d ⟨(b,0),Or.inr (Or.inl rfl)⟩ s = H₀ (s,b) :=
    ContinuousMap.congr_fun (hd0 b) s
  have hd1' (s : I) (b : B) : d ⟨(b,1),Or.inr (Or.inr rfl)⟩ s = H₁ (s,b) :=
    ContinuousMap.congr_fun (hd1 b) s
  refine ⟨{
    toContinuousMap := d.uncurry.comp ContinuousMap.prodSwap
    map_zero_left := ?_
    map_one_left := ?_ },hd',hd0',hd1'⟩
  · rintro ⟨⟨b,t⟩,hb⟩
    rcases hb with ⟨x,hx⟩ | ht | ht
    · change i x = b at hx
      subst b
      exact (hd' 0 x t).trans (Ha.apply_zero (x,t))
    · change t = 0 at ht
      subst t
      exact (hd0' 0 b).trans (H₀.apply_zero b)
    · change t = 1 at ht
      subst t
      exact (hd1' 0 b).trans (H₁.apply_zero b)
  · rintro ⟨⟨b,t⟩,hb⟩
    rcases hb with ⟨x,hx⟩ | ht | ht
    · change i x = b at hx
      subst b
      exact (hd' 1 x t).trans (Ha.apply_one (x,t))
    · change t = 0 at ht
      subst t
      exact (hd0' 1 b).trans (H₀.apply_one b)
    · change t = 1 at ht
      subst t
      exact (hd1' 1 b).trans (H₁.apply_one b)

end KIP126.Topology.HomotopyExtension
