module

import KIP126.AdamsSynthetic.Quotients
import all KIP126.ProofTools.GeneralizedMahowald.OctahedralPullback

/-! A pure triangulated common-lift construction. This research lemma assumes
the selected finite horizontal row is distinguished. That is a remaining
condition to prove from the frozen interfaces, not a new production premise.
No tensor quotient identification or May tensor axiom is used. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald.ThreeByThree
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] [IsTriangulated C]

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

omit [HasFunctorialCofiber (C := C)] [IsTriangulated C] in
private theorem octahedron_pair_lift
    {A B D E V U S : C}
    {u : A ⟶ B} {l : B ⟶ D} {f : A ⟶ D} {hcomp : u≫l=f}
    {j : B ⟶ U} {h : U ⟶ A⟦(1:ℤ)⟧}
    {rho : D ⟶ E} {delta : E ⟶ B⟦(1:ℤ)⟧}
    {incl : D ⟶ V} {proj : V ⟶ A⟦(1:ℤ)⟧}
    {hU : Triangle.mk u j h ∈ distTriang C}
    {hL : Triangle.mk l rho delta ∈ distTriang C}
    {hF : Triangle.mk f incl proj ∈ distTriang C}
    (O : Triangulated.Octahedron hcomp hU hL hF)
    (a : S ⟶ E) (b : S ⟶ A⟦(1:ℤ)⟧)
    (hab : a≫delta=b≫(shiftFunctor C (1:ℤ)).map u) :
    ∃ v : S ⟶ V, v≫O.m₃=a ∧ v≫proj=b := by
  have huj : u ≫ j = 0 := comp_distTriang_mor_zero₁₂ _ hU
  have haz : a ≫ (delta ≫ (shiftFunctor C (1:ℤ)).map j)=0 := by
    rw [←Category.assoc,hab,Category.assoc,←Functor.map_comp,
      huj,Functor.map_zero,comp_zero]
  obtain ⟨v₀,hv₀⟩ := O.triangle.coyoneda_exact₃ O.mem a haz
  change S ⟶ V at v₀
  change a = v₀ ≫ O.m₃ at hv₀
  let e := b-v₀≫proj
  have he : e ≫ (-((shiftFunctor C (1:ℤ)).map u))=0 := by
    simp only [e,Preadditive.comp_neg,Preadditive.sub_comp,Category.assoc,O.comm₄]
    rw [←Category.assoc,←hv₀,←hab,sub_self,neg_zero]
  obtain ⟨c,hc⟩ := (Triangle.mk u j h).rotate.coyoneda_exact₃
    (rot_of_distTriang _ hU) e he
  change e=c≫h at hc
  have hzero : O.m₁ ≫ O.m₃ = 0 := comp_distTriang_mor_zero₁₂ _ O.mem
  refine ⟨v₀+c≫O.m₁,?_,?_⟩
  · rw [Preadditive.add_comp,Category.assoc,hzero,comp_zero,add_zero]
    exact hv₀.symm
  · rw [Preadditive.add_comp,Category.assoc,O.comm₂,←hc]
    dsimp only [e]
    abel

/-- A full pure-TR3/TR4 construction, with one universal restriction defect.
The second prescribed image is exact. The defect is a fixed map z, chosen
before the inputs a and b. Sphere no-return can annihilate b≫z in normalized
applications without identifying all cofiber fillings globally. -/
private theorem common_lift_with_restriction_defect
    {YB ZB YN ZN ZA CN CA : C}
    (u : YB ⟶ ZB) (lZ : ZB ⟶ ZN) (lY : YB ⟶ YN)
    (gN : YN ⟶ ZN) (hN : ZN ⟶ CN) (kN : CN ⟶ YN⟦(1:ℤ)⟧)
    (rhoZ : ZN ⟶ ZA) (deltaZ : ZA ⟶ ZB⟦(1:ℤ)⟧)
    (hA : ZA ⟶ CA) (rhoC : CN ⟶ CA)
    (hL : Triangle.mk lZ rhoZ deltaZ ∈ distTriang C)
    (hRow : Triangle.mk gN hN kN ∈ distTriang C)
    (hSquare : lY ≫ gN = u ≫ lZ)
    (hRho : hN ≫ rhoC = rhoZ ≫ hA) :
    ∃ z : YB⟦(1:ℤ)⟧ ⟶ CA,
      ∀ {S : C} (a : S ⟶ ZA) (b : S ⟶ YB⟦(1:ℤ)⟧),
        a ≫ deltaZ = b ≫ (shiftFunctor C (1:ℤ)).map u →
        ∃ c : S ⟶ CN,
          c ≫ rhoC - a ≫ hA = b ≫ z ∧
          c ≫ kN = b ≫ (shiftFunctor C (1:ℤ)).map lY := by
  let f := u ≫ lZ
  let TF := Triangle.mk f (HasFunctorialCofiber.cofibι f) (HasFunctorialCofiber.cofibδ f)
  have hTF := HasFunctorialCofiber.cofib_distinguished f
  let O := Triangulated.someOctahedron rfl
    (HasFunctorialCofiber.cofib_distinguished u) hL hTF
  obtain ⟨φ,hφ,hφk⟩ := complete_distinguished_triangle_morphism
    TF (Triangle.mk gN hN kN) hTF hRow lY (𝟙 ZN) (by
      exact (Category.comp_id f).trans hSquare.symm)
  change HasFunctorialCofiber.cofib f ⟶ CN at φ
  have hφ' : HasFunctorialCofiber.cofibι f ≫ φ = hN := by
    exact hφ.trans (Category.id_comp hN)
  change HasFunctorialCofiber.cofibδ f ≫ (shiftFunctor C (1:ℤ)).map lY = φ ≫ kN at hφk
  have hz : HasFunctorialCofiber.cofibι f ≫ (φ ≫ rhoC - O.m₃ ≫ hA) = 0 := by
    rw [Preadditive.comp_sub,←Category.assoc,hφ',←Category.assoc,O.comm₃,hRho,sub_self]
  obtain ⟨z,hz⟩ := TF.yoneda_exact₃ hTF (φ ≫ rhoC - O.m₃ ≫ hA) hz
  change φ ≫ rhoC - O.m₃ ≫ hA = HasFunctorialCofiber.cofibδ f ≫ z at hz
  refine ⟨z,?_⟩
  intro S a b hab
  obtain ⟨v,hv,hvb⟩ := octahedron_pair_lift O a b hab
  refine ⟨v ≫ φ,?_,?_⟩
  · rw [Category.assoc,←hv,Category.assoc,←Preadditive.comp_sub,hz,
      ←Category.assoc,hvb]
  · rw [Category.assoc,←hφk,←Category.assoc,hvb]

/-- If the restriction defect vanishes on the chosen source group, the same
construction gives both fixed images. This is an actual construction from
TR3/TR4, conditional only on the displayed rows and no-return statement. -/
private theorem common_lift_of_no_return
    {YB ZB YN ZN ZA CN CA S : C}
    (u : YB ⟶ ZB) (lZ : ZB ⟶ ZN) (lY : YB ⟶ YN)
    (gN : YN ⟶ ZN) (hN : ZN ⟶ CN) (kN : CN ⟶ YN⟦(1:ℤ)⟧)
    (rhoZ : ZN ⟶ ZA) (deltaZ : ZA ⟶ ZB⟦(1:ℤ)⟧)
    (hA : ZA ⟶ CA) (rhoC : CN ⟶ CA)
    (hL : Triangle.mk lZ rhoZ deltaZ ∈ distTriang C)
    (hRow : Triangle.mk gN hN kN ∈ distTriang C)
    (hSquare : lY ≫ gN = u ≫ lZ)
    (hRho : hN ≫ rhoC = rhoZ ≫ hA)
    (hNoReturn : ∀ (b : S ⟶ YB⟦(1:ℤ)⟧) (z : YB⟦(1:ℤ)⟧ ⟶ CA), b ≫ z = 0)
    (a : S ⟶ ZA) (b : S ⟶ YB⟦(1:ℤ)⟧)
    (hab : a ≫ deltaZ = b ≫ (shiftFunctor C (1:ℤ)).map u) :
    ∃ c : S ⟶ CN, c ≫ rhoC = a ≫ hA ∧
      c ≫ kN = b ≫ (shiftFunctor C (1:ℤ)).map lY := by
  obtain ⟨z,hz⟩ := common_lift_with_restriction_defect u lZ lY gN hN kN
    rhoZ deltaZ hA rhoC hL hRow hSquare hRho
  obtain ⟨c,hc,hck⟩ := hz a b hab
  refine ⟨c,?_,hck⟩
  apply sub_eq_zero.mp
  exact hc.trans (hNoReturn b z)

end
end KIP126.ProofTools.Internal.Mahowald.ThreeByThree

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Kervaire.Route KIP126.Literature
open KIP126.AdamsSynthetic.Standard
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

/-- The normalized finite common lift from one fixed distinguished horizontal
row. All rho, lambda and quotient maps are the existing selected maps.

This conditional theorem does not establish its horizontal-row premise.
Its finite tail is fixed in advance and can be the literal negative of the
quotient of a suspended map, followed by one chosen suspension comparison.
No additivity of the quotient functor is assumed. A future producer may supply
a canonical comparison and row; spherewise comparison independence, rather
than global distinguishedness for every comparison, handles other choices. -/
private theorem normalized_finite_may_of_horizontal_row
    (X Y : ClassicalObject) (Z Cg : SyntheticSpectrum)
    (ef eg : ℤ) (hef : 0 ≤ ef)
    (eC : Cg ≅ (SyntheticCategory.biShift (1,ef+eg)).obj
      (model.nu.functor.obj (X.obj model.auxiliary)))
    (G : (SyntheticCategory.biShift (0,eg)).obj
      (model.nu.functor.obj (Y.obj model.auxiliary)) ⟶ Z)
    (h : Z ⟶ Cg)
    (i q : ℕ) (hi : 0 < i) (hq : 0 < q)
    (kN : XModLambdaN Cg (i+q) ⟶
      (XModLambdaN ((SyntheticCategory.biShift (0,eg)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) (i+q))⟦(1:ℤ)⟧)
    (hRow : Triangle.mk (XModLambdaN.map G (i+q)) (XModLambdaN.map h (i+q))
        kN ∈ distTriang SyntheticSpectrum)
    (m w : ℤ)
    (a : BiHom m w (XModLambdaN Z i))
    (b : BiHom m w (((SyntheticCategory.biShift (0,-(i:ℤ))).obj
      (XModLambdaN ((SyntheticCategory.biShift (0,eg)).obj
        (model.nu.functor.obj (Y.obj model.auxiliary))) ((i+q)-i)))⟦(1:ℤ)⟧))
    (hab : a ≫ ((model.quotients.tower Z).triangle hi (show i < i+q by omega)).delta =
      b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
        ((SyntheticCategory.biShift (0,-(i:ℤ))).map (XModLambdaN.map G ((i+q)-i)))) :
    ∃ c : BiHom m w (XModLambdaN Cg (i+q)),
      c ≫ (model.quotients.tower Cg).rho i (i+q) (by omega) =
        a ≫ XModLambdaN.map h i ∧
      c ≫ kN =
        b ≫ (shiftFunctor SyntheticSpectrum (1:ℤ)).map
          ((model.quotients.tower _).triangle hi (show i < i+q by omega)).lambdaMap := by
  letI := model.exactness.syntheticTriangulated
  let U := (SyntheticCategory.biShift (0,eg)).obj
    (model.nu.functor.obj (Y.obj model.auxiliary))
  let F := SyntheticCategory.biShift (Syn:=SyntheticSpectrum) (0,-(i:ℤ))
  let LZ := (model.quotients.tower Z).triangle hi (show i < i+q by omega)
  let LY := (model.quotients.tower U).triangle hi (show i < i+q by omega)
  have hSquare : LY.lambdaMap ≫ XModLambdaN.map G (i+q) =
      F.map (XModLambdaN.map G ((i+q)-i)) ≫ LZ.lambdaMap :=
    ((model.quotients.natural G).lambda_naturality hi (show i < i+q by omega)).symm
  have hRho : XModLambdaN.map h (i+q) ≫ (model.quotients.tower Cg).rho i (i+q) (by omega) =
      LZ.rho ≫ XModLambdaN.map h i := by
    rw [(model.quotients.tower Z).triangle_rho hi (show i < i+q by omega)]
    exact ((model.quotients.natural h).rho_naturality (show i ≤ i+q by omega)).symm
  obtain ⟨c,hc,hck⟩ := ThreeByThree.common_lift_of_no_return
    (F.map (XModLambdaN.map G ((i+q)-i))) LZ.lambdaMap LY.lambdaMap
    (XModLambdaN.map G (i+q)) (XModLambdaN.map h (i+q))
    kN LZ.rho LZ.delta (XModLambdaN.map h i)
    ((model.quotients.tower Cg).rho i (i+q) (by omega)) LZ.distinguished hRow hSquare hRho
    (fun b z => normalized_finite_no_return X Y Cg ef eg hef eC ((i+q)-i) i
      (by omega) hi m w b z) a b hab
  refine ⟨c,?_,?_⟩
  · exact hc
  · simpa only [Category.assoc] using hck

end
end KIP126.ProofTools.Internal.Mahowald
