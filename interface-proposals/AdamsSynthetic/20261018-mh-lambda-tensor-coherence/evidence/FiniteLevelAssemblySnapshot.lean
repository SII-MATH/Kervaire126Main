module

import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelStatement
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelInputs
import all KIP126.ProofTools.GeneralizedMahowald.FiniteMayAtTriangle
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelConclusion
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelSourceLabel
import all KIP126.ProofTools.GeneralizedMahowald.FiniteLevelOutputLabels

/-! Complete conditional proof of the full finite-layer Mahowald target.
The structural horizontal-row predicate is not asserted here. Its fixed-model
producer remains an upstream responsibility requiring separate interface review.
Every input, representative, signed image, detection and terminal conclusion
is the one specified in the public target proposition. -/

@[expose] section
namespace KIP126.ProofTools.Internal.Mahowald
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP126.StableHomotopy KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.AdamsSynthetic KIP126.Core.SpectralSequence KIP126.Kervaire.Route
open KIP126.AdamsSynthetic.Standard KIP126.Literature
open KIP126.ProofTools.Internal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

private theorem finite_mahowald_at_level_of_horizontal_rows (hRows : NormalizedFiniteQuotientHorizontalRows) (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    KIP126.ProofTools.Standard.FiniteMahowaldAtLevelStatement T he := by
  unfold KIP126.ProofTools.Standard.FiniteMahowaldAtLevelStatement
  intro shiftFinitePageLabel hT n₁ m₁ k i j hn₁ hj s t
    ef eg eh n m l r A B N K J Q V VX VY VZ QA HA DB GB CN FN p
    hA hAN F LZ LY delta lambdaY exA exN eyN hincA hincN hincY
    hmap dmap gmap Mh Md Mg xbar x y ybar hxbar hdclass hybar hx hy
    xbarA xA yB ybarB xN yN e0 ex ey ez hxbarInf hxInf hyInf hybarInf hh hd hg hnc
  have hB : 0 < B := by dsimp [B]; omega
  have hfil : (s+l+n)+m=s+r := by dsimp [r]; omega
  have hwindow : (B:ℤ) ≤ p.1+(s+r)-p.2-A+(-eg) :=
    (finite_level_input_top_window T he n₁ m₁ k i j hj s t).le
  obtain ⟨a,b,ha,hah,had,hb,hbg,hab⟩ := finite_level_synchronized_inputs
    VX VY T.Z (-eg) V.mor₃ V.mor₂ A B hA hB exA
    p s l r (s+l+n) m hfil hwindow
    xbarA xA yB ybarB e0 ex ey ez hxbarInf hxInf hyInf hybarInf hh hd hg hnc
  have may : ∀ (a : BiHom p.1 p.2 (XModLambdaN V.obj₃ A))
      (b : BiHom p.1 p.2 ((F.obj (XModLambdaN V.obj₂ B))⟦(1:ℤ)⟧)),
      a≫delta=b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map
        (F.map (XModLambdaN.map V.mor₂ B)) →
      ∃ c : BiHom p.1 p.2 (XModLambdaN (V.obj₁⟦(1:ℤ)⟧) N),
        c≫(model.quotients.tower _).rho A N hAN.le=a≫XModLambdaN.map V.mor₃ A ∧
        c≫XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) N≫eyN.hom=
          -(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map lambdaY) := by
    exact finite_may_at_normalized_triangle_explicit_lengths hRows T he hT A B hA hB p.1 p.2 eyN hincY
  obtain ⟨c,hcr,hcf⟩ := may a b hab
  refine ⟨a,b,c,ha,hah,had,hb,hbg,hab,hcr,hcf,?_⟩
  have hKN : K<N := by dsimp [K,N,A,B]; omega
  have hJN : J<N := by dsimp [J,N,B]; omega
  have hn : (normalizedExponent model.classicalTower T.f:ℤ) ≤ n := by dsimp [n,ef]; omega
  have hJNat : J=K+n₁ := by dsimp [J,K,A]; omega
  have hJ : (J:ℤ)=(K:ℤ)+n-normalizedExponent model.classicalTower T.f := by
    rw [hJNat]
    simp only [Nat.cast_add]
    dsimp [n,ef]
    omega
  have hp : p.1=(t+l-1)-(s+l)+1 := by dsimp [p]; omega
  have he' : ef+eg+eh=1 := he
  have hw : p.2=(t+l-1)+normalizedExponent model.classicalTower T.f-K := by
    dsimp only [p,K,l]
    simp only [Nat.cast_add]
    change t-i-eg=t+(↑k+eh)-1+ef-(↑i+↑k)
    omega
  let yy : Ambient model T.Y ((s+l)+n,(t+l-1)+n) :=
    (eqToHom (congrArg (fun q => (model.classical.obj (T.Y.obj model.auxiliary)).Page 2 q)
      (show (s+l+n,t+l+n-1)=(s+l+n,t+l-1+n) by ext <;> omega))) y
  have conclusion := finite_level_conclusion_of_suspended_detects T.X T.Y T.f N K J hKN hJN
    n (s+l) (t+l-1) hn hJ p hp hw x yy exN eyN hincN hincY c
  have finish
      (hcx : Detects (model.convergence CN) (s+l,p.1+(s+l),p.2) xN
        (homotopyRegrade (by dsimp; omega) rfl
          (c≫exN.hom≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)))
      (hcy : Detects (model.convergence FN) (s+l+n,p.1+(s+l+n),p.2) yN
        (homotopyRegrade (by dsimp; omega) rfl
          (c≫XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) N≫eyN.hom≫
            (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _))) :
      IsCycle model T.X Q (s+l,t+l-1) x ∧
        KIP126.ProofTools.Standard.LevelFiniteExtension T.X T.Y T.f (Q+1) K n
          (s+l) (t+l-1) x yy := by
    have hcx' : Detects (model.convergence CN) (s+l,p.1+(s+l),p.2)
        (finiteConclusionSourceLabel T.X N K ef (s+l) (t+l-1) p hp hw x)
        (homotopyRegrade (by dsimp; omega) rfl
          (c≫exN.hom≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) := by
      simpa only [xN,finiteConclusionSourceLabel,finiteConclusionShiftLabel,shiftFinitePageLabel,VX] using hcx
    have hyp : HEq y yy := by
      have point {u v : ℤ×ℤ} (h : u=v) (z : Ambient model T.Y u) :
          HEq z ((eqToHom (congrArg
            (fun q => (model.classical.obj (T.Y.obj model.auxiliary)).Page 2 q) h)) z) := by
        subst v
        rfl
      exact point (show (s+l+n,t+l+n-1)=(s+l+n,t+l-1+n) by ext <;> omega) y
    have hyLabel : yN=finiteConclusionTargetLabel T.Y N J (s+l) (t+l-1) n p hp (by omega) yy := by
      simpa only [yN,shiftFinitePageLabel,VY,finiteConclusionShiftLabel] using
        (finite_conclusion_target_label_regrade T.Y N J (s+l) (t+l-1) n p hp (by omega)
          (t+l+n-1) (by omega) y yy hyp _)
    have hcy' := hcy
    rw [hyLabel] at hcy'
    obtain ⟨hcycle,hext⟩ := conclusion hcx' hcy'
    refine ⟨?_,hext⟩
    convert hcycle using 1
    dsimp [Q]
    omega
  have hKA : K<A := by dsimp [K,A]; omega
  obtain ⟨hcx0,_⟩ := finite_suspended_source_label_reflection T.X ef A N K hAN.le hKA
    (s+l) (t+l-1) p hp hw x exA exN hincA hincN
    (a≫XModLambdaN.map V.mor₃ A) c hcr (by
      simpa only [hmap,Category.assoc,xA,finiteConclusionSourceLabel,
        finiteConclusionShiftLabel,shiftFinitePageLabel,VX,mhInputH,mhInputHMap,
        SyntheticObject.obj] using hah)
  have hcx : Detects (model.convergence CN) (s+l,p.1+(s+l),p.2) xN
      (homotopyRegrade (by dsimp; omega) rfl
        (c≫exN.hom≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) := by
    simpa only [xN,finiteConclusionSourceLabel,finiteConclusionShiftLabel,shiftFinitePageLabel,VX,
      CN,V,normalizedTriangle,Triangle.mk,SyntheticObject.obj] using hcx0
  refine ⟨hcx,?_⟩
  have hpY : p.1=(t+l+n-1)-(s+l+n)+1 := by omega
  have hJsum : (J:ℤ)=(A:ℤ)+j := by dsimp [J]
  have hwY : p.2=(t+l+n-1)-j-A := by omega
  have hjB : j<B := by dsimp [B]; omega
  have hbInput : Detects (model.convergence GB) (s+l+n,p.1+(s+l+n),p.2)
      (finiteLambdaSuspendedInputLabel T.Y B A j (s+l+n) (t+l+n-1) p hpY hwY y)
      (homotopyRegrade (by dsimp; omega) rfl
        (b≫(SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) := by
    simpa only [yB,finiteLambdaSuspendedInputLabel,finiteConclusionShiftLabel,
      shiftFinitePageLabel,GB,VY,mhInputG] using hb
  have out := finite_lambda_suspended_signed_detects_explicit_lengths T.Y A B j hA hB hjB
    (s+l+n) (t+l+n-1) p hpY hwY y b hbInput
  have hyImage : Detects (model.convergence FN) (s+l+n,p.1+(s+l+n),p.2) yN
      (homotopyRegrade (by dsimp; omega) rfl
        ((-(b≫(shiftFunctor SyntheticSpectrum (1:ℤ)).map lambdaY))≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) := by
    have hyLabel : finiteLambdaSuspendedOutputLabel T.Y (A+B) A j
        (s+l+n) (t+l+n-1) p hpY hwY y = yN := by rfl
    rw [hyLabel] at out
    exact out
  rw [←hcf] at hyImage
  have hcy : Detects (model.convergence FN) (s+l+n,p.1+(s+l+n),p.2) yN
      (homotopyRegrade (by dsimp; omega) rfl
        (c≫XModLambdaN.map ((shiftFunctor SyntheticSpectrum (1:ℤ)).map V.mor₁) N≫eyN.hom≫
          (SyntheticCategory.biShift_compat (Syn:=SyntheticSpectrum) 1).inv.app _)) := by
    simpa only [Category.assoc] using hyImage
  exact ⟨hcy,finish hcx hcy⟩

end
end KIP126.ProofTools.Internal.Mahowald

