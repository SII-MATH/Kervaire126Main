module

public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Smash.Good.Proofs
public import KIP126.Def.StableHomotopy.Spectra.Prespectrum.Smash.Diagonal.Map.Data

@[expose] public section

/-! A point-set sequential smash construction. The even level 2n is
Xₙ∧Yₙ, and the intervening odd level is its suspension. Thus both suspension
coordinates are accounted for; Xₙ∧Yₙ is never incorrectly put in level n.
The point-set definitions and good replacements are imported from their
dedicated modules. The double bonds follow MMSS, Definition 11.6.
Descent to the stable localization still requires the flatness statement
(cf. MMSS, Proposition 11.7), which is not established in this file. -/
namespace KIP126.StableHomotopy.Spectra
open CategoryTheory _root_.Topology
open scoped unitInterval
namespace Prespectrum

private theorem stable_even_representative (P : Prespectrum.{0}) (d : ℤ)
    (x : StableHomotopy P d) :
    ∃ a : Representative P d, a.stage % 2 = 0 ∧ Quot.mk _ a = x := by
  refine Quot.inductionOn x ?_
  intro a
  by_cases h : a.stage % 2 = 0
  · exact ⟨a,h,rfl⟩
  · refine ⟨a.next,?_,(Quot.sound (StableRelation.stabilization a)).symm⟩
    change (a.stage+1)%2=0
    omega

private theorem stableHomotopy_equiv_of_even_loops (P Q : Prespectrum.{0})
    (L : ∀ n r, GenLoop (Fin r) (P.level n) (P.level n).point →
      GenLoop (Fin r) (Q.level n) (Q.level n).point)
    (M : ∀ n r, GenLoop (Fin r) (Q.level n) (Q.level n).point →
      GenLoop (Fin r) (P.level n) (P.level n).point)
    (hL : ∀ n r p q, GenLoop.Homotopic p q → GenLoop.Homotopic (L n r p) (L n r q))
    (hM : ∀ n r p q, GenLoop.Homotopic p q → GenLoop.Homotopic (M n r p) (M n r q))
    (hLstep : ∀ n r (_hn : n%2=0) p,
      L (n+2) (r+2) (stabilizeLoop P (n+1) (r+1) (stabilizeLoop P n r p)) =
        stabilizeLoop Q (n+1) (r+1) (stabilizeLoop Q n r (L n r p)))
    (hMstep : ∀ n r (_hn : n%2=0) p,
      M (n+2) (r+2) (stabilizeLoop Q (n+1) (r+1) (stabilizeLoop Q n r p)) =
        stabilizeLoop P (n+1) (r+1) (stabilizeLoop P n r (M n r p)))
    (hML : ∀ n r p, M n r (L n r p)=p)
    (hLM : ∀ n r p, L n r (M n r p)=p) (d : ℤ) :
    ∃ e : StableHomotopy P d ≃ StableHomotopy Q d,
      ∀ a : Representative P d, a.stage%2=0 →
        e (Quot.mk _ a) = Quot.mk _ ⟨a.stage,a.dimension,a.degree,L _ _ a.loop⟩ := by
  have stabilizeLoop_homotopic (P : Prespectrum.{0}) (n r : ℕ)
      (p q : GenLoop (Fin r) (P.level n) (P.level n).point) (h : GenLoop.Homotopic p q) :
      GenLoop.Homotopic (stabilizeLoop P n r p) (stabilizeLoop P n r q) := by
    obtain ⟨H⟩ := h
    refine ⟨{ toFun := fun t => P.bond n (H (t.1,fun i => t.2 i.succ),t.2 0)
              continuous_toFun := (P.bond n).continuous.comp
                ((H.continuous.comp (continuous_fst.prodMk
                  (continuous_pi fun i => (continuous_apply i.succ).comp continuous_snd))).prodMk
                    ((continuous_apply 0).comp continuous_snd))
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro t
      change P.bond n (H (0,_),_) = _
      rw [H.apply_zero]
      rfl
    · intro t
      change P.bond n (H (1,_),_) = _
      rw [H.apply_one]
      rfl
    · intro s t ht
      obtain ⟨i,hi⟩ := ht
      induction i using Fin.cases with
      | zero =>
        rcases hi with h | h
        · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
          rw [h,P.bond_zero,P.bond_zero]
        · change P.bond n (H (s,_),t 0) = P.bond n (p _,t 0)
          rw [h,P.bond_one,P.bond_one]
      | succ j =>
        change P.bond n (H (s,_),_) = P.bond n (p _,_)
        rw [H.eq_fst s ⟨j,hi⟩]
        rfl
  let mapRep {R S : Prespectrum.{0}}
      (U : ∀ n r, GenLoop (Fin r) (R.level n) (R.level n).point →
        GenLoop (Fin r) (S.level n) (S.level n).point)
      (a : Representative R d) : Representative S d :=
    ⟨a.stage,a.dimension,a.degree,U _ _ a.loop⟩
  let φ {R S : Prespectrum.{0}}
      (U : ∀ n r, GenLoop (Fin r) (R.level n) (R.level n).point →
        GenLoop (Fin r) (S.level n) (S.level n).point)
      (a : Representative R d) : StableHomotopy S d :=
    if a.stage%2=0 then Quot.mk _ (mapRep U a) else Quot.mk _ (mapRep U a.next)
  have respects {R S : Prespectrum.{0}}
      (U : ∀ n r, GenLoop (Fin r) (R.level n) (R.level n).point →
        GenLoop (Fin r) (S.level n) (S.level n).point)
      (hU : ∀ n r p q, GenLoop.Homotopic p q → GenLoop.Homotopic (U n r p) (U n r q))
      (hUstep : ∀ n r (_hn : n%2=0) p,
        U (n+2) (r+2) (stabilizeLoop R (n+1) (r+1) (stabilizeLoop R n r p)) =
          stabilizeLoop S (n+1) (r+1) (stabilizeLoop S n r (U n r p))) :
      ∀ a b, StableRelation R d a b → φ U a = φ U b := by
    intro a b h
    cases h with
    | homotopy p hp =>
      by_cases he : a.stage%2=0
      · dsimp only [φ]
        rw [if_pos he,if_pos he]
        exact Quot.sound (StableRelation.homotopy (mapRep U a) _ (hU _ _ _ _ hp))
      · have hh := hU _ _ _ _ (stabilizeLoop_homotopic R _ _ _ _ hp)
        dsimp only [φ]
        rw [if_neg he,if_neg he]
        exact Quot.sound (StableRelation.homotopy (mapRep U a.next) _ hh)
    | stabilization =>
      by_cases he : a.stage%2=0
      · have ho : a.next.stage%2≠0 := by change (a.stage+1)%2≠0; omega
        dsimp only [φ]
        rw [if_pos he,if_neg ho]
        have hs : mapRep U a.next.next = (mapRep U a).next.next := by
          cases a with
          | mk n r hd p =>
            dsimp only [mapRep,Representative.next]
            congr 1
            exact hUstep n r he p
        rw [hs]
        exact (Quot.sound (StableRelation.stabilization (mapRep U a))).trans
          (Quot.sound (StableRelation.stabilization (mapRep U a).next))
      · have hz : a.next.stage%2=0 := by change (a.stage+1)%2=0; omega
        dsimp only [φ]
        rw [if_neg he,if_pos hz]
  let F : StableHomotopy P d → StableHomotopy Q d := Quot.lift (φ L) (respects L hL hLstep)
  let G : StableHomotopy Q d → StableHomotopy P d := Quot.lift (φ M) (respects M hM hMstep)
  have hinv {R S : Prespectrum.{0}}
      (U : ∀ n r, GenLoop (Fin r) (R.level n) (R.level n).point →
        GenLoop (Fin r) (S.level n) (S.level n).point)
      (V : ∀ n r, GenLoop (Fin r) (S.level n) (S.level n).point →
        GenLoop (Fin r) (R.level n) (R.level n).point)
      (hVU : ∀ n r p, V n r (U n r p)=p)
      (rU : ∀ a b, StableRelation R d a b → φ U a=φ U b)
      (rV : ∀ a b, StableRelation S d a b → φ V a=φ V b)
      (x : StableHomotopy R d) :
      Quot.lift (φ V) rV (Quot.lift (φ U) rU x)=x := by
    obtain ⟨a,ha,rfl⟩ := stable_even_representative R d x
    change Quot.lift (φ V) rV (φ U a)=Quot.mk _ a
    dsimp only [φ]
    rw [if_pos ha]
    change φ V (mapRep U a)=Quot.mk _ a
    dsimp only [φ]
    rw [if_pos ha]
    congr 1
    cases a with
    | mk n r hd p =>
      dsimp only [mapRep]
      rw [hVU]
  refine ⟨⟨F,G,hinv L M hML _ _,hinv M L hLM _ _⟩,?_⟩
  intro a ha
  change φ L a = _
  exact if_pos ha

private theorem diagonalSmash_stable_swap :
    ∃ e : ∀ (X Y : Prespectrum.{0}) (d : ℤ),
      StableHomotopy (diagonalSmash X Y) d ≃ StableHomotopy (diagonalSmash Y X) d,
      ∀ {X Y X' Y' : Prespectrum.{0}} (f : X ⟶ X') (g : Y ⟶ Y') (d : ℤ) a,
        e X' Y' d (stableHomotopyMap (diagonalSmashMap f g) d a) =
          stableHomotopyMap (diagonalSmashMap g f) d (e X Y d a) := by
  let blocks (n : ℕ) : (Fin 2 ⊕ Fin n) ≃ Fin (n+2) :=
    finSumFinEquiv.trans (finCongr (Nat.add_comm 2 n))
  let pairSwap : (n : ℕ) → Fin n ≃ Fin n :=
    Nat.twoStepInduction (Equiv.refl _) (Equiv.refl _) (fun n ih _ =>
      (blocks n).symm.trans
        ((Equiv.sumCongr (Equiv.swap (0 : Fin 2) 1) ih).trans (blocks n)))
  have blocks_zero (n : ℕ) : blocks n (.inl 0) = 0 := by
    apply Fin.ext
    rfl
  have blocks_one (n : ℕ) : blocks n (.inl 1) = 1 := by
    apply Fin.ext
    rfl
  have blocks_right (n : ℕ) (i : Fin n) : blocks n (.inr i) = i.succ.succ := by
    apply Fin.ext
    simp only [blocks,Equiv.trans_apply,finSumFinEquiv_apply_right,finCongr_apply,Fin.val_cast,Fin.val_natAdd,Fin.val_succ]
    omega
  have sigma_zero (n : ℕ) : pairSwap (n+2) 0 = 1 := by
    rw [← blocks_zero n]
    simp only [pairSwap,Nat.twoStepInduction,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply]
    simp [blocks_one]
  have sigma_one (n : ℕ) : pairSwap (n+2) 1 = 0 := by
    rw [← blocks_one n]
    simp only [pairSwap,Nat.twoStepInduction,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply]
    simp [blocks_zero]
  have sigma_succ_succ (n : ℕ) (i : Fin n) :
      pairSwap (n+2) i.succ.succ = (pairSwap n i).succ.succ := by
    rw [← blocks_right n i]
    simp only [pairSwap,Nat.twoStepInduction,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply]
    exact blocks_right n _
  have sigma_involutive (n : ℕ) : Function.Involutive (pairSwap n) := by
    induction n using Nat.twoStepInduction with
    | zero => intro i; exact Fin.elim0 i
    | one => intro i; rfl
    | more n hn _ =>
      intro i
      obtain ⟨j,rfl⟩ := (blocks n).surjective i
      cases j with
      | inl j =>
        fin_cases j <;> simp [blocks_zero,blocks_one,sigma_zero,sigma_one]
      | inr j =>
        rw [blocks_right,sigma_succ_succ,sigma_succ_succ,hn]
  let S (X Y : Prespectrum.{0}) (n : ℕ) : diagonalLevel X Y n ⟶ diagonalLevel Y X n :=
    Nat.twoStepInduction (motive := fun n => ∀ X Y : Prespectrum.{0},
      diagonalLevel X Y n ⟶ diagonalLevel Y X n)
      (fun X Y => BasedSpace.smashSwap (X.level 0) (Y.level 0))
      (fun X Y => BasedSpace.suspendMap (BasedSpace.smashSwap (X.level 0) (Y.level 0)))
      (fun _ ih _ X Y => ih X.tail Y.tail) n X Y
  have hs (A B : BasedSpace.{0}) (a : A) (b : B) :
      (BasedSpace.smashSwap A B).map (BasedSpace.smashPoint A B a b) =
        BasedSpace.smashPoint B A b a :=
    (BasedSpace.smashCoherence_exists.2 A B).exists.choose_spec a b
  have hinv (X Y : Prespectrum.{0}) (n : ℕ) (a : diagonalLevel X Y n) :
      (S Y X n).map ((S X Y n).map a)=a := by
    induction n using Nat.twoStepInduction generalizing X Y with
    | zero =>
      refine Quot.inductionOn a ?_
      rintro ⟨x,y⟩
      change (BasedSpace.smashSwap _ _).map ((BasedSpace.smashSwap _ _).map
        (BasedSpace.smashPoint _ _ x y)) = _
      rw [hs,hs]
      rfl
    | one =>
      refine Quot.inductionOn a ?_
      rintro ⟨p,t⟩
      refine Quot.inductionOn p ?_
      rintro ⟨x,y⟩
      change BasedSpace.suspensionProjection _
        ((BasedSpace.smashSwap _ _).map ((BasedSpace.smashSwap _ _).map
          (BasedSpace.smashPoint _ _ x y)),t) = _
      rw [hs,hs]
      rfl
    | more n hn _ => exact hn X.tail Y.tail a
  have hnat {X Y X' Y' : Prespectrum.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
      (n : ℕ) (a : diagonalLevel X Y n) :
      (S X' Y' n).map ((diagonalMapLevel f g n).map a) =
        (diagonalMapLevel g f n).map ((S X Y n).map a) := by
    have hm {A B A' B' : BasedSpace.{0}} (f : A ⟶ A') (g : B ⟶ B') (a : A) (b : B) :
        (BasedSpace.smashMap f g).map (BasedSpace.smashPoint _ _ a b) =
          BasedSpace.smashPoint _ _ (f.map a) (g.map b) :=
      (BasedSpace.smashMap_exists f g).exists.choose_spec a b
    induction n using Nat.twoStepInduction generalizing X Y X' Y' with
    | zero =>
      refine Quot.inductionOn a ?_
      rintro ⟨x,y⟩
      change (BasedSpace.smashSwap _ _).map ((BasedSpace.smashMap _ _).map
        (BasedSpace.smashPoint _ _ x y)) =
        (BasedSpace.smashMap _ _).map ((BasedSpace.smashSwap _ _).map
          (BasedSpace.smashPoint _ _ x y))
      rw [hm,hs,hs,hm]
    | one =>
      refine Quot.inductionOn a ?_
      rintro ⟨p,t⟩
      refine Quot.inductionOn p ?_
      rintro ⟨x,y⟩
      change BasedSpace.suspensionProjection _
        ((BasedSpace.smashSwap _ _).map ((BasedSpace.smashMap _ _).map
          (BasedSpace.smashPoint _ _ x y)),t) =
        BasedSpace.suspensionProjection _
          ((BasedSpace.smashMap _ _).map ((BasedSpace.smashSwap _ _).map
            (BasedSpace.smashPoint _ _ x y)),t)
      rw [hm,hs,hs,hm]
    | more n hn _ => exact hn (tailMap f) (tailMap g) a
  have hdouble (X Y : Prespectrum.{0}) (n : ℕ) (hn : n%2=0)
      (a : diagonalLevel X Y n) (s t : I) :
      (S X Y (n+2)).map (diagonalBond X Y (n+1) (diagonalBond X Y n (a,s),t)) =
        diagonalBond Y X (n+1) (diagonalBond Y X n ((S X Y n).map a,t),s) := by
    induction n using Nat.twoStepInduction generalizing X Y with
    | zero =>
      refine Quot.inductionOn a ?_
      rintro ⟨x,y⟩
      have hp (U V : Prespectrum.{0}) (x : U.level 0) (y : V.level 0) (s t : I) :
          pairedBond U V (BasedSpace.suspensionProjection _
            (BasedSpace.smashPoint _ _ x y,s),t) =
            BasedSpace.smashPoint _ _ (U.bond 0 (x,s)) (V.bond 0 (y,t)) :=
        (pairedBond_exists U V).exists.choose_spec.1 x y s t
      change (BasedSpace.smashSwap _ _).map
        (pairedBond X Y (BasedSpace.suspensionProjection _ (BasedSpace.smashPoint _ _ x y,s),t)) =
        pairedBond Y X (BasedSpace.suspensionProjection _
          ((BasedSpace.smashSwap _ _).map (BasedSpace.smashPoint _ _ x y),t),s)
      rw [hp,hs,hs,hp]
    | one => omega
    | more n ih _ => exact ih X.tail Y.tail (by omega) a
  let L (X Y : Prespectrum.{0}) (n r : ℕ)
      (p : GenLoop (Fin r) ((diagonalSmash X Y).level n) ((diagonalSmash X Y).level n).point) :
      GenLoop (Fin r) ((diagonalSmash Y X).level n) ((diagonalSmash Y X).level n).point :=
    ⟨(S X Y n).map.comp ((GenLoop.congr _ (pairSwap r)) p).val,by
      intro t ht
      exact (congrArg (S X Y n).map (((GenLoop.congr _ (pairSwap r)) p).property t ht)).trans
        (S X Y n).point⟩
  have hL (X Y : Prespectrum.{0}) (n r : ℕ) (p q) (h : GenLoop.Homotopic p q) :
      GenLoop.Homotopic (L X Y n r p) (L X Y n r q) := by
    obtain ⟨H⟩ := h
    have hp : GenLoop.Homotopic ((GenLoop.congr _ (pairSwap r)) p) ((GenLoop.congr _ (pairSwap r)) q) := by
      refine ⟨{ toFun := fun t => H (t.1,fun i => t.2 (pairSwap r i))
                continuous_toFun := H.continuous.comp
                  (continuous_fst.prodMk (continuous_pi fun i =>
                    (continuous_apply (pairSwap r i)).comp continuous_snd))
                map_zero_left := ?_
                map_one_left := ?_
                prop' := ?_ }⟩
      · intro t
        exact H.apply_zero _
      · intro t
        exact H.apply_one _
      · intro s t ht
        obtain ⟨i,hi⟩ := ht
        exact H.eq_fst s ⟨(pairSwap r).symm i,by simpa using hi⟩
    exact hp.comp_continuousMap (S X Y n).map
  have hLstep (X Y : Prespectrum.{0}) (n r : ℕ) (hn : n%2=0) (p) :
      L X Y (n+2) (r+2)
        (stabilizeLoop (diagonalSmash X Y) (n+1) (r+1)
          (stabilizeLoop (diagonalSmash X Y) n r p)) =
        stabilizeLoop (diagonalSmash Y X) (n+1) (r+1)
          (stabilizeLoop (diagonalSmash Y X) n r (L X Y n r p)) := by
    apply GenLoop.ext
    intro t
    change (S X Y (n+2)).map (diagonalBond X Y (n+1)
      (diagonalBond X Y n (p (fun i => t (pairSwap (r+2) i.succ.succ)),t (pairSwap (r+2) 1)),t (pairSwap (r+2) 0))) =
        diagonalBond Y X (n+1) (diagonalBond Y X n
          ((S X Y n).map (p (fun i => t (pairSwap r i).succ.succ)),t 1),t 0)
    simp only [sigma_zero,sigma_one,sigma_succ_succ]
    exact hdouble X Y n hn _ _ _
  have hLL (X Y : Prespectrum.{0}) (n r : ℕ) (p) : L Y X n r (L X Y n r p)=p := by
    apply GenLoop.ext
    intro t
    change (S Y X n).map ((S X Y n).map (p (fun i => t (pairSwap r (pairSwap r i)))))=p t
    have hpi : (fun i => t (pairSwap r (pairSwap r i)))=t :=
      funext (fun i => congrArg t (sigma_involutive r i))
    rw [hpi,hinv]
  obtain ⟨e,he⟩ : ∃ e : ∀ (X Y : Prespectrum.{0}) (d : ℤ),
      StableHomotopy (diagonalSmash X Y) d ≃ StableHomotopy (diagonalSmash Y X) d,
      ∀ X Y d (a : Representative (diagonalSmash X Y) d), a.stage%2=0 →
        e X Y d (Quot.mk _ a)=Quot.mk _ ⟨a.stage,a.dimension,a.degree,L X Y _ _ a.loop⟩ := by
    choose e he using fun X Y d => stableHomotopy_equiv_of_even_loops
      (diagonalSmash X Y) (diagonalSmash Y X) (L X Y) (L Y X)
        (hL X Y) (hL Y X) (hLstep X Y) (hLstep Y X) (hLL X Y) (hLL Y X) d
    exact ⟨e,he⟩
  refine ⟨e,?_⟩
  intro X Y X' Y' f g d a
  obtain ⟨a,ha,rfl⟩ := stable_even_representative (diagonalSmash X Y) d a
  change e X' Y' d (Quot.mk _ (a.map (diagonalSmashMap f g))) = _
  rw [he X' Y' d _ ha,he X Y d a ha]
  change Quot.mk _ _ = Quot.mk _ _
  congr 1
  cases a with
  | mk n r hd p =>
    dsimp only [Representative.map]
    congr 1
    apply GenLoop.ext
    intro t
    exact hnat f g n (p (fun i => t (pairSwap r i)))
/-- The zeroth-stage inclusion is the free/evaluation counit. -/
noncomputable def zeroStage (X : Prespectrum.{0}) : suspensionSpectrum (X.level 0) ⟶ X :=
  freeCounit X 0

end Prespectrum
end KIP126.StableHomotopy.Spectra
