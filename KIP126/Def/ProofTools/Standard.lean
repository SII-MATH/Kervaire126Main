module

public import KIP126.Def.ProofTools.FiniteFiltration
public import KIP126.Def.ProofTools.GeneralizedLeibniz

/-! Callable paper tools on the fixed upstream system. These are results of
AimPaper, not outside literature assumptions. The pending ports below retain
exact source statements and are tracked separately from new mathematical
proof debts; complete pinned proof text is retained in the migration archive. -/

@[expose] section
namespace KIP126.ProofTools.Standard
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Kervaire.Route KIP126.AdamsSynthetic.Standard
noncomputable section

/-- AimPaper finite stretching criterion (`prop:dec738d3`, strengthened
layer-preserving sufficient condition). The pinned source proof is complete;
its adaptation from concrete tower internals remains a proof-port obligation.
The three finite-filtration arguments have already been migrated with proofs.
This does not assert an infinite lift or a compatible tower of strict lifts. -/
public theorem finitePageExtensionStretching
    (X Y : ClassicalObject) (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    FinitePageExtensionStretchingLaw model X Y f := by
  intro rEarlier rLater n s t x y hr hle hn hnUpper hx hy hW hcross
  by_cases hsame : rEarlier = rLater
  · subst rLater
    exact hW
  -- Proof-port obligation: the nontrivial finite correction proof is present
  -- in pinned PageExtensionStretching/Proofs.lean, not a new accepted axiom.
  sorry

/-- AimPaper Theorem 6.12 (`thm:158d451a`). The fixed upstream May signed
boundary theorem and synthetic comparisons are available directly. The
compatible normalized triangle and all page/crossing hypotheses remain in
`GeneralizedMahowaldLaw`. Pinned proof had two geometric gaps, MH1 and MH2;
its proved auxiliary cases still require adaptation to the abstract tower API. -/
public theorem generalizedMahowald (T : TriangleData model.auxiliary) :
    GeneralizedMahowaldLaw model T := by
  -- Port the retained 3402-line source proof; its existing MH1 and MH2
  -- obligations belong to AimPaper, while upstream constructions do not.
  sorry

end
end KIP126.ProofTools.Standard
