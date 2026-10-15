module
public import KIP126.Def.Computation.Table
public import KIP126.Def.Computation.Table.Dimensions

@[expose] section
namespace KIP126.Computation.Table

/-- Exact extra staircase states used by AlphaOne: sheet 23 row 61 (record
3005) and sheet 24 row 4 (record 3076). Level 9000 decodes to reaches 1000;
there is no permanence assertion here. -/
public def staircaseClaims : List Raw.Claim := [
  ⟨.sphere,.reaches,1000,14,138,[2],14,138,[],"S0_AdamsSS_staircase:23:61",3005⟩,
  ⟨.sphere,.reaches,1000,15,139,[1,3],15,139,[],"S0_AdamsSS_staircase:24:4",3076⟩
]

public theorem staircase_result (c : Raw.Claim) (hc : c ∈ staircaseClaims) :
    Statement c := by
  sorry

end KIP126.Computation.Table
