module
import all KIP126.E2Computation.Table.Internal.ZeroDimension

public import KIP126.E2Computation.Table
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The finite monomial-to-coordinate binding of the pinned sphere archive.
Expressions are evaluated using the existing actual sphere product and the
existing source generators/comparison, never an independent family of classes.
Rows are transcribed from LinProgram/Route/Selected.lean and the pinned
S0_AdamsE2_generators.csv (bbac1fc05843). -/
@[expose] section
namespace KIP126.Computation.Table
open CategoryTheory KIP126.AdamsSynthetic.Standard
noncomputable section

public inductive Expression where
  | one
  | named (a : Atom)
  | generator (id s t : ℕ)
  | mul (a b : Expression)
  deriving DecidableEq

public def Expression.degree : Expression → ℕ × ℕ
  | .one => (0,0)
  | .named a => a.degree
  | .generator _ s t => (s,t)
  | .mul a b => (a.degree.1+b.degree.1,a.degree.2+b.degree.2)

public def generatorImage (id s t : ℕ) : Page .sphere s t :=
  if ht : t ≤ 261 then
    if hi : id < Standard.archive.generators.count then
      if hd : Standard.archive.generators.degree ⟨id,hi⟩ = (s,t) then
        Standard.comparison s t ht
          ((eqToHom (congrArg (fun p : ℕ × ℕ => Standard.sourceData.component p.1 p.2) hd))
            (Standard.sourceGenerator ⟨id,hi⟩))
      else 0
    else 0
  else 0

public def Expression.value : (e : Expression) → Page .sphere e.degree.1 e.degree.2
  | .one => model.sphereAlgebra.unit
  | .named a => Standard.atom a
  | .generator id s t => generatorImage id s t
  | .mul a b => Standard.product a.value b.value
      (by simp only [Expression.degree, Prod.mk_add_mk, Nat.cast_add])

public structure BasisValue where
  expression : Expression
  index : ℕ
  deriving DecidableEq

public def basisValues : List BasisValue := [
  ⟨(.named .h0), 0⟩,
  ⟨(.named .h1), 0⟩,
  ⟨(.named .h2), 0⟩,
  ⟨(.named .h4), 0⟩,
  ⟨(.named .h5), 0⟩,
  ⟨(.named .h6), 0⟩,
  ⟨(.generator 324 1 128), 0⟩,
  ⟨(.mul (.named .h0) (.named .h0)), 0⟩,
  ⟨(.mul (.named .h1) (.named .h4)), 0⟩,
  ⟨(.mul (.named .h5) (.named .h5)), 0⟩,
  ⟨(.mul (.named .h0) (.named .h6)), 0⟩,
  ⟨(.mul (.named .h6) (.named .h6)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.named .h5) (.named .h5))), 0⟩,
  ⟨(.mul (.named .h1) (.mul (.named .h5) (.named .h5))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.named .h6)), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.named .h6) (.named .h6))), 0⟩,
  ⟨(.mul (.named .h1) (.mul (.named .h6) (.named .h6))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)), 0⟩,
  ⟨(.named .e0), 0⟩,
  ⟨(.named .g), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .h5) (.named .h5))), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h6)), 0⟩,
  ⟨(.named .x_126_4), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .h6) (.named .h6))), 1⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.generator 76 5 67), 0⟩,
  ⟨(.mul (.named .h1) (.generator 70 4 65)), 1⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.mul (.named .h5) (.named .h5))), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h6)), 0⟩,
  ⟨(.named .x_125_5), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.generator 378 5 133), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)), 0⟩,
  ⟨(.mul (.named .h5) (.generator 24 5 36)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h5) (.named .h5))), 1⟩,
  ⟨(.mul (.named .h1) (.generator 76 5 67)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h6)), 1⟩,
  ⟨(.generator 86 6 70), 0⟩,
  ⟨(.generator 339 6 130), 0⟩,
  ⟨(.mul (.named .h6) (.generator 76 5 67)), 0⟩,
  ⟨(.mul (.named .h0) (.named .x_125_5)), 1⟩,
  ⟨(.named .x_126_6), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 1⟩,
  ⟨(.generator 377 6 133), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.generator 399 6 134), 0⟩,
  ⟨(.generator 398 6 134), 1⟩,
  ⟨(.mul (.named .h2) (.named .x_125_5)), 2⟩,
  ⟨(.mul (.named .h0) (.generator 378 5 133)), 3⟩,
  ⟨(.mul (.named .h0) (.generator 75 6 67)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 74 6 67)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h5) (.named .h5))), 0⟩,
  ⟨(.generator 85 7 70), 0⟩,
  ⟨(.generator 84 7 70), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h6)), 2⟩,
  ⟨(.mul (.named .h2) (.generator 75 6 67)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 86 6 70)), 1⟩,
  ⟨(.named .x_121_7), 0⟩,
  ⟨(.mul (.generator 68 6 64) (.named .h6)), 1⟩,
  ⟨(.generator 353 7 131), 0⟩,
  ⟨(.mul (.named .h6) (.generator 75 6 67)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 339 6 130)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.named .x_125_5)), 0⟩,
  ⟨(.mul (.named .h1) (.mul (.named .h6) (.generator 76 5 67))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 1⟩,
  ⟨(.generator 397 7 134), 0⟩,
  ⟨(.generator 396 7 134), 1⟩,
  ⟨(.mul (.named .h1) (.named .x_126_6)), 2⟩,
  ⟨(.mul (.named .h0) (.generator 377 6 133)), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 4⟩,
  ⟨(.mul (.named .h2) (.mul (.named .h6) (.generator 76 5 67))), 0⟩,
  ⟨(.mul (.named .h0) (.generator 398 6 134)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 378 5 133)), 2⟩,
  ⟨(.mul (.named .g) (.named .g)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 74 6 67)), 0⟩,
  ⟨(.generator 83 8 70), 0⟩,
  ⟨(.named .b), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h5) (.named .h5))), 2⟩,
  ⟨(.mul (.named .h0) (.generator 84 7 70)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h6)), 1⟩,
  ⟨(.named .x_94_8), 0⟩,
  ⟨(.mul (.named .h1) (.named .x_121_7)), 0⟩,
  ⟨(.named .x_123_8), 0⟩,
  ⟨(.named .x_124_8), 0⟩,
  ⟨(.generator 376 8 133), 0⟩,
  ⟨(.named .x_125_8), 1⟩,
  ⟨(.named .x_126_8_4), 0⟩,
  ⟨(.generator 394 8 134), 1⟩,
  ⟨(.named .x_126_8_2), 2⟩,
  ⟨(.named .x_126_8), 3⟩,
  ⟨(.mul (.named .h6) (.generator 85 7 70)), 4⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 5⟩,
  ⟨(.generator 415 8 135), 0⟩,
  ⟨(.mul (.named .h2) (.generator 353 7 131)), 1⟩,
  ⟨(.mul (.named .h2) (.mul (.named .h6) (.generator 75 6 67))), 2⟩,
  ⟨(.mul (.named .h0) (.generator 397 7 134)), 3⟩,
  ⟨(.mul (.named .h0) (.generator 396 7 134)), 4⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 377 6 133)), 5⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 6⟩,
  ⟨(.mul (.generator 3 1 8) (.mul (.generator 68 6 64) (.named .h6))), 0⟩,
  ⟨(.named .delta_h_1_mul_g), 0⟩,
  ⟨(.named .b4), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 73 7 67)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h5) (.named .h5))), 0⟩,
  ⟨(.mul (.named .h1) (.named .b)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 84 7 70)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h6)), 2⟩,
  ⟨(.named .delta_h_6_mul_g), 0⟩,
  ⟨(.named .x_123_9), 0⟩,
  ⟨(.mul (.named .h0) (.named .x_123_8)), 1⟩,
  ⟨(.generator 374 9 133), 0⟩,
  ⟨(.generator 373 9 133), 1⟩,
  ⟨(.mul (.named .h0) (.named .x_124_8)), 2⟩,
  ⟨(.named .x_125_9_2), 0⟩,
  ⟨(.generator 390 9 134), 1⟩,
  ⟨(.mul (.named .h6) (.named .b)), 2⟩,
  ⟨(.mul (.named .h5) (.named .x_94_8)), 3⟩,
  ⟨(.mul (.named .h0) (.named .x_125_8)), 4⟩,
  ⟨(.generator 414 9 135), 0⟩,
  ⟨(.mul (.named .h1) (.generator 376 8 133)), 1⟩,
  ⟨(.mul (.named .h1) (.named .x_125_8)), 2⟩,
  ⟨(.mul (.named .h0) (.generator 394 8 134)), 3⟩,
  ⟨(.mul (.named .h0) (.named .x_126_8)), 4⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 5⟩,
  ⟨(.mul (.named .h1) (.named .x_126_8_2)), 0⟩,
  ⟨(.mul (.named .h1) (.named .x_126_8)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 415 8 135)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 396 7 134)), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 4⟩,
  ⟨(.mul (.named .h2) (.generator 376 8 133)), 0⟩,
  ⟨(.mul (.named .h1) (.generator 415 8 135)), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 3 1 8) (.mul (.generator 68 6 64) (.named .h6)))), 2⟩,
  ⟨(.named .M_mul_d_0), 0⟩,
  ⟨(.generator 90 10 72), 0⟩,
  ⟨(.generator 89 10 72), 1⟩,
  ⟨(.mul (.named .h1) (.generator 81 9 70)), 2⟩,
  ⟨(.generator 372 10 133), 0⟩,
  ⟨(.mul (.named .h6) (.named .b4)), 1⟩,
  ⟨(.mul (.named .h0) (.named .x_123_9)), 2⟩,
  ⟨(.generator 389 10 134), 0⟩,
  ⟨(.generator 388 10 134), 1⟩,
  ⟨(.mul (.named .h1) (.named .x_123_9)), 2⟩,
  ⟨(.mul (.named .h0) (.generator 373 9 133)), 3⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.named .x_124_8)), 4⟩,
  ⟨(.generator 413 10 135), 0⟩,
  ⟨(.generator 412 10 135), 1⟩,
  ⟨(.mul (.named .h0) (.named .x_125_9_2)), 2⟩,
  ⟨(.mul (.named .h0) (.generator 390 9 134)), 3⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.named .x_125_8)), 4⟩,
  ⟨(.generator 419 10 136), 0⟩,
  ⟨(.mul (.named .h0) (.generator 414 9 135)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 394 8 134)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.named .x_126_8)), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 4⟩,
  ⟨(.generator 428 10 137), 0⟩,
  ⟨(.mul (.generator 3 1 8) (.generator 333 9 129)), 1⟩,
  ⟨(.mul (.named .h2) (.generator 373 9 133)), 2⟩,
  ⟨(.mul (.mul (.named .h1) (.named .h1)) (.named .x_125_8)), 3⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 415 8 135)), 4⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 5⟩,
  ⟨(.generator 442 10 138), 0⟩,
  ⟨(.generator 441 10 138), 1⟩,
  ⟨(.mul (.named .h2) (.mul (.named .h6) (.named .b))), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 3 1 8) (.mul (.generator 68 6 64) (.named .h6)))), 3⟩,
  ⟨(.mul (.generator 23 6 36) (.generator 24 5 36)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 81 9 70)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 90 10 72)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 89 10 72)), 1⟩,
  ⟨(.named .x_91_11), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.named .h6))), 1⟩,
  ⟨(.generator 371 11 133), 0⟩,
  ⟨(.mul (.named .h6) (.named .M_mul_d_0)), 1⟩,
  ⟨(.named .x_123_11_2), 0⟩,
  ⟨(.named .x_123_11), 1⟩,
  ⟨(.mul (.named .h5) (.generator 189 10 102)), 2⟩,
  ⟨(.mul (.named .h0) (.mul (.named .h6) (.named .b4))), 3⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.named .x_123_9)), 4⟩,
  ⟨(.generator 411 11 135), 0⟩,
  ⟨(.generator 410 11 135), 1⟩,
  ⟨(.generator 409 11 135), 2⟩,
  ⟨(.mul (.named .h0) (.generator 389 10 134)), 3⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .x_124_8)), 4⟩,
  ⟨(.mul (.named .h6) (.generator 89 10 72)), 0⟩,
  ⟨(.mul (.named .h1) (.generator 389 10 134)), 1⟩,
  ⟨(.mul (.named .h1) (.generator 388 10 134)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.named .x_125_9_2)), 3⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .x_125_8)), 4⟩,
  ⟨(.generator 427 11 137), 0⟩,
  ⟨(.mul (.named .h1) (.generator 413 10 135)), 1⟩,
  ⟨(.mul (.named .h1) (.generator 412 10 135)), 2⟩,
  ⟨(.mul (.named .h0) (.generator 419 10 136)), 3⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 414 9 135)), 4⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 5⟩,
  ⟨(.mul (.named .h0) (.generator 428 10 137)), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 3 1 8) (.generator 333 9 129))), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.named .h2) (.generator 373 9 133))), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 3⟩,
  ⟨(.mul (.named .h5) (.generator 209 10 107)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 442 10 138)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 441 10 138)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 90 10 72)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 89 10 72)), 1⟩,
  ⟨(.named .x_109_12), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.generator 29 7 39) (.named .h6))), 1⟩,
  ⟨(.mul (.named .h5) (.named .x_91_11)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 371 11 133)), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.named .h6) (.named .M_mul_d_0))), 2⟩,
  ⟨(.generator 408 12 135), 0⟩,
  ⟨(.mul (.named .h0) (.named .x_123_11)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .h6) (.named .b4))), 2⟩,
  ⟨(.mul (.named .h1) (.named .x_123_11_2)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 410 11 135)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 409 11 135)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 389 10 134)), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_124_8)), 4⟩,
  ⟨(.generator 426 12 137), 0⟩,
  ⟨(.generator 425 12 137), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.named .h6) (.generator 89 10 72))), 2⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .x_125_9_2)), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_8)), 4⟩,
  ⟨(.mul (.generator 25 4 36) (.named .x_94_8)), 0⟩,
  ⟨(.mul (.generator 3 1 8) (.generator 336 11 130)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 427 11 137)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 419 10 136)), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 4⟩,
  ⟨(.mul (.named .h1) (.generator 427 11 137)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 428 10 137)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.generator 460 12 140), 0⟩,
  ⟨(.generator 459 12 140), 1⟩,
  ⟨(.mul (.generator 76 5 67) (.generator 95 7 73)), 2⟩,
  ⟨(.mul (.generator 3 1 8) (.generator 365 11 132)), 3⟩,
  ⟨(.mul (.named .h0) (.mul (.named .h5) (.generator 209 10 107))), 4⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 81 9 70)), 0⟩,
  ⟨(.generator 407 13 135), 0⟩,
  ⟨(.mul (.mul (.named .h1) (.named .h1)) (.generator 351 11 131)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .h6) (.named .M_mul_d_0))), 2⟩,
  ⟨(.named .x_123_13_2), 0⟩,
  ⟨(.generator 417 13 136), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.named .x_123_11)), 2⟩,
  ⟨(.mul (.generator 76 5 67) (.named .b)), 0⟩,
  ⟨(.mul (.named .e0) (.named .delta_h_6_mul_g)), 1⟩,
  ⟨(.mul (.named .h4) (.named .x_109_12)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_124_8)), 3⟩,
  ⟨(.mul (.generator 24 5 36) (.named .x_94_8)), 0⟩,
  ⟨(.mul (.generator 3 1 8) (.generator 335 12 130)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 425 12 137)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_9_2)), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_125_8)), 4⟩,
  ⟨(.mul (.named .h1) (.generator 426 12 137)), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 3 1 8) (.generator 336 11 130))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 2⟩,
  ⟨(.generator 458 13 140), 0⟩,
  ⟨(.mul (.named .g) (.named .delta_h_6_mul_g)), 1⟩,
  ⟨(.mul (.generator 3 1 8) (.generator 363 12 132)), 2⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 428 10 137)), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 4⟩,
  ⟨(.generator 475 13 141), 0⟩,
  ⟨(.generator 474 13 141), 1⟩,
  ⟨(.mul (.named .h0) (.generator 460 12 140)), 2⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 3 1 8) (.generator 365 11 132))), 3⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.named .e0) (.generator 23 6 36))), 0⟩,
  ⟨(.mul (.named .h0) (.generator 407 13 135)), 0⟩,
  ⟨(.mul (.generator 23 6 36) (.generator 181 8 101)), 0⟩,
  ⟨(.mul (.named .h0) (.named .x_123_13_2)), 1⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .x_123_11)), 2⟩,
  ⟨(.generator 440 14 138), 0⟩,
  ⟨(.generator 439 14 138), 1⟩,
  ⟨(.mul (.generator 23 6 36) (.named .x_94_8)), 2⟩,
  ⟨(.mul (.named .h1) (.named .x_123_13_2)), 3⟩,
  ⟨(.mul (.named .h1) (.generator 417 13 136)), 4⟩,
  ⟨(.generator 449 14 139), 0⟩,
  ⟨(.mul (.named .h1) (.mul (.named .h4) (.named .x_109_12))), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 425 12 137)), 2⟩,
  ⟨(.generator 457 14 140), 0⟩,
  ⟨(.mul (.generator 68 6 64) (.generator 107 8 76)), 1⟩,
  ⟨(.mul (.named .h1) (.mul (.generator 3 1 8) (.generator 335 12 130))), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 3⟩,
  ⟨(.mul (.named .h0) (.mul (.named .g) (.named .delta_h_6_mul_g))), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 3 1 8) (.generator 363 12 132))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.generator 482 14 142), 0⟩,
  ⟨(.mul (.named .h6) (.generator 113 13 78)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 475 13 141)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 460 12 140)), 3⟩,
  ⟨(.named .x_122_15_2), 0⟩,
  ⟨(.generator 423 15 137), 1⟩,
  ⟨(.generator 438 15 138), 0⟩,
  ⟨(.mul (.named .h4) (.generator 279 14 122)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.named .x_123_13_2)), 2⟩,
  ⟨(.generator 448 15 139), 0⟩,
  ⟨(.mul (.mul (.generator 3 1 8) (.generator 3 1 8)) (.generator 287 13 123)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 440 14 138)), 2⟩,
  ⟨(.mul (.named .h0) (.generator 439 14 138)), 3⟩,
  ⟨(.generator 456 15 140), 0⟩,
  ⟨(.mul (.generator 67 7 64) (.generator 107 8 76)), 1⟩,
  ⟨(.mul (.named .h1) (.generator 439 14 138)), 2⟩,
  ⟨(.mul (.named .h0) (.generator 449 14 139)), 3⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 425 12 137)), 4⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 68 6 64) (.generator 107 8 76))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 1⟩,
  ⟨(.generator 481 15 142), 0⟩,
  ⟨(.mul (.named .h6) (.generator 112 14 78)), 1⟩,
  ⟨(.mul (.named .h2) (.generator 439 14 138)), 2⟩,
  ⟨(.mul (.named .h1) (.generator 457 14 140)), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 4⟩,
  ⟨(.generator 495 15 143), 0⟩,
  ⟨(.mul (.named .g) (.generator 262 11 119)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 482 14 142)), 2⟩,
  ⟨(.mul (.named .h0) (.mul (.named .h6) (.generator 113 13 78))), 3⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 475 13 141)), 4⟩,
  ⟨(.generator 162 16 96), 0⟩,
  ⟨(.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.named .g)), 1⟩,
  ⟨(.named .x_122_16), 0⟩,
  ⟨(.mul (.generator 23 6 36) (.generator 189 10 102)), 1⟩,
  ⟨(.mul (.named .h0) (.named .x_122_15_2)), 2⟩,
  ⟨(.mul (.named .h1) (.named .x_122_15_2)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 438 15 138)), 1⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .x_123_13_2)), 2⟩,
  ⟨(.mul (.named .e0) (.generator 261 12 119)), 0⟩,
  ⟨(.mul (.named .h1) (.generator 438 15 138)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 448 15 139)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 440 14 138)), 3⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 439 14 138)), 4⟩,
  ⟨(.generator 473 16 141), 0⟩,
  ⟨(.mul (.named .h1) (.generator 448 15 139)), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 67 7 64) (.generator 107 8 76))), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 449 14 139)), 3⟩,
  ⟨(.mul (.mul (.named .h1) (.named .h1)) (.generator 439 14 138)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 68 6 64) (.generator 107 8 76))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 2⟩,
  ⟨(.generator 494 16 143), 0⟩,
  ⟨(.mul (.named .g) (.generator 261 12 119)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 481 15 142)), 2⟩,
  ⟨(.mul (.named .h0) (.mul (.named .h6) (.generator 112 14 78))), 3⟩,
  ⟨(.mul (.named .h0) (.mul (.named .h2) (.generator 439 14 138))), 4⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 5⟩,
  ⟨(.mul (.named .h0) (.generator 495 15 143)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 482 14 142)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .h6) (.generator 113 13 78))), 2⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 475 13 141)), 3⟩,
  ⟨(.named .x_121_17), 0⟩,
  ⟨(.mul (.generator 23 6 36) (.named .x_91_11)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 422 16 137)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .h4) (.generator 267 14 120))), 3⟩,
  ⟨(.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.generator 76 5 67)), 0⟩,
  ⟨(.mul (.named .h0) (.named .x_122_16)), 1⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 280 13 122)), 0⟩,
  ⟨(.mul (.generator 3 1 8) (.generator 359 16 132)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 438 15 138)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .x_123_13_2)), 3⟩,
  ⟨(.generator 472 17 141), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 448 15 139)), 1⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 440 14 138)), 2⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 439 14 138)), 3⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 67 7 64) (.generator 107 8 76))), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 449 14 139)), 1⟩,
  ⟨(.generator 493 17 143), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 294 13 125)), 1⟩,
  ⟨(.mul (.mul (.named .h1) (.named .h1)) (.generator 448 15 139)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.named .h6))), 3⟩,
  ⟨(.mul (.named .g) (.generator 268 13 120)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 481 15 142)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .h6) (.generator 112 14 78))), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .h2) (.generator 439 14 138))), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 4⟩,
  ⟨(.mul (.named .h2) (.generator 473 16 141)), 0⟩,
  ⟨(.mul (.named .h1) (.generator 494 16 143)), 1⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 482 14 142)), 2⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 279 14 122)), 0⟩,
  ⟨(.mul (.named .h1) (.named .x_121_17)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.named .x_122_16)), 2⟩,
  ⟨(.mul (.named .h0) (.generator 472 17 141)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 440 14 138)), 1⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 209 10 107)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 449 14 139)), 1⟩,
  ⟨(.generator 501 18 144), 0⟩,
  ⟨(.generator 500 18 144), 1⟩,
  ⟨(.mul (.named .g) (.generator 267 14 120)), 2⟩,
  ⟨(.mul (.named .e0) (.generator 286 14 123)), 3⟩,
  ⟨(.mul (.mul (.named .g) (.named .g)) (.generator 164 10 97)), 0⟩,
  ⟨(.mul (.named .h1) (.generator 493 17 143)), 1⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 481 15 142)), 2⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.mul (.named .h6) (.generator 112 14 78))), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 4⟩,
  ⟨(.generator 519 18 146), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.named .e0) (.generator 209 10 107))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 482 14 142)), 2⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.named .e0) (.named .x_91_11))), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .x_122_16)), 1⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 293 15 125)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 440 14 138)), 1⟩,
  ⟨(.mul (.named .g) (.generator 266 15 120)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.named .g) (.named .x_91_11))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 449 14 139)), 2⟩,
  ⟨(.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.generator 95 7 73)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 500 18 144)), 1⟩,
  ⟨(.mul (.named .e0) (.generator 293 15 125)), 0⟩,
  ⟨(.mul (.named .h1) (.generator 501 18 144)), 1⟩,
  ⟨(.mul (.named .h1) (.generator 500 18 144)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 481 15 142)), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 4⟩,
  ⟨(.mul (.named .e0) (.mul (.named .g) (.named .x_91_11))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 482 14 142)), 1⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 212 12 108)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 440 14 138)), 1⟩,
  ⟨(.generator 510 20 145), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.mul (.named .g) (.named .x_91_11)))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 449 14 139)), 2⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 318 16 128)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 500 18 144)), 1⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.named .e0) (.generator 212 12 108))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 481 15 142)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.mul (.named .h0) (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 212 12 108))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 440 14 138)), 1⟩,
  ⟨(.generator 518 21 146), 0⟩,
  ⟨(.mul (.named .e0) (.generator 292 17 125)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 449 14 139)), 2⟩,
  ⟨(.generator 530 21 147), 0⟩,
  ⟨(.mul (.named .h1) (.generator 510 20 145)), 1⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 2⟩,
  ⟨(.generator 537 21 148), 0⟩,
  ⟨(.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.generator 105 9 76)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 481 15 142)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 3⟩,
  ⟨(.generator 550 21 149), 0⟩,
  ⟨(.mul (.named .g) (.generator 292 17 125)), 1⟩,
  ⟨(.generator 517 22 146), 0⟩,
  ⟨(.mul (.mul (.named .g) (.named .g)) (.generator 168 14 98)), 1⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 316 18 128)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 440 14 138)), 3⟩,
  ⟨(.mul (.generator 17 7 30) (.generator 255 15 117)), 0⟩,
  ⟨(.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.generator 101 10 75)), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.named .e0) (.generator 292 17 125))), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 449 14 139)), 3⟩,
  ⟨(.mul (.named .h0) (.generator 530 21 147)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 1⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 347 18 131)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 346 18 131)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.generator 17 7 30) (.named .x_91_11))), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.named .g) (.generator 292 17 125))), 1⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 327 19 129)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.named .g) (.mul (.generator 23 6 36) (.named .b4)))), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.generator 316 18 128))), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 440 14 138)), 3⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .e0) (.generator 292 17 125))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 449 14 139)), 1⟩,
  ⟨(.generator 549 23 149), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 1⟩,
  ⟨(.mul (.named .e0) (.mul (.named .g) (.mul (.generator 23 6 36) (.named .b4)))), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.generator 16 8 30) (.named .x_91_11))), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.generator 346 18 131))), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 3⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.mul (.generator 17 7 30) (.named .x_91_11)))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.named .g) (.generator 292 17 125))), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 8 4 18) (.generator 316 18 128))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 440 14 138)), 1⟩,
  ⟨(.mul (.named .e0) (.mul (.named .g) (.generator 194 16 104))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.named .g)) (.generator 52 8 54)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.generator 16 8 30) (.generator 187 12 102))), 1⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.named .e0) (.mul (.generator 23 6 36) (.generator 101 10 75)))), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 3⟩,
  ⟨(.mul (.named .h1) (.generator 549 23 149)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 8 4 18) (.generator 346 18 131))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.generator 573 24 152), 0⟩,
  ⟨(.mul (.mul (.named .g) (.named .g)) (.generator 194 16 104)), 1⟩,
  ⟨(.mul (.generator 17 7 30) (.generator 260 18 119)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.named .e0) (.generator 219 17 110))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 440 14 138)), 2⟩,
  ⟨(.generator 559 25 150), 0⟩,
  ⟨(.generator 558 25 150), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.named .g)) (.named .delta_h_1_mul_g)), 2⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.mul (.named .e0) (.mul (.named .g) (.named .b4)))), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 0⟩,
  ⟨(.mul (.generator 17 7 30) (.generator 278 18 122)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.named .g) (.generator 219 17 110))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.generator 580 25 153), 0⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.mul (.mul (.named .g) (.named .g)) (.named .b4))), 1⟩,
  ⟨(.mul (.named .h0) (.generator 573 24 152)), 2⟩,
  ⟨(.generator 557 26 150), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.named .g)) (.generator 23 6 36))), 1⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.named .e0) (.generator 101 10 75))), 2⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 17 7 30) (.generator 260 18 119))), 3⟩,
  ⟨(.mul (.named .h0) (.generator 558 25 150)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 380 22 134)), 0⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 248 18 116)), 1⟩,
  ⟨(.mul (.named .h1) (.generator 558 25 150)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 3⟩,
  ⟨(.mul (.named .e0) (.mul (.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.named .g)) (.generator 23 6 36))), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 404 22 135)), 1⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.named .g) (.generator 101 10 75))), 2⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 17 7 30) (.generator 278 18 122))), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 4⟩,
  ⟨(.mul (.named .h0) (.generator 557 26 150)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 17 7 30) (.generator 260 18 119))), 1⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 167 15 98)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 558 25 150)), 1⟩,
  ⟨(.mul (.generator 64 10 63) (.generator 147 17 90)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.named .e0) (.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.generator 32 7 42)))), 1⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 173 15 99)), 2⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.generator 380 22 134))), 3⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 4⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.generator 404 22 135))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 17 7 30) (.generator 278 18 122))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.mul (.named .e0) (.generator 167 15 98))), 0⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 166 16 98)), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.mul (.generator 17 7 30) (.generator 260 18 119))), 1⟩,
  ⟨(.mul (.generator 64 10 63) (.generator 146 18 90)), 0⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.mul (.named .e0) (.mul (.mul (.mul (.named .g) (.named .g)) (.named .g)) (.named .g)))), 1⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.generator 17 7 30) (.named .b4))), 2⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 558 25 150)), 3⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 64 10 63) (.generator 147 17 90))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 8 4 18) (.generator 380 22 134))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 2⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 180 16 101)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.named .e0) (.mul (.named .g) (.named .delta_h_1_mul_g)))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 118 13 81)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.generator 17 7 30) (.generator 260 18 119))), 2⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 64 10 63) (.generator 146 18 90))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 558 25 150)), 1⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 259 21 119)), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 64 10 63) (.generator 147 17 90))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 2⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.mul (.named .g) (.named .g)) (.named .delta_h_1_mul_g))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 127 13 84)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.mul (.mul (.named .h1) (.named .h1)) (.mul (.generator 64 10 63) (.generator 137 18 87))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.generator 17 7 30) (.generator 260 18 119))), 1⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 258 22 119)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 558 25 150)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.mul (.named .g) (.named .g)) (.generator 23 6 36))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 72 10 66)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.generator 623 30 158), 0⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 277 22 122)), 1⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.mul (.generator 17 7 30) (.generator 17 7 30)) (.generator 113 13 78))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.named .g) (.generator 32 7 42))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 558 25 150)), 2⟩,
  ⟨(.mul (.generator 5 5 14) (.generator 491 26 143)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 1⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.mul (.generator 17 7 30) (.generator 149 16 92))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.mul (.generator 17 7 30) (.generator 147 17 90))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.named .g) (.named .g))), 1⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.mul (.generator 16 8 30) (.generator 149 16 92))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 1⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.mul (.generator 16 8 30) (.generator 154 16 93))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.named .e0) (.mul (.named .g) (.named .g)))), 1⟩,
  ⟨(.mul (.named .h1) (.mul (.generator 5 5 14) (.generator 491 26 143))), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 3⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 453 29 140)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 138 17 87)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 46 9 51)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 490 29 143)), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 623 30 158)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 137 18 87)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 45 10 51)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 489 30 143)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 146 18 90)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 23 6 36)), 1⟩,
  ⟨(.mul (.generator 42 9 48) (.generator 224 26 111)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 20 7 33)), 1⟩,
  ⟨(.mul (.generator 17 7 30) (.generator 343 28 131)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 1⟩,
  ⟨(.mul (.mul (.generator 17 7 30) (.generator 17 7 30)) (.generator 185 21 102)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 22 7 36)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 488 32 143)), 0⟩,
  ⟨(.mul (.named .h1) (.mul (.generator 42 9 48) (.generator 224 26 111))), 1⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.generator 17 7 30) (.generator 238 25 114))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.generator 16 8 30) (.generator 244 24 116))), 0⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 298 29 126)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 88 17 72)), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.mul (.generator 17 7 30) (.generator 238 25 114)))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 500 18 144)), 1⟩,
  ⟨(.generator 687 37 164), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 225 25 111)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 100 17 75)), 1⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 297 30 126)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.generator 16 8 30) (.mul (.generator 17 7 30) (.generator 17 7 30)))), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 298 29 126))), 0⟩,
  ⟨(.generator 686 38 164), 0⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 224 26 111)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.generator 17 7 30) (.generator 40 11 45))), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.mul (.named .h1) (.generator 687 37 164)), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 225 25 111))), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 297 30 126))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 298 29 126))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 56 15 57)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 686 38 164)), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 224 26 111))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.generator 17 7 30) (.generator 403 33 135)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 55 16 57)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 686 38 164)), 0⟩,
  ⟨(.generator 722 40 167), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.generator 17 7 30) (.generator 433 33 138)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 31 12 42)), 1⟩,
  ⟨(.mul (.generator 16 8 30) (.generator 403 33 135)), 0⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 223 29 111)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 685 40 164)), 2⟩,
  ⟨(.mul (.named .h1) (.generator 685 40 164)), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 17 7 30) (.generator 403 33 135))), 1⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 556 37 150)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 161 25 96)), 1⟩,
  ⟨(.mul (.named .h0) (.generator 722 40 167)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 3⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 17 7 30) (.generator 433 33 138))), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 16 8 30) (.generator 403 33 135))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 685 40 164)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 17 7 30) (.generator 403 33 135))), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 555 38 150)), 0⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.mul (.generator 16 8 30) (.mul (.generator 17 7 30) (.generator 50 15 54)))), 1⟩,
  ⟨(.mul (.mul (.named .h1) (.named .h1)) (.generator 685 40 164)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 3⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.generator 556 37 150))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 722 40 167)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 16 8 30) (.generator 403 33 135))), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 685 40 164)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 111 23 78)), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.mul (.generator 17 7 30) (.generator 403 33 135))), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.generator 555 38 150))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 8 4 18) (.generator 556 37 150))), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 722 40 167)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 2⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 110 24 78)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 685 40 164)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.generator 17 7 30) (.generator 403 33 135))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 8 4 18) (.generator 555 38 150))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 116 24 81)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 685 40 164)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.generator 17 7 30) (.generator 403 33 135))), 0⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 401 37 135)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 685 40 164)), 0⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.mul (.generator 17 7 30) (.generator 200 31 105))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.generator 805 46 174), 0⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.mul (.generator 16 8 30) (.mul (.generator 17 7 30) (.generator 111 23 78)))), 1⟩,
  ⟨(.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 253 35 117)), 0⟩,
  ⟨(.mul (.generator 5 5 14) (.generator 635 42 159)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 183 31 102)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 8 4 18)) (.generator 182 32 102)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 1⟩,
  ⟨(.mul (.named .h1) (.mul (.generator 5 5 14) (.generator 635 42 159))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 607 45 156)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 634 45 159)), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 805 46 174)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.mul (.generator 17 7 30) (.generator 326 39 129))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 470 43 141)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.mul (.generator 8 4 18) (.generator 8 4 18)) (.generator 469 44 141)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 686 38 164)), 0⟩,
  ⟨(.generator 886 53 180), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.generator 17 7 30) (.generator 554 47 150)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.generator 16 8 30) (.generator 554 47 150)), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 17 7 30) (.generator 554 47 150))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 701 51 165)), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 661 52 162)), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 16 8 30) (.generator 554 47 150))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 17 7 30) (.generator 554 47 150))), 0⟩,
  ⟨(.mul (.generator 8 4 18) (.generator 700 52 165)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.generator 701 51 165))), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.generator 661 52 162))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 16 8 30) (.generator 554 47 150))), 0⟩,
  ⟨(.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.mul (.generator 17 7 30) (.generator 554 47 150))), 0⟩,
  ⟨(.mul (.named .h0) (.mul (.generator 8 4 18) (.generator 700 52 165))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 8 4 18) (.generator 701 51 165))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 8 4 18) (.generator 661 52 162))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.generator 17 7 30) (.generator 554 47 150))), 0⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.mul (.generator 8 4 18) (.generator 700 52 165))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.mul (.generator 17 7 30) (.generator 554 47 150))), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.generator 951 60 186), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.named .h0) (.generator 951 60 186)), 0⟩,
  ⟨(.mul (.named .h1) (.generator 951 60 186)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 1⟩,
  ⟨(.mul (.mul (.named .h0) (.named .h0)) (.generator 951 60 186)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩,
  ⟨(.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.named .h0)) (.generator 324 1 128)), 0⟩
]

/- Normalize both archived source monomials and displayed expressions only
in the actual sphere E₂. The fixed multiplication's HEq laws supply the private
sigma monoid; no associativity of ProgramData is assumed. -/
section ArchiveBasisValueConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open CategoryTheory KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.AdamsSynthetic.Standard

private abbrev ActualTotal := Σ p : Bidegree, model.classical.sphere.Page 2 p
private noncomputable def totalProduct (x y : ActualTotal) : ActualTotal :=
  ⟨x.1+y.1, model.sphereAlgebra.product x.1 y.1 x.2 y.2⟩
private noncomputable def totalUnit : ActualTotal := ⟨(0,0), model.sphereAlgebra.unit⟩
private theorem totalProduct_assoc (x y z : ActualTotal) :
    totalProduct (totalProduct x y) z = totalProduct x (totalProduct y z) := by
  apply Sigma.ext (add_assoc x.1 y.1 z.1)
  exact model.sphereAlgebra.assoc x.1 y.1 z.1 x.2 y.2 z.2
private theorem totalUnit_left (x : ActualTotal) : totalProduct totalUnit x = x := by
  apply Sigma.ext (zero_add x.1)
  exact model.sphereAlgebra.unit_left x.1 x.2
private theorem totalUnit_right (x : ActualTotal) : totalProduct x totalUnit = x := by
  apply Sigma.ext (add_zero x.1)
  exact model.sphereAlgebra.unit_right x.1 x.2
private noncomputable instance actualTotalMonoid : Monoid ActualTotal where
  mul := totalProduct
  one := totalUnit
  mul_assoc := totalProduct_assoc
  one_mul := totalUnit_left
  mul_one := totalUnit_right

private noncomputable def totalClass {s t : ℕ} (x : Page .sphere s t) : ActualTotal :=
  ⟨(s,t), x⟩
private theorem totalClass_product {s t s' t' : ℕ}
    (x : Page .sphere s t) (y : Page .sphere s' t') :
    totalClass (Standard.product (r := ((s+s' : ℕ),(t+t' : ℕ))) x y
      (by simp only [Prod.mk_add_mk,Nat.cast_add])) = totalClass x * totalClass y := by
  rfl

private noncomputable def totalGenerator (id : ℕ) : ActualTotal :=
  if hi : id < Standard.archive.generators.count then
    let d := Standard.archive.generators.degree ⟨id,hi⟩
    totalClass (generatorImage id d.1 d.2)
  else totalClass (0 : Page .sphere 0 0)

private def monomialWord : ∀ {s t : ℕ},
    SourceMonomial Standard.archive.generators s t → List ℕ
  | _, _, .one => []
  | _, _, .generator i => [i.val]
  | _, _, .mul a b => monomialWord a ++ monomialWord b

private noncomputable def actualMonomial {s t : ℕ}
    (m : SourceMonomial Standard.archive.generators s t) (ht : t ≤ 261) : ActualTotal :=
  totalClass (Standard.comparison s t ht (m.value Standard.sourceData Standard.sourceGenerator))

private theorem actualMonomial_product {s t s' t' : ℕ}
    (a : SourceMonomial Standard.archive.generators s t)
    (b : SourceMonomial Standard.archive.generators s' t')
    (ht : t+t' ≤ 261) (ha : t ≤ 261) (hb : t' ≤ 261) :
    actualMonomial (.mul a b) ht = actualMonomial a ha * actualMonomial b hb := by
  refine Sigma.ext ?_ ?_
  · rfl
  exact heq_of_eq (Standard.comparison_product s t s' t' ht
    (a.value Standard.sourceData Standard.sourceGenerator)
    (b.value Standard.sourceData Standard.sourceGenerator))

private theorem actualMonomial_normalize {s t : ℕ}
    (m : SourceMonomial Standard.archive.generators s t) :
    ∀ ht : t ≤ 261, actualMonomial m ht = (monomialWord m |>.map totalGenerator).prod := by
  induction m with
  | one =>
    intro ht
    exact congrArg (fun x : Page .sphere 0 0 => totalClass x) Standard.comparison_unit
  | generator i =>
    intro ht
    simp only [monomialWord, List.map_singleton, List.prod_singleton]
    dsimp only [actualMonomial, SourceMonomial.value, totalGenerator]
    rw [dif_pos i.isLt]
    dsimp only [generatorImage]
    rw [dif_pos ht, dif_pos i.isLt, dif_pos rfl]
    rfl
  | @mul s t s' t' a b iha ihb =>
    intro ht
    have ha : t ≤ 261 := by omega
    have hb : t' ≤ 261 := by omega
    rw [actualMonomial_product a b ht ha hb, iha ha, ihb hb]
    simp only [monomialWord, List.map_append, List.prod_append]

private noncomputable def expressionWord : Expression → List ℕ
  | .one => []
  | .named a => [(Standard.archive.atomIndex a).val]
  | .generator id _ _ => [id]
  | .mul a b => expressionWord a ++ expressionWord b

private def admissible : Expression → Prop
  | .one => True
  | .named _ => True
  | .generator id s t => if hi : id < Standard.archive.generators.count then
      Standard.archive.generators.degree ⟨id,hi⟩ = (s,t) else False
  | .mul a b => admissible a ∧ admissible b

private noncomputable def admissibleDecidable : (e : Expression) → Decidable (admissible e)
  | .one => isTrue trivial
  | .named _ => isTrue trivial
  | .generator id s t => by
    dsimp only [admissible]
    split_ifs <;> infer_instance
  | .mul a b => by
    letI := admissibleDecidable a
    letI := admissibleDecidable b
    dsimp only [admissible]
    infer_instance
private noncomputable instance (e : Expression) : Decidable (admissible e) := admissibleDecidable e

private theorem named_total (a : Atom) :
    totalClass (Standard.atom a) = totalGenerator (Standard.archive.atomIndex a).val := by
  cases a <;> rfl

private theorem expression_normalize (e : Expression) (hv : admissible e) :
    totalClass e.value = (expressionWord e |>.map totalGenerator).prod := by
  induction e with
  | one => rfl
  | named a =>
    dsimp only [Expression.value]
    simpa only [expressionWord, List.map_singleton, List.prod_singleton] using named_total a
  | generator id s t =>
    dsimp only [admissible] at hv
    split_ifs at hv with hi
    · have hs := congrArg Prod.fst hv
      have ht := congrArg Prod.snd hv
      dsimp only at hs ht
      subst s
      subst t
      simp only [expressionWord, List.map_singleton, List.prod_singleton]
      dsimp only [totalGenerator]
      rw [dif_pos hi]
      rfl
  | mul a b iha ihb =>
    rw [show totalClass (Expression.mul a b).value = totalClass a.value * totalClass b.value from rfl]
    rw [iha hv.1, ihb hv.2]
    simp only [expressionWord, List.map_append, List.prod_append]


private noncomputable def checkedWord (s t i : ℕ) : Option (List ℕ) :=
  if hi : i < Standard.archive.basisCount s t then
    some (monomialWord (Standard.archive.basisMonomial s t ⟨i,hi⟩))
  else none

private def rowValid (v : BasisValue) : Prop :=
  admissible v.expression ∧ v.expression.degree.2 ≤ 261 ∧
    checkedWord v.expression.degree.1 v.expression.degree.2 v.index =
      some (expressionWord v.expression)
private noncomputable instance (v : BasisValue) : Decidable (rowValid v) := by
  dsimp only [rowValid]
  infer_instance

private theorem row_binding (v : BasisValue) (hrow : rowValid v) :
    basis .sphere v.expression.degree.1 v.expression.degree.2 v.index = v.expression.value := by
  have hword := hrow.2.2
  dsimp only [checkedWord] at hword
  split_ifs at hword with hi
  have hw := Option.some.inj hword
  let m := Standard.archive.basisMonomial v.expression.degree.1 v.expression.degree.2 ⟨v.index,hi⟩
  have hm := actualMonomial_normalize m hrow.2.1
  have he := expression_normalize v.expression hrow.1
  change monomialWord m = expressionWord v.expression at hw
  rw [hw] at hm
  have htotal := hm.trans he.symm
  dsimp only [actualMonomial, totalClass] at htotal
  have hactual := sigma_mk_injective htotal
  have hb := Standard.coordinates_basis v.expression.degree.1 v.expression.degree.2 hrow.2.1
    (⟨v.index,hi⟩ : Fin (Standard.archive.basisCount v.expression.degree.1 v.expression.degree.2))
  dsimp only [basis, sphereBasis]
  rw [dif_pos hrow.2.1, dif_pos hi]
  exact hb.trans hactual


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
private theorem basisValues_checked :
    basisValues.all (fun v => decide (rowValid v)) = true := by
  decide

private theorem archiveBasisValueBinding (v : BasisValue) (hv : v ∈ basisValues) :
    basis .sphere v.expression.degree.1 v.expression.degree.2 v.index = v.expression.value := by
  apply row_binding v
  exact of_decide_eq_true ((List.all_eq_true.mp basisValues_checked) v hv)

end ArchiveBasisValueConstruction

/-- The original finite CSV monomials are the corresponding coordinate vectors
in the same archive and actual E₂ comparison. This is a source binding obligation. -/
public theorem basis_value (v : BasisValue) (hv : v ∈ basisValues) :
    basis .sphere v.expression.degree.1 v.expression.degree.2 v.index =
      v.expression.value := by
  exact archiveBasisValueBinding v hv

public theorem basis_P : basis .sphere 11 133 1 = Standard.P := by
  have h := basis_value ⟨.mul (.named .h6) (.named .M_mul_d_0),1⟩ (by decide)
  simpa only [Expression.value, Expression.degree, Standard.P, Standard.atom_h6] using h

public theorem basis_Q : basis .sphere 12 134 0 = Standard.Q := by
  have h := basis_value ⟨.mul (.named .h5) (.named .x_91_11),0⟩ (by decide)
  simpa only [Expression.value, Expression.degree, Standard.Q, Standard.atom_h5] using h

public theorem basis_T : basis .sphere 14 139 1 = Standard.T := by
  have h := basis_value ⟨.mul (.named .h1) (.mul (.named .h4) (.named .x_109_12)),1⟩ (by decide)
  simpa only [Expression.value, Expression.degree, Standard.T, Standard.atom_h1,
    Standard.atom_h4] using h

/-- The first archived sphere relation, `0,1,1,1`, transported to the
same actual E₂. Original LinProgram/Model/Classes/Proofs.lean:92–105. -/
public theorem h0_h1_zero :
    Standard.product (r := (2,3)) Standard.h0 Standard.h1 = 0 := by
  exact Internal.actual_page_zero 2 3 (by decide) (by decide) _

public theorem basis_correction : basis .sphere 13 137 1 = Standard.correction := by
  have h := basis_value ⟨.mul (.named .e0) (.named .delta_h_6_mul_g),1⟩ (by decide)
  exact h

public theorem basis_h4_x109 : basis .sphere 13 137 2 =
    Standard.product (r := (13,137)) Standard.h4 (Standard.atom .x_109_12) := by
  have h := basis_value ⟨.mul (.named .h4) (.named .x_109_12),2⟩ (by decide)
  simpa only [Expression.value, Expression.degree, Standard.atom_h4] using h

public theorem basis_U : basis .sphere 10 134 4 = Standard.U := by
  have h := basis_value ⟨.mul (.mul (.named .h0) (.named .h0)) (.named .x_124_8),4⟩ (by decide)
  simpa only [Expression.value, Expression.degree, Standard.U, Standard.h0Square,
    Standard.atom_h0] using h

/- Source commutativity is the multiplication of the same native CSV quotient.
Transport along the original bounded comparison keeps both degree casts. -/
section NativeSourceCommutativity
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
private theorem comparison_heq {s t u v : ℕ} (hs : s = u) (ht : t = v)
    (ha : t ≤ 261) (hb : v ≤ 261)
    (x : Standard.sourceData.component s t) (y : Standard.sourceData.component u v)
    (hxy : HEq x y) :
    HEq (Standard.comparison s t ha x) (Standard.comparison u v hb y) := by
  subst u
  subst v
  cases hxy
  rfl

private theorem transport_heq {X Y : ModuleCat.{0} ℤ} (h : X = Y) (x : X) :
    HEq ((eqToHom h) x) x := by
  cases h
  rfl

private theorem product_transport_heq {p q r : ℤ × ℤ}
    (x : model.classical.sphere.Page 2 p) (y : model.classical.sphere.Page 2 q)
    (h : p + q = r) :
    HEq (Standard.product (r := r) x y h) (model.sphereAlgebra.product p q x y) := by
  exact transport_heq (congrArg (model.classical.sphere.Page 2) h) _

private theorem native_source_product_comm (s t s' t' : ℕ)
    (a : Standard.sourceData.component s t) (b : Standard.sourceData.component s' t') :
    HEq (Standard.sourceData.product s t s' t' a b)
      (Standard.sourceData.product s' t' s t b a) := by
  apply (Subtype.heq_iff_coe_eq (by
    intro z
    rw [Nat.add_comm s s', Nat.add_comm t t'])).2
  exact mul_comm _ _

private theorem actual_product_comm (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : model.classical.sphere.Page 2 (s,t))
    (y : model.classical.sphere.Page 2 (s',t')) :
    HEq (model.sphereAlgebra.product (s,t) (s',t') x y)
      (model.sphereAlgebra.product (s',t') (s,t) y x) := by
  let a := (Standard.comparison s t (by omega)).symm x
  let b := (Standard.comparison s' t' (by omega)).symm y
  have ha : Standard.comparison s t (by omega) a = x :=
    (Standard.comparison s t (by omega)).apply_symm_apply x
  have hb : Standard.comparison s' t' (by omega) b = y :=
    (Standard.comparison s' t' (by omega)).apply_symm_apply y
  have hsource := native_source_product_comm s t s' t' a b
  have hactual := comparison_heq (Nat.add_comm s s') (Nat.add_comm t t')
    ht (by omega) _ _ hsource
  rw [Standard.comparison_product, Standard.comparison_product, ha, hb] at hactual
  exact hactual

end NativeSourceCommutativity

/-- The original commutative source algebra, transported by the same bounded
comparison. This retains the total-degree bound of comparison_product. -/
public theorem product_comm (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : model.classical.sphere.Page 2 (s,t))
    (y : model.classical.sphere.Page 2 (s',t')) :
    Standard.product (r := ((s+s' : ℕ),(t+t' : ℕ))) x y
        (by simp only [Prod.mk_add_mk,Nat.cast_add]) =
      Standard.product (r := ((s+s' : ℕ),(t+t' : ℕ))) y x
        (by simp only [Prod.mk_add_mk,Nat.cast_add]; ext <;> omega) := by
  exact eq_of_heq ((product_transport_heq x y _).trans
    ((actual_product_comm s t s' t' ht x y).trans (product_transport_heq y x _).symm))

end
end KIP126.Computation.Table
