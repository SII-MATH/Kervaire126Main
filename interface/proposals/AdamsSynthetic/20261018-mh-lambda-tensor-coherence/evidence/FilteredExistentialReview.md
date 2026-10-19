# Weaker filtered existential MH route

Baseline HEAD: `b5ad178bab6c9a295baf66f9b1042797f449aac5`.
Task: study the actual `FiniteMahowaldAtLevelStatement`, allowing simultaneous reselection of a,b,c while retaining its five input detections; do not replace it with the stronger theorem for every preselected a,b. Research-only delivery. No production writes in this follow-up.

## Actual target and premises used

Read the current `FiniteLevelStatement.lean` in full, together with `FiniteLevelInputs.lean`, `ActualNoCrossing.lean`, `SphereMayCorrection.lean`, `SphereMayActual.lean`, `MayCorrection.lean`, `NuCofiberMayCorrection.lean` and `CommonShiftEdge.lean`.

The actual statement has one normalized compatible T, A=n₁+k+i−j, B=m₁+j+1, N=A+B, with j<n₁. Its conclusion is existential in a,b,c. The source and target labels are intrinsic actual finite-quotient labels, not arbitrary page-coordinate identifications. The inputs include the four infinity labels, h/d/g actual extension equations, classical cycles, the prescribed d_r differential and permanent differential target, and actual essential no-crossing on h or d. In particular the theorem does not prescribe the actual b in advance.

`FiniteLevelInputs` now proves synchronization of a and b using exactly those actual no-crossing/extension/infinity inputs and finite top-window vanishing. This gives all five input detections and δa=g_B b. There is no reason to insist that those choices remain fixed if higher corrections preserve all five labels.

The worker's earlier generic arbitrary-a,b finite May statement is therefore a sufficient route, not a necessary theorem that the MH task must prove.

## Verified progress on the weaker route

1. The first-image lift and a lambda factorization of the second image exist on the actual fixed quotients without any sphere restriction on Y. See `FiniteMay.lean` and its earlier delivery.
2. `MayCorrection.finite_cycle_image_correction` is already general in Y. It can produce an elementwise correction c_d with the needed d(y) label and zero rho image. The restriction Y=sphere enters the older `SphereMayCorrection` when promoting this into global extensions d_Q and R_Q out of Q_B, not in the finite-cycle elementwise correction itself.
3. The coordinator has now proved `finite_lambda_filtered_surjective`: in the actual quotient map λ^A:F_-A Q_(N-A)(νY)→Q_N(νY), every sufficiently high-filtered target element lifts to a source element in the same filtration. This uses existing E∞ surjectivity and finite target separation; no new upstream condition. It is useful for changing b at higher filtration.
4. New, checked research lemma `finite_detected_whole_defect` in `FilteredDefectCheck.lean`: given an actual identity

   ```
   incl K - incl J = d h - R
   ```

   and a finite alpha detecting `pageMap incl x`, the actual element `alpha K - alpha J` detects `pageMap (d h - R) x`. The proof uses the single map K−J, `detects_map`, and functorial composition. It does not assume that familyPageMap is additive in its actual-map argument. Thus the whole defect can be transferred to the finite representative despite nonpermanence of x.
5. New, checked pure additive lemma `fixed_source_signed_repair_iff` gives the exact residual range problem when keeping the synchronized a fixed. For actual additive maps rho:C→H, f:C→D, lambda:B→D, g:B→Z and V=F^(sg+1)B, modifying b0,c0 without changing the b label, g image, or rho image is equivalent to solving

   ```
   v ∈ V,   g(v)=0,   rho(z)=0,
   f(z)+lambda(v)=-(f(c0)+lambda(b0)).
   ```

   This is an exact algebraic reformulation, not a proposed additional MH input and not a proof that its range condition follows from current MH premises. Allowing a to change can enlarge the correction space further, so this fixed-a criterion is not asserted necessary for the full existential statement.

## Exact remaining points

### A. Identifying and removing the leading defect

The whole-defect lemma identifies the alpha error with the label `pageMap(d h−R)x`. The elementwise c_d correction has label `pageMap(d h)x` after applying h, and the Toda residual supplies the zero infinity class for `pageMap R x` in the older applicable branch. To conclude that subtracting c_d leaves an error one filtration higher, one still needs a valid comparison between these image labels on this x.

Actual E∞ maps are additive in actual maps once source and target convergence are fixed; this follows from actual filtered maps and associated-graded naturality. That observation settles the special case in which x itself has an infinity representative. Here x lies on the unquotiented νY and can be nonpermanent: the assumptions only make `pageMap incl x` permanent in Q_B. The source cycle length is B−j=m₁+1, not infinity. Hence E∞ map additivity cannot simply be applied to x.

No existing actual-map E₂ additivity theorem was found. `SyntheticAdamsFamily` is given as a functor, without an Additive field, and `SyntheticTowerPresentation.map` is a selection of TowerMaps with no stated comparison between map(f+g) and stagewise sums. Its natural_e2 field alone does not make this a one-line linearity argument. Independent read-only review by mh_crossing and its crossing_audit child confirmed this exact boundary. This is a remaining proof step, not a formal counterexample or proof of impossibility.

A sufficient lower-level producer statement would be the needed pointwise stable additivity on these finite-cycle image labels, or a coherent actual three-by-three finite quotient diagram. Full tensor/quotient compatibility is a different sufficient route and has not been shown necessary.

### B. Keeping the g detection while changing b

Suppose the leading defect has been removed and E=f(c0)+lambda(b0) lies in F^(sg+1). Strict lambda surjectivity provides v in F^(sg+1) with lambda(v)=E. This preserves the y label when replacing b0 by b0−v. It does **not** by itself preserve the g image.

The map g preserves filtration, so g(v) is only known to be in F^(sg+1). The required top target filtration is s+r=sg+m, and m can exceed zero. Thus finite top-window separation cannot kill g(v) from this bound alone. The relation lambda_Z(g(v))=0 only places it in a lambda kernel, where nonzero finite labels can occur. A proof needs a relative lambda lifting result inside ker g, or a simultaneous correction of a,b,c preserving all five labels using the actual h/d no-crossing. Neither has been proved here. Ordinary lambda strict surjectivity is not silently treated as strict surjectivity on ker g.

For m=0, source-next filtration is already beyond the top target, so this particular preservation problem disappears; the leading-defect comparison remains separate.

## Why the old global extension cannot simply be generalized

For d:F_a νY→F_b Q_NνX, composing λ^B on the source gives the favorable gap N≤B+b−a. The existing general no-return lemma indeed proves

```
for every bigraded sphere representative u, u ≫ (lambdaPow B _ ≫ d) = 0.
```

This is a statement about elements of represented homotopy groups. It does not prove the actual map `lambdaPow B _ ≫ d = 0`. The sphere branch uses νY≅Smn to evaluate the map itself on a sphere; the nuCofiber branch uses its finite-cell triangle. Arbitrary νY, including the detector case, is not supplied with such a source presentation. Object homotopy separation separates homotopy classes, not arbitrary-domain maps; maps invisible on all homotopy groups can be nonzero ghost maps in spectra. No global ghost-vanishing assertion was inferred or added.

## Actual checks and dependencies

Command:

```
lake env lean local-history/proof-sessions/mh-finite-20261018/may/FilteredDefectCheck.lean
```

Passed, exit 0. Pinned toolchain, sandbox elevation only; no shared output path or full build. Log: `filtered-defect-check.log`.
Source SHA-256: `5e7e5c4a40fbc90311f6f9b88030e5e184bd79cdfea3ab5cbdb1b2872de88e79`.

The whole-defect lemma inherits `sorryAx` through registered fixed-model inputs. The pure additive repair criterion has only `[propext, Classical.choice, Quot.sound]`. No new sorry, axiom, public premise or pending responsibility was introduced. No fixed-model counterexample to the actual existential statement was found, and no abstract failure of a stronger arbitrary-b statement was used as evidence against it.
