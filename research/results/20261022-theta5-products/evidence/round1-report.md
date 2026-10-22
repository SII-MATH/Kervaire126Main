# The filtration-13 coefficient in the square of the stem-62 class

Baseline: `34fb925fd3c30304832e40e1c87938ff00908b67`, worktree
`/inspire/hdd/global_user/czxs25250150/ops/tmp/d3-x126-6-20261021`.
Research output only; production Lean, interfaces, locks and build outputs are unchanged.

## Result and evidence level

Let `F` be the classical mod-2 Adams filtration on the 2-primary stable
homotopy groups of spheres. For every `a_6 in pi_62` detected by `h_5 n`,
the argument below proves

\[
                 a_6^2\in F^{14}\pi_{124}.
\]

Consequently, if `c_13` denotes the nonzero filtration-13 class detected by
`e_0 Delta h_6 g`, the coefficient in

\[
       a_6^2\equiv\varepsilon c_{13}\pmod {F^{14}\pi_{124}}
\]

is `epsilon = 0`. This conclusion uses the explicitly listed classical Adams
computations below as inputs. It is an informal mathematical proof, supported
by bounded reproducible algebra/database checks and an independent source
audit. It is not a new Lean theorem, and the database checks do not constitute
a formal proof of the database's Adams input.

The argument does not prove `a_6^2 = 0`, does not prove membership in `F^15`,
and does not determine the square of a chosen `theta_5` or its filtration-10
coefficient. It specifically settles the possible filtration-13 contribution
from the AF-6 change of representative.

## Conventions and input ledger

Write `E_r^{s,t}` with stem `t-s`, and use decreasing multiplicative Adams
filtration. All Toda brackets in the proof are classical stable Toda brackets.
Signs do not affect any filtration estimate. Classical convergence is used
for the 2-complete sphere; finite filtration gaps are interpreted through its
associated graded filtration.

1. Choose a class `n in pi_31`, detected by `n in E_2^{5,36}`, with `2n=0`.
   This is a choice of representative, not a claim about every element of
   the detection coset. IWX's Toda table contains the defined bracket
   `<{n},2,theta_5>`, detected by `h_6 n`; it therefore explicitly supplies a
   representative with `2n=0`. Use that same representative throughout.
   Source: `more-stable-stems-tables.tex:691,1163` (Table of permanent cycles
   and Table of Toda brackets; Table 11 in the cached v2 PDF). Passing from
   the C-motivic statement to the classical one preserves the bracket and
   the zero product. The classical chart confirms the nonzero `n` detector.
2. Choose the classical `theta_4 in pi_30`, detected by `h_4^2`, such that
   `2 theta_4=0` and `theta_4^2=0`. The first is classical; the second is
   Xu's main theorem. Source: `Source/Xu/source/theta5_arxiv.tex:118,129`,
   with the proof at lines 194--213. Both zero products are needed below.
3. `pi_61=0`: Wang--Xu, *The triviality of the 61-stem in the stable homotopy
   groups of spheres*, Theorem 1.9. The local text conversion is
   `wang-xu-61stem.txt:154`; the article's printed page is 504.
4. `pi_31=F^3 pi_31`. Its classical E-infinity detectors have filtrations
   `3,5,11,12,13,14,15,16`. The first two Ext classes in stem 31, `h_5` and
   `h_0 h_5`, support nonzero `d_2` differentials. See the classical CSV and
   the `stem31` / `moss_crossing_windows` probe output.
5. `pi_62=(Z/2)^4`, with complete Adams filtrations `2,6,8,10`, detected by
   `h_5^2`, `h_5 n`, `Delta e_1+C_0`, and `R`, respectively. In particular
   `F^7 pi_62=F^8 pi_62` and all elements of this group are killed by 2.
   Source: IWX's classical chart and group computation; AimPaper/main.tex
   lines 2234--2239 records exactly this classification. This is the full
   filtered group classification, not an inference from a truncated list.
6. In stem 93, the classical E-infinity groups in filtrations 6,7,8,9 are
   zero, so `F^6 pi_93=F^10 pi_93`. The classical IWX E-infinity CSV records
   a class in AF 5 and the next class in AF 10. Independent confirmation is
   given by the nonzero outgoing differentials in the cw49 database:

   | AF | E2 basis | nonzero outgoing differential |
   | --- | --- | --- |
   | 6 | `h_0^3 h_4^2 h_6` | `d_5` |
   | 7 | `Delta h_2^2 h_6` | `d_3` |
   | 8 | `x_{93,8}`; `h_0 Delta h_2^2 h_6` | `d_3`; `d_5` |
   | 9 | `h_0^2 Delta h_2^2 h_6` | `d_5` |

   The proof only requires this finite vanishing window. The database's
   level-9000 rows are not independently promoted to permanence. The IWX
   group table in the text is stated through stem 90; the stem-93 input here
   is specifically its accompanying classical E-infinity data through 95
   and the matching finite differential computation, not that group-table
   corollary extrapolated beyond its stated range.
7. The Ext identities `h_0 n=0` and `d_1 h_4^2=0`, and
   `d_2(h_5)=h_0 h_4^2`, are used for the first Massey product. The bounded
   probe verifies both zero products and the defining differential against
   the stated database. It also verifies the degrees and complete bases of
   both indeterminacy summands.
8. Moss's convergence theorem and the full Toda shuffle equality are used
   with their actual hypotheses, not inferred from the project's unfinished
   Literature delivery theorem. Primary Moss source: *Secondary compositions
   and the Adams spectral sequence*, Theorem 1.2 and condition (1.3), printed
   p. 285. The independent auditor inspected that page. A modern readable
   statement is Belmont--Kong, Theorem 1.1, Definition 2.4 and Definition
   3.11. IWX gives the higher-page convention and the zero-detection warning
   in `more-stable-stems-background.tex:458--487,607--616`; its shuffle
   equality, including equal product-set indeterminacies, is at 844--891.

## Proof

### 1. A calibrated Toda representative of the AF-6 class

The Toda bracket `<n,2,theta_4>` is defined by inputs 1 and 2. On `E_3`,

\[
 \langle n,h_0,h_4^2\rangle=\{h_5n\}
 \subset E_3^{6,68}.
\]

Indeed, on the preceding `E_2` page use `0` as the nullhomotopy of `n h_0`
and `h_5` as the nullhomotopy of `h_0 h_4^2`. The defining value is `h_5 n`.
The left indeterminacy is `E_3^{4,36} h_4^2`; its unique possible generator
is `d_1`, and `d_1 h_4^2=0`. The right indeterminacy is
`n E_3^{1,32}=0`, because `h_5` supports the stated `d_2`. Thus this is a
singleton calculation, not just a claim that the Massey set contains `h_5 n`.

Here is the complete Moss crossing check. For a product in filtration `f`
and stem `v`, on `E_r` a crossing can have source in stem `v+1`, filtration
`q<f-(r-1)`, and differential length `m>r`, with `q+m>f`.

* For `n h_0`, `(f,v,r)=(6,31,3)`: only `0<=q<4` matters in stem 32.
  The only source is the permanent class `h_1 h_5` at `q=2`; hence there is
  no crossing.
* For `h_0 h_4^2`, `(f,v,r)=(3,30,3)`: only `0<=q<1` matters in stem 31,
  and this range is empty.

Moss therefore supplies a class

\[
       \alpha\in\langle n,2,\theta_4\rangle
\]

detected by `h_5 n`, of Adams filtration exactly 6.

### 2. The second bracket is genuinely defined

The bracket `<2,theta_4,theta_4>` is defined because both
`2 theta_4=0` and `theta_4^2=0`. It is a subset of `pi_61=0`, hence is
exactly `{0}`. The full shuffle equality gives

\[
 \langle n,2,\theta_4\rangle\theta_4
       = n\langle 2,\theta_4,\theta_4\rangle=\{0\}.
\]

In particular `theta_4 alpha=0`, so

\[
              B=\langle2,\theta_4,\alpha\rangle\subset\pi_{93}
\]

is defined. A second shuffle gives

\[
 \alpha^2\in\langle n,2,\theta_4\rangle\alpha
            = n B.
\]

Thus there is some `beta_0 in B` such that `alpha^2=+/- n beta_0`.

### 3. An E4 Moss application gives a high-filtration member of B

Apply Moss on `E_4` to the permanent inputs
`h_0`, `h_4^2`, `h_5 n`, of filtrations `1,2,6`. Their two products are
already zero on `E_3`: the first was killed by `d_2(h_5)`, and the second
is zero already in Ext. Zero preceding-page defining nullhomotopies are
therefore legitimate. The resulting Massey degree is

\[
 (1,1)+(2,32)+(6,68)-(3,2)=(6,99).
\]

The crossing ranges now are:

* For `h_0 h_4^2`, `f=3`, so `q<3-(4-1)=0`: no source exists.
* For `h_4^2(h_5n)`, `f=8`, stem 92, so only `q<5` in stem 93 is relevant.
  The only nonzero sources are `h_4^2 h_6` at `q=3` and
  `h_0 h_4^2 h_6` at `q=4`. Both support nonzero `d_4`, with respective
  targets `h_0^3 g_3` and `h_0^4 g_3`. Neither survives to support a
  qualifying later differential. Hence no crossing exists.

Moss supplies some member `beta_1 in B` of filtration at least 6. It is not
necessary to assert that the E4 Massey set is a singleton or that Moss
chooses its zero defining value: every possible permanent output lies in
the same degree, and the associated graded group there is zero. By input 6,

\[
                    \beta_1\in F^{10}\pi_{93}.
\]

The earlier E3 attempt really is blocked by the crossing
`d_4(h_0^2 h_4^2 h_6)=h_0^5 g_3`: its source filtration 5 satisfies the E3
bound `q<6`, and its target filtration 9 exceeds 8. At E4, the required
bound is `q<5`, which excludes that source. This is an ordinary weaker
filtration conclusion on a later page, not removal of a source hypothesis.

The standard sanity check is `<2,eta,2>={eta^2}`. Its E3 Massey product is
zero in AF 1; Moss says the bracket contains a class in `F^2`, which is
consistent with `eta^2`. It does not assert that the bracket contains zero.
IWX explicitly discusses this example and the zero-detection convention.

### 4. Control the full Toda indeterminacy before multiplying by n

The two members `beta_0,beta_1` belong to the same bracket with the same
actual inputs. Its full indeterminacy is

\[
                    2\pi_{93}+\pi_{31}\alpha.
\]

After multiplication by `n`, the first summand vanishes because `2n=0`.
The second summand lies in `F^{5+3+6}=F^{14}`, using input 4.
Meanwhile `n beta_1 in F^{5+10}=F^{15}`. Therefore

\[
 \alpha^2=\pm n\beta_0
        \in n\beta_1+F^{14}\pi_{124}
        \subseteq F^{14}\pi_{124}.
\]

This step is why a conclusion in `F^15` has not been claimed.

### 5. Remove the auxiliary choice of the AF-6 representative

For any prescribed `a_6` detected by `h_5 n`, write `a_6=alpha+delta`.
The detector equality gives `delta in F^7 pi_62=F^8 pi_62`. Since the
degree is even and `pi_62` has exponent 2,

\[
       a_6^2=\alpha^2+2\alpha\delta+\delta^2
             =\alpha^2+\delta^2.
\]

The last term belongs to `F^16`, so `a_6^2 in F^14`, as claimed.

## Reproduction and provenance

Run from the baseline worktree:

```sh
timeout 120s python3 -B local-history/Reports/strong-kervaire-cuts-20261022/theta5/probe.py --output local-history/Reports/strong-kervaire-cuts-20261022/theta5/probe-result.json
```

The probe sets address-space and CPU bounds of 4 GiB and 110 seconds. Its
source database is opened with SQLite `mode=ro`. Output is confined to this
report directory. It checks the Ext products, complete degree bases, raw
differential staircases, finite crossing windows, and structured CSV rows.
The final rerun completed successfully. No scratch Lean or shared builds
were run.

* Database: `/inspire/hdd/global_user/czxs25250150/ops/tmp/d3-x126-6-evidence/data/kervaire-49/S0_AdamsSS_t261.db`.
  SHA-256: `518a2ed86af6d4f7bcdc5db135ab6252bd50df34492ae208663aa1c140a820ed`.
* Helper: `/inspire/hdd/global_user/czxs25250150/ops/tmp/d3-x126-6-evidence/probe_data.py`.
  SHA-256: `d0f8a662c740bccd65264253c4aee7c2de725206fdc7b9bf6b87cc7e7f9f2f0c`.
* IWX classical CSV: `/inspire/hdd/global_user/czxs25250150/Kervaire126/Source/IWX/data/Adams-classical-Einfty.csv`.
  SHA-256: `1e3b79c97472241543f1c58e713cf4c96447f553d99a94a7fc6ce3eeaac8393b`.
* IWX LaTeX files cited above are under `/inspire/hdd/global_user/czxs25250150/Kervaire126/Source/IWX/source/`.
* Xu LaTeX is under `/inspire/hdd/global_user/czxs25250150/Kervaire126/Source/Xu/source/`.
* Moss's original PDF and Belmont--Kong text are under
  `/inspire/hdd/global_user/czxs25250150/Kervaire126Main/local-history/Reports/literature-source-verification-2026-10-18/secondary/sources/`,
  files `moss-original-gdz.pdf` and `belmont-kong-v2.txt`.

## Boundaries and discarded shortcuts

The Ext equation `(h_5 n)^2=0` alone gives only `a_6^2 in F^13`; it does not
give the result proved here. The vanishing of `h_1 n` in Ext does not prove
`eta n=0`, and `h_1 c_13=0` cannot distinguish the coefficient. Nonzero
`a_6` is not an eta multiple because `pi_61=0`. A detector called `h_1 g_3`
does not by itself exhibit an actual eta factorization since `g_3` dies.
None of these shortcuts is used. The proof uses neither an old unlayered
generalized Leibniz/Mahowald statement nor a disputed interface contract.

Remaining work is formal delivery of these classical source inputs and the
Toda/Moss argument within the frozen production interfaces, plus any
stronger calculation above filtration 13. No new public interface or proof
obligation is proposed by this report.
