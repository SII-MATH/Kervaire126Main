---
title: 固定 tmf 与球谱对象上的 GL 反例
archived_from: local-history/metadata/interface-reviews/ProofTools/20261018-gl-fixed-object-counterexample/report.md
archived_sha256: 8c453dca1be9778ca6edc8c4788e00ad74cf734d89dca60cce8b799a33ca54ef
summary: "固定 tmf 与球谱上的数学反例否定原 GL 陈述；无 Lean 否定证书，且未获修改公共接口的授权。"
issue_id: "ProofTools-20261018-GL-fixed-object-counterexample"
responsibility_module: "ProofTools"
targets:
  - "KIP126.ProofTools.Standard.generalizedLeibniz"
  - "KIP126.ProofTools.GeneralizedLeibnizLaw"
baseline_commit: "18113d44df596c43d4fb7aab2aaf7ca9e0c52c48"
worktree: "/inspire/hdd/global_user/czxs25250150/Kervaire126Main"
candidate_source_commit: "uncommitted research evidence; shared dirty worktree"
api_file_and_sha256: "metadata/proof-tools-api.json; b22076575c6abdb44300a9e1959eb35d73bdd200767ea1f87a5098210ed30a7f"
source_file_and_sha256: "KIP126/ProofTools/GeneralizedLeibniz.lean; 5ffca10bbcfc95048225a2d17175a76374d804288d022e9ee1e64736167cd8b9 (report-finalization body)"
reporter_agent: "/root/fixed_counterexample_report"
independent_of_discoverer_and_implementer: true
evidence_level: "independently reviewed actual-object mathematical counterexample; finite checks passed; no Lean negation certificate"
status: pending-human-review
human_decision: null
---

# 固定对象 GL 反例：独立接口人审报告

**结论：当前 GL 的数学陈述在仓库允许的固定 detector（tmf）上也不成立。** 取 detector 自身的乘 2 映射，所有原前提成立，结论却要求 `d₄(0)=v`，其中 `v` 是非零永久存活类。此例没有引入新 classical 对象、直和、Moore 谱或可自由选择的 detector。

本报告完整核验 tmf 实例，包括实际 normalized map 的唯一性、原无限扩张、全部三个 crossing 位置、所有源线性组合、边界指数和结论页上的非零性。普通 tmf 与 2 完备 tmf 的关系单独论证，不靠省略 completion 条件成立。另有 sphere 实例会要求 `d₅(0)=gn`，见末尾独立审计补充。

这里的证据等级是**实际数学对象上的反例**。当前仓库尚未形式化该 tmf 计算与全部实际来源识别，故没有生成 Lean 命题 `¬ GeneralizedLeibnizLaw model ...` 的完整证明，也没有从 `sorryAx` 导出 `False`。这项形式化边界不能解释为数学反例只发生在一个任选抽象模型中。

## 请求人类决定的具体问题

用户本次授权是“找一个固定版反例”。本次已完成该研究与独立报告；没有得到公共接口修改授权。

需后续决定的是：如何处理已经失败的原 GL 目标。上一份报告的方案 A（保持全部原前提和结论，在既有对象上寻找特殊证明）不能再作为恢复原定理的路线。方案 B（新增实际同 weight 的无 crossing 充分条件）仍是独立、未批准的目标修改；本报告不将“找到反例”解释为批准 B，也不宣布 B 已证。

建议后续先确定需要的正确定理和实际应用范围，再给出精确修改签名及证明。不得默认把原责任移成下游额外结果包。此报告不请求批准某个尚未准备好的实现补丁。

## 原接口、背景与问题成因

公共 theorem 固定 `KIP126.AdamsSynthetic.Standard.model`，锁中无 free universe 参数：

```lean
public theorem KIP126.ProofTools.Standard.generalizedLeibniz
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary) :
    GeneralizedLeibnizLaw model X Y f
```

其完整 generic proposition 的上下文与声明如下；这些宇宙和实例均在 theorem 中由同一固定 model 专门化：

```lean
namespace KIP126.ProofTools
noncomputable section
open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams KIP126.AdamsSynthetic
open KIP126.Core.SpectralSequence KIP126.Kervaire.Route
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)
public def GeneralizedLeibnizLaw (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) : Prop :=
  ∀ (page : ℕ) (r m l s t : ℤ)
    (x : Ambient D X (s, t)) (y : Ambient D Y (s + m, t + m))
    (xInfinity : Ambient D X (s + r, t + r - 1))
    (yInfinity : Ambient D Y (s + r + l, t + r - 1 + l)),
    2 ≤ page → (page : ℤ) ≤ r →
    (normalizedExponent D.classicalTower f : ℤ) ≤ m →
    m ≤ (page : ℤ) - 2 + normalizedExponent D.classicalTower f →
    (normalizedExponent D.classicalTower f : ℤ) ≤ l →
    IsCycle D X (r - 1) (s, t) x →
    IsCycle D Y (r - 1 - m + normalizedExponent D.classicalTower f) (s + m, t + m) y →
    IsPermanent D X (s + r, t + r - 1) xInfinity →
    IsPermanent D Y (s + r + l, t + r - 1 + l) yInfinity →
    DifferentialAt D X r (s, t) (s + r, t + r - 1) x xInfinity →
    FiniteExtension D X Y f page m s t x y →
    InfiniteExtension D X Y f l (s + r) (t + r - 1) xInfinity yInfinity →
    (NoCrossingOn D X r page (s, t) ∨
      FiniteNoCrossing D X Y f page m s t) →
    InfiniteNoCrossing D X Y f l (s + r) (t + r - 1) →
    DifferentialAt D Y (r + l - m) (s + m, t + m)
      (s + r + l, t + r - 1 + l) y yInfinity
```

其来源为 AimPaper Theorem 6.1；Blueprint `paper/ProofTools.tex` 的 `paper:6.1` 条目保留原文。数学目的为：由一个经典微分、同一 map 的有限/无限扩张及指定无 crossing 前提推出下边微分。责任在 ProofTools；固定对象、实际塔、ν、归一化、比较和收敛分别由 AdamsSynthetic/Literature 提供。

`ClassicalObject` 只包含 sphere、ν-cofiber、detector 及其整数移位。这里 `X=Y=.detector`，并沿已指定的 `Literature.Standard.tmfIso : tmf ≅ model.auxiliary.detector` 传递。`f=2·id` 是这个对象的真实自映射。公开量词允许所有这样的 map，且并不要求 x、y、x∞、y∞ 非零。

`InfiniteExtensionWitness` 只要求相同实际 map 上的代表、cycle 条件和 `TowerExtensionEquation`；**不要求原扩张 essential**。`IsPermanent` 是共同永久 cycle，可含零或已经成为边界的 E₂ 标签。仅 crossing 候选要求 `.Essential`，并排除某个指定 B 层中的靶。`Extension.essential_iff_no_zero_target` 核对 essential 的全部目标陪集，而非仅检查一个选定靶非零。

问题分类为：**原数学命题为假，原 crossing 前提没有排除实际同 weight 的干扰**。它不只是尚未找到证明，也不是一个实现笔误。本例利用原接口确实允许的零标签和 inessential 原扩张；擅自补上“原扩张 essential”或“原标签非零”会改变题目。这样的限制可排除本例，但仅排除本例不等于证明修正版。

## 真实前提与对象核对

采用经典二次分次 `(s,t)`，stem 为 `t−s`。设

\[
 c=d_0w_2^2\in E_2^{20,130}(\mathrm{tmf}),\qquad
 v=\gamma^2g^3=\beta^2g^4\in E_2^{22,132}(\mathrm{tmf}).
\]

Bruner–Rognes 的独立计算给出 κ₄ 由 c 检测，`2κ₄≠0` 由 v 检测；所以 c、v 均在经典 E∞ 上非零。

精确参数为

\[
 X=Y=\mathrm{detector},\quad f=2\,\mathrm{id},\quad e(f)=1,
 \quad \mathrm{page}=r=2,\ m=1,\ l=3,\ s=17,\ t=128,
\]
\[
 x=0_{(17,128)},\quad y=0_{(18,129)},\quad
 x_\infty=0_{(19,129)},\quad y_\infty=v_{(22,132)}.
\]

| 原前提或对象条件 | 核验 | 来源／形式化边界 |
| --- | --- | --- |
| 固定 X、Y | 两者都是 `.detector` | 既有 `tmfIso`；实际 tmf/source 识别仍是项目待构造项 |
| 同一个实际 f 和 normalized map | f 为乘 2；normalized lift 唯一，是 scalar `tilde 2` | 下面的 factorization 与 Pstrągowski 精确序列 |
| `2≤page≤r` | `2≤2≤2` | 整数检查 |
| `e≤m≤page−2+e`，`e≤l` | `1≤1≤1`，`1≤3` | e 是首层 binary 指数，非完整 Adams filtration |
| 四个标签的次数 | `(17,128),(18,129),(19,129),(22,132)` | 逐项代入 Law；最后两个均 stem 110 |
| x、y 的 cycle 层 | 两个所需层均为 1；零标签属于它们 | 不假设任何非零源类 |
| x∞、y∞ 永久 | 零；v 非零永久存活 | BR21 Theorem 9.8(110) |
| 原经典微分 | `d₂(0)=0` | 真实线性微分 |
| page 2 的有限长度 1 扩张 | Q₁ 内实际源靶均取 0 | same map，正确的长度界；无需 essential |
| 无限长度 3 扩张 | 源代表 λC，像 `2C` 检测为 λ²v | 下面给出实际同 weight 构造 |
| 源 no-crossing disjunction | 经典分支成立：`0<a≤page−2=0` 无解 | 原 `NoCrossingOn` 的完整范围 |
| 无限 no-crossing | 全部三对 `(a,b)` 均排除 | 下面包含所有源组合、representative 和 B 层 |
| 结论失效 | 要求 `d₄(0)=v`；v 在 E₄ 非零 | 非零 E∞ 检测，非仅 E₂ 非零 |

## 独立证据与复现

### 原始来源与独立阅读

报告员未参与候选发现或实现。除读取发现者和审计者材料外，独立读取当前完整源码，并重新检查以下原始材料；相关原文片段、哈希、来源快照在 `evidence/`。

- [Bruner–Rognes, The Adams Spectral Sequence for Topological Modular Forms](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rognes-bruner-tmf-book.pdf)：Proposition 3.45/Table 3.6，printed pp.152–154；Theorem 3.46；Theorem 5.15 及 proof pp.191–192；Theorem 9.8(110)，statement p.315、proof p.318。ordinary tmf 有限生成及完备约定见 p.2；去掉 2、3 后的环计算见 Chapter 13 开头。附存文本为 `BR21-excerpts.txt`；原 PDF SHA-256 为 `cad4df7d4f6057408e7ec90d8b7003f5658cdd46ee5eb3972d66eaef86f6e1b1`。
- [Pstrągowski, Synthetic spectra and the cellular motivic category](https://arxiv.org/abs/1803.01804)：v3，Lemma 4.56、Proposition 4.57、Theorem 4.58，printed pp.54–55。此处 maps 的精确序列适用于任意 spectra，不偷加“tmf 有限”条件。
- [Burklund–Hahn–Senger, v3](https://arxiv.org/pdf/1910.14116v3)：Theorem 9.12，Theorem 9.19，Appendix A 的谱页比较、Proposition A.16、Corollary A.19。完成性仅在其真实适用范围内调用；ordinary 对象另作下面的传递。

没有以 AimPaper GL 或其 crossing 等价作为这些计算的证明。BR21 的隐藏乘 2 证明使用 tmf/2 的独立计算和 homotopy cofiber 精确列，相关源与目标并非本次 GL 实例中新增的对象。

### 完整低滤过窗口

Table 3.6 给出 Ext 作为 `F₂[g,w₁,w₂]` 的完整 cyclic-module 分解。因三种系数生成元的 stem 均被 4 整除，只需且必须检查 stem `2 mod 4` 的十个 module 生成元。独立脚本完整枚举它们的所有允许幂次，得到 stem 110 的完整窗口：

| filtration | 完整 E₂ 基底 |
| --- | --- |
| 19 | 0 |
| 20 | `c=d₀w₂²` |
| 21 | `b=h₀d₀w₂²`，`z=e₀γgw₂` |
| 22 | `b₂=h₂²w₁w₂²=h₀²c`，`v=β²g⁴=γ²g³` |

原始关系及 d₂ 计算给出

\[
 d_2(\beta w_2^2)=b,\qquad
 d_2(h_0\beta w_2^2)=b_2,\qquad
 d_2(z)=\alpha e_0g^4\ne0.
\]

最后一项位于 Table 3.6 的自由 summand，确实非零。因此 filtration 21 的永久 cycle 子空间恰为 `F₂{b}`；`z` 与 `b+z` 都不能用作无限 crossing 的源。`b,b₂∈B₂`，其中 B₂ 是累积至 d₂ 的实际边界层。

### 归一化 map 的唯一性

乘 2 后到第一 Adams coefficient 层的复合是零，因为该层为 HF₂-module，乘 2 在此为零。因此 f 通过第一 residual stage 分解，当前 binary 定义给出 `e(f)=1`。

记 h 为 synthetic scalar `tilde 2`，满足 `λh=2`。Pstrągowski Proposition 4.57 中 `(t,w)=(0,0)` 的前项为 `Ext^{-1,0}=0`，故

\[
 [\nu T,\nu T]_{0,1}\xrightarrow{\lambda}
 [\nu T,\nu T]_{0,0}
\]

是单射。λ 的自然性把这个乘法与仓库 `factorization` 中的 source precomposition 识别。因此任何满足固定 factorization 的 normalized map 必然是 h 的作用；不能换一个 λ-torsion lift 避开例子。

h 的源 weight 增加 1，其 Adams filtration 至少为 1，且 native leading action 是 h₀ 乘法。故 `c↦b`、`b↦b₂` 是同一个实际 map 的关联分次作用。不同实际源代表的高滤过差值只会映到再高一层。

### 同一 weight 上的实际无限扩张

先在完备 tmf 取实际类

\[
 C\in\pi_{110,130}\nu T
\]

由 c 检测，并使其 realization 等于上述 κ₄；BHS 9.19(3b) 保证可选择这个指定 realization。

在 normalized map 的 shifted source `Σ^{0,1}νT` 中使用 λC。其未移位 weight 是 129，移位后和靶的共同 weight 是 130。它处于 filtration 20，所以在需要的 filtration 19 源 grade 上恰代表零。其像是

\[
 h(\lambda C)=2C\in\pi_{110,130}\nu T.
\]

`2C` 的 filtration 至少为 21。在 weight 130 的 filtration 21，唯一永久候选 λb 被前述 d₂ 杀掉，z 不是 cycle，故这一完整 grade 为零。于是 `2C∈F^{22}`。

filtration 22、weight 130 的完整 grade 只余 `F₂{λ²v}`：λ²b₂ 也被 d₂ 杀掉。而 `2C` 的 realization 是由 v 检测的 `2κ₄`，不能处于经典 filtration 23；realization 保持 filtration，故 `2C` 也不能在 synthetic filtration 23。它必由 λ²v 检测。

这正是 `InfiniteExtension ... 3 19 129 0 v` 的 source `(19,129,130)`、target `(22,132,130)`，且 target 的 λ 次数为 `l−e=2`。`TowerExtensionEquation` 允许一个 F²⁰ 实际代表在 F¹⁹/F²⁰ 中代表零，故这是真实 witness。零代表也给出同源零靶，因此此扩张 inessential，完全符合原前提。

### 全部无限 crossing，含零源、所有源组合与靶歧义

原 infinite base 为 `(n,S,T,e)=(3,19,129,1)`，所以 `0<a≤2` 且 `0≤b≤2−a`。只有以下三种可能：

| `(a,b)` | 源 filtration / 未移位 native weight | shorter length | excluded B index | 全部候选如何排除 |
| --- | --- | --- | --- | --- |
| `(1,0)` | 20 / 130 | 2 | 3 | 非零源只能是 c。靶共同 weight 131 的 filtration 21 有非零 native b，像不能进入所需 filtration 22，故没有该 witness。 |
| `(1,1)` | 20 / 130 | 1 | 2 | 非零源只能是 c，唯一 leading target 是 b；b∈B₂，违反靶排除条件。 |
| `(2,0)` | 21 / 131 | 1 | 3 | 非零永久源只能是 b，唯一 native target 是 b₂；b₂∈B₂⊆B₃，违反靶排除条件。 |

每行的零源都不支持 essential extension：实际零代表的像为零，因此零属于完整目标陪集。filtration 21 的全部四个 F₂ 组合为 `0,b,z,b+z`；最后两者的 d₂ 非零，均已排除。

对于非零源，代表修改发生在更高 filtration，h 将修改项提高至少一层，不能改变所列最低非零输出。长度 1 的 native target λ 层数为 0，其 quotient denominator 是 `B₁=0`；尤其最后一行不能把 v 擅自加到 b₂ 上仍当成同一靶。以上也检查了实际 target coset，不将“有一个非零输出”误当 essential 性。

所以原 `InfiniteNoCrossing` 成立。可是原 witness 实际同 weight 的高滤过干扰确实存在；转到较高 native weight 后出现被 λ 消掉的 b 阻挡了原 crossing 定义所需的 shorter witness。这解释了为什么旧 no-crossing 条件漏检。

### 普通 tmf 的传递：不偷换为其 completion

若仓库的实际 tmf 指普通 connective tmf，而非完备版本，令 `j:T→T₂∧`，`C₀=cofib(j)`，并独立定义 synthetic `Q=cofib(νj)`。j 是 HF₂-homology equivalence；BHS 9.12(5) 给出 `Cλ⊗νj` 是等价，故 `Cλ⊗Q=0`，Q 上 λ 可逆。λ-inversion 保持 cofiber，由 9.12(1)–(3) 得

\[
 \pi_{n,w}Q\cong\pi_n C_0
\]

且不依赖 weight。这里没有假称 ν 保持任意 classical cofiber。

BR21 p.2 给出 ordinary tmf 每阶 homotopy 有限生成；Chapter 13 开头的 `π_*tmf[1/6]=Z[1/6][c₄,c₆]` 表明 π₁₀₉、π₁₁₀、π₁₁₁ 的 rational 部分为零，故这三群有限。完成化在有限群上是投影到 2-primary 部分。因此

\[
 \pi_{111}C_0\cong(\pi_{110}T)_{\mathrm{odd}},\qquad
 \pi_{110}C_0\cong(\pi_{109}T)_{\mathrm{odd}}.
\]

synthetic 精确列

\[
 \pi_{111}C_0\to\pi_{110,w}\nu T\to
 \pi_{110,w}\nu(T_2^\wedge)\to\pi_{110}C_0
\]

两端均为奇阶有限群。相关 middle groups 有限：在 weight 110 用 nonnegative-Chow 比较起步，再以 λ 精确列逐个到 129–132，所有涉及的 Ext 群有限。这给出每个所需 weight 上 2-primary 部分的同构。

这些同构来自同一个 completion map，与 λ、唯一 normalized h、actual Adams tower 及共同 Ext 标签相容。对 2-primary 部分 filtration 也相容且反映：Adams coefficient 层在 completion 下相同，residual stage 的差只有同一个奇阶部分，逐层 lifting 不产生 2-primary 障碍。ordinary kernel 的奇阶元素在 mod-2 associated grades 中全为零。

因而可取 completed C 的 2-primary 原像，上述像、检测和 source relation 原样传回普通 tmf。所有 native crossing 的 E₂/永久源子空间也未改变，奇阶或高滤过修正不能改变 leading action。2-local tmf 情况更简单：所需两端直接为零。实际反例不依赖把仓库 detector 换成另一个对象。

### 假结论与实际检查

GL 要求的页为 `r+l−m=4`，即

\[
 d_4(0\in E_4^{18,129})=v\in E_4^{22,132}.
\]

左边为零，右边非零，因为 v 非零存活到 E∞。故原结论为假。普通零微分以及有限零扩张不是遗漏前提，而是现有声明明确允许的数据。

报告员实际运行以下命令，均 exit 0；完整结果及 scope 见 `evidence/validation.json`：

```sh
python3 local-history/metadata/interface-reviews/ProofTools/20261018-gl-fixed-object-counterexample/evidence/independent_check.py
python3 local-history/proof-sessions/gl-fixed-counterexample-20261018/detector/check_stem110.py
python3 local-history/proof-sessions/gl-fixed-counterexample-20261018/audit/tmf_degree_check.py
python3 local-history/proof-sessions/gl-fixed-counterexample-20261018/sphere/evidence/check_window.py
```

第一条由报告员独立编写，重核完整可贡献基底、degree、全部 crossing 位置和所有源组合。程序验证的是有限计算；文献定理、实际对象与 synthetic 群的识别由上面的数学论证承担。其通过不能升级为 Lean 反例证书。

另一个独立 auditor 的普通 public-import `InterfaceProbe.lean` 已 exit 0，打印完整 kernel 类型与依赖；日志快照在 `evidence/peer-snapshots/audit/`。报告员没有把该类型 probe 当成 counterexample proof，也没有声称自己运行了该 Lean probe。先前 sandbox 尝试的 executable-location 失败后来由获自动批准的正常环境执行解决，并非 Lean 工具链损坏。

本报告只写其分配的 review_dir，不改生产、锁或待补记录；没有全量 `lake build`。本次报告型检查不需要修改生产构建输入，生产改动的全量验证仍由相应实施者负责。

## 循环、未证及矛盾依赖审计

1. 数学证据链为 BR21 的 independent Ext/d₂/hidden-2 计算，加 Pstrągowski 与 BHS 基础比较。没有使用 GL、MH2、Proposition 5.10 的争议转换、其下游 Adams 计算或从矛盾推出任何事实。
2. fixed tmfIso、Standard category、ν、classical/synthetic towers、comparisons、normalizedMap、convergence 目前仍含项目已登记待构造／待证明责任。它们作为 Lean constants 的实现和 source recognition 没有被此报告完成；公开类型存在不等于所有实际识别已在 kernel 内完成。
3. tmf stem 110 的完整外部计算尚未在仓库 E2Computation/Literature 中变成可实例化 Lean 输入。若将来形式化此反例，须按责任边界正式处理，不能给本次随手新增公理或待补项来凑一个 `False`。
4. 本报告独立证明实际 tmf 上的 map 行为，不以 Standard.model 的 `sorryAx` 为“计算结果”。数学已确定与 Lean 实现未完成是两条不同结论。
5. 报告开始后，另一个任务并发更新了 `GeneralizedLeibniz.lean` 的证明体：新增 LeftEdge/MinimalBottom 组装，仍保留两处 crossing 洞。完整 Law、Language、API 未改。最终复查还发现 `metadata/proof-obligations.json` 仅同步了该 theorem 的 body fingerprint（`17631794875784975235→1860436171643766606`），type fingerprint 与 `pending-proof` 状态未改；其余已快照文件未改。旧 body hash 为 `660fd29e307a53b89b0478452d6faaaae56529417a61686293f41ac7666f0e3d`，当前 hash 见 front matter；差异在 `evidence/concurrent-gl-body-change.diff`。新增分支只解决 `l≤e` 的局部情况；本例 `l=3>e=1`，sphere 例 `l=4>e=1`，故不影响本反例或其接口判断。

## 方案及精确差异

### 保留原接口的内部证明方案

已先评估：只补 proof body、利用既有对象特殊性质、或换一个 normalized lift，都不能证明本次已满足全部前提的原结论。tmf 本身就在固定范围；normalized lift 已由实际精确序列唯一确定；所有 crossing 已穷尽；目标 v 在结论页非零。因此，在保持所声明实际数学对象和来源识别的前提下，原方案 A 已被反例排除。

`l≤e` 等原定理子范围可能仍可证明；这些是有限范围的正确结果，并不能推出全量原接口。不应因为已有 LeftEdge、minimal case 或方块 helper 编译通过，就声称原 GL 已闭合。

### 尚未批准的调整方向

本次任务未要求交付修正版 theorem；报告不提出未经证明的新完整签名供立即实施。

上一报告的方案 B 有一个明确语义差异：在现有两项 crossing 前提上，额外要求实际同一个商/同一 weight 的有限边与传播后底边没有 essential crossing，原结论和其余量词保持不变。这加强前提、缩小适用范围；详细拟议 predicate 签名见 [上一报告](../20261018-gl-crossing-lambda-lift/report.md) 的“方案 B”。本报告没有重新审定 B 的充分性，更没有批准或应用它。

另一些可能的人审方向是仅保留已证子范围，或增添原扩张 essential 等真实数学条件；这些都会改变原 signature/body semantics。**尚无证据支持任意一个简单附加条件单独就是正确修复**。尤其“禁止零标签”或“要求 essential”不能凭它排除本例就作为已证定理交付。

因此此处没有伪造已备妥的候选签名；后续接口方案需要单独给出原/新完整声明、证明和应用范围，批准范围也须单独指定。

## 下游影响

| 声明／记录／测试 | 精确影响与责任 |
| --- | --- |
| `ProofTools.Standard.generalizedLeibniz` | 原全面求证目标在所声明实际对象上失败；不能继续依原 crossing 转换闭合两处洞。 |
| `ProofTools.GeneralizedLeibnizLaw` | 定义本身是合法 proposition；但当前 theorem 断言对全部固定对象/map 成立是假的。改正文即语义改接口，即使 `...→Prop` 的表面锁类型不变。 |
| 原 `InfiniteNoCrossing` / `FiniteNoCrossing` | 反例证明它们不足以推出本 GL；不因此授权全局改定义，后者会波及其他应用。 |
| 固定 detector / tmfIso / normalizedMap | 沿原对象和唯一 map 计算。不得为消除此例而偷偷换 detector、map 或 source identification。 |
| 生产调用者 | 当前 KIP126 生产代码未实际调用 `generalizedLeibniz`；`Tests/ProofTools/Consumers.lean` 整体消费该 Law，名称/消费通过不验证数学正确性。 |
| Main | `KIP126/Main/InternalAudit.lean` 明确禁止 GL 与 MH2 进入 public-root 依赖。此反例不直接否定 Main 当前路线或主目标。此边界不代表 Main 全部上游责任已无待补。 |
| MH2 | 不是本次反例目标；不凭 GL 失败宣告 MH2 假，也不修改或接手其责任。 |
| 私有已证辅助 | LeftEdge、minimal length、实际方块和有条件读出仍可独立使用，保留其精确前提，不冒充无条件 GL。 |
| `metadata/proof-tools-api.json` | 后续若获准调整需准确重捕获名称、类型、导出、公理依赖；本次无改动。 |
| `metadata/proof-obligations.json` / `ProofTools.InternalAudit` | 当前两处 GL 洞仍在；不得靠删除待补项或放宽 audit 宣称通过。本次不写这些协调记录。 |
| Blueprint / hgraph / MEMO | 旧“反例未落入固定范围”的历史结论需要以后由协调者按真实授权更新；本报告给出替代证据，不自行扩大写权限。 |
| 测试与后续实现 | 若批准修订，保留 public consumption、接口锁、私有隐藏、Main boundary、Trust；运行 inventory 与 lake build。加入精确 regression 应检验正确新前提，不删除既有覆盖。 |

## 阻塞范围与继续项

**被证据确实阻塞**：原固定 GL 全量目标的正确证明；在原 crossing 前提下无条件完成底边实际 no-crossing 转换；任何依赖这些未成立断言的后续推导。

**可继续**：不调用 GL/MH2 的 Main 路线；独立的 E₂/Adams 输入；有真实附加条件的内部方块、LeftEdge、minimal-length 结果；针对有具体用途的正确修正版进行研究；按既定责任将外部 tmf/sphere 反例形式化。是否实施某个公共修改仍需人类明确决定。

### 补充：同一固定对象范围内的 sphere 反例

另一队独立发现并审计了 sphere 例，完整材料为 [sphere 发现报告](../../../../proof-sessions/gl-fixed-counterexample-20261018/sphere/report.md) 与 [sphere 独立审计](../../../../proof-sessions/gl-fixed-counterexample-20261018/sphere-audit/report.md)；为避免相对路径误读，本报告也将两者原文快照保存在 `evidence/peer-snapshots/sphere/` 和 `evidence/peer-snapshots/sphere-audit/`。

其精确输入是 `X=Y=.sphere`、f 为乘 2、`e=1,page=r=2,m=1,l=4,s=3,t=55`，`x=y=x∞=0`，`y∞=gn∈E₂^{9,60}`。依据 Wang–Xu 的 stem 51 hidden-2 结果，原前提可满足但结论为 `d₅(0)=gn≠0`。独立审计覆盖全部六个 crossing、完整源/靶窗口、order-2 代表、normalized lift 唯一性及 ordinary sphere 的 2-primary completion 传递；其数学审计结论为 PASS，不是未决的抽象对象候选。报告员重跑了该例的表格/degree 检查（exit 0），但本报告独立详细重建的是上面的 tmf 证明，**不以另一审计的 PASS 替代自己对 tmf 的核验**。

两例均无需引入 HZ/HZ4 或额外直和。找到任一个已经足够否定当前固定对象范围的原全称 GL。

## 人类审核记录

`status: pending-human-review`；`human_decision: null`。

本次用户指令为寻找反例，未包含批准公共接口调整的明确决定。研究、发现者意见、独立审计 PASS、协调者建议、等待或对不同报告的历史批准均不记录为本方案的人类授权。后续真实决定应记录原话、出处和精确范围；实施由协调者另行安排。
