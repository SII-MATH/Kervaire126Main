---
title: 命题 2.20 的共同核代表元与收敛桥
archived_from: local-history/metadata/interface-reviews/ProofTools/20261018-original220-convergence/report.md
archived_sha256: 653cca994d3ed5aad0b4a83e2cf5ec3e26ae6031a1da9ef0420c6449887e7d65
summary: "永久类到共同核代表元的强收敛桥仍缺失；按既有授权保持 statement 与直接待补，不请求立即修改接口。"
issue_id: "ProofTools-original-2.20-classical-ESS-convergence"
responsibility_module: "ProofTools"
targets:
  - "KIP126.ProofTools.Paper.extensionBoundary_of_exact"
baseline_commit: "9cd8ea5ac99f23d2ad65cba56a878ce03adce4b8"
worktree: "/inspire/hdd/global_user/czxs25250150/Kervaire126Main"
candidate_source_commit: "shared-working-tree; no implementation candidate proposed"
api_file_and_sha256: "metadata/proof-tools-api.json: 4fb52e6e3a5e0faf8d1d7f10d225131ff14a22b75c4de922942aba1ec1d9224b"
source_file_and_sha256: "KIP126/ProofTools/Paper/OriginalStatements.lean: 203d72615c5904c42f508b299489aba8f1ac8f5777e6280370765d8003ca71bb"
reporter_agent: "/root/convergence_interface_report"
independent_of_discoverer_and_implementer: true
evidence_level: "independent source/signature audit; Lean-checked conditional bridge; abstract filtered-group counterexample only"
status: pending-human-review
human_decision: null
---

# AimPaper 2.20：永久类到共同核代表元的收敛桥审查

## 请求人类决定的具体问题

**本轮按用户要求保持 statement 不变，并保留 2.20 的直接待补证明。没有请求立即实施接口变化。** 本报告供后续决定如何补足强收敛责任；不是对固定 `Model` 的反例报告，也不是证明命题为假的结论。

后续如果不能从当前完整 `Model` 推出下述核代表元桥，需要另行选择：继续构造固定模型所需的收敛理论，还是经明确授权补充上游数学契约。若要修改契约，须先具体说明如何表达 AimPaper 的全局条件、由谁证明、影响哪些调用方。给 2.20 添加局部核代表元假设或偷换 `ClassicalPermanent` 的定义，不属于本轮授权。当前没有足以实施的已批准调整方案。

用户对本轮的约束为：“那就先补这十个里能接上现有证明的，优先处理 2.15，保持 statement 不变，缺桥接的地方如实保留。”这不是对任何未来接口变化的授权；`human_decision` 因而保持 `null`。

## 原接口、背景与问题成因

### 完整声明及固定参数

源文件为 `KIP126/ProofTools/Paper/OriginalStatements.lean`；命名空间是 `KIP126.ProofTools.Paper`。完整上下文与原声明如下，原声明另原样保存于同目录 `original-signature.lean.txt`。

```lean
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)

public theorem extensionBoundary_of_exact (X Y Z : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (g : Y.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (hexact : ∀ d : ℤ, ∀ a : HomotopyGroup d (Y.obj D.auxiliary),
      a ≫ g = 0 ↔ ∃ b : HomotopyGroup d (X.obj D.auxiliary), b ≫ f = a) :
    ∀ d s : ℤ, ∀ y : ClassicalGrade D Y s d,
      ClassicalPermanent D Y Z g d s y →
      ∃ a : ℤ, a ≤ s ∧ ∃ x : ClassicalGrade D X a d,
        ClassicalExtension D X Y f d a s x y := by
  sorry
```

API 锁的类型指纹为 `14191341919733461197`。待补清单保留同名目标、模块 `KIP126.ProofTools.Paper.OriginalStatements`，状态 `pending-proof`。本报告未修改这些记录。

`ClassicalGrade D Y s d` 是同一给定 `D.classical` 在次数 `(s,d+s)` 的实际 Adams `E∞`，不是一个可自由替换的抽象滤过群。`ClassicalRepresents` 用同一 `D.classicalTower` 的像滤过和 `D.classicalConvergence` 的等价定义实际同伦代表元；其次数搬运是 `(d+s)-s=d`。`ClassicalExtension` 的完整定义为：

```lean
public def ClassicalExtension (X Y : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (d s t : ℤ)
    (x : ClassicalGrade D X s d) (y : ClassicalGrade D Y t d) : Prop :=
  ∃ a : HomotopyGroup d (X.obj D.auxiliary),
    ClassicalRepresents D X s d x a ∧ ClassicalRepresents D Y t d y (a ≫ f)

public def ClassicalPermanent (X Y : ClassicalObject)
    (g : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) (d s : ℤ)
    (x : ClassicalGrade D X s d) : Prop :=
  ∀ n : ℕ, ClassicalExtension D X Y g d s (s+n) x 0
```

结论只要求某个 `a ≤ s` 的 `f`-extension，允许 `x=0` 和非 essential extension。前提只要求中间同伦群处正合；没有要求短正合、满射、单射或指定的 cofiber sequence。

### AimPaper 的实际语境

独立读取了 **`AimPaper/main.tex`**，不是同目录只含图代码的 `112.tex`：

- 第 254 行规定全文谱对象为 **2-completed、connective、finite type**，并说明其 HF₂-Adams 谱序列强收敛。这是全局前提，不能因为没有重复写在 2.20 的局部陈述里就忽略。
- 第 648–654 行是 2.20 的原陈述：同伦群在中间项正合，则 `g`-ESS 的永久类都是 `f`-ESS 的边界。
- 第 656–661 行第一证明使用滤过三项复形的收敛与中间同调为零。
- 第 663 行第二证明明确从 ESS 收敛取得 **同一个** `g`-torsion 同伦代表元，再使用同伦群正合性提升到 `X`。

当前 `ClassicalTowerConvergence` 的字段仅为：

```lean
public structure ClassicalTowerConvergence
    (P : ClassicalTowerPresentation unit A) (X : C) where
  identification : ∀ p : ℤ × ℤ, ((A.obj X).ssData p).eInfty ≅
    (P.tower X).filtration.associatedGraded p.1 (p.2-p.1)
  canonical : ClassicalCanonicalIdentification P X identification
```

`canonical` 约束同一塔提升、cofiber 像、实际同伦代表元之间的对应；不是滤过拓扑上的完备性、Hausdorff 性或紧性。转成 `Convergence` 后仍只是弱收敛的 `E∞≅gr` 记录。`Model` 没有把 AimPaper 上述全局条件显式作为额外字段；其注释还明确不由这个接口制造滤过分离结论。

**已确认的接口疑点是缺少已实现的收敛桥，不是已确认的假命题。** 全部 `Model` 条件能否间接推出所需桥，本报告没有证明肯定，也没有给出否定的完整模型。

## 真实前提与对象核对

| 前提或对象条件 | 核对结果 | 证据及仍依赖的责任 |
| --- | --- | --- |
| 同一个 `D : Model C Syn` | 是 | 定理和全部 grade、tower、代表元关系都使用此 `D`；不能替成任意滤过群后声称推翻本定理。 |
| 稳定、加性、移位、张量与三角结构 | 是，作为实例前提 | `Context.lean` 的类定义不包含 t-structure、2-完备、finite type 或 Adams 强收敛条件。 |
| `X,Y,Z` 为指定对象闭包 | 是 | `Configuration.lean` 仅有 sphere、ν-cofiber、detector、整数 shift；detector 是带指定 unit 的实际参数对象。名字本身不提供 finite type 或完备性。 |
| Adams 塔来自同一系数单位，层与系数 smash 关联 | 是 | `Tower.lean` 的 `AbstractAdamsTower`、`ClassicalTowerPresentation` 包含 `layerIso`、`layer_unit`、实际塔映射及谱页对应；抽象群例没有构造这些数据。 |
| 实际同伦滤过及次数 | 是 | `filtrationSubmodule` 是 `projection s` 的像；`ClassicalRepresents` 用该滤过和实际 `E∞` 等价。 |
| `E∞≅gr` 和同一提升的 canonical 对应 | 是，`D` 的字段 | `Detection.lean:25–44`；不等价于永久 ESS 类具有共同核代表元。 |
| 中间同伦群逐次数正合 | 是，局部假设 | `hexact` 只要求 `ker(g_*)=im(f_*)`；这也能推出复合在各同伦群上为零，但不必推出谱映射本身为零。 |
| 对全部页的永久性 | 是，局部假设 | 是 `∀ n, ∃` 相应代表元；允许页与页之间更换代表元。 |
| 同一个代表元落在 `ker g_*` | 尚未接通 | 正是 AimPaper 第二证明使用的 ESS 收敛步骤。 |
| 源滤过在 `a≤0` 为全群 | 可从已有塔证明 | `stageAt a = stage a.toNat`；`a≤0` 时 projection 是 `zeroIso`。同目录 Lean 证据实际使用此事实。 |
| 源非零类的有限最大滤过 | 当前结论不需要 | 允许 `x=0` / inessential extension，可取 `a=min 0 s`，不用另设最大滤过假设。 |
| AimPaper 全局 2-完成、connective、finite type 条件已形式化 | 未在当前接口中识别出完整证明 | 不能把原文全局条件视为不存在，也不能把弱收敛记录当作它们的完整实现；整数 shift 对 connective 范围还需按实际有界下性质处理。 |

## 独立证据与复现

### 1. 量词差及精确未接桥

固定 stem `d`、滤过 `s` 和类 `y`。由定义和“零 grade 等价于下一层滤过”，`ClassicalPermanent` 给出：

\[
\forall n\ge0\;\exists b_n\in\{y\},\qquad
g_*(b_n)\in F^{s+n+1}\pi_dZ.
\]

所需桥是：

\[
\exists b\in\{y\},\qquad g_*(b)=0.
\]

两个式子不能直接交换量词。即使只知道 \(\bigcap_N F^N\pi_dZ=0\)，也只能对**固定的**目标元素取交；此处 `g_*(b_n)` 可以随 `n` 改变。增加一个未经证明的 “same witness” 选择不构成补证。

### 2. 已实际核验的 Lean 尾段

同目录 **`KernelBridge.lean`** 只证明：给定一个代表 `y` 的共同 `g`-核元素，使用原 `hexact` 即可推出原定理的结论。它不调用 `extensionBoundary_of_exact`，不证明或假定整体 `Model` 一致性，也不从 `False` 导出结论。

实际命令（在仓库根目录运行）：

```bash
lake env lean local-history/metadata/interface-reviews/ProofTools/20261018-original220-convergence/KernelBridge.lean
```

实际结果：退出码 **0**；`kernel-bridge.log` 中 `#print axioms` 只有
`[propext, Classical.choice, Quot.sound]`，**无 `sorryAx`**。这是报告内的条件引理核验，不是整个 2.20 或全仓构建通过。初次受限运行无法定位 Lake 配置；随后用环境允许的固定项目工具链完成核验，未变更依赖或工具链。

证明取 `a=min 0 s`。原 `hexact` 提供 `b : π_dX`，由 `F^aπ_dX=π_dX` 构造其 grade，允许这个 grade 为零。因此报告没有把一个不必要的“源代表元有有限最大滤过”任务转给下游。

### 3. 抽象滤过群警示例；不是实际 `Model` 反例

以下例子由报告员独立推导，说明**即便源和目标滤过都分离，也不能只凭弱 `E∞≅gr` 和逐页存在性完成量词交换**。它未构造本项目的完整 `Model`，证据等级限于抽象滤过阿贝尔群。

在 \(\mathbf F_2[[t]]\) 中令
\(\alpha=t/(1+t)=t+t^2+t^3+\cdots\)。取

\[
X=0,\qquad
Y=\mathbf F_2\alpha\oplus t\mathbf F_2[t],\qquad
Z=\mathbf F_2[[t]],
\]

`f=0`，`g` 为包含。令源 \(F^0Y=Y\)，\(F^sY=t^s\mathbf F_2[t]\)（`s≥1`）；目标 \(F^sZ=t^s\mathbf F_2[[t]]\)（`s≥0`），非正层延拓为全群。这是保滤过映射，两边滤过都分离，目标也完备；源未完成。

`g` 单射，所以中间正合且 \(\ker g=\operatorname{im}f=0\)。\(y=[\alpha]\in F^0Y/F^1Y\) 非零，因为 \(\alpha\) 不是多项式。对任意 `n≥0`，

\[
b_n=\alpha+\sum_{k=1}^n t^k\in\{y\},\qquad
g(b_n)=\frac{t^{n+1}}{1+t}\in F^{n+1}Z.
\]

因此抽象意义的所有出微分都为零，却不存在代表 `y` 的 `g`-核元素，且 `X=0` 没有非零目标的边界。这否定的是“任意这类滤过群都可以不经额外收敛条件推出核代表元”的推理。**它没有满足或检验 `Model` 中的系数单位塔、`layer_unit`、指定经典/合成范畴、ν/λ 恢复、比较、标准类和对象闭包，因此不否定固定的项目接口，也不反驳 AimPaper 全局假设下的命题。**

同目录 `abstract_reproduction.py` 以 GF₂ 多项式的位表示精确检查分子恒等式，在 `n=0,…,128` 的 129 个例子上通过；实际输出保存为 `abstract-result.json`。该计算只检查有限批次的见证；任意 `n` 的恒等式来自上面的代数推导，不能把有限计算称为全称 Lean 反例。

协调者转述的另一个 \(\mathbb Z_{(2)}\to\mathbb Q\) 目标常值滤过例也仅是抽象模型警示；本报告没有靠那个例子声称已经完成实际对象识别。

### 4. 传递依赖、循环和矛盾审计

- 本报告的已核验 Lean 条件引理只使用泛参 `D` 的定义、塔零层、给定的 `hexact` 和给定的核代表元。公理输出无项目待补或目标定理依赖。
- 原目标当前仍是直接 `sorry`。API 锁中包含 `sorryAx`，不应把它作为上游现成引理反过来证明所需 ESS 收敛桥。
- `Standard.classicalConvergence`、`Standard.classicalTower`、具体范畴和比较等生产者仍有登记的构造责任。调用它们时是带这些传递责任的条件性工作；没有据此证明任意群例已成为本项目的 `Model`。
- 没有构造 `False`，没有用不一致环境导出形式反例，也没有从使用 2.20 的结论回推出 2.20。本报告未完成泛参 `Model` 一致性验证，也未完成具体标准模型的强收敛实现。
- 全仓引用检索未发现数学证明体调用此新 2.20 定理；直接出现于自身、ProofTools 公共消费 `#check`、审计许可名单、API/待补锁和 Blueprint 绑定。数学依赖叙述还可能通过 Blueprint 条目引用该命题，其说明不等于已有 Lean 证明调用。

## 方案及精确差异

### A. 当前采用：保留原接口，保留直接洞，补内部收敛桥

优先路线是从同一固定对象和实际 Adams 滤过构造：

```lean
∀ d s : ℤ, ∀ y : ClassicalGrade D Y s d,
  ClassicalPermanent D Y Z g d s y →
  ∃ b : HomotopyGroup d (Y.obj D.auxiliary),
    ClassicalRepresents D Y s d y b ∧ b ≫ g = 0
```

这只是一项**私有中间目标**，不是新增的已接受假设。来源是 AimPaper:663 的 ESS 收敛步骤。现有 `KernelBridge.lean` 已验证其后有限代数尾段可接通。

可以研究的实质路线是证明在目标滤过拓扑中，\(g_*(F^{s+1}\pi_dY)\) 闭合。选择一个代表 `b₀` 后，逐页见证说明 `−g_*(b₀)` 属于该像的闭包；闭合性给出同一个修正元素，从而得到共同核代表元。另一条路线是在同一固定滤过下建立完整 ESS 的收敛/永久类检测定理，然后用它取核代表元。有限类型的 2-完备对象常见的紧性论证可作为来源候选，但当前 Lean 接口没有提供完成这条论证的拓扑和对象性质。

现有 `BoundedExtensionSS.weakConvergence` 明确需要两端滤过 `IsBounded`；`truncatedESS` 只为每个截断给出有界谱序列。不能从它们直接移除“有界”前提或把所有截断上的见证未经兼容性证明拼成极限。也不能假定某个有限页等于无限页。原2.20保留为待补恰好反映这一边界。

### B. 条件性差异示范：给原 theorem 增添核代表元前提

**本轮不建议、不申请实施此变化。** 为防止把较容易证明的另一个定理误认为原 theorem，精确记录差异：在原签名 `hexact` 后插入以下 binder，其他 binder 和结论逐字不变：

```lean
    (hkernel : ∀ d s : ℤ, ∀ y : ClassicalGrade D Y s d,
      ClassicalPermanent D Y Z g d s y →
      ∃ b : HomotopyGroup d (Y.obj D.auxiliary),
        ClassicalRepresents D Y s d y b ∧ b ≫ g = 0)
```

这样会严格增加证明输入，降低 theorem 对任意 `D` 的保证，把最关键的收敛责任交给调用方；对象关联及结论文字保持，但公共类型和数学契约改变。它不是本轮“保持 statement 不变”的补证方案。把 `ClassicalPermanent` 改写为“存在共同核代表元”同样改变公共谓词的语义，也会影响 2.19 等调用方，不能用来悄悄绕过桥。

若以后要调整，应优先讨论如何在**上游固定模型的真实来源责任**里表达并证明所需性质；这也可能改变 `Model`，影响范围远大于单个 theorem。没有完整反例和精确新契约前，不能从“暂时缺桥”推出必须修改接口。

## 下游影响

| 声明、记录或消费者 | 当前处理 | 若未来实质改接口的影响 |
| --- | --- | --- |
| `ProofTools.Paper.extensionBoundary_of_exact` | 保留名称、类型、前提、结论及直接待补 | 必须单独获准，重新核对与 AimPaper 全局条件的对应。 |
| `ClassicalPermanent` | 保持逐页存在性语义 | 改成共同核代表元会改变2.19与2.20的契约；不能默改。 |
| `Model` / `ClassicalTowerConvergence` | 只读，不修改 | 加强其字段是 AdamsSynthetic 的上游接口变化，需要模块授权、生产者构造与独立审查。 |
| `metadata/proof-tools-api.json` | 不修改 | 2.20类型/依赖变化必须如实更新；不能先改锁掩盖未获准变化。 |
| `metadata/proof-obligations.json` | 保留2.20原待补 | 原洞未补不能删除，也不新增伪收敛公理或待补项。 |
| `InternalAudit`、公共消费和 Blueprint 测试 | 本报告不修改 | 后续只在实际完成目标时更新状态，不把条件引理绑定成完整2.20。 |
| `blueprint/paper/ProofTools.tex` 的 `paper:2.20` | 保留原文与真实 pending 状态 | 来源说明可指出尚缺收敛桥；不得加入已完成证明的表示。 |
| `corrections.yaml` | 本报告未修改 | 尚未确认原命题错误，不能登记为固定对象反例或假命题。 |

## 阻塞范围与继续项

确实未完成的目标是 `extensionBoundary_of_exact` 的共同核代表元步骤，以及未来任何把它当作**已无待补依赖**的论证。当前未发现正在补的有限代表元论证必须调用它。

2.15、2.12、2.16、2.17 等有限滤过区间的代表元兼容性工作不需要上述极限量词交换，可以继续。2.19 的方向从已经给出的 `f`-extension 和零复合直接产生共同核代表元，也不需要先证明2.20。具体是否已经完成这些目标由各任务实际证明与统一构建决定；本报告不替它们发布验证结论。

未受争议的源码构建、公共接口类型核对、原文对齐检查和 Blueprint 原生状态导出也可继续。没有必要为此疑点冻结 ProofTools 全模块，更不需要改变 hgraph 状态规则。

## 人类审核记录

尚无针对本报告具体调整方案的人类决定。`status=pending-human-review`、`human_decision=null`。报告员建议、协调者阅读、其他报告的批准或等待均不等于本报告的授权。

本报告及所有证据仅写入协调者指定、被 Git 忽略的目录。`source-hashes.json` 和 `source-evidence.md` 记录共享工作树的读取快照；它们不声称整个工作树是一个干净提交，也不声称已经运行全仓构建。
