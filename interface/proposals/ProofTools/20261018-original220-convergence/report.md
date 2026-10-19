---
title: 命题 2.20：恢复原文全局完备性提供的紧性条件
archived_from: local-history/metadata/interface-reviews/ProofTools/20261018-original220-convergence/report.md
archived_sha256: 653cca994d3ed5aad0b4a83e2cf5ec3e26ae6031a1da9ef0420c6449887e7d65
summary: "建议仅给泛型2.20补入Y的实际Adams滤过完备性及有限商、Z的滤过分离性；逐页永久性、hexact和结论不变。用户已明确批准三个自然条件及补证明；获准条件型定理已完成，独立实际Lean递归审计覆盖249项目节点且无证明洞。完整构建及Standard条件来源不由此替代。"
issue_id: "ProofTools-original-2.20-classical-ESS-convergence"
responsibility_module: "ProofTools"
targets:
  - "KIP126.ProofTools.Paper.extensionBoundary_of_exact"
baseline_commit: "0e940a5108088ad73a19415721060012a8aad779"
worktree: "/inspire/hdd/global_user/czxs25250150/ops/tmp/prooftools-main-proofs-20261019"
candidate_source_commit: "shared worktree; approved implementation in progress; reporter changes only report/evidence"
api_file_and_sha256: "interface/baselines/proof-tools-api.json: ba104746fa0e0b6ae2c34a961a02b530b3c8b3b439e404bdaeaebad4a35ed62a"
source_file_and_sha256: "KIP126/ProofTools/Paper/OriginalStatements.lean: ac4eb11d31ef053edcaa8553eba5b959fd2349fcd092b8d1341b3f13a04da7cc"
reporter_agent: "/root/convergence_reporter"
independent_of_discoverer_and_implementer: true
evidence_level: "independent interface/source audit; approved conditional theorem proved and separately kernel-audited across 249 project nodes with only 3 foundational axioms; reporter inspected artifacts without rerunning Lean"
status: approved-interface-change
human_decision: "2026-10-19 当前session用户明确回复：‘第一项和第三项同意，现在就可以改；并行地，交给一个 subagent 这个任务：第二项因为涉及到修改原来的自然语言，需要给一个具体的 pdf ，讲清楚原命题是什么，反例是什么，应该改成什么样子，发到 project-math-assistant’。此处第一项为2.20补hYcomplete/hYfinite/hZseparated；授权保留hexact、逐页永久性和原结论，完成证明及对应接口锁、待补和测试同步，不新增sorry。第三项5.14有独立报告；第二项5.10仅另行说明材料，不包含于本报告实施授权。原话与编号映射由协调者/root在本session派工消息转发，报告员未将其他批准或agent意见算作授权。"
---

# 2.20 接口补前提提案与独立审查

## 请求人类决定的具体问题

**用户已批准只给 `extensionBoundary_of_exact` 增加下列三个自然数学条件；原 `hexact`、逐页 `ClassicalPermanent`、所有固定对象及原结论保持不变。** 记 `Fⁿ` 为同一 `D.classicalTower` 的实际像滤过。对每个整数次数 d 要求：

1. **Y 完备：**典范映射 `π_dY → lim_n π_dY/Fⁿπ_dY` 是双射，n 遍历自然数，极限沿商映射取。
2. **Y 的有限商：**对每个自然数 n，群 `π_dY/Fⁿπ_dY` 有限。
3. **Z 分离：**若 c∈π_dZ 满足对每个自然数 n 都有 c∈Fⁿπ_dZ，则 c=0。

这是**充分、自然的前提组合**，不是必要条件或最弱条件的声明。Y 因而带实际 Adams 滤过的 profinite 紧拓扑；g 由实际 tower map 保滤过而连续，Z 的拓扑 Hausdorff。这些性质足以完成永久类到共同核代表元的桥，不需要对 X 加条件，也不需要新增“存在共同核代表元”这种与目标同形的假设。

**分类：形式化遗漏来源全局前提所提供的完备性/紧性，不是 AimPaper 自然语言命题错误。** AimPaper `main.tex:254` 已明确全篇谱为 2-completed、connective、finite type，不能把局部2.20当成对任意不完备谱的陈述。所提条件描述这些来源条件在本证明中实际使用的后果；它们不把范畴、detector、Adams 塔换成其他对象。

已批准的实施范围限于该公开定理的三个新增 binder、与其对应的接口锁/待补类型、消费测试和来源/Blueprint条件说明。证明仍由 ProofTools 负责。**不请求授权给 AdamsSynthetic 新增公理或待补责任，不把紧性证明默认转给下游，不更改 Model 全局字段，不改 `ClassicalPermanent` 的语义。** 若后续要给 Standard 提供无额外前提的专用推论，需要另核对其实际完整/有限类型来源证明，不能本报告批准后自动制造一个 Standard 完备性公理。

## 原接口、背景与问题成因

### 完整原声明与语义

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

`ClassicalGrade D Y s d` 是同一实际 Adams E∞ 在 `(s,d+s)` 的分量。`ClassicalRepresents` 通过同一实际 tower 的像滤过和同一 canonical convergence 同构定义代表元。其代表元集合是 `a₀+F^(s+1)π_dY`，不是任意新选的滤过。

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

`hexact` 只要求中间同伦群正合，允许一般映射、非短正合、非三角。结论允许零源类/非 essential extension 和任意 `a≤s`。新增条件不加强这些局部语义。

`ClassicalTowerConvergence` 只提供实际 `E∞≅gr` 及同一塔提升的 canonical 方程；`Model` 另外要求合成比较、恢复、全部选定对象收敛等，但没有明示上述完备、有限商及分离条件。`E∞≅gr` 不等于滤过拓扑完备，也不等于永久 ESS 类具有共同核代表元。

AimPaper `main.tex:648–664` 的2.20在第254行全局条件下，第二证明先通过 ESS 收敛取得一个 g-核代表元，再用同伦群正合性提升。当前泛型 `D : Model` 缺少将全局条件接到这一步的接口。普通实现错误与“目前没有证明”须区分：此前只有缺桥疑点；本轮谱级模型候选进一步显示，不应继续把弱收敛当作充足的极限输入。

## 真实前提与固定对象核对

| 条件 | 独立核对 | 证据及局限 |
| --- | --- | --- |
| 同一个 D、实际塔、实际像滤过 | 是 | `System.lean`、`Tower.lean`、`Detection.lean`、`OriginalStatements.lean`。没有替换目标对象后声称补证。 |
| 实际 Adams 系数单位、layer_unit、自然 map | 是 | Model 要求同一系数单位塔；候选使用实际系数 fiber tower，而非抽象滤过群。 |
| X/Y/Z 属于指定 ClassicalObject 闭包 | 是 | sphere、ν cofiber、参数 detector、整数移位；类型不把 detector 自动识别为 tmf。 |
| hexact 逐所有整数次数 | 是 | 候选 g 在π₀单射，其余次数 M 的同伦为零；f=0，恰满足 `ker g=im f`。 |
| 原逐页永久性语义 | 是 | 候选甚至同一个代表元产生全部零 outgoing extensions；没有交换见证后偷用共同核。 |
| 源负滤过全群 | 是 | `stageAt s=stage s.toNat`，s≤0时为零层；原结论可取源滤过 `min 0 s`，不用 X 完备/分离/有限型。 |
| 泛型 Model 可推出全局源/目标拓扑条件 | 未获证明 | 完整谱级候选字段审计在同目录证据；不能直接从弱 convergence 推出。 |
| 候选恢复及单位匹配 | 数学上核对 | 只取非hypercomplete HF₂合成范畴的odd-local子范畴，其**局部化单位**为νS_(2)，λ可逆子范畴恢复Sp_(2)。不是把全部合成范畴误认成2-local恢复。 |
| 所有递归 SyntheticObject 的收敛 | 数学上覆盖 | 首个正λ商消去 rational summand；完整基对象有限移位/嵌套商的实际 tower layer 每tridegree有限，配合nilpotent completeness及ML得canonical convergence。没有Lean实例化所有字段。 |
| AimPaper 全局2-complete/finite-type | 原文有，当前泛型缺 | 候选 M 故意不2-complete；不反驳原文，也不反驳Standard。 |

## 独立证据与复现

### 谱级反例候选：范围与可信等级

候选发现者为 `paper_tools`；本报告员未参与发现或实现。已主动逐字段核对 `ModelData` 及 Model 四个额外字段、来源和依赖。完整推导见 [独立字段与收敛审计](evidence/independent-model-audit-20261019.md)，收到的原候选另存 [候选快照](evidence/candidate-received-20261019.md)。这些文件随提案持久保存。

取 `C=Sp_(2)` 和上述实际非hypercomplete、odd-local HF₂合成范畴。取

`M=H(Z_(2))⊕H(Q[t])`, `X=sphere`, `Y=Z=detector=M`, `f=0`,

`g(z,p(t))=(0,z+t p(t))`。

g 是实际 Eilenberg–Mac Lane 谱映射。取常数项证明其单射，故逐所有次数满足原 hexact。实际 classical Adams 滤过为

`Fⁿπ₀M=2ⁿZ_(2)⊕Q[t]`，n≥0。

令 `y=[(1,0)]` 是对应的非零 E∞ grade 0 类；g 把同一代表元送到 `(0,1)`，这个非零 rational 元在每层滤过中。因此逐页永久性成立；原结论若成立，则 f=0 的像代表非零 y，矛盾。

这个例子既强调源不完备，也强调目标不分离。它不是三个候选条件逐一必要性的证明。历史中另有分离但源不完备的抽象滤过群警示例；仍不能把历史抽象群例单独称为完整Model反例。

**最高证据等级：具有完整字段审计的谱级数学反例候选；经典谱/滤过矛盾已独立确认，完整合成Model未在Lean中构造。** 所引 Pst/BHS 来源核对、完整范畴与canonical coherence的数学论证、所有有限嵌套商的ML覆盖见证据。没有内核检查的 `D : Model` 项，没有 `¬... Standard.model` 证明；不把有限计算当作谱级证书。若要求全部形式化后才能认定泛型定理为假，该门槛尚未达到；当前也无依据宣称标准模型环境不一致。

### 独立排除的错误传输

“completion cofiber 是 rational”本身不够推出 associated-grade 同构。`fiber(HZ_(2)→HQ)→HZ_(2)→HQ` 即为此简化推理的反例。正确的传输还需要每个次数的 `im(πB→πR)` 对2可除；候选实际 `S_(2)→S₂^∧` 和 `HZ_(2)→HZ₂` 的 cofiber 为 `H(Z₂/Z_(2))`，每个权重stem0像为整个可除商，其余stem像为0，满足所需条件。证据给出逐次数/权重及相邻stem的LES核对，未把“rational cofiber”无条件当作gr等价。

### 实际局部验证和来源

[局部精确计算及原命令](evidence/local-checks-20261019.txt) 检查1296个有理多项式取样的单射/像恢复、n=0…128的同一见证及非零grade0，退出0。全称单射性和永久性来自上述代数推导，取样不是全称证明。

[读取哈希快照](evidence/source-snapshot-20261019.json) 记录实际源码、API、原文、固定Pst/BHS源；它不是干净提交或全仓构建快照。局部读取和有理计算未写 `.lake/build`，未产生 .olean。依用户要求本轮不运行完整检查，也未运行新的Lean测试。

固定来源为 `/inspire/hdd/global_user/czxs25250150/Kervaire126/Source/Pst/source/synthetic_spectra.tex` 的完整homology-SES保三角、λ恢复、CλνX心对象/Ext，以及同根 `Source/BHS/source/SynRevAdams.tex` 的 `thm:synth-ASS`、`lemm:easy-e-compton`、`thm:strong-conv`。BHS的strong convergence要求nilpotent completeness；报告没有把其任意X的E₂比较误用于不完备对象的strong convergence。

### 循环、未证和矛盾依赖审计

没有调用2.20自身、GL/MH、Main不相容定理、Standard未证构造或由它们得到的False来证明反例。候选使用外部标准谱/合成理论作为数学输入，未将项目sorry伪装成模型构造。`canonical_convergence_natural`在Standard源码有泛型定义层推导可供对照，但证据不通过Standard的未完成背景“构造”该模型。

当前OriginalStatements源码已有两个private引理：`classical_permanent_iff_approximate_kernel` 精确识别 `∀n∃` 近似核代表元，`classical_boundary_of_kernel_representative` 完成取得共同核后的代数尾段。本报告只阅读这些引理，没有本轮重新编译或声明其全仓信任审计已通过。

旧报告保留在 [更新前完整历史](evidence/report-before-20261019-review.md)，包含当时已编译 `KernelBridge.lean` 的命令/结果及仅为抽象滤过群的证据等级。该历史结果不是本轮新运行。原始迁入来源/哈希保留于文件头；历史授权只允许保持原statement补证，不构成本轮三个binder的新授权。

## 方案及精确差异

### 先评估保留原接口

有限代数尾段可以保留并完成；困难集中在紧性/闭像桥。仅靠现有弱 E∞≅gr、自然性、实际塔和永久性，没有可审核的内部证明推出所需紧性。谱级模型候选解释缺失输入为何实质相关。不能通过交换 `∀n∃a_n`、把分离性当完备性、或给永久性改定义来伪装成原类型补证。

若完全保留原类型，仍需证明整个Model蕴含足够的闭像条件，或证明并排除完整候选的某一字段；本轮没有完成这条路线。相比继续在缺前提的泛型语境里寻找极限证明，补回来源条件的实际后果更直接。本报告所列三个新增条件现已获准，ProofTools可继续实施与补证；获准不等于证明或构建已经通过。

### 推荐候选签名

以下是**获准的候选接口完整文本**；本报告员不修改源码；获准后实际实现及独立审计结果见末尾验证补记，不把初始候选文本当成新的构建证据。宇宙、实例、D、X/Y/Z、f/g及hexact沿用完整原上下文。`hYcomplete`的序列形式等价于上面典范映射到逆极限双射：兼容商代表元的相邻差落Fⁿ；唯一极限代表元给出满射和分离性。它是滤过本身的完备性条件，不包含g、y、permanence或结论。

```lean
public theorem extensionBoundary_of_exact (X Y Z : ClassicalObject)
    (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary)
    (g : Y.obj D.auxiliary ⟶ Z.obj D.auxiliary)
    (hexact : ∀ d : ℤ, ∀ a : HomotopyGroup d (Y.obj D.auxiliary),
      a ≫ g = 0 ↔ ∃ b : HomotopyGroup d (X.obj D.auxiliary), b ≫ f = a)
    (hYcomplete : ∀ d : ℤ,
      ∀ q : ℕ → HomotopyGroup d (Y.obj D.auxiliary),
        (∀ n : ℕ, q (n+1) - q n ∈
          (D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule (n : ℤ) d) →
        ∃! b : HomotopyGroup d (Y.obj D.auxiliary),
          ∀ n : ℕ, b - q n ∈
            (D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule (n : ℤ) d)
    (hYfinite : ∀ (d : ℤ) (n : ℕ),
      Finite ((HomotopyGroup d (Y.obj D.auxiliary)) ⧸
        (D.classicalTower.tower (Y.obj D.auxiliary)).filtrationSubmodule (n : ℤ) d))
    (hZseparated : ∀ (d : ℤ) (c : HomotopyGroup d (Z.obj D.auxiliary)),
      (∀ n : ℕ, c ∈
        (D.classicalTower.tower (Z.obj D.auxiliary)).filtrationSubmodule (n : ℤ) d) →
      c = 0) :
    ∀ d s : ℤ, ∀ y : ClassicalGrade D Y s d,
      ClassicalPermanent D Y Z g d s y →
      ∃ a : ℤ, a ≤ s ∧ ∃ x : ClassicalGrade D X a d,
        ClassicalExtension D X Y f d a s x y := by
  -- proposed compactness bridge and existing finite algebra
  ...
```

三个新增前提缩小泛型适用范围；结论不变，ClassicalPermanent逐页语义不变，对象关联不变，ProofTools责任不变。序列形式比“存在某次g核代表元”自然得多，能独立在来源的实际谱滤过上核验。若使用命名predicate封装这些binder，应保持以上完整量词与实际tower绑定；新增public predicate本身也须在批准范围内明确登记，不能顺手扩接口。

### 充分性的独立证明

固定d，令A=π_dY，B=π_dZ，赋实际Adams滤过拓扑。hYcomplete+hYfinite将A识别为有限离散商的逆极限，所以A紧且Hausdorff。hZseparated使B为Hausdorff。D.classicalTower的实际map使g保持每层，故连续，无需额外连续性binder。

给定y与其任一代表元a₀，代表元全集R=a₀+F^(s+1)A是开闭的：s+1>0时是有限商的coset，s+1≤0时是全群。故R紧，g(R)在B中为紧闭集。永久性给出每n存在a_n∈R使g(a_n)∈F^(s+n+1)B；这些层在n→∞时构成零点的共尾邻域基，包括s为负整数的情况。所以0在g(R)闭包内，从闭性得0∈g(R)。取得一个共同g核代表元后，接现有hexact与private有限尾段即可。源X的元素在 `min 0 s` 层总可取grade，允许它为零，因此无需X的最大滤过/紧性/分离条件。

三个条件不是逐一必要。比如某些特殊g本身已有闭像，或存在其他强ESS收敛输入，也能完成桥。单纯“Y完备”没有有限商/紧性论证通常不够；单纯“Z分离”也不能交换逐页见证。只添加“hkernel”虽易证明却把核心责任交调用方，不是推荐修复。

### 其他方案及范围

另一个数学可行方向是加强上游Model到确实表示原文完整类别，或将2.20限于已实现来源的Standard系统；这会触及AdamsSynthetic公共对象与多模块接口，范围明显更大，也不能由本报告直接实施。推荐的三个局部自然前提避免强制所有泛型消费者承担不相关全局字段；来源模型满足它们的事实仍须有实际证明，不能新增未证公理。

## 下游影响

| 目标/记录 | 推荐调整的影响 |
| --- | --- |
| `ProofTools.Paper.extensionBoundary_of_exact` | 只新增三个binder，按新类型证明；原直接洞只有真的补完后才删除。 |
| `ClassicalPermanent` / `ClassicalGrade` / `ClassicalExtension` | 类型与语义全部保持，不借改谓词获得证明。 |
| `Model` / `ClassicalTowerConvergence` / `SyntheticObject` | 不改；完整来源实现责任不转进ProofTools，不新增上游公理。 |
| `interface/baselines/proof-tools-api.json` | 经授权后更新2.20类型、最终实际公理依赖及完整导出，不能提前改指纹绕门禁。 |
| `interface/baselines/proof-obligations.json` | 授权改类型时如实同步该既有责任类型；未完成证明仍保留pending。 |
| `KIP126/ProofTools/InternalAudit.lean`、`Tests/ProofTools/Consumers.lean`、`Tests/test_blueprint_native.py` | 核对名称消费和唯一原statement对应；新增有意义的条件消费/边界检查，不删除已有覆盖。 |
| `blueprint/paper/ProofTools.tex:paper:2.20`及hgraph附件 | 保留AimPaper原句及其全局条件来源说明，准确写出形式化使用的三个后果，不将条件引理冒充已证原泛型定理。 |
| `corrections.yaml` | 相对AimPaper修正的唯一记录源；分类应写形式化漏全局条件，不把本文登记成原文数学反例。本报告不写此共享文件。 |
| 数学Lean调用方 | 本轮检索未见其他证明体使用该定理；主要消费者为上述#check/审计/蓝图，最终仍需整合后重新检索。 |

依现有批准完成三个目标的证明工作后由协调者统一跑source inventory、接口/责任/公共消费审计及完整lake build。用户当前明确暂缓完整检查，本报告没有提前触发。

## 阻塞范围与继续项

原泛型类型的共同核代表元极限步骤不能只靠弱收敛补足。三个自然条件的调整现已获准，可继续在ProofTools内部证明紧性桥并接现有尾段；不得新增sorry、公理或将关键证明责任转移给下游。

5.10、5.14的有限/无限合成比较责任需要各自核对，不能由本2.20候选直接判假；不受本报告自动阻塞。已授权删除旧GL/MH、保留law与AtLevel版本、Main已有补证及其同步可继续。本报告不撤回其他改动，不声称解决其他问题。

## 2026-10-19 获准条件型定理的实际验证补记

**获准后的 `extensionBoundary_of_exact` 已完成Lean证明，独立审计员 `main_audit` 对其实际传递闭包的内核环境检查覆盖249个项目声明，未发现项目axiom、普通sorry或synthetic sorry；collectAxioms只有 `[propext, Classical.choice, Quot.sound]`。** 这是带本报告三个自然条件的定理，不是旧无条件泛型定理或Standard条件已获来源证明的声明。

本补记的证据来源分两层：协调者 `/root` 转发独立审计员实际成功运行的结果，并将原件存于 `local-history/proof-sessions/20261019-approved-220-514/`；本报告员**没有重新运行Lean或全量检查**，只读取审计源码、输出JSON和普通公共导入日志，独立核对其完整条件签名、宇宙与固定对象及依赖闭包。可分享副本保存在本提案evidence中，避免网页依赖被忽略的local-history：

- [该目标完整审计JSON](evidence/KernelAudit22020261019.json)：从原PaperAudit20261019.json原样提取本root的完整对象，含完整elaborated type、宇宙u/v/w、249项type/body依赖和三项axioms。
- [审计源码](evidence/PaperAudit20261019.lean)：使用实际已编译声明的type及opaque body递归遍历，遇任一KIP126节点 `ci.isAxiom`、`ci.type.hasSorry` 或 `body.hasSorry` 即抛错；不依赖人工待补名单来决定“无洞”。
- [普通公共导入核对源码](evidence/PaperAuditPublic20261019.lean) 与 [实际公开类型输出](evidence/PaperAuditPublic20261019.log)。
- [报告员读取核验与原件SHA-256](evidence/kernel-audit-review-20261019.json)，以及 [实际实现签名](evidence/implemented-signature-220-20261019.lean.txt)。

实现以 `hYcomplete : ∀ d, Nonempty (Filtration.CompletionWitness actualFiltration d)` 表达完备性，而非上文提案展示的兼容代表元序列版本。已独立读取 `CompletionWitness` 定义：其唯一字段是**同一actualFiltration的canonical quotientTowerCone为极限锥**，即典范映射到 `lim_s π_dY/F^sπ_dY` 为同构，没有自由选择不同锥或新增g核性质。该商塔按全部整数索引；实际Adams负滤过层恒为全群，自然数子塔共尾，所以仍是已批准的完备条件。`hYfinite`依然量化全部d及自然数n，`hZsep`仍是同一实际目标滤过交为0；hexact和逐页ClassicalPermanent及结论完全保留。实际binder顺序是f、g、三个自然条件、hexact；这只是明确调用顺序，不扩大授权语义。

JSON中的实际type fingerprint为 `360519681979022276`，宇宙仍为u/v/w。249项闭包没有Standard声明；独立读取未见2.20反向调用自身、Main不相容结果或其他目标形成循环。广泛import的环境中有其他未完成责任，不等于本root实际闭包依赖它们；本次检查追踪的是具体type/body依赖。

以上结果不提升谱级反例候选为Lean构造的完整Model证书，也不证明每个Standard对象满足新增自然条件；原文全局条件到具体形式化Standard实现的来源边界仍如上。完整项目检查由协调者统一安排，报告状态与人类授权范围不变。

## 人类审核记录

2026-10-19，当前session用户明确回复：

> 第一项和第三项同意，现在就可以改；并行地，交给一个 subagent 这个任务：第二项因为涉及到修改原来的自然语言，需要给一个具体的 pdf ，讲清楚原命题是什么，反例是什么，应该改成什么样子，发到 project-math-assistant

出处：协调者 `/root` 在本session后续派工消息转发的真实用户原话；编号映射是第一项2.20、第三项5.14、第二项5.10。本报告仅记录第一项授权：添加上文 `hYcomplete`、`hYfinite`、`hZseparated`，保持原hexact、逐页ClassicalPermanent及结论，补完证明并同步既有接口/责任/测试，不新增sorry。其他项各自报告，不把5.10的说明/PDF请求解释成其statement修改授权。

状态为 `approved-interface-change`。这不表示实现已完成、Standard的条件已无待补来源依赖或全仓检查已通过。实施及统一验证由协调者继续安排。旧报告2026-10-18的保留statement授权仅作为历史保存；本条新的明确授权在上述限定范围内取代旧限制。
