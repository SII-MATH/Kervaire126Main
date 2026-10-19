---
title: 命题 6.20 固定原目标与 b = 0
archived_from: local-history/metadata/interface-reviews/ProofTools/20261017-prop620-fixed-target-bzero/report.md
archived_sha256: 0a56d86efcdbebefa92433b35db6418b32b03a8342ca42513cd7b08a2004a156
summary: "固定原目标与非提升源必要性存在数学反例；证据是实际谱上的数学论证，未给出固定 Lean 模型的形式化反例。"
issue_id: "20261017-prop620-fixed-target-bzero"
responsibility_module: "ProofTools"
targets:
  - "AimPaper Proposition 6.20, second clause, fixed-original-y and b=0 interpretation"
  - "Unproved nonliftable-leading-source necessity"
baseline_commit: "aad718722aa01dfce361f40645fc776037d1078f"
worktree: "/inspire/hdd/global_user/czxs25250150/Kervaire126Main"
candidate_source_commit: "uncommitted evidence, snapshots in evidence/baseline.json"
api_file_and_sha256: "metadata/proof-tools-api.json: 12e126b3d07992712555dc5ea0bde9c0afbbd2cdbdb3112adaad190edb64cb5f"
source_file_and_sha256: "KIP126/ProofTools/Paper/ExtensionDescent.lean: e9094c45e638242ae998b81fb8a8d69383384db793998393b032ef2542a33a95"
reporter_agent: "/root/prop620_bzero_report"
independent_of_discoverer_and_implementer: true
evidence_level: "paper-level actual-spectrum counterexample to the fixed-y/nonliftable-source necessity, based on standard synthetic comparison theorems; independently checked Lean coefficient/quotient/exact-target lemmas; not a formalized fixed-Lean-model counterexample"
status: pending-human-review
human_decision: null
---

# 接口调整人审报告：6.20 固定原目标与 b=0

## 请求人类决定的具体问题

**已公开的合法页下降定理没有发现新问题，保持不动。争议只涉及尚未公开、尚未完成的第二段完整等价式。**

王老师在群 `project-math-assistant` 的消息 `om_x100b620395ee84a4de3f31d816bb406`（位置 1481，记录时间 2026-10-17 13:52）为“一般的b，可以推b=0”；此前意见为“y′应该是y吧？”。本轮用户要求“看下王老师在群里回复了没，有回复就按他的意见继续补证”。这些意见足以授权继续尝试证明，但不是已给出消去引理，也不是对本报告任何实质接口调整的批准。

需要确认的具体数学问题是：**在固定原目标 y、b=0 的同时，是否仍要求短扩张的首项属于原文的严格差集 Z_early \\ Z_late？** 当前的高源代表判据能保持同一个 y，但没有推出该首项必须不提升。独立逐项核验的 HZ/16 实际谱例子表明这个必要方向不能一般成立。

建议先保留当前公开接口，继续核实下述目标保持消去引理；若要改变第二段的语义，应明确选择：

1. 保留原文严格差集的必要性，并提供/补证把可提升首项消去后仍命中原 y 的步骤；本报告的实际谱反例反对该引理在当前一般前提下成立。
2. 先采用已证明的“同一 y 的实际高源代表”精确判据，暂不声称它等价于存在不提升首项；这是第二段结论的实质改变，不能冒称原命题已补齐。

本报告没有应用任一方案，没有改生产源码、锁、memo 或待补记录，也没有向飞书发送消息。

## 原接口、背景与问题成因

### 原文完整数学声明

来源：`AimPaper/main.tex:1981–1993`，标签 `prop:dec738d3`。

设 e=e(f)，有 (f,E_r)-extension d_n(x)=y，

- x ∈ Z_(r−1)^(s,t)(X)；
- y ∈ Z_(r−1−n+e)^(s+n,t+n)(Y)。

第一段原文说对所有 2≤r′<r 仍有 (f,E_r′)-extension d_n(x)=y。已批准的范围修正是再要求 n≤r′−2+e；下文全部采用这个修正，且原扩张给出 e≤n。

第二段原文：若晚页扩张 essential 且 n≤r′−2+e，则早页扩张 inessential 当且仅当存在

- 0<a′≤n−e；
- x′ ∈ Z_(r′−1−a′)^(s+a′,t+a′)(X) \\ Z_(r−1−a′)^(s+a′,t+a′)(X)；
- b≥0；

使得

    d_(n−a′−b)^(fhat_(r′−1))(λ^a′ x′) = λ^(n−b−e) y′.

原文没有完整量化 y′、规定其分次和与 y 的关系。故原文本身不能不加解释就转成一个完整 Lean 类型。固定原 y 时，分次约束迫使 b=0；这一分次事实不能代替存在性证明。

### 已存在公共 Lean 声明及其完整参数

`KIP126.ProofTools.Paper.finiteExtension_descends` 位于 `KIP126/ProofTools/Paper/ExtensionDescent.lean:83`，以固定 `KIP126.AdamsSynthetic.Standard.model` 为模型：

```lean
public theorem finiteExtension_descends
    (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient model X (s,t))
    (y : Ambient model Y (s+n,t+n))
    (hr : 2 ≤ rEarlier) (hle : rEarlier ≤ rLater)
    (hnUpper : n ≤ (rEarlier : ℤ) - 2 +
      normalizedExponent model.classicalTower f)
    (h : FiniteExtension model X Y f rLater n s t x y) :
    FiniteExtension model X Y f rEarlier n s t x y
```

这里没有省略此声明的额外隐式数学参数；所用范畴与实例来自固定 Standard 系统，完整 elaborated 类型、universe、axiom 项已另存 `evidence/public-descent-api.json`。`hle` 包含相同页，是自然性的有效加强；未改源、靶、实际 f 或代表标签。

当前**没有**第二段 iff 的已登记公共 Lean 声明。不能将新争议说成已存在冻结定理被本报告形式化反驳。

`FiniteExtensionWitness` 的全部条件已核对：page_ge_two、length_lower、length_upper、source_cycle、target_cycle；实际有限商 E∞ 的 source/target；通过 `finiteSourceForExtension`、`finiteTargetForExtension` 的两个 HasInfinityRepresentative；同一个 `finiteExtensionMap`、分次 `(t−s,t+e)` 下的 `TowerExtensionEquation`。Essential 使用这一实际 filtered map 的不定性，而非仅仅 y≠0。没有把任意过滤方块当成此固定对象的实现。

### 问题类型

- 合法页范围遗漏已解决，与本争议分开。
- 固定 y 后 b 的分次问题已解决为 b=0，但完整必要方向尚未证成。
- 存在不提升的**整体实际修正**与该修正的**首个关联分次类不提升**是不同结论。
- 本报告独立核对实际谱、指定映射、νδ/ρ和滤过识别后，认为它构成固定原y、b=0、保留严格非提升首项必要方向的**纸面实际谱反例**。这一数学判断使用论文已引用的标准synthetic比较定理及HZ Adams计算；未编码不是数学识别的附加假设。
- 它不是当前固定Lean对象中的已形式化反例，也不反驳已证第一段、任意未定型的general-b/y′版本或论文主定理。原印刷general-b版本还需要先补齐y′的量化和目标关联，不能由本报告擅自定义其含义。

## 真实前提与对象核对

候选取 E=Hℤ₂^∧、M=E/16，标准三角 E --16→ E → M --δ→ ΣE：

    X = ΣE_x ⊕ ΣE_u ⊕ M,
    Y = ΣE_z ⊕ ΣE_y0,
    f(x)=8y0, f(u)=2z, f|M=(δ,2δ).

参数为 e=0、r′=5、r=7、n=3、(s,t)=(0,1)，原目标 y=h₀³y0 ∈ Ext^(3,4)(Y)。

| 前提或对象条件 | 是否满足 | 独立核查与局限 |
| --- | --- | --- |
| 实际谱和实际映射 | 数学构造明确 | HZ/16 的连接映射及有限直和给出具体 f；不是仅指定矩阵而没有谱映射。当前 Lean 未构造这些对象。 |
| connective、2-complete、finite type | 已核对 | 取2-completed HZ、HZ16及有限直和，逐度mod2同调有限，满足原文main.tex:255全局约定及强收敛。 |
| 范围 2≤r′<r、e≤n≤r′−2+e | 已检查 | 2≤5<7、0≤3≤3，Lean 算术通过。 |
| AF(f)=0、e(f)=0 | 数学上核对支持 | δ 在 mod-2 同调上非零，而 16 和 2 的同调映射为零；δ 是实际连接。尚未在固定 Lean Model 内识别。 |
| 原 x 的晚页循环条件 | 数学上满足 | x 为 ΣHZ 的永久 h₀-tower 首类。 |
| 原 y 的目标循环条件 | 数学上满足 | Y 的两条 HZ tower 永久，因而满足全部所需目标循环。 |
| M 的 Ext 与 d₄ | 有直接一手依据 | May–Milgram Lemma 3(ii)(iii)、Lemma 4，见下文；不依赖 6.20。 |
| νM 的归一化三角以及箭头 νδ | 逐项数学核查，未形式化 | 使用 AimPaper `not:fhat` 和紧随的三角，e(16)=1、e(ι)=e(δ)=0；不把任意 cofiber 同构当成指定连接。 |
| ρ 与连接坐标的兼容 | 由同一三角自然性推导 | Q₆→Q₄ 在连接像中是模16约化；未在 Lean 对此 HZ 对象构造。 |
| Adams 滤过与系数整除性的对应 | 纸面已逐项核对，Lean未编码 | 单h₀ tower、2的检测、有限strip公式及δ在各存活关联分次的单射，逐级反射有限滤过；不是裸群同构。 |
| 晚 essential、早 inessential | 纸面实际谱已核对，有限系数已穷举 | 检查全部高源修正而非只查目标非零；由前述指定坐标和滤过识别把算术结论应用于实际谱。 |
| 全部 0<a′≤3 的非提升首项 | 模型中穷尽 | 差集只在 a′=1,2 非空；二者的 z 首项无法进入目标 F³；a′=3 两边循环组相同。 |
| 属于当前固定 ClassicalObject | **未满足** | Configuration.lean:28 只有 sphere、nuCofiber、detector 和 shifts，没有 HZ、HZ16、这些有限直和或已证等价。不能擅改 detector 或 auxiliary 来冒充固定对象。 |

### 一手来源与 synthetic 识别的独立推导

已于本轮直接读取并查看 [May–Milgram, The Bockstein and the Adams Spectral Sequences, p.129, Lemma 3/4](https://math.uchicago.edu/~may/PAPERS/34.pdf)。该来源支持：HZ 为单条永久 h₀ spike；HZ/2^k 有两条 spike 以及 d_k；有限楔和按直和计算。以 HZ 的 2-completion 工作保留相同 HF₂-Adams 数据，不据此擅自套用该文其他需要 integral finite type 的定理。

独立检查的 synthetic 路线为：

1. HZ 的单 tower 加上乘2由h₀检测，给出 λh₀=2。固定相关 weight 的 π₀ 是无 λ-torsion 的 ℤ₂ tower；其他 stem 没有额外关联分次项。这里需要强收敛与滤过分离，不仅是给 E₂ 作命名。
2. e(16)=1；连接与包含的 mod2 同调映射非零，e=0。由归一化三角得到

       Σ^(0,1)νE --widehat16→ νE → νM --νδ→ Σ^(1,1)νE.

   `λ widehat16=16`，在所需无torsion坐标中 widehat16 的系数是8，而不是16。没有使用全局唯一除 λ 的假设。
3. Q_q 是 λ^q 的 cofiber，作为固定张量保持三角。νE 上 λ^q 在相关坐标单射、系数2^q，故 Q_q 的相关 π₀ 是 ℤ/2^q，相关 π₁ 为0。上述三角长正合列因此把

       π_(1,1) Q_qνM --νδ→ ℤ/2^q

   **注入地**识别为 K_q=ker(8:ℤ/2^q→ℤ/2^q)。得到 K₄=2ℤ/16、K₆=8ℤ/64。
4. 商约化与指定 νδ 交换，所以 K₆→K₄ 是通常约化，像为8ℤ/16。不是任意选择的同构。
5. finite E∞ strip 公式给出源 h₀^a v 在 q 商存活 iff a+3≥q。早商 q4 与晚商 q6 的差集在 1≤a≤3 中恰为 a=1,2。δ 的关联分次映射由实际 mod2 映射确定，故这两处非提升首项的 v 系数分别有精确2-adic阶1、2；不能被同滤过 u 项经过乘2后的更高阶 z 系数消去。

第5步的滤过兼容不是额外的strictness假设：δ在有限strip的每个存活关联分次上是h₀-tower的单射。若δ(c)属于更高目标滤过，首个非零源分次的像也必须为零，违反该单射；有限逐层反射直到strip末端即得c属于同级源滤过。反向包含由映射保滤过给出。如此确定K坐标中完整滤过，排除了仅计算群而遗漏hidden filtration的可能。

以上路线核对了指定实际谱到系数群、δ、ρ、f与全部相关滤过，没有剩余“任意方块也许不能实现为谱”的数学识别假设。它构成纸面实际谱反例。当前没有HZ对象和这些比较的Lean构造，只限制其形式化完成程度，不能据此把已经论证的纸面数学降成条件性猜想。复核结论与后来交付的旧目录`evidence/wang-bzero-audit.md`一致；本报告已自行读取原文、来源、三角和实际系数并复跑独立穷举，而非以该报告批准代替核查。

## 独立证据与复现

### 证据 1：九条算术引理

同目录快照 `evidence/WangBzeroProof.lean`。

    lake env lean metadata/interface-reviews/ProofTools/20261017-prop620-fixed-target-bzero/evidence/WangBzeroProof.lean

实际复跑 exit 0。`#print axioms` 全部至多 propext、Classical.choice、Quot.sound，无 sorryAx。该文件**仅**证明整数整除/奇偶、窗口及合法长度，不证明实际谱识别。

### 证据 2：循环差集与商映射像

`evidence/WangBzeroAudit.lean` 的两条引理独立复跑 exit 0，同样无 sorryAx。它先在同一分母 B 下证明

    [x] ∈ range(L/B → E/B) ↔ x∈L, 其中 B≤L≤E，

再专门化到真实 `Literature.cycles`、`boundaries`。这排除了“代表只在边界意义下不提升，而非真正循环差集”的偷换：同一分母且边界已属于晚循环时，两者等价。它没有构造 HZ 的循环子群。

### 证据 3：独立穷举有限 filtered-group 模型

运行：

    python3 metadata/interface-reviews/ProofTools/20261017-prop620-fixed-target-bzero/evidence/check_finite_model.py

脚本在 A_q=(ℤ/2^q)²⊕K_q、B_q=(ℤ/2^q)² 上，采用每坐标的2-adic滤过和同一个映射

    (x,u,v) ↦ (2u+v, 8x+2v) = (z,y0)

穷举全部源元素。实际 exit 0、输出：

    early F1 fixed-target witnesses: 32
    late F1 fixed-target witnesses: 0
    a=1: nonlift leading witnesses 256, images in target F3 0
    a=2: nonlift leading witnesses 32, images in target F3 0
    a=3: early and late leading cycle groups agree

原 x=(1,0,0) 映到(0,8)。早商的高源修正(0,−2,4)也映到(0,8)。晚商任意F¹源的 y0 坐标为16的倍数，不能代表目标F³/F⁴中的8。非提升首项a=1,2的v坐标具有精确阶a，其z像不可能在F³，因而不能命中固定原目标；这是对全部允许a的检查，不是挑一个代表失败。

脚本本身只证明有限filtered-group计算。上节另行提供实际谱、ν/δ/ρ/滤过的纸面识别，所以整体证据支持纸面实际谱反例；脚本与9条Lean算术单独均不够。这仍不是当前Lean固定对象反例。

### 证据 4：固定目标的真实判据已证明

`evidence/WangBzeroExactTarget.lean` 独立复跑 exit 0，五条主要定理全部只有基础逻辑公理。核心完整泛型签名如下，其中 Acat 为 Abelian category，F/G 为真实 filtrations，f 为其 filtered morphism：

```lean
universe u v w
variable {Acat : Type u} [Category.{v} Acat] [Abelian Acat]
  {ι : Type w} {A B : ι → Acat} {F : Filtration A} {G : Filtration B}

 theorem inessential_iff_zero_source_same_target
    (f : FilteredMorphism F G) (k : ι) (s n : ℤ) {T : Acat}
    (x : T ⟶ F.associatedGraded s k)
    (y : T ⟶ G.associatedGraded (s+n) k)
    (h : FilteredMapExtension.Relation f k s n x y) :
    ¬ FilteredMapExtension.Essential f k s n x y ↔
      FilteredMapExtension.Relation f k s n 0 y
```

证明由已知 h 与零目标/零源关系相减得到，保持同一 map、分次和 y；再由 `mem_indeterminacy_iff` 得到 F^(s+1) 的实际源代表命中同一 y 的版本；并专门化到实际 synthetic tower 和 `FiniteExtensionWitness D ...`。不能删除已知扩张方程h，也不能把这个判据叫作已经找到不提升的首项。

### 依赖与循环审计

- 对三份证据实际执行了 `#print axioms`；这些参数化定理没有借用 Standard.model 的待构造项，没有 sorryAx，无目标自身、6.20第二段、7章结论或从矛盾消去的依赖。
- Python 脚本无项目输入依赖，仅基础整数/穷举；不证明谱识别。
- 来源支持只用 HZ/HZ16 的独立 ASS、归一化三角和有限 E∞ strip，不使用6.20或由它推出的6.21，因而未发现循环。
- 已公开下降定理使用 Standard 模型和 Literature 的既有未证上游责任。本报告没有重新证明那些对象，也不把该定理“局部证明完成”误说成整条标准系统无待补。
- 证据首次默认沙箱运行因 `could not detect the configuration of the Lake installation` exit1；随后申请运行相同只读Lean命令获准，三份最终复跑均exit0。没有输出 `.olean`，没有写生产构建缓存。失败和成功日志均保留，未隐去。
- 本报告只新增审查证据，未改生产代码，因此没有重跑整个lake build；不把局部检查声称为本轮全仓新构建通过。

## 方案及精确差异

### 优先方案：保留接口，补真实目标保持引理

记早页实际修正为 δ∈F_early^(s+1)，g_early(δ) 在目标关联分次中等于原y。晚页 essential 加目标有限范围 graded单射，可以尝试证明整个δ不在ρ_X(F_late^(s+1))中。这一步与候选不矛盾：候选中δ=−2u+4v整体不提升，但它的首项−2u提升。

**准确缺失引理**：在上述完整实际商方块、长度范围及原晚页 essential 条件下，能否从任一这样δ构造 δ′，其首个非零关联分次类不在晚页ρ_X的像，同时 g_early(δ′) 仍有精确原目标y作为首项。

不得只证明整体δ不提升，或只证明某个非提升首项命中不相关y′。消去可提升首项ε时，g(δ−ρε)=gδ−ρgε；若gε在较低目标滤过非零，就改变了当前目标。在有限模型中正有这种抵消：−2u的−4z与4v的4z+8y0抵消后才得到8y0。后续v首项本身命中z，不能单独命中y。这是现有内部方案的具体障碍。

这个障碍由上面的实际谱例子实现，因此在同一一般前提下，不能继续把该强必要方向当作一个仅待技术消去即可证明的事实。若希望保留它，需要说明排除该例子的额外真实前提，或重新澄清目标和差集的解释；新增前提是接口语义改变，不能冒称内部补证。

### 候选 A：固定 y、b=0，保留严格差集

原纸面第二段为未量化y′的“早inessential iff ∃a′,x′,b≥0,短扩张到y′”。候选精确数学式是：

    原前提 ∧ 晚essential ⇒
    [早inessential ↔ ∃0<a≤n−e,
       x′∈Z_(r′−1−a)^(s+a,t+a) \\ Z_(r−1−a)^(s+a,t+a),
       d_(n−a)^(fhat_(r′−1))(λ^a x′)=λ^(n−e)y].

它固定对象和目标、删除b；比只存在较低目标 crossing 的条件更强。当前并无已公开原Lean签名可机械替换；若要公开，需先给出真正完整类型并证明上述缺失方向。九条算术和分次相容性都不能完成它。本报告不建议直接登记为已证。

### 候选 B：公开精确高源代表判据，继续保留完整crossing任务

采用证据4已证明的同一filtered-map签名，或其实际 finite witness 专门化，说明

    ¬W.Essential ↔ 同一TowerExtensionEquation(..., source=0, target=W.target).

等价的实际代表形式保留F^(s+1)源和同一y。它没有要求首项严格不提升，因而没有完成原第二段的crossing等价。它不把证明责任转给Main或其他下游，也不新增axiom。是否新增公共声明及其命名/锁/契约由协调者按用户授权范围处理；本报告不实施。

### 不采用的修复

不把HZ对象偷偷等同于当前detector；不扩展ClassicalObject绕开接口冻结；不增加“目标保持消去”公理；不把严格差集改成整体修正不提升却仍标原6.20完成；不使用6.21来反证6.20而形成循环。

## 下游影响

| 项目 | 当前影响与后续要求 |
| --- | --- |
| `ProofTools.Paper.finiteExtension_descends` | 不受影响；名称/类型/锁/源与靶保持。 |
| 6.20完整第二段 | 仅此未完成目标的必要方向受阻；尚无生产公共声明需撤回。 |
| 原文6.21 | 原文说为6.20第二段逆否；若未来依赖完整crossing等价，须独立证明或等待澄清，不能自动升级状态。 |
| 已登记Main/ProofTools代码 | 本轮未发现调用这个未存在声明的生产依赖；不能因此冻结整个Main或否定主定理。 |
| API/契约/来源 | 现有记录明确仅第一段已公开。若新增精确判据需新增正确来源范围，不能把第二段标完整。 |
| 待补清单 | 本报告不新增责任、不改变既有条目；未证目标继续如实记录。 |
| 测试 | 若以后整合方案，增加普通导入的同目标公共消费并运行source inventory和lake build；不删除现有边界覆盖。 |
| Memo和外发 | 交协调者在确认后如实更新；本报告无相应写入/发布授权。 |

## 阻塞范围与继续项

准确阻塞：固定原y、b=0、严格非提升首项的**必要方向**，以及任何必须依赖该必要方向的后续结论。

可继续：合法页自然性；已证固定目标零源/高源代表判据的正常整合；有限目标滤过反射和“整体修正不可提升”的局部证明；HZ/16纸面谱反例进一步外部核阅或独立形式化（对象范围须另行授权）；其他不依赖完整6.20第二段的论文接口证明。

不能把纸面广义谱反例当成已经在Lean中正式反驳固定Standard接口的证据；也不能因为用户希望继续补证，就把未完成的消去步骤或群中一句建议当成证明。

## 人类审核记录

尚无针对本报告、候选A/B及其具体范围的人类决定。`human_decision: null` 保持。

群内原话及用户本轮指令仅作为本次研究背景，真实出处见旧目录 `wang-bzero-feedback.json`；没有把它们填写成对本报告的批准。

### 2026-10-17 群内后续：PDF 与 Adams 图

王老师 14:20 UTC 回复反例消息，要求“这个输出pdf，画相应的adams chart”。已完成四页 A4 PDF，包含经典 Adams 图、固定 weight 1 的早晚页 ESS 图、全部不定性计算及候选条件问题；14:31 UTC 发群并回读核验。材料、复现步骤和视觉 QA 见 [presentation/README.md](presentation/README.md)。图的每条非零箭头另经独立审查与有限枚举核验。

最终回读尚无新的数学条件修改，故没有继续尝试证明已被反例阻断的强必要方向，也没有擅自选择候选 A/B；完整第二段状态与 `human_decision: null` 保持。PDF 请求仅决定审阅材料形式。

### 2026-10-17 14:40 UTC 群内后续：明确是哪条 f-extension

王老师询问“所以究竟是哪个的f estension”，尚未给出修改非提升源条件的数学决定。已核对原文定义5.4与6.20，回复同一个谱映射

    f : ΣE_x ⊕ ΣE_u ⊕ H(ℤ/16) → ΣE_z ⊕ ΣE_y0,
    f = [[0, 2, δ], [8, 0, 2δ]],  E=Hℤ₂^∧,

的两条扩张 `d₃^(f,E₇)(x)=h₀³y0`（essential）与 `d₃^(f,E₅)(x)=h₀³y0`（inessential）。其 synthetic 表述分别是同一个 `νf` 的模 `λ⁶` 与模 `λ⁴` 扩张，目标都是 `λ³h₀³y0`；早商中短扩张 `d₂^(fhat₄)(λh₀u)=λ³h₀³y0` 使后者 inessential。并明确 PDF 的经典 d4 仅用于源 cycle 差集计算。

原回复及取回信息见 `evidence/wang-which-f-feedback.json`，外发全文见 `evidence/group-which-f-reply.txt`，发送回执见 `evidence/group-which-f-send-response.json`。此次澄清没有改变生产接口、证明前提或未完成状态；不把疑问当作对任一修正条件的批准。

### 2026-10-17 14:55 UTC 群内后续：短微分与一般 b 见证

王老师指出“这个例子，早页的inessential不是被短diff命中了吗”。已回应确认：早商的 essential 短微分是 `d₂^(fhat₄)(λh₀u)=λ³h₀³y0`，其源首项可提升，但晚页先有 `d₁^(fhat₆)(λh₀u)=λ²h₀²z`，故该短微分并非晚页同长度微分的像。

本例允许按原文第二种情形向较低目标迭代：取 `a′=2,b=1,x′=h₀²v,y′=h₀²z`，则 `x′∈Z₂^(2,3)\Z₄^(2,3)`，且 `d₀^(fhat₄)(λ²h₀²v)=λ²h₀²z`。与 `presentation/chart-checks.json` 中 q4 的源 v、滤过2、essential d0 箭头一致，实际坐标 `(0,0,4)` 映到 `(4,8)`，首项为 `(4,0)`。参数 `n−a′−b=0` 合法，目标 `y′` 永久。这是此特定例子的一般 b 必要方向见证，不是该必要方向的普遍证明，也不证明完整 iff。

已在回复中明确本例不反驳允许较低目标的一般 b 必要方向，并询问应保留该较低目标还是另有保持原目标的处理。原回复、外发全文与回执分别为 `evidence/wang-short-differential-feedback.json`、`group-short-differential-reply.txt`、`group-short-differential-send-response.json`。生产接口及 `human_decision: null` 保持；未擅自把未量化 y′ 解释成任意无关目标。

### 2026-10-17 15:02 UTC 群内后续：固定 y、b=0 的确切障碍

王老师追问“所以固定y，b=0究竟哪里不对”。已组织独立、针对性的定义审查，并逐项复核所有允许的源，见 [evidence/fixed-y-bzero-final-audit.md](evidence/fixed-y-bzero-final-audit.md)。复核没有要求早页短方程在晚页存在：全部排除发生在早页 ESS。a′=1/2 的差集源必含 v 首项，其 d0 命中非零 z；同次混合及任意高源修正均不能改变这一点。a′=3 差集空。原文第2节的记号约定要求源存活，即使靶余类为零也不能省略；因此不能把 inessential 理解为允许已被 d0 杀掉的源任意支持更高微分。

已将上述完整候选排除回复到群中，明确短原目标扩张的存在与其首项属于非提升差集是两个不能同时满足的要求，并请作者核对早页 d0／差集计算。问题原话见 `evidence/wang-fixed-y-question.json`，外发全文及回读见 `group-fixed-y-careful-reply.txt`、`group-fixed-y-careful-receipt.json`。未修改生产声明或未完成状态。

## 后续授权修正版（删除差集）已完成

王老师随后明确要求“把差集条件先去掉”，用户授权依此继续并记入memo。固定原y、b=0、保留早循环及同早商的修正版，现已由 `KIP126.ProofTools.Paper.finiteExtension_inessential_iff_shorter` 补证并公开，全仓构建通过3088 jobs。见 [新范围报告](../20261017-prop620-remove-difference/report.md) 和 [验证](../20261017-prop620-remove-difference/validation.json)。本报告此前的含差集版本分析作为历史依据保留，不据此阻塞已获授权的修正版；也不将原含差集版本改记为已证。
