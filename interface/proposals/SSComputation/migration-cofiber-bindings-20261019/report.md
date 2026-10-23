---
issue_id: AdamsCalculations-migration-cofiber-bindings-20261019
title: Cν 旧坐标证明到固定 bottom 与 topCell 的内部连接
summary: cofiber_target_to_e6 已在原接口下生产补证，当前上游产物的整文件检查通过；最终API核对与默认完整构建通过，独立实际依赖审计通过并保留登记上游。cofiber_d3 仍待补，不请求接口修改。
responsibility_module: SSComputation
targets:
  - KIP126.Computation.Standard.cofiber_d3
  - KIP126.Computation.Standard.cofiber_target_to_e6
baseline_commit: ef01dcfd904b51fe2288f0dc3e1eed074591967f
worktree: /inspire/hdd/global_user/czxs25250150/ops/tmp/main-followup-20261019
candidate_source_commit: 71e63c47d1be7ebad1589bd08a598179e468f23b
api_file_and_sha256: interface/baselines/adams-calculations-api.json 69729c4a1e57c1bbf0e7c81606ffc53a2f0430f3b1869b41dc35fb7a8431443f
source_file_and_sha256: KIP126/AdamsCalculations/Standard.lean 58c34f82bb4f9ca30176f815be15ba045f8a9b1b4462d4b44258e7cfa39f98ab
baseline_source_file_and_sha256: KIP126/AdamsCalculations/Standard.lean c11c5482d79dedc6352fa25a72ef74e14727d4e54118dc26d2b03d579f42bd23
reporter_agent: /root/interface_report
independent_of_discoverer_and_implementer: true
evidence_level: 独立源码与完整前提核验；完整E6生存证明已生产集成、当前无overlay整文件检查退出0；最终公共API、默认完整构建与独立实际依赖审计通过并保留登记上游，无实际Cν反例
status: pending-human-review
human_decision: null
blocking: cofiber_d3 仍需实际源靶/非零E3桥；cofiber_target_to_e6 已补到同一E6代表非零，完整构建与实际依赖审计通过；登记上游责任保留。
resolution: E6生存通过同一首商正合性、有限基数与微分自然性内部证明完成，不要求新增坐标接口；d3继续原对象内部连接，不改变模块责任。
---

# Cν 固定类迁移审查报告

## 请求人类决定的具体问题

当前不请求新的权限或公共接口变更。用户已经要求“把这些迁移回来，保持公共接口不变”。独立审查确认的是旧坐标证明向固定类的迁移仍有内部桥接责任；尚无实际反例，没有证明既有 API 必须修改。报告状态按协议保持 `pending-human-review`，并不冻结固定接口补证。

Blueprint 的约定为 mod-two Adams 页，`(s,t)` 的 stem 为 `t-s`；LWX126 引用的谱条件为 2-completed、connective、finite type。既有固定模型仍是本报告对象，不以任意向量空间模型替换。

两个最终目标归 AdamsCalculations；基底、E₂ 底胞映射和顶胞 lift 的构造仍归 E2Computation。此报告放在最终目标所属模块，**不代表**把 E₂ 责任移交下游，也不要求下游重新构造固定 Adams 系统。

## 2026-10-20 路线集成阶段：完整 E₆ 生存已生产补证，最终验证通过且继承登记上游

本次状态更新由独立报告员 `/root/route_status_report` 核对。集成基线为 `ef1c6c718075659f68c6beaf0aae09937d2a4c25`；当前 `AdamsCalculations/Standard.lean` 的 SHA-256 为 `58c34f82bb4f9ca30176f815be15ba045f8a9b1b4462d4b44258e7cfa39f98ab`。报告员独立逐字比较两个公共目标的完整源码类型，与基线相同。`cofiber_target_to_e6` 的直接 `sorry` 已替换为私有证明调用，`cofiber_d3` 仍保留原直接洞；实际 Cν、ν 映射、bottom、指定 topCell、Y、T 以及模块责任均未改变。

完整新证明绕开了旧坐标绑定。它从 `normalized_finite_quotient_horizontal_row` 的真实首商 distinguished triangle，对同一 `nuRouteTriangle`、指数和、原三角与正商长度逐项应用正合性。经固定首商/移位比较，相关三项 Hom 群基数分别为 **8、16、至多2**。中间正合性给第一箭头像等于第二箭头核；核基数至少8且是8元源群的满像，故第一箭头单射。再通过已证首商自然性，将这一单射性运输到**字面上的实际 bottom E₂ 映射**，没有换 cofiber、映射或基底，也不需先标定 Qν=h₂。

随后沿实际 inclusion 运输球谱 d₂ 行，借 bottom 单射及 Cν 已登记的完整 d₂ 像，识别该像的非零基方向；用同一球谱 T 的既有边界避让排除 bottom(T) 被 d₂ 击中。已有永久代表沿 actual bottom 给出同一 E₆ 代表存在，再分别排除 d₃、d₄、d₅ 的 incoming，将同一代表的非零保持到 E₆。结论恰是原 **`SurvivesTo nuCofiberSequence 6 (14,139) (bottom 14 139 T)`**，不再只是 `ReachesPage`。此路线不借 G89、h₂ 非整除、`cofiber_d3`、Y 或 Main 的目标后果。

报告员独立读取上述生产证明、基数引理及末尾同一代表链条；读取了 worker/两位审查员的证据和协调者当前无 overlay 的整文件检查日志，日志无 error，协调者记录退出0。整文件副本与生产源码 SHA 相同，实际核验摘要为本地 `cofiber-current-integration.json`。此前旧匹配 overlay 的探针及源码/依赖审计仅作为早期预检保留，不冒充当前产物检查。报告员未亲自编译，实际当前产物检查由协调者执行。

当前状态为 **`resolved-by-fixed-interface-proof`**。包含全部十一项的八数学入口构建、八模块完整公开捕获、原214项 kernel 表达式核对及默认完整 `lake build` 均已通过；清单现为203。独立实际十一目标依赖审计已通过并保留登记上游，准确范围见下节。首商、范畴、比较、cofiber基底和 `Table.result` 等已登记传递责任持续保留，不能将本地目标完成称为全证明信任闭合。

`cofiber_d3` 的固定源靶代表及 E₃ 靶非零尚未完成。正在研究的另一次数正合性/矩阵秩路线不能仅凭非零或维数确定指定 topCell 的唯一坐标；本报告不将其标为已证明，也不请求接口变更。证据摘要见 [本轮证据](evidence/reassessment-20261020.json)。大型日志保留于 Git 忽略的本地会话目录，不伪造网页链接。

### 本轮最终捕获、清单与完整构建通过

本轮最终公开捕获和清单核对现已完成：八个数学入口普通导入后的全部导出、完整渲染类型、宇宙参数及实际定义源模块均与原基线精确相同，八份 API 锁文件逐字节不变。报告员独立比较了八份锁与 `ef1c6c7`；实际捕获和原214项 kernel 表达式比对由协调者执行，报告员读取其结果。原214项完整 kernel 类型全相同，恰好11项直接责任完成；其余43项仅 Lean 的诊断 sorry 标签变化，经完整表达式解析比较后才刷新证明体指纹，其余待补字段未改。清单现为 **203**（AdamsCalculations 5、AdamsSynthetic 72、E2Computation 15、Literature 110、ProofTools 1；133项证明、70项构造）。本地责任完成仍继承登记上游，不能称为无 `sorryAx` 闭合。

包含全部十一项的八数学入口构建已通过3436任务；源码清单核验554个项目文件及35个消费/审计文件，依赖方向和私有导入边界通过。默认完整 `lake build` 已实际退出0，以 **`Build completed successfully (3580 jobs).`** 结束，全部既有消费、八模块信任审计、`Tests.Trust`、Main 公开根/ProofTools边界/Nu9回归均保留并通过。该构建由协调者执行，报告员独立读取最终成功日志；独立实际十一目标闭包随后已通过，准确范围见下一节。准确摘要见本报告既有证据 JSON；大型当前日志为 Git 忽略的本地会话材料。

### 本轮独立实际依赖闭包终验通过

独立证明审计员使用本轮当前已构建产物的全源码正文 collector，实际退出0，捕获 **8442** 个项目常量和本轮全部 **11** 个目标；随后按最终203项清单的 analyzer 全通过。报告员实际读取并逐项核对 `closure-summary.json`、`closure-summary.log`、`project-dependency-cycle-check.json` 与 collector 日志，没有重跑审计，也没有用旧 overlay 预检代替此次结果。

十一项完整 kernel 类型表达式、类型指纹、宇宙、公开导出及实际源模块责任与原基线相同，十一项本地直接洞均已消除。全部可达直接洞同时在原214项和当前203项清单登记，完整类型原样；真实项目公理、synthetic sorry、缺失项目正文依赖、目标循环及 Main/Geometry 反向依赖均为0。完整项目依赖图8442节点全部可拓扑移除，无循环残余。

最终结论为 **`passed-with-registered-upstream-obligations`**：本地固定接口补证及其实际依赖登记通过验收，**不表示全证明的未证输入已经闭合**。同一实际闭包中，E6 生存仍继承58项登记上游、product detection 38项、bx 等价34项、六个 BHS 包装各30项、sourceReplacement flatness 6项、rel2 33项；各目标仍含 `sorryAx`。这些计数是各自可达上游集合大小，不能相加作为全仓责任数。准确摘要和当前源/证据哈希见 [本轮证据](evidence/reassessment-20261020.json)，旧阶段证据继续保留。

## 2026-10-20 盘点阶段：固定 bottom(T) 已有 E₆ 代表（历史记录）

盘点阶段未改生产源码、API 或清单，当时仍登记 214 项，上轮五项尚未提交；以下原 partial 源码与核验范围保留为历史记录。后续五项形成 `ef1c6c7` 提交，路线集成阶段状态以上节为准。当时这两个完整公共目标的直接 `sorry` 均保留，既有人审 `pending-human-review`/`human_decision: null` 不变，不请求接口变更。

已独立读取本轮 `local-history/reports/comprehensive-proof-inventory-20261020/adams-prooftools/PartialRoutes.lean`：第一个完整 partial 声明是

```lean
ReachesPage nuCofiberSequence 6 (14,139) (bottom 14 139 T)
```

它取现有 `t_permanent_cycle` 的同一球谱永久 cycle，在第六页构造代表，再沿**实际** `cofibι model.auxiliary.nuMap` 的谱序列态射传递代表。它没有用 `cofiber_target_to_e6`，没有替换实际 bottom map，也不需要先作 Cν 数值坐标识别。原 worker 的 `report.md` 与协调者记录该文件 `lake env lean`（无 `-o`）退出 0；本报告员独立读源码，但没有重跑编译，也没有可用的同名 `PartialRoutes.log`，不伪造日志。

所以此前若笼统写“连到达 E₆ 也必须先补坐标标定”，该说法应纠正。**完整 `SurvivesTo` 仍未完成**：新证明只给到达页/存在代表，不给同一 E₆ 代表非零。剩余可选路线是证明真实包含映射在该代表上非零，或证明 bottom(T) 与旧存活坐标 `[2]` 的对应，再复用旧非零边界分析；不能把 `ReachesPage` 改名当作 `SurvivesTo`，也不能分别找到无关代表而丢失同一见证要求。

`cofiber_d3` 仍需固定 `cofiberSource` 和 `bottom(Y)` 的实际代表解释及靶 E₃ 非零；旧坐标 `[0,3,4]→[3]` 的证明仍可作模板。实际元素严格相等只是一个充分方案，差值在所需页代表为零或微分为零也可研究。`comparison`、`cofiber_basis_correct`、`Table.result`、`topCell`、`top_comparison` 等已登记上游责任可按依赖方向直接调用，不要求先证明这些上游，也不恢复旧参数包。

本轮独立审计还核对：`ClassicalAdamsFamily` 给出函子、起始页和微分次数；`StructuralExactness` 的三角范畴/移位/realization 正合性本身不等于未声明的 Adams 页级 exactness 或具体 bottom-map 坐标等式。不能因对象名含 cofiber 就补入这些性质；仍可从完整塔/表示及登记接口进一步推导。连接像不能自动唯一确定 lift 是一般观察，不是固定模型反例。**未完成表示尚需证明，不表示两目标不可证明。**

准确本地来源为 Git 忽略的 `local-history/reports/comprehensive-proof-inventory-20261020/independent-review/report.md`、`six-reasons.json`，以及 `local-history/reports/comprehensive-proof-inventory-20261020/adams-prooftools/report.md`、`PartialRoutes.lean`。本报告只保存 [本轮摘要与文件哈希](evidence/reassessment-20261020.json) 和 [小型源码证据](evidence/reassessment-20261020-partial-routes.lean)；不平行复制全球盘点和其他模块候选。

盘点阶段数学输入未变，复用上轮默认完整构建和扩展审计，结论为 `passed-with-registered-upstream-obligations`；它没有消除这两个直接洞。路线集成阶段的上游输入已变化，旧构建不能充当新输入的最终验收，当前官方构建状态以上节为准。报告员只进行源码/证据复核与提案校验，没有运行全量构建、改数学源码或写共享缓存。

## 原接口、背景与问题成因

本报告员与候选发现者/实现者独立。完整检查当前实际定义、旧证书及其 `AdamsComputationTheorems` 条件，确认历史 `cnu_d3` 与 `cnu_target_through5` 是对一个带条件的解释 `I` 的推导，不能把 `I` 的条件作为已经被迁入的证明。

两个完整原签名如下，处在固定模型和范畴，无额外宇宙变量或外部参数。以下基线 `sorry` 仅作历史展示；当前 E6 目标的生产证明以上节为准：
```lean
public theorem cofiber_d3 : HasNonzeroDifferential nuCofiberSequence 3 (8,134) (11,136)
    cofiberSource (bottom 11 136 Y) := by sorry
```

```lean
public theorem cofiber_target_to_e6 :
    SurvivesTo nuCofiberSequence 6 (14,139) (bottom 14 139 T) := by sorry
```

目标中的同一个 Cν、底胞映射、指定源、Y、T 的完整定义如下：
```lean
public noncomputable abbrev nuCofiberSequence :=
  model.classical.obj (HasFunctorialCofiber.cofib model.auxiliary.nuMap)
```

```lean
public noncomputable def bottom (s t : ℤ) :
    model.classical.sphere.Page 2 (s,t) →ₗ[ℤ] nuCofiberSequence.Page 2 (s,t) :=
  (model.classical.pageMap (HasFunctorialCofiber.cofibι model.auxiliary.nuMap) 2 (s,t)).hom
```

```lean
public noncomputable def topCell : nuCofiberSequence.Page 2 (8,134) := by sorry
```

```lean
public noncomputable def cofiberSource : nuCofiberSequence.Page 2 (8,134) :=
  topCell + bottom 8 134 (atom .x_126_8_2) + bottom 8 134 (atom .x_126_8)
```

```lean
public noncomputable def Y : model.classical.sphere.Page 2 (11,136) :=
  product h0Square (atom .x_125_9_2)
```

```lean
public noncomputable def T : model.classical.sphere.Page 2 (14,139) :=
  product h1 (product (r := (13,137)) h4 (atom .x_109_12))
```

现有顶胞比较绑定连接箭头和四次指定降悬：
```lean
public theorem top_comparison :
  ∃ (a3 : (model.classical.obj (Sphere 3)).Page 2 (8,133))
    (a2 : (model.classical.obj (Sphere 2)).Page 2 (8,132))
    (a1 : (model.classical.obj (Sphere 1)).Page 2 (8,131)),
    (model.classicalSuspension (.shift 3 .sphere)).DesuspendsClass 8 134
      (model.classical.pageMap (HasFunctorialCofiber.cofibδ model.auxiliary.nuMap) 2 (8,134) topCell) a3 ∧
    (model.classicalSuspension (.shift 2 .sphere)).DesuspendsClass 8 133
      (model.classical.pageMap
        ((shiftFunctorAdd' Spectrum (2 : ℤ) 1 3 (by decide)).hom.app SphereSpectrum)
        2 (8,133) a3) a2 ∧
    (model.classicalSuspension (.shift 1 .sphere)).DesuspendsClass 8 132
      (model.classical.pageMap
        ((shiftFunctorAdd' Spectrum (1 : ℤ) 1 2 (by decide)).hom.app SphereSpectrum)
        2 (8,132) a2) a1 ∧
    (model.classicalSuspension .sphere).DesuspendsClass 8 131 a1 X := by sorry
```

现有 `basis_correct` 的结论是以下 `BasisCorrect`，当前表格微分的 `result` 结论是以下 `Statement`。这些签名完整保留：
```lean
public def BasisCorrect (d : Raw.Degree) : Prop :=
  ∃ e : Page d.spectrum d.s d.t ≃ₗ[ℤ] (Fin d.monomials.length →₀ ZMod 2),
    ∀ i, e.symm (Finsupp.single i 1) = basis d.spectrum d.s d.t i.val
```

```lean
public theorem basis_correct (d : Raw.Degree) (hd : d ∈ Raw.degrees) : BasisCorrect d := by
  rcases d with ⟨o,s,t,ms⟩
  cases o with
  | sphere =>
    have hc := basis_count ⟨.sphere,s,t,ms⟩ hd rfl
    have ht := table_degree_bound ⟨.sphere,s,t,ms⟩ hd
    dsimp only at hc ht
    change ∃ e : model.classical.sphere.Page 2 (s,t) ≃ₗ[ℤ] (Fin ms.length →₀ ZMod 2),
      ∀ i, e.symm (Finsupp.single i 1) = sphereBasis s t i.val
    rw [← hc]
    refine ⟨Standard.coordinates s t ht, ?_⟩
    intro i
    simp only [sphereBasis, dif_pos ht, dif_pos i.isLt]
  | nuCofiber => exact cofiber_basis_correct ⟨.nuCofiber,s,t,ms⟩ hd rfl
```

```lean
public def Statement (c : Raw.Claim) : Prop :=
  ∃ x, decode c.spectrum c.s c.t c.x = some x ∧
    match c.kind with
    | .reaches => ReachesPage (sequence c.spectrum) c.r (c.s,c.t) x
    | .boundaryBy => IsBoundaryBy (sequence c.spectrum) c.r (c.s,c.t) x
    | .equation => ∃ y, decode c.spectrum c.ts c.tt c.y = some y ∧
        HasDifferential (sequence c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y
    | .refutation => ∃ y, decode c.spectrum c.ts c.tt c.y = some y ∧
        ¬ HasDifferential (sequence c.spectrum) c.r (c.s,c.t) (c.ts,c.tt) x y
```

```lean
public theorem result (c : Raw.Claim) (hc : c ∈ Raw.claims) : Statement c := by
  sorry
```

`BasisCorrect` 证明给定基底的张成与独立；`Statement` 证明解码后元素的页上关系。两者均没有提及 `Standard.topCell` 或 `Standard.bottom`。因此它们并没有**直接给出**把坐标计算改写为本报告两项目标所需的命名类等式。不能仅从“表格结果存在”推断该连接已经完成。

原生数据仍保存四条底胞对应：
```lean
public def bottomMaps : List BottomMap := [
  ⟨8, 134, [3], [4]⟩,
  ⟨8, 134, [2], [3]⟩,
  ⟨11, 136, [3], [3]⟩,
  ⟨14, 139, [1], [2]⟩
]
```

基线在 `KIP126/` 内只出现这一处 `bottomMaps` 声明。历史 `71e63c4` 的 `AdamsComputationTheorems` 明确额外带有 `cofiberInclusion`、`cofiberBoundary` 字段，分别要求这些行由实际 cofiber inclusion 实现，以及**坐标 [0] 本身**经同一个连接箭头降悬到球谱坐标 [0]。当前 `top_comparison` 只控制现已指定 `topCell` 的连接像；其中没有 `Table.basis .nuCofiber 8 134 0`。这就是需要额外完成的固定 lift 识别，而不是从降悬数据自动得到的等式。

问题分类：条件性证明桥接缺口；未确认假命题、未确认错误度数/错误 Cν、未建立公共接口不可实现性。不同 lift 可能相差连接箭头的核是一般数学上的警示，**不是**当前固定对象的反例；这里没有构造满足全部固定前提且使两个目标失败的实例。

## 真实前提与对象核对

| 条件/对象 | 核对结果 | 待补或证据 |
| --- | --- | --- |
| Cν 对象与 ν 映射 | 当前两处相同 | `Table.object .nuCofiber`、`nuCofiberSequence` 均使用 `HasFunctorialCofiber.cofib model.auxiliary.nuMap` |
| 实际底胞箭头 | 已固定 | `bottom` 是同一 `cofibι` 的 E₂ 页映射，不可换成任意线性映射 |
| 完整 Cν 基底 | 已登记但未构造完 | `cofiberBasis`、`cofiber_basis_correct`；不是只给维数 |
| 球谱坐标 [1] 与 T | 已有公共 `basis_T` | 仍传递依赖源基底和比较待补 |
| Y 及源中两 Atom 的球谱坐标 | 可从既有 `basis_value`/源码表推导 | 实施应实际证明相关索引；仅同度不够 |
| 四条 bottomMap 行 | 数据存在但未见数学连接证明 | 不得把 `Raw.bottomMaps` 数据成员证明当成实际页映射等式 |
| 指定 topCell 与 Cν 坐标 [0] | 未获识别证明 | `top_comparison` 不声明此等式；连接像相同未必唯一确定 lift |
| 旧有限页证明的输入 | 明确为带条件 I | 基底、表格微分、实际 inclusion/boundary 等字段；不可恢复结果包作为新下游参数 |
| 当前有限页表格 | 已登记可消费 | `Table.result` 仍待补；其责任留 AdamsCalculations |
| 非零存活与仅到达页 | 必须区分 | 旧 `cnu_target_through5` 用边界像排除保非零；不能只取 `reaches` 行冒充 `SurvivesTo` |

## 独立证据与复现

证据等级是源码与历史条件的独立核验，**没有 Lean 反例或实际 Cν 数学反例**。本次不构建、不写共享缓存、不修改数学源码。基线源码 SHA-256 和完整相关声明见 [源码证据](evidence/source-audit.json)；旧解释条件及两个有限页证明全文片段见 [历史证据](evidence/historical-excerpts.txt)。

复现命令（仓库根目录）：

```sh
python3 interface/proposals/AdamsCalculations/migration-cofiber-bindings-20261019/evidence/reproduce.txt
```

实际结果：基线哈希匹配；对基线 `KIP126/` 的文本检查证明 `bottomMaps` 只有其数据声明。该负搜索限定于字面量使用，不能证明绝不存在一个不引用该数据名的数学推导；核对完整 `BasisCorrect`、`Statement`、`top_comparison` 的类型后，结论仅限“旧迁移步骤所需识别尚未被这些声明直接提供”。没有声称全 API 在逻辑上无法推出识别。

提案校验也已通过，见 [实际验证记录](evidence/validation.txt)。系统 Python 首次运行缺少 `hgraph`；随后复用主检出现有 Blueprint Python 环境，无安装或构建。

旧 `cnu_d3` 将三条 d₃ 坐标行相加，得到源 `[0,3,4]`、靶 `[3]`；利用完整 `(9,135)` 基底确定 d₂ 为零，保证靶在 E₃ 非零。旧 `cnu_target_through5` 对目标 Cν `[2]`：一方面证明到达远页，另一方面用完整来源基底计算 d₂ 像为 0 或目标 `[3]`，再证明页 3—5 没有新增边界，得到 E₆ 非零。它们是有效的**条件性证明路线**，本报告未重新编译这些旧文件，也不将其输入条件认作当前已完成事实。

传递依赖：当前 `cofiberBasis`、`cofiber_basis_correct`、`topCell`、`top_comparison`、`Table.result` 都列于待补清单；球谱识别还依赖 `sourceCoordinates`、`sourceBasis_values`、`comparison`、`comparison_product`。迁移完两个定理的本地证明不等于这些上游责任全部已消除。未使用两个目标自身或 Main 的 Mahowald/CofiberRigidity 后果来构造坐标连接，没有靠 `False.elim` 取证。本次未发现所审查候选路线中的必然循环；未作全仓库一致性审计。

## 方案及精确差异（旧坐标充分方案保留，E6 已由替代方案补证）

优先保留两个公开签名：候选签名就是上述原签名，前提、结论强弱、实际 Cν/ν 映射、指定 topCell、bottom 与类关联**全部差异为零**。

E₂ 内部构造需要证成下列精确等式（这里是报告内的拟议**私有引理目标**，不新增公开接口，也不是已经证明的事实）：

```lean
Table.basis .nuCofiber 8 134 0 = Standard.topCell
Standard.bottom 8 134 (Table.basis .sphere 8 134 3) =
  Table.basis .nuCofiber 8 134 4
Standard.bottom 8 134 (Table.basis .sphere 8 134 2) =
  Table.basis .nuCofiber 8 134 3
Standard.bottom 11 136 (Table.basis .sphere 11 136 3) =
  Table.basis .nuCofiber 11 136 3
Standard.bottom 14 139 (Table.basis .sphere 14 139 1) =
  Table.basis .nuCofiber 14 139 2
```

这些目标中的 `Table` 和 `Standard` 分别指 `KIP126.Computation.Table` 与 `KIP126.Computation.Standard`，数值参数取声明对应的 ℕ/ℤ 类型。四条底胞等式正对应现有数据行。加上现有球谱 `basis_value` 的命名类绑定，可将 `cofiberSource`、`bottom Y`、`bottom T` 改写为旧有限页证明使用的坐标。

内部方案：E2Computation 完成 `topCell`/`cofiberBasis` 原已指定的实际构造，证明以上等式和 `top_comparison`，或证明现有固定实现与该构造相等。AdamsCalculations 用现有 `Table.result`、`basis_correct` 接口直接移植有限页证明，不引入旧 `AdamsComputationTheorems` 参数包。E₂ 只研究实际 E₂ 输入，不得反过来依赖目标 d₃ 或 E₆ 生存来选择基底/顶胞；旧坐标标签应由独立 E₂ 识别确定。

替代方案：在实际 Cν 上用自然性、cofiber exactness、指定 lift 的结构以及现有上游事实直接证明两个目标，绕开全部坐标对应；仍需处理 lift 差异及非零存活，不能只控制连接像。若只能证明所有允许 lift 有相同所需微分，则给出明确差异项的 d₃ 消失和源代表条件，也可避免顶胞严格等式。其中 E6 生存的结构替代路线本轮已完整实现并通过当前产物局部检查，见本报告集成阶段；d3 的替代路线仍未完成。

未提出公共接口调整候选，因为没有证据显示它不可避免。把 `top_comparison` 增强为额外公开坐标绑定、把两项目标改写成坐标目标或增加“绑定存在”假设都会改变公开范围或对象语义，当前均未授权，也不是本报告建议的默认修复。

## 下游影响

| 范围 | 影响与责任 |
| --- | --- |
| E₂ 输入 | `cofiberBasis`、`cofiber_basis_correct`、`topCell`、`top_comparison` 及其私有桥归 E2Computation；不得移动到 AdamsCalculations 或 Main |
| 两个最终目标 | `AdamsCalculations/Standard.lean` 原有责任保持；E6 本地责任已固定接口解决且实际审计通过，d3 仍待补；`Table.result` 可正常消费且其上游责任保留 |
| 直接推论 | `cofiber_target_not_hit_through5` 已由 `cofiber_target_to_e6` 推出，签名无需变更 |
| Main 调用 | `Main/Internal/NuThree/Mahowald.lean` 调用 `cofiber_d3` 与 `top_comparison`；`Main/SectionSeven/CofiberRigidity.lean` 调用生存，继续保留上游依赖 |
| 记录/接口锁 | `e2-computation-api.json`、`adams-calculations-api.json` 类型与导出冻结；真实补证后只由协调者更新实际公理/待补状态，不增加结果包或假设 |
| 来源/Blueprint | 既有 Cν 表格及来源路径保留；不新建平行论文修正记录，不改 `corrections.yaml` |
| 验证 | `Tests/AdamsCalculations/SourceConsumers.lean`、E2 公共消费和依赖方向、API/Trust 审计、源码清单、`lake build`；协调者串行处理，本报告未执行 |

## 阻塞范围与继续项

仅阻塞把旧坐标证明未经固定对象改写就标作 `cofiber_d3` 已完成；E6 已有保接口完整结构证明且完整构建/实际依赖审计通过。可以独立继续有限页线性代数/边界控制引理、表格输入和基底责任、四条底胞识别与指定 topCell 的 E₂ 构造。E2 非整除的原生系数泛函路线及其他不消费此桥的任务可继续；报告等待不构成全局暂停。

已确认：对象与 ν 映射一致；原表格有四条数据行；旧证明确有 inclusion/boundary 输入；当前相关类型没有直接记录这些特定命名识别。未决：cofiber_d3 的实际源靶及 E₃ 非零，以及传递上游责任。E6 新生产证明的完整构建与独立实际依赖审计均已通过。E6 同一代表非零已由完整结构证明给出并集成，不再列为缺失数学步骤。**不以未完工判定命题为假。**

## 人类审核记录

尚未收到对本报告或具体接口修改的明确人类决定；`human_decision: null`。既有“公共接口不变”的授权持续适用；报告不请求重新批准正常内部补证。
