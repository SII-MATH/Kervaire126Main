---
title: 命题 6.20 的差集短式与晚页 crossing
archived_from: local-history/metadata/interface-reviews/ProofTools/20261018-prop620-crossing-dichotomy/report.md
archived_sha256: 67f787854c3d57724c0184cd32e5ecebfbd19613a674a84b7b2b997e06273ab4
summary: "命题 6.20 的差集短式或晚页 crossing 精确候选；需保留原目标、前提与未完成范围，授权记录见全文。"
issue_id: "20261018-prop620-crossing-dichotomy"
responsibility_module: "ProofTools"
targets:
  - "AimPaper Proposition 6.20: latest authorized nonliftable-short-or-later-crossing revision"
  - "proposed FiniteExtensionNonliftableShortTo"
  - "proposed finiteExtension_nonliftableShort_or_lateCrossing"
baseline_commit: "aad718722aa01dfce361f40645fc776037d1078f"
worktree: "/inspire/hdd/global_user/czxs25250150/Kervaire126Main"
candidate_source_commit: "uncommitted frozen production source; SHA256 aa1ae0f936ebb219b551f03731bf4001baef78dd1010029442525517afe50251; local Lean and public ProofTools facade build passed"
api_file_and_sha256: "metadata/proof-tools-api.json: fcec6893b94ffc475e8ccd95630bb49818c91ca9550f35dbd1247aee0a7ad500"
source_file_and_sha256: "KIP126/ProofTools/Paper/ExtensionIndeterminacy.lean: 1720fccd565456ad350d489a3da09eacecce316d5d9626077b71e5fdad71c34c"
reporter_agent: "/root/prop620_bzero_report"
independent_of_discoverer_and_implementer: true
evidence_level: "independent complete signature/source proof review; local Lean and public ProofTools facade build passed; independent all-import dependency audit passed (predicate601/33, theorem929/38); global trust/interface/whole-project validation pending"
status: pending-human-review
human_decision: null
authorized_mathematical_scope: "User explicitly requested recording and formalizing the teacher's latest dichotomy revision; no repeated approval is needed within this mathematical scope. No exact unprovided Lean signature is represented as already approved."
---

# 接口调整记录：差集短式或晚页 crossing

## 请求人类决定的具体问题

本轮数学修改范围已有明确授权：王老师提出新的二择形式，用户要求“把修改版计memo，对最新版形式化”（协调者转交的本聊天最新指令）。**无需再次询问是否允许按这个数学范围补证。** 本报告记录授权、精确对象与量词、下游边界；实际D_y谓词已交付并完成类型核对；主定理签名和完整证明源码现已交付，独立语义核对通过；最终冻结源码的局部Lean、公共ProofTools入口构建及独立全import依赖审计已exit0；全仓接口/责任/交叉CaptureTrust与完整构建仍待协调者完成，不提前标全仓整合通过。

王老师原话为：“原先差集的版本，写，若晚diff本质，早diff不本质，且不满足差集条件，则一定存在crossing”。消息`om_x100b620dc11210a4dd281834ddfa376`，群位置1500，2026-10-17 15:49 UTC（北京时间23:49），[原消息链接](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1500)。原始JSON存于本目录`evidence/wang-crossing-feedback.json`。

`pending-human-review`保留模板初始状态，`human_decision: null`不伪造人类已逐字批准新Lean签名的逐字源码。它不撤销用户已给的数学范围授权，也不要求协调者重复索取同一许可。

## 原接口、背景与问题成因

### 三个版本须分别记录

1. 原印刷6.20第二段引入未完整量化的y′及一般b，还要求早循环与晚循环的严格差集。此前把y′解释为原y并取b=0、但保留差集的加强版有纸面实际谱反例，不能标作原义已证。
2. 已授权并完成的“去差集、固定y、b=0”版本：`finiteExtension_inessential_iff_shorter`。它公开同一早商、同一map、同一原target的短式判据，允许短式inessential或零源。当前保持原样。
3. 本轮最新版恢复差集短式作为第一分支，另加**晚页normalized synthetic ESS crossing**分支。这是新增结论，不撤回第2项，不声称旧的固定目标差集iff已经获得证明。

原6.20来源是`AimPaper/main.tex`的`prop:dec738d3`。合法页下降前提修正及公开自然性`finiteExtension_descends`继续保持。

### 当前相关公共接口及用途

`KIP126.ProofTools.Paper.finiteExtension_inessential_iff_shorter`，`ExtensionIndeterminacy.lean:300`，完整参数为固定Standard模型中的X/Y、实际f、rEarlier/rLater、n/s/t、同x/y的晚早两个`FiniteExtensionWitness`、`rEarlier≤rLater`和晚witness.Essential。其结论为早witness非本质 iff 存在a:ℕ、0<a≤n−e、经典早cycle源x′、其`finiteExtensionCorrectionLabel`的真实E∞代表z，以及同一早map长度n−a到原`Wearly.target`的`TowerExtensionEquation`。合法页、长度、source/target循环和代表条件均由witness字段给出，未额外要求目标ρ绑定。

本轮相关crossing公共定义位于`ExtensionRepresentatives.lean:39`。以下是其完整泛型环境和声明（没有隐藏的任意目标选择结果包）：

```lean
universe u v
variable {Syn : Type u} [SyntheticCategory.{u,v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Syn} {unit : S_0_0 ⟶ H} {E : SyntheticAdamsFamily Syn}
  {P : SyntheticTowerPresentation unit E} {X Y : Syn} {g : X ⟶ Y}
  {cx : SyntheticTowerConvergence P X} {cy : SyntheticTowerConvergence P Y}

public def ExtensionNoCrossingRange
    (M : ConvergentMap E g cx.toConvergence cy.toConvergence)
    (p : ℤ × ℤ) (s n threshold : ℤ) : Prop :=
  ∀ a b : ℤ, s < a → a ≤ b → threshold ≤ b → b ≤ s+n →
    ∀ x y, TowerExtensionEquation M p a (b-a) x y → y = 0
```

定义使用actual filtered map及convergence，否定它表达有较高源到允许范围内非零目标的实际扩张。这里的短式本身无需额外essential前提；这不等于定义5.9的经典有限页`FiniteHasCrossing`。

### 本轮拟新增两个公共项

记e为`normalizedExponent model.classicalTower f`、qE=rEarlier−1、qL=rLater−1、p=(t−s,t+e)。固定X/Y、同一实际f、同x/y的`Wlater`与`Wearly`。

拟定义

    FiniteExtensionNonliftableShortTo X Y f rEarlier rLater n s t x y Wearly

为D_y：存在a:ℕ和x′、z，使

- 0<a且a≤n−e；
- x′∈cycles X (qE−a) (s+a,t+a)；
- x′∉cycles X (qL−a) (s+a,t+a)；
- 在**同一早商normalized源**中，`finiteExtensionCorrectionLabel ... qE ... a x′`代表z；
- 同一早商`finiteExtensionMap ... qE`支持长度n−a的`TowerExtensionEquation`，源为z，target严格为原`Wearly.target`的整数指标regrade。

第一分支保持原y、b=0，不要求短式在晚页存在。这里“Nonliftable”由经典严格差集表达，不能仅凭名称默认为真实ρ像外；两种表达的关联必须由实际有限商标签、相同边界分母与ρ自然性证明。

拟定理

    finiteExtension_nonliftableShort_or_lateCrossing
      (... Wlater Wearly hle lateEssential earlyInessential) :
      D_y ∨ ¬ ExtensionNoCrossingRange Mlate p s n s

其中Mlate严格是`model.convergentMap`，源为qL阶商的`extensionSourceObject`，靶为qL阶商的`.nu Y`，映射是`finiteExtensionMap model X Y f qL`。这不是自由替换的convergent map或早商map。

令第二分支为C_晚，其展开是：存在u,v∈ℤ，s<u≤v≤s+n，以及晚商真实E∞源zL、目标ηL≠0，使`TowerExtensionEquation Mlate p u (v−u) zL ηL`成立。stem和weight始终是同一p；ηL可为较低目标，不冒充原y。

## 真实前提与对象核对

| 条件/对象 | 必须保留的准确范围 | 当前状态 |
| --- | --- | --- |
| 模型、X/Y、f | 固定Standard模型及同一个实际谱映射 | 已核对设计范围，已核对新精确签名，保持固定model和同X/Y/f。 |
| 原x/y | x在(s,t)、y在(s+n,t+n) | 两witness必须绑定相同Ambient标签。 |
| 页与长度 | 早页≥2、早≤晚、e≤n≤rEarlier−2+e | 可由witness字段及hle给出，不加方便证明的新前提。 |
| 原晚页扩张 | 已存在且Essential | 不能把该已存在前提忘掉，进而声称推出升页存在。 |
| 原早页扩张 | 同x/y且非本质 | 不能只用任意短式存在而丢掉原目标关联。 |
| D_y的a范围 | 0<a≤n−e≤rEarlier−2 | 保证qE−a和qL−a至少为1。 |
| D_y早cycle与晚排除 | 两者完整保留 | 不是只检查一个任意代表，也不是从已完成去差集iff删除其正确性。 |
| D_y固定target | 同一Wearly.target，只允许degree equality运输 | 没有新y′或自由target premise。 |
| 短源ESS存活 | 由实际`TowerExtensionEquation`确保 | 不得把已被早ESS d₀杀掉的经典源作为短式见证。 |
| C_晚 | 晚normalized有限商、同stem/weight、非零target、较高source | 不替换成早crossing或Definition5.9经典crossing。 |
| 晚页无crossing的反证前提 | 只在私有证明中作`by_contra`/分类使用 | 不新增成公共定理前提来弱化结论。 |
| 经典latecycle到实际ρ首项提升 | 必须保持指定标签、实际Q/shift/ρ | 私有兼容链已给完整源码，未加public premise；实际kernel检查待完成。 |
| n=e / rEarlier=2 | D_y为空；已有结果排除早inessential前提 | 应复用真实边界证明，不擅加n>e。 |
| zero/boundary标签 | 晚Essential排除其真实target为零，不等于只写经典y≠0 | 必须用实际rep、ρ单射和同y唯一性。 |

### “不满足差集条件”的量词

本轮“若不满足差集条件则有crossing”解释为**不存在任何D_y见证**，即¬∃a,x′,z满足全部条件。它不同于挑选某一个早短式，发现该x′属于latecycle，就声称D_y不存在；其他a或其他源可能仍在差集中。

目标D_y∨C_晚在经典逻辑下等价于¬D_y→C_晚。给定一个early短式、它的源可提升，只提供局部事实，必须通过后续essential短式提取/保持目标修正的完整论证接到这个全称否定。

## 独立证据与复现

本轮已直接读取原始新群消息、baseline、memo、实际`ExtensionNoCrossingRange`、已完成去差集iff及其真实源/target签名。没有实现候选、没有写生产或共享记录、没有运行lake build、没有发送飞书。

本目录baseline固定了六模块API、`Language.lean`、`Laws.lean`、`ExtensionIndeterminacy.lean`、工具链和待补清单哈希。旧stretching谓词的冻结源为：

- Language SHA `50164249c50b08c58a5357e1aec2ea6035dd8043474e71b69082b56eed9cd7ee`；
- Laws SHA `8731a608b3c750b044837c927ae45a8aee71eebdff441d89dd82df6b97f0732a`。

前一版本“去差集iff”的完整all-import依赖审计为822项目常量、38个既有上游直接holes，CorrectionLabel为567/33，无Main或ProofTools本地洞。这是已完成旧版本的基线，**不能拿来当新二择实现的依赖审计结果**。普通module视图602/28仅下界；新候选完成后必须重新核对实际完整闭包。

实际新D_y和主定理完整源码现已交付并完成只读核对。协调者报告ESSShiftNaturality证据已Lean exit0、ExtensionEssentialSource helper已lake build exit0，报告员也已读取其完整证明体，但没有自行重跑这些命令，也不据此称主二择定理已编译通过。分项结果不能代替整合后主结论的kernel和依赖审计。

## 方案及精确差异

### 先评估保持现有接口的内部方案

现有`finiteExtension_inessential_iff_shorter`保持，无须改其签名。已冻结`FiniteExtensionNonliftableCrossing`及`FinitePageExtensionStretchingLaw`保持。新增D_y谓词和二择定理，在ProofTools内部完成所需代表构造；不转移责任到Main或新增上游假设。

核心内部路线必须完成两个真实引理：

1. 从早页原扩张非本质中提取命中指定原y的**essential早短式**。去差集iff可提供允许零源/inessential的短式，但不能不加证明就称所选a=1短式essential。
2. 在¬D_y下，该essential早短式的经典首项属于latecycle。构造实际晚商E∞首项，其ρ像恰是早首项。该步骤必须证明Qq选择iso、归一化shift、标签和ρ的自然性；不能只拿两个各自存在的cofiber同构就假定跨页兼容。

在假设晚页无crossing时，可用晚较高源的实际像进入高于原target的滤过，减去其早ρ像保持原target、提高早源滤过，进而与该早短式的essential性冲突。这是已交付源码的内部证明路线，此前该段仅完成源码核对；最终冻结版本已实际Lean成功，实绩见末节。不能把第2项直接作为新公共前提、或恢复“结果包/Challenge”绕过构造。主候选现已给出该内部构造，源码核对见末节，kernel状态另列。

### 精确语义变化

- 去差集iff：早inessential ↔ 存在早短式到同y，不要求差集。
- 新结论：晚Essential且早inessential ⇒ **存在差集早短式到同y，或存在晚synthetic crossing**。
- 新结论不声称D_y必然成立；也不要求crossing目标等于原y。
- 原差集固定目标iff的失败不再是本轮结论的反例，因为其可能落入C_晚分支。但不得仅因“加了crossing分支”就声称新结论自动为真，仍要完成上述真实引理。

实际新增谓词的完整Lean类型已交付并核对，见末节。主定理精确类型与整合证明已交付并完成独立源码核对，所有隐式参数/实例/宇宙、实际对象关联与proof-body的结论见末节；最终源码局部kernel和公共入口构建已通过；全闭包及全仓整合审计尚待，不预先标全仓整合通过。

## 下游影响

| 声明/记录 | 影响与边界 |
| --- | --- |
| `finiteExtension_descends` | 完全保留。 |
| `finiteExtensionCorrectionLabel` / `finiteExtension_inessential_iff_shorter` | 已证去差集版本完全保留，不改已登记类型。 |
| 新D_y与二择 | 仅新增此次授权数学版本；源/target/map须固定。 |
| 原stretching障碍谓词和充分条件 | 完全不改，不借同名nonliftable概念偷换责任。 |
| Definition5.9经典crossing | 不自动得到；需另证从当前synthetic C到该谓词的比较。 |
| 升页推论 | 实际编号6.23，此前误称6.21（公式号）。本定理已假定晚页原扩张存在，不能用它自动推出晚页存在。 |
| Main及其他模块 | 不接手证明、不修改其接口；新增二择的证明责任在ProofTools。 |
| API/契约/sources/coverage | 明确新增“最新授权二择版本”；原印刷版、去差集版、新二择版分别保留来源与状态，不覆写历史变成“原文原义全证”。 |
| 待补清单 | 不新增公理/sorry或责任；既有上游责任如实记录。 |
| Memo | 用户已明确要求，协调者已更新；报告员只读。 |
| Tests/构建 | 新签名完成后做普通公共消费、合法/边界例、接口锁/全闭包与source inventory/lake build，由协调者统一运行。 |

## 阻塞范围与继续项

授权范围不阻塞。分项进展：essential早短源提取helper源码已读取，协调者报告其构建通过；ESS shift自然性证据源码已读取，协调者报告Lean检查通过。实际待补：全闭包传递审计、旧接口与既有责任不变核对、全仓完整构建及最终状态记录。主二择及Q/shift/ρ同首项链的完整源码现已通过局部Lean及公共入口构建，实绩见末节。

可继续：以上私有引理与新公共候选实现、独立对象/接口核验；已完成去差集iff和合法域下降正常消费；不依赖新结论的其他目标。

不得继续：以新的public假设绕过上述构造、修改旧stretching或已证去差集接口、自动将6.23标完成、将C_晚改称已比较到经典Definition5.9。

## 人类审核记录

- 王老师真实原话及原消息出处见本报告首节和`evidence/wang-crossing-feedback.json`。
- 本聊天用户明确要求最新版计memo并形式化，协调者已记录该授权；本轮可以继续构造，无需重复询问。
- 当前没有声称王老师逐字审核过新Lean源码。本报告不把数学范围授权伪装成未知签名已审核通过，也不因模板初始状态要求重问已授权的数学修改。

## 新精确候选核验

### 实际 D_y 谓词：类型和对象核对通过

已直接读取`KIP126/ProofTools/Paper/ExtensionCrossingDichotomy.lean:28`的实际定义，当前完整公共类型及定义为：

```lean
@[expose] public def FiniteExtensionNonliftableShortTo (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ) (x y)
    (Wearly : FiniteExtensionWitness model X Y f rEarlier n s t x y) : Prop :=
  ∃ a : ℕ, 0 < a ∧ (a:ℤ) ≤ n-normalizedExponent model.classicalTower f ∧
    ∃ x' : Ambient model X (s+a,(t-s)+(s+a)),
      x' ∈ cycles model X (((rEarlier-1:ℕ):ℤ)-a) (s+a,(t-s)+(s+a)) ∧
      x' ∉ cycles model X (((rLater-1:ℕ):ℤ)-a) (s+a,(t-s)+(s+a)) ∧
      ∃ z,
        HasInfinityRepresentative _ 2 _
          (finiteExtensionCorrectionLabel X Y f (rEarlier-1) s t a x') z ∧
        TowerExtensionEquation (model.convergentMap
          (.quotient (rEarlier-1) (extensionSourceObject model X Y f))
          (.quotient (rEarlier-1) (.nu Y)) (finiteExtensionMap model X Y f (rEarlier-1)))
          (t-s,t+normalizedExponent model.classicalTower f) (s+a) (n-a) z
          ((eqToHom (congrArg (fun d =>
            ((model.family.obj ((SyntheticObject.quotient (rEarlier-1) (.nu Y)).obj
              model.nu model.auxiliary)).sequence.ssData
              (d,(t-s)+d,t+normalizedExponent model.classicalTower f)).eInfty)
            (show s+n = (s+a)+(n-a) by omega))) Wearly.target)
```

这里model为固定`AdamsSynthetic.Standard.model`，无新增自由D、范畴或额外实例参数。x/y由同一Wearly约束到既定Ambient分次，不能从私有未指定对象取得。经典源第二坐标`(t−s)+(s+a)=t+a`；cycles索引的自然数减1后转整数，再减整数a，因定理范围可证各层合法，并未用自然数截断a差值偷换cycle层。

该实际定义与本轮授权D_y逐项一致：完整早cycle与晚排除、0<a≤n−e、同一早商、同一实际f、同一normalized source/weight、λ^a经典标签、同一个Wearly.target。它不要求短式essential或源非零，不把晚cycle排除换成任意ρ像谓词，也不改旧stretching。D_y本身不额外携带hle；应由最终定理提供rEarlier≤rLater，从而适用跨页比较。

首次读取该谓词时主定理尚未存在，中间SHA为`93e40d449daaad93f726e857988ea65cc4534da1b5f1f2b9c6f1c3f5f3b23411`；随后完整候选已交付，SHA与新核对结果见下节。两次哈希都是审查检查点，最终验证应固定实际成功版本。

### Essential 早短源私有 helper：真实证明体已核对

已读取`KIP126/ProofTools/Paper/ExtensionEssentialSource.lean`全部两条private theorem：

- `tower_essential_shorter_same_target`：保持同一M/p/y，取所有能命中y的高源实际代表中source filtration最大者。`Nat.findGreatest`在1…n的有限区间选择，若短式仍非本质，零源/同目标关系给出F^(s+a+1)的代表，与最大性矛盾；若到a=n，映射保滤过会使目标进入下一层，违背y非零。
- `finiteExtension_essential_shorter_source`：在同一实际有限normalized map中调用上项，然后用已存在`finite_crossing_target_bound`把a≤n加强为a≤n−e，再用真实`correction_label_exists`解码早cycle与λ^a标签。给出的短式Essential是构造结果，不是新增公共前提。

已核对n>0从`inessential_length_strict`结合e≥0推出，没有默默漏掉n=e；最终a<r−1来自witness合法域。源和target始终为同一实际商，目标仅作整数坐标transport，未换成任意y′。源码本次SHA为`b304c817a0cc1f7a958b16ae0c0e74c2e60357e2317d723b39b400c34ab36aa4`。协调者报告该文件已经实际lake build exit0；本报告员未自行运行构建，也未把此helper通过称作主二择通过。

### Shift/ρ 自然性证据与装配状态

已读取本目录`ESSShiftNaturality.lean`的三条private theorem：

1. `infinityGradedTransportComm`从真实`FilteredMapTransport`的level箭头兼容，经associated-graded投影的epi性质证明graded方块；
2. `infinityTowerGradedNatural`使用已有`infinity_graded_naturality`，把实际family的E∞映射与同一convergence的graded映射关联；
3. `infinityTowerNatural`组合前两项及`SyntheticESSShiftComparison.transport`，证明实际ESS shift的E∞方块自然性。

第三项针对Type1/ModuleCat.{0}层级，符合当前固定Standard模型；不冒称任意宇宙的新增公共一般定理。它是从已有结构的真实map_comm/level/graded兼容证明，没有新增λ商选择自然性的公理。协调者报告该证据文件Lean exit0，当前主文件已包含同样私有自然性证明。

主文件已出现`essential_short_source_not_in_range`、`infinity_map_eq_of_homotopy_eq`、`correction_rho_square_infinity`、`correction_unshifted_label_rho`和`correctionInfinity_represents`等真实构造。已核对其设计使用指定Q包含兼容、既有`quotient_shift_restriction_on_spheres`以及实际homotopy/associated-grade代表，不以任意cone同构“自然”作为无证假设。

上述分项已装配进最终完整proof-body并经源码复核：`correction_source_lift_of_late_cycle`准确证明晚zL经actualρ恰等于所选早z，主定理以该等式调用`essential_short_source_not_in_range`；没有只列各页对象的独立存在。最终冻结版本已完成局部Lean及公共入口构建；全闭包和全仓结果仍待记录。

### 当前独立结论

已提供的D_y类型忠实于授权范围；helper和自然性证据的数学/对象/依赖方向核对未发现新前提或循环。主公共二择完整源码已经成形并核对，最终局部kernel实现和公共入口构建已通过，尚未提前作全传递闭包及全仓整合通过的判断。旧去差集iff和stretching继续保持；无需对上述已授权数学范围重复询问用户。


### 主定理精确签名与完整 lift 链：源码核对通过（最终实绩见末节）

本节审查输入`ExtensionCrossingDichotomy.lean`中间SHA为`496e0aade7bfd84b14b3224d893ac7e3334100a819f96a1e36983aef375cfcb5`。该版本主定理位于432行，完整公共签名如下：

```lean
public theorem finiteExtension_nonliftableShort_or_lateCrossing (X Y : ClassicalObject)
    (f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
    (rEarlier rLater : ℕ) (n s t : ℤ) (x y)
    (Wlater : FiniteExtensionWitness model X Y f rLater n s t x y)
    (Wearly : FiniteExtensionWitness model X Y f rEarlier n s t x y)
    (hle : rEarlier ≤ rLater) (hess : Wlater.Essential) (hne : ¬Wearly.Essential) :
    FiniteExtensionNonliftableShortTo X Y f rEarlier rLater n s t x y Wearly ∨
      ¬ ExtensionNoCrossingRange (model.convergentMap
        (.quotient (rLater-1) (extensionSourceObject model X Y f))
        (.quotient (rLater-1) (.nu Y)) (finiteExtensionMap model X Y f (rLater-1)))
        (t-s,t+normalizedExponent model.classicalTower f) s n s
```

无新自由范畴/模型/实例参数；固定Standard模型与先前两个公共结果一致。x/y的类型由相同X/Y/f、同n/s/t的两witness推断。两witness分别带完整page/length/source-cycle/target-cycle/实际代表/equation条件；因此并未漏掉早页≥2、n≥e、合法早页上界、原类循环等前提。hle允许等页，是有效加强而非遗漏晚页严格性。hess、hne分别针对这两个具体witness，没有把经典y≠0当作晚essential。

右侧D_y直接使用Wearly及其原target；C分支的source/target均为rLater−1商，实际map为同一f的`finiteExtensionMap`，weight为t+e、stem为t−s，threshold=s、目标上界s+n。没有早/晚商混用，没有把C改成经典`FiniteHasCrossing`，没有新的目标兼容前提或升页存在性结论。谓词存在量词覆盖所有合法a/x′/z；主证明不会把单个x′属于latecycle误当成全体D_y不存在。

#### 经典 latecycle 到 actual rho 首项：完整源码链

1. `unshifted_label_infinity_exists`：在qL商利用实际有限E∞/Z-B识别和给定经典latecycle，构造同一x′的`finiteTargetLabel ... a`的晚未移位E∞代表zu。前提0<a<qE≤qL由合法域和hle给出，不新增。
2. `correction_unshifted_label_rho`：从商塔`rho_quotient`及family page复合，证明该晚标签映到同一x′的早未移位标签。
3. `correction_rho_square_infinity`：对已经满足指定商包含方块的Qq选择iso，调用既有`quotient_shift_restriction_on_spheres`，只使用实际所有BiHom代表上的复合相等；再由`infinity_map_eq_of_homotopy_eq`通过真实associated-grade代表满射和map自然性提升为E∞方块。没有擅自声称任意cone maps在范畴层面严格相等。
4. `infinityTowerNatural`与`infinity_map_regrade`：将实际shift transport的自然性与整数坐标transport结合，得到`correctionInfinity_rho`，即晚归一化Correction首项经actualρ等于早Correction首项。它使用Qhom/Qinv的实际互逆消去和已证明homotopy方块，不假定各页各自存在的Q天然相容。
5. `correction_source_lift_of_late_cycle`：取第1步zu，先从真实未移位ρ及第2步得到早未移位代表，再经`correctionInfinity_represents`得到同一早CorrectionLabel代表。与原早z的`HasInfinityRepresentative.unique`比较，严格得到actual normalized sourceρ(zL)=z。此时才调用后续不可提升首项反证，没有把“经典latecycle”与“实际ρ像”无证等同。

各步保持同一X、actualνX、Qq、e归一化shift、固定stem/weight及经典x′。a<qE使早/晚strip与循环索引均合法。没有把ρ首项lift作为public premise，也没有使用未定理化的跨页自然性结果包。

#### 主证明的两分支和量词核对

主证明对真实晚`ExtensionNoCrossingRange`分类：若其否定成立，直接返回C_晚；若无晚crossing，先由同y标签/ρ单射得到早target非零，再由私有helper选取同一原target的essential早短式。

对这个已构造的x′再分是否属于latecycle：若不属于，已满足完整早cycle、晚排除、λ^a标签与固定target短式，返回D_y，并只遗忘私有构造给出的额外essential性（使用hs.1）。若属于，调用上段实际首项lift链得到zL，然后`essential_short_source_not_in_range`给出矛盾。

后一个引理实际选取zL的晚F^(s+a)代表；无晚crossing由`image_correction_in_next`使其像在G^(s+n+1)。实际商方块保证其早ρ代表的像仍高于短式目标，而首项恰为z。它构造同一早源首项到零target的equation，违背原早短式essential。因此源码中的`False.elim`来自这个完整局部矛盾证明，不能误报为借项目不一致假设无中生有地消去False。

#### 边界、依赖方向与当前证据限度

- n=e及rEarlier=2由既有`inessential_length_strict`和早target非零排除，helper只在得到n>0后使用最大滤过选择；没有加公共n>e。
- hle等号时早晚严格cycle差集为空，联合essential/inessential前提不能造成虚假D；sphere自然性与lift链包含qE=qL。
- 原target为零或落入分母时晚essential不成立；没有用经典y非零代替synthetic target非零。
- 新谓词不调用新主定理，主定理只调用私有构造、已证去差集/代表/有限商接口，没有调用6.23或从其逆否回证，源码未见循环。
- 已完成的去差集iff和旧stretching接口不变；本轮只添加授权二择和相应私有数学构造。

本节最初审查的是中间SHA`496e0aad…`，当时尚未Lean成功，未将其标成kernel通过。后续最终成功源码及实绩如下；中间检查点仍不用于冒充最终构建输入。


### 最终冻结源码、局部 kernel 与公共入口构建实绩

报告员已重新直接读取最终主签名与`correctionInfinity_rho`的实际cast/同构取消收尾，并运行只读SHA核对。最终生产文件为：

- 路径：`KIP126/ProofTools/Paper/ExtensionCrossingDichotomy.lean`；
- SHA-256：`aa1ae0f936ebb219b551f03731bf4001baef78dd1010029442525517afe50251`；
- `FiniteExtensionNonliftableShortTo`位于29行；`finiteExtension_nonliftableShort_or_lateCrossing`位于450行；
- 最终两条公共签名与本报告已核对版本相同，变更是内部cast/同构合成的证明收尾，没有改变模型、前提、量词、对象或结论。

已直接读取同目录`worker-source-hashes.json`和`worker.md`：worker7对最终完整文件执行

```text
lake env lean KIP126/ProofTools/Paper/ExtensionCrossingDichotomy.lean
```

实际exit0，原日志保存为`worker-final-lean.log`，只有linter/style提示。worker6的此前失败保留在`worker6-before-comp-id.log`，没有记成成功。这是worker的实际运行结果；本报告员没有伪称自己重新运行kernel检查。

协调者随后执行正式公共入口构建：

```text
lake build KIP126.ProofTools
```

实际exit0；报告员直接读取`/tmp/prop620-crossing-public-build.log`末尾，确认`Built KIP126.ProofTools`与`Build completed successfully (2823 jobs)`。因此最终主文件的局部kernel检查、所属公共入口编译已成功，不再停留在“只有数学证明路线”的状态。

这两项成功仍不替代全仓最终验证。本次独立production审计随后已交付并核对，准确结果见下节；全import-all CaptureTrust交叉核对、旧116条导出保持、299项既有责任保持、source inventory、普通公共消费及完整`lake build`结果仍由协调者串行完成并记录。**不把上一轮822/38套到本轮，也不声称完整全仓构建已经通过。** 协调者随后提供本目录最终validation记录时，再据真实输出补链接和结果。既有标准模型及文献责任继续如实保留。


### 最终节点的独立 all-import 完整依赖审计

独立审计员随后通知已实际exit0，并提供本目录：

- `IndependentProductionAudit.lean`；
- `independent-production-audit.log`；
- `independent-production-audit.json`。

审计覆盖当前476个数学模块的全import-all视图，加Lean共477个imports。报告员已直接读取JSON中的两个实际root结果，并核对其上游直接holes、空数组与公理列表；不以worker普通module导入可见闭包代替此完整视图。

| 最终公共root | 项目常量完整闭包 | 既有已登记上游直接holes | ProofTools本地holes | 未登记holes | 项目axiom | Main依赖 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `FiniteExtensionNonliftableShortTo` | 601 | 33 | 0 | 0 | 0 | 0 |
| `finiteExtension_nonliftableShort_or_lateCrossing` | 929 | 38 | 0 | 0 | 0 | 0 |

两root的`level_params`均为空，符合固定Standard模型的完整实例化类型。公理清单仍为`propext`、`sorryAx`、`Classical.choice`、`Quot.sound`；其中sorryAx来自上述既有AdamsSynthetic/Literature上游责任，不能宣称本次完整定理在项目中已无任何未证依赖。实际直接holes名称已完整保存在JSON中，本报告不省略它们的责任归属。

新主定理929/38与上一轮去差集iff822/38是不同root的不同闭包，不因holes数相同就合并记录。新谓词601/33也不同于上一轮CorrectionLabel567/33。此次仅确认最终冻结SHA对应的独立依赖审计已完成；最终全仓CaptureTrust交叉核对、接口不变/待补清单不变和完整构建结果继续等待协调者的真实validation记录。
