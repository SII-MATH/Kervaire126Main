---
issue_id: "20261017-prop620-remove-difference"
responsibility_module: "ProofTools"
targets:
  - "AimPaper Proposition 6.20, authorized revised second clause"
baseline_commit: "aad718722aa01dfce361f40645fc776037d1078f"
worktree: "/inspire/hdd/global_user/czxs25250150/Kervaire126Main"
candidate_source_commit: "uncommitted ExtensionIndeterminacy.lean snapshot, SHA256 1720fccd565456ad350d489a3da09eacecce316d5d9626077b71e5fdad71c34c"
api_baseline_file_and_sha256: "metadata/proof-tools-api.json: 12e126b3d07992712555dc5ea0bde9c0afbbd2cdbdb3112adaad190edb64cb5f"
source_file_and_sha256: "KIP126/ProofTools/Language.lean: 50164249c50b08c58a5357e1aec2ea6035dd8043474e71b69082b56eed9cd7ee"
reporter_agent: "/root/prop620_bzero_report"
independent_of_discoverer_and_implementer: true
evidence_level: "independent complete public signature and source proof review; worker Lean success recorded; existing upstream proof obligations retained; full integration checks managed by coordinator"
status: pending-human-review
human_decision: null
authorized_mathematical_scope: "Human explicitly requested removal of the late-cycle exclusion in the unpublished second clause; preserve the early-cycle condition, original target y, and b=0. No repeated authorization question is needed for implementation within this scope."
---

# 接口调整记录：命题 6.20 删除差集排除条件

## 请求人类决定的具体问题

**本轮数学修改范围已有明确的人类意见，不需要再次询问是否允许去掉差集条件。** 本报告独立记录真实授权范围并审查其语义边界；它将真实人类修改意见与随后完成的独立Lean签名审查分别记录，也不将这一修改写成“原接口无语义变化的补证”。

王老师于 2026-10-17 15:06 UTC 在 `project-math-assistant` 群回复：“把差集条件先去掉”。原消息：`om_x100b620ca1ac9ca4c1bb712f5951ae8`，position 1496，[消息链接](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1496)。原始JSON逐字快照保存在同目录 `evidence/wang-remove-difference-feedback.json`。

本聊天用户已授权“有回复就按他的意见继续补证”，并明确新增“这个改动也写到memo里”。协调者负责实施、公共登记和memo；本报告员不重复请求这项范围的授权，不写共享记录。

`status: pending-human-review` 和 `human_decision: null` 不表示需要再次获得同一数学范围授权；本报告没有声称人类逐字审核过新Lean源码，不能解释成必须停工再让用户重复同一修改指令。

## 原接口、背景与问题成因

### 原纸面声明及此前拟解释

`AimPaper/main.tex:1981–1993`，Proposition 6.20，标签 `prop:dec738d3`。

固定同一个实际谱映射 f:X→Y，记 e=e(f)。原晚页扩张 d_n^(f,E_r)(x)=y 满足

- x∈Z_(r−1)^(s,t)(X)；
- y∈Z_(r−1−n+e)^(s+n,t+n)(Y)；
- e≤n≤r−2+e。

第一段在已批准修正的范围 2≤r′<r、n≤r′−2+e 下，给出同一 x、y、f 的早页扩张。该部分已由 `ProofTools.Paper.finiteExtension_descends` 公开，本次不变。

第二段另假设晚页原扩张 essential。原印刷式声称早页原扩张 inessential iff 存在 0<a′≤n−e、

    x′ ∈ Z_(r′−1−a′)^(s+a′,t+a′)(X)
         \\ Z_(r−1−a′)^(s+a′,t+a′)(X)

和某 b≥0，使短 synthetic 扩张满足

    d_(n−a′−b)^(fhat_(r′−1))(λ^a′x′) = λ^(n−b−e)y′.

原印刷式没有完整规定 y′；此前按王老师“y′应该是y吧？”和“一般的b，可以推b=0”继续尝试固定原目标、b=0 解释。该解释若保留严格差集，其必要方向已出现纸面实际谱反例；详见前一独立报告 `../20261017-prop620-fixed-target-bzero/report.md`。本次人类指令针对这个差集限制进行实质修改。

### 本次修正版的精确数学式

保留上述同一 f、x、y、r′、r、n、s、t、e 和全部真实前提，取 b=0；将第二段右侧改成

    ∃ a′, 0<a′≤n−e,
      ∃ x′∈Z_(r′−1−a′)^(s+a′,t+a′)(X),
        d_(n−a′)^(fhat_(r′−1))(λ^a′x′) = λ^(n−e)y.

即：早页原扩张 inessential iff 存在这样一个更高源滤过、命中同一原目标 y 的较短 synthetic 扩张。**只删除 x′∉Z_(r−1−a′)；保留 x′属于早页循环组。** 不要求这个短扩张的源或方程在晚页存在，也不额外要求短扩张 essential。

右侧的 differential 写法仍包含该源支持所写 ESS 微分的存活要求。不能仅以 synthetic Adams E∞ 中有一个同次类替代 ESS 中支持 d_(n−a′) 的源，也不能以 y 已是 ESS 边界为由免除源的 ESS 存活要求。

### 当前并无旧公共第二段签名可原地修改

当前公共登记只含第一段 `KIP126.ProofTools.Paper.finiteExtension_descends`。完整声明保存在本报告 `evidence/ExtensionDescent.lean`，它以固定Standard模型、同一实际f、Ambient类x/y和合法页前提，从晚 `FiniteExtension` 推出早 `FiniteExtension`。本次不改变其名称、类型、前提、导出。

本次应为未公开的修正版第二段新添正确声明，而不能替换旧的 stretching 障碍谓词。

### 与被冻结的 stretching 接口区分

`KIP126/ProofTools/Language.lean:119`：

```lean
public def FiniteExtensionNonliftableCrossing
    (rEarlier rLater : ℕ) (n s t : ℤ) : Prop := ...
```

它参数化于给定 `D : Model C Syn`、`X Y : ClassicalObject` 和实际 `f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary`，使用早商固定weight的真实E∞ source/target，要求 source 不属于晚商ρ的实际E∞映射像、同一个有限商中的 `TowerExtensionEquation`、target≠0；允许b=0和零长度。完整包含隐式范畴/宇宙/实例/公式的声明逐字快照见同目录 `evidence/Language.lean`。

`KIP126/ProofTools/Laws.lean` 中 `FinitePageExtensionStretchingLaw` 使用这个谓词的否定，作为一个**已冻结的充分条件**。它不是本轮未公开6.20第二段的原样定义，不声称与普通Adams代表差集等价。本次授权没有允许从它删除非提升条件，也没有允许削弱/重写 stretching 的类型。

## 真实前提与对象核对

| 条件或对象 | 本次要求 | 核对状态 |
| --- | --- | --- |
| 模型、X/Y、实际f | 与原扩张相同，不另传任意方块或替代对象 | 已核对完整签名，使用固定model及同X/Y/f。 |
| 原x/y的Ambient分次 | x为(s,t)，y为(s+n,t+n) | 必须完整保留。 |
| 页范围 | 2≤r′<r；现有自然性允许≤的加强不自动改变第二段背景 | 保留原第二段背景，待实现明确。 |
| 长度 | e≤n且n≤r′−2+e | 保留；n=e是必须审查的边界，不能默默加n>e。 |
| 原晚source/target cycle | 由同一个晚 `FiniteExtensionWitness` 给出 | 保留，不用额外假设恢复“结果包”。 |
| 原晚essential | 原第二段前提保持 | 新核心局部判据若确实不需要，可另证加强版，但不得冒称去掉该前提是本轮唯一修改。 |
| 早扩张 | 通过已证同对象下降获得，或显式传入与晚witness关联的早witness | 已核对：显式同x/y的两个witness，目标ρ相容在内部证明。 |
| 更高源a′ | 0<a′≤n−e | 保留；不得随意改成≤n或加额外源假设。 |
| 短源早页cycle | x′∈Z_(r′−1−a′)^(s+a′,t+a′) | 保留；不是删整个cycle集合。 |
| 短源晚页cycle排除 | x′∉Z_(r−1−a′) | **本次明确删除。** |
| 短微分源ESS存活 | 支持所写d_(n−a′) | 保留，由实际extension relation表达。 |
| 原目标 | 同一个y，synthetic目标为λ^(n−e)y | 保留，不能存在任意不相关y′。 |
| b | b=0 | 延续此前固定目标解释，本次未恢复自由b。 |
| 短式的essential/目标非零 | 不擅自新增必要假设 | 依据真证明判断，不把充分条件误作等价。 |

## 独立证据与复现

本报告员只做授权、完整前提、对象和语义边界审查；没有实现候选证明，没有运行新的lake build，没有发送飞书消息。已有脏改动完整保留。

已实际读取：

1. 当前仓库 `AGENTS.md`、协作协议、指定模板；
2. 新群消息原始JSON与已更新memo条目；
3. 原6.20、Definition 5.4、当前下降源码；
4. `FiniteExtensionNonliftableCrossing` 与其 `FinitePageExtensionStretchingLaw` 调用；
5. 前一轮固定目标局部判据、反例报告及其局限。

原语义与修正语义对比是完整的集合逻辑事实：令E为允许的早页循环集合，L为晚页循环集合，则旧候选要求x′∈E\\L，新候选仅要求x′∈E。任何旧右侧见证也是新右侧见证，反向一般不成立。此修改扩大右侧存在量词的允许见证，因此使“早非本质⇒存在短式”的必要方向变弱；相应地，“存在短式⇒早非本质”需要对扩大的见证集合成立。它是实质性的目标调整，不能记为保持原类型的证明补全。

删除差集本身不自动证明完整修正版。已证固定目标高源代表判据提供起点，候选现已从高源实际代表取F^(s+1)分次（允许零首项），证明a′范围、经典早循环标签、同一λ权重、ESS源存活和同一指定目标关系。n=e时右侧不存在正a′，候选证明左侧也不发生，详见末节。

依赖审计边界：不允许调用待证明修正版、依赖它的6.21来形成循环；不允许新设“代表选择/保持目标”公理；固定Standard模型的既有上游待构造/文献责任应如实保留。精确签名、真实证明体和实际传递审计现已读取，结论与局限记录在末节。

## 方案及精确差异

### 优先评估保持原接口的内部方案

第一段可且应保持原接口。旧未公开第二段的固定y/nonlift必要方向不能靠内部证明一般解决，前一轮实际谱例子说明必须区分新旧语义。王老师已明确选择删除其晚循环排除条件。

### 已授权本轮方案

- 原：存在x′属于早循环、**不属于晚循环**，命中同一y的b=0短式。
- 新：存在x′属于早循环，命中同一y的b=0短式。
- 精确删除项：`x′ ∉ Z_(r−1−a′)^(s+a′,t+a′)(X)`。
- 未改变项：同一模型/映射/分次/目标、合法页、原晚essential、a′范围、早cycle、短式源ESS存活。
- 责任：ProofTools完成实际对象和代表构造，不向Main或上游添加新的待补责任。

新Lean声明及全部源码现已交付并逐项核对，完整签名快照见末节。独立语义审查通过不等同于声称人类逐字审核过Lean源码；实施处于既有数学范围授权内。

## 下游影响

| 声明/记录 | 处理范围 |
| --- | --- |
| `ProofTools.Paper.finiteExtension_descends` | 保持，已证合法页下降不受影响。 |
| 新6.20修正版第二段 | 可在已授权数学范围内新增公共接口；与原版区分命名、契约和来源范围。 |
| `FiniteExtensionNonliftableCrossing` | 完全不改。 |
| `FinitePageExtensionStretchingLaw` 及已证stretching实现 | 完全不改，不因本次修改重分配责任。 |
| 原6.21 | 不能自动声称新修正版推出原印刷6.21；如使用新的前提和结论须另核对。 |
| Main与其他模块 | 不接手其证明、不改其接口；调用新增上游时仍检查对象关联。 |
| API、契约、sources、待补记录 | 协调者在证明通过后按新修正版如实登记，不把旧版标成已证。 |
| Memo | 用户已要求，root已记录；本报告员只读，无新增写入。 |
| Tests | 正常公共消费、范围边界、接口/信任审计，由协调者统一整合；仍需source inventory和lake build。 |

## 阻塞范围与继续项

已授权范围可继续实施，无需重复询问用户是否删除差集。精确签名及数学源码核验已完成；剩余为协调者统一的公共登记、全仓检查和最终状态记录，不是数学范围授权。

可继续：worker补证、固定目标判据调用、实际代表与标签转换、合法页自然性、独立边界审查。不可擅自继续：修改stretching冻结接口、扩大ClassicalObject、增加axiom或待补责任、将原印刷命题标成原义已证。

## 人类审核记录

- 真实原话：“把差集条件先去掉”。发送者 guozhen，2026-10-17 15:06 UTC，群消息 `om_x100b620ca1ac9ca4c1bb712f5951ae8`，position1496。该话授权删除上述晚循环排除，不授权修改任意同名nonliftable谓词。
- 本聊天用户既有指令：“有回复就按他的意见继续补证”；本轮新增要求：“这个改动也写到memo里”。这些授权覆盖本轮修正版的补证和记录，协调者可执行。
- 随后交付的精确新Lean签名由本报告员独立核对，忠实落在上述已授权数学范围；没有另添数学假设或改变stretching接口。本报告没有伪造王老师对具体Lean源码的逐字批准。协调者可以继续正常整合，超出本范围的实质变更另记。

## 精确候选签名审查

已收到worker交付；当前已收到完整生产候选并完成只读审查。源文件`KIP126/ProofTools/Paper/ExtensionIndeterminacy.lean`，SHA-256为`1720fccd565456ad350d489a3da09eacecce316d5d9626077b71e5fdad71c34c`，审查快照`evidence/ExtensionIndeterminacy-reviewed.lean`；两条完整公共签名另存`evidence/reviewed-public-signatures.txt`。以下“通过”是独立语义/源码核对，不伪造王老师逐字阅读Lean代码的批准。

### 两个公共声明

1. `finiteExtensionCorrectionLabel`（191行）：`@[no_expose] public noncomputable def`。给定固定Standard模型中的X/Y/f、q、s/t、a:ℕ、`x : Ambient model X (s+a,(t−s)+(s+a))`，返回实际归一化源的q阶λ商E₂标签，三分次为`(s+a,(t−s)+(s+a),t+e)`。
2. `finiteExtension_inessential_iff_shorter`（300行）：给定同X/Y/f、rEarlier/rLater、n/s/t、同x/y的两个`FiniteExtensionWitness`、`rEarlier≤rLater`、晚witness.Essential，结论是早witness非本质 iff 存在a:ℕ、0<a≤n−e、早循环x′、实际早商E∞源z、该CorrectionLabel代表z，以及同一个早商normalized map长度n−a的TowerExtensionEquation到原`Wearly.target`。

该第二声明完整保留数学范围所需的前提。page≥2、e≤n、早页长度上界、原source/target cycles等已经由两个witness的字段提供，没有从公共类型里丢失。x/y的隐式类型由相同witness参数固定，未另选标准类。

### 代表、λ权重和目标绑定：通过

CorrectionLabel从实际未移位早商的`finiteTargetLabel ... a x′`出发，经`essShift (0,e)`和一个与商包含交换的`correctionShiftIso.inv`送入同一个normalized源。`correctionShiftIso_incl`从`quotient_shift_exists.choose_spec.1`证明与指定包含兼容；它不是任意同形对象替换。无曝光封装隐藏私有choose实现，没有改变公共数学对象。

`correction_label_exists`从任一该位置真实E∞源，逆向运输到未移位早商，调用真实`CrossingLabels.finite_grade_label`，得到`cycles(q−a)`中的经典x′及该标签的代表。前后degree equality只是整数相等的transport，最后通过同一个Q的hom/inv消去返回原z。没有传入“任选一个经典标签存在”的新假设。

RHS的target只有`Wearly.target`，通过`s+n=(s+a)+(n−a)`作索引transport。其map始终是`finiteExtensionMap model X Y f (rEarlier−1)`，stem=t−s、synthetic weight=t+e固定。没有任意y′，没有把短式改成较小λ商上的无层扩张。

`earlier_target_nonzero`在内部由`finite_target_rho`和`HasInfinityRepresentative.unique`导出晚目标的ρ像等于早目标，再用合法strip的`rho_infty_injective`传递非零。公共签名没有新增ρ目标相容或早target≠0前提。

### 必要/充分方向及边界：通过

必要方向先由晚essential与上段得到早target≠0。`inessential_length_strict`调用既有完整`minimal_length_finite_tower_no_crossing`和`target_nonzero_of_no_crossing`排除n=e；所以n>e且由早上界可得q=rEarlier−1>1。随后直接选a=1，将命中同一target的真实F^(s+1)代表投到同一早源E∞，再解码经典x′。短式允许inessential或零源首项，忠实于原写法未要求nonzero/essential的事实；实际`TowerExtensionEquation`仍保证源支持所写ESS微分，不能混同为已被d₀杀掉的源。

充分方向把任意F^(s+a)的短式实际源代表通过滤过单调性放入F^(s+1)，直接得到原早扩张的同target不定性。没有借用非lift性或晚短式。

n=e时RHS无正a，LHS也由上述最短长度论证排除；rEarlier=2必处于该边界，没有遗漏q=1。rEarlier=rLater是对原严格页差范围的有效加强：两witness具有同标签，晚essential迫使早target非零，同样证明适用；它不要求撤销原严格页差下的论文结论。

### 实际检查与未证依赖

Worker已报告对完整最终文件实际`lake env lean` exit0；成功日志快照为`evidence/worker-success-reported.log`，只见style warnings。本报告员依任务没有另跑lake build或写构建缓存，不能把worker日志伪称本报告员独立kernel复跑。

已只读检查完整生产证明体：没有sorry、axiom、新待补或从False消去的伪证明。读取`worker-dependency-audit.json`所得602个项目常量、28个直接上游sorry责任，来自普通module导入视图；其opaque封装隐藏部分上游proof-body，所以**只是依赖下界，不能作为最终完整闭包计数，也不能说只有28个上游责任**。精简快照`evidence/reviewed-dependency-summary.json`已明确标注下界。

随后独立审计使用`IndependentProductionAudit.lean`对当前全部数学模块`import all`，实际exit0。协调者转述的完整结果为：新iff定理的闭包822个项目常量、38个既有已登记上游直接holes；CorrectionLabel闭包567个项目常量、33个既有已登记上游直接holes。两者均无Main依赖、无ProofTools本地洞、无项目axiom、无未登记holes。以该完整视图替代602/28下界作为最终依赖口径；详细最终记录见同目录`audit.md`追加的完整实现/类型/实际运行记录，复现入口为`IndependentProductionAudit.lean`；审计员没有另存独立production日志或JSON，故本报告不虚构其路径。协调者全仓CaptureTrust再作交叉核对。

公理清单仍含sorryAx，来自这些既有上游责任，不能宣称整条标准模型证明完全无未证依赖。调用的最短长度链已读取到CrossingFinite的finite source/image bounds；没有调用新的6.20 iff或其6.21逆否结论，未发现循环。

`Language.lean`与`Laws.lean`在本轮审查前后哈希分别仍为`50164249c50b08c58a5357e1aec2ea6035dd8043474e71b69082b56eed9cd7ee`和`8731a608b3c750b044837c927ae45a8aee71eebdff441d89dd82df6b97f0732a`，原stretching谓词/法则未被本候选修改。

### 完成计数和来源版本：通过所述口径，待协调者实际整合

协调者拟在“用户要求公开的11项”清单中，将6.20标为`complete-revised`，已完成项由7变8；含义是**用户授权的修正版两段完成**，不是原印刷文本原义完成。

在“论文57项原文审计”中，6.20的印刷原句继续保留`partial`，另附`authorized_revision`记录新完整公共对应及修正版`complete`，并明确原差集必要方向未证/存在反例。这个双记录口径清楚地区分原文版本和修正版，符合如实记录；不能只把所有表中的旧状态一律覆盖成complete。

最终完整source inventory、普通公共消费、接口锁与trust审计、lake build由协调者统一完成。只有这些真实检查结束后，才可对外报告修正版已经完整整合通过；本报告不提前代报最终全仓构建结果。

## 协调者最终整合与验证

已完成公共入口、普通消费、接口新增记录和完整信任审计整合。默认 lake build 成功（3088 jobs）；source inventory 覆盖481个项目文件、28个消费/审计文件。原有113个导出记录逐项保持相同JSON值；新增2个显式公共声明及1个Lean生成支持声明。原299项直接待补清单、其他模块API及工具链/依赖锁均字节未改。完整CaptureTrust遍历与独立审计交叉一致：主iff闭包822、38个既有上游责任；label567/33；无Main或ProofTools本地证明洞、新公理、未登记责任。详见 validation.json 与 dependency-audit.json。

11项清单将6.20记为complete-revised，完成计数8（其中1项授权修正版）；57项原文逐条审计仍保留该印刷陈述partial，另记authorized_revision complete。未将修改后的数学陈述冒称原含差集版本已证。

群内已发送修正版陈述、双向证明要点与n=e边界核验，并回读确认：https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1499。
