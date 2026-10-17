---
issue_id: main-high125-detector-nonodd-20261017
responsibility_module: Literature
targets: [KIP126.Literature.Standard.tmf_high125_nonzero]
baseline_commit: 2c703812db7edb830b995c53e9fe648747a66429
worktree: /inspire/hdd/global_user/czxs25250150/Kervaire126Main
candidate_source_commit: null
api_file_and_sha256: metadata/literature-api.json / 9c4ecaf0ae66430ce1ed5e07cbf43851ebb762a7fa198207fb4c0ae22f26304f
source_file_and_sha256: KIP126/Literature/Standard.lean / bd23b61c2a2dafbdd801ff3d0af25a358284a67b14034418932aab3d3b0aeb6f
reporter_agent: /root/final_change_audit
independent_of_discoverer_and_implementer: true
evidence_level: primary-literature-supported candidate plus abstract filtered-group insufficiency; fixed-object proof unresolved
status: approved-implemented-and-validated-before-publication
human_decision: approved-option-A
---

# 高125 detector 图像非奇挠：接口加强候选

**当前状态：用户已明确批准方案A，生产实现与完整3080项默认构建均通过。下文待审/未实施文字是原始审查历史；当前精确结果见 approval.json 和 implementation-validation.json。最终提交及匹配缓存由 Git/Release 记录。**

本报告供协调者先核查，**暂不向用户发问**。只负责本目录的 report.md/proposal.json，不改生产、锁、检查或待补清单。报告者未参与本候选的生产实现，独立检索了实际公开类型与原论文，并与 `/root/independent_math_audit` 互通；候选由协调者指定，不将发现者摘要当独立证明。

## 请求人类决定的具体问题

建议讨论方案 A：将既有同名 Literature theorem 的结论由固定 `high125 ≫ tmfUnit ≠ 0` 加强为同一个图像的 `¬ IsOddTorsionMap`。它严格强于旧接口，可推出原非零；不新增公开前提、不更换对象、不新增导出，若继续保留既有直接待补则数量不增加，但它**确实改变公共类型、语义和该上游证明责任的强度，必须另获明确批准**。

此前用户批准的四项上游调整和单独 θ₅ 责任都不覆盖此项；当前没有对此项的批准。报告不能授权先填新 sorry、重刷锁或把 Main 缺口转移登记；以下只是待审精确候选。

## 原接口、背景与问题成因

固定命名空间 `KIP126.Literature.Standard`，源位置 `KIP126/Literature/Standard.lean:498`：

```lean
public theorem tmf_high125_nonzero :
  high125 ≫ tmfUnit ≠ 0
```

当前 exported capture 与 registry 的完整 kernel type：

```lean
Ne.{1} (CategoryTheory.CategoryStruct.comp.{0, 1}
  KIP126.Literature.Standard.high125
  KIP126.Literature.Standard.tmfUnit) 0
```

named universe parameters 为 `[]`；`Spectrum : Type 1`，Hom 宇宙 0，无额外隐式模型变量、前提或实例参数。`high125 : HomotopyGroup (C := Spectrum) 125 SphereSpectrum` 定义为**同一个**选定 `kappaBar : π₂₀S` 的四重乘积再乘**同一个** `wClass : π₄₅S`；`tmfUnit : SphereSpectrum ⟶ tmf` 是固定 `tmf_algebra` 的实际单位。`tmfIso` 与 `tmfUnit_agrees` 指定它与固定 model detector 及单位的关系。ordinary 球与完成球保持分离。

旧 theorem 本身是已登记 Literature pending-proof，指纹 `16606212098900527494`。本报告没有反驳它，也没有证明某个满足所有谱前提的 fixed high125 图像是奇挠。问题是 Main 当前从非零图像推断非零 associated-graded survival 时，旧论证使用了已被批准收窄的普通球全称零分离性：新分离性只能给无限滤过元素为奇挠。`x≠0` 无法排除非零奇挠；2-primary source 语境在压缩为当前 ordinary 单一非零声明后丢失了后续需要的强度。

实际原始迁移代码也暴露同一证明依赖：`Sources/Kervaire126Proofs.tar.gz` 内 `KIP126/Main/Solution/Computation/Tmf.lean:57–84` 的 `high125_nonzero_survival_of_computation` 显式接收 `ClassicalSphereSeparated H`，第82–84行用 F26 source 消失和 unit 图像非零反证。不能把旧代码成功编译当该 separation 在 ordinary sphere 上适用的证明。此快照保持原样，不回写历史。

## 真实前提与对象核对

| 条件 | 状态与真实边界 |
| --- | --- |
| 同一个 high125、单位、tmf 与 detector | 定义/比较均是当前固定常量；本候选保持关联。背景对象和具体比较仍有已登记上游待补 |
| high125 图像非零 | 当前公开直接待补，不是已完成来源证明 |
| high125 图像2-primary或非奇挠 | 未找到现有可直接调用公开定理；新候选正是补足后者的责任强度 |
| BMQ 是否讨论 ordinary/integral 所有主分量 | 原论文显式使用2-local语境；不能无比较地当作当前全整系数范畴的已完成识别 |
| κ̄、w 是文献的同一球类 | 当前有固定定义及mod-2检测，但真实来源选择/局部化识别仍待 producer 提供 |
| Main 实际待消失输入被2杀 | 固定 η 的2torsion可从既有 `toda_h0_eta` 与 `toda_lambda_h0` 及真实coherence推出；任意 η 乘积/choice差继承。不需要任意62-stem阶二 |
| 从 E∞=0 推 ordinary 类为零 | 不可用。新 classical separation只给奇挠；要用nonodd image或odd∩2torsion另行消除 |
| 有限 λ 商 separation | 已批准限于实际有限cofiber；不得升级未截断sphere separation |

## 独立文献核查与精确来源

BMQ：Mark Behrens、Mark Mahowald、J. D. Quigley，*The 2-primary Hurewicz image of tmf*，arXiv:2011.08956v4（20 Nov 2021），后刊 Geom. Topol. 27(7), 2763–2831 (2023)。本轮实际打开并搜索 [原论文 PDF](https://arxiv.org/pdf/2011.08956)，定位：印刷p.2的全篇2-local约定，p.4的κ̄/w命名与球像关系，p.47 Corollary 7.5列出的 κ̄⁴w∈π125(tmf) Hurewicz像。该结果支持2-local图像方向；同一项目常量的运输尚未完成。不是由标题或二手引文猜测。

若当前 tmf 是 ordinary connective tmf，证明新结论可通过其**实际2-local化映射**进行：odd-torsion元素的局部化像为零；若 fixed high125 的同一个单位像局部化后等于 BMQ 非零类，便不能是odd-torsion。若项目选定tmf已为2-local对象，则须证明同一对象的odd multiplication可逆及非零类识别。两条路线都不要求把ordinary sphere悄换完成球，也不能仅凭抽象tmfIso宣称与文献模型已识别。

本地论文 `AimPaper/main.tex:2342` 使用高类的tmf检测，并引用BMQ；这是下游用途定位，不独立提供上面的固定类/单位/localization比较。`AimPaper/main.bbl:48–51` 记录原始书目信息。所需producer仍需实际构造；本报告不把文献假设当已完成Lean证明。

## 独立证据与复现

### 公开接口检索

只读扫描 Literature、AdamsSynthetic、Computation 的公开源码、三个API清单，以及现有普通导入 exported kernel capture；精确结果见 `/tmp/kip-main-high125-interface-search.md`。κ̄、w、high125没有有限2power阶接口；tmf有π62消失、负同伦消失、有限mod2同调type、低滤过63页及br21微分，但没有π125排奇挠或`HomotopyTwoLocal tmf`。不能从这些不同度数/不同检测对象结果补出新结论。

### 缺口的最小抽象过滤例

G=(Z/2)a⊕(Z/3)h；F_s=G（s≤25），F_s=(Z/3)h（s≥26），选定 source=a+h，detector是到Z/3的投影。则source图像非零；F26及无限滤过均为奇挠；Gr25=Z/2且source有非零leading grade；实际a是非零2torsion F15元素、detector(a)=0。因此“source图像非零+tail只含奇挠+实际输入2torsion”不足推出detector在该输入单射。这个例子**仅检查过滤群推理的信息强度**，没有构造项目固定谱、κ̄/w乘法或所有同调前提，绝不能称原接口反例或新候选已假。

### 新结论严格推出旧结论

零图像属于`IsOddTorsionMap`（取n=1）。因此`¬ IsOddTorsionMap x`蕴含x≠0。形式化只需固定x、1为正奇数、1•0=0，不依赖Main或其它争议接口。反方向在Z/3非零元素上失败，故变更确实加强责任，不能当“只是补证明”。

### 实际运行与依赖

实际命令包括rg、sed/cat、Python JSON完整类型检索、tarfile只读读取上述历史源码、SHA-256。web执行search/open/find到BMQ原PDF；PDF screenshot调用已返回引用，但图像未呈现给本报告者，故本报告**未声称视觉核验Figure1.1图上某点**。没有运行Lean/Lake，没有写共享缓存，没有形式化固定对象反例。

未用旧sphere无限分离性、任意synthetic62-stem阶二或Main目标自身导出新事实。候选证明尚未实现，完整可编译kernel type/fingerprint尚未产生，以下拟议类型不可用旧指纹覆盖。

## 方案及精确差异

### A：同名加强（建议先供协调者讨论）

```lean
public theorem tmf_high125_nonzero :
  ¬ KIP126.AdamsSynthetic.IsOddTorsionMap (high125 ≫ tmfUnit)
```

候选在当前固定对象上的预期完整kernel类型（尚未运行Lean生成新指纹；没有新增level参数）：

```lean
Not (KIP126.AdamsSynthetic.IsOddTorsionMap.{1, 0}
  (CategoryTheory.CategoryStruct.comp.{0, 1}
    KIP126.Literature.Standard.high125
    KIP126.Literature.Standard.tmfUnit))
```

这里 `IsOddTorsionMap` 实际公开定义的完整kernel类型已从现有普通导入捕获独立核对：

```lean
{C : Type u} →
  [inst : KIP126.StableHomotopy.StableHomotopyCategory.{u, v} C] →
  {X Y : C} → Quiver.Hom.{v, u} X Y → Prop
```

该定义level parameters为`[u,v]`、指纹`15645126546111667274`，定义在`KIP126/AdamsSynthetic/AdamsFiltration.lean:93`。候选使用`.{1,0}`，隐式C是固定`Standard.Spectrum`、实例是固定`Standard.spectrumCategory`，X是`Sphere (C:=Spectrum) 125`、Y是同一`Standard.tmf`；没有遗漏cofiber实例前提（该谓词实际kernel类型并不需要它）。

类型完整语义为：对同一个 `x := high125 ≫ tmfUnit : SphereSpectrum⟦125⟧ ⟶ tmf`，不存在 n:ℕ 满足 Odd n、0<n及n•x=0。固定对象、度数、宇宙、名称和前提不变；结论严格加强。旧nonzero可在Main私有adapter中由n=1导出，避免新增公开helper导出。

若获批后仍作为上游已登记pending结果消费，同一名字/责任的数量变化为0；但清单必须记录真实新类型/指纹与更强来源要求。**待补数量不增加并不等于无需人审**。不得假称旧证明支持新结论，必须保留它的未完成producer状态。

### B：保留原类型，新增精确nonodd公开定理

```lean
public theorem tmf_high125_nonodd :
  ¬ KIP126.AdamsSynthetic.IsOddTorsionMap (high125 ≫ tmfUnit)
```

优点：保留旧消费者类型和命名语义；新增结果名字清楚。代价：新增一个公开导出；若没有真实独立证明就登记pending，则新增一个Literature直接责任，需显式授权。可在获准实施时把旧nonzero改为由新结果推出，从而旧直接责任消除、总直接计数净0，但这仍是责任重新组织而非自动授权，必须精确审核新旧依赖且不循环。

### C：接口全部保留的真实内部证明

继续构造同一tmf局部化比较、单位与指定κ̄/w像识别，用BMQ证明nonodd并作为Main私有引理调用。这保留接口，若无新hole则无需新增责任；本轮检索没有现成公开输入支撑立即完成，但也没有证明不可构造。若选择此路，不能把Main目标结论装成结果包或添未授权假设。

相比“source high125有2power阶+image nonzero”，A需要的nonodd image更弱：前者可推出后者，后者不要求source自身没有可加的奇主分量。相比“tmf整个π125没有奇挠”，A只约束同一指定图像，影响更小。

## 下游2torsion有限尾路线与仍需证明的步骤

以下是**有条件的局部重构路线，不是已完成证明**：

1. 从现有页表将classical source high125在F26推进至所有滤过；用修正classical_sphere_separated得source odd。组成同一个tmfUnit保持odd，和A矛盾，从而建立同一highClass的nonzero survival。此步骤不需要source high125的2power阶。
2. 在F25分支，用已有prescribed lift选择b，其realization精确为同一high125；a和λ20b有相同leading detector，故差在F26。需要真实filtration-to-realization运输（或等价逐层λ除法/经典检测论证）得realized difference为odd。detector(a)=0后，此odd差的单位像等于±指定high125图像，于是和A矛盾。**不需要把差直接证零，也不需要b为2torsion。**
3. F26分支的实际a是ηproduct或choice差，已有2torsion来源。若同一运输得realize(a) odd，加性保证它被2杀，因此realize(a)=0。再用现有selected_realization_kernel取得某个有限λ幂消去a，结合每个实际有限λ商尾部消失、所需λkernel/除法的真实级数和同一witness，完成a=0或当前论文所需的有限表达消失。**不能仅由“所有有限商像为零”直接推出未截断a=0。**
4. 这里的filtration-realization运输和有限λkernel消除尚须Main本地证明，当前搜索未找到可直接调用的通用公开运输结论。A只修复来源强度缺口，不豁免这些剩余步骤。若它们不能闭合，继续标未决，禁止新增Main sorry或重新使用原错误无限分离性。

现有η阶二输入为`Standard.toda_h0_eta : h0·eta=0`和`Standard.toda_lambda_h0 : λh0=2`，同一coherence保证2eta=0；此链独立于high125候选和目标，不形成循环。Main最后公开结论及标准h6²对象不因此增加前提。

## 下游影响与验证计划

生产直接消费者目前只有 `Main/Internal/High125/Source.lean:48,60`。前者high_nonzero_survival应改为source odd⇒image odd矛盾；后者high125_detector_nonzero可用n=1私有adapter或更强nonodd版本（该Main内部声明默认私有）。不能让旧nonzero应用把odd witness错当zero。

传递影响：High125.Injectivity、ChoiceIndependence、DifferentialCriterion及主永久存活目标。实际η乘积/choice差可用局部2torsion重构；现有任意a的强detector-injectivity中间引理若不必要可私有缩小，而不改变公开Main目标。

若人审批准A：协调者串行更新 Literature API锁、contracts、sources、原同名待补责任的完整类型/哈希及授权记录；保留当前来源历史。普通import消费者、Literature trust、Main/ProofTools模块、完整source inventory和lake build均须实际通过后才能报完成。与此无关的Computation并发工作、Mathlib/toolchain/依赖锁、旧审查原证据不在批准范围。

## 阻塞范围与继续项

阻塞的是依赖source非零leading survival和高125detector注入的Main局部闭包；没有证据冻结不相关模块。可以继续现有有限商分离性适配、同一witness/coherence证明、η2torsion和local filtration运输研究。此报告不批准候选，不修改当前可调用接口，不请求用户立即决策。协调者先核查来源识别及下游路线是否足够，再将具体方案呈现人类。

## 人类审核记录

`human_decision: null`。本报告没有获批；此前“同意以上提案，修改原接口”及“允许新增这1项待补”对应的具体目录/θ₅责任均已记录在另一审批记录，不得外推到这里。

## 当前读取源码 SHA-256

- `KIP126/Literature/Standard.lean`: `bd23b61c2a2dafbdd801ff3d0af25a358284a67b14034418932aab3d3b0aeb6f`
- `KIP126/AdamsSynthetic/AdamsFiltration.lean`: `12dcb22b5fe2aa4804f0a32bacaea9ffaa227eb22c4e2f47c92a2b00b46964bf`
- `KIP126/Main/Internal/High125/Filtration.lean`: `9afc54c92e4a799086d0cd491428b65a9e6a51dabf7aaf6d69d8a6f39cbc30ba`
- `KIP126/Main/Internal/High125/Source.lean`: `183e7a9bf4ea394a526c83986d0b0318e971737e738a872e3d4731f80b87a82a`
- `KIP126/Main/Internal/High125/Injectivity.lean`: `1f61501126f5079475a2c25ac897e6b296de322cb518495d4a4a1b698078b0ff`
- `metadata/literature-api.json`: `9c4ecaf0ae66430ce1ed5e07cbf43851ebb762a7fa198207fb4c0ae22f26304f`
- `metadata/proof-obligations.json`: `bc390df37bb141eb30f5bb04d030fcbb7253378677007866a65f72eecf200ca2`
- `AimPaper/main.tex`: `828ee5a5aa06e1f390b036a043230ed417446fa7be11a4e27eecc4a565135c4b`
- `AimPaper/main.bbl`: `bab55d90e78aa1910e086c0b811be5113eea2470af20e4eb3bf1e26e9d8f6675`

历史tar内Tmf.lean SHA-256 `76a15e2eb42e295edbed29ee1809791f234186d4e8d974a41ee0b4d576d0bc88`；SourceLanguage.lean SHA-256 `8fa4634e7d40f2baf4ea1060bddeda727d5683a06b8e17b822b65a7c53193abd`。保留原tar，不覆盖证据。

## 协调者后续类型表达式核验

协调者已把方案A结论仅作为私有 `Prop` 值定义实际交给固定 Lean 检查，退出0；候选表达式无 sorry 或未解元变量，type fingerprint 为 `5689349671372562828`、named universes为`[]`。证据保存于本目录 `evidence/kip-high125-proposed-type.{lean,log,json}`。这仅核验候选类型表达式，不证明该事实、不改变生产 theorem、API锁或原责任，也不代替用户批准。前面的“尚未运行Lean”描述的是独立报告者交付时的状态。

## 后续明确用户批准

用户在本对话明确批准方案A：

> 同意将 tmf_high125_nonzero 加强为同一个像非奇挠，不增加待补数量。继续修 Main，完整构建通过后 commit 并 push，同步 Release 构建缓存。

本项状态更新为获批实施中。前文 pending/未获批记录保留为历史，不再代表当前授权状态。保持原名、原固定像与同一 Literature 直接责任，责任数量不增加；完整构建、提交、推送与 Release 缓存同步仍须实际执行。

## 获批实施与完整验证

同名声明已在相同 high125、tmfUnit 和 tmf 对象上加强为非奇挠，实际类型指纹为 `5689349671372562828`。Literature 精确导出仍773，唯一新增类型变化即本声明；Literature119项、总299项、Main0项直接责任均保持。默认 `lake build` 已实际退出0、3080 jobs；Main17个命名公共根的1565个Main证明节点和32个实际ProofTools交接点通过全部严格审计，旧MH2/GL未回流。原33项记录仅有1项旧辅助不再直接消费，独立核对后保留历史并从当前精确数组移除，审计代码未改。Main的18个公共导出及其完整类型/宇宙/信任保持不变。

独立全体证明观察亦已完成：467个数学模块、12044个常量，299项直接责任的完整类型和证明体指纹逐条匹配登记，无synthetic sorry或项目新公理；主目标实际闭包4672节点，仍依赖177项已有上游责任，Main/ProofTools无直接待补或旧MH2/GL依赖。最终独立审计详见集成目录 evidence/kip-main-final-authorization-audit.md。本记录止于发布前验证，实际最终提交与缓存见Git历史及对应build-cache Release。
