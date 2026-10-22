---
issue_id: E2Computation-migration-coordinate-bindings-20261019
title: 旧商环关系证书迁移所需的固定生成元识别
summary: 上轮三条关系已固定接口解决；本轮 h2_rel2 已生产集成并通过局部内核检查，默认完整构建通过、独立实际依赖审计通过并保留登记上游；仅另三条仍需新内部证明桥。不请求接口修改。
responsibility_module: E2Computation
targets:
  - KIP126.Computation.Table.h0_obstruction_rel0
  - KIP126.Computation.Table.h0_obstruction_rel1
  - KIP126.Computation.Table.h2_obstruction_rel0
  - KIP126.Computation.Table.h2_obstruction_rel1
  - KIP126.Computation.Table.h2_obstruction_rel2
  - KIP126.Computation.Table.theta_h5_generator84_zero
  - KIP126.Computation.Table.theta_h5_generator85_zero
baseline_commit: ef01dcfd904b51fe2288f0dc3e1eed074591967f
worktree: /inspire/hdd/global_user/czxs25250150/ops/tmp/main-followup-20261019
candidate_source_commit: 71e63c47d1be7ebad1589bd08a598179e468f23b
api_file_and_sha256: interface/baselines/e2-computation-api.json b6da08b20f73640c5f7847d6109ffe3426e5ff760f23f941ceefacf4e3779cdd
source_file_and_sha256: KIP126/E2Computation/Standard.lean e3d0c252644f9d216ad1e1fa92b894457b6db112d699dbd2fe2e7d68115186e2
baseline_source_file_and_sha256: KIP126/E2Computation/Standard.lean 32ab999ceb76b426813841e17e6131c51502f3ad29d7cb25b53ca0d2f98772fa
reporter_agent: /root/interface_report
independent_of_discoverer_and_implementer: true
evidence_level: 上轮生产及依赖审计通过且继承已登记上游责任；本轮 rel2 生产单文件检查与独立探针退出0，默认完整构建通过、独立实际依赖审计通过并保留登记上游；三项新桥未完成，无固定对象反例
status: pending-human-review
human_decision: null
blocking: 三条关系仍需新内部证明桥；h2_rel2 已集成、局部内核通过，默认完整构建通过，独立实际依赖审计通过并保留登记上游；不必先证明已登记 rel1。
resolution: 保留原接口；已集成 rel2 直接消费已登记 rel1 和原生 Atom 关系，保留其上游待补；另三条继续内部补证。
---

# 固定生成元的迁移审查报告

## 请求人类决定的具体问题

当前无需新的授权。用户对本 session 的明确限制是“把这些迁移回来，保持公共接口不变”。本报告确认尚未完成的内部识别证明，**没有证明任何当前公共命题为假，也没有提出必须修改公共接口的方案**。`pending-human-review` 只表示本独立报告尚无人审决定，不要求暂停保持接口不变的补证。

如未来发现内部构造确实不能满足既有语义，才另交可审阅的精确修改方案。本报告不以 agent 意见授权重选固定生成元、增加下游假设、增加公理、移动责任或修改接口锁。当前七项签名及对象关联原样保留。

## 2026-10-20 路线集成阶段：rel2 已写入生产，最终验证通过且继承登记上游

本次状态更新由独立报告员 `/root/route_status_report` 核对。当前集成基线为 `ef1c6c718075659f68c6beaf0aae09937d2a4c25`；原报告的 `ef01dcf` 基线、完整原接口和历史证据不改写。生产 `KIP126/E2Computation/Table/Relations.lean` 的 SHA-256 为 `ac770f198e8764d6999423ccd2eb2e5878ed8d41aae851aec4ce0f1bd5b5e5b8`，`h2_obstruction_rel2` 的直接 `sorry` 已替换。报告员逐字核对原公开签名与当前签名，未改名称、类型、前提、固定 generator89、次数、页或责任；新增私有导入仅限 E2Computation 内部。

报告员独立读取了实际生产证明、同一原生商环中的 `h2Relation2`/`h2Relation859` 及生产单文件检查日志；局部检查退出 0，日志仅余 `h0_obstruction_rel0`、`h0_obstruction_rel1`、`h2_obstruction_rel1` 三项原有直接洞。独立 countercheck 的通用环探针也退出 0，其公理仅 `propext`、`Quot.sound`。这些检查由 worker/独立审计员执行，报告员读取其源码和日志，没有亲自重跑编译。完整实际目标仍通过同一 `comparison` 运输，因此继承 rel1、比较、模型等已登记责任；通用环探针无 `sorryAx` 不能用来声称完整生产目标已无待补依赖。

包含全部十一项的八数学入口构建、八模块 API、原214项表达式核对及默认完整构建均已通过，当前清单为203；独立实际十一目标依赖审计已通过并保留登记上游。当前 rel2 状态为 **`resolved-by-fixed-interface-proof`**。准确范围见下节。上轮默认构建和 8383 常量闭包只作为其原输入的历史证据保留，不能充当这轮新源码的验收。

剩三条关系的新内部证明可继续，已登记上游可直接调用；本次不请求接口变更、人审重新授权或全局暂停。可随提案读取的集成摘要见 [本轮证据](evidence/reassessment-20261020.json)，原候选源码/日志仍保留。大型本地会话日志位于 Git 忽略的 `local-history/proof-sessions/route-integration-20261020/`，仅作本地证据，不伪造网页链接。

### 本轮最终捕获、清单与完整构建通过

本轮最终公开捕获和清单核对现已完成：八个数学入口普通导入后的全部导出、完整渲染类型、宇宙参数及实际定义源模块均与原基线精确相同，八份 API 锁文件逐字节不变。报告员独立比较了八份锁与 `ef1c6c7`；实际捕获和原214项 kernel 表达式比对由协调者执行，报告员读取其结果。原214项完整 kernel 类型全相同，恰好11项直接责任完成；其余43项仅 Lean 的诊断 sorry 标签变化，经完整表达式解析比较后才刷新证明体指纹，其余待补字段未改。清单现为 **203**（AdamsCalculations 5、AdamsSynthetic 72、E2Computation 15、Literature 110、ProofTools 1；133项证明、70项构造）。本地责任完成仍继承登记上游，不能称为无 `sorryAx` 闭合。

包含全部十一项的八数学入口构建已通过3436任务；源码清单核验554个项目文件及35个消费/审计文件，依赖方向和私有导入边界通过。默认完整 `lake build` 已实际退出0，以 **`Build completed successfully (3580 jobs).`** 结束，全部既有消费、八模块信任审计、`Tests.Trust`、Main 公开根/ProofTools边界/Nu9回归均保留并通过。该构建由协调者执行，报告员独立读取最终成功日志；独立实际十一目标闭包随后已通过，准确范围见下一节。准确摘要见本报告既有证据 JSON；大型当前日志为 Git 忽略的本地会话材料。

### 剩三条关系的当前产物辅助探针：通过不等于完成目标

三份研究探针已使用本轮当前产物、普通公共导入、无 overlay、无 `-o` 各退出0，报告员读取了源码及 `RemainingThreeCurrentChecks.json`：完整 `(13,135)` 上 h₂ 作用恒零；h₀ 从源 `(10,72)` 到 `(11,73)` 在指定坐标中是 **`(x₀,x₁,x₂) ↦ (x₀,x₁)`**；原完整 rel1 等价于固定 h₂·Md₀ 在目标坐标等于 `Finsupp.single 1 1`。后一项不调用 rel1 或 rel2 自身，给的是等价归约，**尚未证明该坐标条件**。

特别是 h₀ 的核是一维第三基方向，已有非零见证；不能记录为核零或单射。这些局部结果仍继承 `sourceCoordinates`、`sourceBasis_values` 等原登记责任；全分量 h₂ 消去还调用登记 rel1。它们支持进一步研究，**不是再完成三项公共目标**；本轮清单只移除前述11项。准确源/产物哈希、命令与空日志记录见 [本轮证据摘要](evidence/reassessment-20261020.json)。

### 本轮独立实际依赖闭包终验通过

独立证明审计员使用本轮当前已构建产物的全源码正文 collector，实际退出0，捕获 **8442** 个项目常量和本轮全部 **11** 个目标；随后按最终203项清单的 analyzer 全通过。报告员实际读取并逐项核对 `closure-summary.json`、`closure-summary.log`、`project-dependency-cycle-check.json` 与 collector 日志，没有重跑审计，也没有用旧 overlay 预检代替此次结果。

十一项完整 kernel 类型表达式、类型指纹、宇宙、公开导出及实际源模块责任与原基线相同，十一项本地直接洞均已消除。全部可达直接洞同时在原214项和当前203项清单登记，完整类型原样；真实项目公理、synthetic sorry、缺失项目正文依赖、目标循环及 Main/Geometry 反向依赖均为0。完整项目依赖图8442节点全部可拓扑移除，无循环残余。

最终结论为 **`passed-with-registered-upstream-obligations`**：本地固定接口补证及其实际依赖登记通过验收，**不表示全证明的未证输入已经闭合**。同一实际闭包中，E6 生存仍继承58项登记上游、product detection 38项、bx 等价34项、六个 BHS 包装各30项、sourceReplacement flatness 6项、rel2 33项；各目标仍含 `sorryAx`。这些计数是各自可达上游集合大小，不能相加作为全仓责任数。准确摘要和当前源/证据哈希见 [本轮证据](evidence/reassessment-20261020.json)，旧阶段证据继续保留。

## 2026-10-20 盘点阶段：rel2 保接口候选（历史记录）

盘点阶段生产源码、公共接口及待补清单未改，登记 **214** 项；当时上轮五项本地补证尚未提交，worktree 以 `ef01dcf` 为 HEAD。协调者当时说明 main `06159aa` 仅有文档变化。该阶段结论与下列原探针证据保留为历史记录；后续五项已形成 `ef1c6c7` 提交，本轮生产集成状态以上节为准。

本报告员独立读取本轮审计的完整六项原因及 `H2Rel2Reviewed.lean`/日志，确认此前“剩四条都缺固定坐标桥”的概括过强。**`h2_obstruction_rel2` 改为 `candidate-kernel-verified-not-integrated`**：原目标仍是实际 E₂ `(13,75)` 上的 h₀³ 乘同一个 `generatorImage 89 10 72` 等于零；没有改名称、签名、前提、固定对象或结论。

候选先用同一 `value_comparison` 和 `comparison 11 73` 的单射性，把已登记 `h2_obstruction_rel1` 变为原生源代数中 `X2*X79 = X0*g`，其中 `g` 是现有 `sourceValue (.generator 89 10 72)` 的值。然后乘 X0²，使用已证原生 Atom 关系 `h2Relation2 : X1^3 + X0^2*X2 = 0` 与 `h2Relation859 : X1^2*X79 = 0`，得到 X0³*g=0，最后经同一个 `comparison 13 75` 搬回原完整目标。它不要求 `g=X89`，不调用 rel2 本身、下游结论或 `False`。

原探针 `local-history/reports/comprehensive-proof-inventory-20261020/e2/H2Rel2Probe.lean` 以及独立复跑副本 `local-history/reports/comprehensive-proof-inventory-20261020/independent-review/H2Rel2Reviewed.lean` 均报告 `lake env lean`（无 `-o`）退出 0；本报告员读取副本和实际 axiom 输出，没有重跑编译。依赖为 `propext`、`Classical.choice`、`Quot.sound`、`sorryAx`，后者来自 rel1/比较/模型等已登记责任。候选不新增公开前提，**无需先完成 rel1 的证明**；集成后仍必须保留 rel1 的传递待补并保持未来证明依赖无环。当前只是候选验证，不能把生产直接洞或清单数提前减少。

准确本地来源：`local-history/reports/comprehensive-proof-inventory-20261020/independent-review/report.md`、`six-reasons.json`、`candidate-reviews.json`；均为 Git 忽略历史材料。可随正式提案读取的局部证据为 [本轮审查摘要与源哈希](evidence/reassessment-20261020.json)、[候选完整源码](evidence/reassessment-20261020-h2-rel2.lean)、[独立探针 axiom 输出](evidence/reassessment-20261020-kernel.log)。这些不是新增平行提案或论文修正记录。

剩三项新内部责任分别为：`h0_obstruction_rel0` 需证明 h₀ 消去当前 `(5,36)` 选定向量，可研究整分量或乘法核；`h0_obstruction_rel1` 需当前两侧选定表达式在 `(14,139)` 的精确乘法比较；`h2_obstruction_rel1` 只需识别 h₀*g89 的像与固定 h₂*Md₀，模 ker(h₀) 的识别已经足够，不必追求生成元完全相等。`sourceBasis_values` 的所有乘积约束应当使用，不能仅看 singleton 的自指特例而忽略全体约束。

所有已登记 `comparison`、`comparison_product`、`sourceCoordinates`、`sourceBasis_values` 均可按依赖方向直接调用；它们自身待补不是下游暂停理由。这里“未决”表示新局部证明尚未完成，**不是不可证明或接口必须改型**。本轮未建立六目标中任一固定对象反例。更广的候选由协调者本地盘点维护，本提案不复制其其他模块清单。

## 上轮固定接口补证进展（2026-10-19，状态由上节更新）

| 目标 | 本次独立复核后的状态 | 尚存责任 |
| --- | --- | --- |
| `theta_h5_generator84_zero` | `resolved-by-fixed-interface-proof` | `comparison`、`comparison_product` 等已登记实际页上游责任仍保留 |
| `theta_h5_generator85_zero` | `resolved-by-fixed-interface-proof` | 同上；不要求证明 generator84/85 等于原生 X |
| `h0_obstruction_rel0`、`h0_obstruction_rel1` | 迁移桥未补 | 现有固定生成元的原生识别或不变关系证明 |
| `h2_obstruction_rel0` | `resolved-by-fixed-interface-proof` | 完整原生/枚举/运输证明已生产编译通过；比较接口的传递责任保留 |
| `h2_obstruction_rel1` | 内部证明桥未补 | 只需 h0 像的标定或等价商类识别；原生生成元完全相等是更强的充分条件 |
| `h2_obstruction_rel2` | `resolved-by-fixed-interface-proof` | 同一生产目标的直接 sorry 已替换；已登记 rel1 及比较的传递责任保留，完整构建通过、独立实际依赖审计通过并保留登记上游 |

已独立检查新增 `Table/Internal/ThetaAnnihilation.lean` 及修改后的 `ThetaRelations.lean`。新私有证明先完整枚举自由多项式中权为 `(7,70)` 的 **33 个单项式**：`enumerateMonomials_complete` 用全部生成元 s 权为正保证递归穷尽，`thetaCandidates_complete` 覆盖所有可能支撑，`thetaEnumeration` 核对固定列表。**20 条原生定义关系**逐项消去它们乘 h₅ 的积；加法、标量与加权齐次归纳把结论提升到每个 `sourceData.component 7 70` 元素。这里使用整个同次分量的表示性质，没有声称这些 33 项是商环基底。

随后 `thetaActualZero` 对任意实际页 `generatorImage id 7 70` 取 `comparison.symm`，用上述全分量零乘法和 `comparison_product` 搬运回实际页。故即使固定 `sourceGenerator` 是坐标选择，两个 theta 结论也成立；无需 generator84/85 与原生 `X` 的识别。这正是原报告已列出的“不变关系证明”路线的完成实例。公共名称、完整签名、对象关联和导出没有改变，也没有增加前提或公开声明。

新增私有 helper 无 `sorry`、新公理、`False`、`sourceCoordinates`、`sourceBasis_values`、`sourceGenerator` 或实际比较接口引用；所用原生关系辅助引理确为理想成员证书。不能由此断言最终公共定理已无 `sorryAx`：实际页运输仍使用已登记 `comparison`、`comparison_product`，而 `generatorImage` 对象项本身仍可包含坐标构造。没有使用 theta 目标自身、Main 结论、ProofTools 或后续 Adams 计算，因此此路线没有把本项责任绕成循环。

协调者在本 session 的明确工具记录确认两个命令均退出 0：

```sh
lake env lean -o .lake/build/lib/lean/KIP126/E2Computation/Table/Internal/ThetaAnnihilation.olean KIP126/E2Computation/Table/Internal/ThetaAnnihilation.lean
lake env lean -o .lake/build/lib/lean/KIP126/E2Computation/Table/ThetaRelations.olean KIP126/E2Computation/Table/ThetaRelations.lean
```

记录出处分别是协调者工具 session `2747`、`20790`，均 exit 0；空编译日志表示没有错误/警告输出。本报告员进行了独立源码与数学依赖复核，**没有重新编译或独立运行完整 axiom closure**；实际编译成功与核验范围据此分开记录。当前文件哈希、目标签名同基线比较、33/20 计数及实际静态检查结果见 [theta 解决证据](evidence/theta-resolution-audit.json)、[证明摘录](evidence/theta-resolution-excerpts.txt)。独立静态复现命令为：

```sh
python3 interface/proposals/E2Computation/migration-coordinate-bindings-20261019/evidence/theta-resolution-reproduce.txt
```

### H₂ 固定接口证明复核（生产编译及核心构建通过）

当前已安装 `Table/Internal/H2Annihilation.lean` 与 `Relations.lean` 中 `h2_obstruction_rel0` 的固定签名证明候选。独立检查其链条为：候选生成元覆盖所有可能的 `(13,135)` 支撑；完整通用枚举在 fuel 13 下覆盖每个自由齐次单项式；带缓存裁剪的前缀检查由 `trimPrefixCheck_sound` 证明对应完整枚举，gate 的提前结束有单独 `h2IndexedGate_sound` 证明。所有命中零因子的项经子排列/整除消去，例外项用多项式关系组合及特征 2 算术消去，最后经齐次归纳得到任意 `sourceData.component 13 135` 与 h₂ 的乘积为零。

实际页证明对现有 `generatorImage 407 13 135` 取比较逆像，再调用该全分量消去和 `comparison_product`；因此候选同样绕开了 ID 407 的原生 X 识别。完整公开签名与基线逐字核对一致，helper 都是私有，没有新增公理、`sorry` 或坐标构造调用。源码有一处 `False.elim`，位于过滤枚举证明，用同一布尔谓词的局部否定与已给出的成立证明消去不可达分支；它不是从项目数学假设矛盾取证。

协调者随后明确提供生产验证结果：H₂ helper（约 417 秒）、`Relations`、E2 及本轮五个目标的生产编译均通过；`lake build KIP126.Geometry` 退出 0，共 3435 个构建任务。因此本项更新为 **`resolved-by-fixed-interface-proof`**，此前 `candidate-pending-final-build` 只保留在历史检查记录中。theta 两项也维持已解决。`comparison`、`comparison_product` 的既有上游待补持续保留。协调者随后提供默认完整 `lake build` 退出 0 的工具结果，日志以 `Build completed successfully (3580 jobs).` 结束；报告员独立读取了该日志。现有审计同时通过：E2 8567 个声明/16 项已登记待补/无项目公理；Main 1922 个声明/0 项本地待补；34 个 ProofTools 边界及 `Tests.Trust` 全通过。**这是协调者执行的构建，报告员未亲自运行；独立扩展闭包审计现已退出 0，状态为 `passed-with-registered-upstream-obligations`；具体限制见下节。**另两条 T 非整除的生产成功来自协调者整合结果，不纳入本报告的独立数学审查范围。

[H₂ 候选独立证据](evidence/h2-candidate-audit.json)记录检查时的源码 SHA-256、私有性、目标签名一致性与静态计数；[关键证明摘录](evidence/h2-candidate-excerpts.txt)给出枚举 soundness、齐次延拓与实际运输的代码。原候选证据是源码核验；当前通过状态另记录于 [生产检查点记录](evidence/production-checkpoint.json)，生产与默认完整构建结果由协调者执行并提供，报告员独立读取 [完整构建日志摘录](evidence/final-full-build-excerpts.txt)；扩展闭包审计已通过但保留已登记上游责任。

上轮默认完整构建通过时，本报告仍有四条 E₂ 关系及另份 Cν 报告中的两个直接洞；其后 rel2 的生产集成状态以上节为准，不能把该旧构建当成本轮新源码的验证。既有 `pending-human-review`/`human_decision: null` 表示本报告尚无人审决定；构建成功不是接口变更授权。

### 最终扩展依赖审计状态

独立证明审计员的最终 collector 退出 0：遍历 8383 个项目常量，11 个原目标的完整类型/宇宙参数/导出/源模块责任均与基线一致；八份 API 文件逐字节一致。项目公理、synthetic sorry、目标依赖循环、缺失项目依赖及未登记直接洞均为 0；501 个新增证书族常量无本地洞或项目公理。全部直接洞同时在原 219 项与当前 214 项清单登记。该结果记为 **`passed-with-registered-upstream-obligations`**。

五个本地补证仍分别继承已登记上游洞：theta84/85 各 32，`t_not_h0_multiple` 为 35，`t_not_h2_multiple` 为 36，`h2_obstruction_rel0` 为 32；它们的最终公理依赖仍含 `sorryAx`。因此本地责任移除和接口保留通过审计，**全证明的信任依赖尚未闭合**；仍需完成既有比较、范畴等上游责任。T 两项这里只同步最终审计状态，不扩大本报告独立数学审查范围。

结果由独立证明审计员产生并经协调者提供；报告员读取其最终结论，没有重新运行 collector。准确来源为 Git 忽略的本地材料 `local-history/reports/migration-proof-audit-20261019/verdict.json` 和 `local-history/reports/migration-proof-audit-20261019/report.md`（以文件开头的 final 结论为准，后文历史 interim 记录保留）。这些路径标为本地证据，不伪造发布后的网页链接。[生产检查点](evidence/production-checkpoint.json)同步摘要。该审计快照仍保留四条 E₂ 关系和两条 Cν 直接洞；本轮 rel2 后续已集成，不能把六项一概视为同一种阻塞，人审 `pending-human-review`/`human_decision: null` 保持原样。

### 当前源码与构建记录的边界

独立审查时的 `Standard.lean` SHA-256 为 `7b88e15e00019384dbbd46f4fe28bb502fac1d4547a90495b35b12faa65c1f7c`，既有证据仍对应该审查快照。主线整合版本的 SHA-256 为 `e3d0c252644f9d216ad1e1fa92b894457b6db112d699dbd2fe2e7d68115186e2`：整合者将一处 `@[expose] section` 拆成属性行和 `section` 行，并移去相邻空行，保持后续声明行号不变，使固定 hgraph 原生解析器正确保留命名空间。数学声明、证明正文和公共接口不变；该排版修复由整合者验证，不冒充原报告员的独立检查。文件头 `source_file_and_sha256` 指向整合版本；`baseline_source_file_and_sha256` 和 `evidence/source-audit.json` 中旧哈希仍仅对应 `ef01dcf` 基线。theta 早期审查哈希和生产检查点保留为历史快照。

协调者报告全部八模块公开 exports/types/universes 精确相同，官方 freeze 后八个 API 文件零差异；本报告员另外以 `git diff ef01dcf -- interface/baselines/*-api.json` 独立确认八个文件无差异。协调者还报告 219 个原待补表达式已核对，5 项完成，13 项仅诊断标签发生变化并已审查迁移，当前清单为 214（E2 为 16）。这些全局检查结果注明为协调者提供，不替代本报告的局部独立数学审查，也不表示当前 214 项责任全部完成。

以下“原接口/基线”部分仍保留 `ef01dcf` 的原始 `sorry` 和历史证据，供复核问题起因；不得据此把已完成 theta 两项继续列为未解。本次不审查另两项 T 非整除成果。

## 原接口、背景与问题成因

本报告员未参与候选发现或实现。独立读取基线 Lean 源码、接口锁、待补清单、Blueprint 相关引用及历史提交，不仅依据派发摘要判断。

Blueprint 约定 mod-two Adams 页，`(s,t)` 的 stem 为 `t-s`；引用 LWX126 的陈述使用 2-completed、connective、finite-type 谱。本报告审查既有固定标准模型中的声明，不增补这些条件为下游参数。

当前命名空间仍是 `KIP126.Computation.*`，责任按实际定义源文件划归 E2Computation。七项目标位于 `KIP126/E2Computation/Table/{Relations,ThetaRelations}.lean`。这些是**固定项目实际球谱 E₂ 页**上的等式，不是对任意 `ProgramData` 的假设性结论；无额外宇宙变量或外部实参。`Expression.generator id s t` 经固定 `sourceGenerator` 和 `comparison` 求值；`Expression.named a` 经固定 `sourceData.atom a` 和同一个比较求值。全部原签名如下（基线证明体 `sorry` 如实保留，仅供报告展示）。
```lean
public theorem h0_obstruction_rel0 :
    ((.mul (.named .h0) (.generator 24 5 36)) : Expression).value = 0 := by
  sorry
```

```lean
public theorem h0_obstruction_rel1 :
    ((.mul (.mul (.named .h0) (.generator 3 1 8)) (.generator 335 12 130)) : Expression).value = ((.mul (.mul (.named .h0) (.named .h0)) (.generator 425 12 137)) : Expression).value := by
  sorry
```

```lean
public theorem h2_obstruction_rel0 :
    ((.mul (.named .h2) (.generator 407 13 135)) : Expression).value = 0 := by
  sorry
```

```lean
public theorem h2_obstruction_rel1 :
    ((.mul (.named .h2) (.named .M_mul_d_0)) : Expression).value = ((.mul (.named .h0) (.generator 89 10 72)) : Expression).value := by
  sorry
```

```lean
public theorem h2_obstruction_rel2 :
    ((.mul (.mul (.mul (.named .h0) (.named .h0)) (.named .h0)) (.generator 89 10 72)) : Expression).value = 0 := by
  sorry
```

```lean
public theorem theta_h5_generator84_zero :
    ((.mul (.named .h5) (.generator 84 7 70)) : Expression).value = 0 := by
  sorry
```

```lean
public theorem theta_h5_generator85_zero :
    ((.mul (.named .h5) (.generator 85 7 70)) : Expression).value = 0 := by
  sorry
```

设计来源是 `bbac1fc05843bdf2d56057e6114a38839e939378` 的固定计算，历史迁移候选来自 `71e63c4` 的 `KIP126/Computation/LinCoordinates/Certificates/Model/RelationCertificates.lean` 和 `.../Relations/ThetaMassey.lean`。历史关系证明在原生多项式关系商环中证明 `projection (X id)` 的乘法等式；历史证明不单独证明这些类就是当前 `sourceGenerator`。

当前原生源代数的同次分量、乘法、单位和 Atom 已由 `nativeAlgebra = nativePoly ⧸ nativeIdeal` 构造。`sourceAtomConstruction a` 的底层值确实是 `nativeProjection (MvPolynomial.X (atomIndex a))`。但是非 Atom 的 `sourceGenerator` 由 `sourceCoordinates.symm (single singletonBasisIndex 1)` 构造；`sourceCoordinates` 本身仍是已登记待构造接口。这些完整公共声明为：
```lean
public noncomputable def sourceCoordinates (s t : ℕ) (ht : t ≤ 261) :
    sourceData.component s t ≃ₗ[ℤ] (Fin (archive.basisCount s t) →₀ ZMod 2) := by sorry

```

```lean
public noncomputable def sourceGenerator (i : Fin archive.generators.count) :
    sourceData.component (archive.generators.degree i).1 (archive.generators.degree i).2 :=
  sourceGeneratorImplementation i
```

```lean
public theorem sourceAtom_agrees (a : Atom) :
    (eqToHom (congrArg (fun d : ℕ × ℕ => sourceData.component d.1 d.2)
      (archive.atom_degree a))) (sourceGenerator (archive.atomIndex a)) = sourceData.atom a := by
  dsimp only [sourceGenerator, sourceGeneratorImplementation]
  exact sourceGeneratorAtoms_agrees coordinateGenerator a
```

```lean
public theorem sourceBasis_values (s t : ℕ) (ht : t ≤ 261)
    (i : Fin (archive.basisCount s t)) :
    (sourceCoordinates s t ht).symm (Finsupp.single i 1) =
      (archive.basisMonomial s t i).value sourceData sourceGenerator := by sorry
```

```lean
public noncomputable def comparison (s t : ℕ) (ht : t ≤ 261) :
    sourceData.component s t ≃ₗ[ℤ] model.classical.sphere.Page 2 (s,t) := by sorry
```

```lean
public theorem comparison_product (s t s' t' : ℕ) (ht : t+t' ≤ 261)
    (x : sourceData.component s t) (y : sourceData.component s' t') :
    comparison (s+s') (t+t') ht (sourceData.product s t s' t' x y) =
      model.sphereAlgebra.product (s,t) (s',t')
        (comparison s t (by omega) x) (comparison s' t' (by omega) y) := by sorry
```

相关完整私有实现片段及 `SourceBasisSpecification` 保存在 [基线源码证据](evidence/source-audit.json)。对于非 Atom 的单生成元基底项，`sourceBasis_values` 会把坐标逆像等于用同一坐标逆像定义的生成元；该特例自身不能额外识别它与原生 `X id`。**这不表示整个 `sourceBasis_values` 是同义反复**：对一般乘积基底的兼容条件仍是实质性数学责任，可能与完整源构造一起支持迁移；本次没有证明这些条件逻辑上不足以推导七项等式。

问题分类：已确认的是历史商环对象与当前坐标定义生成元之间的证明桥尚未给出。不是已确认假命题，不是已确认漏掉数学前提，不是已确认接口必须改变；也未把可疑坐标选择当作当前实际对象反例。

## 真实前提与对象核对

| 条件或对象 | 独立核对 | 证据和仍待完成项 |
| --- | --- | --- |
| 同一固定未截断 CSV 原生商环 | 当前源构造已明确 | `sourceComponentConstruction`、`sourceProductConstruction`、`sourceAtomConstruction`；无新选择代数 |
| Atom 为原始指定生成元 | 已有原生定义和 `sourceAtom_agrees` | Atom 的 CSV ID 在 `Atom.record` 中固定；`sourceAtom_agrees` 不能覆盖非 Atom ID |
| 非 Atom ID 的原生识别 | 本次未获得证明 | 三项需新桥涉及 24、3、335、425、89；rel2 无需 g89 的原生 X 识别，已集成且局部内核通过；407/84/85 已解决 |
| degree、ID 有效及 `t ≤ 261` | 当前目标全在范围内 | 最大结果总次数为 139；错误 ID/次数不能用 `generatorImage` 的默认零分支绕过 |
| 基底逆像与所有归档单项式兼容 | 已登记但未证 | `sourceBasis_values`；并非仅有维数相同就已证成 |
| 源到实际同一 E₂ 比较 | 已登记但未构造/证明完 | `comparison`、`comparison_product`；可以按仓库规则直接消费，不能宣传最终无待补依赖 |
| 当前源商环与历史商环识别 | 要比较生成元数量、度、关系和解析器 | 历史证书可作证明模板；相同字符串出处本身不是同构或相等证明 |
| 新接口、新假设、新公理 | 不需要且未授权 | 本报告只提出内部构造和私有引理路线 |

## 独立证据与复现

证据等级为**源码结构核验与条件性桥接缺口**。没有运行 Lean 反例、没有提供固定对象数学反例、没有运行全量构建，也没有声称七项等式不可证明。源码中的 `sorry` 和锁中 `sorryAx` 是已知待补责任，不能当作一致环境中的反例。

证据包括基线 SHA-256、完整关键声明、旧证书摘录。可复现命令（仓库根目录）：

```sh
python3 interface/proposals/E2Computation/migration-coordinate-bindings-20261019/evidence/reproduce.txt
```

实际结果：检查通过；基线哈希匹配，非 Atom 生成元确实通过坐标逆像实现，`bottomMaps` 在数学源码中仅有数据声明。后一个断言为同次独立 Cν 审查的共享结构检查，不用于证明七项关系。见 [独立源码快照](evidence/source-audit.json)、[历史证书片段](evidence/historical-excerpts.txt)、[只读复现程序](evidence/reproduce.txt)。

提案校验也已通过，见 [实际验证记录](evidence/validation.txt)。系统 Python 首次运行缺少 `hgraph`；随后复用主检出现有 Blueprint Python 环境，无安装或构建。

传递依赖审计（基线路径；theta 更新见上节）：目标的实际页搬运需要 `comparison` 与 `comparison_product`；当前基底计算通过 `sourceCoordinates` 和 `sourceBasis_values`，后二者仍待补。原生理想成员证书本身可独立于任何实际页或坐标逆像完成。不得用这七个目标自身或依赖它们的 Main 后果反推原生识别；不得先借未证目标导出 `False` 再填证明。此次未运行这样的推导，也未发现能据本次证据确认的依赖循环。未作全仓库一致性证明；不能把没有发现循环理解为所有上游责任已核验。

## 方案及精确差异

优先方案保持所有公共签名、语义、固定对象、导出与责任不变。原签名就是上列七个完整声明；候选公共签名与原签名**逐字相同**，前提、结论强弱和对象关联差异均为零。无需更新公开类型指纹。

1. 一个充分的上游内部方案是在 E2Computation 内完成已登记 `sourceCoordinates` 的原生 CSV 基底构造（不是下游消费前置门禁），并证明在原生 `projection (X id)` 上取指定 singleton。构造必须同时实现完整基底兼容，不能只凭维数选任意等价。再由等价的单射性证明现有 `coordinateGenerator id` 与原生 `X id` 相同。`sourceGenerator` 的定义不必重选。
2. 逐条移植理想成员证书到**当前固定 nativeIdeal**；使用私有识别引理展开各 ID，证明现有 `sourceValue` 的关系。经同一个 `comparison_product` 搬到实际页，保留比较接口的传递待补。
3. 替代路线：若能在现有源对象上给出对允许坐标选择不变的关系证明，或由完整 `sourceBasis_values` 的乘积约束直接推出目标，可以避免统一原生识别。必须实际证明，不能把“基底维数正确”当作关系保持。

以上为剩三项的可选内部补证计划；rel2 的短路线已生产集成且通过局部内核检查，直接消费登记 rel1，无需等待该完整坐标构造。**不建议**将 `sourceGenerator` 改定义为新的任意原生生成元后仅检查 Lean 类型不变：在用户要求下，固定语义/对象关联也冻结，必须先证明新旧实现相同或完成原已指定构造。若这一等同性不能建立，须另行报告精确候选，不在本报告预先授权。

## 下游影响

| 范围 | 影响/责任 |
| --- | --- |
| 七个目标 | 直接证明责任留在 E2Computation；theta84/85、h2_rel0 已固定接口解决；rel2 已集成待本轮最终验证，另三项仍在 Relations；不得向 Main 增加前提 |
| 源构造与比较 | `sourceCoordinates`、`sourceBasis_values`、`comparison`、`comparison_product` 的已登记责任保留；不移到 ProofTools 或 AdamsCalculations |
| Main 消费 | `Main/SectionSeven/NuTargetH0Products.lean`、`NuTargetProducts.lean`、`Main/Internal/Theta/Products.lean` 直接使用七项关系；不改其接口 |
| AdamsCalculations 消费 | `AdamsCalculations/Standard.lean` 使用 `h2_obstruction_rel1`；可按登记上游输入继续工作，但不算最终无未证依赖 |
| 接口锁及待补清单 | `e2-computation-api.json` 的名称/类型/导出冻结；真实补证完成后协调者更新实际公理依赖和 `proof-obligations.json`，本报告员不写这些文件 |
| Blueprint/出处 | 延续 E2Computation 的既有来源条目；报告不建立平行论文修正版，不改 `corrections.yaml` |
| 验证 | `Tests/E2Computation/Consumers.lean`、模块锁/公共消费/独立上游消费、信任审计与 `lake build` 由协调者串行执行；本报告未运行构建 |

## 阻塞范围与继续项

目前仅三条仍需新内部桥：`h0_obstruction_rel0`、`h0_obstruction_rel1`、`h2_obstruction_rel1`；`h2_obstruction_rel2` 已生产集成且完整构建通过，独立实际依赖审计通过并保留登记上游；它消费登记 rel1，不要求先证明 rel1。`h2_obstruction_rel0` 的完整原生/枚举/运输证明现已生产编译通过，记为 `resolved-by-fixed-interface-proof`。两条 theta 已 `resolved-by-fixed-interface-proof`，不在阻塞列表。可以继续原生理想成员证书、正确坐标构造、生成元识别、完整基底兼容、坐标不变关系证明及其他不依赖此桥的目标。本 session 的 `t_not_h0_multiple`、`t_not_h2_multiple` 原生系数泛函路线与此桥独立，可以继续。两项 Cν 迁移的单独问题见 AdamsCalculations 同日 cofiber 报告。

已确认：当前实现采用坐标逆像，原始 Atom 是原生 `X`，历史关系针对原生商环。未决：三条关系的新内部证明及相关传递上游责任的最终完成。rel2 的本轮生产与独立实际依赖审计均已通过。上轮默认完整构建和扩展审计仅验证上轮输入，本轮默认完整构建已通过、独立实际依赖审计已通过并保留登记上游；任何通过结果均不消除已登记上游责任。theta 与 h2_rel0 的本地证明已完成，但实际比较接口的待补仍保留。人审等待不阻塞已授权固定接口补证。

## 人类审核记录

尚未收到人类对本报告或接口调整的具体决定；`human_decision: null`。用户的迁移指令只授权保持公共接口不变的工作，不构成本报告任何未来接口变更的授权。
