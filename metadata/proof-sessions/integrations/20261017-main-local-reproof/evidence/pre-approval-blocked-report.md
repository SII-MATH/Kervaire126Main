# Main 局部重证集成交付记录

基线提交：`2c703812db7edb830b995c53e9fe648747a66429`，加本聊天已经批准的上游接口修正及并行工作区改动。本记录采集到 `2026-10-17T06:23:14.219440+00:00`（UTC）；每份附件另列精确采集时间、源修改时间、字节数和 SHA-256，见 [validation.json](validation.json)。这是未提交工作区的证据快照，不是提交构建缓存指纹。

本记录由 `/root/downstream_adaptation` 整理。整理者同时参与 λ-kernel 实现，**不是本轮独立审查者**。独立核验结论归属于所附原作者；构造报告、带显式参数的隔离检查、独立审查及项目生产构建分别保留真实范围。

## 当前结论与边界

修正后的实际有限 λ 商分离性和 2-primary 指数二接口，已经支持 LowEta、λ-kernel、选定 b 阶二及有限 λ⁹ shuffle 的真实 Main 局部重证；High125 的无限滤过桥与实际阶二尾部消失也已补完。协调者生产目标构建分别完成 **2809 jobs**、**2766 jobs** 和恢复合法辅助后的 Detector **2757 jobs**，均有成功日志。

**整 Main 与最终默认 `lake build` 尚不能据此记为通过。** High125 F25/source 分支仍等待一项未批准的上游加强：将同一个 `Literature.Standard.tmf_high125_nonzero` 的非零结论加强为同一实际图像非奇挠。完整条件候选已经用显式 `hImageNonodd` 检查通过，但该参数只存在于 scratch；未写入 Main 公共目标，未注册新待补，未应用待批补丁。精确人审范围见 [高125 detector 非奇挠报告](../../../interface-reviews/Main/20261017-high125-detector-nonodd/report.md)。

本轮没有 commit、push 或 Release 缓存发布。第一次默认构建失败（exit 1）后，协调者恢复了误删的合法 realization 注入辅助；Detector 的独立生产目标构建已通过（2757 jobs）。**最终当前默认构建 session 76840 仍 exit 1，唯一失败目标为 `KIP126.Main.Internal.High125.Source`**，其旧 `classical_filtration26_zero` 调用需要待批的 nonodd 图像论证替代。当前状态是 `blocked_pending_human_interface_decision`，不是整个 Main 已编译通过。用户异步确认尚未回复，等待不构成此次接口加强的批准。最终失败日志已完整归档；不把成功的局部目标构建标为完整项目成功。

## 已完成的真实局部推导

| 范围 | 当前实际成果 | 原作者及证据 |
| --- | --- | --- |
| LowEta | 仅在实际有限 λ 商证明 `(1,3)` 像消失；首商同值的 η 在全部有限商同值；源自同构固定有限商中的 η 作用。删除无法再由原上游证明的未截断唯一性辅助。 | `/root/separation_interfaces`，[报告](evidence/kip-main-reproof-loweta.md) |
| λ 注入 / weight71 kernel | 从实际 cofiber 首商原像、永久 lift 证明 λ 注入；F9 首商 projection 消失后，经 TR3/finite no-return 的实际 δ 比较、q=1 Bockstein 和 stem63 无晚期微分关闭 λ 核，保留原 weight71 realization-kernel 类型。删除原过强泛型 E∞ 注入论证。 | `/root/downstream_adaptation`，[报告](evidence/kip-main-reproof-lambda.md)、[工具返回记录](evidence/kip-main-reproof-lambda-validation.json) |
| 选定 b | 对实际 lift 的 realization 先取正奇数倍，使其成为 2-primary；奇数保持同一首商标签，再应用修正后的 stem62 定理及已重证 kernel 得到所选 b 阶二。没有断言任意 b 阶二。 | `/root/literature_interfaces`，[报告](evidence/kip-main-reproof-selected-b.md)、[哈希](evidence/kip-main-reproof-selected-b-hashes.json) |
| AnyY / Theta shuffle | 只在下游需要的实际 λ⁹ 商消去 η 的源自同构；原 Toda 成员、符号、相容性与真实阶二前提保留。私有 wrapper 和实际消费者同步为有限商等式。 | `/root/compose_interface`，[报告](evidence/kip-main-reproof-shuffle.md)、[AnyY 日志](evidence/kip-main-any-y-shuffle.log)、[Theta 日志](evidence/kip-main-theta-shuffle.log) |
| ν / 球无限滤过 λ-torsion | 由同一个首商类的各有限 λ lift 得同一个 E₂ 标签到达各有限页；实际 `B₀⊂Z∞` 与 `Z∞=⋂Zr` 构造共同永久 cycle，再用永久 lift 消去 actual connecting；按有限 λ 幂挠指数归纳。 | `/root/main_interface_report`（该新构造的实现者），[报告](evidence/kip-main-infinite-lambda-kernel-result.md)、[源码](evidence/kip-main-infinite-lambda-kernel.lean)、[检查日志](evidence/kip-main-infinite-lambda-kernel-validation.log) |
| High125 Filtration | 普通 F26 仅推出奇挠；synthetic F26 推无限滤过。真实桥证明无限 synthetic 滤过的 realization 奇挠；结合实际阶二、realization-kernel 与前项 λ-torsion 消失，证明**阶二输入域上** F26=0。η 乘积与实际选择差均有独立阶二证明。 | `/root/high125_local_repair`，[最终报告](evidence/kip-main-reproof-high125.md)、[实际 realization 桥](evidence/kip-high125-bridge.lean) |

最后一份 High125 报告是在作者明确通知最终稳定、补齐生产构建及 conditional 机器验证之后重新采集，当前 SHA-256 为 `98ea4540b20389e5657367e3f1184870c5ab99dea9083d878a82bdad04cb4e28`。它替代同一作者更早的过程报告，不能将旧“尚待 kernel”描述当作当前成果状态。

## 独立检查与真实依赖

[独立 λ 审查](evidence/kip-main-lambda-independent-audit.md) 由未参与该候选实现的 `/root/separation_interfaces` 完成，并实际编译候选及依赖遍历器。三个核验根的实际可达直接待补数分别为 25、29、44，Main 均为 0；[完整依赖数据](evidence/kip-main-lambda-independent-deps.json)、[审计源码](evidence/kip-main-lambda-independent-audit.lean) 与 [日志](evidence/kip-main-lambda-independent-audit.log) 已归档。该结论是对现有 producer 接口的合法局部推导，不是这些 producer 已经补完。

[独立反例及桥审查](evidence/kip-main-reproof-counteraudit.md) 属于 `/root/independent_math_audit`。报告区分原始文献支持的数学事实、运输到固定 Lean 对象的待补、抽象过滤群反模型与实际源码审查。其最后更新已审查新的无限滤过 λ-kernel 桥与 realization 奇挠桥，未发现符合全部实际前提的反例或目标循环；该审查者没有把协调者的 Lean 结果冒充自己重跑的完整构建。

仍使用的既有上游包括 fixed model/对象识别、实际 cofiber/quotient/tower/convergence、有限 λ 商分离性、finite-map 奇挠判定、ν/有限商 E∞ 比较、BHS finite/permanent lift、selected realization kernel/prescribed lift、实际 λ/shift/coherence 与计算标定。没有恢复错误的未截断 sphere 全称零分离性，没有把旧普通 stem62 全群指数二改名重用，也没有从项目不一致环境导出任意结论。

待补清单采集时真实记录：**299 项直接上游责任**（AdamsSynthetic 90、Literature 119、Computation 88、ProofTools 2；pending construction 86、pending proof 213），Main 直接待补 **0**。本轮局部 reproof 没有新增 Main 公理、sorry、结果包或公共前提；局部编译仍可传递到这些已登记上游待补，不能称无 `sorryAx` 的完整数学闭合。

## 生产构建与有条件验证分开记录

| 证据 | 实际结果 | 限制 |
| --- | --- | --- |
| [生产局部链日志](evidence/kip-main-reproof-local-build.log) | `Build completed successfully (2809 jobs).` | 协调者执行的选定生产目标链；包含修复后的 kernel、选定 b、shuffle/Toda 消费，不是默认全项目构建。 |
| [High125 Filtration 日志](evidence/kip-main-high125-filtration-build.log) | `Build completed successfully (2766 jobs).` | 只证明该生产目标依赖闭包通过，不含待批 F25/source 最终接口。 |
| [条件 F25 源码](evidence/kip-high125-conditional.lean)、[机器记录](evidence/kip-high125-conditional-validation.json)、[实际日志](evidence/kip-high125-conditional-validation.log) | bare Lean exit 0 | 唯一额外局部参数 `hImageNonodd : ¬ IsOddTorsionMap (high125 ≫ tmfUnit)`，只验证条件版构造；不证明该前提，不等于生产 Main 通过。 |
| [第一次默认构建](evidence/default-build-attempt-1.log) | session 52034，exit 1 | 保留真实历史：当时失败 Detector 与 Source；Detector 的合法辅助后来已恢复。 |
| [恢复辅助后的 Detector](evidence/detector-restored-build.log) | `Build completed successfully (2757 jobs).` | 恢复的是有效 `realization_injective_of_lambda_powers` 和同模块导入，未恢复任意 θ 阶二断言。 |
| [最终当前默认构建](evidence/default-build-after-detector.log) | session 76840，exit 1 | 唯一失败 `KIP126.Main.Internal.High125.Source`。当前 `blocked_pending_human_interface_decision`；整个 Main、Architecture/Integration/Trust 最终汇总未通过。 |

[待批准后才能应用的局部补丁](evidence/kip-high125-after-nonodd-approval.patch) 仅作为具体可审查候选归档，**尚未应用到生产**。当前人审状态为 `pending-human-review`，`human_decision: null`；已有四项接口授权及 θ₅ 单项责任授权不覆盖此次更强结论。

部分原 worker 报告保留其早期“进口尚缺”或“显式 kernel 参数隔离检查”记录。它们是当时实际结果；后续上面生产日志证实相应局部链通过，但没有把尚未批准的 High125 条件结果升级成全 Main 完成。

## 元数据、采集完整性与后续

Main 源/契约整理者的 [报告](evidence/kip-main-metadata-reproof-result.md)、[字段差异](evidence/kip-main-metadata-field-diff.json)、[一致性检查](evidence/kip-main-metadata-validation.json) 已归档：14 个稳定源快照与当前私有声明记录同步，保留来源、历史退休记录及同一 public declarations 数组；High125 Source/Injectivity 与最终完整状态仍留待真实完成。Main API 锁文件字节与 HEAD 相同；完整 Main 公共消费/Trust 汇总仍受 Source 失败阻塞。协调者最新 `python3 scripts/check-source-inventory.py` 通过（473 个项目源文件、28 个消费/审计文件），`git diff --check` 通过；这些检查不能替代失败的默认构建。

本目录整理者只创建本目录的 report、validation 和 evidence；没有修改生产源码、API 锁、待补清单、其他模块元数据或共享构建状态，也没有重跑已有数学检查。每份 evidence 均逐字节复制；`validation.json.evidence` 记录完整 SHA-256、字节数、源位置、作者/责任方、采集时间与源修改时间。归档报告保留原 `/tmp` 引用以忠实保存来源，其被采集的对应文件通过本报告及 JSON 映射到 evidence。

本次最终默认构建失败已如实记录，剩余工作等待上述**同名**上游结论 `≠ 0 → ¬ IsOddTorsionMap` 的真实用户决定。批准前不应用条件补丁，不更换对象，不把其参数塞进 Main 公共目标。批准并实际完成后仍须重新跑完整默认构建及接口/信任检查；只有实际通过后才能处理用户要求的 commit/push，并按仓库规则显式同步对应已推提交的 Release 构建缓存。当前未 commit、未 push、未发布 Release 缓存。
