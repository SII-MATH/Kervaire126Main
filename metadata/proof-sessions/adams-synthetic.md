使用 $kip-upstream-session，负责 AdamsSynthetic 的现有待补构造与证明，公共接口、指定对象、导出及六模块职责保持不变。

第一优先级：完成 a484b981fad612eabe2bc7a01b54e049e9a01ce4 中可兼容本模块固定接口的实现迁移，以及连接这些实现所必需的适配证明。先建立“源文件/声明→当前接口”的迁移清单，边盘点边推进；本模块全部 sorry 的额外从零补证放在迁移阶段之后。清单区分已具备、可迁移、需适配、人审阻塞、依赖阻塞、源中仍未证和不适用，并提供证据。有其他非阻塞 a48 迁移项时优先继续它们，不因单项人审停下整个 session。

源仓库：/inspire/hdd/global_user/czxs25250150/Kervaire126Main
共享人审目录 REVIEW_ROOT：/inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/interface-reviews
优先迁移源（源快照只读）：a484b981fad612eabe2bc7a01b54e049e9a01ce4

先读当前 AGENTS.md、已安装 skill 的通用 protocol，以及本次任务文件 `/inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/proof-sessions/campaign-context.md` 和 `/inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/proof-sessions/module-scopes.md` 中的本模块范围，重新盘点 metadata 中的接口、契约、来源及待补清单。为本 session 建立或复用独立 worktree 和 codex/complete-adams-synthetic-<run-id> 分支；记录基线与绝对路径，保留已有改动，不切换共享主工作区。

派发每个子任务时，把本轮 a48 来源与优先级、具体目标、基线、写入权限、交付路径和验证安排显式写入任务 prompt，并传入 `protocol_path`。报告员另传 `report_template_path` 和确切 `review_dir`；不要依赖 skill 或 agent 预置本次任务参数。迁移清单与进展记录放各自工作树的 `metadata/proof-sessions/runs/<模块>/<run-id>/`。

充分调用多个 subagent：并行分配至少两个证明研究任务，持续安排 kip_counterexample 主动寻找满足真实前提的反例，另用 kip_proof_auditor 独立核验；按实际槽位轮换。使用 kip_proof_worker，按文件和依赖前沿拆分任务；同文件只允许一个写入者，其余 worker 交带基线哈希的局部补丁。协调者负责元数据和构建整合，各工作树不共享可写 Lake 缓存。

重点核对并补齐：源预谱/谱范畴、HF₂、替换和导出 smash 的实际识别，经典 Adams 塔与完整谱页，Milnor 坐标与 E₁/E₂ 的对应，synthetic 范畴与 ν、λ反演和实现，有限λ商塔、规范化和首商比较，以及收敛、检测、滤过、乘法、映射复合和权移。复用已有实现，候选源只借鉴实际构造和证明，不恢复其背景/外部结果公理，不新增公理、sorry 或假设。

可直接调用 SpectralSequence 已登记上游接口并如实记录依赖，不等待其他 session。不要修改 Literature、Computation、ProofTools、Main 的数学接口或接手其责任。

任何成员认为公共名称、类型、前提、语义、对象关联、导出或责任需要调整，立即另派未参与该候选的 kip_interface_reporter 独立复核，写 REVIEW_ROOT/<责任模块>/<唯一ID>/report.md，附背景、精确证据、最小方案与下游影响，状态 pending-human-review。只暂停确实受影响目标，等待人类明确批准，继续其余非阻塞项。不得利用相关未证责任或矛盾环境伪造反例/证明。

持续推进，分批完成真实证明、来源和责任状态同步。运行现有相关检查、python3 scripts/check-source-inventory.py 及完整 lake build；首先报告 a48 迁移清单、迁入/适配结果和未迁移理由，再报告实际消除的直接责任、仍有的传递待补、人审报告绝对路径和剩余目标。先不要提交或推送。
