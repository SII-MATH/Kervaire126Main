使用 $kip-upstream-session，负责 Computation 的现有有限计算、证书及其与实际 Adams 对象的对应，公共接口、标准类、对象关联、导出及六模块职责保持不变。

第一优先级：完成 a484b981fad612eabe2bc7a01b54e049e9a01ce4 中可兼容本模块固定接口的实现迁移，以及连接这些实现所必需的适配证明。先建立“源文件/声明→当前接口”的迁移清单，边盘点边推进；本模块全部 sorry 的额外从零补证放在迁移阶段之后。清单区分已具备、可迁移、需适配、人审阻塞、依赖阻塞、源中仍未证和不适用，并提供证据。有其他非阻塞 a48 迁移项时优先继续它们，不因单项人审停下整个 session。

源仓库：/inspire/hdd/global_user/czxs25250150/Kervaire126Main
共享人审目录 REVIEW_ROOT：/inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/interface-reviews
优先迁移源（源快照只读）：a484b981fad612eabe2bc7a01b54e049e9a01ce4

先读当前 AGENTS.md、已安装 skill 的通用 protocol，以及本次任务文件 `/inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/proof-sessions/campaign-context.md` 和 `/inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/proof-sessions/module-scopes.md` 中的本模块范围，重新盘点 metadata 中的接口、契约、来源、实际数据和待补清单。建立或复用独立 worktree 和 codex/complete-computation-<run-id> 分支，记录基线与绝对路径，保留已有改动，不切换共享主工作区。

派发每个子任务时，把本轮 a48 来源与优先级、具体目标、基线、写入权限、交付路径和验证安排显式写入任务 prompt，并传入 `protocol_path`。报告员另传 `report_template_path` 和确切 `review_dir`；不要依赖 skill 或 agent 预置本次任务参数。迁移清单与进展记录放各自工作树的 `metadata/proof-sessions/runs/<模块>/<run-id>/`。

充分调用多个 subagent：用 kip_proof_worker 并行研究至少两个计算族，持续安排独立 kip_counterexample 检查反例，另由 kip_proof_auditor 核验。Standard.lean 集中了大量责任，采用多个 worker 交带基线哈希的局部补丁，唯一文件写入者串行整合；其他文件按独占路径分工。协调者统一更新元数据、全局清单并调度构建，各工作树的可写缓存独立。

重点推进：完整生成元及基目录，Lin 分次商代数和坐标，同实际球面 E₂ 的比较及 h_i/g/δ 标定，维数/乘积/零关系/有限证书，球面微分/存活/消失与 staircase，Cν基/顶胞腔/包含和连接映射，tmf模型及 v₂¹⁶、βg⁴ 等指定类。明确区分“有限坐标证书正确”和“证书确实计算固定 Adams 对象”；不得另造满足表的模型替代几何识别。候选 a484 仅借实际数据、解析和证明，不引入外部计算公理或新假设。

直接消费 SpectralSequence、AdamsSynthetic、Literature 的已登记接口，记录真实传递依赖，不等待其他 session，不改其数学接口或责任。主动核查编号、分次、有限范围端点、负次数、遗漏关系和证书数据错误。

任何成员认为公共名称、类型、前提、语义、对象关联、导出或责任需要调整，另派未参与该候选的 kip_interface_reporter 独立复核并写 REVIEW_ROOT/<责任模块>/<唯一ID>/report.md，说明背景、满足全部前提的证据、精确方案和下游影响，状态 pending-human-review。只停真实依赖该问题的目标，等待人类明确批准，同时继续其他非阻塞项。条件性或抽象模型反例不能冒充固定实际对象上的无条件反例。

持续推进并同步真实来源、有限证书和责任状态。保留现有接口和信任检查，完成相关检查、python3 scripts/check-source-inventory.py 和完整 lake build，首先报告 a48 迁移清单、迁入/适配结果和未迁移理由，再报告真实补完项、仍需上游证明的依赖、人审报告绝对路径及剩余目标。先不要提交或推送。
