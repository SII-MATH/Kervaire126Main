使用 $kip-upstream-session，负责 Literature 的现有待补结论、对象识别和比较证明，公共接口、真实前提、固定对象、导出及六模块职责保持不变。

第一优先级：完成 a484b981fad612eabe2bc7a01b54e049e9a01ce4 中可兼容本模块固定接口的实现迁移，以及连接这些实现所必需的适配证明。先建立“源文件/声明→当前接口”的迁移清单，边盘点边推进；本模块全部 sorry 的额外从零补证放在迁移阶段之后。清单区分已具备、可迁移、需适配、人审阻塞、依赖阻塞、源中仍未证和不适用，并提供证据。有其他非阻塞 a48 迁移项时优先继续它们，不因单项人审停下整个 session。

源仓库：/inspire/hdd/global_user/czxs25250150/Kervaire126Main
共享人审目录 REVIEW_ROOT：/inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/interface-reviews
优先迁移源（源快照只读）：a484b981fad612eabe2bc7a01b54e049e9a01ce4

先读当前 AGENTS.md、已安装 skill 的通用 protocol，以及本次任务文件 `/inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/proof-sessions/campaign-context.md` 和 `/inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/proof-sessions/module-scopes.md` 中的本模块范围，重新盘点 metadata 中的接口、契约、来源及待补清单。建立或复用独立 worktree 和 codex/complete-literature-<run-id> 分支；记录基线、绝对路径和已有改动，不切换共享主工作区。

派发每个子任务时，把本轮 a48 来源与优先级、具体目标、基线、写入权限、交付路径和验证安排显式写入任务 prompt，并传入 `protocol_path`。报告员另传 `report_template_path` 和确切 `review_dir`；不要依赖 skill 或 agent 预置本次任务参数。迁移清单与进展记录放各自工作树的 `metadata/proof-sessions/runs/<模块>/<run-id>/`。

充分调用多个 subagent：以 kip_proof_worker 并行研究至少两个定理族，持续安排独立 kip_counterexample 主动尝试反例，另由 kip_proof_auditor 核验实际论证和依赖。Standard.lean 集中了大量责任，采用多个 worker 并行找证明/交带基线哈希的局部补丁，唯一文件写入者串行整合；协调者统一写元数据并调度构建，各工作树缓存写入独立。

重点推进：实现/λ反演/权移，E₂自由部分和有限λ商，E∞与λ/ρ相容，商代数、乘法与检测滤过，BHS lifting及比较，May/Moss/Toda和次级操作，以及经典η/ν/θ₅、BX、tmf等文献对象与标准类。核验原始来源支持当前完整量词、次数、对象和边界条件；引用文献与完成 Lean 证明分别记录。只借鉴 a484 的实际证明和构造，不把其外部文献结果公理当作解答。

直接消费 SpectralSequence、AdamsSynthetic 已登记接口并如实记录传递依赖，不等待其他 session；保留同一源对象与固定对象的实际比较，不接手上游或下游模块责任。

任何成员提出公共名称、类型、前提、语义、对象关联、导出或责任调整，必须另派未参与该候选的 kip_interface_reporter 独立复核，写 REVIEW_ROOT/<责任模块>/<唯一ID>/report.md，完整说明前因后果、证据、精确方案、影响和备选，状态 pending-human-review。只停受影响项，等人类明确批准；同时继续其他任务。反例必须满足真实前提，不能借目标或相关 sorry/矛盾依赖声称已推翻。

持续推进并同步真实来源和待补状态，保留全部现有检查。完成相关模块检查、python3 scripts/check-source-inventory.py 和完整 lake build，首先汇报 a48 迁移清单、迁入/适配结果和未迁移理由，再汇报真实完成项、传递待补、人审报告绝对路径与剩余任务。先不要提交或推送。
