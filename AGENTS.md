# 协作规则

| 模块（接口清单） | 职责 |
| --- | --- |
| [SpectralSequence](spectral-sequence-api.json) | 谱页、微分、代表、存活、滤过、收敛、检测与 ESS；Algebra 为内部支撑。 |
| [AdamsSynthetic](adams-synthetic-api.json) | 固定范畴、Adams 系统、标准类、乘法、ν、λ 商与比较。 |
| [Literature](literature-api.json) | 带来源和完整条件的文献结果。 |
| [Computation](computation-api.json) | 计算数据与实际对象的对应、标准类标定、微分、乘积及存活。 |
| [ProofTools](proof-tools-api.json) | stretching、广义 Leibniz、广义 Mahowald 及公共操作定理。 |
| [Main](main-api.json) | 论文局部推导及标准 h₆² 非零永久存活目标。 |

公共入口为 `KIP126.Def.<模块名>`，Main 为 `KIP126.Main`。`*-api.json` 锁定类型与导出，`*-contracts.json` 说明用途，`*-sources.json` 记录来源。

- **接口冻结。** 未经用户明确允许，不增删或改变公共声明的名称、类型、前提、语义、对象关联及导出。认为接口不合理或不足时，提交具体修改方案、理由和下游影响，获准后实施；不得改锁文件绕过检查。已有授权不重复确认。
- **单模块任务。** 未经明确允许，不修改其他模块、接手其证明或移动责任归属。阅读和调用上游公共接口可以正常进行。
- **自顶向下证明。** 从当前目标递归拆分局部引理与构造，直到接到已有上游接口、mathlib 或基础定义；依赖不得成环。辅助声明保持私有。
- **上游直接调用。** 上游已登记的待构造、待证明接口可直接使用，责任不转入下游；不恢复 Challenge、结果包或额外假设，保留真正的数学前提。
- **如实记录。** 保持接口不变的补证明及状态更新无需另行批准；同步来源、测试和 [待补清单](proof-obligations.json)。未经允许不新增公理或待补责任，不能靠放宽检查掩盖缺口。
- **封装与检查。** 使用 `module`，默认私有、显式 `public`；`import all` 仅限同模块内部。遵守依赖方向，以普通导入验证公共消费，复用缓存完成相关检查和 `lake build`。
- **工程边界。** 工具链按 [README](README.md) 固定，未经允许不升级或改依赖锁；避免无必要地清理缓存。Blueprint 迁移与检查继续延后。
