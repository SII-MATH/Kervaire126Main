# Computation 私有表达式比较辅助层

从 `/tmp/kip-computation-20261017` 的未提交交付提取
`Table/Internal/SourceExpression.lean`，精确来源 SHA-256 见
`metadata/computation-sources.json` 的对应条目。

只新增私有 `sourceValue` 和 `value_comparison`，递归处理单位、命名原子、指定生成元及乘积。
源端求值沿用已有 `sourceData`，经同一 `comparison` 解释为已有 `Expression.value`；
乘积必须满足总内部次数不超过 261。非法编号、错误次数与超界表达式保留原有零分支，
不据此扩展比较定理的适用范围。

删除源文件中未被使用的具体 `SphereQuotient` 导入。没有复制 Program 数据、目录、
解析器、商模型、tmf 模型或具体计算证书，也没有引入额外公理或待补接口。
比较映射、乘法比较和单位比较仍直接调用既有上游接口；它们的构造并未由本辅助证明完成。

本次修改保持 Computation 公共声明、类型、导出和接口锁不变。Computation 的 88 项直接待补保持原样，
本任务不修改 `metadata/proof-obligations.json`；其他 session 可继续更新自己模块的记录。本次完成私有辅助证明，不声称消除了公共待补。
测试覆盖一般及嵌套表达式传递、非法编号、错误次数、超界分支、比较范围拒绝和普通导入隐藏；
原内部审计新增此文件，原全部消费者/信任测试保留；新测试加入 ComputationChecks 的构建根。

验证结果见同目录 `validation.json`。任务初始工作区及日志快照位于
`/tmp/kip-main-source-expression-20261017/`。保留其他模块及未跟踪工作；未提交或推送。

## 实际验证结果

- 当前源码清单检查和 `git diff --check` 通过。
- 独立检出：已提交 develop 基线加本次完全相同的补丁，完整 `lake build` 通过，共 3,080 项。
- 共享工作区：新增辅助层、内部边界测试、普通导入隐藏、Computation 公共接口和内部信任审计均通过；内部审计仍登记 88 项原待补。
- 共享完整构建失败：其他并行修改的 AdamsSynthetic/Literature 接口锁和待补记录未一致，另有 Main 下游类型/名称错误；后段还出现并行重建造成的上游缓存文件缺失。完整错误保留在 validation.json 和原构建日志中。未通过修改其他模块、接口锁或移除检查来消除这些失败。
- 本任务不修改其他模块；任务期间其他 session 继续更新其源码和记录，原工作文件没有丢失。未提交或推送。
