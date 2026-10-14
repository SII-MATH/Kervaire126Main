# 主证明迁移工作约束

先读 README.md、migration-baseline.json 及其中定位的资料包。
本文件记录建仓阶段约束，不宣称精确接口或最终定理签名已经审核。

- 主仓沿用原 02–07 六模块。先迁 02，再接 03，随后 04／05、06、07。
- 迁入前读取来源固定版本适用的 AGENTS.md、PROJECT_BOUNDARY.md 及相关 Blueprint。
  对抽象输入方案与原规范的冲突提交具体修订及数学影响，不能静默降低目标。
- 保留已有公共 Lean 名字、完整类型、量词、universe、typeclass、来源和未完成状态；
  新公共类型先给出数学含义、实际消费者和完整前提。
- Challenge2 保持 literature 与 computation(literature) 两个相关根字段。
  不增加第三根字段、平行 witness 或新的全局 bundle axiom。
- 来源仓的唯一临时项目 axiom 为 Main.Axiom.challenge2；这是待消除的现状，
  不代表本空仓已实现其类型或实例。不以结构打包或编译通过宣称输入已经构造。
- 标准 h₆² 非零永久存活以及本文 C3／C4／C5、选择无关性等应推导的结论保留为证明义务。
  保留共同 Z∞ 代表及 E∞ 商像非零语义。
- 最终 Challenge／Solution 的完整类型一致；Challenge 保留 by sorry，
  Solution 不直接或间接调用该占位。内部里程碑不增设 Challenge 镜像。
- 自然性归 03，一般 Moss 文献输入归 04；06 的一般工具独立于 Main 特定条件及待认证结果。
- 主仓默认构建与 Main import 闭包均应排除具体 Steenrod／Milnor／cobar、
  LinProgram 原始制品、Generated 与 checker；不整体导入 KIPBase 或恢复旧工具树。
- 逐文件保留 attribution。数学来源登记使用 docs/external-inputs.json 的单一机制；
  migration-baseline.json 只记录工程来源版本，不是另一份数学输入注册表。
- 迁入 Lean 时同步相关 Blueprint 声明、依赖与证明状态，并运行范围匹配的编译、
  来源和边界检查。哈希、编译与 Blueprint 标记都不是数学证明完成证据。
- 不为显示架构创建空目录、占位模块或单模块包装导出。
