# 本轮新增公共接口：独立证明核验

基线：`93fbf1215b16c9630198370c6ce3cbcff9eb4912`。协议：`/root/.agents/skills/kip-upstream-session/references/protocol.md`。本审查者没有参与候选实现；只写本 `/tmp/aimpaper-new-interface-audit-20261017/` 交付目录，生产源码及 metadata 全程只读，未运行 `lake build`，未刷新接口锁或改动检查。

本报告重点核验 Prop 2.10、Lemma 7.14、Lemma 7.20，以及 Prop 6.20 的合法域下降候选。它不是其余本轮论文条目的全部通过证书。

## 目标级结论

| 论文目标 | 核验结论 | 精确范围 |
|---|---|---|
| Proposition 2.10 | 局部数学证明通过 | 同一 synthetic convergent map 的 E∞代表等价式及三分款；另有任意滤过阿贝尔群的完整四款代表版本。普通 classical π 可代入后者，无分离或完备性额外假设。 |
| Lemma 7.14 | 局部构造及公开包装通过 | 固定标准类 V、U；同一个 Q11 类及其实际 Q9 投影；每个 untruncated U 代表允许各自选择 a2、a3；两等式和 h0 精确消灭关系均保留。仍有已登记上游待补依赖。 |
| Lemma 7.20 | 局部构造及公开包装通过 | 同一实际 Q9 中 λ⁴X、λ⁵Y 的非零 detected existential representatives，使用 Literature.normalizedNu 的固定 h2；不是任意源代表版本。仍有已登记上游待补依赖。 |
| Proposition 6.20 | 仅受限下降候选通过；原完整命题未完成 | `finiteExtension_descends` 额外明确要求 `n ≤ rEarlier−2+e(f)`，只证明 Definition 5.4 合法长度范围内的第一段自然性。没有断言 essentiality iff，不能把它标作完整 6.20。 |

完整公共入口导出、精确接口锁、source inventory 和仓库总构建由协调者串行整合验证。本报告不凭候选文件里的 `public` 修饰符单独认定模块根入口已经完成导出。

## Proposition 2.10：原文、对象与证明

原文：`AimPaper/main.tex:408` 起的 `prop:i8r47oe`；crossing 的真实定义在 `main.tex:344` 起的 `def:98skj23`。论文明确不要求 crossing essential，要求更高源滤过、非零目标标签及目标位于给定有限范围。`main.tex:255` 的全局条件是 2-completed connective finite-type spectra，因而 strongly convergent；本证明只使用有限滤过区间，实际上不需要从该全局约定额外引入强完备性结论。

`ExtensionNoCrossingRange` 量化同一个 M、P、g、cx、cy、stem 和 synthetic weight，排除所有目标 E∞ 标签非零的更高源扩张；不是只排除 essential crossing。u>s、u≤v、threshold≤v≤s+n 和扩张长度 v−u 完整保留。`RepresentsInfinityClass` 的 associated-graded iso 与源/目标收敛是同一个 P；既不另选 E∞ 类，也不丢掉真实同伦类。

主定理从原扩张取一个共同见证 a0、b0。任意相同源标签代表 a 与 a0 的差进入 F^(s+1)。其像处于 threshold 后，如未进入 G^(s+n+1)，`first_nonzero_filtration_grade` 在有限区间选出真正非零目标 grade，从而产生被排除的 crossing。逆向取 crossing 的实际代表 c，把 a0+c 与 a0 相比，目标代表相同迫使 f(c) 进入 G^(v+1)，故 crossing 目标标签为零。所有差、和、复合均在固定对象中。

三个分款也逐项正确：threshold=s 与论文 s+1 对 crossing 的 u>s、u≤v 而言等价；零目标标签精确对应 G^(s+n+1)，包括零元素；若 f(F^k)⊆G^(k+n)，则相同源代表之差的像处于 G^(s+n+1)。第三款只需 AF(f)≥n 所蕴含的实际滤过提升界，不需要 exact filtration。公开候选把这个真实滤过界显式作为前提；未声称它在任意抽象范畴自动等价于 `MapAdamsFiltration`。

新增 Additive 版本进一步消除了特定 SyntheticCategory 限制。给定扩张见证 a0∈F^s 且 f(a0)∈G^(s+n)，源标签全部代表恰为 a∈F^s 且 a−a0∈F^(s+1)；目标标签全部代表恰为 f(a)∈G^(s+n) 且 f(a)−f(a0)∈G^(s+n+1)。`FilteredNoCrossingRange` 的反例正是某个 a∈F^u，其像位于 G^v 但不位于 G^(v+1)，因而给出 y'=[f(a)]≠0；它没有偷换成 essential 版本。hF、hG 为真实滤过单调性，hf 为实际映射保持滤过，均不新增强假设。普通 classical E∞标签与 associated graded 的现有识别可用于实例化；此文件未另新增一个以 classical E∞标签为参数的包装声明，这属于接口表述的工程差别，不是该代表论证的数学空洞。

协调者负责该文件编译，要求避免本审查重复编译同一证明。已读 `/tmp/kip-extension-representatives.log` 的最终空日志和协调者 exit 0 通知；早期失败日志没有被当作最终状态。两条调用的私有辅助证明体已读，并另用 Lean 捕获其真实传递依赖。

## Lemma 7.14：同一见证、分次、量词

原文：`AimPaper/main.tex:2387`。候选：`KIP126/Main/PaperResults.lean:42`。公开证明直接消费已有实际构造 `Internal.AlphaOne.alpha_one_exists`，而不是新增结果包或从最终矛盾导出。

a11 位于 (123,132) 的实际 Q11；a9 严格定义为它与 rho 9 11 的复合，两个 finite detection 标签均为固定 V，附带非零 E∞检测。对于每个 (124,134) 的 untruncated U 代表 u，产生 Q9 中 (124,137) 的 a2 和 (125,140) 的 a3；λ³ηa9、λ³q(u)、λ⁶a2 同处 (124,131)，ηa2 与 λa3 同处 (125,138)。λ³h0a9 位于 (123,130)，恰为论文 pi_(123,123+7) 的严格零关系。

读到的构造链实际先从 V 到 E12 生存构造 Q11/Q9 detection pair，再通过 D2 数据和 F11/F12 gap 把误差升到 F13，剥离 F13/F14/F15 三层为 λ⁶a2，并构造 ηa2 的 λ整除见证。h0关系先在 Q11 升至 F17，才沿实际 rho 下降并用 Q9 的高滤过消灭。没有把“滤过足够高”直接当作零，也没有只证明某一 U 代表。

## Lemma 7.20：实际 ν 作用与存在量词

原文：`AimPaper/main.tex:2617`。候选：`KIP126/Main/PaperResults.lean:63`。x 在 Q9 的 (122,126)，由固定 (s,t,k)=(8,130,4) 的 X 非零检测；y 在 Q9 的 (125,131)，由固定 (11,136,5) 的 Y 非零检测。νx 与 λy 同在 (125,130)。ν 是原模型的 `normalizedNu model nuCofiber_nu_exponent`，没有另选 h2。所需存在量词与原文一致。

实际证明链从 Cν 的 computation D3 与固定 top/bottom 比较，通过 `nuCofiberMahowaldZeroLayer` 得到 Q3 实际 normalized-map 等式，保留源/目标标签；随后 Q3→Q5 做 F9/F10误差校正，再通过真正的 λ⁴ Q5→Q9 映射推进，并在 F12/F13 校正 y。最终分别证实 X、Y 的非零 detection，不将仅弱 detection 冒充非零。链中没有调用本轮 7.16、7.18，也没有调用 Main.Final 或 H6SquarePermanent。

## Proposition 6.20：受限第一段及未完成范围

原文：`AimPaper/main.tex:1981`；`FiniteExtensionWitness.length_upper` 在 `KIP126/AdamsSynthetic/ExtensionWitnesses.lean:26`。候选使用同一实际 normalized-map 方块的两个 rho，保留原 x、y 的标签。早页 source_cycle 由 reaches_earlier 得出；target_cycle 的早页下界是 `rEarlier−n+e(f)≥2`，恰由显式长度上界保证。witness 的 source/target 沿同一方块的实际 E∞映射给出，代表标签由 `finite_source_rho`、`finite_target_rho` 保持，方程由实际交换方块和 associated-graded自然性构造。没有转移 essentiality 责任。

独立反例员提供的零代表 r=3、r'=2、n=e(f)+1 证据已读：晚页合法，早页 length_upper 不可能成立。因此本受限定理的范围不能在记录中悄悄删去，更不能以它声称论文全部早页量词已经证明。第二段 essentiality iff 也未由本候选完成。有关接口审查由另外的独立报告员负责；本审查没有批准或实施接口调整。

## 实际检查与责任

- 已核对基线 HEAD、当前源码、完整显式候选类型、定义展开、论文原文、固定映射、非零标签及各次数。
- `PublicMainChecks.lean` 是 Main 两条候选的精确证明源码副本，仅补审计 imports 和检查命令；独立 `lake env lean` exit 0，完整公开类型（显式参数和宇宙）及 `#print axioms` 见 `PublicMainChecks.log`。
- `Capture.lean` 从实际 Lean 环境读取 `info.value? (allowOpaque := true)` 的证明体及类型，逐常量计算项目依赖闭包。审计专用 import all 补载 baseline 各模块，避免普通导入屏蔽 opaque 体。初版普通导入捕获完整保留为 `preliminary-*`，不冒充最终证据。
- 未改生产文件、metadata、接口锁、待补注册或测试；未运行 `lake build`。

最终闭包结果、待补清单核对及全部被审源码 SHA-256 由相邻 JSON 记录。公共定义/定理的局部证明完成不意味着其固定上游模型已构造、计算数据比较或文献传输责任已经消除。
