# 获批接口与下游适配独立只读审计

审计者 `/root/final_change_audit`，2026-10-17。基线 `2c703812db7edb830b995c53e9fe648747a66429`。已读当前 AGENTS.md 与指定 protocol.md；未参与候选实现。仅写本报告，未改生产、metadata、检查或锁；未运行 Lean/Lake 或写共享构建缓存。Computation、Tests.Computation、Tests.Trust、lakefile 的其他会话工作不纳入本轮。

## 目标级结论

- **通过（授权及局部源码/现有 kernel 证据）：** 三项获批数学接口精确改型、`graded_compose` 的 no_expose 方案、同名 `_proof_1` 保留、`tmf_convergence` 的具体公开实现及精确 19 项新增导出。无额外公开名称/类型/宇宙变化。两模块捕获中新增直接待补精确为获单独批准的 `theta5_order_two` 一项；没有项目公理或 synthetic sorry。
- **源码核验通过，编译状态未决：** ProofTools 五文件的有限商/shift 调用适配，以及 Main 的 BX 平方差桥、Toda 显式局部阶二参数和固定 high125 detector 非零证明。未见这些新增证明体使用目标循环、从争议接口推出新零结论、换对象或新增 Main 责任。
- **未通过整体完成门槛：** Main 仍有旧无限分离性和任意元素阶二调用；当前源码不具备完整 Main / `lake build` 通过证据。局部安全修复不代表其传递依赖已可用，也不允许把 Main 目标记为完成。

## 真实接口及固定对象

`Separation.lean:20` 现为 `(X : SyntheticObject) (n : ℕ) → HomotopySeparated model.syntheticTower (XModLambdaN (X.obj model.nu model.auxiliary) n)`。固定 `SyntheticSpectrum : Type 1`、Hom 宇宙 0、同一 model 和实际 λⁿ cofiber；`HomotopySeparated` 量化所有 m,w 和同一个 a，并要求所有自然数滤过层。n=0 仍在范围；新接口本身保留一个原有直接 sorry，未伪装 producer 已完成。

`ClassicalSupport.lean:67` 的普通球 `a : π_m S` 及所有自然数滤过前提不变，结论改为 `IsOddTorsionMap a`。该谓词完整为 `∃ n : ℕ, Odd n ∧ 0 < n ∧ n • a = 0`，包含零。证明调用既有 `finite_map_separation`，源是 `SphereSpectrum⟦m⟧`、靶是普通 SphereSpectrum，有限性分别由 shift/sphere 给出；所有整数 s 使用 `ha s.toNat`，与 MapAdamsFiltration 的真实定义吻合。没有再声称普通无限滤过类为零。

`Literature/Standard.lean:185` 的 `stem62_exponent_two` 对同一个 ordinary π₆₂ 元素 a 增加 `(∃ n : ℕ, (2^n : ℕ) • a = 0)` 前提；n=0 只覆盖零。没有把 mod-2 检测直接当作该前提，没有替换完成球。`theta5_order_two:224` 的原类型和固定 theta5 保留，新增一个直接 sorry，与额外用户授权一致；没有通过自己阶二反向证 2-primary 后套用指数接口的循环。

## 公开类型、宇宙及封装

独立 Python 对比基线 `git show 2c70381:metadata/*-api.json` 与 `/tmp/kip-approved-{adams,literature}-public.json` 的每个完整 `full_type`、`type_fingerprint` 和 `universes`：

| 范围 | 基线→捕获 | 差异 |
| --- | --- | --- |
| AdamsSynthetic | 1825→1825 | 无增删；仅两项 separation 类型变化，均无宇宙参数变化 |
| Literature | 754→773 | 无删除；仅 stem62 类型变化；精确增加 tmf `_proof_1` 至 `_proof_19` |

十九项逐项与获批 `proposed-additional-exports.json` 的完整类型、fingerprint、universes 对比一致。此原始提案文件内 `not_authorized: true` 是历史状态，不被重写；后续授权由 `approved-upstream-20261017/approval.json` 和当前用户原话单独保存。

`Operations.lean:347` 手写公开 `graded_compose._proof_1` 的类型显式保留原 polynomial action 与 graded_module 实例，而非仅同名结论；完整 kernel 类型指纹仍为 `13301073175485286128`、宇宙 `[]`。`graded_compose` 指纹仍为 `8046296169434938693`、宇宙 `[]`。公开捕获显示没有因此新增其他导出。no_expose 仅应用该 def。新增 `import all Enrichment` 属同模块内部消费；没有越过其他数学模块封装。

## 实际证明体和传递责任

1. **graded composition：** 私有 `totalComp` 按两项 homogeneous direct-sum 分量实际调用 `weightHomComp`，然后加法扩张。结合律递归降到已有 `homogeneous_assoc quotients.coherence`；λ 中心性使用同一 `SyntheticCategory.lam.naturality` 与 `quotients.coherence.lambda_comm`；polynomial 线性从常数整数作用、加法和 X 递推，X 作用经 `totalLambda_eq_compLambda` 精确识别。`graded_compose_homogeneous` 直接化归 `totalComp_of`。不是零运算、没有利用该目标本身或不相关 contradiction。捕获依赖闭包仍有 9 个上游直接待补（背景对象/范畴、exactness、nu、quotients、recovery、syntheticCofiber）；只消除本地 compose 与 homogeneous 两项责任。
2. **tmf convergence：** `Standard.lean:256–411` 用固定 `e := tmfIso : tmf ≅ model.auxiliary.detector` 和固定 detector convergence。真实 tower map 运输各滤过层；商同构用相同的 s+1→s inclusion，通过 `cokernel.mapIso` 构造；同一 z 的 cycleMap 和同一 a 的 stage map 保留 `layerMap` 等式。最后调用 detector convergence 的 `canonical`，将同一个 b 和 associated-graded projection 沿 q 运输回来。不把 bare E∞ 同构冒充 canonical 强度。合并当前 Adams+Literature trust 图得 31 项传递直接待补：29 Adams 背景责任加 tmf、tmfIso；不是无未证依赖的收敛定理。旧报告的 33 数字属于历史捕获，不覆盖此当前遍历结果。
3. **classical odd torsion：** 直接责任消除但依赖既有 `finite_map_separation`；当前联合闭包 30 个直接待补。该责任没有转移给下游。
4. **责任差异：** 与基线 proof-obligations 的名称集合比，Adams 减少 `classical_sphere_separated`、`graded_compose`、`graded_compose_homogeneous` 三项，无新增；Literature 减少 `tmf_convergence`、新增获批 `theta5_order_two`，净计数不变。注意这里是现有捕获与基线的比较，不替协调者完成 metadata 更新。
5. **依赖循环：** 对上述 compose/classical/tmf/theta5 四根，联合 trust dependencies DFS 未发现循环；也逐段核对真实新增体没有自我调用。类型中记录的固定 model 背景责任仍须保留。

## ProofTools 适配

`GeneralizedMahowald/Filtration.lean:54–94` 私有 shift helper 的关键是 `FilteredPieceIso` 的实际 `level_arrow`，而非仅 E∞：设 p=(m−δ₁,w−δ₂)，沿 p+δ=(m,w) 取得 e；对每层 s，将 a 的真 subobject witness x 用 `(e.level s).inv` 拉回，借 `e.symm.level_arrow s` 确认拉回后 ambient 元素恰是 `e.ambient.inv a`；由同一个基础分离性 hsep 得零，再用 ambient.inv 的单射性回到 a=0。

该 helper 用 `(.quotient q X)` 的固定 convergence/essShift 和新 `synthetic_homotopy_separated X q`，目标是同一 `shift δ (XModLambdaN X q)`。没有错误地将商后 shift 换成 shift 后另一个 cofiber，也没有把 `(.quotient q X)` 再传 q 导致二重商。

HSource 使用 `(shift (0,e) (nu X)) 1`，MayCorrection 使用 `(shift (0,b) (nu X)) i`，两个无返回论证和 shifted finite high filtration 通过同一 private shifted_quotient helper。新增辅助均 private，五文件无新增 sorry 或公开前提变化。**未在本审计运行构建；其最终 kernel 检查仍需协调者调度。**

## Main 安全局部修复与剩余阻塞

- `Choice/OrderTwo.lean` 删除错误任意 θ 阶二证明，仅保留 realization additivity；`ChoiceIndependence.lean:110` 的 theta' 实际 let-bound 到 `bxTheta5`，使用 `bx_order_two` 的确是同一代表。
- `Choice/Invariance.lean:25–43` 以固定 BX θ₀ 为桥，两次使用真实 θ₀ 阶二的平方差公式，借同一 filtration submodule 的 sub_mem 相减抵消 θ₀²。未假定任意 θ、θ' 阶二；目标 detection 类型未增加公开前提。仍依赖既有 BX 待补、choice gap 和局部 filtration 结果。
- `Theta/TodaExistence.lean:72` 及 `SectionSeven/ThetaToda.lean:30,74` 只在私有 helper 加显式 `theta+theta=0`；最终 `NuTarget.lean:42` 用固定 BX 提供真实来源。因此本地新增 θ 阶二参数没有流入任何公开 Main 声明。然而它们仍调用下述未修复任意 b 阶二引理，故链条未闭合。
- `High125/Source.lean:54` 的新 `high125_detector_nonzero` 只对同一固定 `Standard.high125`，通过 `tmfUnit_agrees`、同一 tmfIso、`tmf_high125_nonzero` 得出。它删除了不再可用的“任意同检测代表唯一”。`Injectivity.lean:118` 使用 hr 将 realization a 精确认作固定 high125 后应用此非零矛盾；此处 False.elim 是真实局部零/非零矛盾，没有从旧分离性恢复新零结论。不过该文件仍经 high_nonzero_survival 依赖未闭合 filtration 结论。

**当前明确阻塞位置（源码实际检查，不能报完成）：**

| 位置 | 未闭合点 |
| --- | --- |
| Main/Internal/Choice/LambdaInjectivity.lean:97 | 仍以任意 X 调用旧无限对象 separation，不能由有限商新接口提供 |
| Main/Internal/Theta/RealizationKernel.lean:124 | 同样对任意 X 用旧 separation 得 kernel zero |
| Main/Internal/LowEta.lean:75 | sphere (1,3) 的原 separation 特例尚需独立局部证明 |
| Main/Internal/High125/Filtration.lean:76 | sphere (125,130) 原 separation 特例尚未修复 |
| Main/Internal/High125/Filtration.lean:126 | 新经典结论是奇挠，而该处目标为零，尚无排奇挠证明 |
| Main/Internal/Theta/OrderTwo.lean:59 | 新 stem62 调用得到 2-primary 前提→阶二函数，不能作为阶二证明；任意 b 的前提无来源 |

这些失败不是新接口为假的证明。更早独立反例报告已指出任意 synthetic 62-stem 阶二在真实 ordinary/HF₂ 语义下存在奇挠反例；本审计不重做该外部文献工作、不把条件性对象识别当当前 kernel 反例。不得为这些 Main 缺口偷偷增 sorry、公开前提、对象重关联或恢复旧全称零接口。

## 实际验证与证据边界

本审计实际运行：git status/diff/show、rg、sed/cat；Python 比较完整类型/fingerprint/宇宙/名称、十九项导出、基线直接责任集合、联合依赖 DFS、源码 SHA-256。没有运行任何修改检查或重刷锁命令。捕获脚本本身已读：公共捕获采用普通 public import 并检查 exporting environment，trust 捕获使用 import all 审计真实 body 及 dependencies。

读取既有日志 `/tmp/kip-interface-adams-build-final.log`（AdamsSynthetic 局部 build 成功）、`/tmp/kip-interface-literature-build.log`、`/tmp/kip-interface-literature-checks.log`（Literature 消费/接口/trust 2733 jobs 成功）和 separation 日志。Literature trust 为1374声明/119直接待补；Adams trust 捕获2950声明。二者捕获均零项目 axiom、零 synthetic sorry。日志中 Unknown identifier 信息来自现有接口阴性检查，末尾明确 build success，不能仅见该文本判失败。

尚无本审计验证过的 ProofTools/Main/full lake success。`capture` 是现有环境证据，其文件 mtime 晚于对应生产文件，但没有随捕获绑定的源码 SHA manifest；最终整合仍须记录下面哈希与构建输入并按协调者计划重查。旧 worker 文档中的 tmf-only/未改 stem62 状态保留为历史，不覆盖现在实际源码。

## 本轮观察到的精确源码哈希

以下双哈希从基线 Git blob 和当前实际文件独立计算。并发修改后应重核；本报告不对其后版本背书。

| 文件 | 基线 SHA-256 | 当前 SHA-256 |
| --- | --- | --- |
| `KIP126/AdamsSynthetic/Standard/ClassicalSupport.lean` | `c576f2e00939f5638d37f19d3a8d89cf67bcb7cceb3870e1cd864068e08e4fd3` | `3856a58c4239e54a58c12d9a4ec14f24a26a3e2f5342cc17d28fdc6a6a67cc11` |
| `KIP126/AdamsSynthetic/Standard/Operations.lean` | `63bb1c57b1bc949af0553c8baebc6e4ef95090be38594e0a83b26e9f837ad1d0` | `b170aa7f3c878d4b79b11a911fcf149e01a76d16a8d5403a45ac5ae463ec9f00` |
| `KIP126/AdamsSynthetic/Standard/Separation.lean` | `ba0da5ea44e3ca3aa11e075646bd85424047bdfb4997d7812c2dcf38d386bd1b` | `a121fcd827cadf0de6d2fecc6ed46ef5083f26e04608e6a12867eac739294afd` |
| `KIP126/Literature/Standard.lean` | `f73c1ad8b6fda516b8fac98758492b67e258e4692ce280b11719d6922f114377` | `bd23b61c2a2dafbdd801ff3d0af25a358284a67b14034418932aab3d3b0aeb6f` |
| `KIP126/Main/ChoiceIndependence.lean` | `0db94baeddfa638a570f3acbc329407e17e237cfd50f13496e6b3e1872467aba` | `4094efc10e5b05faba803648e3f98a4ce8696b045f8a6fb7179e0163225820be` |
| `KIP126/Main/Internal/Choice/Invariance.lean` | `3d95910ada61d47265e5563cc15a1b214f97e8e8bbc1729631b82bede0362a01` | `92856f6d5b0ce04f4e1d3875e347d12f10d22a34a0fa5617c58b4f49873cb1cb` |
| `KIP126/Main/Internal/Choice/OrderTwo.lean` | `73f209f89ac62ebec27b2bb0443cdf8dbceb9c651ace35361cc1df980242bb7d` | `36d1dbdf573cf420c7fb78560fd7b0bc807430c8472d5ed0dc83080040ac20af` |
| `KIP126/Main/Internal/High125/Injectivity.lean` | `32d6476fec0fc8ac68152d7f86e8a8ec3a4a5c809dd865c67aa001a9f40d36f7` | `a311839e3c457b7e24160ea734a5a3f9d61d8153eb1a09363e129fd724fdbff9` |
| `KIP126/Main/Internal/High125/Source.lean` | `8e388410bb8ab3e73c735462e4e5c60219eddd6fedf78d69e6615c697e1227ba` | `183e7a9bf4ea394a526c83986d0b0318e971737e738a872e3d4731f80b87a82a` |
| `KIP126/Main/Internal/Theta/TodaExistence.lean` | `8071d5efa44940249ace4e7d52fe77f243839455a58051ec030ba4ed3183f591` | `dd8f32586841c6ca4040ce97d14d2d7d8d02664d58e94b1bab5cea032c23ef0e` |
| `KIP126/Main/SectionSeven/NuTarget.lean` | `120acb2a156b3a9196cec874bfea5a3ffe2e37edb9fa44c2c6edebcd9e05b2ad` | `c768d01ececdfb7f3f1797fd53640324f26094f8bb665270c0994b29a5d844fe` |
| `KIP126/Main/SectionSeven/ThetaToda.lean` | `7f275f7f43e967074f6ab0840bbedd309582dfe0b374056e4b15672410e331f9` | `bbc942b9141b1aa1f3bab2926da945e2f751cb55076701df50ed3ca15fac4298` |
| `KIP126/ProofTools/GeneralizedMahowald/Filtration.lean` | `b565084919c083740b423cfdd04760ff4416e5d8c62b3f6f27dd2a908c80be93` | `54f61c7307af0f7b887137c1d16faaf0c0bc73f9c84d6963fcdfde5c0d45598b` |
| `KIP126/ProofTools/GeneralizedMahowald/HSource.lean` | `1c555391e7df56302a381725dd8994ba14abb067ec60437bbb62ba46dc79c3ab` | `bc9873ea098069c368c57fbfcbee0fa3b8be1699c16b17e09af64abcc053b774` |
| `KIP126/ProofTools/GeneralizedMahowald/MayCorrection.lean` | `56733d6ae5e514a8e1684d2bc378099ff540c73486a9e67177e28a6cdcf6c3de` | `4a15a2e989e0a63af90e7e3b781dfb9e3ebd726f0b05cbde73caf3a294b384fd` |
| `KIP126/ProofTools/GeneralizedMahowald/OctahedralPullback.lean` | `8d10546c24560a30db8d648194e079e4df7789b4642a2e982311f235f313e570` | `0f28af19433fde05db82a5dd2d8f715e872dde98eb6c981c9ff947b64164a17e` |
| `KIP126/ProofTools/GeneralizedMahowald/SphereMayCorrection.lean` | `cb2eaa9aaeabafe95da880076e5f4811d3df461ab1967fdafd59d208b45716bc` | `232d78c5b0cd24d816b3e5ce2c1eb0b11c67a7c564c8bb3c2a61358f05dd5aca` |
