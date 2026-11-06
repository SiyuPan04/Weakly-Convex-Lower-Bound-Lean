# 新稿逐项覆盖

源文件：`wclb_snapshot/main.tex`。快照与提供的稿件源文件逐字节一致；来源及文件哈希见 `wclb_snapshot/provenance.json`。

剥离 TeX 注释后，共有 **22 个正式陈述**：5 项定义、1 项 hard-instance condition、16 项定理/引理/命题。全部陈述已有对应定义或实际证明；主定理、新稿精确固定半径的具体构造和对数维数 randomized-reduction 均已闭合。最终统一构建与公理审计由 `scripts/check_wclb.py` 核验。

| 新稿行号 | 陈述 | Lean 入口 | 状态 |
|---|---|---|---|
| 557 | Informal complexity theorem | `WCLB.main`、`WCLB.main_explicit` | 已证 |
| 649 | Function class | `WC.Admissible`、`WC.gapBound_iff_inf`、`WCLB.Model.Instance` | 已编码 |
| 664 | Moreau stationary point | `WC.moreauEnvelope`、`WC.moreau_gradient_eq`、`WCLB.Model.successProbability` | 已编码，梯度存在性已证 |
| 689 | Full first-order oracle | `WC.subdifferential`、`WC.fullOracle_measurable` | 已编码，可测性已证 |
| 697 | Randomized algorithm | `WCLB.Model.BorelAlgorithm`、`WC.Model.UnitBorelAlgorithm.extend_trajectory` | 已编码，unit-seed 等价性已证 |
| 736 | Oracle complexity | `WCLB.Model.oracleComplexityOn`、`WCLB.Model.oracleComplexityOn_univ` | 已编码 |
| 772 | Main theorem | `WCLB.main_explicit`、`WCLB.main` | 已证 |
| 870 | Unscaled C1–C4 | `WCLB.UnscaledHardInstanceConditions`、`WCLB.construction_satisfies_conditions` | 已逐项填满 |
| 1003 | Tilted-block locality | `WC.euclideanTiltedBlock_frechetSubgradient_locality` | 已证 |
| 1153 | Variational representation | `WC.coupledFunction_variational`、`WC.weightedCoupledFunction_relay_expansion` | 已证 |
| 1208 | Progress regularity | `WC.hasGradientAt_euclideanProgress`、`WC.progressGradient_norm_sub_le` | 已证 |
| 1264 | Coupled weak convexity | `WC.weaklyConvex_coupledFunction` | 已证 |
| 1313 | Majorant regularity | `WC.chainMajorant_finite`、`WC.chainMajorant_lipschitz`、`WC.chainMajorant_weaklyConvex` | 已证 |
| 1409 | Diagonal width | `WC.diagonal_filtration_width` | 直和及商维数字面陈述已证 |
| 1448 | Full raw subdifferential | `WC.subdifferential_coupledFunction_blockwise`、`WC.mem_coupledBlockSubgradients_iff` | 原稿分块显示式已证 |
| 1527 | Sources and majorant subdifferential | `WC.chainMajorant_sources_isCompact`、`WC.chainMajorant_subdifferential` | 完整实际 source 公式已证 |
| 1572 | Source order | `WCLB.source_order`、`WCLB.remote_source_subdifferential` | 坐标次序及远源 singleton 已证 |
| 1642 | Robust oracle identity | `WCLB.robust_oracle_identity` | 函数值、完整次微分及 support 已证 |
| 2040 | Terminal stationarity | `WCLB.unscaled_terminal_barrier`、`WCLB.terminal_stationarity`、`WCLB.terminal_subspace_barrier` | horizon、子空间及鲁棒坐标三部分均已证 |
| 2535 | Initial gap | `WCLB.initial_gap_le_five` | 新稿 `5M/N` 已证 |
| 2667 | Prescribed radial modification | `WCLB.radial_moreau_barrier`、`WCLB.radial_exterior_gradient`、`WCLB.radial_exterior_oracle` | 新稿精确固定半径已证 |
| 2901 | Randomized reduction | `WCLB.randomized_reduction` | 精确对数维数及联合概率已证 |

## 证明路线与范围

`WCLB.main` 的准确率条件与新稿一致，并且给出 `c₀=1/512`、`c=2⁻²⁹`，不依赖置信参数 `ν`。最终主定理通过 `WCLB.uniformFamilies` 使用新稿精确固定半径的实际函数族；共享的 WC 库提供已证明的解析引理与缩放归约。所有构造字段均有实际证明，没有假设新的函数族存在。

与此同时，新稿明确指定的 `R=2¹⁸(M+√K)` 和归一化 max 函数有独立证明。它们没有被旧工程的较大 `chainWallRadius` 暗中替换。其正则性、初始 gap、外部完整 oracle、真实 Moreau 梯度屏障和 prefix 局部性均使用实际定义。

终端驻点命题通过已建立的 8-band 凸组合下界证明，这给出比所需终端数值更强的估计。原稿证明内部使用的 `r₀=1/(360√N)` 和二进制分组并未作为未证明的证书假设；这种证明路线变化不改变已证命题。

最后一项新稿随机旋转引理证明的是**实际旋转与 seed 联合概率**以及**原稿精确对数维数预算**。`WCLB.Concentration.sphere_mgf_le` 从实际球面不变概率证明 MGF；闭 bad event 的指数尾界、适应性 stabilizer averaging、完整 oracle 耦合与有限并集界构成 `WCLB.randomized_reduction` 的证明。旧工程中的 polynomial dimension bound 未被当作该项证据。

机器可读声明清单为 `wclb_coverage.json`，复现核对入口为 `scripts/check_wclb_coverage.lean`。
