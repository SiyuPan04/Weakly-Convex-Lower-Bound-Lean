# 论文编号与 Lean 声明对照

参考文稿为 Jiajin Li 和 Siyu Pan 的 *Optimal Oracle Complexity for Weakly Convex Optimization*（`WC.pdf`，2026-11-12）。下表按文稿顺序列出 **24 个编号陈述**：5 个定义、1 个条件、1 个 Fact、2 个定理、11 个引理、4 个命题。页码是**陈述开始**的印刷页码；一行可以对应多个 Lean 定义或定理。[机器可读清单](wclb_coverage.json)列出了对应声明，表中链接给出主要入口。

| 页 | 编号 | 数学内容 | Lean 入口 |
| ---: | --- | --- | --- |
| 3 | 定理 1 | 对固定的正参数，充分小的精度给出与失败概率参数无关的复杂度下界 | [`WCLB.main_for_sufficiently_small`、`WCLB.main_for_sufficiently_small_nonneg_gap`](WCLB/Main.lean) |
| 4 | 定义 1 | 弱凸、全局 Lipschitz、初始函数值差距有界的函数类 | [`WC.Admissible`、`WC.gapBound_iff_inf`](WC/Basic.lean)；[`WC.Model.Instance`](WC/Model.lean) |
| 5 | 定义 2 | 通过 Moreau 包络梯度范数定义近似驻点 | [`WC.moreau_gradient_eq`](WC/Moreau.lean)；[`WC.Model.successProbability`](WC/Model.lean) |
| 5 | 定义 3 | 每次查询返回函数值和整个次微分集合 | [`WC.fullOracle`、`WC.fullOracle_measurable`](WC/Oracle.lean) |
| 5 | 定义 4 | 私有均匀随机种子、Borel 决策及查询序列 | [`WC.Model.BorelAlgorithm`、`WC.Model.trajectory`](WC/Model.lean)；[单位区间种子](WC/ModelSeedExtension.lean) |
| 5 | 定义 5 | 在算法子类和实例子类上定义 oracle 复杂度 | [`WCLB.Model.oracleComplexityOn`](WCLB/Model.lean)；[`oracleComplexityOn_univ`](WCLB/ModelClass.lean) |
| 6 | 定理 2 | 小精度与初始差距条件下的显式复杂度下界 | [`WCLB.Model.MainTheorem`](WCLB/Model.lean)；[`WCLB.main`、正维度版本 `WCLB.main_positive_dimension`](WCLB/Main.lean) |
| 7 | 条件 1 | 未缩放困难实例需要满足的 C1–C4 | [`WCLB.UnscaledHardInstanceConditions`](WCLB/Conditions.lean)；[`WCLB.construction_satisfies_conditions`](WCLB/Verification.lean) |
| 8 | 引理 1 | 单块的完整次微分至多多出一个坐标方向 | [`WC.euclideanTiltedBlock_frechetSubgradient_locality`](WC/BlockSubgradient.lean) |
| 10 | 引理 2 | 耦合函数的变分表示、按块展开的最大化目标 | [`WC.coupledFunction_variational`、`WC.weightedCoupledFunction_relay_expansion`](WC/Variational.lean) |
| 11 | 引理 3 | 进度函数的值域、梯度大小及梯度 Lipschitz 界 | [值域](WC/Block.lean)；[`WC.progressGradient_norm_le`、`WC.progressGradient_norm_sub_le`](WC/Progress.lean) |
| 11 | 引理 4 | 耦合函数的弱凸常数为 $9/2$ | [`WC.weaklyConvex_coupledFunction`](WC/CoupledCurvature.lean) |
| 12 | 命题 1 | Lipschitz 上界函数取有限值、有下界，且为 2-Lipschitz、$9/2$-弱凸 | [`WC.chainMajorant_finite`、`WC.chainMajorant_lipschitz`、`WC.chainMajorant_weaklyConvex`](WC/ChainMajorant.lean) |
| 13 | 引理 5 | 耦合函数的完整分块次微分公式，以及最优权重的刻画 | [`WC.subdifferential_coupledFunction_blockwise`](WC/RegroupedSubdifferential.lean)；[`WCLB.active_weight_characterization`](WCLB/Certificates.lean) |
| 13 | 引理 6 | 最大化点集合非空紧；上界函数的次微分等于相应次微分之并的凸包 | [`WC.chainMajorant_sources_nonempty`、`WC.chainMajorant_sources_isCompact`](WC/ChainMajorant.lean)；[`WC.chainMajorant_subdifferential`](WC/ChainSources.lean) |
| 14 | 引理 7 | 最大化点不超过查询点；两点不同时，最大化点处的次微分为单点集 | [`WCLB.source_order`、`WCLB.remote_source_subdifferential`](WCLB/Locality.lean) |
| 14 | 命题 2 | 投影前后的函数值及完整次微分相等，次微分包含于下一层子空间 | [`WCLB.robust_oracle_identity`](WCLB/Locality.lean) |
| 15 | Fact 1 | 未揭示坐标上门函数及导数为零、仿射项的严格排序、后续块的失活条件 | [`WCLB.fact_one`](WCLB/Certificates.lean) |
| 15 | 引理 8 | 最大化点与查询点的位移在下一层之外为零 | [`WCLB.remote_source_displacement`](WCLB/Certificates.lean) |
| 18 | 命题 3 | $T\ge MN/16$，终端隐藏坐标条件推出严格的 Moreau 梯度下界 | [`WCLB.terminal_stationarity`](WCLB/TerminalSubspace.lean)；[`WCLB.terminal_diagonal_barrier`](WCLB/Construction.lean) |
| 18 | 引理 9 | (i) 不活跃集合 $Z$ 的坐标与距离界；(ii) 最大化点严格半径界；(iii) 远离 $Z$ 时每个次梯度的范数下界 | [`WCLB.terminal_geometry`](WCLB/Certificates.lean)；[`WCLB.source_radius_lt_three`](WCLB/Construction.lean)；[`WCLB.off_terminal_subgradient_lower`](WCLB/OffTerminal.lean) |
| 22 | 命题 4 | 未缩放构造的初始函数值差距至多为 $5M/N$ | [`WCLB.initial_gap_le_five`](WCLB/Construction.lean) |
| 23 | 引理 10 | 半径 $4R$ 之外的完整 oracle 和梯度范数，以及至少 $N$ 个小坐标所保证的梯度下界 | [`WCLB.radial_exterior_oracle`](WCLB/RadialOracle.lean)；[`WCLB.radial_exterior_gradient`、`WCLB.radial_moreau_barrier`](WCLB/Radial.lean) |
| 26 | 引理 11 | 在 (6.5) 的维度条件下，前 $T$ 个查询与任意 Borel 输出同时满足梯度下界，概率至少 $1-\delta$ | [`WCLB.logarithmicDimensionBound`](WCLB/Budget.lean)；[`WCLB.randomized_reduction`](WCLB/RandomizedReduction.lean) |

第 9 页 Remark 3 中相邻块的两个激活阈值另见 [`WCLB.unstarted_relay_thresholds`](WCLB/Certificates.lean)。

## 如何核对第 6 节

[式 (6.1)](WCLB/Radial.lean)对应 `WCLB.radial_subgradient_inner_lower`。其中 $K=MN$，径向函数使用 $R=2^{18}(M+\sqrt K)$。引理 10 的两个结论分别处理 $\lVert z\rVert\ge 4R$ 与至少 $N$ 个投影坐标不大于 $\eta$ 的情形；两处梯度都是径向函数自身的 Moreau 包络梯度。

引理 11 的概率空间是 Haar 正交标架与独立私有种子的乘积。[`WCLB.randomized_reduction_fixed_frame`](WCLB/RandomizedReduction.lean) 对标架取平均；同文件的 `physical_joint_barrier_logarithmic` 把联合事件传到原参数尺度，`physical_hard_instance_logarithmic` 给出复杂度定义所需的成功概率上界。两步沿用论文的同一个维度条件：

```math
d \ge K+1+\frac{128 R^2}{9\eta^2}\log\frac{2K(T+1)}{\delta}.
```

## 核验范围

[验证脚本](scripts/check_wclb.py)检查构建、映射的声明及其传递公理依赖。可运行 `python3 scripts/check_wclb.py --paper /path/to/WC.pdf` 额外核对论文文件的 SHA-256：

```text
002d3616e51469ac2bbc2c12a3e40236b3214cdc1409e3b9bee7cb3e0df63c9c
```

哈希标识文稿版本；Lean 检查形式陈述与证明。表中页码与数学说明用于人工核对二者的含义。
