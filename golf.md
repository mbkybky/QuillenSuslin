# 证明简化方法

## 1. 先补接口，再删证明

很多成功的 golf 都来自先加入一个更自然的接口，让后面的证明自动变短。

典型例子：

- `TateAlgebra.renameEquiv` 把一对互逆的 `rename` 同态包装成 `AlgEquiv`。之后证明 `rename_norm_eq`、strict affinoid presentation 的互逆性时，不再手写 `hφψ`、`hψφ` 和 `congrArg`。
- `Integer.norm_eq`、`Integer.norm_le`、`Integer.algebraMap_eq_val`、`integerMap_val`、`Ideal.integer_mem_iff` 把常见 coercion 事实固定下来，后续大量 `change`、`Subtype.ext`、`map_sum` 展开可以由 `simp` 接管。
- `topNil_le_jacobson`、`ideal_integer_fg` 抽出后，`ideal_tfae_red_generate` 中原本很长的手写 Nakayama 证明变成调用 `Submodule.le_of_le_smul_of_le_jacobson_bot`。
- `reduction_mem_map_integerMap_ker_of_sub_topNil` 抽出后，多个 reduction kernel 证明共用同一个“减去 topNil lift 后落入 map kernel”的步骤。

经验：如果同一类 `Subtype.ext`、`Ideal.Quotient.eq`、`map_sum/map_mul` 反复出现，应优先考虑做成 lemma，而不是每处局部压缩。

## 2. 用库引理替代手写归纳

多个提交把手写交换代数引理、`Finset.induction_on`、`span_induction`、逐项估计，替换为 Mathlib 已有引理或已有引理的简单推论。

常用替换：

- 有限和的非阿基米德估计：
  `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`
  取代手写 `Finset.induction_on`。
- 有限积估计：
  `Finset.norm_prod_le` + `Finset.prod_le_one`
  取代逐项展开乘积。
- Tate 系数有界：
  `TateAlgebra.coeff_norm_le`、`norm_le_of_forall_coeff_le`
  取代手写 `ciSup` 上界。
- 趋于零的系数族有界：
  `bddAbove_range_of_cofinite`
  取代 `Bornology.IsBounded.exists_norm_le` 的中间构造。
- 截断多项式：
  `MvPowerSeries.truncFinset`、`MvPowerSeries.trunc'`
  取代手写 `Polynomial.ofFinsupp` 和复杂的 `Finset.sum_eq_single` 系数计算。
- 单位判别：
  `isUnit_one_sub_of_norm_lt_one`、`isUnit_of_norm_sub_lt_unit`
  取代显式构造几何级数逆元。
- 闭图、开映射、稠密延拓：
  `ContinuousLinearMap.isOpenMap`、`DenseRange.equalizer`、`IsDenseInducing.extend_eq`
  取代手工拼接连续性和等化子证明。
- 子模生成：
  `Submodule.smul_span`、`Submodule.span_le`
  取代对 `Submodule.span_induction` 的逐构造子证明。

经验：看到“对 finite set 归纳”“对 span 归纳”“逐系数证明有界”时，先搜库引理。

## 3. 用 `grw`、`gcongr`、`field_simp`、`ring` 收尾不等式和代数恒等式

长证明里常见大量：

- `norm_mul_le`
- `mul_le_mul_of_nonneg_left/right`
- `pow_le_one₀`
- `inv_mul_cancel₀`
- `mul_assoc/mul_comm/mul_left_comm`

golf 后的写法倾向于：

```lean
grw [norm_mul_le, h1, h2]
```

```lean
calc
  _ ≤ _ := by gcongr
  _ = _ := by ring
```

```lean
field_simp [norm_ne_zero_iff.mpr h]
```

经验：不等式链如果只是“乘以非负数保持不等式”“把 `* 1` 消掉”“除以正数”，优先尝试 `grw/gcongr/field_simp/ring_nf`，少写中间 `have`。

## 5. 用构造器和析构的短写法减少样板

反复出现的局部压缩：

- `constructor <;> intro h` 或 `constructor <;> rintro ...`
- `rintro ⟨x, hx, rfl⟩`
- `obtain ⟨_, ⟨x, hx, hnorm⟩, hlt⟩ := ...`
- `exact ⟨x, by simpa ..., by simpa ...⟩`
- `fun x ↦ ...` 直接证明简单全称命题。
- 不要写 `have h : ∀ a, P a := by intro a ...`；直接写 `have h (a : T) : P a := by ...`。
- `of_not_not fun h => ...` 处理否定目标。
- `False.elim <| ...` 或 `(...).elim` 处理矛盾。

例子：

```lean
have hφρ : φ.comp ρ = φ₀ :=
  TateAlgebra.hom_ext fun i ↦ by simp [ρ, eLeft, a, hφX (Sum.inl i)]
```

比 `apply TateAlgebra.hom_ext; intro i; simp ...` 更短。

## 6. 用等价和同构转移结构

许多长证明本质是在同构两边转移性质。golf 提交把这些证明改成标准转移：

- `RingEquiv.ofBijective ...`
- `AlgEquiv.ofAlgHom ...`
- `Module.IsCartesian.of_linearEquiv`
- `Module.IsPseudoCartesian.of_ringEquiv`
- `Submodule.IsStrictlyClosed.of_linearEquiv`
- `Submodule.IsStrictlyClosed.of_ringEquiv`
- `Submodule.Quotient.restrictScalarsEquiv_norm`

经验：如果证明中正在手写“把对象搬过去、再搬回来、范数保持不变”，应先尝试建立一个 `LinearEquiv` / `RingEquiv` / `AlgEquiv`，然后用转移 lemma。

## 8. 删除死代码和临时探索代码

提交中删除了：

- 未使用的 private lemma。
- 只服务旧证明的中间 lemma，例如可由结构字段直接证明的 `polynomialToTate_one`、`polynomialToTate_C`。

经验：proof golf 后要回头检查哪些辅助 lemma 已经没有独立价值。删掉它们能减少维护负担，也能避免后续 simp 搜索空间变大。

## 9. 使用更自然的参数和命名

后期提交把一些参数改成隐式或改用 `.val`：

```lean
theorem coeff_mem_span_uniformizer_pow_of_norm_le {ϖ : 𝒪[k]} ...
```

调用处从：

```lean
coeff_mem_span_uniformizer_pow_of_norm_le ϖ hϖ n ...
```

变成：

```lean
coeff_mem_span_uniformizer_pow_of_norm_le hϖ n ...
```

同时把 `‖(ϖ : k)‖` 改成 `‖ϖ.val‖` 或 `‖ϖ.1‖`，减少 coercion 歧义。

经验：若一个参数几乎总能从另一个假设推断出来，应考虑设为隐式。若 coercion 反复卡住，使用 `.val`/`.1` 明确底层对象。

## 可复用检查清单

下次简化 Lean 证明时可以按这个顺序检查：

1. 有没有库引理能替代手写归纳、span induction、系数估计？
2. 目标是不是可以通过 `ext`、`Subtype.ext`、`Ideal.Quotient.eq`、`RingHom.mem_ker` 变成 `simp` 目标？
3. 不等式链能否交给 `grw`、`gcongr`、`field_simp`、`linarith/nlinarith`？
4. 是否正在手写同构转移？若是，先建立 `Equiv`/`AlgEquiv`/`LinearEquiv`。
5. 是否能把 `∃ a, P a ∧ Q a` 改成 `∃ (a) (_ : P a), Q a` 一类更好析构的形状？
6. 新增 helper 后，旧的 private lemma、探索代码和中间 `have` 是否已经可以删除？
