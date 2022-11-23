# lean-reducibility
Lean3で計算可能性理論を形式化する。Iterated trees of strategiesを形式化する。

## 構造
 - `lib.lean`
 - `rpartrec.lean`：相対的計算可能性
 - `coding.lean`：神託付き万能チューリングマシン
 - `function.lean`：様々な計算可能な関数
 - `reducibility.lean`：チューリング還元に関する諸定理
 - `tree.lean`
 - `its.lean`: （簡易版）Iterated trees of strategiesの定義や定理
 - `its_computable.lean`
 - `friedberg_muchnik.lean`：Friedberg-Muchnikの定理
 - `degree.lean`：チューリング次数の構造

## 定義
 - 相対的計算可能性 `rpartrec`
 - チューリング還元可能性 `(≤ₜ)`
 - インデックス`e`の神託`f`のもとでの万能関数 `⟦e⟧^f x`
 - チューリングジャンプ `(′)`
 - 相対的r.e.集合 `rre_pred`
 - 算術的階層 `𝚷⁰`, `𝚺⁰`
 - チューリング次数 `turing_degree`, `𝐃`
 - r.e.チューリング次数 `re_degree`, `𝐑`

## 定理
 - $A <_T A^\prime$
   - `lt_Jump : ∀ A, A <ₜ A′`
 - チューリング次数の上半束構造
   - `turing_degree.semilattice_sup_bot : semilattice_sup_bot 𝐃`
 - Friedberg-Muchnikの定理
   - `friedberg_muchnik.incomparable_re_sets : ∃ I₀ I₁ : set ℕ, r.e. I₀ ∧ r.e. I₁ ∧ I₁ ≰ₜ I₀ ∧ I₀ ≰ₜ I₁`
   - `turing_degree.friedberg_muchnik : ∃ a b : 𝐑, ¬a ≤ b ∧ ¬b ≤ a`


## 参考文献
 * mathlib https://github.com/leanprover-community/mathlib
 * Robert I. Soare, Recursively Enumerable  Sets and Degrees
 * Hartley Rogers Jr, Theory of Recursive Functions and Effective Computability
 * Manuel Lerman, A Framework for Priority Argument
   https://www2.math.uconn.edu/~lerman/GFposet.pdf
