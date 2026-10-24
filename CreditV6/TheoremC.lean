import Mathlib

/-!
# 定理 C: 一国モデルのずれは「成長率のばらつき × 構成比の動き」で抑えられる

N 地域の線形の核 `x' = A x` を考える。世界の合計 `S = Σ xᵢ` の 1 期の伸び率は、
各地域の「列の和」`gᵢ = Σⱼ A j i`(地域 i の 1 単位が、次の期に世界全体で生む量)を、
**その時点の構成比** `wᵢ = xᵢ/S` で重み付けた平均になる(`sum_step`)。

一国モデルは、縮約した時点の構成比 `w⁰` で重みを固定しているので、伸び率は `Σ gᵢ w⁰ᵢ` のまま変わらない。
その差は `Σ (gᵢ − ḡ)(wᵢ − w⁰ᵢ)`(`ḡ` は任意の定数)と書け(`growth_gap`)、
`max |gᵢ − ḡ| · Σ |wᵢ − w⁰ᵢ|` 以下である(`growth_gap_bound`)。
つまり、ずれは「地域の成長率のばらつき」と「構成比の動き」の両方があって初めて生じる。
定理 B により、つながった世界では構成比の動きが幾何級数的に小さくなるので、ずれは育たない。

n 期の累積については、毎期の伸び率の比を `1 + u_k` とすると、n 期後の世界の合計と一国モデルの比は
`Π (1 + u_k)` で、`|Π (1 + u_k) − 1| ≤ Π (1 + |u_k|) − 1` である(`prod_bound`)。

実際のモデルの式についての対応物(定理 C′)は `TheoremCModel.lean` にある。そこでは、1 期の縮約誤差が
1 次の近似で構成比のずれだけで決まることを示し、成長率のばらつき `G` の役は誤差の微分のノルムが果たす。
-/

open Finset BigOperators

namespace CreditV6.ErrorBound

variable {N : ℕ}

/-- 線形の写像の後の合計は、列の和を重みにした和になる。 -/
theorem sum_step (A : Fin N → Fin N → ℝ) (x : Fin N → ℝ) :
    ∑ j, ∑ i, A j i * x i = ∑ i, (∑ j, A j i) * x i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]

/-- 1 期のずれは、成長率の偏差と構成比の動きの積の和になる。 -/
theorem growth_gap (g w w0 : Fin N → ℝ) (gbar : ℝ) (hw : ∑ i, w i = ∑ i, w0 i) :
    ∑ i, g i * w i - ∑ i, g i * w0 i = ∑ i, (g i - gbar) * (w i - w0 i) := by
  have h : ∑ i, gbar * (w i - w0 i) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hw, sub_self, mul_zero]
  have e : ∑ i, (g i - gbar) * (w i - w0 i) = ∑ i, g i * (w i - w0 i) - ∑ i, gbar * (w i - w0 i) := by
    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
  rw [e, h, sub_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

/-- **定理 C(1 期)**: 1 期のずれは、成長率のばらつきの最大値と、構成比の動きの合計の積以下。 -/
theorem growth_gap_bound (g w w0 : Fin N → ℝ) (gbar G : ℝ) (hG : ∀ i, |g i - gbar| ≤ G)
    (hw : ∑ i, w i = ∑ i, w0 i) :
    |∑ i, g i * w i - ∑ i, g i * w0 i| ≤ G * ∑ i, |w i - w0 i| := by
  rw [growth_gap g w w0 gbar hw, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hG i) (abs_nonneg _)

lemma one_le_prod_one_add_abs (u : ℕ → ℝ) (n : ℕ) : 1 ≤ ∏ k ∈ range n, (1 + |u k|) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_range_succ]; nlinarith [abs_nonneg (u n)]

/-- **定理 C(n 期)**: 毎期の比が `1 + u_k` なら、積と 1 のずれは `Π (1 + |u_k|) − 1` 以下。 -/
theorem prod_bound (u : ℕ → ℝ) (n : ℕ) :
    |∏ k ∈ range n, (1 + u k) - 1| ≤ ∏ k ∈ range n, (1 + |u k|) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    set P := ∏ k ∈ range n, (1 + u k)
    set Q := ∏ k ∈ range n, (1 + |u k|)
    have hQ : 1 ≤ Q := one_le_prod_one_add_abs u n
    have e : P * (1 + u n) - 1 = (P - 1) * (1 + u n) + u n := by ring
    have h2 : |1 + u n| ≤ 1 + |u n| := by simpa using abs_add_le (1 : ℝ) (u n)
    rw [e]
    calc |(P - 1) * (1 + u n) + u n| ≤ |P - 1| * |1 + u n| + |u n| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (Q - 1) * (1 + |u n|) + |u n| := by
          have := mul_le_mul ih h2 (abs_nonneg _) (by linarith)
          linarith
      _ = Q * (1 + |u n|) - 1 := by ring

end CreditV6.ErrorBound
