import Mathlib

/-!
# 定理 B: つながっていれば、構成比は釣り合い経路の比重に幾何級数的に近づく

信用循環モデルの「線形の核」を考える。金融(借入・国債)を外し、需要の式と投資の式だけを残すと、
二つの地域の資本 `(K_B, K_C)` は、1 期ごとに 2×2 の行列で動く:

  `K_B' = a K_B + b K_C`,  `K_C' = c K_B + d K_C`。

対角の `a`, `d` は自分の資本が自分の次の期の資本を生む分、非対角の `b`, `c` は、貿易を通じて相手の需要が
自分の投資を生む分である。**つながっていなければ `b = c = 0`、つながっていれば `b, c > 0`。**

* つながっているとき(`b, c > 0`、`a + d > 0`)、二つの固有値は実数で `λ₁ > |λ₂|`。
  状態を「釣り合い経路の方向 `v₁`」と「ずれの方向 `v₂`」に分けると、ずれの係数と釣り合い経路の係数の比は、
  毎期ちょうど `λ₂/λ₁` 倍になる(`deviation_ratio`)。`|λ₂/λ₁| < 1` なので、構成比は釣り合い経路の比重へ
  幾何級数的に近づく。つながりが強い(`b c` が大きい)ほど `λ₁` と `λ₂` が離れ、近づくのが速い。
* つながっていないとき(`b = c = 0`)、二つの資本はそれぞれ `aⁿ`, `dⁿ` で伸び、`a ≠ d` なら
  構成比はずっと動き続ける(`unlinked_ratio`)。
-/

namespace CreditV6.LinearCore

/-- 2×2 の行列(線形の核の 1 期の写像)。 -/
structure M2 where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

variable (A : M2)

/-- 1 期の写像。 -/
def step (x : ℝ × ℝ) : ℝ × ℝ := (A.a * x.1 + A.b * x.2, A.c * x.1 + A.d * x.2)

/-- 判別式とその平方根。 -/
noncomputable def disc : ℝ := (A.a - A.d) ^ 2 + 4 * A.b * A.c
noncomputable def D : ℝ := Real.sqrt (disc A)

/-- 二つの固有値。 -/
noncomputable def lam1 : ℝ := (A.a + A.d + D A) / 2
noncomputable def lam2 : ℝ := (A.a + A.d - D A) / 2

/-- 固有ベクトル(`v₁` が釣り合い経路の方向、`v₂` がずれの方向)。 -/
noncomputable def v1 : ℝ × ℝ := (A.b, lam1 A - A.a)
noncomputable def v2 : ℝ × ℝ := (A.b, lam2 A - A.a)

lemma step_add_smul (α β : ℝ) (u w : ℝ × ℝ) :
    step A (α • u + β • w) = α • step A u + β • step A w := by
  ext <;> simp [step] <;> ring

section linked
variable (hb : 0 < A.b) (hc : 0 < A.c)
include hb hc

lemma disc_pos : 0 < disc A := by
  unfold disc; nlinarith [sq_nonneg (A.a - A.d), mul_pos hb hc]

lemma D_sq : D A ^ 2 = disc A := Real.sq_sqrt (disc_pos A hb hc).le

lemma D_pos : 0 < D A := Real.sqrt_pos.mpr (disc_pos A hb hc)

/-- `D > |a − d|`(つながりがあると、固有値が離れる)。 -/
lemma D_gt_abs : |A.a - A.d| < D A := by
  have h := D_sq A hb hc
  have hD := (D_pos A hb hc).le
  rw [← Real.sqrt_sq_eq_abs]
  unfold D
  apply Real.sqrt_lt_sqrt (sq_nonneg _)
  unfold disc; nlinarith [mul_pos hb hc]

/-- 固有値は特性方程式 `λ² − (a+d)λ + (ad − bc) = 0` を満たす。 -/
lemma char1 : lam1 A ^ 2 - (A.a + A.d) * lam1 A + (A.a * A.d - A.b * A.c) = 0 := by
  have h := D_sq A hb hc; unfold lam1; unfold disc at h; nlinarith [h]

lemma char2 : lam2 A ^ 2 - (A.a + A.d) * lam2 A + (A.a * A.d - A.b * A.c) = 0 := by
  have h := D_sq A hb hc; unfold lam2; unfold disc at h; nlinarith [h]

lemma step_v1 : step A (v1 A) = lam1 A • v1 A := by
  have h := char1 A hb hc
  ext
  · simp [step, v1]; ring
  · simp [step, v1]; nlinarith [h]

lemma step_v2 : step A (v2 A) = lam2 A • v2 A := by
  have h := char2 A hb hc
  ext
  · simp [step, v2]; ring
  · simp [step, v2]; nlinarith [h]

/-- 釣り合い経路の方向とずれの方向に分けた状態は、それぞれの固有値の冪で伸びる。 -/
theorem iterate_decomp (α β : ℝ) (n : ℕ) :
    (step A)^[n] (α • v1 A + β • v2 A) = (α * lam1 A ^ n) • v1 A + (β * lam2 A ^ n) • v2 A := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, step_add_smul, step_v1 A hb hc, step_v2 A hb hc,
      smul_smul, smul_smul, pow_succ, pow_succ]
    congr 1 <;> ring_nf

/-- どんな状態も、釣り合い経路の方向とずれの方向に分けられる。 -/
theorem decomp_exists (x : ℝ × ℝ) : ∃ α β : ℝ, x = α • v1 A + β • v2 A := by
  have hD := D_pos A hb hc
  have hb0 : A.b ≠ 0 := hb.ne'
  have h12 : lam1 A - lam2 A = D A := by unfold lam1 lam2; ring
  refine ⟨(x.2 - (lam2 A - A.a) * x.1 / A.b) / D A, ((lam1 A - A.a) * x.1 / A.b - x.2) / D A, ?_⟩
  ext
  · simp [v1, v2]; field_simp; rw [show lam1 A = lam2 A + D A by linarith]; ring
  · simp [v1, v2]; field_simp; linear_combination (-(x.2 * A.b)) * h12

/-- `λ₁ > |λ₂|`(つながりがあり、`a + d > 0` のとき)。 -/
theorem lam_gap (had : 0 < A.a + A.d) : |lam2 A| < lam1 A := by
  have hD := D_pos A hb hc
  rw [abs_lt]; unfold lam1 lam2; constructor <;> linarith

/-- **定理 B**: ずれの係数と釣り合い経路の係数の比は、毎期ちょうど `λ₂/λ₁` 倍になる。 -/
theorem deviation_ratio (had : 0 < A.a + A.d) (α β : ℝ) (n : ℕ) :
    (β * lam2 A ^ n) / (α * lam1 A ^ n) = (β / α) * (lam2 A / lam1 A) ^ n := by
  have h1 : 0 < lam1 A := lt_of_le_of_lt (abs_nonneg _) (lam_gap A hb hc had)
  rw [div_pow]
  by_cases hα : α = 0
  · simp [hα]
  · field_simp

/-- 減衰の率 `|λ₂/λ₁|` は 1 より小さい。 -/
theorem rate_lt_one (had : 0 < A.a + A.d) : |lam2 A / lam1 A| < 1 := by
  have hg := lam_gap A hb hc had
  have h1 : 0 < lam1 A := lt_of_le_of_lt (abs_nonneg _) hg
  rw [abs_div, abs_of_pos h1, div_lt_one h1]; exact hg

end linked

/-- つながっていないとき(`b = c = 0`)、二つの資本は `aⁿ`, `dⁿ` で別々に伸びる。
`a ≠ d` なら、資本の比 `K_C/K_B` は `(d/a)ⁿ` 倍になり、構成比は動き続ける。 -/
theorem unlinked_iterate (hb : A.b = 0) (hc : A.c = 0) (x : ℝ × ℝ) (n : ℕ) :
    (step A)^[n] x = (A.a ^ n * x.1, A.d ^ n * x.2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ext <;> simp [step, hb, hc, pow_succ] <;> ring

theorem unlinked_ratio (hb : A.b = 0) (hc : A.c = 0) (ha : A.a ≠ 0) (x : ℝ × ℝ) (hx : x.1 ≠ 0) (n : ℕ) :
    ((step A)^[n] x).2 / ((step A)^[n] x).1 = (A.d / A.a) ^ n * (x.2 / x.1) := by
  rw [unlinked_iterate A hb hc x n, div_pow]
  simp only
  field_simp

end CreditV6.LinearCore
