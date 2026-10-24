import Mathlib
import CreditV6.TheoremB
import CreditV6.Linearization

/-!
# 定理 B と定理 B′ の関係: 共通の核と、二つの当てはめ

定理 B(`TheoremB.lean`)と定理 B′(`Linearization.lean`)は、次の**共通の核**の二つの当てはめである。

**共通の核**(`iterate_two_modes`、`ratio_tendsto_zero`): 線形の写像 `f` に、固有値 `λ₁`, `λ₂` の固有ベクトル
`u₁`, `u₂` があれば、状態 `α u₁ + β u₂` は n 期後に `(α λ₁ⁿ) u₁ + (β λ₂ⁿ) u₂` になる。
係数の比は毎期 `λ₂/λ₁` 倍になり、`|λ₂| < λ₁` なら 0 に近づく。`u₁` が釣り合い経路の方向、
`u₂` が構成比のずれの方向なら、これは「構成比が釣り合い経路の比重に近づく」ことである。

当てはめるには、`λ₁` の固有ベクトル(釣り合い経路の方向)と、`|λ₂| < λ₁` を満たす `λ₂` の固有ベクトル
(ずれの方向)を用意すればよい。二つの定理は、それぞれ次のように用意する。

| | 写像 `f` | `λ₁` と `u₁`(釣り合い経路) | `λ₂` と `u₂`(ずれ)、`\|λ₂\| < λ₁` |
|---|---|---|---|
| 定理 B | 2×2 の線形の核 | `lam1`, `v1`(`step_v1`) | `lam2`, `v2`(`step_v2`)、`lam_gap`(つながり `b, c > 0` から) |
| 実際のモデル | モデルの 1 期の写像のヤコビアン `J` | **γ と規模の方向 `P₁ x₀`(定理 B′)** | 仮定(数値で確かめる: IPYNB 第 14.8 節) |

つまり、**定理 B′ は、実際のモデルで定理 B の `λ₁` の役を果たすものを与える定理**である(だから B′ と呼ぶ)。
実際のモデルでは、ずれの方向の固有値が `|λ₂| < γ` を満たすことは Lean では示しておらず、
Python のモデルのヤコビアンを数値で求めて確かめている。
-/

namespace CreditV6.TwoModes

section core
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **共通の核(1)**: 線形の写像で、二つの固有ベクトルに分けた状態は、それぞれの固有値の冪で伸びる。 -/
theorem iterate_two_modes (f : V → V) (hlin : ∀ (α β : ℝ) (u w : V), f (α • u + β • w) = α • f u + β • f w)
    (u₁ u₂ : V) (l₁ l₂ : ℝ) (h₁ : f u₁ = l₁ • u₁) (h₂ : f u₂ = l₂ • u₂) (α β : ℝ) (n : ℕ) :
    f^[n] (α • u₁ + β • u₂) = (α * l₁ ^ n) • u₁ + (β * l₂ ^ n) • u₂ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hlin, h₁, h₂, smul_smul, smul_smul, pow_succ, pow_succ]
    congr 1 <;> ring_nf

end core

/-- **共通の核(2)**: 係数の比は毎期 `λ₂/λ₁` 倍になる。 -/
theorem ratio_eq (l₁ l₂ : ℝ) (h₁ : l₁ ≠ 0) (α β : ℝ) (n : ℕ) :
    (β * l₂ ^ n) / (α * l₁ ^ n) = (β / α) * (l₂ / l₁) ^ n := by
  rw [div_pow]
  by_cases hα : α = 0
  · simp [hα]
  · field_simp

/-- **共通の核(3)**: `|λ₂| < λ₁` なら、係数の比は 0 に近づく。 -/
theorem ratio_tendsto_zero (l₁ l₂ : ℝ) (hgap : |l₂| < l₁) (α β : ℝ) :
    Filter.Tendsto (fun n : ℕ => (β * l₂ ^ n) / (α * l₁ ^ n)) Filter.atTop (nhds 0) := by
  have h1 : 0 < l₁ := lt_of_le_of_lt (abs_nonneg _) hgap
  have hr : |l₂ / l₁| < 1 := by rw [abs_div, abs_of_pos h1, div_lt_one h1]; exact hgap
  have := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).const_mul (β / α)
  rw [mul_zero] at this
  refine this.congr (fun n => ?_)
  rw [ratio_eq l₁ l₂ h1.ne' α β n]

/-! ## 当てはめ 1: 定理 B(2×2 の線形の核) -/

section theoremB
open CreditV6.LinearCore
variable (A : M2) (hb : 0 < A.b) (hc : 0 < A.c)
include hb hc

/-- 定理 B の `iterate_decomp` は、共通の核の当てはめとして出てくる。 -/
theorem theoremB_iterate (α β : ℝ) (n : ℕ) :
    (LinearCore.step A)^[n] (α • v1 A + β • v2 A) = (α * lam1 A ^ n) • v1 A + (β * lam2 A ^ n) • v2 A :=
  iterate_two_modes (LinearCore.step A) (step_add_smul A) (v1 A) (v2 A) (lam1 A) (lam2 A)
    (step_v1 A hb hc) (step_v2 A hb hc) α β n

/-- **定理 B(共通の核から)**: つながっていれば(`b, c > 0`、`a + d > 0`)、ずれの係数と
釣り合い経路の係数の比は 0 に近づく。 -/
theorem theoremB_tendsto (had : 0 < A.a + A.d) (α β : ℝ) :
    Filter.Tendsto (fun n : ℕ => (β * lam2 A ^ n) / (α * lam1 A ^ n)) Filter.atTop (nhds 0) :=
  ratio_tendsto_zero (lam1 A) (lam2 A) (lam_gap A hb hc had) α β

end theoremB

/-! ## 当てはめ 2: 実際のモデル(定理 B′ が `λ₁ = γ` を与える) -/

section model
open CreditV6.Linearization
variable {N : ℕ}

/-- **実際のモデルの線形化での定理 B**: モデルの 1 期の写像が釣り合い経路の上の点 `x₀`
(`step p x₀ = x₀.act γ`)で微分可能で、そのヤコビアン `J` に、`|λ| < γ` の固有ベクトル `u`
(構成比のずれの方向)があるとする。このとき、線形化した写像で n 期進めた状態は
`(α γⁿ) P₁x₀ + (β λⁿ) u` になり、ずれの係数と釣り合い経路の係数の比は 0 に近づく。
`λ₁ = γ` と、その固有ベクトルが規模の方向 `P₁x₀` であることは、定理 B′(`step_jacobian_on_ray`)が与える。 -/
theorem model_theoremB (p : Params N) (x₀ : State N) (γ : ℝ) (hray : step p x₀ = x₀.act γ)
    (J : SVec N →L[ℝ] SVec N) (hJ : HasFDerivAt (stepV p) J (enc x₀))
    (u : SVec N) (l : ℝ) (hu : J u = l • u) (hgap : |l| < γ) (α β : ℝ) :
    (∀ n : ℕ, (⇑J)^[n] (α • P1 (enc x₀) + β • u) = (α * γ ^ n) • P1 (enc x₀) + (β * l ^ n) • u) ∧
    Filter.Tendsto (fun n : ℕ => (β * l ^ n) / (α * γ ^ n)) Filter.atTop (nhds 0) := by
  have hγ := step_jacobian_on_ray p x₀ γ hray J hJ          -- 定理 B′: λ₁ = γ
  refine ⟨fun n => iterate_two_modes (⇑J) (fun a b u w => by simp [map_add, map_smul])
    (P1 (enc x₀)) u γ l hγ hu α β n, ratio_tendsto_zero γ l hgap α β⟩

end model

end CreditV6.TwoModes
