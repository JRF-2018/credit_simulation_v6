import Mathlib
import CreditV6.Homogeneity

/-!
# 定理 A: 釣り合い経路の上で、多地域のモデルは一国のモデルに厳密に縮約できる

* 世界: N 地域のモデル `step p`(地域ごとにパラメータが違ってよい)。
* 一国のモデル: 同じ式の 1 地域版 `step pA`(パラメータ `pA` は、流れで重み付けた平均として作る)。
* まとめる写像 `aggState`: 1 次の量は地域の合計、0 次の量は 1 次の量で重み付けた平均(貸倒れ率は借入残高で、稼働率は資本で)。

世界が釣り合いの取れた成長経路の上にあり(全部の 1 次の量が同じ倍率 γ で伸び、比率は変わらない)、
一国のモデルがある時点で世界の合計と一致するなら、その後のすべての期で一致する(`world_reduction`)。

証明に使うのは、モデルの 1 期の写像が規模について 1 次同次であること(`step_hom`)と、
`aggState` が規模の作用と可換であること(`agg_act`)だけである。
「ある時点で一致する」(`hone`)は仮定である。Python の `aggregate` は、流れを重みにしてパラメータを作ることで、
これを(なめらかな min・max の効き方の違いを除いて)満たすようにしている。
-/

open Finset BigOperators

namespace CreditV6

variable {N : ℕ}

/-- 重み付きの平均(重みの和が 0 なら 0)。 -/
noncomputable def wavg (w v : Vec N) : ℝ := (∑ i, w i * v i) / ∑ i, w i

/-- 世界の状態を、一国の状態にまとめる。 -/
noncomputable def aggState (x : State N) : State 1 where
  K := fun _ => ∑ i, x.K i
  L := fun _ => ∑ i, x.L i
  B := fun _ => ∑ i, x.B i
  S := fun _ => ∑ i, x.S i
  Pi_e := fun _ => ∑ i, x.Pi_e i
  Pi_prev := fun _ => ∑ i, x.Pi_prev i
  E_prev := fun _ => ∑ i, x.E_prev i
  Y_prev := fun _ => ∑ i, x.Y_prev i
  loss := fun _ => wavg x.L x.loss
  u_prev := fun _ => wavg x.K x.u_prev

lemma sum_smul_vec (c : ℝ) (v : Vec N) : ∑ i, (c • v) i = c * ∑ i, v i := by
  simp [Finset.mul_sum]

lemma wavg_smul {c : ℝ} (hc : 0 < c) (w v : Vec N) : wavg (c • w) v = wavg w v := by
  unfold wavg
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show ∑ i, c * w i * v i = c * ∑ i, w i * v i by rw [Finset.mul_sum]; congr 1; ext i; ring,
    ← Finset.mul_sum, mul_div_mul_left _ _ hc.ne']

/-- まとめる写像は、規模の作用と可換。 -/
lemma agg_act {c : ℝ} (hc : 0 < c) (x : State N) : aggState (x.act c) = (aggState x).act c := by
  ext i <;> simp [aggState, State.act, wavg_smul hc, Finset.mul_sum]

/-- **定理 A**: 釣り合い経路の上では、一度一致した一国のモデルは、世界の合計とずっと一致する。
地域ごとのパラメータは違ってよい。 -/
theorem world_reduction (p : Params N) (pA : Params 1) (x₀ : State N) (γ : ℝ) (hγ : 0 < γ)
    (hray : step p x₀ = x₀.act γ) (hone : step pA (aggState x₀) = aggState (step p x₀)) :
    ∀ n : ℕ, (step pA)^[n] (aggState x₀) = aggState ((step p)^[n] x₀) :=
  exact_reduction_on_ray_S (step p) (step pA) aggState (step_hom p) (step_hom pA)
    (fun _ hc x => agg_act hc x) x₀ γ hγ hray hone

end CreditV6
