import Mathlib

/-!
# 信用循環モデルの連結と縮約: 言える部分の証明

単位(地域・国・企業)の集合を有限型 `ι` とし、単位 `i` から単位 `j` への支払いを `f i j` で表す。
連結(縮約)は、単位を「どのまとまりに入れるか」を表す写像 `π : ι → κ` で与える。
-/

open Finset BigOperators

namespace CreditV6

/-- 支払いの行列 `f` を、写像 `π` でまとめた支払いの行列(まとまりどうしの支払いの合計)。 -/
noncomputable def consolidate {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (π : ι → κ) (f : ι → ι → ℝ) : κ → κ → ℝ :=
  fun J K => ∑ i ∈ univ.filter (fun i => π i = J), ∑ j ∈ univ.filter (fun j => π j = K), f i j

/-- 単位 `i` の純受取(受け取り − 支払い)。経常収支や純貸出に当たる。 -/
def netReceipt {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) (i : ι) : ℝ :=
  ∑ j, f j i - ∑ j, f i j

/-- T2a: 世界全体の純受取の和は 0(全地域の経常収支の和は 0)。 -/
theorem sum_netReceipt_eq_zero {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) :
    ∑ i, netReceipt f i = 0 := by
  unfold netReceipt
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  ring

/-- まとまりごとに和を取ってから足すと、全体の和になる。 -/
lemma sum_fibers {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (π : ι → κ) (g : ι → ℝ) :
    ∑ J, ∑ i ∈ univ.filter (fun i => π i = J), g i = ∑ i, g i :=
  Finset.sum_fiberwise univ π g

/-- T2b: まとまりの純受取は、構成する単位の純受取の和に等しい(まとまりの中の取引は相殺される)。 -/
theorem netReceipt_consolidate {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (π : ι → κ) (f : ι → ι → ℝ) (J : κ) :
    netReceipt (consolidate π f) J = ∑ i ∈ univ.filter (fun i => π i = J), netReceipt f i := by
  unfold netReceipt consolidate
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [sum_fibers π (fun i => ∑ j ∈ univ.filter (fun j => π j = J), f i j), Finset.sum_comm]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact sum_fibers π (fun j => f i j)

/-- 二段の和: まとまり J(σ J = M となるもの)ごとに、J に入る単位の和を取って足すと、
σ ∘ π で M に入る単位の和になる。 -/
lemma fiber_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [DecidableEq μ]
    (π : ι → κ) (σ : κ → μ) (M : μ) (g : ι → ℝ) :
    ∑ J ∈ univ.filter (fun J => σ J = M), ∑ i ∈ univ.filter (fun i => π i = J), g i
      = ∑ i ∈ univ.filter (fun i => σ (π i) = M), g i := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun i => σ (π i) = M))
        (t := univ.filter (fun J => σ J = M)) (g := π) (by intro i hi; simpa using hi)]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [mem_filter, mem_univ, true_and] at hJ
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i; simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h; exact ⟨by rw [h, hJ], h⟩
  · intro h; exact h.2

/-- T1: 段階的に連結しても、一度に連結しても同じ(連結は写像の合成と整合する)。
二地域の連結 B ⊕ C を繰り返して (B ⊕ C) ⊕ D と B ⊕ (C ⊕ D) を作っても、どちらも
三地域を一度に連結したものに等しい。これが「連結の結合性」の正確な形である。 -/
theorem consolidate_comp {ι κ μ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [DecidableEq μ]
    (π : ι → κ) (σ : κ → μ) (f : ι → ι → ℝ) :
    consolidate σ (consolidate π f) = consolidate (σ ∘ π) f := by
  funext M N
  unfold consolidate
  simp only [Function.comp]
  rw [← fiber_comp π σ M]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact fiber_comp π σ N (fun j => f i j)

/-- 何もまとめない連結(恒等写像)は、元のままである(単位元)。 -/
theorem consolidate_id {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ι → ℝ) :
    consolidate id f = f := by
  funext J K
  unfold consolidate
  simp [Finset.filter_eq']

/-- 重みとパラメータの対。重み `w` は流れの大きさ(所得・資本など)。 -/
structure WP where
  w : ℝ
  p : ℝ

/-- 二つの対の連結: 重みは足し、パラメータは重み付きの平均を取る。 -/
noncomputable def comb (a b : WP) : WP :=
  ⟨a.w + b.w, (a.w * a.p + b.w * b.p) / (a.w + b.w)⟩

/-- T3a: 連結したパラメータは、流れ(重み × パラメータ)の和をちょうど再現する。 -/
theorem comb_flow (a b : WP) (h : a.w + b.w ≠ 0) :
    (comb a b).w * (comb a b).p = a.w * a.p + b.w * b.p := by
  simp only [comb]
  field_simp

/-- T3b: 連結は可換。 -/
theorem comb_comm (a b : WP) : comb a b = comb b a := by
  simp only [comb, WP.mk.injEq]
  constructor <;> ring

/-- T3c: 連結は結合的(重みが正のとき)。 -/
theorem comb_assoc (a b c : WP) (ha : 0 < a.w) (hb : 0 < b.w) (hc : 0 < c.w) :
    comb (comb a b) c = comb a (comb b c) := by
  have h1 : a.w + b.w ≠ 0 := by positivity
  have h2 : b.w + c.w ≠ 0 := by positivity
  have h3 : a.w + b.w + c.w ≠ 0 := by positivity
  have h4 : a.w + (b.w + c.w) ≠ 0 := by positivity
  simp only [comb, WP.mk.injEq]
  constructor
  · ring
  · field_simp
    ring

/-- T4: 閉じた二地域の乗数モデル Y_i = a_i + b_i Y_i(b_i < 1)を一つにまとめると、
まとめた乗数 1/(1 − b_A) は、各地域の乗数 1/(1 − b_i) を自律需要 a_i で重み付けた平均になる。
重み付きの平均なので、T3 により、まとめる順序によらない。 -/
theorem multiplier_aggregate (a1 a2 b1 b2 : ℝ) (h1 : b1 < 1) (h2 : b2 < 1) (ha : 0 < a1 + a2) :
    a1 / (1 - b1) + a2 / (1 - b2)
      = (a1 + a2) * ((a1 * (1 / (1 - b1)) + a2 * (1 / (1 - b2))) / (a1 + a2)) := by
  have : (1 - b1) ≠ 0 := by linarith
  have : (1 - b2) ≠ 0 := by linarith
  have : a1 + a2 ≠ 0 := ne_of_gt ha
  field_simp

/-- T5: 伸び率の違う二つの地域の合計は、一定の伸び率で伸びる一つの地域としては書けない。
離散時間で、地域の大きさが w₁ xⁿ と w₂ yⁿ(x ≠ y)なら、どんな c, z でも w₁ xⁿ + w₂ yⁿ = c zⁿ は
すべての n では成り立たない。だから、パラメータが一定の一国モデルで動学を厳密に縮約することはできない。 -/
theorem no_single_exponential (w1 w2 x y : ℝ) (hw1 : 0 < w1) (hw2 : 0 < w2) (hxy : x ≠ y) :
    ¬ ∃ c z : ℝ, ∀ n : ℕ, w1 * x ^ n + w2 * y ^ n = c * z ^ n := by
  rintro ⟨c, z, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [pow_zero, mul_one, pow_one] at h0 h1
  have e : (w1 * x + w2 * y) ^ 2 = (w1 + w2) * (w1 * x ^ 2 + w2 * y ^ 2) := by
    rw [h1, h0, h2]; ring
  have key : w1 * w2 * (x - y) ^ 2 = 0 := by linear_combination (-1 : ℝ) * e
  have : 0 < w1 * w2 * (x - y) ^ 2 := by
    have : x - y ≠ 0 := sub_ne_zero.mpr hxy
    positivity
  linarith

/-- T6: 折れ線の閾値の集計(イェンセン)。地域ごとの損失 max(0, x_i) を重み付きで足したものは、
平均の地域に当てはめた損失 max(0, Σ w_i x_i) 以上になる。 -/
theorem jensen_max {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    max 0 (∑ i ∈ s, w i * x i) ≤ ∑ i ∈ s, w i * max 0 (x i) := by
  apply max_le
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (le_max_left _ _))
  · exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (le_max_right _ _) (hw i hi))

/-- 等号が成り立たない例: 半々の重みで x = (1, −1) なら、平均の損失は 0 だが、損失の平均は 1/2。 -/
example : max (0 : ℝ) ((1 / 2) * 1 + (1 / 2) * (-1)) < (1 / 2) * max 0 1 + (1 / 2) * max 0 (-1) := by
  norm_num

/-- 重み付きの平均(集計)。 -/
noncomputable def agg {ι : Type*} (s : Finset ι) (w p : ι → ℝ) : ℝ :=
  (∑ i ∈ s, w i * p i) / ∑ i ∈ s, w i

/-- T7a: 射影してから集計すると元に戻る。集計した変化 Δ を、配分 α_i(Σ w_i α_i = Σ w_i を満たすもの)で
地域に割り振る(p_i ↦ p_i + Δ α_i)と、集計したパラメータはちょうど Δ だけ変わる。
「一様」(α_i = 1)、「一地域に集中」(α_j = Σw/w_j、他は 0)などは、どれもこの条件を満たす。 -/
theorem agg_proj {ι : Type*} (s : Finset ι) (w p α : ι → ℝ) (Δ : ℝ)
    (hW : ∑ i ∈ s, w i ≠ 0) (hα : ∑ i ∈ s, w i * α i = ∑ i ∈ s, w i) :
    agg s w (fun i => p i + Δ * α i) = agg s w p + Δ := by
  unfold agg
  have : ∑ i ∈ s, w i * (p i + Δ * α i) = ∑ i ∈ s, w i * p i + Δ * ∑ i ∈ s, w i * α i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [this, hα]
  field_simp

/-- T7b: 集計してから射影しても、一般には元に戻らない。二地域 p = (1, 0)、重み (1, 1) を集計すると 1/2。
それを一様に射影すると (1/2, 1/2) で、元の (1, 0) とは違う。 -/
example : (fun _ : Fin 2 => agg univ (fun _ => (1 : ℝ)) ![1, 0]) ≠ ![1, 0] := by
  intro h
  have := congrFun h 1
  simp [agg, Fin.sum_univ_two] at this

/-- T8: 閾値を「分布」として持つと、連結について閉じる。地域 A, B の閾値の分布(有限個の点 θ_k に重み)を
大きさ w_A, w_B で混ぜた分布で計算した損失は、各地域の損失の重み付き平均にちょうど等しい。
分布の混合は重み付きの平均なので、T3 により結合的である。 -/
theorem mixture_loss {K : Type*} (s : Finset K) (θ μA μB : K → ℝ) (Φ wA wB : ℝ) (h : wA + wB ≠ 0) :
    ∑ k ∈ s, ((wA * μA k + wB * μB k) / (wA + wB)) * max 0 (Φ - θ k)
      = (wA * ∑ k ∈ s, μA k * max 0 (Φ - θ k) + wB * ∑ k ∈ s, μB k * max 0 (Φ - θ k)) / (wA + wB) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  field_simp

end CreditV6
