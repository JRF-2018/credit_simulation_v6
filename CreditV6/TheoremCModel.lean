import Mathlib
import CreditV6.TheoremA
import CreditV6.Linearization

/-!
# 定理 C′: 実際のモデルの縮約誤差は、1 次の近似で構成比のずれだけで決まる

定理 C(`TheoremC.lean`)は、一国のモデルのずれを「地域の成長率のばらつき × 構成比の動き」で抑える。
その評価は線形の核の上の算術で、一国のモデルの伸び率を「縮約した時点の構成比で重み付けた平均」と読むところに、
線形性を使っている。定理 B に対する B′ と同じく、実際のモデルの式についての対応物がここで示す C′ である。

実際のモデルの **1 期の縮約誤差** を
`e(x) = 一国のモデルで 1 期進めたもの(step pA (aggState x)) − 世界で 1 期進めてまとめたもの(aggState (step p x))`
とする。`e` は、二つの 1 次同次な写像の差なので、それ自体 1 次同次である(`errV_hom`)。

* 定理 A の仮定「ある時点 `x₀` で一致する」(`e x₀ = 0`)があれば、`x₀` を何倍した点でも一致する
  (`model_error_zero_on_ray`)。釣り合い経路の上にあることは要らない。
* `e` が `x₀` で微分可能なら、その微分 `De` は規模の方向 `P₁x₀` で 0 になる(オイラーの恒等式、`deriv_scale`)。
* したがって、`x₀` の近くでは `‖e(x₀ + δ)‖ ≤ ‖De‖ · ‖δ − a P₁x₀‖ + ε ‖δ‖`(どんな `a` でも)。
  つまり 1 次の近似では、**誤差は規模の方向を除いた部分 = 構成比のずれだけで決まる**(`model_theoremC`)。

定理 C との対応は次のとおり。

| | 定理 C(線形の核) | 定理 C′(実際のモデル) |
|---|---|---|
| 1 期のずれの上限 | 成長率のばらつき `G` × 構成比の動き `Σ\|wᵢ − w⁰ᵢ\|` | `‖De‖` × 規模の方向を除いたずれ `‖δ − a P₁x₀‖`(+ 高次の項) |
| ずれが生じない場合 | 成長率がそろっている、または構成比が動かない | 規模の方向にしか動かない(釣り合い経路) |

`‖De‖` が `G` の役を果たす。IPYNB「信用の世界経済は一つか」の第 14.9 節では、Python のモデルで、地域のパラメータが同じなら構成比の方向の `De` が 0 に
なり(1 次の誤差がない)、パラメータのばらつきに比例して大きくなることを数値で確かめている。
微分可能であることは、定理 B′ と同じく仮定である。
モデルが微分できないのは、`max`・`min` の折れ目の上(貸倒れの始まり、投資の下限、株式的富が減り始める瞬間など)である。
どこで、いつそうなるか(危機のとき)は、IPYNB「信用の世界経済は一つか」の第 14.10 節で論じている。
-/

namespace CreditV6.ErrorModel

open CreditV6.Linearization

section abstract
variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **オイラーの恒等式**(二つの空間の間の写像): 1 次同次で `x₀` で微分可能なら、`J (P x₀) = P' (F x₀)`。 -/
theorem deriv_scale (F : E → E') (P : E →L[ℝ] E) (P' : E' →L[ℝ] E')
    (hom : ∀ c : ℝ, 0 < c → ∀ x, F (actP P c x) = actP P' c (F x))
    (J : E →L[ℝ] E') (x₀ : E) (hJ : HasFDerivAt F J x₀) :
    J (P x₀) = P' (F x₀) := by
  have hh : HasDerivAt (fun t : ℝ => x₀ + (t - 1) • P x₀) (P x₀) 1 := by
    have : HasDerivAt (fun t : ℝ => (t - 1) • P x₀) ((1 : ℝ) • P x₀) 1 :=
      ((hasDerivAt_id (1 : ℝ)).sub_const 1).smul_const (P x₀)
    simpa using this.const_add x₀
  have h1 : (fun t : ℝ => x₀ + (t - 1) • P x₀) 1 = x₀ := by simp
  have hJ' : HasFDerivAt F J ((fun t : ℝ => x₀ + (t - 1) • P x₀) 1) := by rw [h1]; exact hJ
  have hd1 : HasDerivAt (fun t : ℝ => F (x₀ + (t - 1) • P x₀)) (J (P x₀)) 1 :=
    hJ'.comp_hasDerivAt (1 : ℝ) hh
  have hd2 : HasDerivAt (fun t : ℝ => F x₀ + (t - 1) • P' (F x₀)) (P' (F x₀)) 1 := by
    have : HasDerivAt (fun t : ℝ => (t - 1) • P' (F x₀)) ((1 : ℝ) • P' (F x₀)) 1 :=
      ((hasDerivAt_id (1 : ℝ)).sub_const 1).smul_const (P' (F x₀))
    simpa using this.const_add (F x₀)
  have heq : (fun t : ℝ => F (x₀ + (t - 1) • P x₀)) =ᶠ[nhds (1 : ℝ)]
      (fun t : ℝ => F x₀ + (t - 1) • P' (F x₀)) := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hom t ht x₀
  exact (hd1.congr_of_eventuallyEq heq.symm).unique hd2

/-- 1 次同次な写像が `x₀` で 0 なら、`x₀` を何倍した点でも 0。 -/
theorem zero_on_ray (e : E → E') (P : E →L[ℝ] E) (P' : E' →L[ℝ] E')
    (hom : ∀ c : ℝ, 0 < c → ∀ x, e (actP P c x) = actP P' c (e x)) (x₀ : E) (h0 : e x₀ = 0)
    (c : ℝ) (hc : 0 < c) : e (actP P c x₀) = 0 := by
  rw [hom c hc, h0]; simp [actP]

/-- **定理 C′(抽象形)**: 1 次同次な誤差の写像 `e` が `x₀` で 0 で、微分可能なら、
規模の方向の微分は 0 で、`x₀` の近くでは誤差は規模の方向を除いたずれで抑えられる。 -/
theorem error_first_order (e : E → E') (P : E →L[ℝ] E) (P' : E' →L[ℝ] E')
    (hom : ∀ c : ℝ, 0 < c → ∀ x, e (actP P c x) = actP P' c (e x))
    (De : E →L[ℝ] E') (x₀ : E) (hD : HasFDerivAt e De x₀) (h0 : e x₀ = 0) :
    De (P x₀) = 0 ∧ ∀ ε > 0, ∃ r > 0, ∀ δ : E, ‖δ‖ < r → ∀ a : ℝ,
      ‖e (x₀ + δ)‖ ≤ ‖De‖ * ‖δ - a • P x₀‖ + ε * ‖δ‖ := by
  have hscale : De (P x₀) = 0 := by rw [deriv_scale e P P' hom De x₀ hD, h0, map_zero]
  refine ⟨hscale, fun ε hε => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hD.isLittleO.def hε)
  refine ⟨r, hr, fun δ hδ a => ?_⟩
  have hb := hball (y := x₀ + δ) (by simpa [dist_eq_norm] using hδ)
  simp only [add_sub_cancel_left, h0, sub_zero] at hb
  have hsplit : e (x₀ + δ) = (e (x₀ + δ) - De δ) + De (δ - a • P x₀) := by
    rw [map_sub, map_smul, hscale, smul_zero, sub_zero]; abel
  rw [hsplit]
  calc ‖(e (x₀ + δ) - De δ) + De (δ - a • P x₀)‖
      ≤ ‖e (x₀ + δ) - De δ‖ + ‖De (δ - a • P x₀)‖ := norm_add_le _ _
    _ ≤ ε * ‖δ‖ + ‖De‖ * ‖δ - a • P x₀‖ := add_le_add hb (De.le_opNorm _)
    _ = ‖De‖ * ‖δ - a • P x₀‖ + ε * ‖δ‖ := by ring

end abstract

section model
variable {N : ℕ}

/-- 実際のモデルの 1 期の縮約誤差(一国のモデル − 世界をまとめたもの)を、ベクトルの写像として見たもの。 -/
noncomputable def errV (p : Params N) (pA : Params 1) (v : SVec N) : SVec 1 :=
  enc (step pA (aggState (dec v))) - enc (aggState (step p (dec v)))

lemma actP_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : E →L[ℝ] E) (c : ℝ) (a b : E) :
    actP P c a - actP P c b = actP P c (a - b) := by
  simp only [actP, map_sub, smul_sub]; abel

/-- 縮約誤差も 1 次同次。 -/
theorem errV_hom (p : Params N) (pA : Params 1) (c : ℝ) (hc : 0 < c) (v : SVec N) :
    errV p pA (actP P1 c v) = actP P1 c (errV p pA v) := by
  have hw := step_hom p c hc (dec v)
  have h1 := step_hom pA c hc (aggState (dec v))
  simp only [Scaling.act] at hw h1
  unfold errV
  rw [dec_actP, agg_act hc, h1, hw, agg_act hc, enc_act, enc_act, actP_sub]

/-- 定理 A の仮定「`x₀` で一致する」があれば、`x₀` を何倍した点でも一致する(釣り合い経路の上でなくてよい)。 -/
theorem model_error_zero_on_ray (p : Params N) (pA : Params 1) (x₀ : State N)
    (hone : step pA (aggState x₀) = aggState (step p x₀)) (c : ℝ) (hc : 0 < c) :
    step pA (aggState (x₀.act c)) = aggState (step p (x₀.act c)) := by
  have hw := step_hom p c hc x₀
  have h1 := step_hom pA c hc (aggState x₀)
  simp only [Scaling.act] at hw h1
  rw [agg_act hc, h1, hone, hw, agg_act hc]

/-- **定理 C′(実際のモデル)**: 一国のモデルが `x₀` で世界の合計と一致し(`hone`)、縮約誤差が `x₀` で
微分可能なら、誤差の微分は規模の方向で 0 で、`x₀` の近くでは、誤差は規模の方向を除いたずれ
(構成比のずれ)で抑えられる。 -/
theorem model_theoremC (p : Params N) (pA : Params 1) (x₀ : State N)
    (hone : step pA (aggState x₀) = aggState (step p x₀))
    (De : SVec N →L[ℝ] SVec 1) (hD : HasFDerivAt (errV p pA) De (enc x₀)) :
    De (P1 (enc x₀)) = 0 ∧ ∀ ε > 0, ∃ r > 0, ∀ δ : SVec N, ‖δ‖ < r → ∀ a : ℝ,
      ‖errV p pA (enc x₀ + δ)‖ ≤ ‖De‖ * ‖δ - a • P1 (enc x₀)‖ + ε * ‖δ‖ := by
  have h0 : errV p pA (enc x₀) = 0 := by
    unfold errV; rw [show dec (enc x₀) = x₀ from rfl, hone, sub_self]
  exact error_first_order (errV p pA) P1 P1 (errV_hom p pA) De (enc x₀) hD h0

end model

end CreditV6.ErrorModel
