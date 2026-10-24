import Mathlib
import CreditV6.Homogeneity

/-!
# 定理 B′: 実際のモデルの線形化(ヤコビアン)と、定理 B の線形の核のつながり

定理 B は 2×2 の線形の核についての定理である。実際のモデルとのつながりは、**釣り合い経路の上での線形化**
(1 期の写像の微分、ヤコビアン)を通して付く。ここでは、その出発点になる事実を示す。

**オイラーの恒等式**: 規模について 1 次同次な写像 `F` が点 `x₀` で微分可能なら、その微分 `J` は
「規模の方向」`P x₀`(1 次の量だけを残したもの)を `P (F x₀)` に写す。
とくに `x₀` が釣り合い経路の上(`F x₀ = γ·x₀`)にあれば、`J (P x₀) = γ • P x₀`。
つまり、**成長率 γ はヤコビアンの固有値で、規模の方向がその固有ベクトル**である。
定理 B の `λ₁` はこの γ にあたり、構成比のずれの減衰率は、残りの固有値と γ の比 `|λ₂|/γ` で決まる。
この対応を Lean の定理として書いたのが `TheoremBModel.lean` の `model_theoremB` である。

* 抽象的な形(`jacobian_on_ray`): 規模の作用を `x ↦ x + (c − 1) • P x`(`P` は 1 次の量への射影)と書く。
* 実際のモデル(`step_jacobian_on_ray`): `Model.lean` の `step` を、10 個の量を並べたベクトル空間の写像として見て、
  `step_hom`(同次性)から上を当てはめる。

微分可能であることは仮定に置いた。モデルはなめらかな min・max(`softmin`・`softplus`)で書いてあるので、
`max(0, ·)` などの折れ目から離れた点では微分可能だが、所得 `Ysol` の微分可能性を示すには陰関数定理が要るので、
ここでは示していない。数値では、IPYNB「信用の世界経済は一つか」の第 14.8 節で、Python のモデルのヤコビアンを数値微分で求め、
この恒等式が 10⁻¹⁰ の精度で成り立つこと、構成比の固有値がシミュレーションの減衰率と合うことを確かめている。
モデルが微分できないのは、`max`・`min` の折れ目の上(貸倒れの始まり、投資の下限、株式的富が減り始める瞬間など)である。
どこで、いつそうなるか(危機のとき)は、IPYNB「信用の世界経済は一つか」の第 14.10 節で論じている。
-/

namespace CreditV6.Linearization

section abstract
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- 規模の作用 `c` 倍: 1 次の部分 `P x` だけを `c` 倍する。 -/
def actP (P : E →L[ℝ] E) (c : ℝ) (x : E) : E := x + (c - 1) • P x

/-- **オイラーの恒等式**: 1 次同次で `x₀` で微分可能なら、`J (P x₀) = P (F x₀)`。 -/
theorem jacobian_scale (F : E → E) (P : E →L[ℝ] E)
    (hom : ∀ c : ℝ, 0 < c → ∀ x, F (actP P c x) = actP P c (F x))
    (J : E →L[ℝ] E) (x₀ : E) (hJ : HasFDerivAt F J x₀) :
    J (P x₀) = P (F x₀) := by
  -- 道 h(t) = x₀ + (t − 1)•P x₀ に沿って F を微分する
  have hh : HasDerivAt (fun t : ℝ => x₀ + (t - 1) • P x₀) (P x₀) 1 := by
    have : HasDerivAt (fun t : ℝ => (t - 1) • P x₀) ((1 : ℝ) • P x₀) 1 :=
      ((hasDerivAt_id (1 : ℝ)).sub_const 1).smul_const (P x₀)
    simpa using this.const_add x₀
  have h1 : (fun t : ℝ => x₀ + (t - 1) • P x₀) 1 = x₀ := by simp
  have hJ' : HasFDerivAt F J ((fun t : ℝ => x₀ + (t - 1) • P x₀) 1) := by rw [h1]; exact hJ
  have hd1 : HasDerivAt (fun t : ℝ => F (x₀ + (t - 1) • P x₀)) (J (P x₀)) 1 :=
    hJ'.comp_hasDerivAt (1 : ℝ) hh
  -- 同次性から、t > 0 の近くでは F(h(t)) = F x₀ + (t − 1)•P(F x₀)
  have hd2 : HasDerivAt (fun t : ℝ => F x₀ + (t - 1) • P (F x₀)) (P (F x₀)) 1 := by
    have : HasDerivAt (fun t : ℝ => (t - 1) • P (F x₀)) ((1 : ℝ) • P (F x₀)) 1 :=
      ((hasDerivAt_id (1 : ℝ)).sub_const 1).smul_const (P (F x₀))
    simpa using this.const_add (F x₀)
  have heq : (fun t : ℝ => F (x₀ + (t - 1) • P x₀)) =ᶠ[nhds (1 : ℝ)]
      (fun t : ℝ => F x₀ + (t - 1) • P (F x₀)) := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hom t ht x₀
  exact (hd1.congr_of_eventuallyEq heq.symm).unique hd2

/-- **定理 B′(抽象形)**: 釣り合い経路の上 `F x₀ = γ·x₀` では、ヤコビアンは規模の方向を γ 倍する。
`P` は射影(`P (P x) = P x`)とする。 -/
theorem jacobian_on_ray (F : E → E) (P : E →L[ℝ] E) (hP : ∀ x, P (P x) = P x)
    (hom : ∀ c : ℝ, 0 < c → ∀ x, F (actP P c x) = actP P c (F x))
    (J : E →L[ℝ] E) (x₀ : E) (hJ : HasFDerivAt F J x₀) (γ : ℝ) (hray : F x₀ = actP P γ x₀) :
    J (P x₀) = γ • P x₀ := by
  rw [jacobian_scale F P hom J x₀ hJ, hray, actP, map_add, map_smul, hP]
  module

end abstract

section model
variable {N : ℕ}

/-- 状態の 10 個の量を並べたベクトル(0〜7 番が 1 次の量、8・9 番が 0 次の量)。 -/
abbrev SVec (N : ℕ) := Fin 10 → Fin N → ℝ

/-- 状態をベクトルにする。 -/
def enc (x : State N) : SVec N :=
  ![x.K, x.L, x.B, x.S, x.Pi_e, x.Pi_prev, x.E_prev, x.Y_prev, x.loss, x.u_prev]

/-- ベクトルを状態に戻す。 -/
def dec (v : SVec N) : State N :=
  ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9⟩

/-- 1 次の量への射影(8・9 番の 0 次の量を 0 にする)。 -/
def P1 : SVec N →L[ℝ] SVec N :=
  ContinuousLinearMap.pi fun i : Fin 10 =>
    if i.val < 8 then ContinuousLinearMap.proj i else 0

lemma P1_apply (v : SVec N) (i : Fin 10) : P1 v i = if i.val < 8 then v i else 0 := by
  unfold P1; split_ifs <;> simp [*]

lemma P1_idem (v : SVec N) : P1 (P1 v) = P1 v := by
  funext i; simp only [P1_apply]; split_ifs <;> rfl

lemma dec_actP (v : SVec N) (c : ℝ) : dec (actP P1 c v) = (dec v).act c := by
  simp only [dec, actP, State.act]
  congr 1 <;> funext j <;> simp [P1_apply] <;> ring

lemma enc_act (x : State N) (c : ℝ) : enc (x.act c) = actP P1 c (enc x) := by
  funext i j
  fin_cases i <;> simp [enc, actP, P1_apply, State.act] <;> ring

lemma enc_dec (v : SVec N) : enc (dec v) = v := by
  funext i; fin_cases i <;> rfl

/-- 実際のモデルの 1 期の写像を、ベクトル空間の写像として見たもの。 -/
noncomputable def stepV (p : Params N) (v : SVec N) : SVec N := enc (step p (dec v))

/-- `step_hom` から、ベクトルの写像も 1 次同次。 -/
theorem stepV_hom (p : Params N) (c : ℝ) (hc : 0 < c) (v : SVec N) :
    stepV p (actP P1 c v) = actP P1 c (stepV p v) := by
  unfold stepV
  rw [dec_actP]
  have := step_hom p c hc (dec v)
  simp only [Scaling.act] at this
  rw [this, enc_act]

/-- **定理 B′(実際のモデル)**: モデルの 1 期の写像が釣り合い経路の上の点 `x₀`
(`step p x₀ = x₀.act γ`)で微分可能なら、そのヤコビアンは規模の方向(1 次の量)を γ 倍する。
つまり γ はヤコビアンの固有値で、定理 B の `λ₁` にあたる。 -/
theorem step_jacobian_on_ray (p : Params N) (x₀ : State N) (γ : ℝ)
    (hray : step p x₀ = x₀.act γ) (J : SVec N →L[ℝ] SVec N) (hJ : HasFDerivAt (stepV p) J (enc x₀)) :
    J (P1 (enc x₀)) = γ • P1 (enc x₀) := by
  refine jacobian_on_ray (stepV p) P1 P1_idem (stepV_hom p) J (enc x₀) hJ γ ?_
  rw [stepV, show dec (enc x₀) = x₀ from rfl, hray, enc_act]

end model

end CreditV6.Linearization
