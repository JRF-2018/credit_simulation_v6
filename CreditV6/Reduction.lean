import Mathlib

/-!
# 定理 A の骨格: 釣り合い経路の上での縮約

世界の 1 期の写像 `F : X → X`(全地域の状態)と、一国モデルの 1 期の写像 `G : A → A`、
世界の状態を一国の状態にまとめる線形写像 `S : X →ₗ[ℝ] A`(地域の合計)を考える。

* `F` と `G` は、規模について 1 次同次である(状態を c 倍すると、次の期の状態も c 倍になる)。
* 世界は釣り合いの取れた成長経路の上にある: `F x₀ = γ • x₀`(全部の量が γ 倍になり、構成比は変わらない)。
* 一国モデルは、その時点の流れを重みにして作られているので、その時点では厳密に一致する: `G (S x₀) = S (F x₀)`。

このとき、一国モデルは世界の合計を、その後のすべての期について厳密に再現する(`exact_reduction_on_ray`)。
その時点での一致が誤差 ε を含むときは、`G` がリプシッツ連続なら、n 期後のずれは
`ε · Σ_{k<n} L^k γ^{n-1-k}` 以下に抑えられる(`approx_reduction_on_ray`)。
-/

namespace CreditV6

/-- 規模について 1 次同次(正の倍率について)。 -/
def Hom1 {V : Type*} [AddCommGroup V] [Module ℝ V] (F : V → V) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ v, F (c • v) = c • F v

/-- 1 次同次な写像で、`x₀` が倍率 γ の釣り合い経路の上にあれば、n 期後は γⁿ 倍になる。 -/
lemma iterate_on_ray {V : Type*} [AddCommGroup V] [Module ℝ V] (F : V → V) (hF : Hom1 F)
    (x₀ : V) (γ : ℝ) (hγ : 0 < γ) (hray : F x₀ = γ • x₀) :
    ∀ n : ℕ, F^[n] x₀ = γ ^ n • x₀ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hF _ (pow_pos hγ n), hray, smul_smul, pow_succ]

/-- **定理 A(骨格)**: 釣り合い経路の上では、その時点で一致する一国モデルは、ずっと厳密に一致する。 -/
theorem exact_reduction_on_ray {X A : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup A] [Module ℝ A]
    (F : X → X) (G : A → A) (S : X →ₗ[ℝ] A) (hF : Hom1 F) (hG : Hom1 G)
    (x₀ : X) (γ : ℝ) (hγ : 0 < γ) (hray : F x₀ = γ • x₀) (hone : G (S x₀) = S (F x₀)) :
    ∀ n : ℕ, G^[n] (S x₀) = S (F^[n] x₀) := by
  have hrayA : G (S x₀) = γ • S x₀ := by rw [hone, hray, map_smul]
  intro n
  rw [iterate_on_ray G hG (S x₀) γ hγ hrayA n, iterate_on_ray F hF x₀ γ hγ hray n, map_smul]

/-- 和の付け替え: `L · Σ_{k<n} L^k γ^{n-1-k} + γ^n = Σ_{k<n+1} L^k γ^{n-k}`。 -/
lemma sum_shift (L γ : ℝ) (n : ℕ) :
    L * ∑ k ∈ Finset.range n, L ^ k * γ ^ (n - 1 - k) + γ ^ n
      = ∑ k ∈ Finset.range (n + 1), L ^ k * γ ^ (n + 1 - 1 - k) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, one_mul, Nat.add_sub_cancel, Nat.sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n := Finset.mem_range.mp hk
  have e : n - (k + 1) = n - 1 - k := by omega
  rw [e, pow_succ]
  ring

/-- **定理 A(誤差つき)**: その時点での一致に誤差 `ε · ‖S x₀‖` があり、`G` がリプシッツ定数 `L` を持つなら、
n 期後のずれは `ε · ‖S x₀‖ · Σ_{k<n} L^k γ^{n-1-k}` 以下である。 -/
theorem approx_reduction_on_ray {X A : Type*} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (F : X → X) (G : A → A) (S : X →ₗ[ℝ] A) (hF : Hom1 F) (hG : Hom1 G)
    (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ a b, ‖G a - G b‖ ≤ L * ‖a - b‖)
    (x₀ : X) (γ : ℝ) (hγ : 0 < γ) (hray : F x₀ = γ • x₀)
    (ε : ℝ) (hone : ‖G (S x₀) - S (F x₀)‖ ≤ ε * ‖S x₀‖) :
    ∀ n : ℕ, ‖G^[n] (S x₀) - S (F^[n] x₀)‖
      ≤ ε * ‖S x₀‖ * ∑ k ∈ Finset.range n, L ^ k * γ ^ (n - 1 - k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : F^[n + 1] x₀ = γ ^ (n + 1) • x₀ := iterate_on_ray F hF x₀ γ hγ hray (n + 1)
    have hxn' : F^[n] x₀ = γ ^ n • x₀ := iterate_on_ray F hF x₀ γ hγ hray n
    -- G (γⁿ S x₀) = γⁿ G (S x₀)
    have hGn : G (γ ^ n • S x₀) = γ ^ n • G (S x₀) := hG _ (pow_pos hγ n) _
    have h1 : G (S (F^[n] x₀)) = γ ^ n • G (S x₀) := by rw [hxn', map_smul, hGn]
    have h2 : S (F^[n + 1] x₀) = γ ^ n • S (F x₀) := by
      rw [hxn, hray, map_smul, map_smul, smul_smul, pow_succ]
    have key : G^[n + 1] (S x₀) - S (F^[n + 1] x₀)
        = (G (G^[n] (S x₀)) - G (S (F^[n] x₀))) + γ ^ n • (G (S x₀) - S (F x₀)) := by
      rw [Function.iterate_succ_apply', h1, h2, smul_sub]
      abel
    rw [key]
    calc ‖(G (G^[n] (S x₀)) - G (S (F^[n] x₀))) + γ ^ n • (G (S x₀) - S (F x₀))‖
        ≤ ‖G (G^[n] (S x₀)) - G (S (F^[n] x₀))‖ + ‖γ ^ n • (G (S x₀) - S (F x₀))‖ := norm_add_le _ _
      _ ≤ L * ‖G^[n] (S x₀) - S (F^[n] x₀)‖ + γ ^ n * (ε * ‖S x₀‖) := by
          gcongr
          · exact hLip _ _
          · rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hγ.le n)]
            exact mul_le_mul_of_nonneg_left hone (pow_nonneg hγ.le n)
      _ ≤ L * (ε * ‖S x₀‖ * ∑ k ∈ Finset.range n, L ^ k * γ ^ (n - 1 - k)) + γ ^ n * (ε * ‖S x₀‖) := by
          gcongr
      _ = ε * ‖S x₀‖ * (L * ∑ k ∈ Finset.range n, L ^ k * γ ^ (n - 1 - k) + γ ^ n) := by ring
      _ = ε * ‖S x₀‖ * ∑ k ∈ Finset.range (n + 1), L ^ k * γ ^ (n + 1 - 1 - k) := by
          rw [sum_shift]


/-! ## 一般の「規模の作用」での定理 A

モデルの状態には、規模とともに伸びる量(資本・債務など、1 次の量)と、規模によらない量(貸倒れ率・稼働率など、
0 次の量)が混ざっている。そこで、状態への「規模の作用」`act c` を一般に考える(1 次の量だけを c 倍する)。
まとめる写像 `S` は、作用と可換であればよい(1 次の量は合計し、0 次の量は 1 次の量で重み付けて平均する、など)。
-/

/-- 規模の作用: `act c` は状態を c 倍の規模にする。 -/
class Scaling (V : Type*) where
  act : ℝ → V → V
  act_mul : ∀ a b v, act a (act b v) = act (a * b) v
  act_one : ∀ v, act 1 v = v

/-- 作用について 1 次同次な写像。 -/
def HomS {V : Type*} [Scaling V] (F : V → V) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ v, F (Scaling.act c v) = Scaling.act c (F v)

lemma iterate_on_ray_S {V : Type*} [Scaling V] (F : V → V) (hF : HomS F)
    (x₀ : V) (γ : ℝ) (hγ : 0 < γ) (hray : F x₀ = Scaling.act γ x₀) :
    ∀ n : ℕ, F^[n] x₀ = Scaling.act (γ ^ n) x₀ := by
  intro n
  induction n with
  | zero => simp [Scaling.act_one]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, hF _ (pow_pos hγ n), hray, Scaling.act_mul, pow_succ]

/-- **定理 A(作用の形)**: 世界の写像 `F` と一国モデルの写像 `G` が作用について 1 次同次で、
まとめる写像 `S` が作用と可換なら、釣り合い経路の上で一度一致すれば、ずっと一致する。 -/
theorem exact_reduction_on_ray_S {X A : Type*} [Scaling X] [Scaling A]
    (F : X → X) (G : A → A) (S : X → A) (hF : HomS F) (hG : HomS G)
    (hS : ∀ c : ℝ, 0 < c → ∀ x, S (Scaling.act c x) = Scaling.act c (S x))
    (x₀ : X) (γ : ℝ) (hγ : 0 < γ) (hray : F x₀ = Scaling.act γ x₀) (hone : G (S x₀) = S (F x₀)) :
    ∀ n : ℕ, G^[n] (S x₀) = S (F^[n] x₀) := by
  have hrayA : G (S x₀) = Scaling.act γ (S x₀) := by rw [hone, hray, hS _ hγ]
  intro n
  rw [iterate_on_ray_S G hG (S x₀) γ hγ hrayA n, iterate_on_ray_S F hF x₀ γ hγ hray n,
    hS _ (pow_pos hγ n)]

end CreditV6
