import Mathlib
import CreditV6.Model

/-!
# モデルの 1 期の写像は、規模について 1 次同次である

状態の 1 次の量(資本・債務・期待利潤など)をすべて c 倍(c > 0)すると、次の期の状態の 1 次の量もちょうど c 倍になり、
0 次の量(貸倒れ率・稼働率)は変わらない(`step_hom`)。

証明は、モデルの量を一つずつ「c 倍になる」か「変わらない」かを確かめていくだけである。
割り算は、どれも `(c·a)/(c·b) = a/b` の形になるので、状態が正である(分母が 0 でない)ことは仮定しなくてよい。
なめらかな min・max は、幅も規模に比例させているので同次になる(`softmin_smul`、`softplus_smul`)。
-/

open Finset BigOperators Real

set_option linter.unusedSectionVars false

namespace CreditV6

section basic
variable {c : ℝ} (hc : 0 < c)
include hc

lemma softmin_smul (a b w : ℝ) : softmin (c * a) (c * b) (c * w) = c * softmin a b w := by
  unfold softmin
  rw [show -(c * a) = c * (-a) by ring, show -(c * b) = c * (-b) by ring,
    mul_div_mul_left _ _ hc.ne', mul_div_mul_left _ _ hc.ne']
  ring

lemma softplus_smul (a w : ℝ) : softplus (c * a) (c * w) = c * softplus a w := by
  unfold softplus
  rw [mul_div_mul_left _ _ hc.ne']
  ring

lemma max0_smul (a : ℝ) : max 0 (c * a) = c * max 0 a := by
  rw [mul_max_of_nonneg _ _ hc.le, mul_zero]

lemma min_smul (a b : ℝ) : min (c * a) (c * b) = c * min a b := by
  rw [mul_min_of_nonneg _ _ hc.le]

lemma ratio_smul (a b : ℝ) : c * a / (c * b) = a / b := mul_div_mul_left _ _ hc.ne'

end basic

section act
variable {N : ℕ} (x : State N) (c : ℝ)
@[simp] lemma act_K : (x.act c).K = c • x.K := rfl
@[simp] lemma act_L : (x.act c).L = c • x.L := rfl
@[simp] lemma act_B : (x.act c).B = c • x.B := rfl
@[simp] lemma act_S : (x.act c).S = c • x.S := rfl
@[simp] lemma act_Pi_e : (x.act c).Pi_e = c • x.Pi_e := rfl
@[simp] lemma act_Pi_prev : (x.act c).Pi_prev = c • x.Pi_prev := rfl
@[simp] lemma act_E_prev : (x.act c).E_prev = c • x.E_prev := rfl
@[simp] lemma act_Y_prev : (x.act c).Y_prev = c • x.Y_prev := rfl
@[simp] lemma act_loss : (x.act c).loss = x.loss := rfl
@[simp] lemma act_u_prev : (x.act c).u_prev = x.u_prev := rfl

end act

section quantities
variable {N : ℕ} (p : Params N) (x : State N) {c : ℝ} (hc : 0 < c)
include hc

lemma Yk_act : Yk p (x.act c) = c • Yk p x := by
  funext i; simp [Yk, mul_div_assoc]

lemma Yp_act : Yp p (x.act c) = c • Yp p x := by
  funext i; simp [Yp, Yk_act p x hc]; ring

lemma rL_act : rL p (x.act c) = rL p x := by
  funext i; simp [rL]

lemma Eq_act : Eq p (x.act c) = c • Eq p x := by
  funext i
  simp only [Eq, act_Pi_e, act_K, Pi.smul_apply, smul_eq_mul, rL_act p x hc]
  rw [show (0.001 : ℝ) * (c * x.K i) = c * (0.001 * x.K i) by ring, softplus_smul hc, mul_div_assoc]

lemma delta_act : delta p (x.act c) = delta p x := by
  funext i
  simp only [delta, Eq_act p x hc, act_E_prev, Pi.smul_apply, smul_eq_mul]
  rw [show -(c * Eq p x i - c * x.E_prev i) = c * (-(Eq p x i - x.E_prev i)) by ring, ratio_smul hc]

lemma gnet_act : gnet p (x.act c) = gnet p x := by
  funext i
  simp only [gnet, Eq_act p x hc, act_K, act_Pi_prev, act_u_prev, Pi.smul_apply, smul_eq_mul]
  field_simp

lemma Ides_act : Ides p (x.act c) = c • Ides p x := by
  funext i
  simp only [Ides, gnet_act p x hc, act_K, Pi.smul_apply, smul_eq_mul]
  ring

lemma retained_act : retained p (x.act c) = c • retained p x := by
  funext i
  simp only [retained, act_K, act_Pi_prev, Pi.smul_apply, smul_eq_mul]
  ring

lemma dLraw_act : dLraw p (x.act c) = c • dLraw p x := by
  funext i
  simp only [dLraw, Ides_act p x hc, retained_act p x hc, Eq_act p x hc, act_K, act_L, Pi.smul_apply,
    smul_eq_mul]
  rw [show c * Ides p x i - c * retained p x i = c * (Ides p x i - retained p x i) by ring,
    show (p.lam i * (c * Eq p x i + c * x.K i) - c * x.L i) / p.T_adj i
      = c * ((p.lam i * (Eq p x i + x.K i) - x.L i) / p.T_adj i) by ring,
    show (0.01 : ℝ) * (c * x.K i) = c * (0.01 * x.K i) by ring, softmin_smul hc]

lemma Inv_act : Inv p (x.act c) = c • Inv p x := by
  funext i
  simp only [Inv, dLraw_act p x hc, retained_act p x hc, Pi.smul_apply, smul_eq_mul]
  rw [← mul_add, max0_smul hc]

lemma dL_act : dL p (x.act c) = c • dL p x := by
  funext i
  simp only [dL, Inv_act p x hc, retained_act p x hc, Pi.smul_apply, smul_eq_mul]
  ring

lemma Gov_act : Gov p (x.act c) = c • Gov p x := by
  funext i
  simp only [Gov, Yp_act p x hc, Pi.smul_apply, smul_eq_mul]
  ring

lemma tauE_act : tauE p (x.act c) = tauE p x := by
  funext i
  simp only [tauE, act_B, act_Y_prev, Pi.smul_apply, smul_eq_mul]
  rw [ratio_smul hc]

lemma ct_act : ct p (x.act c) = ct p x := by
  funext i; simp only [ct, tauE_act p x hc]

/-- 各項が c 倍なら、和も c 倍。 -/
lemma sum_smul_of {f g : Fin N → ℝ} (h : ∀ j, f j = c * g j) : ∑ j, f j = c * ∑ j, g j := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => h j)

lemma flow0_act : flow0 p (x.act c) = c • flow0 p x := by
  funext j
  simp only [flow0, rL_act p x hc, act_L, act_B, act_K, Pi.smul_apply, smul_eq_mul]
  ring

lemma wealth_act : wealth p (x.act c) = c • wealth p x := by
  funext i
  simp only [wealth, act_L, act_B, act_S, Pi.smul_apply, smul_eq_mul]
  rw [sum_smul_of (hc := hc) (g := fun j => p.hold j i * (x.L j + x.B j)) (fun j => by ring)]
  ring

lemma avec_act : avec p (x.act c) = c • avec p x := by
  funext i
  simp only [avec, ct_act p x hc, flow0_act p x hc, wealth_act p x hc, Inv_act p x hc, Gov_act p x hc,
    act_S, Pi.smul_apply, smul_eq_mul]
  rw [sum_smul_of (hc := hc) (g := fun j => p.hold j i * flow0 p x j) (fun j => by ring)]
  ring

lemma Dvec_act (Y : Vec N) : Dvec p (x.act c) (c • Y) = c • Dvec p x Y := by
  funext i
  simp only [Dvec, ct_act p x hc, avec_act p x hc, Pi.smul_apply, smul_eq_mul]
  rw [sum_smul_of (hc := hc) (g := fun j => p.hold j i * (p.payout j * (1 - p.omega j) * Y j))
    (fun j => by ring)]
  ring

lemma demand_act (Y : Vec N) : demand p (x.act c) (c • Y) = c • demand p x Y := by
  funext i
  simp only [demand, Dvec_act p x hc, Pi.smul_apply, smul_eq_mul]
  exact sum_smul_of (hc := hc) (fun j => by ring)

/-- 所得の方程式は同次: `c • Y` が規模 c 倍の状態の解であることと、`Y` が元の状態の解であることは同値。 -/
lemma eqY_act (Y : Vec N) : eqY p (x.act c) (c • Y) ↔ eqY p x Y := by
  simp only [eqY, demand_act p x hc, Yp_act p x hc, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h i
    have := h i
    rw [show (0.01 : ℝ) * (c * Yp p x i) = c * (0.01 * Yp p x i) by ring, softmin_smul hc] at this
    exact mul_left_cancel₀ hc.ne' this
  · intro h i
    rw [show (0.01 : ℝ) * (c * Yp p x i) = c * (0.01 * Yp p x i) by ring, softmin_smul hc, ← h i]

/-- 所得(方程式のただ一つの解)も同次。 -/
lemma Ysol_act : Ysol p (x.act c) = c • Ysol p x := by
  have hinv : ∀ Y, eqY p (x.act c) Y ↔ eqY p x (c⁻¹ • Y) := by
    intro Y
    rw [← eqY_act p x hc (c⁻¹ • Y), smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hu : (∃! Y, eqY p (x.act c) Y) ↔ (∃! Y, eqY p x Y) := by
    constructor
    · rintro ⟨Y, hY, huniq⟩
      refine ⟨c⁻¹ • Y, (hinv Y).1 hY, fun Z hZ => ?_⟩
      have : c • Z = Y := huniq _ ((eqY_act p x hc Z).2 hZ)
      rw [← this, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    · rintro ⟨Y, hY, huniq⟩
      refine ⟨c • Y, (eqY_act p x hc Y).2 hY, fun Z hZ => ?_⟩
      have : c⁻¹ • Z = Y := huniq _ ((hinv Z).1 hZ)
      rw [← this, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  unfold Ysol
  by_cases h : ∃! Y, eqY p x Y
  · have h' : ∃! Y, eqY p (x.act c) Y := hu.2 h
    simp only [h', h, ↓reduceDIte]
    apply h'.unique h'.exists.choose_spec
    exact (eqY_act p x hc _).2 h.exists.choose_spec
  · have h' : ¬ ∃! Y, eqY p (x.act c) Y := fun h'' => h (hu.1 h'')
    simp only [h', h, ↓reduceDIte, smul_zero]

lemma Yv_act : Yv p (x.act c) = c • Yv p x := Ysol_act p x hc

lemma Pi_act : Pi p (x.act c) = c • Pi p x := by
  funext i
  simp only [CreditV6.Pi, Yv_act p x hc, rL_act p x hc, act_K, act_L, Pi.smul_apply, smul_eq_mul]
  ring

lemma pay_act : pay p (x.act c) = c • pay p x := by
  funext j
  simp only [pay, Pi_act p x hc, rL_act p x hc, act_L, act_B, Pi.smul_apply, smul_eq_mul]
  ring

lemma rentIn_act : rentIn p (x.act c) = c • rentIn p x := by
  funext i
  simp only [rentIn, pay_act p x hc, act_S, Pi.smul_apply, smul_eq_mul]
  rw [sum_smul_of (hc := hc) (g := fun j => p.hold j i * pay p x j) (fun j => by ring)]
  ring

lemma Wage_act : Wage p (x.act c) = c • Wage p x := by
  funext i; simp only [Wage, Yv_act p x hc, Pi.smul_apply, smul_eq_mul]; ring

lemma consDes_act : consDes p (x.act c) = c • consDes p x := by
  funext i
  simp only [consDes, ct_act p x hc, Wage_act p x hc, rentIn_act p x hc, wealth_act p x hc,
    Pi.smul_apply, smul_eq_mul]
  ring

lemma Ddes_act : Ddes p (x.act c) = c • Ddes p x := by
  funext i
  simp only [Ddes, consDes_act p x hc, Inv_act p x hc, Gov_act p x hc, Pi.smul_apply, smul_eq_mul]
  ring

lemma rhoS_act : rhoS p (x.act c) = rhoS p x := by
  funext i
  simp only [rhoS, Yv_act p x hc, demand_act p x hc, Pi.smul_apply, smul_eq_mul]
  rw [ratio_smul hc]

lemma purch_act (i j : Fin N) : purch p (x.act c) i j = c * purch p x i j := by
  simp only [purch, Ddes_act p x hc, rhoS_act p x hc, Pi.smul_apply, smul_eq_mul]
  ring

lemma Dreal_act : Dreal p (x.act c) = c • Dreal p x := by
  funext j
  simp only [Dreal, purch_act p x hc, Pi.smul_apply, smul_eq_mul]
  exact sum_smul_of (hc := hc) (fun i => rfl)

lemma Imp_act : Imp p (x.act c) = c • Imp p x := by
  funext j
  simp only [Imp, Dreal_act p x hc, purch_act p x hc, Pi.smul_apply, smul_eq_mul]
  ring

lemma Exp_act : Exp p (x.act c) = c • Exp p x := by
  funext i
  simp only [Exp, purch_act p x hc, Pi.smul_apply, smul_eq_mul]
  rw [sum_smul_of (hc := hc) (g := fun j => purch p x i j) (fun j => rfl)]
  ring

lemma tax_act : tax p (x.act c) = c • tax p x := by
  funext i
  simp only [tax, tauE_act p x hc, Wage_act p x hc, rentIn_act p x hc, Pi.smul_apply, smul_eq_mul]
  ring

lemma CA_act : CA p (x.act c) = c • CA p x := by
  funext i
  simp only [CA, Exp_act p x hc, Imp_act p x hc, rentIn_act p x hc, pay_act p x hc,
    Pi.smul_apply, smul_eq_mul]
  ring

lemma CF_act : CF p (x.act c) = c • CF p x := by
  funext i
  simp only [CF, Yv_act p x hc, rL_act p x hc, act_L, Pi.smul_apply, smul_eq_mul]
  ring

lemma default_act : default p (x.act c) = c • default p x := by
  funext i
  simp only [default, CF_act p x hc, act_L, Pi.smul_apply, smul_eq_mul]
  rw [show -(c * CF p x i) = c * (-CF p x i) by ring, max0_smul hc,
    show p.default_share i * (c * max 0 (-CF p x i)) = c * (p.default_share i * max 0 (-CF p x i)) by ring,
    show (0.5 : ℝ) * (c * x.L i) = c * (0.5 * x.L i) by ring, min_smul hc]

lemma dB_act : dB p (x.act c) = c • dB p x := by
  funext i
  simp only [dB, Gov_act p x hc, tax_act p x hc, act_B, Pi.smul_apply, smul_eq_mul]
  ring

lemma newIss_act : newIss p (x.act c) = c • newIss p x := by
  funext i
  simp only [newIss, dL_act p x hc, dB_act p x hc, Pi.smul_apply, smul_eq_mul]
  ring

lemma portOut_act : portOut p (x.act c) = c • portOut p x := by
  funext i
  simp only [portOut, newIss_act p x hc, Pi.smul_apply, smul_eq_mul]
  rw [sum_smul_of (hc := hc) (g := fun j => p.hold j i * newIss p x j) (fun j => by ring)]
  ring

lemma dS_act : dS p (x.act c) = c • dS p x := by
  funext i
  simp only [dS, CA_act p x hc, portOut_act p x hc, Pi.smul_apply, smul_eq_mul]
  ring

end quantities

/-- **モデルの 1 期の写像は、規模について 1 次同次である。** -/
theorem step_hom {N : ℕ} (p : Params N) : HomS (step p) := by
  intro c hc x
  change step p (x.act c) = (step p x).act c
  ext i
  · simp only [step, Inv_act p x hc, delta_act p x hc, act_K, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [step, dL_act p x hc, default_act p x hc, act_L, Pi.smul_apply, smul_eq_mul]
    rw [show c * x.L i + (c * dL p x i - c * default p x i) * p.dt
      = c * (x.L i + (dL p x i - default p x i) * p.dt) by ring, max0_smul hc]
  · simp only [step, dB_act p x hc, act_B, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [step, dS_act p x hc, act_S, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [step, Pi_act p x hc, act_Pi_e, Pi.smul_apply, smul_eq_mul]; ring
  · simp only [step, Pi_act p x hc, act_Pi_prev, Pi.smul_apply, smul_eq_mul]
  · simp only [step, Eq_act p x hc, act_E_prev, Pi.smul_apply, smul_eq_mul]
  · simp only [step, Yv_act p x hc, act_Y_prev, Pi.smul_apply, smul_eq_mul]
  · simp only [step, default_act p x hc, act_L, act_loss, Pi.smul_apply, smul_eq_mul]
    rw [ratio_smul hc]
  · simp only [step, Yv_act p x hc, Yk_act p x hc, act_u_prev, Pi.smul_apply, smul_eq_mul]
    rw [ratio_smul hc]

end CreditV6
