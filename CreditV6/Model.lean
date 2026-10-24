import Mathlib
import CreditV6.Reduction

/-!
# 多地域の信用循環モデルの 1 期の写像

`python/world.py` の `simulate_world` の 1 期の計算を、そのまま Lean に書き写したもの。
対象は、続編のノート(credit_linkage.ipynb)の第 3〜9 節で使った範囲である:

* 通貨は共通(`fx` なし)、財政統合なし、労働の天井なし、競争力による貿易配分なし、パラメータのショックなし。
* 財政ルール(`fiscal`)は含む。
* Python 版でゼロ除算を避けるために置いている下限(資本 ≥ 10⁻³、所得 ≥ 10⁻⁹、借入残高 ≥ 10⁻⁶ での割り算)は
  省く。状態が正の範囲にあるとき、両者は一致する。

所得 `Y` は、生産能力の上限込みの方程式 `Y = softmin(Z(C Y + a), Y_p)` の解として定義する(`Ysol`)。
Python 版はこれを反復法で解いている。ここでは、解がただ一つあるときはそれを、そうでなければ 0 を取る。
-/

open Finset BigOperators Real

namespace CreditV6

/-- 地域ごとの量。 -/
abbrev Vec (N : ℕ) := Fin N → ℝ

/-- `min(a, b)` のなめらか版(幅 `w`)。Python の `softmin` と同じ。 -/
noncomputable def softmin (a b w : ℝ) : ℝ := -w * log (exp (-a / w) + exp (-b / w))

/-- `max(0, a)` のなめらか版(幅 `w`): `w · log(1 + exp(a/w))`。Python の `w * np.logaddexp(0, a / w)` と同じ。 -/
noncomputable def softplus (a w : ℝ) : ℝ := w * log (exp 0 + exp (a / w))

/-- モデルのパラメータ(地域ごと)と、地域の間の構造。 -/
structure Params (N : ℕ) where
  dt : ℝ
  v : Vec N
  u_max : Vec N
  omega : Vec N
  d0 : Vec N
  kappa : Vec N
  c_w : Vec N
  c_r : Vec N
  c_v : Vec N
  payout : Vec N
  tau : Vec N
  gG : Vec N
  fiscal : Vec N
  b_target : Vec N
  r_cb : Vec N
  spread : Vec N
  spread_loss : Vec N
  rho : Vec N
  g0 : Vec N
  g1 : Vec N
  g2 : Vec N
  g_q : Vec N
  q_ref : Vec N
  prem : Vec N
  lam : Vec N
  T_adj : Vec N
  default_share : Vec N
  tau_e : Vec N
  m : Vec N
  /-- `trade j i`: 地域 j の輸入のうち地域 i から買う割合。 -/
  trade : Fin N → Fin N → ℝ
  /-- `hold j i`: 地域 j の企業・政府への請求権のうち、地域 i の金利生活者が持つ割合。 -/
  hold : Fin N → Fin N → ℝ

/-- モデルの状態。前半は規模とともに伸びる量(1 次)、後半は比率(0 次)。 -/
@[ext]
structure State (N : ℕ) where
  K : Vec N
  L : Vec N
  B : Vec N
  S : Vec N
  Pi_e : Vec N
  Pi_prev : Vec N
  E_prev : Vec N
  Y_prev : Vec N
  loss : Vec N
  u_prev : Vec N

/-- 規模の作用: 1 次の量だけを c 倍する。 -/
def State.act {N : ℕ} (c : ℝ) (x : State N) : State N where
  K := c • x.K
  L := c • x.L
  B := c • x.B
  S := c • x.S
  Pi_e := c • x.Pi_e
  Pi_prev := c • x.Pi_prev
  E_prev := c • x.E_prev
  Y_prev := c • x.Y_prev
  loss := x.loss
  u_prev := x.u_prev

instance {N : ℕ} : Scaling (State N) where
  act := State.act
  act_mul := by intro a b x; simp [State.act, smul_smul]
  act_one := by intro x; simp [State.act]

section quantities
variable {N : ℕ} (p : Params N) (x : State N)

/-- 資本で決まる生産能力 `K/v` と、上限込みの能力 `u_max K/v`。 -/
noncomputable def Yk : Vec N := fun i => x.K i / p.v i
noncomputable def Yp : Vec N := fun i => p.u_max i * Yk p x i

/-- 貸出金利(0 次)。 -/
noncomputable def rL : Vec N := fun i =>
  (p.r_cb i + p.spread i) / (1 - p.rho i) + p.spread_loss i * min (x.loss i) 0.1

/-- 株式的富: 期待利潤をなめらかに正にして(幅は資本の 0.1%)、割引率で割る。 -/
noncomputable def Eq : Vec N := fun i =>
  softplus (x.Pi_e i) (0.001 * x.K i) / (softplus (rL p x i + p.prem i) 0.005 + 0.005)

/-- 株式的富の目減りによる損耗の増幅(0 次)。 -/
noncomputable def delta : Vec N := fun i =>
  p.d0 i * (1 + p.kappa i * (max 0 (-(Eq p x i - x.E_prev i) / x.E_prev i) / p.dt))

/-- 純投資率の希望(0 次)。 -/
noncomputable def gnet : Vec N := fun i =>
  p.g0 i + p.g1 i * x.Pi_prev i / x.K i + p.g2 i * (x.u_prev i - 0.85) + p.g_q i * (Eq p x i / x.K i - p.q_ref i)

noncomputable def Ides : Vec N := fun i => x.K i * max 0 (p.d0 i + gnet p x i)
noncomputable def retained : Vec N := fun i => (1 - p.payout i) * x.Pi_prev i + p.d0 i * x.K i
noncomputable def dLraw : Vec N := fun i =>
  softmin (Ides p x i - retained p x i) ((p.lam i * (Eq p x i + x.K i) - x.L i) / p.T_adj i) (0.01 * x.K i)
noncomputable def Inv : Vec N := fun i => max 0 (dLraw p x i + retained p x i)
noncomputable def dL : Vec N := fun i => Inv p x i - retained p x i
noncomputable def Gov : Vec N := fun i => p.gG i * Yp p x i / p.u_max i

/-- 財政ルールで動く税率(0 次)。 -/
noncomputable def tauE : Vec N := fun i =>
  max 0 (min (p.tau i + p.fiscal i * (x.B i / x.Y_prev i - p.b_target i)) 0.8)

noncomputable def ct : Vec N := fun i => 1 - tauE p x i

/-- 所得に依らない利子・配当の部分(支払う側 j)。 -/
noncomputable def flow0 : Vec N := fun j =>
  rL p x j * x.L j + p.r_cb j * x.B j + p.payout j * (-p.d0 j * x.K j - rL p x j * x.L j)

noncomputable def wealth : Vec N := fun i => (∑ j, p.hold j i * (x.L j + x.B j)) + x.S i

/-- 需要のうち所得に依らない部分 `a`。 -/
noncomputable def avec : Vec N := fun i =>
  p.c_r i * ct p x i * ((∑ j, p.hold j i * flow0 p x j) + p.r_cb i * x.S i)
    + p.c_v i * wealth p x i + Inv p x i + Gov p x i

/-- 支出 `D = C Y + a`(所得 `Y` を与えたとき)。 -/
noncomputable def Dvec (Y : Vec N) : Vec N := fun i =>
  p.c_w i * ct p x i * p.omega i * Y i
    + p.c_r i * ct p x i * (∑ j, p.hold j i * (p.payout j * (1 - p.omega j) * Y j))
    + avec p x i

/-- `Z[i, j]`: 地域 j の支出のうち地域 i の生産になる割合。 -/
def Zm (i j : Fin N) : ℝ := (if i = j then 1 - p.m j else 0) + p.trade j i * p.m j

/-- 実際の所得のもとでの需要(生産の側から見たもの) `Z (C Y + a)`。 -/
noncomputable def demand (Y : Vec N) : Vec N := fun i => ∑ j, Zm p i j * Dvec p x Y j

/-- 所得の方程式: `Y = softmin(Z(C Y + a), Y_p)`(幅は能力の 1%)。 -/
def eqY (Y : Vec N) : Prop := ∀ i, Y i = softmin (demand p x Y i) (Yp p x i) (0.01 * Yp p x i)

open Classical in
/-- 所得: 方程式の解がただ一つあればそれ、なければ 0。 -/
noncomputable def Ysol : Vec N := if h : ∃! Y, eqY p x Y then h.exists.choose else 0

end quantities

section step
variable {N : ℕ} (p : Params N) (x : State N)

noncomputable def Yv : Vec N := Ysol p x
noncomputable def Pi : Vec N := fun i => (1 - p.omega i) * Yv p x i - p.d0 i * x.K i - rL p x i * x.L i
noncomputable def pay : Vec N := fun j => rL p x j * x.L j + p.r_cb j * x.B j + p.payout j * Pi p x j
noncomputable def rentIn : Vec N := fun i => (∑ j, p.hold j i * pay p x j) + p.r_cb i * x.S i
noncomputable def Wage : Vec N := fun i => p.omega i * Yv p x i
noncomputable def consDes : Vec N := fun i =>
  p.c_w i * ct p x i * Wage p x i + p.c_r i * ct p x i * rentIn p x i + p.c_v i * wealth p x i
noncomputable def Ddes : Vec N := fun i => consDes p x i + Inv p x i + Gov p x i
/-- 財が行き渡る割合(0 次)。 -/
noncomputable def rhoS : Vec N := fun i => Yv p x i / demand p x (Yv p x) i
/-- `purch i j`: 地域 j が実際に地域 i から買う額。 -/
noncomputable def purch (i j : Fin N) : ℝ := Zm p i j * Ddes p x j * rhoS p x i
noncomputable def Dreal : Vec N := fun j => ∑ i, purch p x i j
noncomputable def Imp : Vec N := fun j => Dreal p x j - purch p x j j
noncomputable def Exp : Vec N := fun i => (∑ j, purch p x i j) - purch p x i i
noncomputable def tax : Vec N := fun i => tauE p x i * (Wage p x i + rentIn p x i)
noncomputable def CA : Vec N := fun i => Exp p x i - Imp p x i + (rentIn p x i - pay p x i)
noncomputable def CF : Vec N := fun i => (1 - p.omega i) * Yv p x i - rL p x i * x.L i
noncomputable def default : Vec N := fun i =>
  min (p.default_share i * max 0 (-CF p x i)) (0.5 * x.L i)
noncomputable def dB : Vec N := fun i => Gov p x i + p.r_cb i * x.B i - tax p x i
noncomputable def newIss : Vec N := fun i => dL p x i + dB p x i
noncomputable def portOut : Vec N := fun i => (∑ j, p.hold j i * newIss p x j) - newIss p x i
noncomputable def dS : Vec N := fun i => CA p x i - portOut p x i

/-- **1 期の写像**(`simulate_world` のループの 1 回分)。 -/
noncomputable def step : State N where
  K := fun i => x.K i + (Inv p x i - delta p x i * x.K i) * p.dt
  L := fun i => max 0 (x.L i + (dL p x i - default p x i) * p.dt)
  B := fun i => x.B i + dB p x i * p.dt
  S := fun i => x.S i + dS p x i * p.dt
  Pi_e := fun i => x.Pi_e i + (Pi p x i - x.Pi_e i) / p.tau_e i * p.dt
  Pi_prev := Pi p x
  E_prev := Eq p x
  Y_prev := Yv p x
  loss := fun i => default p x i / x.L i
  u_prev := fun i => Yv p x i / Yk p x i

end step

end CreditV6
