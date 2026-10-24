# 信用創造ダイナミクス v5 の Python 移植と検証用シミュレーション
# ノートブックには %%CELL マーカーで分割して埋め込む予定。

# %%CELL v5
import numpy as np

V5_DEFAULT = dict(r=0.05, rho=0.10, s=0.20, d0=0.04, kappa=3.0, dC=0.05,
                  theta=0.25, mu=0.60, lam=0.25, gam=0.40, alpha=0.70, T=150,
                  C0=10.0, K0=10.0, Y0=1.0, smooth=0.0)


def ramp(x, w):
    """max(0, x)。w>0 なら幅 w の softplus で滑らかにする。"""
    if w <= 0:
        return max(0.0, x)
    return w * np.logaddexp(0.0, x / w)


def simulate_v5(**kw):
    """credit_simulation_v5.html の simulate() の忠実な移植(dt=0.1 のオイラー法)。"""
    p = {**V5_DEFAULT, **kw}
    eps = 1e-8
    C, K = p['C0'], p['K0']
    E_prev = K ** p['alpha'] / (p['r'] + p['d0'] + eps)
    Y_prev = p['Y0']  # JS 版の初期値は 1(h.Y が空のとき)
    keys = ['C', 'K', 'Y', 'E', 'Phi', 'dK', 'seff', 'rhoeff', 'cons', 'dk2', 'Cflow']
    h = {k: [] for k in keys}
    for t in range(int(p['T'])):
        E_cur = K ** p['alpha'] / (p['r'] + p['d0'] + eps)
        stress = max(0.0, -(E_cur - E_prev) / (abs(E_prev) + eps))
        dK = p['d0'] * (1 + p['kappa'] * stress)
        loss_K = dK * K
        Phi = p['r'] * C / max(Y_prev, eps)
        rho_eff = min(p['rho'] + p['mu'] * ramp(Phi - p['theta'], p['smooth']), 0.99)
        s_eff = min(p['s'] + p['gam'] * ramp(Phi - p['theta'], p['smooth']), 0.95)
        E = K ** p['alpha'] / (p['r'] + dK + eps)
        C_flow = p['lam'] * E * (1 - rho_eff)
        dC2 = C_flow - p['r'] * C
        Y = C_flow / max(1 + s_eff + p['dC'] * (1 - s_eff), eps)
        cons = (1 - s_eff) * Y
        deltaK = s_eff * Y - loss_K
        for k, v in zip(keys, [C, K, Y, E, Phi, dK, s_eff, rho_eff, cons, deltaK, C_flow]):
            h[k].append(v)
        E_prev = E
        Y_prev = Y
        C = max(C + dC2 * 0.1, 0.01)
        K = max(K + deltaK * 0.1, 0.01)
    return {k: np.array(v) for k, v in h.items()}


# %%CELL v5_steady
def v5_steady_state(**kw):
    """v5 の内点定常状態(ΔC=0, ΔK=0, stress=0)を解析的に求める。

    ΔC=0 より C_flow = rC、Y = C_flow/D なので Φ* = rC/Y = D(s_eff)。
    D = 1 + s_eff + δC(1−s_eff) ≥ 1 なので、Φ* は必ず 1 以上になる。
    """
    p = {**V5_DEFAULT, **kw}
    # Φ = D, s_eff = s + γ max(0, Φ−θ) の不動点(クリップ込み)を反復で解く
    Phi = 1.0
    for _ in range(500):
        s_eff = min(p['s'] + p['gam'] * max(0.0, Phi - p['theta']), 0.95)
        Phi_new = 1 + s_eff + p['dC'] * (1 - s_eff)
        if abs(Phi_new - Phi) < 1e-13:
            break
        Phi = 0.5 * Phi + 0.5 * Phi_new
    rho_eff_raw = p['rho'] + p['mu'] * max(0.0, Phi - p['theta'])
    rho_eff = min(rho_eff_raw, 0.99)
    a, d0, r = p['alpha'], p['d0'], p['r']
    # K = s_eff Y/δ0, E = K^α/(r+δ0), Y = λE(1−ρ_eff)/D
    Y = (p['lam'] * (1 - rho_eff) * (s_eff / d0) ** a / (Phi * (r + d0))) ** (1 / (1 - a))
    K = s_eff * Y / d0
    return dict(Phi=Phi, s_eff=s_eff, rho_eff_raw=rho_eff_raw, rho_eff=rho_eff,
                Y=Y, K=K, C=Phi * Y / r, E=K ** a / (r + d0))


# %%CELL v5_jacobian
def v5_step(state, p):
    """v5 の 1 ステップ写像(状態 = C, K, 前期 Y, 前期 E)。クリップは定常点の近傍では効かないものとする。"""
    C, K, Yp, Ep = state
    eps = 1e-8
    E_cur = K ** p['alpha'] / (p['r'] + p['d0'] + eps)
    stress = max(0.0, -(E_cur - Ep) / (abs(Ep) + eps))
    dK = p['d0'] * (1 + p['kappa'] * stress)
    Phi = p['r'] * C / Yp
    rho_eff = p['rho'] + p['mu'] * max(0.0, Phi - p['theta'])
    s_eff = p['s'] + p['gam'] * max(0.0, Phi - p['theta'])
    E = K ** p['alpha'] / (p['r'] + dK + eps)
    C_flow = p['lam'] * E * (1 - rho_eff)
    Y = C_flow / (1 + s_eff + p['dC'] * (1 - s_eff))
    return np.array([C + (C_flow - p['r'] * C) * 0.1,
                     K + (s_eff * Y - dK * K) * 0.1, Y, E])


def v5_spectral_radius(**kw):
    """内点定常状態での 1 ステップ写像のヤコビアンの最大固有値の絶対値(1 未満なら局所安定)。"""
    p = {**V5_DEFAULT, **kw}
    ss = v5_steady_state(**kw)
    x0 = np.array([ss['C'], ss['K'], ss['Y'], ss['E']])
    J = np.zeros((4, 4))
    for j in range(4):
        # stress は max(0, ·) の折れ目にあるので、stress が立たない側(前期 E は下げる側)の片側差分を取る
        h = 1e-6 * x0[j] * (-1 if j == 3 else 1)
        J[:, j] = (v5_step(x0 + np.eye(4)[j] * h, p) - v5_step(x0, p)) / h
    return max(abs(np.linalg.eigvals(J)))


# %%CELL cmodel
# Claude 版「信用循環モデル」: ストック・フロー一貫(SFC)の二階級モデル。
# 部門: 企業(借りて K を積む)、労働者(賃金を消費)、金利生活者(利子・配当を受け取り、貯蓄しやすい)、
#       銀行(貸出が預金を作る。準備率 ρ と現金選好 cu で量的上限がかかりうる)、政府(G・税・国債)。
CM_DEFAULT = dict(
    T=150.0, dt=0.1,
    v=2.5,          # 資本係数: 生産能力 Y_p = K/v
    u_max=1.1,      # 資本稼働率の上限(能力を超えた需要は実現せず「価格圧力」になる)
    omega=0.65,     # 賃金分配率(利潤分配率 π = 1 − ω)
    d0=0.05,        # 平時の損耗率 δ0(在庫・設備・知識の陳腐化)
    kappa=3.0,      # 株式的富 E が縮むときの損耗増幅(在庫維持能力の喪失)
    c_w=0.95,       # 労働者の消費性向
    c_r=0.35,       # 金利生活者の所得からの消費性向
    c_v=0.02,       # 金利生活者の金融資産(L+B)からの消費性向
    payout=0.6,     # 配当性向
    tau=0.25,       # 税率(全所得)
    foreign=0.0,    # 利子・配当のうち国外の金利生活者に渡る割合(国内では使われず、課税もされない)
    gG=0.20,        # 政府支出 G = gG·Y_p
    fiscal=0.0,     # 財政ルール: 税率を (B/Y − b_target) に比例して上げる強さ
    b_target=0.6,
    r_cb=0.03,      # 政策金利(= 国債金利)
    spread=0.01,    # 貸出スプレッド
    spread_loss=2.0,# 貸倒れ率に応じたスプレッドの上乗せ
    rho=0.05,       # 法定準備率
    regime='rate',  # 'rate': 金利レジーム、'quantity': ベースマネー H を一定率で伸ばす量的レジーム
    gH=0.025,       # 量的レジームでの H の伸び率
    cu0=0.05,       # 平時の現金/預金比(タンス預金)
    cu_loss=8.0,    # 貸倒れ率に対する現金選好の感応度
    g0=-0.02, g1=0.75, g2=0.0,  # 純投資率 I/K − δ = g0 + g1·(Π/K) + g2·(u − 0.85)
    prem=0.02,      # 株式のリスクプレミアム(E = 期待利潤/(r_L + prem − g_e))
    g_exp=0.0,      # 期待成長率 g_e を E の評価に織り込む度合い(1 で完全。バブルの温床)
    tau_g=3.0,      # 期待成長率の適応の時定数(年)
    g_q=0.0,        # 投資のトービンの q への反応: + g_q·(E/K − q_ref)
    q_ref=0.9,
    lam=0.6,        # 担保制約: 借入上限 L_max = lam·(E + K)
    T_adj=2.0,      # 上限を超えたときの返済の速さ(年)
    default_share=0.5,  # 企業損失のうち貸倒れになる割合
    tau_e=2.0,      # 期待利潤の適応の時定数(年)
    a_growth=0.015, pop_growth=0.005,  # 労働生産性と人口の伸び(自然成長率 ≈ 2%)
    labor_cap=False,# True: 生産能力は「資本」と「完全雇用」の小さいほう。False: 労働は読み出しのみ
    phillips=0.0,   # 賃金分配率の雇用率への反応(グッドウィン)。0 で賃金分配率固定
    e_star=0.90,    # 賃金分配率が動かない雇用率
    K0=250.0, L0=60.0, B0=60.0, emp0=0.92,
    init='steady',  # 'steady': 予備走行(κ=0, ショックなし)で釣り合った比率を求めて初期値にする
    shocks=(),      # [(t, {param: value}) または (t, {...}, 期間)]: 時刻 t から(期間をかけて線形に)書き換える
)


def softmin(a, b, w):
    """min(a, b) の滑らか版(幅 w)。"""
    return -w * np.logaddexp(-a / w, -b / w)


# 毎期記録する量(simulate_cm が返す辞書のキー)
CM_KEYS = [
    't',         # 時刻(年)
    'Y',         # 実現した所得(= 生産)
    'Yd',        # 需要の合計(生産能力の上限をかける前)。Yd − Y が価格圧力
    'K',         # 在庫・資本(生産能力のもと。研究・知識も含む)
    'L',         # 企業の借入残高(= v5 の信用量 C に当たる)
    'B',         # 国債残高
    'E',         # 株式的富(期待利潤の資本還元)
    'Pi',        # 企業の純利潤(平時の減価償却 δ0 と利払いを引いた後)
    'Phi',       # 利払い負担率 r_L·L/Y(v5 の Φ)
    'theta_star',# 利払い前の純利潤分配率 ((1−ω)Y − δ0 K)/Y(v5 の θ に当たる)
    'u',         # 資本稼働率 Y/(K/v)
    'I',         # 実際の投資
    'cons_w',    # 労働者の消費
    'cons_r',    # 金利生活者の消費
    'G',         # 政府支出
    'tax',       # 税収
    'r_L',       # 貸出金利
    'cu',        # 現金/預金比(タンス預金)
    'rho_eff',   # 実効準備率 ρ + cu
    's_agg',     # 経済全体の貯蓄率(可処分所得のうち使われなかった割合)
    'loss_rate', # 貸倒れ率(1 年あたり、借入残高に対する割合)
    'emp',       # 雇用率
    'omega',     # 賃金分配率
    'delta',     # 実際の損耗率(株式的富の目減りで増幅)
    'minsky',    # 資金繰りの分類 2=ヘッジ, 1=投機的, 0=ポンジ
    'credit_cap',# 量の制度での銀行信用の上限 (1−ρ)H/(ρ+cu)
    'tau',       # 税率(財政ルールで動く)
    'rent_share',# 金利生活者の所得(利子・配当)/ Y
    'g',         # 資本の純成長率 (I − δK)/K
    'B_Y',       # 国債残高 / Y
    'L_Y',       # 企業の借入残高 / Y
    'g_e',       # 期待成長率
    'q',         # トービンの q = E/K
]


def simulate_cm(**kw):
    p = {**CM_DEFAULT, **kw}
    dt = p['dt']
    n = int(round(p['T'] / dt))
    K, L, B = float(p['K0']), float(p['L0']), float(p['B0'])
    omega = p['omega']
    r_L0 = (p['r_cb'] + p['spread']) / (1 - p['rho'])
    Pi_e = (1 - omega) * K / p['v'] * 0.9 - p['d0'] * K - r_L0 * L
    if p['init'] == 'steady':
        pre = simulate_cm(**{**kw, 'init': None, 'kappa': 0.0, 'shocks': (), 'T': 300.0,
                             'regime': 'rate', 'phillips': 0.0})
        f = K / pre['K'][-1]
        L, B, Pi_e = pre['L'][-1] * f, pre['B'][-1] * f, pre['Pi'][-1] * f
    Pi_prev, loss_rate, delta, E_prev = Pi_e, 0.0, p['d0'], None
    g_e = pre['g'][-1] if p['init'] == 'steady' else 0.0
    a, Pop = 1.0, (0.9 * K / p['v']) / p['emp0']
    H = (L + B) * (p['rho'] + p['cu0']) / (1 - p['rho'])  # 初期は量的上限ちょうど
    out = {k: np.empty(n) for k in CM_KEYS}
    shocks = [(sh[0], sh[1], sh[2] if len(sh) > 2 else 0.0, {}) for sh in p['shocks']]
    for i in range(n):
        t = i * dt
        for ts, ch, dur, base in shocks:
            if t >= ts - dt / 2 and t <= ts + dur + dt / 2:
                if not base:
                    base.update({k: p[k] for k in ch})
                w = 1.0 if dur <= 0 else min(1.0, (t - ts + dt / 2) / dur)
                for k, v in ch.items():
                    p[k] = base[k] + w * (v - base[k]) if isinstance(v, float) else v
                if 'omega' in ch:
                    omega = p['omega']
        Y_k = K / p['v']                       # 資本で決まる能力
        Y_n = a * Pop                          # 完全雇用で決まる能力
        Y_p = softmin(p['u_max'] * Y_k, Y_n, 0.01 * Y_n) if p['labor_cap'] else p['u_max'] * Y_k
        r_L = (p['r_cb'] + p['spread']) / (1 - p['rho']) + p['spread_loss'] * min(loss_rate, 0.1)
        r_B = p['r_cb']
        # 株式的富 E: 期待利潤を資本還元(永続企業の前提)。期待利潤が負なら 0 に近づく
        disc = r_L + p['prem'] - p['g_exp'] * g_e
        wE = 0.001 * K                           # なめらかさの幅は資本に比例させる(モデルを規模について同次に保つ)
        E = wE * np.logaddexp(0.0, Pi_e / wE) / (0.005 * np.logaddexp(0.0, disc / 0.005) + 0.005)
        if E_prev is not None:
            stress = max(0.0, -(E - E_prev) / max(E_prev, 1e-9)) / dt
            delta = p['d0'] * (1 + p['kappa'] * stress)
        E_prev = E
        # 投資の希望と資金繰り
        u_prev = out['u'][i - 1] if i > 0 else 0.9  # 資本稼働率 Y/(K/v)
        g_net = (p['g0'] + p['g1'] * Pi_prev / K + p['g2'] * (u_prev - 0.85)
                 + p['g_q'] * (E / K - p['q_ref']))
        # 置き換え投資は平時の δ0 分だけ(ストレスで壊れた分は「失われる」だけで置き換えない)
        I_des = K * max(0.0, p['d0'] + g_net)
        retained = (1 - p['payout']) * Pi_prev + p['d0'] * K  # 内部資金 = 内部留保 + 減価償却
        dL_des = I_des - retained
        dL_col = (p['lam'] * (E + K) - L) / p['T_adj']          # 担保制約
        cu = p['cu0'] + p['cu_loss'] * loss_rate                 # タンス預金(現金選好)
        credit_cap = (1 - p['rho']) * H / (p['rho'] + cu)        # 量的上限(銀行信用 L+B)
        w = 0.01 * K
        dL = softmin(dL_des, dL_col, w)
        if p['regime'] == 'quantity':
            dL = softmin(dL, (credit_cap - L - B) / p['T_adj'], w)
        I = max(0.0, dL + retained)
        dL = I - retained
        # 政府
        G = p['gG'] * Y_p / p['u_max']
        Yl = out['Y'][i - 1] if i > 0 else 0.9 * Y_p
        tau = min(max(p['tau'] + p['fiscal'] * (B / Yl - p['b_target']), 0.0), 0.8)
        # 所得の決定: Y = 労働者消費 + 金利生活者消費 + I + G(Y について一次式)
        pi_sh = 1 - omega
        ct = 1 - tau
        dom = 1 - p['foreign']
        auto = (p['c_r'] * ct * dom * (r_L * L + r_B * B + p['payout'] * (-p['d0'] * K - r_L * L))
                + p['c_v'] * dom * (L + B) + I + G)
        mult = 1 - p['c_w'] * ct * omega - p['c_r'] * ct * dom * p['payout'] * pi_sh
        Yd = auto / mult
        # 生産能力の上限込みの釣り合い: Y = softmin(auto + (1 − mult) Y, Y_p) を反復で解く
        Y = max(softmin(Yd, Y_p, 0.01 * Y_p), 1e-9)
        for _ in range(200):
            Y_new = max(softmin(auto + (1 - mult) * Y, Y_p, 0.01 * Y_p), 1e-9)
            if abs(Y_new - Y) < 1e-12 * Y:
                Y = Y_new
                break
            Y = 0.5 * Y + 0.5 * Y_new
        gap = auto + (1 - mult) * Y - Y              # 生産できなかった需要(買えなかった分は消費から引く)
        Pi = pi_sh * Y - p['d0'] * K - r_L * L   # 平時の減価償却での利潤(配当・投資判断・期待の基準)
        div = p['payout'] * Pi
        W = omega * Y
        rent_inc = r_L * L + r_B * B + div
        cons_w = p['c_w'] * ct * W
        cons_r = p['c_r'] * ct * dom * rent_inc + p['c_v'] * dom * (L + B)
        if gap > 0:                                  # 強制貯蓄: 買えなかった分を消費に比例して割り当てる
            f_c = 1 - gap / (cons_w + cons_r)
            cons_w, cons_r = cons_w * f_c, cons_r * f_c
        tax = tau * (W + dom * rent_inc)
        CF = pi_sh * Y - r_L * L                 # 利払い後の営業キャッシュフロー
        default = min(p['default_share'] * max(0.0, -CF), 0.5 * L)  # 利払いができない分の一部が貸倒れ(年に残高の半分まで)
        loss_rate = default / max(L, 1e-6)
        op_cf = pi_sh * Y - p['d0'] * K
        emp = (Y / a) / Pop
        rec = dict(t=t, Y=Y, Yd=Yd, K=K, L=L, B=B, E=E, Pi=Pi, Phi=r_L * L / Y, theta_star=op_cf / Y,
                   u=Y / Y_k, I=I, cons_w=cons_w, cons_r=cons_r, G=G, tax=tax, r_L=r_L, cu=cu,
                   rho_eff=p['rho'] + cu, s_agg=1 - (cons_w + cons_r) / max(W + rent_inc - tax, 1e-9),
                   loss_rate=loss_rate, emp=emp, omega=omega, delta=delta,
                   minsky=2 if op_cf >= r_L * L + L / 10 else (1 if op_cf >= r_L * L else 0),
                   credit_cap=credit_cap, tau=tau, rent_share=rent_inc / Y, g=(I - delta * K) / K,
                   B_Y=B / Y, L_Y=L / Y, g_e=g_e, q=E / K)
        for k, val in rec.items():
            out[k][i] = val
        # ストックの更新
        K = max(K + (I - delta * K) * dt, 1e-3)
        L = max(L + (dL - default) * dt, 0.0)
        B = B + (G + r_B * B - tax) * dt
        Pi_e += (Pi - Pi_e) / p['tau_e'] * dt
        Pi_prev = Pi
        g_e += ((I - delta * K) / K - g_e) / p['tau_g'] * dt
        H *= np.exp(p['gH'] * dt)
        a *= np.exp(p['a_growth'] * dt)
        Pop *= np.exp(p['pop_growth'] * dt)
        if p['phillips'] > 0:
            omega = min(max(omega * (1 + p['phillips'] * (emp - p['e_star']) * dt), 0.3), 0.95)
    return out
