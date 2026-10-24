# 多地域の信用循環モデル(共通通貨)。前のノートの simulate_cm を N 地域に一般化したもの。
# ノートブックには %%CELL マーカーで分割して埋め込む。

# %%CELL world
import numpy as np

# 地域ごとに持てるパラメータ(スカラーなら全地域共通、長さ N の配列なら地域別)
WORLD_DEFAULT = dict(
    T=150.0, dt=0.1,
    v=2.5,          # 資本係数: 生産能力 Y_p = K/v
    u_max=1.1,      # 資本稼働率の上限
    omega=0.65,     # 賃金分配率
    d0=0.05,        # 平時の損耗率 δ0
    kappa=3.0,      # 株式的富が縮むときの損耗増幅
    c_w=0.95,       # 労働者の消費性向
    c_r=0.35,       # 金利生活者の所得からの消費性向
    c_v=0.02,       # 金利生活者の金融資産からの消費性向
    payout=0.6,     # 配当性向
    tau=0.25,       # 税率(居住地ベース)
    gG=0.20,        # 政府支出 G = gG·Y_p/u_max
    fiscal=0.0,     # 財政ルール: 税率を (国債/所得 − b_target) に比例して上げる強さ(財政統合中は統合全体の比率を見る)
    b_target=0.6,
    r_cb=0.03,      # 共通の政策金利(= 国債金利 = 決済残高の金利)
    spread=0.01,    # 貸出スプレッド
    spread_loss=2.0,# 貸倒れ率に応じたスプレッドの上乗せ
    rho=0.05,       # 法定準備率
    g0=-0.02, g1=0.75, g2=0.0,  # 純投資率 = g0 + g1·Π/K + g2·(u − 0.85) + g_q·(q − q_ref)
    g_q=0.0, q_ref=0.9,
    prem=0.02,      # 株式のリスクプレミアム
    lam=0.6,        # 担保制約 L ≤ lam·(E + K)
    T_adj=2.0,      # 担保制約を超えたときの返済の速さ(年)
    default_share=0.5,
    tau_e=2.0,      # 期待利潤の適応の時定数(年)
    m=0.0,          # 輸入性向(支出のうち他地域から買う割合)
    a_growth=0.015, pop_growth=0.005,
    labor_cap=False, phillips=0.0, e_star=0.90,
    theta_c=5.0,    # 貿易の取り分の競争力への感応度(phi_trade を与えたときだけ使う)
    verdoorn=0.0,   # 競争力の伸び = verdoorn ×(成長率 − 世界平均)− price_adj ×(稼働率 − 世界平均)− diffuse × ln A
    price_adj=0.0,  # 売れずに設備が遊ぶ地域は、賃金・価格が下がって競争力を取り戻す(安定化の力)
    diffuse=0.05,   # 技術の拡散(競争力の差は平均へ引き戻される)
)
# 地域の間の構造(N×N 行列)と初期値
WORLD_STRUCT = dict(
    trade=None,     # trade[j, i]: 地域 j の輸入のうち地域 i から買う割合(行の和 1、対角 0)。None なら均等
    hold=None,      # hold[j, i]: 地域 j の企業の借入・国債への請求権のうち、地域 i の金利生活者が持つ割合(行の和 1)。None なら単位行列
    K0=None,        # 地域ごとの初期の資本(None なら 250 を N 等分)
    init='steady',  # 'steady': 予備走行(κ=0, ショックなし)で釣り合った比率を求めて初期値にする
    state=None,     # 初期状態を直接与える辞書(K, L, B, S, Pi_e)。与えたときは init を無視する
    phi_trade=None, # 貿易の自由度 φ(0〜1)。与えると、支出の地域への配分を競争力 A から
                    # S_ij = K_i A_i^θ φ^{[i≠j]} / Σ_k K_k A_k^θ φ^{[k≠j]} で決め、m と trade はそれで上書きする
    A0=None,        # 競争力の初期値(None なら全地域 1)
    fx=None,        # 通貨が別々のとき: dict(currency=[地域ごとの通貨 0/1], regime='float' か 'fixed',
                    #   eta=輸入の価格弾力性, k_ca=経常収支への為替の反応, k_r=金利差への反応,
                    #   k_q=株式の収益見通し(トービンの q)の差への反応(資本の流れ),
                    #   k_u=稼働率の差への反応(不況の国の通貨が下がる), e0=為替の初期値,
                    #   shifts=[(時刻, 新しい平価, 期間)]: 固定相場での平価の変更)
                    # e は通貨 1 の価値を通貨 0 で測ったもの。各地域の量は自国通貨建て
    fiscal_union=None,  # (開始時刻, 終了時刻): その間、全地域の赤字を合算し、新しい国債を所得の比率で割り振る
                        # (過去の国債は各地域に残る)。差額は地域間の財政移転として経常収支に入る
    shocks=(),      # [(t, {param: 値 または 配列}, 期間)]
)

WORLD_KEYS = [
    't',          # 時刻(年)
    'Y',          # 実現した所得(= 生産)
    'Yd',         # 需要で決まる所得(生産能力の上限をかける前)
    'D',          # 地域の支出(消費 + 投資 + 政府支出)
    'K',          # 資本
    'L',          # 企業の借入残高
    'B',          # 国債残高
    'S',          # 決済残高(共通の中央銀行への請求権)
    'E',          # 株式的富
    'Pi',         # 企業の純利潤
    'X',          # 輸出
    'M',          # 輸入
    'CA',         # 経常収支 = 輸出 − 輸入 + 純第一次所得(利子・配当の受け払い)
    'NFA',        # 対外純資産(ポートフォリオ + 決済残高)
    'rent_in',    # 金利生活者が受け取る利子・配当(居住地ベース)
    'r_L',        # 貸出金利
    'u',          # 資本稼働率
    'g',          # 資本の純成長率
    'Phi',        # 利払い負担率 r_L L / Y
    'theta_star', # 利払い前の純利潤分配率
    'q',          # トービンの q
    'delta',      # 実際の損耗率
    'emp',        # 雇用率
    'omega',      # 賃金分配率
    'tax',        # 税収
    'G',          # 政府支出
    'sb_err',     # 部門収支の恒等式の誤差(0 になるはず)
    'pay',        # 企業の借入・国債に対して地域が払う利子・配当
    'I',          # 投資
    'Pi_e',       # 期待利潤
    'A',          # 競争力
    'm',          # 輸入性向
    'tr',         # 地域間の財政移転(受け取り)
    'tau',        # 税率(財政ルールで動く)
    'e',          # 為替レート(通貨 1 の価値を通貨 0 で測ったもの)
    'cv',         # 自国通貨 1 単位の、通貨 0 での価値
]


def softmin(a, b, w):
    """min(a, b) の滑らか版(幅 w)。"""
    return -w * np.logaddexp(-a / w, -b / w)


def _vec(x, N):
    return np.full(N, float(x)) if np.isscalar(x) else np.asarray(x, float).copy()


def simulate_world(N=2, **kw):
    struct = {k: kw.pop(k) if k in kw else v for k, v in WORLD_STRUCT.items()}
    p = {k: (kw[k] if k in kw else v) for k, v in WORLD_DEFAULT.items()}
    flags = {k: p[k] for k in ('labor_cap',)}
    P = {k: _vec(v, N) for k, v in p.items() if k not in ('T', 'dt', 'labor_cap')}
    dt = p['dt']
    n = int(round(p['T'] / dt))
    Tm = (np.ones((N, N)) - np.eye(N)) / max(N - 1, 1) if struct['trade'] is None else np.asarray(struct['trade'], float)
    F = np.eye(N) if struct['hold'] is None else np.asarray(struct['hold'], float)
    K = _vec(250.0 / N, N) if struct['K0'] is None else _vec(struct['K0'], N)
    L, B, S = 60.0 / 250.0 * K, 60.0 / 250.0 * K, np.zeros(N)
    omega = P['omega'].copy()
    r_L0 = (P['r_cb'] + P['spread']) / (1 - P['rho'])
    Pi_e = (1 - omega) * K / P['v'] * 0.9 - P['d0'] * K - r_L0 * L
    if struct['state'] is not None:
        st = struct['state']
        K, L, B, S, Pi_e = (_vec(st[k], N) for k in ('K', 'L', 'B', 'S', 'Pi_e'))
        Pi_prev0 = _vec(st.get('Pi_prev', st['Pi_e']), N)
    elif struct['init'] == 'steady':
        pre = simulate_world(N=N, **{**kw, 'kappa': 0.0, 'T': 300.0, 'phillips': 0.0},
                             trade=struct['trade'], hold=struct['hold'], K0=K, init=None, state=None, shocks=(),
                             phi_trade=struct['phi_trade'], A0=struct['A0'], fiscal_union=None,
                             fx=None if struct['fx'] is None else {k: v for k, v in struct['fx'].items() if k != 'shifts'})
        f = K.sum() / pre['K'][-1].sum()
        K, L, B, S, Pi_e = (pre[k][-1] * f for k in ('K', 'L', 'B', 'S', 'Pi'))
    Pi_prev, loss_rate, delta, E_prev = Pi_e.copy(), np.zeros(N), P['d0'].copy(), None
    if struct['state'] is not None:
        Pi_prev = Pi_prev0
    a = np.ones(N)
    Pop = (0.9 * K / P['v']) / 0.92
    A = np.ones(N) if struct['A0'] is None else _vec(struct['A0'], N)
    fx = struct['fx']
    cur = np.zeros(N, dtype=int) if fx is None else np.asarray(fx['currency'], int)
    e = 1.0 if fx is None else fx.get('e0', 1.0)
    m_base = P['m'].copy()
    shift_base = {}                                   # 平価変更の起点の為替
    out = {k: np.empty((n, N)) for k in WORLD_KEYS}
    out['t'] = np.empty(n)
    shocks = [(sh[0], sh[1], sh[2] if len(sh) > 2 else 0.0, {}) for sh in struct['shocks']]
    for i in range(n):
        t = i * dt
        for ts, ch, dur, base in shocks:
            if ts - dt / 2 <= t <= ts + dur + dt / 2:
                if not base:
                    base.update({k: P[k].copy() for k in ch})
                w = 1.0 if dur <= 0 else min(1.0, (t - ts + dt / 2) / dur)
                for k, v in ch.items():
                    P[k] = base[k] + w * (_vec(v, N) - base[k])
                if 'omega' in ch:
                    omega = P['omega'].copy()
        if struct['phi_trade'] is not None:
            # 重力型: 支出は、売り手の生産能力 K_i と競争力 A_i^θ に比例して配られる
            Wt = (K * A ** P['theta_c'])[:, None] * np.where(np.eye(N, dtype=bool), 1.0, struct['phi_trade'])
            Sh = Wt / Wt.sum(axis=0, keepdims=True)          # Sh[i, j]: 地域 j の支出のうち i から買う割合
            P['m'] = 1 - np.diag(Sh)
            Tm = (Sh / np.maximum(P['m'], 1e-12)[None, :]).T
            np.fill_diagonal(Tm, 0.0)
        cv = np.where(cur == 1, e, 1.0)                   # 自国通貨 1 単位の、通貨 0 での価値
        Q = cv[None, :] / cv[:, None]                     # Q[i, j]: j の通貨を i の通貨に換算する率
        if fx is not None and struct['phi_trade'] is None:
            pf = (Tm * Q).sum(axis=1)                     # 地域 j から見た輸入品の相対価格(Q[j, i] = 売り手 i の通貨の j での価値)
            P['m'] = np.clip(m_base * pf ** (-fx.get('eta', 1.0)), 0.0, 0.95)
        Fc = F * Q.T                                      # Fc[j, i]: j の支払いを i の通貨で受け取る割合
        Y_k = K / P['v']
        Y_n = a * Pop
        Y_p = softmin(P['u_max'] * Y_k, Y_n, 0.01 * Y_n) if flags['labor_cap'] else P['u_max'] * Y_k
        r_L = (P['r_cb'] + P['spread']) / (1 - P['rho']) + P['spread_loss'] * np.minimum(loss_rate, 0.1)
        r_B = P['r_cb']
        wE = 0.001 * K                                    # なめらかさの幅は資本に比例させる(規模について同次に保つ)
        E = wE * np.logaddexp(0.0, Pi_e / wE) / (0.005 * np.logaddexp(0.0, (r_L + P['prem']) / 0.005) + 0.005)
        if E_prev is not None:
            stress = np.maximum(0.0, -(E - E_prev) / np.maximum(E_prev, 1e-9)) / dt
            delta = P['d0'] * (1 + P['kappa'] * stress)
        E_prev = E
        u_prev = out['u'][i - 1] if i > 0 else np.full(N, 0.9)
        g_net = P['g0'] + P['g1'] * Pi_prev / K + P['g2'] * (u_prev - 0.85) + P['g_q'] * (E / K - P['q_ref'])
        I_des = K * np.maximum(0.0, P['d0'] + g_net)
        retained = (1 - P['payout']) * Pi_prev + P['d0'] * K
        dL = softmin(I_des - retained, (P['lam'] * (E + K) - L) / P['T_adj'], 0.01 * K)
        I = np.maximum(0.0, dL + retained)
        dL = I - retained
        G = P['gG'] * Y_p / P['u_max']
        fu = struct['fiscal_union']
        in_union = fu is not None and fu[0] - dt / 2 <= t < fu[1] - dt / 2
        if i > 0:
            Yl = out['Y'][i - 1]
            ratio = np.full(N, B.sum() / Yl.sum()) if in_union else B / Yl
            tau = np.clip(P['tau'] + P['fiscal'] * (ratio - P['b_target']), 0.0, 0.8)
        else:
            tau = P['tau'].copy()
        ct = 1 - tau
        pi_sh = 1 - omega
        # 金利生活者 i の受け取り = Σ_j F[j, i]·(r_L,j L_j + r_B B_j + 配当_j) + r_B S_i
        flow_j0 = r_L * L + r_B * B + P['payout'] * (-P['d0'] * K - r_L * L)   # Y に依らない部分
        wealth = Fc.T @ (L + B) + S / cv
        a_vec = P['c_r'] * ct * (Fc.T @ flow_j0 + r_B * S / cv) + P['c_v'] * wealth + I + G
        Cm = np.diag(P['c_w'] * ct * omega) + np.diag(P['c_r'] * ct) @ Fc.T @ np.diag(P['payout'] * pi_sh)
        Z = np.diag(1 - P['m']) + Tm.T @ np.diag(P['m'])   # Z[i, j]: 地域 j の支出のうち i の生産になる割合
        Yd = np.linalg.solve(np.eye(N) - (Z * Q) @ Cm, (Z * Q) @ a_vec)
        # 生産能力の上限込みの釣り合い: Y = softmin(Z(C Y + a), Y_p) を反復で解く
        Y = np.maximum(softmin(Yd, Y_p, 0.01 * Y_p), 1e-9)
        for _ in range(200):
            Y_new = np.maximum(softmin((Z * Q) @ (Cm @ Y + a_vec), Y_p, 0.01 * Y_p), 1e-9)
            if np.max(np.abs(Y_new - Y) / Y) < 1e-12:
                Y = Y_new
                break
            Y = 0.5 * Y + 0.5 * Y_new
        Ydem = (Z * Q) @ (Cm @ Y + a_vec)                     # 実際の所得のもとでの需要
        rho_s = Y / Ydem                                  # 地域 i の財が行き渡る割合(上限に届くと 1 未満)
        Pi = pi_sh * Y - P['d0'] * K - r_L * L
        div = P['payout'] * Pi
        pay_j = r_L * L + r_B * B + div                  # 地域 j が払う利子・配当
        rent_in = Fc.T @ pay_j + r_B * S / cv
        W = omega * Y
        cons_des = P['c_w'] * ct * W + P['c_r'] * ct * rent_in + P['c_v'] * wealth
        D_des = cons_des + I + G
        purch = (Z * Q) * D_des[None, :] * rho_s[:, None]  # purch[i, j]: 地域 j が実際に i から買う額(i の通貨建て)
        Dv = (purch / Q).sum(axis=0)                      # 実際の支出(j の通貨建て)
        cons = cons_des - (D_des - Dv)                    # 買えなかった分は消費から引く(強制貯蓄)
        M = Dv - np.diag(purch)                           # 輸入(自国通貨建て)
        X = purch.sum(axis=1) - np.diag(purch)
        tax = tau * (W + rent_in)
        CA = X - M + (rent_in - pay_j)
        CF = pi_sh * Y - r_L * L
        default = np.minimum(P['default_share'] * np.maximum(0.0, -CF), 0.5 * L)
        loss_rate = default / np.maximum(L, 1e-6)
        dB = G + r_B * B - tax
        tr = np.zeros(N)                                 # 地域間の財政移転(受け取り)
        if in_union:
            dB_u = Y / Y.sum() * dB.sum()
            tr = dB - dB_u
            dB = dB_u
        CA = CA + tr
        # ポートフォリオ投資(新規の貸出・国債のうち、他地域の金利生活者が持つ分)
        new = dL + dB
        port_out = Fc.T @ new - new                       # 地域 i の金利生活者が新たに取得する他地域分 − 他地域に渡す自地域分
        dS = cv * (CA - port_out)                         # 決済残高・外貨準備は通貨 0 建て
        # 部門収支の恒等式: 家計・金利生活者の純貸出 + 企業の純貸出 + 政府の純貸出 = 経常収支
        hh_nl = (W + rent_in - tax) - cons
        firm_nl = (Pi - div) + P['d0'] * K - I
        sb_err = hh_nl + firm_nl - dB - CA            # 政府の純貸出 = 税 − G − 利払い + 移転 = −dB
        emp = (Y / a) / Pop
        rec = dict(Y=Y, Yd=Yd, D=Dv, K=K, L=L, B=B, S=S, E=E, Pi=Pi, X=X, M=M, CA=CA,
                   NFA=Fc.T @ (L + B) - (L + B) + S / cv, rent_in=rent_in, r_L=r_L, u=Y / Y_k,
                   g=(I - delta * K) / K, Phi=r_L * L / Y, theta_star=(pi_sh * Y - P['d0'] * K) / Y,
                   q=E / K, delta=delta, emp=emp, omega=omega, tax=tax, G=G, sb_err=sb_err, tau=tau,
                   pay=pay_j, I=I, Pi_e=Pi_e, A=A.copy(), m=P['m'].copy(), tr=tr, e=np.full(N, e), cv=cv)
        out['t'][i] = t
        for k, val in rec.items():
            out[k][i] = val
        if i == n - 1:
            out['final'] = dict(K=K, L=L, B=B, S=S, Pi_e=Pi_e, Pi_prev=Pi_prev)
        K = np.maximum(K + (I - delta * K) * dt, 1e-3)
        L = np.maximum(L + (dL - default) * dt, 0.0)
        B = B + dB * dt
        S = S + dS * dt
        Pi_e = Pi_e + (Pi - Pi_e) / P['tau_e'] * dt
        Pi_prev = Pi
        a = a * np.exp(P['a_growth'] * dt)
        gk = (I - delta * K) / K
        uk = Y / Y_k
        A = A * np.exp((P['verdoorn'] * (gk - np.average(gk, weights=Y))
                        - P['price_adj'] * (uk - np.average(uk, weights=Y)) - P['diffuse'] * np.log(A)) * dt)
        Pop = Pop * np.exp(P['pop_growth'] * dt)
        if fx is not None and fx.get('regime') == 'fixed' and fx.get('shifts'):
            for ts, e_new, dur in fx['shifts']:          # 平価の変更(切り下げ・切り上げ)を期間をかけて行う
                if ts - dt / 2 <= t + dt <= ts + dur + dt / 2:
                    e_old = shift_base.setdefault(ts, e)
                    w_ = min(1.0, (t + dt - ts + dt / 2) / max(dur, dt))
                    e = e_old * (e_new / e_old) ** w_
        if fx is not None and fx.get('regime', 'float') == 'float':
            one = cur == 1
            ca1 = CA[one].sum() / Y[one].sum()
            dr = np.mean(P['r_cb'][one]) - np.mean(P['r_cb'][~one])
            dq = np.average(E[one] / K[one]) - np.average(E[~one] / K[~one])   # 株式の収益見通しの差
            du = np.average(Y[one] / Y_k[one]) - np.average(Y[~one] / Y_k[~one])   # 稼働率の差(景気の差)
            e = e * np.exp((fx.get('k_ca', 0.5) * ca1 + fx.get('k_r', 1.0) * dr + fx.get('k_q', 0.0) * dq
                            + fx.get('k_u', 0.0) * du) * dt)
        if np.any(P['phillips'] > 0):
            omega = np.clip(omega * (1 + P['phillips'] * (emp - P['e_star']) * dt), 0.3, 0.95)
    return out


# %%CELL aggregate
def state_at(w, i):
    """i 期目の始めの状態(再開用)。"""
    st = {k: w[k][i].copy() for k in ('K', 'L', 'B', 'S', 'Pi_e')}
    st['Pi_prev'] = w['Pi'][i - 1].copy() if i > 0 else w['Pi_e'][0].copy()
    return st


def aggregate(w, i, blocks, params, trade, hold):
    """i 期目の流れを重みにして、地域を blocks(添字のリストのリスト)にまとめた粗いモデルのパラメータと状態を返す。

    線形の部分(消費・投資・貿易・利子の受け払い)は、その期について厳密に一致するように重みを選ぶ。
    """
    N = w['Y'].shape[1]
    P = {k: _vec(v, N) for k, v in {**WORLD_DEFAULT, **params}.items() if k not in ('T', 'dt', 'labor_cap')}
    Tm = (np.ones((N, N)) - np.eye(N)) / max(N - 1, 1) if trade is None else np.asarray(trade, float)
    F = np.eye(N) if hold is None else np.asarray(hold, float)
    nb = len(blocks)
    Y, K, L, B, S = (w[k][i] for k in ('Y', 'K', 'L', 'B', 'S'))
    rent, Pi, D, M = w['rent_in'][i], w['Pi'][i], w['D'][i], w['M'][i]
    W = w['omega'][i] * Y
    tb = W + rent                                             # 課税ベース
    wealth = F.T @ (L + B) + S
    Pp = w['Pi'][i - 1] if i > 0 else w['Pi_e'][0]
    def wavg(x, wt, bl):
        return np.sum(x[bl] * wt[bl]) / np.sum(wt[bl])
    agg = {k: np.zeros(nb) for k in ('omega', 'tau', 'c_w', 'c_r', 'c_v', 'v', 'd0', 'g0', 'g1', 'payout', 'm', 'gG')}
    for b, bl in enumerate(blocks):
        agg['omega'][b] = W[bl].sum() / Y[bl].sum()
        agg['tau'][b] = wavg(P['tau'], tb, bl)
        ctA = 1 - agg['tau'][b]
        agg['c_w'][b] = np.sum(P['c_w'][bl] * (1 - P['tau'][bl]) * W[bl]) / (ctA * W[bl].sum())
        agg['c_r'][b] = np.sum(P['c_r'][bl] * (1 - P['tau'][bl]) * rent[bl]) / (ctA * rent[bl].sum())
        agg['c_v'][b] = wavg(P['c_v'], wealth, bl)
        agg['v'][b] = K[bl].sum() / np.sum(K[bl] / P['v'][bl])
        agg['d0'][b] = wavg(P['d0'], K, bl)
        agg['g0'][b] = wavg(P['g0'], K, bl)
        agg['g1'][b] = wavg(P['g1'], np.abs(Pp), bl)
        agg['payout'][b] = wavg(P['payout'], np.abs(Pi), bl)
        agg['gG'][b] = wavg(P['gG'], K / P['v'], bl)
        outside = [j for j in range(N) if j not in bl]
        imp_out = np.sum(M[bl][:, None] * Tm[np.ix_(bl, outside)]) if outside else 0.0
        agg['m'][b] = imp_out / D[bl].sum()
    # ブロック間の貿易行列と保有行列
    TA, FA = np.zeros((nb, nb)), np.zeros((nb, nb))
    cl = L + B
    for J, blJ in enumerate(blocks):
        for I_, blI in enumerate(blocks):
            if I_ != J:
                TA[J, I_] = np.sum(M[blJ][:, None] * Tm[np.ix_(blJ, blI)])
            FA[J, I_] = np.sum(cl[blJ][:, None] * F[np.ix_(blJ, blI)]) / cl[blJ].sum()
        if TA[J].sum() > 0:
            TA[J] /= TA[J].sum()
    st = state_at(w, i)
    stA = {k: np.array([st[k][bl].sum() for bl in blocks]) for k in st}
    pA = {k: v for k, v in params.items() if k not in agg}
    pA.update({k: (v if nb > 1 else float(v[0])) for k, v in agg.items()})
    return pA, TA, FA, stA


# %%CELL helpers
def neutral_links(sizes, k=0.3):
    """大きさに中立なつながり: 輸入性向・貿易の相手・金融資産の保有を、相手の大きさに比例させる。

    地域 i の支出のうち k(1 − s_i) を輸入し、輸入の相手は大きさに比例して選ぶ。
    地域 j の企業・政府への請求権のうち、他地域 i の金利生活者が k·s_i を持つ。
    """
    s = np.asarray(sizes, float) / np.sum(sizes)
    N = len(s)
    m = k * (1 - s)
    trade = np.array([[0.0 if i == j else s[j] / (1 - s[i]) for j in range(N)] for i in range(N)])
    hold = np.array([[1 - k * (1 - s[j]) if i == j else k * s[i] for i in range(N)] for j in range(N)])
    return dict(m=m, trade=trade, hold=hold)
