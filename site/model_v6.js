// 信用創造ダイナミクス v6(信用循環モデル)の一地域版。
// python/sims.py の simulate_cm を、計算の順序もそのままに JavaScript に移したもの。
// ブラウザでは window.CreditV6、Node では module.exports から使う。
(function (root) {
  'use strict';

  const CM_DEFAULT = {
    T: 150.0, dt: 0.1,
    v: 2.5,          // 資本係数: 生産能力 Y_p = K/v
    u_max: 1.1,      // 資本稼働率の上限
    omega: 0.65,     // 賃金分配率
    d0: 0.05,        // 平時の損耗率
    kappa: 3.0,      // 株式的富が縮むときの損耗増幅(在庫維持能力の喪失)
    c_w: 0.95,       // 労働者の消費性向
    c_r: 0.35,       // 金利生活者の所得からの消費性向
    c_v: 0.02,       // 金利生活者の金融資産からの消費性向
    payout: 0.6,     // 配当性向
    tau: 0.25,       // 税率
    foreign: 0.0,    // 利子・配当のうち国外に渡る割合
    gG: 0.20,        // 政府支出 G = gG·Y_p
    fiscal: 0.0,     // 財政ルールの強さ
    b_target: 0.6,
    r_cb: 0.03,      // 政策金利(= 国債金利)
    spread: 0.01,    // 貸出スプレッド
    spread_loss: 2.0,
    rho: 0.05,       // 法定準備率
    regime: 'rate',  // 'rate' または 'quantity'
    gH: 0.025,       // 量的制度でのベースマネーの伸び率
    cu0: 0.05,       // 平時の現金/預金比(タンス預金)
    cu_loss: 8.0,
    g0: -0.02, g1: 0.75, g2: 0.0,
    prem: 0.02,      // 株式のリスクプレミアム
    g_exp: 0.0, tau_g: 3.0,
    g_q: 0.0, q_ref: 0.9,
    lam: 0.6,        // 担保制約
    T_adj: 2.0,
    default_share: 0.5,
    tau_e: 2.0,
    a_growth: 0.015, pop_growth: 0.005,
    labor_cap: false, phillips: 0.0, e_star: 0.90,
    K0: 250.0, L0: 60.0, B0: 60.0, emp0: 0.92,
    init: 'steady',
    shocks: [],      // [[t, {param: value}, 期間], ...]
  };

  const CM_KEYS = ['t', 'Y', 'Yd', 'K', 'L', 'B', 'E', 'Pi', 'Phi', 'theta_star', 'u', 'I', 'cons_w', 'cons_r',
    'G', 'tax', 'r_L', 'cu', 'rho_eff', 's_agg', 'loss_rate', 'emp', 'omega', 'delta', 'minsky',
    'credit_cap', 'tau', 'rent_share', 'g', 'B_Y', 'L_Y', 'g_e', 'q'];

  // numpy の logaddexp と同じ(あふれない形)
  function logaddexp(a, b) {
    const m = Math.max(a, b);
    if (m === -Infinity) return -Infinity;
    return m + Math.log1p(Math.exp(-Math.abs(a - b)));
  }
  function softmin(a, b, w) { return -w * logaddexp(-a / w, -b / w); }

  function simulateCM(kw) {
    kw = kw || {};
    const p = Object.assign({}, CM_DEFAULT, kw);
    const dt = p.dt;
    const n = Math.round(p.T / dt);
    let K = p.K0, L = p.L0, B = p.B0;
    let omega = p.omega;
    const r_L0 = (p.r_cb + p.spread) / (1 - p.rho);
    let Pi_e = (1 - omega) * K / p.v * 0.9 - p.d0 * K - r_L0 * L;
    let pre = null;
    if (p.init === 'steady') {
      pre = simulateCM(Object.assign({}, kw, { init: null, kappa: 0.0, shocks: [], T: 300.0,
        regime: 'rate', phillips: 0.0 }));
      const last = pre.K.length - 1;
      const f = K / pre.K[last];
      L = pre.L[last] * f; B = pre.B[last] * f; Pi_e = pre.Pi[last] * f;
    }
    let Pi_prev = Pi_e, loss_rate = 0.0, delta = p.d0, E_prev = null;
    let g_e = (p.init === 'steady') ? pre.g[pre.g.length - 1] : 0.0;
    let a = 1.0, Pop = (0.9 * K / p.v) / p.emp0;
    let H = (L + B) * (p.rho + p.cu0) / (1 - p.rho);
    const out = {};
    for (const k of CM_KEYS) out[k] = new Float64Array(n);
    const shocks = (p.shocks || []).map(sh => ({ ts: sh[0], ch: sh[1], dur: sh.length > 2 ? sh[2] : 0.0, base: null }));
    for (let i = 0; i < n; i++) {
      const t = i * dt;
      for (const sh of shocks) {
        if (t >= sh.ts - dt / 2 && t <= sh.ts + sh.dur + dt / 2) {
          if (!sh.base) { sh.base = {}; for (const k in sh.ch) sh.base[k] = p[k]; }
          const w = sh.dur <= 0 ? 1.0 : Math.min(1.0, (t - sh.ts + dt / 2) / sh.dur);
          for (const k in sh.ch) {
            const v = sh.ch[k];
            p[k] = (typeof v === 'number') ? sh.base[k] + w * (v - sh.base[k]) : v;
          }
          if ('omega' in sh.ch) omega = p.omega;
        }
      }
      const Y_k = K / p.v;
      const Y_n = a * Pop;
      const Y_p = p.labor_cap ? softmin(p.u_max * Y_k, Y_n, 0.01 * Y_n) : p.u_max * Y_k;
      const r_L = (p.r_cb + p.spread) / (1 - p.rho) + p.spread_loss * Math.min(loss_rate, 0.1);
      const r_B = p.r_cb;
      const disc = r_L + p.prem - p.g_exp * g_e;
      const wE = 0.001 * K;
      const E = wE * logaddexp(0.0, Pi_e / wE) / (0.005 * logaddexp(0.0, disc / 0.005) + 0.005);
      if (E_prev !== null) {
        const stress = Math.max(0.0, -(E - E_prev) / Math.max(E_prev, 1e-9)) / dt;
        delta = p.d0 * (1 + p.kappa * stress);
      }
      E_prev = E;
      const u_prev = i > 0 ? out.u[i - 1] : 0.9;
      const g_net = p.g0 + p.g1 * Pi_prev / K + p.g2 * (u_prev - 0.85) + p.g_q * (E / K - p.q_ref);
      const I_des = K * Math.max(0.0, p.d0 + g_net);
      const retained = (1 - p.payout) * Pi_prev + p.d0 * K;
      const dL_des = I_des - retained;
      const dL_col = (p.lam * (E + K) - L) / p.T_adj;
      const cu = p.cu0 + p.cu_loss * loss_rate;
      const credit_cap = (1 - p.rho) * H / (p.rho + cu);
      const wS = 0.01 * K;
      let dL = softmin(dL_des, dL_col, wS);
      if (p.regime === 'quantity') dL = softmin(dL, (credit_cap - L - B) / p.T_adj, wS);
      const I = Math.max(0.0, dL + retained);
      dL = I - retained;
      const G = p.gG * Y_p / p.u_max;
      const Yl = i > 0 ? out.Y[i - 1] : 0.9 * Y_p;
      const tau = Math.min(Math.max(p.tau + p.fiscal * (B / Yl - p.b_target), 0.0), 0.8);
      const pi_sh = 1 - omega;
      const ct = 1 - tau;
      const dom = 1 - p.foreign;
      const auto = p.c_r * ct * dom * (r_L * L + r_B * B + p.payout * (-p.d0 * K - r_L * L))
        + p.c_v * dom * (L + B) + I + G;
      const mult = 1 - p.c_w * ct * omega - p.c_r * ct * dom * p.payout * pi_sh;
      const Yd = auto / mult;
      let Y = Math.max(softmin(Yd, Y_p, 0.01 * Y_p), 1e-9);
      for (let it = 0; it < 200; it++) {
        const Y_new = Math.max(softmin(auto + (1 - mult) * Y, Y_p, 0.01 * Y_p), 1e-9);
        if (Math.abs(Y_new - Y) < 1e-12 * Y) { Y = Y_new; break; }
        Y = 0.5 * Y + 0.5 * Y_new;
      }
      const gap = auto + (1 - mult) * Y - Y;
      const Pi = pi_sh * Y - p.d0 * K - r_L * L;
      const div = p.payout * Pi;
      const W = omega * Y;
      const rent_inc = r_L * L + r_B * B + div;
      let cons_w = p.c_w * ct * W;
      let cons_r = p.c_r * ct * dom * rent_inc + p.c_v * dom * (L + B);
      if (gap > 0) {
        const f_c = 1 - gap / (cons_w + cons_r);
        cons_w *= f_c; cons_r *= f_c;
      }
      const tax = tau * (W + dom * rent_inc);
      const CF = pi_sh * Y - r_L * L;
      const deflt = Math.min(p.default_share * Math.max(0.0, -CF), 0.5 * L);
      loss_rate = deflt / Math.max(L, 1e-6);
      const op_cf = pi_sh * Y - p.d0 * K;
      const emp = (Y / a) / Pop;
      const rec = {
        t, Y, Yd, K, L, B, E, Pi, Phi: r_L * L / Y, theta_star: op_cf / Y, u: Y / Y_k, I, cons_w, cons_r, G, tax,
        r_L, cu, rho_eff: p.rho + cu, s_agg: 1 - (cons_w + cons_r) / Math.max(W + rent_inc - tax, 1e-9),
        loss_rate, emp, omega, delta,
        minsky: op_cf >= r_L * L + L / 10 ? 2 : (op_cf >= r_L * L ? 1 : 0),
        credit_cap, tau, rent_share: rent_inc / Y, g: (I - delta * K) / K, B_Y: B / Y, L_Y: L / Y, g_e, q: E / K,
      };
      for (const k of CM_KEYS) out[k][i] = rec[k];
      K = Math.max(K + (I - delta * K) * dt, 1e-3);
      L = Math.max(L + (dL - deflt) * dt, 0.0);
      B = B + (G + r_B * B - tax) * dt;
      Pi_e += (Pi - Pi_e) / p.tau_e * dt;
      Pi_prev = Pi;
      g_e += ((I - delta * K) / K - g_e) / p.tau_g * dt;
      H *= Math.exp(p.gH * dt);
      a *= Math.exp(p.a_growth * dt);
      Pop *= Math.exp(p.pop_growth * dt);
      if (p.phillips > 0) omega = Math.min(Math.max(omega * (1 + p.phillips * (emp - p.e_star) * dt), 0.3), 0.95);
    }
    return out;
  }

  const api = { CM_DEFAULT, CM_KEYS, simulateCM, softmin, logaddexp };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.CreditV6 = Object.assign(root.CreditV6 || {}, api);
})(typeof window !== 'undefined' ? window : this);
