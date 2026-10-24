// 信用創造ダイナミクス v6 の世界版(多地域)。
// python/world.py の simulate_world を、計算の順序もそのままに JavaScript に移したもの。
// ブラウザでは window.CreditV6.simulateWorld、Node では module.exports から使う。
(function (root) {
  'use strict';

  const WORLD_DEFAULT = {
    T: 150.0, dt: 0.1,
    v: 2.5, u_max: 1.1, omega: 0.65, d0: 0.05, kappa: 3.0,
    c_w: 0.95, c_r: 0.35, c_v: 0.02, payout: 0.6, tau: 0.25,
    gG: 0.20, fiscal: 0.0, b_target: 0.6,
    r_cb: 0.03, spread: 0.01, spread_loss: 2.0, rho: 0.05,
    g0: -0.02, g1: 0.75, g2: 0.0, g_q: 0.0, q_ref: 0.9,
    prem: 0.02, lam: 0.6, T_adj: 2.0, default_share: 0.5, tau_e: 2.0,
    m: 0.0,
    a_growth: 0.015, pop_growth: 0.005,
    labor_cap: false, phillips: 0.0, e_star: 0.90,
    theta_c: 5.0, verdoorn: 0.0, price_adj: 0.0, diffuse: 0.05,
  };
  const WORLD_STRUCT = { trade: null, hold: null, K0: null, init: 'steady', state: null, phi_trade: null,
    A0: null, fx: null, fiscal_union: null, shocks: [] };
  const WORLD_KEYS = ['Y', 'Yd', 'D', 'K', 'L', 'B', 'S', 'E', 'Pi', 'X', 'M', 'CA', 'NFA', 'rent_in', 'r_L', 'u',
    'g', 'Phi', 'theta_star', 'q', 'delta', 'emp', 'omega', 'tax', 'G', 'sb_err', 'pay', 'I', 'Pi_e', 'A', 'm',
    'tr', 'tau', 'e', 'cv'];

  function logaddexp(a, b) {
    const m = Math.max(a, b);
    if (m === -Infinity) return -Infinity;
    return m + Math.log1p(Math.exp(-Math.abs(a - b)));
  }
  function softmin(a, b, w) { return -w * logaddexp(-a / w, -b / w); }

  const vec = (x, N) => (typeof x === 'number') ? new Array(N).fill(x) : Array.from(x);
  const map = (n, f) => Array.from({ length: n }, (_, i) => f(i));
  const sum = a => a.reduce((s, x) => s + x, 0);
  // y = A x(A[i][j])
  const matvec = (A, x) => A.map(row => row.reduce((s, a, j) => s + a * x[j], 0));
  // y = Aᵀ x
  const tmatvec = (A, x) => map(A[0].length, j => A.reduce((s, row, i) => s + row[j] * x[i], 0));
  const matmul = (A, B) => A.map(row => map(B[0].length, j => row.reduce((s, a, k) => s + a * B[k][j], 0)));
  function solve(A, b) {   // 部分ピボット選択つきガウスの消去法
    const n = b.length, M = A.map((r, i) => r.concat([b[i]]));
    for (let c = 0; c < n; c++) {
      let piv = c;
      for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[piv][c])) piv = r;
      [M[c], M[piv]] = [M[piv], M[c]];
      for (let r = c + 1; r < n; r++) {
        const f = M[r][c] / M[c][c];
        for (let k = c; k <= n; k++) M[r][k] -= f * M[c][k];
      }
    }
    const x = new Array(n).fill(0);
    for (let r = n - 1; r >= 0; r--) {
      let s = M[r][n];
      for (let k = r + 1; k < n; k++) s -= M[r][k] * x[k];
      x[r] = s / M[r][r];
    }
    return x;
  }

  function simulateWorld(N, kw) {
    kw = Object.assign({}, kw || {});
    const struct = {};
    for (const k in WORLD_STRUCT) { struct[k] = (k in kw) ? kw[k] : WORLD_STRUCT[k]; delete kw[k]; }
    const p = Object.assign({}, WORLD_DEFAULT, kw);
    const P = {};
    for (const k in p) if (!['T', 'dt', 'labor_cap'].includes(k)) P[k] = vec(p[k], N);
    const dt = p.dt, n = Math.round(p.T / dt);
    let Tm = struct.trade ? struct.trade.map(r => Array.from(r))
      : map(N, i => map(N, j => i === j ? 0 : 1 / Math.max(N - 1, 1)));
    const F = struct.hold ? struct.hold.map(r => Array.from(r)) : map(N, i => map(N, j => i === j ? 1 : 0));
    let K = struct.K0 ? vec(struct.K0, N) : vec(250.0 / N, N);
    let L = K.map(k => 60.0 / 250.0 * k), B = K.map(k => 60.0 / 250.0 * k), S = new Array(N).fill(0);
    let omega = Array.from(P.omega);
    let Pi_e = map(N, i => (1 - omega[i]) * K[i] / P.v[i] * 0.9 - P.d0[i] * K[i]
      - (P.r_cb[i] + P.spread[i]) / (1 - P.rho[i]) * L[i]);
    let Pi_prev0 = null;
    if (struct.state) {
      const st = struct.state;
      K = vec(st.K, N); L = vec(st.L, N); B = vec(st.B, N); S = vec(st.S, N); Pi_e = vec(st.Pi_e, N);
      Pi_prev0 = vec(st.Pi_prev !== undefined ? st.Pi_prev : st.Pi_e, N);
    } else if (struct.init === 'steady') {
      const fx0 = struct.fx ? Object.fromEntries(Object.entries(struct.fx).filter(([k]) => k !== 'shifts')) : null;
      const pre = simulateWorld(N, Object.assign({}, kw, { kappa: 0.0, T: 300.0, phillips: 0.0,
        trade: struct.trade, hold: struct.hold, K0: K, init: null, state: null, shocks: [],
        phi_trade: struct.phi_trade, A0: struct.A0, fiscal_union: null, fx: fx0 }));
      const last = pre.K.length - 1, f = sum(K) / sum(pre.K[last]);
      K = pre.K[last].map(x => x * f); L = pre.L[last].map(x => x * f); B = pre.B[last].map(x => x * f);
      S = pre.S[last].map(x => x * f); Pi_e = pre.Pi[last].map(x => x * f);
    }
    let Pi_prev = Pi_prev0 ? Pi_prev0 : Array.from(Pi_e);
    let loss_rate = new Array(N).fill(0), delta = Array.from(P.d0), E_prev = null;
    let a = new Array(N).fill(1), Pop = K.map((k, i) => (0.9 * k / P.v[i]) / 0.92);
    let A = struct.A0 ? vec(struct.A0, N) : new Array(N).fill(1);
    const fx = struct.fx;
    const cur = fx ? Array.from(fx.currency) : new Array(N).fill(0);
    let e = fx ? (fx.e0 !== undefined ? fx.e0 : 1.0) : 1.0;
    const m_base = Array.from(P.m), shift_base = {};
    const out = { t: [] };
    for (const k of WORLD_KEYS) out[k] = [];
    const shocks = (struct.shocks || []).map(sh => ({ ts: sh[0], ch: sh[1], dur: sh.length > 2 ? sh[2] : 0.0, base: null }));
    for (let i = 0; i < n; i++) {
      const t = i * dt;
      for (const sh of shocks) {
        if (sh.ts - dt / 2 <= t && t <= sh.ts + sh.dur + dt / 2) {
          if (!sh.base) { sh.base = {}; for (const k in sh.ch) sh.base[k] = Array.from(P[k]); }
          const w = sh.dur <= 0 ? 1.0 : Math.min(1.0, (t - sh.ts + dt / 2) / sh.dur);
          for (const k in sh.ch) { const v = vec(sh.ch[k], N); P[k] = map(N, j => sh.base[k][j] + w * (v[j] - sh.base[k][j])); }
          if ('omega' in sh.ch) omega = Array.from(P.omega);
        }
      }
      if (struct.phi_trade !== null) {
        const Wt = map(N, r => map(N, c => K[r] * Math.pow(A[r], P.theta_c[r]) * (r === c ? 1.0 : struct.phi_trade)));
        const colsum = map(N, c => Wt.reduce((s, row) => s + row[c], 0));
        const Sh = map(N, r => map(N, c => Wt[r][c] / colsum[c]));
        P.m = map(N, j => 1 - Sh[j][j]);
        Tm = map(N, j => map(N, r => j === r ? 0 : Sh[r][j] / Math.max(P.m[j], 1e-12)));
      }
      const cv = cur.map(c => c === 1 ? e : 1.0);
      const Q = map(N, r => map(N, c => cv[c] / cv[r]));
      if (fx && struct.phi_trade === null) {
        const pf = map(N, j => Tm[j].reduce((s, tji, r) => s + tji * Q[j][r], 0));
        P.m = map(N, j => Math.min(Math.max(m_base[j] * Math.pow(pf[j], -(fx.eta !== undefined ? fx.eta : 1.0)), 0.0), 0.95));
      }
      const Fc = map(N, j => map(N, r => F[j][r] * Q[r][j]));
      const Y_k = map(N, j => K[j] / P.v[j]);
      const Y_n = map(N, j => a[j] * Pop[j]);
      const Y_p = p.labor_cap ? map(N, j => softmin(P.u_max[j] * Y_k[j], Y_n[j], 0.01 * Y_n[j])) : map(N, j => P.u_max[j] * Y_k[j]);
      const r_L = map(N, j => (P.r_cb[j] + P.spread[j]) / (1 - P.rho[j]) + P.spread_loss[j] * Math.min(loss_rate[j], 0.1));
      const r_B = P.r_cb;
      const E = map(N, j => { const wE = 0.001 * K[j];
        return wE * logaddexp(0.0, Pi_e[j] / wE) / (0.005 * logaddexp(0.0, (r_L[j] + P.prem[j]) / 0.005) + 0.005); });
      if (E_prev !== null) delta = map(N, j => P.d0[j] * (1 + P.kappa[j] * (Math.max(0.0, -(E[j] - E_prev[j]) / Math.max(E_prev[j], 1e-9)) / dt)));
      E_prev = E;
      const u_prev = i > 0 ? out.u[i - 1] : new Array(N).fill(0.9);
      const I = new Array(N), dL = new Array(N), retained = new Array(N);
      for (let j = 0; j < N; j++) {
        const g_net = P.g0[j] + P.g1[j] * Pi_prev[j] / K[j] + P.g2[j] * (u_prev[j] - 0.85) + P.g_q[j] * (E[j] / K[j] - P.q_ref[j]);
        const I_des = K[j] * Math.max(0.0, P.d0[j] + g_net);
        retained[j] = (1 - P.payout[j]) * Pi_prev[j] + P.d0[j] * K[j];
        const dl = softmin(I_des - retained[j], (P.lam[j] * (E[j] + K[j]) - L[j]) / P.T_adj[j], 0.01 * K[j]);
        I[j] = Math.max(0.0, dl + retained[j]);
        dL[j] = I[j] - retained[j];
      }
      const G = map(N, j => P.gG[j] * Y_p[j] / P.u_max[j]);
      const fu = struct.fiscal_union;
      const in_union = !!fu && fu[0] - dt / 2 <= t && t < fu[1] - dt / 2;
      let tau;
      if (i > 0) {
        const Yl = out.Y[i - 1];
        const ratio = in_union ? new Array(N).fill(sum(B) / sum(Yl)) : map(N, j => B[j] / Yl[j]);
        tau = map(N, j => Math.min(Math.max(P.tau[j] + P.fiscal[j] * (ratio[j] - P.b_target[j]), 0.0), 0.8));
      } else tau = Array.from(P.tau);
      const ct = tau.map(x => 1 - x);
      const pi_sh = omega.map(x => 1 - x);
      const flow_j0 = map(N, j => r_L[j] * L[j] + r_B[j] * B[j] + P.payout[j] * (-P.d0[j] * K[j] - r_L[j] * L[j]));
      const LB = map(N, j => L[j] + B[j]);
      const wealth = map(N, j => tmatvec(Fc, LB)[j] + S[j] / cv[j]);
      const Fflow = tmatvec(Fc, flow_j0);
      const a_vec = map(N, j => P.c_r[j] * ct[j] * (Fflow[j] + r_B[j] * S[j] / cv[j]) + P.c_v[j] * wealth[j] + I[j] + G[j]);
      // Cm = diag(c_w ct ω) + diag(c_r ct) Fcᵀ diag(payout π)
      const Cm = map(N, r => map(N, c => (r === c ? P.c_w[r] * ct[r] * omega[r] : 0) + P.c_r[r] * ct[r] * Fc[c][r] * P.payout[c] * pi_sh[c]));
      const Z = map(N, r => map(N, c => (r === c ? 1 - P.m[c] : 0) + Tm[c][r] * P.m[c]));
      const ZQ = map(N, r => map(N, c => Z[r][c] * Q[r][c]));
      const ZQC = matmul(ZQ, Cm);
      const Yd = solve(map(N, r => map(N, c => (r === c ? 1 : 0) - ZQC[r][c])), matvec(ZQ, a_vec));
      let Y = map(N, j => Math.max(softmin(Yd[j], Y_p[j], 0.01 * Y_p[j]), 1e-9));
      for (let it = 0; it < 200; it++) {
        const dem = matvec(ZQ, map(N, j => matvec(Cm, Y)[j] + a_vec[j]));
        const Y_new = map(N, j => Math.max(softmin(dem[j], Y_p[j], 0.01 * Y_p[j]), 1e-9));
        let mx = 0; for (let j = 0; j < N; j++) mx = Math.max(mx, Math.abs(Y_new[j] - Y[j]) / Y[j]);
        if (mx < 1e-12) { Y = Y_new; break; }
        Y = map(N, j => 0.5 * Y[j] + 0.5 * Y_new[j]);
      }
      const CY = matvec(Cm, Y);
      const Ydem = matvec(ZQ, map(N, j => CY[j] + a_vec[j]));
      const rho_s = map(N, j => Y[j] / Ydem[j]);
      const Pi = map(N, j => pi_sh[j] * Y[j] - P.d0[j] * K[j] - r_L[j] * L[j]);
      const div = map(N, j => P.payout[j] * Pi[j]);
      const pay_j = map(N, j => r_L[j] * L[j] + r_B[j] * B[j] + div[j]);
      const Fpay = tmatvec(Fc, pay_j);
      const rent_in = map(N, j => Fpay[j] + r_B[j] * S[j] / cv[j]);
      const W = map(N, j => omega[j] * Y[j]);
      const cons_des = map(N, j => P.c_w[j] * ct[j] * W[j] + P.c_r[j] * ct[j] * rent_in[j] + P.c_v[j] * wealth[j]);
      const D_des = map(N, j => cons_des[j] + I[j] + G[j]);
      const purch = map(N, r => map(N, c => ZQ[r][c] * D_des[c] * rho_s[r]));
      const Dv = map(N, c => purch.reduce((s, row, r) => s + row[c] / Q[r][c], 0));
      const cons = map(N, j => cons_des[j] - (D_des[j] - Dv[j]));
      const M = map(N, j => Dv[j] - purch[j][j]);
      const X = map(N, j => sum(purch[j]) - purch[j][j]);
      const tax = map(N, j => tau[j] * (W[j] + rent_in[j]));
      let CA = map(N, j => X[j] - M[j] + (rent_in[j] - pay_j[j]));
      const CF = map(N, j => pi_sh[j] * Y[j] - r_L[j] * L[j]);
      const deflt = map(N, j => Math.min(P.default_share[j] * Math.max(0.0, -CF[j]), 0.5 * L[j]));
      loss_rate = map(N, j => deflt[j] / Math.max(L[j], 1e-6));
      let dB = map(N, j => G[j] + r_B[j] * B[j] - tax[j]);
      let tr = new Array(N).fill(0);
      if (in_union) {
        const tot = sum(dB), Ys = sum(Y);
        const dB_u = map(N, j => Y[j] / Ys * tot);
        tr = map(N, j => dB[j] - dB_u[j]); dB = dB_u;
      }
      CA = map(N, j => CA[j] + tr[j]);
      const nw = map(N, j => dL[j] + dB[j]);
      const Fnew = tmatvec(Fc, nw);
      const port_out = map(N, j => Fnew[j] - nw[j]);
      const dS = map(N, j => cv[j] * (CA[j] - port_out[j]));
      const sb_err = map(N, j => ((W[j] + rent_in[j] - tax[j]) - cons[j]) + ((Pi[j] - div[j]) + P.d0[j] * K[j] - I[j]) - dB[j] - CA[j]);
      const emp = map(N, j => (Y[j] / a[j]) / Pop[j]);
      const FLB = tmatvec(Fc, LB);
      const rec = { Y, Yd, D: Dv, K: Array.from(K), L: Array.from(L), B: Array.from(B), S: Array.from(S), E, Pi, X, M, CA,
        NFA: map(N, j => FLB[j] - LB[j] + S[j] / cv[j]), rent_in, r_L, u: map(N, j => Y[j] / Y_k[j]),
        g: map(N, j => (I[j] - delta[j] * K[j]) / K[j]), Phi: map(N, j => r_L[j] * L[j] / Y[j]),
        theta_star: map(N, j => (pi_sh[j] * Y[j] - P.d0[j] * K[j]) / Y[j]), q: map(N, j => E[j] / K[j]),
        delta: Array.from(delta), emp, omega: Array.from(omega), tax, G, sb_err, tau, pay: pay_j, I, Pi_e: Array.from(Pi_e),
        A: Array.from(A), m: Array.from(P.m), tr, e: new Array(N).fill(e), cv };
      out.t.push(t);
      for (const k of WORLD_KEYS) out[k].push(rec[k]);
      if (i === n - 1) out.final = { K: Array.from(K), L: Array.from(L), B: Array.from(B), S: Array.from(S), Pi_e: Array.from(Pi_e), Pi_prev: Array.from(Pi_prev) };
      K = map(N, j => Math.max(K[j] + (I[j] - delta[j] * K[j]) * dt, 1e-3));
      L = map(N, j => Math.max(L[j] + (dL[j] - deflt[j]) * dt, 0.0));
      B = map(N, j => B[j] + dB[j] * dt);
      S = map(N, j => S[j] + dS[j] * dt);
      Pi_e = map(N, j => Pi_e[j] + (Pi[j] - Pi_e[j]) / P.tau_e[j] * dt);
      Pi_prev = Pi;
      a = map(N, j => a[j] * Math.exp(P.a_growth[j] * dt));
      const gk = map(N, j => (I[j] - delta[j] * K[j]) / K[j]);
      const uk = map(N, j => Y[j] / Y_k[j]);
      const Ys = sum(Y);
      const gbar = sum(map(N, j => gk[j] * Y[j])) / Ys, ubar = sum(map(N, j => uk[j] * Y[j])) / Ys;
      A = map(N, j => A[j] * Math.exp((P.verdoorn[j] * (gk[j] - gbar) - P.price_adj[j] * (uk[j] - ubar) - P.diffuse[j] * Math.log(A[j])) * dt));
      Pop = map(N, j => Pop[j] * Math.exp(P.pop_growth[j] * dt));
      if (fx && fx.regime === 'fixed' && fx.shifts) {
        for (const [ts, e_new, dur] of fx.shifts) {
          if (ts - dt / 2 <= t + dt && t + dt <= ts + dur + dt / 2) {
            if (!(ts in shift_base)) shift_base[ts] = e;
            const e_old = shift_base[ts];
            const w_ = Math.min(1.0, (t + dt - ts + dt / 2) / Math.max(dur, dt));
            e = e_old * Math.pow(e_new / e_old, w_);
          }
        }
      }
      if (fx && (fx.regime === undefined || fx.regime === 'float')) {
        const one = cur.map(c => c === 1);
        const pick = (arr, want) => arr.filter((_, j) => one[j] === want);
        const ca1 = sum(pick(CA, true)) / sum(pick(Y, true));
        const mean = arr => sum(arr) / arr.length;
        const dr = mean(pick(P.r_cb, true)) - mean(pick(P.r_cb, false));
        const qv = map(N, j => E[j] / K[j]), uv = map(N, j => Y[j] / Y_k[j]);
        const dq = mean(pick(qv, true)) - mean(pick(qv, false));
        const du = mean(pick(uv, true)) - mean(pick(uv, false));
        const g = k => (fx[k] !== undefined ? fx[k] : { k_ca: 0.5, k_r: 1.0, k_q: 0.0, k_u: 0.0 }[k]);
        e = e * Math.exp((g('k_ca') * ca1 + g('k_r') * dr + g('k_q') * dq + g('k_u') * du) * dt);
      }
      if (P.phillips.some(x => x > 0)) omega = map(N, j => Math.min(Math.max(omega[j] * (1 + P.phillips[j] * (emp[j] - P.e_star[j]) * dt), 0.3), 0.95));
    }
    return out;
  }

  // 大きさに中立なつながり(python/world.py の neutral_links と同じ)
  function neutralLinks(sizes, k) {
    k = (k === undefined) ? 0.3 : k;
    const tot = sum(sizes), s = sizes.map(x => x / tot), N = s.length;
    return {
      m: s.map(x => k * (1 - x)),
      trade: map(N, i => map(N, j => i === j ? 0 : s[j] / (1 - s[i]))),
      hold: map(N, j => map(N, i => i === j ? 1 - k * (1 - s[j]) : k * s[i])),
    };
  }

  const api = { WORLD_DEFAULT, WORLD_KEYS, simulateWorld, neutralLinks };
  if (typeof module !== 'undefined' && module.exports) module.exports = api;
  else root.CreditV6 = Object.assign(root.CreditV6 || {}, api);
})(typeof window !== 'undefined' ? window : this);
