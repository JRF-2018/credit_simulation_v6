# site/ の JavaScript のモデルが、Python の参照実装(IPYNB と同じもの)と同じ数値を出すことを確かめる。
# JavaScript は quickjs(Python から使える小さな JS エンジン)で動かす。
#   python python/check_js_vs_py.py
import json
import os
import sys

import numpy as np
import quickjs

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from sims import simulate_cm  # noqa: E402
from world import simulate_world, neutral_links  # noqa: E402

TOL = 1e-9   # 相対誤差の許容(浮動小数点の演算順序の違いだけを許す)

# 一地域版のシナリオ(ショックの値は float で書く。Python 版は float のときだけ線形に補間するため)
SCENARIOS_CM = {
    'baseline': {},
    'rate hike 3%->6%': dict(shocks=[[20.0, dict(r_cb=0.06), 1.0]]),
    'reserve ratio 5%->20%': dict(shocks=[[20.0, dict(rho=0.2), 1.0]]),
    'quantity regime, hoarding': dict(regime='quantity', gH=0.05, shocks=[[20.0, dict(cu0=0.3), 1.0]]),
    'rentiers spend less': dict(shocks=[[20.0, dict(c_r=0.15), 1.0]]),
    'boom then hike': dict(g_q=0.03, T=80.0, shocks=[[10.0, dict(prem=0.008), 10.0], [25.0, dict(r_cb=0.06), 1.0]]),
    'labor cap + Goodwin': dict(labor_cap=True, phillips=0.15),
    'fiscal rule, r=9%': dict(shocks=[[20.0, dict(r_cb=0.09, fiscal=0.05), 1.0]]),
    'wage share up': dict(shocks=[[20.0, dict(omega=0.70), 1.0]]),
}
KEYS = ['Y', 'K', 'L', 'B', 'E', 'u', 'Phi']

NL64 = {k: v.tolist() for k, v in neutral_links([0.6, 0.4]).items()}
SLUMP = [[20.0, dict(g0=[-0.02, -0.08]), 1.0], [25.0, dict(g0=[-0.02, -0.02]), 1.0]]
SCENARIOS_WORLD = {
    'not linked, c_r differ': dict(K0=[175.0, 75.0], c_r=[0.25, 0.6], T=60.0),
    'linked, C slump': dict(K0=[150.0, 100.0], m=NL64['m'], hold=NL64['hold'], shocks=SLUMP, T=60.0),
    'linked, B boom then hike': dict(K0=[150.0, 100.0], m=NL64['m'], hold=NL64['hold'], g_q=0.03, T=60.0,
                                     shocks=[[5.0, dict(prem=[0.008, 0.02]), 10.0], [20.0, dict(r_cb=0.06), 1.0]]),
    'fiscal union, split at 40': dict(K0=[150.0, 100.0], m=NL64['m'], hold=NL64['hold'], fiscal=0.03, b_target=1.5,
                                      shocks=SLUMP, fiscal_union=[0.0, 40.0], T=60.0),
    'devaluation 30%': dict(K0=[150.0, 100.0], m=NL64['m'], hold=NL64['hold'], shocks=SLUMP, T=60.0,
                            fx=dict(currency=[0, 1], regime='fixed', eta=1.0, shifts=[[20.0, 0.7, 1.0]])),
    'float on utilization gap': dict(K0=[150.0, 100.0], m=NL64['m'], hold=NL64['hold'], shocks=SLUMP, T=60.0,
                                     fx=dict(currency=[0, 1], regime='float', eta=1.5, k_ca=0.0, k_r=0.0, k_u=0.5)),
    'core and periphery': dict(K0=[150.0, 100.0], phi_trade=0.5, A0=[1.0, 0.9], hold=[[0.95, 0.05], [0.40, 0.60]],
                               init=None, verdoorn=1.0, price_adj=0.5, spread=[0.01, 0.03], T=100.0),
}
WKEYS = ['Y', 'K', 'L', 'B', 'S', 'e']
TOL_WORLD = 1e-8   # 行列演算の順序の違いがあるので、世界版は少しゆるめる


def run_js(ctx, fn, params):
    s = ctx.eval(f'JSON.stringify((function(){{ const o = {fn}({json.dumps(params)}); '
                 f'const r = {{}}; for (const k of {json.dumps(KEYS)}) r[k] = Array.from(o[k]); return r; }})())')
    return {k: np.array(v) for k, v in json.loads(s).items()}


def main():
    ctx = quickjs.Context()
    ctx.eval(open(os.path.join(ROOT, 'site', 'model_v6.js')).read())
    worst = 0.0
    for name, kw in SCENARIOS_CM.items():
        py = simulate_cm(**{k: (tuple(tuple(x) for x in v) if k == 'shocks' else v) for k, v in kw.items()})
        js = run_js(ctx, 'CreditV6.simulateCM', kw)
        err = max(np.max(np.abs(js[k] - py[k]) / np.maximum(np.abs(py[k]), 1e-12)) for k in KEYS)
        worst = max(worst, err)
        print(f'one region  {name:28s} max rel. diff {err:.2e}')
    ctx.eval(open(os.path.join(ROOT, 'site', 'world_v6.js')).read())
    worst_w = 0.0
    for name, kw in SCENARIOS_WORLD.items():
        kwp = dict(kw)
        if 'shocks' in kwp:
            kwp['shocks'] = tuple(tuple(x) for x in kwp['shocks'])
        if 'fx' in kwp and 'shifts' in kwp['fx']:
            kwp['fx'] = dict(kwp['fx'], shifts=[tuple(x) for x in kwp['fx']['shifts']])
        if 'fiscal_union' in kwp:
            kwp['fiscal_union'] = tuple(kwp['fiscal_union'])
        py = simulate_world(N=2, **kwp)
        s = ctx.eval(f'JSON.stringify((function(){{ const o = CreditV6.simulateWorld(2, {json.dumps(kw)}); '
                     f'const r = {{}}; for (const k of {json.dumps(WKEYS)}) r[k] = o[k]; return r; }})())')
        js = {k: np.array(v) for k, v in json.loads(s).items()}
        err = max(np.max(np.abs(js[k] - py[k]) / np.maximum(np.abs(py[k]), 1e-6 * np.abs(py['Y']).max()))
                  for k in WKEYS)
        worst_w = max(worst_w, err)
        print(f'world (2)   {name:28s} max rel. diff {err:.2e}')
    print(f'worst: one region {worst:.2e} (tolerance {TOL:.0e}), world {worst_w:.2e} (tolerance {TOL_WORLD:.0e})')
    if worst > TOL or worst_w > TOL_WORLD:
        sys.exit(1)


if __name__ == '__main__':
    main()
