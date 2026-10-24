# site/simulation_v6_analysis.md の表を、Python の参照実装から作る。
#   python tools/make_report_tables.py > /tmp/tables.md
# 出力をレポートに貼る(レポートの数値はすべてここから来る)。
import os
import sys

import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, 'python'))
from sims import simulate_v5, simulate_cm  # noqa: E402
from world import simulate_world, neutral_links, aggregate  # noqa: E402


def table(head, rows):
    print('| ' + ' | '.join(head) + ' |')
    print('|' + '---|' * len(head))
    for r in rows:
        print('| ' + ' | '.join(r) + ' |')
    print()


def at(h, k, year):
    return h[k][int(round(year / 0.1))]


print('## A: v5 と v6 の長期')
rows = []
for r in [0.03, 0.05, 0.08, 0.12]:
    v5 = simulate_v5(r=r, T=3000)
    idx = np.where(v5['Y'] < 0.5)[0]
    col = f'{idx[0]} 期' if len(idx) else 'しない'
    h = simulate_cm(T=300, r_cb=r)
    rows.append([f'{r:.2f}', col, f'{h["g"][-1]:.4f}', f'{h["Phi"][-1]:.4f}', f'{h["theta_star"][-1]:.3f}',
                 f'{h["B_Y"][-1]:.2f}'])
table(['金利', 'v5: 崩壊(Y<0.5)', 'v6: 成長率', 'v6: Φ', 'v6: θ*', 'v6: 国債/Y(300 年)'], rows)

print('## B: 金利と準備率(金利の制度、20 年目から 1 年かけて)')
base = simulate_cm(T=100)
rows = []
for lab, ch in [('政策金利 3%→6%', dict(r_cb=0.06)), ('政策金利 3%→8%', dict(r_cb=0.08)),
                ('準備率 5%→20%', dict(rho=0.2))]:
    h = simulate_cm(T=100, shocks=[(20, ch, 1.0)])
    r = h['Y'] / base['Y']
    rows.append([lab, f'{r.min():.3f}', f'{at(h, "Y", 30) / at(base, "Y", 30):.3f}', f'{r[-1]:.3f}',
                 f'{h["g"][-1]:.4f}', f'{h["rent_share"][-1]:.3f}', f'{h["B_Y"][-1]:.2f}'])
table(['操作', 'Y/基準 最低', '30 年目', '100 年目', '成長率', '金利生活者の所得/Y', '国債/Y'], rows)

print('## C: タンス預金と準備率(20 年目から 1 年かけて)')
rows = []
for reg, lab, ch in [('quantity', '量の制度: cu 0.05→0.30', dict(cu0=0.3)), ('quantity', '量の制度: ρ 5%→20%', dict(rho=0.2)),
                     ('rate', '金利の制度: cu 0.05→0.30', dict(cu0=0.3)), ('rate', '金利の制度: ρ 5%→20%', dict(rho=0.2))]:
    b = simulate_cm(T=100, regime=reg, gH=0.05)
    h = simulate_cm(T=100, regime=reg, gH=0.05, shocks=[(20, ch, 1.0)])
    r = h['Y'] / b['Y']
    rows.append([lab, f'{r.min():.3f}', f'{r[-1]:.3f}', f'{h["L_Y"].min():.3f}'])
table(['操作', 'Y/基準 最低', '100 年目', '企業債務/Y 最低'], rows)

print('## D: 金利生活者の消費性向 c_r(20 年目から 1 年かけて)')
rows = []
for cr in [0.15, 0.25, 0.35, 0.50]:
    h = simulate_cm(T=100, shocks=[(20, dict(c_r=cr), 1.0)])
    rows.append([f'0.35→{cr:.2f}', f'{h["Y"][-1] / base["Y"][-1]:.3f}', f'{h["g"][-1]:.4f}', f'{h["s_agg"][-1]:.3f}',
                 f'{h["B_Y"][-1]:.2f}'])
table(['c_r', 'Y/基準(100 年目)', '成長率', '経済全体の貯蓄率', '国債/Y'], rows)

print('## E: ブームと崩壊、在庫維持能力 κ(g_q=0.03)')
bq = simulate_cm(T=80, g_q=0.03)
euph = [(10, dict(prem=0.008), 10.0)]
hike = [(25, dict(r_cb=0.06), 1.0)]
rows = []
for lab, kw in [('ブーム → 金利引上げ', dict(shocks=euph + hike)), ('同上(κ=0)', dict(kappa=0.0, shocks=euph + hike)),
                ('ブームなしで金利引上げ', dict(shocks=hike)), ('ブームだけ', dict(shocks=euph))]:
    h = simulate_cm(T=80, g_q=0.03, **kw)
    r = h['Y'] / bq['Y']
    pk, tr = r[:260].max(), r[250:].min()
    rows.append([lab, f'{pk:.3f}', f'{tr:.3f}', f'{1 - tr / pk:.1%}', f'{h["Phi"].max():.3f}', f'{h["theta_star"].min():.3f}'])
table(['シナリオ', 'Y/基準 ピーク', '底', '下落率', 'Φ 最大', 'θ* 最小'], rows)

print('## F: 金利の三経路(25 年目に 3%→6%、10 年後の Y/引上げなし)')
gqs, gGs = [0.0, 0.02, 0.04], [0.16, 0.20, 0.24]
rows = []
for gq in gqs:
    row = [f'g_q={gq:.2f}']
    for gG in gGs:
        b = simulate_cm(T=40, g_q=gq, gG=gG)
        h = simulate_cm(T=40, g_q=gq, gG=gG, shocks=[(25, dict(r_cb=0.06), 1.0)])
        row.append(f'{h["Y"][350] / b["Y"][350]:.3f}')
    rows.append(row)
by = [simulate_cm(T=1, gG=gG)['B_Y'][0] for gG in gGs]
table(['投資の q への反応'] + [f'G/Yp={g:.2f}(国債/Y={x:.1f})' for g, x in zip(gGs, by)], rows)

print('## G: 国家(20 年目から、税率固定 / 財政ルール)')
rows = []
for r in [0.03, 0.06, 0.09]:
    for fr in [0.0, 0.05]:
        h = simulate_cm(T=100, shocks=[(20, dict(r_cb=r, fiscal=fr), 1.0)])
        rows.append([f'{r:.2f}', 'あり' if fr else 'なし', f'{h["g"][-1]:.4f}', f'{h["B_Y"][-1]:.2f}', f'{h["tau"][-1]:.3f}'])
table(['政策金利', '財政ルール', '成長率', '国債/Y(100 年目)', '税率'], rows)

print('## H: 労働')
rows = []
for lab, kw in [('読み出しだけ', {}), ('労働の天井', dict(labor_cap=True)), ('天井 + グッドウィン', dict(labor_cap=True, phillips=0.15))]:
    h = simulate_cm(T=150, **kw)
    rows.append([lab, f'{h["emp"][-1]:.3f}', f'{h["g"][-1]:.4f}', f'{h["omega"][-1]:.3f}', f'{h["L_Y"][-1]:.3f}', f'{h["B_Y"][-1]:.2f}'])
table(['労働の扱い', '雇用率(150 年目)', '成長率', '賃金分配率', '企業債務/Y', '国債/Y'], rows)

print('## I: 世界版(6:4、大きさに中立なつながり k=0.3、C だけ 5 年の投資の落ち込み)')
NL = neutral_links([0.6, 0.4])
slump = [(20, dict(g0=[-0.02, -0.08]), 1.0), (25, dict(g0=[-0.02, -0.02]), 1.0)]
rows = []
for lab, kw in [('つながりなし', {}), ('貿易だけ', dict(m=NL['m'])), ('金融だけ', dict(hold=NL['hold'])),
                ('貿易 + 金融', dict(m=NL['m'], hold=NL['hold']))]:
    b = simulate_world(N=2, T=60, K0=[150, 100], **kw)
    h = simulate_world(N=2, T=60, K0=[150, 100], shocks=slump, **kw)
    rows.append([lab, f'{np.min(h["Y"][:, 1] / b["Y"][:, 1]):.3f}', f'{np.min(h["Y"][:, 0] / b["Y"][:, 0]):.3f}',
                 f'{np.min(h["Y"].sum(1) / b["Y"].sum(1)):.3f}'])
table(['つながり', 'C の底', 'B の底', '世界の底'], rows)

print('## I2: 縮約(7:3、c_r=0.25/0.6、20 年目で一国に縮約)')
NL73 = neutral_links([0.7, 0.3])
rows = []
for lab, links, prm in [('つながりなし', {}, dict(c_r=[0.25, 0.6])), ('つながりあり', NL73, dict(c_r=[0.25, 0.6], m=NL73['m']))]:
    w = simulate_world(N=2, T=120, K0=[175, 75], hold=links.get('hold'), **prm)
    i0 = 200
    pA, TA, FA, stA = aggregate(w, i0, [[0, 1]], prm, None, links.get('hold'))
    a = simulate_world(N=1, T=100, state=stA, **pA)
    err = a['Y'][:, 0] / w['Y'][i0:i0 + 1000].sum(1) - 1
    rows.append([lab, f'{err[0]:+.1e}', f'{err[100]:+.1e}', f'{err[500]:+.1e}', f'{err[-1]:+.1e}'])
table(['', '縮約した時点', '10 年後', '50 年後', '100 年後'], rows)

print('## J: 通貨(C だけの落ち込み)')
cfg = dict(N=2, T=60, K0=[150, 100], m=NL['m'], hold=NL['hold'])
b = simulate_world(**cfg)
rows = []
for lab, fx in [('通貨統合', None),
                ('固定相場 + 30% 切り下げ', dict(currency=[0, 1], regime='fixed', eta=1.0, shifts=[(20, 0.7, 1.0)])),
                ('変動相場(経常収支に反応)', dict(currency=[0, 1], regime='float', eta=1.5, k_ca=1.0, k_r=0.0)),
                ('変動相場(稼働率の差に反応)', dict(currency=[0, 1], regime='float', eta=1.5, k_ca=0.0, k_r=0.0, k_u=0.5))]:
    h = simulate_world(shocks=slump, fx=fx, **cfg)
    rows.append([lab, f'{np.min(h["Y"][:, 1] / b["Y"][:, 1]):.3f}', f'{np.min(h["Y"][:, 0] / b["Y"][:, 0]):.3f}',
                 f'{h["e"][:, 0].min():.3f}〜{h["e"][:, 0].max():.3f}'])
table(['通貨', 'C の底', 'B の底', '為替 e の幅'], rows)

print('## K: 中核と周辺(φ=0.5、200 年)')
rows = []
for lab, kw in [('格差あり(v=1、C の競争力 0.9、スプレッド 3%、C の請求権の 4 割を B が持つ)',
                 dict(A0=[1.0, 0.9], hold=[[0.95, 0.05], [0.40, 0.60]], verdoorn=1.0, spread=[0.01, 0.03])),
                ('格差あり(同じ、ただし v=2)', dict(A0=[1.0, 0.9], hold=[[0.95, 0.05], [0.40, 0.60]], verdoorn=2.0, spread=[0.01, 0.03])),
                ('対称から 1% だけずらす(v=4)', dict(A0=[1.01, 1.0], verdoorn=4.0))]:
    K0 = [125, 125] if 'v=4' in lab else [150, 100]
    w = simulate_world(N=2, T=200, K0=K0, phi_trade=0.5, init=None, price_adj=0.5, **kw)
    sh = w['Y'][:, 0] / w['Y'].sum(1)
    rows.append([lab, f'{sh[0]:.2f}→{sh[1000]:.2f}→{sh[-1]:.2f}',
                 f'{-(w["rent_in"][-1, 1] - w["pay"][-1, 1]) / w["Y"][-1, 1]:.1%}', f'{w["NFA"][-1, 1] / w["Y"][-1, 1]:.2f}'])
table(['設定', 'B の比重(0→100→200 年)', 'C が外国に払う純額/Y', 'C の対外純資産/Y'], rows)
