# credit_simulation_v6

信用創造ダイナミクス v6(信用循環モデル)

<!-- Time-stamp: "2026-10-24" -->

「信用創造ダイナミクス」v1〜v5([misc_html](https://github.com/JRF-2018/misc_html) の credit_simulation_202602/)の続きです。v5 を読み解いたうえで組み直した「信用循環モデル」を、ブラウザで動くシミュレーション、分析レポート、そしてモデルについての定理の Lean による証明としてまとめました。

## ページ

* [credit_simulation_v6.html](https://jrf-2018.github.io/credit_simulation_v6/credit_simulation_v6.html) … 一地域版のシミュレーション(v5 と同じ形式)。
* [credit_simulation_v6_world.html](https://jrf-2018.github.io/credit_simulation_v6/credit_simulation_v6_world.html) … 世界版(二つの地域を貿易と金融でつなぐ)。
* [simulation_v6_analysis](https://jrf-2018.github.io/credit_simulation_v6/simulation_v6_analysis.html) … 分析レポート([Markdown](site/simulation_v6_analysis.md))。

モデルの導き方と議論は、二つの IPYNB(`notebooks/`)にあります。HTML にしたものも Pages に置いています。

* [信用創造はどこで止まるのか ――「信用創造ダイナミクス v5」を読み解き、利子が経済に戻るモデルへ組み直す](notebooks/credit_creation_v6.ipynb)
  * HTML: https://jrf-2018.github.io/credit_simulation_v6/credit_creation_v6.html
* [信用の世界経済は一つか ―― 国のモデルを連結し、縮約し、射影する](notebooks/credit_linkage.ipynb)
  * HTML: https://jrf-2018.github.io/credit_simulation_v6/credit_linkage.html

どちらも、上から順に実行すれば全部動きます(numpy, scipy, matplotlib。Google Colab でも動きます)。Lean のセルは最後にまとめてチェックします(Lean がない環境では elan と Mathlib を入れるので時間がかかります)。「信用の世界経済は一つか」の最後では、このリポジトリを `git clone` して `CreditV6/`(定理 A・B・C・B′・C′)もビルドします。

## v6 のモデル(v5 との違い)

* **利子と配当は、金利生活者の所得として経済に戻る。** v5 では利払いが経済から消え、定常状態の分配集中度 Φ が必ず 1 以上になり、どの金利でも長期には崩壊していました。
* **所得は需要で決まる**(労働者の消費 + 金利生活者の消費 + 投資 + 政府支出)。生産能力を超えた需要は強制貯蓄になり、会計(部門収支の恒等式)は厳密に閉じます。
* **株式的富 E は期待利潤の資本還元**。投資は利潤率とトービンの q で決まり、借入は担保(E と資本)で頭打ちになります。E が縮むと在庫の損耗が増える(在庫維持能力の喪失)ことは v5 から引き継ぎました。
* **銀行の「金利の制度」と「量の制度」**を切り替えられます。量の制度では実効準備率 = 法定準備率 + 現金/預金比(タンス預金)になります。
* Φ(利払い負担率)、θ\*(利払い前の純利潤分配率)、実効準備率、経済全体の貯蓄率は、仮定ではなく結果として出てきます。
* 世界版では、地域を貿易(輸入性向・相手)と金融(相手の企業・政府への請求権の保有)でつなぎ、経常収支とポートフォリオ投資の差を決済残高で受けます。通貨が別々の場合(為替)、財政統合、競争力による貿易配分(中核と周辺)も扱えます。

## Lean による定理(CreditV6/)

| ファイル | 内容 |
|---|---|
| `Basic.lean` | 連結(縮約)の補題: 段階的に連結しても一度に連結しても同じ(結合性)、世界の経常収支の和は 0、(重み, パラメータ) の加重平均は可換モノイド、線形の乗数の集計、伸び率の違う二つの指数関数の和は一つの指数関数にならない(動学の厳密な縮約の不可能性)、折れ線の閾値の集計のイェンセンの不等式、射影してから集計すると元に戻る(逆は成り立たない)、閾値の分布の混合 |
| `Reduction.lean` | 定理 A の骨格: 世界の写像 F と一国の写像 G が規模について 1 次同次で、まとめる写像が規模と可換なら、釣り合いの取れた成長経路の上で一度一致した一国のモデルは、ずっと一致する。誤差がある場合の上限(G がリプシッツ連続のとき) |
| `Model.lean` | 多地域の信用循環モデルの 1 期の写像(`python/world.py` の `simulate_world` の書き写し。共通通貨・労働の天井なし・財政統合なしの範囲) |
| `Homogeneity.lean` | **モデルの 1 期の写像は、規模について 1 次同次である**(`step_hom`)。所得は生産能力の上限込みの方程式の解として定義し、解がただ一つなら、解も同次になることを示す |
| `TheoremA.lean` | **定理 A**(`world_reduction`): 地域ごとのパラメータが違っていても、釣り合いの取れた成長経路の上では、一度一致した一国のモデルは世界の合計とずっと一致する |
| `TheoremB.lean` | **定理 B**(線形の核、二地域): つながっていれば(行列の非対角が正)、固有値は λ₁ > \|λ₂\| で、釣り合い経路からのずれは毎期ちょうど λ₂/λ₁ 倍に縮む(`deviation_ratio`、`rate_lt_one`)。つながっていなければ、構成比は (d/a)ⁿ 倍で動き続ける(`unlinked_ratio`) |
| `TheoremC.lean` | **定理 C**: 一国のモデルの 1 期のずれは「地域の伸び率のばらつき × 構成比の動き」以下(`growth_gap_bound`)。n 期の累積の上限(`prod_bound`) |
| `Linearization.lean` | **定理 B′**(実際のモデルの線形化): 1 次同次な写像のオイラーの恒等式 `J (P x₀) = P (F x₀)`(`jacobian_scale`)。モデルの `step` が釣り合い経路の上の点で微分可能なら、そのヤコビアンは成長率 γ を固有値に持ち、規模の方向が固有ベクトルになる(`step_jacobian_on_ray`)。定理 B の線形の核の λ₁ はこの γ にあたる |
| `TheoremBModel.lean` | **定理 B と B′ の関係**: 共通の核(線形の写像で、二つの固有ベクトルに分けた状態は固有値の冪で伸び、`\|λ₂\| < λ₁` なら係数の比は 0 に近づく)。定理 B はこれを 2×2 の線形の核に当てはめたもの(`theoremB_tendsto`)。実際のモデルのヤコビアンに当てはめたものが `model_theoremB` で、`λ₁ = γ` を定理 B′ が与える(ずれの方向の `\|λ₂\| < γ` は仮定。数値で確かめる) |
| `TheoremCModel.lean` | **定理 C′**(実際のモデルの縮約誤差): 1 期の縮約誤差(一国のモデル − 世界をまとめたもの)は 1 次同次で、ある時点で一致すれば何倍した点でも一致する(`model_error_zero_on_ray`)。微分可能なら、その近くでは誤差は規模の方向を除いたずれ(構成比のずれ)の 1 次で抑えられる(`model_theoremC`)。定理 C の「成長率のばらつき」の役は誤差の微分のノルムが果たす |

`sorry` はありません。CI(`.github/workflows/lean.yml`)で毎回ビルドしています。

定理 A・B・C を合わせると、「つながっていれば構成比は釣り合い経路に近づき(B)、構成比が動かなくなればずれは生じず(C)、釣り合い経路の上では一国のモデルは厳密に一致する(A)」と言えます。線形の核(B・C)と実際のモデルは、釣り合い経路の上での線形化(B′・C′)でつながります。B′・C′ はモデルが微分できることを仮定していて、それが崩れるのは金融と投資の折れ目を越えるとき(危機)です(IPYNB の第 14.10 節)。Python のモデルのヤコビアンを数値で求めると、構成比の固有値はシミュレーションの減衰の速さと合います(IPYNB の第 14.8 節)。主張(証明は省略)は、IPYNB「信用の世界経済は一つか」の第 14 節にも載せています。

定理 A の仮定「ある時点で一致する」は、Python の `aggregate` が流れを重みにしてパラメータを作ることで(なめらかな min・max の効き方の違いを除いて)満たしています。数値では、つながった二地域を縮約したずれが 100 年後も 10⁻⁷ 程度です(レポートの発見 I)。

## 中身

* `notebooks/` … 二つの IPYNB(実行済みの出力つき)。Pages の配備のときに HTML に変換します。
* `site/` … シミュレーションのページ(`model_v6.js` と `world_v6.js` がモデル本体)と分析レポート。GitHub Actions(`.github/workflows/pages.yml`)で GitHub Pages に配備します。
* `python/` … 参照実装(IPYNB と同じもの)。`sims.py`(v5 の移植と一地域版)、`world.py`(世界版)。
  * `check_js_vs_py.py` … ページの JavaScript と参照実装の数値の一致を確かめる(CI の `.github/workflows/check.yml`)。JavaScript は quickjs で動かします。
* `tools/` … `make_report_tables.py`(レポートの表を作る)、`screenshot.py`(手元でページを確かめる。Playwright が要る)。
* `CreditV6/`、`lakefile.lean` … Lean 4(v4.34.1)と Mathlib。

```bash
pip install numpy quickjs
python python/check_js_vs_py.py
python tools/make_report_tables.py
lake build
```

## 関連

* 信用創造ダイナミクス v1〜v5: https://github.com/JRF-2018/misc_html
* 解説記事(v1〜v3): 《[信用創造の限界は法定準備率か金利か](http://jrf.cocolog-nifty.com/statuses/2026/02/post-a648df.html)》(2026年2月)、(v4・v5)《[資本主義の成立(労働力の空売り)と魔術](http://jrf.cocolog-nifty.com/statuses/2026/04/post-84784d.html)》(2026年4月)
* 中核と周辺: https://github.com/JRF-2018/wallerstein_theory

## Author (文責)

JRF ( http://jrf.cocolog-nifty.com/statuses , Twitter (X): @jion_rockford )

モデル化・プログラム・証明・レポートは Claude Opus 5.5 (Anthropic) によるものです。

## License

基本的に「学習用に特に Public Domain になることを望んでいるが、それが気になる場合は MIT License で。」です。
