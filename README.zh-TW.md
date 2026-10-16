# 稀疏多視角潛在類別模型：識別、語意合併與可認證反演

[English](README.md) · [繁體中文](README.zh-TW.md)

[English](README.md#english-project-description) · [繁體中文](README.zh-TW.md)

**Article / 論文：** [PDF](paper/sparse-multiview-latent-class-models.pdf)  
**Proofs / 證明：** [Lean source](lean/) · [Formal coverage / 形式驗證範圍](docs/formal-coverage.md)  
**Reproduce / 重現：** [Build instructions](BUILD.md) · [Pinned dependencies](DEPENDENCIES.md) · [Exact examples](examples/)

## 繁體中文專案說明

稀疏的多視角資料可能足以辨認潛在混合成分，卻仍無法決定這些成分在科學上
代表什麼。本專案針對有限類別混合模型研究這項差別：資料只觀察到部分相互
重疊的三組聯合分布，各群組共用條件機率核，同一連通分量內共用混合權重。

論文以彼此相容的邊置換與重疊穩定子描述完整觀測纖維。在局部張量分解唯一
的條件下，連通的重疊設計可以對齊可區辨的潛在成分；不同連通分量仍可各自
置換標籤。將潛在狀態固定合併為二元真值後，還要另外解決語意可識別性。
即使已知一個嚴格的方向錨點，敏感度、特異度與盛行率也未必能唯一確定。

對角觀測族在固定狀態數下具有可達到的尖銳有限效能集合。對具備明確條件數
邊界的參數類別，論文給出局部與全域反演界，並以精確有理數區間覆蓋程序，
在符合假設的輸入上最終產生可獨立檢查的正分離證書。同時，乘積方盒證書的
葉節點數下界與精確算例揭示：可計算性不等於實務可行，充分樣本數公式也
可能非常保守。研究另處理金標方向認證與有界條件相依誤差下的信賴集合。

Lean 原始碼涵蓋主要的識別、語意、條件化、統計與證書正確性介面。整篇論文
並非全部經 Lean 形式驗證：新增的幾何下界、部分算例與機率推導仍由傳統證明
或精確算術檢查支持。本專案沒有宣稱完成真實資料或臨床驗證，也沒有宣稱已
成功執行實務規模的完整模型分離搜尋。

## English project description

Sparse multi-view data may determine latent mixture components without
determining what those components mean scientifically. This project studies
that distinction for finite categorical mixtures observed through overlapping
triples of groups, with shared group kernels and mixture weights within each
connected component.

The article describes the full observational fiber using compatible edge
permutations and overlap stabilizers. Under local tensor uniqueness, connected
overlaps align distinguishable components; disconnected components retain
independent permutation choices. A fixed binary coarsening then creates a
separate semantic-identification problem. Even a strict direction anchor can
leave sensitivity, specificity and prevalence unidentified.

For diagonal observations, the paper derives sharp attained finite performance
images at a fixed state count. On conditioned parameter classes it obtains
explicit local/global inverse bounds. An exact rational interval-cover method
eventually produces a checkable positive separation certificate on admitted
inputs. A product-box leaf-count obstruction and exact examples show why this
computability result need not be practical, and why the sufficient sample
prescription can be extremely conservative. Gold-direction certification and
bounded conditional-dependence confidence sets complete the statistical scope.

The companion Lean development covers the core identification, semantic,
conditioning, statistical and certificate-correctness interfaces. The entire
article is not claimed to be Lean verified: the new geometric lower bound,
several worked examples and probability refinements retain conventional proofs
or exact arithmetic checks. No real-data or clinical validation and no
successful practical full-model separation search are claimed.

## 驗證與重現

固定使用 Lean **4.32.0** 與九項依賴的確切版本。公開的 **475** 個 Lean 輸入
檔案與 **2026-10-09** 完整驗證流程的雜湊一致；該次紀錄涵蓋 **159** 個來源
模組，僅觀察到 `propext`、`Classical.choice`、`Quot.sound` 三項標準公理。
本次發佈檢查與該歷史完整編譯分開記錄，詳見 [驗證範圍](verification/README.md)。

```bash
python3 -I examples/verify_examples.py
```

公開內容包含 PDF、Lean 證明與稽核原始碼、依賴版本及重建說明。內部工作紀錄
與論文 LaTeX／TikZ 原始碼留在本機。為保持論文到程式的精確對照，形式介面
沿用原始宣告名稱；範圍界線見 [形式驗證對照](docs/formal-coverage.md)。

## 獻詞

*Dedicated to those who fight harder when everything is turning against them.*

論文保留 AI 協助揭露，其中明確列出："GPT-6 Astra Pro and Claude Opus 5.5 max
assisted with critical review." 模型輸出不取代數學證明與來源核對。
