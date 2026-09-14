# 从零开始：用 Lean 形式化论文（本项目使用手册）

> **本仓库专用说明（2026-09-14）**：这份手册是从"指南仓库"
> `lean-formalization-study` 复制过来的，它讲的 Lean / mathlib / Lake / elan /
> VS Code / GitHub 流程对本仓库**完全一样**，但里面的**具体例子**（`FormalProof`
> 目录、`hammingDist` 练习等）来自那个仓库。本仓库的库名是 **`FCC`**，文件名把
> `FormalProof` 换成 `FCC` 即可；本仓库要形式化的论文是
> **《Function-Correcting Codes With Data Protection》(IEEE TIT 2026)**，
> 范围与步骤见 `PLAN.md`，符号对照见 `Notation.md`。

这份文档写给**完全没有接触过 Lean** 的你。读完它，你应该能够：

1. 知道 Lean / mathlib / Lake / elan / VS Code 各是什么，分别管什么；
2. 看懂本仓库里每个文件是干什么的（它们照着你老师的 `n4code_lean_dev` 搭的）；
3. 独立完成一次"改代码 → 编译 → 检查 → 提交"的完整循环；
4. 大致读懂一段 Lean 代码（定义、定理、`by` 证明块、常用 tactic）；
5. 把结果推到 GitHub，并且知道之后要做什么（发布、引用、论文）。

配合阅读：`README.md`（项目概览）、`PLAN.md`（计划与定理清单）、
`Notation.md`（论文符号 ↔ Lean 名字对照表）、`AGENTS.md`（写代码时必须遵守的规矩）。

---

## 0. 一分钟速览

**形式化论文**的意思是：把论文里的定义、定理和证明，逐条写成 Lean 能理解的语句，
让机器逐步检查每一步推理。机器检查通过，说明"在 Lean 的数学基础之上，证明没错"；
检查通不过，或者写不出来，往往说明论文里某一步推理有问题或写得不清——这正是这项工作
的价值所在（你老师的仓库就记录了若干这类发现，见 `paper/CompanionNote.tex`
的 Discrepancies 一节）。

你的日常循环只有五步：

```text
写下定义 → 写下定理陈述（可以先用 sorry 占位）→ 用 tactic 写证明
        → lake build + 检查脚本 → git commit + push
```

"读完一篇论文"和"形式化一篇论文"的差别是：前者你可以跳过细节，后者每一个
"显然"都要机器认账。

---

## 1. 先搞清楚四个名词

| 名字 | 类比 | 它管什么 |
| --- | --- | --- |
| **Lean 4** | 语言 + 编译器 | 定理证明器本身。你写的 `.lean` 文件是它的语言：既能定义数学对象，也能写证明 |
| **mathlib** | 一个巨大的标准库 | 社区维护的数学图书馆（群论、实分析、组合、`Finset`……）。论文形式化基本离不开它 |
| **Lake** | `npm` / `cargo` | 项目管理与构建工具。`lake build` 编译你的项目，`lake update` 拉依赖 |
| **elan** | `nvm` / `rustup` | 工具链版本管理器。它根据 `lean-toolchain` 文件决定用哪个 Lean 版本，并自动下载 |
| **VS Code + Lean 4 扩展** | 编辑器 + 插件 | 写 Lean 的体验来源：鼠标悬停看类型，**Infoview** 面板实时显示"当前目标" |

最重要的一点：Lean 的体验几乎全在编辑器的 **Infoview** 里。命令行只负责"能不能编译过"，
而"这一步该怎么证"是看 Infoview 里剩下的目标（goal）来决定的。

---

## 2. 你现在这台机器上装了什么

我已经替你装好：

| 项目 | 位置 / 版本 |
| --- | --- |
| elan | `C:\Users\lenovo\.elan`（版本 4.2.4） |
| Lean 工具链 | `leanprover/lean4:v4.34.0-rc2` = **Lean 4.34.0-rc2**（mathlib master 要求的版本） |
| Git | `D:\Program Files\Git\cmd\git.exe`（已配置 `user.name = FrankieLiu20`） |
| GitHub CLI | `C:\Users\lenovo\gh\bin\gh.exe`（v2.100.0，已登录 `FrankieLiu20`，并配好 git 凭据） |
| VS Code | `C:\Users\lenovo\AppData\Local\Programs\Microsoft VS Code` |

**还差一步**：给 VS Code 装 Lean 插件。在 VS Code 里按 `Ctrl+Shift+X` 打开扩展面板，
搜索 **Lean 4**（作者 `leanprover`），点安装。装完后打开任意 `.lean` 文件，
右下角会出现 Lean 状态；`Ctrl+Shift+Enter` 打开 **Lean Infoview** 面板。

> 命令行里如果提示找不到 `lake`，是因为 PATH 还没刷新。重启终端（或重启 VS Code）即可；
> 也可以临时用完整路径 `C:\Users\lenovo\.elan\bin\lake.exe`。

---

## 3. ⚠️ 文件存放规则：文档在 OneDrive，代码在 E:\lean（重要）

Lean 项目一旦编译，会在项目里生成 `.lake\` 目录：**约 7 GB、几万个文件**
（mathlib 的预编译结果）。让 OneDrive 同步这些东西有三个坏处：

* 上传/下载几 GB，磁盘和网络一直响；
* OneDrive 同步时会锁文件，编译偶尔报"文件被占用"之类的怪错；
* 路径很长，容易踩 Windows 的路径长度限制。

所以规则是：**文档放 OneDrive，代码放 `E:\lean`**。已经替你安排好了：

```text
OneDrive\桌面\Lean Formalization-Independent study\   ← 资料区（自动同步，手机也能看）
├─ papers\      四篇论文 PDF
├─ notes\       读书笔记 / 定理清单草稿
└─ README.md    这个布局的说明

E:\lean\                                              ← 代码区（不参与 OneDrive 同步）
├─ lean-formalization-study\   指南仓库（工作副本，已编译通过）
├─ reference\n4code_lean_dev\  你老师仓库的克隆，用来对照写法
└─ _archive\...                早期放在 OneDrive 的那份代码（已归档，可删）
```

换电脑、或者想重建一份代码副本时：

```powershell
New-Item -ItemType Directory -Force E:\lean | Out-Null
cd E:\lean
git clone https://github.com/FrankieLiu20/lean-formalization-study.git
cd lean-formalization-study
lake exe cache get     # 取 mathlib 预编译产物（第一次要下载几 GB，只做一次）
lake build             # 编译（几分钟）
```

**三条铁律：**

1. **不要在 OneDrive 里编译，也不要用 VS Code 打开 OneDrive 里的项目** ——
   打开就会生成 `.lake\`，几 GB 文件立刻开始被同步。
2. **在 VS Code 里要用"打开文件夹"（Ctrl+K Ctrl+O），不要只双击打开单个 `.lean` 文件。**
   只打开文件时插件找不到 `lakefile.toml` / `lean-toolchain`，会退回到 elan 的默认版本，
   于是可能用**错误的 Lean 版本**去加载 mathlib（症状：Infoview 空白、右下角一直转、
   CPU 狂转）。elan 的默认版本已经设成项目用的那个，但正确做法仍然是打开文件夹。
3. **每个论文项目一个仓库，而且每个仓库都要有自己的 `.lake`（7–8 GB）。**
   所以项目都放 E 盘（约 247 GB 空闲）——现在这个项目就在 `E:\lean\lean-formalization-study`。

---

## 4. 项目结构导读

本仓库的文件布局是**照着你老师的 `n4code_lean_dev` 搭的**，所以学会这套，
以后看他的仓库、写自己的仓库都是同一套肌肉记忆。

### 4.1 Lean 代码

| 路径 | 作用 |
| --- | --- |
| `lakefile.toml` | 项目定义：库叫 `FCC`，依赖 mathlib（不写 `rev` = 跟最新 master，具体版本锁定在 `lake-manifest.json`） |
| `lean-toolchain` | 一行字，写着用哪个 Lean 版本，elan 据此选择/下载。**必须和 mathlib 要求的版本一致**，否则 `lake exe cache get` 会拒绝恢复预编译产物 |
| `lake-manifest.json` | **依赖锁定文件**，由 `lake update` 自动生成，记录 mathlib 的确切 commit，保证换台电脑也能复现（要提交进 Git） |
| `FCC.lean` | **库的根模块**，必须放在包根目录、名字必须和库名一致。里面 `import` 了所有子模块——`lake build` 靠它决定编译哪些文件 |
| `FCC/Definitions.lean` | 论文无关的数学建模：二进制字、Hamming 距离、`(n,M)` 码、ML 译码的 `dCode`/`alpha`/`lambda`、码等价 |
| `FCC/Basic.lean` | 第一批**已证明的引理**（XOR 与 Hamming 距离的基本性质），以及若干 `decide` 数值检查 |
| `FCC/Statements.lean` | **论文定理目录**：论文里每条编号定理/引理/推论在这里（或它所属的阶段模块里）有一条对应的 Lean 陈述 |
| `FCC/AxiomCheck.lean` | 公理审计：对每个"头牌定理"执行 `#print axioms`，确认证明只依赖标准公理 |

### 4.2 文档（老师仓库的"文档习惯"，也是它的精华）

| 文件 | 作用 | 你什么时候动它 |
| --- | --- | --- |
| `README.md` | 给外人看的门面：论文出处、状态表、构建与验证方法、目录说明 | 每完成一个阶段 |
| `PLAN.md` | 计划书：把论文里**所有编号定理**列成表，划分阶段 A/B/C…，标注 DONE | 开工时写，阶段完成时更新 |
| `Notation.md` | **论文符号 ↔ Lean 标识符**对照表（整个项目的翻译字典） | 每加一个新符号 |
| `CONSISTENCY.md` | 论文↔代码一致性协议 + 人工检查清单 | 很少改，但要照着做 |
| `VERIFICATION.md` | "verified"的定义、公理白名单、如何从零复现检查 | 发布前 |
| `DEVLOG.md` | 开发日志：日期 + 今天做了什么决定、踩了什么坑 | 每个工作日 |
| `TODO.md` | 待办与后续改进 | 随手记 |
| `AGENTS.md` | **给 AI 助手看的规矩**（构建性能、最小 import、文档字符串、不许留编译错误……） | 一开始就写 |
| `PUBLISHING.md` | 发表计划：投什么会、怎么做 artifact、Zenodo DOI | 后期 |
| `CITATION.cff` | 机器可读的引用信息（GitHub 右边会出现 "Cite this repository"） | 发布前 |
| `NOTICE` | 第三方代码来源与许可说明（本项目核心定义改写自你老师的 Apache-2.0 代码） | 引用别人代码时 |

### 4.3 脚本与自动化

| 路径 | 作用 |
| --- | --- |
| `scripts/consistency_check.ps1` | **每完成一步就运行**：编译 + 检查"文档里引用的论文标签是否真的存在" + "论文里每条定理都有 Lean 对应" + "没有孤儿模块" + 统计剩余 `sorry` |
| `scripts/axioms_check.ps1` | 公理审计：解析 `AxiomCheck.lean`，确认每个头牌定理只依赖 `propext / Quot.sound / Classical.choice`，一旦出现 `sorryAx` 就失败 |
| `scripts/headline_theorems.txt` | 头牌定理清单（与 `AxiomCheck.lean` 双向核对，防止有人悄悄删掉一条定理） |
| `.github/workflows/ci.yml` | GitHub Actions：每次 push 自动在云端编译 + 跑检查 |

---

## 5. 一次完整的工作循环

这是你以后每天重复的动作（假设你在 `E:\lean\lean-formalization-study`）：

```powershell
# 0) 第一次：拉依赖（只做一次，之后都是增量的）
lake exe cache get     # 取 mathlib 预编译产物
lake build             # 编译整个项目

# 1) 打开 VS Code，改一个 .lean 文件，看 Infoview 里有没有红色错误
code .

# 2) 编译检查（增量，几秒钟）
lake build

# 3) 跑一致性检查（每完成一步都要跑）
pwsh scripts/consistency_check.ps1

# 4) 提交
git add -A
git commit -m "prove hammingDist_symm"
git push
```

**只编译一个模块**（大项目里很常用，快得多）：

```powershell
lake build FCC.Basic              # 只编译 Basic 模块
lake env lean FCC/AxiomCheck.lean # 只类型检查一个文件
```

**三条铁律**（你老师的 `AGENTS.md` 里专门强调过）：

1. **永远不要运行裸的 `lake clean`**。它会把 mathlib 的预编译产物一起删掉，
   下次要从源码重编上千个文件（十几分钟）。要清理就写 `lake clean FCC`。
2. **不要从源码重编 mathlib**。产物丢了就跑 `lake exe cache get` 恢复。
3. **永远不要留下编译不过的代码**。证明没写完可以写 `sorry` 占位（编译给警告但不报错），
   但语法错误、类型错误必须当场修掉。

**一个必须知道的坑（我们已经踩过一次）**：`lean-toolchain` 里的版本必须和
**mathlib 要求的版本**一致。判断方法就是打开
`.lake\packages\mathlib\lean-toolchain` 看它写的是什么，然后把项目根目录的
`lean-toolchain` 改成同一行。不一致时，`lake exe cache get` 会直接拒绝恢复
预编译产物，`lake build` 会退化成"用错误的编译器从源码重编 mathlib"，
报出一堆看起来像 mathlib 自己坏了的错误（`Unknown identifier ...`），
实际上是我们这边版本没对齐。以后升级 Lean / mathlib 时，这两处要一起改。

---

## 6. 怎么读 Lean 代码

### 6.1 三种基本句型

```lean
-- 定义：给某个数学对象起个名字
def hammingWeight {n : ℕ} (x : Word n) : ℕ :=
  ∑ i ∈ (Finset.univ : Finset (Fin n)), if x i = true then 1 else 0

-- 引理：先说命题，再给证明（by 后面就是证明）
lemma hammingDist_symm {n : ℕ} (x y : Word n) : hammingDist x y = hammingDist y x := by
  rw [hammingDist, hammingDist, bitXor_comm]
```

读法（以第一行为例）：

* `def` = "定义一个东西"；`lemma`/`theorem`/`example` = "陈述一个要证明的命题"；
* 圆括号里的 `(x : Word n)` 是**参数**：x 是一个长度为 n 的二进制字；
* 花括号里的 `{n : ℕ}` 是**隐式参数**：Lean 通常能从上下文推断出 n，不用你手写；
* 冒号后面（`:` 之后、`:=` 之前）是**命题本身**，也就是"要证什么"；
* `:=` 后面是**证明**；`by` 表示"接下来用 tactic 一步步证"；
* `-- ` 开头是注释；`/-! ... -/` 是**模块文档注释**（会出现在生成的网页文档里）；
  `/-- ... -/` 紧贴在某个定义前面时是它的**文档字符串**——你老师要求每个完成的引理
  都有一行文档字符串，论文对应的引理还要写上论文标签（如 `` `thm:two` (Theorem 1) ``）。

### 6.2 逐行读懂一个真实证明

`FCC/Basic.lean` 里的第一个引理：

```lean
/-- XOR is commutative. -/
lemma bitXor_comm {n : ℕ} (x y : Word n) : bitXor x y = bitXor y x := by
  funext i
  by_cases hx : x i = true <;> by_cases hy : y i = true <;> simp [bitXor, hx, hy]
```

* `funext i`：要证两个函数相等，就取任意一个位置 `i`，证明在该位置相等
  （函数外延性：把"函数相等"化归成"逐点相等"）；
* `by_cases hx : x i = true`：分情况讨论——第 i 位是 `true` 还是 `false`；
  `<;>` 表示"对上一步产生的每个目标都执行后面的 tactic"；
* `simp [bitXor, hx, hy]`：用 `bitXor` 的定义和已知条件 `hx`、`hy` 把两边化简到一样。

再看一个更典型的：

```lean
/-- Hamming distance is symmetric. -/
lemma hammingDist_symm {n : ℕ} (x y : Word n) : hammingDist x y = hammingDist y x := by
  rw [hammingDist, hammingDist, bitXor_comm]
```

* `rw [...]`：重写。先把两处 `hammingDist` 展开成定义 `hammingWeight (bitXor ...)`，
  再用 `bitXor_comm`（XOR 交换律）把 `bitXor x y` 换成 `bitXor y x`，两边就一模一样了。

**学会"看剩下来的目标"**：在 VS Code 里把光标放到 `by` 后面的某一行，Infoview 会显示：

```text
n : ℕ
x y : Word n
⊢ hammingWeight (bitXor x y) = hammingWeight (bitXor y x)
```

`⊢` 后面就是"还差什么"。**写证明 = 不断把目标变形，直到它自己消失。**
卡住时先看目标，再想"这条恒等式在我脑子里叫什么名字"。

### 6.3 常用工具速查

| 写法 | 作用 |
| --- | --- |
| `#check foo` | 看 `foo` 的类型（在文件里写一行，编译输出会打印） |
| `#print axioms foo` | 看定理 `foo` 依赖哪些公理 |
| `sorry` | 占位符："这里还没证"。**编译能过但会警告**；`axioms_check` 会把它算作失败 |
| `exact` | 直接给出正好证明目标的项 |
| `rw [...]` | 用等式重写目标 |
| `simp` | 化简（自动应用一批已注册的等式） |
| `omega` | 自然数/整数的线性算术自动机（非常好用） |
| `linarith` / `nlinarith` | 有序（半）域上的线性/非线性算术 |
| `ring` | 交换环里的多项式等式 |
| `decide` | 有限可判定命题直接算（内核计算，可信度高） |
| `by_cases h : P` | 分情况讨论 |
| `induction n with \| zero => ... \| succ n ih => ...` | 归纳法 |

具体某个 tactic 在某个目标上怎么用，最快的学法是把光标放上去看 Infoview
的红波浪线和报错信息。

---

## 7. 形式化一篇论文的完整流程

### 7.1 总流程

1. **把论文拆成清单**。通读论文，列出所有定义、所有编号的
   Theorem/Lemma/Corollary/Proposition，以及它们之间的依赖关系，写进 `PLAN.md`
   的 "Statements to formalize" 表格（你老师的 `PLAN.md` 就是范本）。
2. **建模**。决定用什么数据结构表示论文里的对象（例如"(n,4) 码"表示成
   `Fin n → Fin 4 → Bool`），写下核心定义，放进 `Definitions.lean`，
   同时更新 `Notation.md`。这一步最考验判断力，也最容易出错。
3. **写陈述**。把论文每条定理翻译成 Lean 命题，先不证明，用 `sorry` 占位，
   保证整个项目能编译。文档字符串里写论文标签，`consistency_check` 会验证
   这些标签在论文里真实存在。
4. **逐个攻破**。从最底层的引理开始，一次只啃一个。每证完一个：
   `lake build` → 提交 → 在 `PLAN.md` 打勾。
5. **收尾审计**。`sorry` 清零；头牌定理登记进 `AxiomCheck.lean` 和
   `scripts/headline_theorems.txt`；跑两个检查脚本；填 `VERIFICATION.md`
   的验证报告；打 tag、发 release。

### 7.2 阶段划分

你老师把工作拆成 Phase A–I（基础设施 → 性能不变性 → 单列引擎 → 双列引擎 →
主归约 → 线性码 → Class-I → 有限 n 分类 → 组装与文档），每个阶段对应一个
`.lean` 模块。**按依赖关系拆阶段，而不是按论文的章节顺序**，这样每一步都能编译、
都能提交。看 `PLAN.md` §4 和 §5（依赖图）。

### 7.3 机器检查的边界（一定要懂）

机器只检查"**从你写的陈述到结论**"这一段推理是否正确。它**不检查**
"你写的陈述是否真的等于论文里那句话"。如果陈述写错了（假设少了、系数写错了、
索引从 0 还是 1 弄错了），你有可能"成功地证明了一个错误的命题"。

所以流程里有两条防线：

* `Notation.md`：论文符号与 Lean 名字的严格对照表；
* `CONSISTENCY.md` 的**人工检查清单**：每完成一步，逐条核对定义是否和论文的
  公式一致、定理的假设是否和论文一致、等式成立的条件是否完整。

你老师的仓库里，这一条不是空话：`Notation.md` §4 和
`paper/CompanionNote.tex` 记录了形式化过程中发现的论文笔误/条件遗漏。
**"发现论文里的问题"正是这项工作的正经产出，不是失败。**

### 7.4 一个能立刻上手的小练习

等 `lake build` 跑通后，试着在 `FCC/Basic.lean` 末尾加一个引理：

```lean
/-- Hamming distance is invariant under XOR by a constant: d(x⊕z, y⊕z) = d(x,y). -/
lemma hammingDist_xor_right {n : ℕ} (x y z : Word n) :
    hammingDist (bitXor x z) (bitXor y z) = hammingDist x y := by
  sorry
```

先编译（会警告 `declaration uses 'sorry'`，这是正常的），把光标放到 `sorry` 上，
在 Infoview 里看目标长什么样；然后试着把它证出来——提示：先把 `hammingDist`
展开，再用 `bitXor_assoc`、`bitXor_comm` 把 `(x⊕z)⊕(y⊕z)` 变形为 `x⊕y`，
中间可能需要 `Bool.xor` 的消去律。证完后跑 `lake build` 和检查脚本，
再 `git commit`。**这就是一个完整的工作循环。**

---

## 8. 把结果放到 GitHub

### 8.1 一次性准备（已经替你做完 ✅）

* **GitHub CLI** 装在 `C:\Users\lenovo\gh\bin\gh.exe`（v2.100.0），已用设备码
  登录 **FrankieLiu20**，并配置了 git 凭据——以后 `git push` 不用再登录。
  （这个目录不在 PATH 里：要么用完整路径 `C:\Users\lenovo\gh\bin\gh.exe`，
  要么把 `C:\Users\lenovo\gh\bin` 加进 PATH。）
* **仓库**已创建并推送：<https://github.com/FrankieLiu20/lean-formalization-study>
  （Public。想改成私有：仓库页 → Settings → 拉到最下面 Change visibility。）
* **一个项目一个仓库**：每篇论文/每个项目单独建一个仓库（像你老师的
  `n4code_lean_dev`），不要把不同论文塞进同一个仓库。

下面是手动做一遍的步骤，供你以后自己建新项目时参考：

1. 注册 GitHub 账号（如果还没有）。
2. 建仓库：右上角 `+` → **New repository** → 名字建议 `itp-study` 或
   `lean-formalization-study` → **Public**（形式化成果通常公开；要私有也行）→
   不要勾 "Add a README"（本地已经有了）。
3. 首次推送时的身份认证，选一种：
   * **最简单**：装 [GitHub Desktop](https://desktop.github.com/) 或
     用 VS Code 的 "Publish to GitHub" 按钮，它会引导你登录；
   * **命令行**：`git push` 时弹出浏览器登录（Git Credential Manager 自带），
     或者生成 Personal Access Token 当密码用；
   * 想以后长期用得舒服，就配 SSH key 或装 `gh`（GitHub CLI）。

### 8.2 把本地项目推上去

```powershell
cd E:\lean\lean-formalization-study
git init                       # 如果还没初始化
git add -A
git commit -m "initial commit: project skeleton following the n4code_lean_dev layout"
git branch -M main
git remote add origin https://github.com/<你的用户名>/<仓库名>.git
git push -u origin main
```

推送前可以 `git status` 确认 `.lake/`、`reference/`、`*.pdf` 都没被加进来
（`.gitignore` 已经把它们排除了）。**只提交源码和文档**：`*.lean`、`*.md`、
`lakefile.toml`、`lean-toolchain`、`lake-manifest.json`、脚本。

### 8.3 之后的日常

```powershell
git status                      # 看改了什么
git add -A
git commit -m "prove Theorem 8 comparison part"
git push
```

**提交粒度**：你老师的习惯是"每证完一个引理就提交一次"，提交信息写清楚
（"update thm 3 statement in lean"、"simplify row distances"、"zero_column_all_odd
changed from better to equal"）。这种细粒度历史在出问题时极其有用——
哪天发现某个引理陈述写错了，能立刻定位到是哪一次改的。

### 8.4 发布一件"可引用的成果"

形式化项目做完后，标准做法是：

* 打 tag 发 release（`git tag v1.0.0 && git push --tags`）；
* 在 [Zenodo](https://zenodo.org/) 关联仓库，生成 **DOI**，把 DOI 写进
  `CITATION.cff` 和 `README.md`；
* 写一篇 companion note（你老师的 `paper/CompanionNote.tex`），说明形式化了什么、
  发现了哪些论文问题、可信基础（公理）是什么；
* 投稿到形式化方向的会议（ITP / CPP）——细节见 `PUBLISHING.md`。

---

## 9. 老师的规矩（已抄进本仓库 `AGENTS.md`）

这些规矩的原版在你老师的 `AGENTS.md` 里，核心是四条：

1. **构建性能**：不跑裸 `lake clean`；不从源码重编 mathlib；用增量编译。
2. **最小 import**：**永远不要 `import Mathlib`**（会把整个库拖进来，编译奇慢）。
   只 import 具体需要的模块，缺什么补什么——报错说缺 `Fintype` 实例就去
   `rg` 找提供它的模块。`lake shake <file>` 能自动算最小集合。
3. **文档字符串**：每个完成的定义/引理一行文档字符串；对应论文的还要带论文标签
   （用**章节号**，不要用 tex 行号，行号太脆）。
4. **不留坏构建**：可以用 `sorry` 占位（且必须注释它对应论文哪一条），
   但文件必须能编译。提交前跑 `consistency_check` 和 `axioms_check`。

还有一条不成文的：**AI 协作要留痕**。你老师仓库的 README 里明确写了
"proof scripts were developed with substantial assistance from AI coding agents …
all theorem statements, definitions and the overall design were authored by the
project author"。以后你发论文也要照这个格式披露——定理陈述和设计是你的责任，
机器只负责检查。

---

## 10. 常用命令总表

| 目的 | 命令 |
| --- | --- |
| 看 Lean 版本 | `lean --version` / `lake --version` |
| 拉依赖 + 取预编译产物 | `lake update` → `lake exe cache get` |
| 编译全部 | `lake build` |
| 编译一个模块 | `lake build FCC.Basic` |
| 只检查一个文件 | `lake env lean FCC/Basic.lean` |
| 在 Lean 环境里开交互/跑脚本 | `lake env lean --run ...` |
| 一键检查（编译+论文标签+孤儿模块+sorry 统计） | `pwsh scripts/consistency_check.ps1` |
| 公理审计 | `pwsh scripts/axioms_check.ps1` |
| 看仓库状态 / 提交 / 推送 | `git status` / `git add -A && git commit -m "..."` / `git push` |
| 看历史 | `git log --oneline -20` |

---

## 11. 你现在的位置和下一步

**已经完成**：

* Lean 工具链（elan + Lean 4.33.1）装好；
* 一个遵循老师仓库结构的项目骨架，含可编译的 mathlib 基础层
  （二进制字 / Hamming 距离 / `(n,M)` 码 / ML 译码）；
* 两个检查脚本、CI 配置、全套文档模板。

**下一步（需要你决定）**：四篇论文先形式化哪一篇？

* Function-Correcting Codes With Data Protection
* MDS Irregular Convertible Code
* Spectral Conditions for the Ingleton Inequality
* Torn-Paper Coding

选定之后，我会先陪你把这篇论文的定理清单拆进 `PLAN.md`、把符号对照表写进
`Notation.md`、把核心定义和定理陈述落到 `.lean` 文件里（用 `sorry` 占位），
然后一个一个引理地证下去。

**建议的节奏**：第一篇论文不要贪大，先挑一个"定理不多、依赖链短"的小结果练手，
把整套流程跑通一遍（哪怕只是一个第三章的小引理），再啃主要定理。
