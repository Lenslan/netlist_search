# netlist_search

在门级网表里，从某个模块实例中的一根 wire 出发向前追溯它的全部 driver，直到寄存器、未知 cell、模块端口；再把追溯路径上每根中间 wire 的门逻辑还原成可读的 RTL 风格表达式。用于 netlist ECO 时定位状态机的条件分支、组合逻辑中的某一条逻辑。

```
grammar                       logic
cnt[3:0] == 5                 cnt[0] & (!cnt[1]) & cnt[2] & (!cnt[3])
sel ? a : b                   sel & a | !sel & b
```

## 构建

```
cargo build --release
```

可执行文件：`target/release/netlist_search`。

## 用法

```
netlist_search --netlist top.vg --lib std.lib [--lib macro.lib ...]
               --inst u_core/u_fsm --wire "nstate[2]"
```

| 参数 | 说明 |
|---|---|
| `--netlist <file>...` | 门级结构化 Verilog 网表，可给多个 |
| `--lib <file>...` | Liberty `.lib` 文本，可给多个 |
| `--inst <path>` | wire 所在模块的**例化路径**。省略表示顶层模块 |
| `--wire <name>` | `name`、`name[i]` 或 `name[msb:lsb]`。整根总线会逐位各出一份报告 |
| `--top <module>` | 顶层模块名，自动判定不了时才需要 |
| `--filter <signal>` | 只显示逻辑上依赖该信号的 wire（寄存器、端口或 net 名，可带位索引） |
| `--radix dec\|hex\|bin` | 常量写法，默认十进制 |
| `--prefer-arith` | 一根线既是 `bus + K` 的某一位、又等价于一个范围判断时，显示算术形式 |
| `--strict` | 不输出任何未经证明的结论 |
| `--effort <N>` | 把分析的工作量上限放大 N 倍（报告提示达到上限时使用） |
| `--expand` | 表达式很长时也完整打印 |
| `--no-cross` / `--max-hier-depth <N>` | 不跨模块 / 限制跨模块层数（默认 8） |
| `--max-nodes <N>` | 锥的 net 位数上限（默认 200000） |
| `--no-lift` | 只追溯并打印局部式 |
| `-o <file>` | 报告写入文件 |
| `--stats` | 在 stderr 打印耗时与规模 |

例化路径的写法：

- `u_core/u_fsm`、`top/u_core/u_fsm`、`u_core.u_fsm` 等价。
- 展平网表里带 `/` 的例化名（`\u_core/u_fsm `）直接照写。
- 只写后缀（如 `u_fsm`）时，全设计内唯一就采用；不唯一则报错并列出候选。这一步需要解析全部模块，会慢一些。

## 报告

```
=== Cone of u_fsm/nstate[2]   (module fsm, instance u_fsm) ===

Endpoints (5): 5 REG
  [REG] /u_cfg/mode  inst /u_cfg/mode_reg  DFFX1
  [REG] state[3]     inst state_reg[3]  DFFRX1
  ...

Wires (9), by distance from the target:
  d0 nstate[2]  AND2X1 U23
        local:    mode & is5or9
        endpoint: /u_cfg/mode & (state[3:0] inside {5, 9})
  d1 is5or9     OR2X1 U22
        local:    is5 | is9
        endpoint: state[3:0] inside {5, 9}
        aliases:  == !branch
  d2 is5        NOR4X1 U20
        local:    !(state[3] | n2 | state[1] | n0)
        endpoint: state[3:0] == 5
  ...
Notes:
  - ...
```

- **Endpoints**：追溯停下的地方。
- **Wires**：锥里的每根线，按离目标的门级距离（`d0`、`d1`…）排列，带驱动它的实例名和 cell 类型。
  - `local`：用它的直接输入 net 表示，和网表连接一一对应。
  - `endpoint`：用端点（寄存器、端口等）表示，说明这根线的含义。
  - `aliases`：锥内函数相同（`==`）或互为取反（`== !`）的其他线。
- **Notes**：所有假设和没做到的事。
- 名字：目标实例内部的名字不带前缀；其他实例里的名字以 `/` 开头，是从顶层起的完整路径。
- 寄存器端点的名字优先由实例名推导（`cnt_reg[3]`、`cnt_reg_3_` → `cnt[3]`），否则用 Q 端的 net 名。

### 端点类型

| 标签 | 含义 |
|---|---|
| `REG` / `LATCH` | lib 中带 `ff` / `latch` 的 cell。QN 输出按取反处理 |
| `UNKNOWN` | cell 既不在 lib 中，也不是网表里的模块（SRAM、硬核等） |
| `BLACKBOX` | cell 在 lib 中，但输出没有 `function`（宏、只有 statetable 的单元如 ICG） |
| `PORT-IN` | 顶层输入端口；或跨模块被关闭/超过层数时的模块输入端口 |
| `SUBMOD-OUT` | 子模块输出，跨模块被关闭/超过层数时出现 |
| `INOUT` | inout 端口或三态输出 |
| `ASSIGN-EXPR` | `assign` 右侧是表达式（不解释） |
| `CONSTX` / `UNDRIVEN` / `MULTI-DRIVER` / `LOOP` / `TRUNCATED` | x 常量、无驱动、多驱动、组合环、超过 `--max-nodes` |

## 能还原的形式

每条 `endpoint` 表达式都经过证明：工具把表达式重新算成 BDD，与这根线的函数逐一比对，相同才输出。识别不依赖门的结构，同一个函数用 AND/NAND/NOR/AOI 怎么搭都得到同一结果。

| 形式 | 示例 | 限制 |
|---|---|---|
| 总线与常量比较 | `cnt[3:0] == 5`、`!= 3`、`< 10`、`>= 6`、`cnt[7:0] >= 16 & cnt[7:0] < 200` | 位连续，≤ 64 位 |
| 取值集合 | `state[3:0] inside {5, 9}` | ≤ 8 个值 |
| 总线与总线比较 | `a[5:0] < b[5:0]`、`>=`、`>`、`<=`、`==`、`!=`、`$signed(a) < $signed(b)` | |
| 按状态分支 | `state[3:0] == 5 ? cnt[7:0] >= 200 \| bitmap[pin[3:0]] : state[0]` | 条件总线 ≤ 8 位，≤ 3 个分支 |
| mux | `sel ? a : b`、`case (s[1:0]) {0: a, 1: b, 2: c, 3: d}` | |
| 索引 | `bitmap[idx[3:0]]` | 索引 ≤ 10 位 |
| 变量移位 | `(d[7:0] >> s[2:0])[2]`、`<<`、`$signed(d) >>> s` | 移位量 ≤ 10 位 |
| 加减 | `(cnt[3:0] + 1)[3]`、`(a[7:0] + b[7:0])[8]`（进位）、`(a - b)[7]`、`(a + b + cin)[5]` | 两个操作数；32 位已验证 |
| 乘法 | `(a[3:0] * b[3:0])[5]` | 两操作数位宽之和 ≤ 16 时可证明 |
| 其余 | 分解成 `&`、`\|`、`^`、`?:`，或与或式 | |

需要知道的几点：

- **字级算符按位显示。** 追溯的是单根线，所以是 `(cnt[3:0] + 1)[3]` 这种形式；外面的使能/复位会被剥出来：`!rst & (en ? (cnt[3:0] + 1)[3] : cnt[3])`。
- **只显示实际依赖的位。** `(a + b)` 的第 2 位只依赖低 3 位，显示为 `(a[2:0] + b[2:0])[2]`。
- **常量移位不产生门**，`a >> 3` 的第 0 位就显示为 `a[3]`。
- **有些位天生有两种读法。** `cnt + 37` 的最高位同时是 `cnt >= 91 & cnt < 219`。默认显示范围判断（步长 ≤ 2 的计数器除外）；`--prefer-arith` 显示算术形式。
- **操作数必须是有名字的总线**（寄存器或端口）。操作数本身是中间逻辑（一堆 `n123`）时，退回布尔形式——仍然正确，只是不好读。
- **宽乘法无法证明。** 乘法器的 BDD 随位宽指数增长。此时改用 4096 组随机向量仿真比对，匹配则输出并在行尾标注 `[simulation-matched, unproven]`，Notes 里也会说明。`--strict` 关闭这类输出。
- **逻辑太大时不给端点式。** 该线标 `[CUT]` 或 `<not computed ...>`，局部式照常给出；Notes 会说明数量。可用 `--filter` 缩小范围或 `--effort` 加大上限。

## 实测

机器：16 线程，Windows 11。网表为 `gen_netlist` 生成的合成网表：**619 MB、1180 万行**、846 个模块（其中一个模块 236 万行），文件已在系统缓存中。

| 项目 | 结果 |
|---|---|
| 建立模块索引（扫描整个文件） | 0.56 s |
| 查询普通模块里的线（锥 30–300 位） | 总计 0.55–1.4 s |
| 查询 236 万行大模块里的线 | 总计 3.0 s（其中解析该模块 2.1 s） |
| 查询 5700 位的随机逻辑锥 | 总计 10.5 s（绝大部分线超出上限，只有局部式） |
| 峰值内存（含映射的网表文件本身） | 0.6–1.2 GB |

重现：

```
cargo run --release --bin gen_netlist -- --lines 11800000 --out bench_data/full
target/release/netlist_search --netlist bench_data/full/bench.v --lib bench_data/full/bench.lib \
    --inst u_blk_421 --wire "nstate[0]" --stats
```

`bench_data/full/queries.txt` 列出了一组可用的查询。

## 已知限制

- **没有在真实网表和真实工艺库上验证过。** 全部测试用的是手写夹具和合成网表。Verilog/Liberty 的写法按 DC / Genus 的常见输出实现，遇到没覆盖的写法会报错或给出 warning，届时需要适配。
- 文件第一次读入（不在系统缓存中）时，耗时取决于磁盘。
- 不穿过寄存器继续向前追（只到第一级寄存器）。
- 模块端口上的表达式、实例数组、`assign` 右侧的运算表达式不解释（会有 warning 或 `ASSIGN-EXPR` 端点）。
- 工具运行期间不要修改网表文件（文件是内存映射的）。

## 开发

```
cargo test
```

设计文档见 `docs/superpowers/specs/2026-11-12-netlist-trace-design.md`。
