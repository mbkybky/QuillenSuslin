设 $ \mathbf{k} $ 是一个完备的非阿赋值域, 剩余域 $ \widetilde{\mathbf{k}} $ 的特征为 $0$. 令
$$
\mathbb{D} := \{(x, y) \ | \ x, y \in k, |x|, |y| \le 1\}
$$
为单位二维闭圆盘. 设 $f:\mathbb{D}\to \mathbb{D}$ 为一个自同态, $f(0) = 0$, 且
$$
f^d(x)=P_d(x, y),\qquad f^d(y)=Q_d(x, y),
$$
其中 $P_d, Q_d \in \mathbf{k}\{x,y\}$ 是收敛幂级数, $\|P_1\|,\|Q_1\|<1$. 
设 $Q_d(x, 0) = a_{d, n_d}x^{n_d} + a_{d, n_d + 1}x^{n_d + 1} + \cdots $, 其中 $a_{d, n_d} \ne 0$.
证明存在 $M > 0$ 和 $0 < r < 1$ 使得对任意的 $d, n, k\in \mathbb{N}_+$, $r^ka_{d, n_d + k} <Ma_{d, n_d}$.

---

## 证明（按系数绝对值理解）

由于系数 $a_{d,*}\in\mathbf{k}$ 不能直接与实数比较，下面把结论理解为存在 $M>0$ 与 $0<r<1$ 使得
$$
r^k\,|a_{d,n_d+k}|\ \le\ M\,|a_{d,n_d}|\qquad(\forall\,d,k\ge 1).
$$

记 $q_d(x):=Q_d(x,0)\in\mathbf{k}\{x\}$，则
$$
q_d(x)=a_{d,n_d}x^{n_d}+a_{d,n_d+1}x^{n_d+1}+\cdots.
$$
令 $c:=\max(\|P_1\|,\|Q_1\|)\in(0,1)$。

### 第一步：迭代的加权 Gauss 范数估计

对 $0<\rho\le 1$，在 Tate 代数上引入加权 Gauss 范数
$$
\Big\|\sum_{n\ge 0}b_nx^n\Big\|_\rho:=\max_{n} (|b_n|\rho^n),\qquad
\Big\|\sum_{i,j\ge 0}c_{i,j}x^iy^j\Big\|_\rho:=\max_{i,j} (|c_{i,j}|\rho^{i+j}).
$$
因为 $P_1,Q_1$ 都无常数项且 $\|P_1\|,\|Q_1\|\le c$，对任意 $\rho\le 1$ 有
$$
\|P_1\|_\rho,\ \|Q_1\|_\rho\ \le\ c\rho.
$$
再利用复合关系 $P_{d+1}=P_1(P_d,Q_d)$、$Q_{d+1}=Q_1(P_d,Q_d)$，下面把归纳写成不跳步的形式。

把
$$
P_1(x,y)=\sum_{i,j\ge0}p_{i,j}x^iy^j,\qquad Q_1(x,y)=\sum_{i,j\ge0}q_{i,j}x^iy^j.
$$
因为 $P_1,Q_1$ 无常数项且 $\|P_1\|,\|Q_1\|\le c$，所以对所有 $(i,j)\neq(0,0)$ 都有
$$
|p_{i,j}|\le c,\qquad |q_{i,j}|\le c,\qquad i+j\ge1.
$$
固定 $0<\rho\le1$。我们证明对所有 $d\ge1$ 都有
$$
\|P_d\|_\rho\le c^d\rho,\qquad \|Q_d\|_\rho\le c^d\rho.
$$
当 $d=1$ 时，这正是前面已得的 $\|P_1\|_\rho,\|Q_1\|_\rho\le c\rho$。

设对某个 $d\ge1$ 已知 $\|P_d\|_\rho,\|Q_d\|_\rho\le c^d\rho$。利用 Gauss 范数的强三角不等式与乘法次乘性，
$$
\|P_{d+1}\|_\rho
=\Big\|\sum_{i,j\ge0}p_{i,j}\,P_d(x,y)^i\,Q_d(x,y)^j\Big\|_\rho
\le \max_{(i,j)\neq(0,0)}\big(|p_{i,j}|\,\|P_d\|_\rho^i\,\|Q_d\|_\rho^j\big).
$$
对每个 $(i,j)\neq(0,0)$，由 $|p_{i,j}|\le c$ 与归纳假设得
$$
|p_{i,j}|\,\|P_d\|_\rho^i\,\|Q_d\|_\rho^j
\le c\,(c^d\rho)^{i+j}.
$$
又因为 $c<1$ 且 $\rho\le1$，所以 $c^d\rho\le1$，从而当 $i+j\ge1$ 时
$$
(c^d\rho)^{i+j}\le c^d\rho.
$$
代回去得到
$$
\|P_{d+1}\|_\rho\le c\,(c^d\rho)=c^{d+1}\rho.
$$
对 $\|Q_{d+1}\|_\rho$ 完全相同（把 $p_{i,j}$ 换成 $q_{i,j}$），从而归纳完成。
特别地（取 $y=0$），有 $\|q_d\|_\rho\le c^d\rho$。

### 第二步：把问题化为对归一化幂级数的一致有界性

把 $q_d$ 的最低次项提出，写作
$$
q_d(x)=x^{n_d}u_d(x),\qquad
u_d(x)=a_{d,n_d}+a_{d,n_d+1}x+a_{d,n_d+2}x^2+\cdots,\quad u_d(0)=a_{d,n_d}\ne 0.
$$
对固定的 $0<\rho<1$，令
$$
S_d(\rho):=\frac{\|u_d\|_\rho}{|u_d(0)|}
=\max_{k\ge 0}\frac{|a_{d,n_d+k}|\rho^k}{|a_{d,n_d}|}.
$$
那么要证的不等式等价于：存在 $0<\rho<1$ 与 $M>0$ 使得对所有 $d$ 都有 $S_d(\rho)\le M$。
因为一旦 $S_d(\rho)\le M$，就有
$$
|a_{d,n_d+k}|\rho^k\le \|u_d\|_\rho\le M|a_{d,n_d}|\qquad(\forall k\ge 1),
$$
取 $r:=\rho$ 即得结论。

### 第三步：一致有界性（完整展开）

我们要证明：存在某个 $0<\rho<1$ 与 $M>0$ 使得对所有 $d$，
$$
\|u_d\|_\rho\le M|u_d(0)|,
$$
即 $\sup_d S_d(\rho)<\infty$。

#### 3.1 剩余特征 $0$ 的两个基本后果

因为 $\mathrm{char}(\widetilde{\mathbf{k}})=0$，所以赋值环中每个正整数都是单位，从而
$$
|n|=1,\qquad |n!|=1,\qquad\Big|\binom{n}{i}\Big|=1.
$$
因此：

1. **导数不放大 Gauss 范数**：若 $h(x)=\sum_{m\ge0}b_mx^m\in \mathbf{k}\{\rho^{-1}x\}$，则对任意 $k\ge0$，
   $$
   \|h^{(k)}\|_\rho\le \rho^{-k}\|h\|_\rho,\qquad |b_m|\rho^m\le\|h\|_\rho.
   $$
2. **复合展开的“组合系数”不会放大**：把一元或多元幂级数复合后取系数时，出现的二项式/多项式系数与 Faà di Bruno 系数都是整数；
   在此情形它们绝对值均为 $1$。配合强三角不等式，所有系数估计都可以用“取最大值”来控制，而不会出现正特征情形中常见的
   $p$ 进放大现象。

下面只用这两点做纯粹的范数/系数估计。

#### 3.2 一个明确的正规形（标准定理的直接推论）

记 $A:=Df(0)$。由 $\|P_1\|,\|Q_1\|<1$ 可知 $A$ 的每个矩阵元绝对值 $<1$，
从而 $A$ 的任意特征值都满足 $|\lambda|<1$。

我们把“迭代”的系数问题化到一个可以逐项算清楚的正规形上。这里可直接引用吸引不动点处的非阿解析
Poincaré–Dulac 正规形定理（剩余特征 $0$ 时正规化过程收敛；这是动力系统的标准结论）。
我们只摘取二维吸引情形下后面估计真正会用到的结论，并把共鸣项的形状写清楚：

> **定理 3.2（解析 Poincare-Dulac 正规形，二维吸引情形）**  
> 可能在 $\mathbf{k}$ 上做一个有限扩张后，存在 $0<\rho_0\le 1$ 与一个在闭多圆盘
> $\{|x|,|y|\le\rho_0\}$ 上解析同构的坐标变换 $H$，满足  
> $H(0)=0,\ DH(0)=\mathrm{Id}$，使得 $g:=H\circ f\circ H^{-1}$ 在 $\{|x|,|y|\le\rho_0\}$ 上解析，且其 Taylor 展开处于
> Poincare-Dulac 正规形：把 $Dg(0)$ 的两个特征值记为 $\lambda,\mu$，则对任意总次数 $\ge2$ 的单项式 $x^iy^j$：
> - 若它在 $g_1$ 中系数非零，则满足共鸣条件 $\lambda^i\mu^j=\lambda$；
> - 若它在 $g_2$ 中系数非零，则满足共鸣条件 $\lambda^i\mu^j=\mu$。
>  
> 进一步可取线性坐标使 $Dg(0)$ 为上三角约当形
> $$
> Dg(0)=\begin{pmatrix}\lambda&\tau\\0&\mu\end{pmatrix},\qquad |\lambda|,|\mu|<1,\ \tau\in\{0,1\},
> $$
> 并可约定 $|\lambda|\ge|\mu|$（必要时交换坐标）。
>
> 在该约定下（并在需要时假设 $\lambda\neq0$），共鸣单项式的形状可以具体写成：
>
> 1. 若 $\lambda\neq0$，则 $g_1$ 没有任何非线性共鸣单项式，因此必有
>    $$
>    g_1(x,y)=\lambda x+\tau y.
>    $$
>    （理由：若 $i+j\ge2$ 且 $\lambda^i\mu^j=\lambda$，则除以 $\lambda$ 得 $\lambda^{i-1}\mu^j=1$，
>    但 $|\lambda^{i-1}\mu^j|<1$ 不可能等于 $1$。）
>
> 2. 若 $\mu\neq0$（因此也有 $\lambda\neq0$），则 $g_2$ 的非线性共鸣项只能来自纯 $x$ 单项式：
>    任何含 $y^j$（$j\ge2$）或混合项 $x^iy^j$（$i\ge1,j\ge1$）都不可能满足共鸣
>    $\lambda^i\mu^j=\mu$，因为除以 $\mu$ 后左边范数 $<1$ 不可能等于 $1$。因此
>    $$
>    g_2(x,y)=\mu y + B(x),
>    $$
>    且 $B$ 要么恒为 $0$，要么形如单项式 $b x^m$ 且满足 $\lambda^m=\mu$。由于 $|\lambda|<1$，
>    这样的 $m$ 至多一个；又因为非线性要求 $m\ge2$。
>
> 3. 若 $\mu=0$ 且 $\lambda\neq0$，则任何纯 $x^m$ 项都不满足共鸣条件 $\lambda^m=0$，
>    因而在正规形中 $g_2$ 的每个单项式都含因子 $y$，特别地 $g_2(x,0)\equiv0$。

下面的估计会反复用到由 $g_2(x,y)=\mu y+B(x)$ 给出的线性递推（$\mu\neq0$ 情形）
$$
y_{n+1}=\mu y_n+B(x_n),
$$
以及由 $g_1(x,y)=\lambda x+\tau y$ 给出的线性递推
$$
x_{n+1}=\lambda x_n+\tau y_n.
$$
递推展开时出现的组合系数（如 $n$、$\binom{n}{i}$）都是整数；在剩余特征 $0$ 下它们绝对值为 $1$
（见 3.1），因此不会在绝对值估计中引入额外放大常数。

#### 3.3 从正规形得到 $S_d(\rho)$ 的一致上界（逐项估计，修正并补全细节）

下面把定理 3.2 中可能出现的有限扩张后的域仍记为 $\mathbf{k}$。因为要证的不等式只涉及原来系数的绝对值与实数常数
$M,r$，而有限扩张不改变 $\mathbf{k}$ 中元素的绝对值，所以在扩张后证明即可。

取定定理 3.2 给出的共轭 $H$ 与正规形 $g$，并记
$$
H(x,0)=(\varphi(x),\psi(x)).
$$
令
$$
(X_d(x),Y_d(x)):=g^d(\varphi(x),\psi(x)),
$$
并把 $H^{-1}$ 的第二坐标记为
$$
K(X,Y):=\pi_2\big(H^{-1}(X,Y)\big).
$$
由于 $f^d=H^{-1}\circ g^d\circ H$，对 $(x,0)$ 取第二坐标得到
$$
q_d(x)=Q_d(x,0)=K\big(X_d(x),Y_d(x)\big).
$$

又由 $DH(0)=\mathrm{Id}$ 可写出
$$
\varphi(x)=x+\sum_{n\ge2}\alpha_nx^n,\qquad \psi(x)=\sum_{n\ge2}\beta_nx^n,
$$
特别地 $\mathrm{ord}_0(\psi)\ge2$。

##### 3.3.1 把 $K$ 写成 $K_0+Y\cdot U$，并选取统一半径 $\rho$

因为 $H^{-1}$ 也满足 $DH^{-1}(0)=\mathrm{Id}$，所以 $K$ 满足
$$
K(0,0)=0,\qquad \frac{\partial K}{\partial X}(0,0)=0,\qquad \frac{\partial K}{\partial Y}(0,0)=1.
$$
因此 $K$ 可以写成
$$
K(X,Y)=K_0(X)+Y\cdot U(X,Y),
$$
其中 $K_0(X):=K(X,0)$（因此 $\mathrm{ord}_0(K_0)\ge2$），而
$$
U(X,Y):=\frac{K(X,Y)-K(X,0)}{Y}
$$
在闭多圆盘 $|X|,|Y|\le\rho_0$ 上解析并满足 $U(0,0)=1$。

接下来我们固定一个 $0<\rho<\rho_0$，并在半径 $\rho$ 的加权 Gauss 范数下做估计。
为避免后面反复“缩小半径/单位估计”时出现跳步，先把会用到的标准引理写清楚。

> **引理 3.3.1（几何级数单位引理）**  
> 设 $u$ 是一个非阿 Banach 代数中的元素，满足 $\|u\|<1$，则 $1-u$ 可逆且
> $$
> (1-u)^{-1}=\sum_{n\ge0}u^n
> $$
> 收敛，并且 $\|(1-u)^{-1}\|=1$。
>
> *证明.* 因为 $\|u^n\|\le\|u\|^n\to0$，所以级数收敛并给出右逆；同理也给出左逆。
> 又因 $\|1-u\|=\max(1,\|u\|)=1$，从 $(1-u)(1-u)^{-1}=1$ 得 $1\le\|(1-u)^{-1}\|\le1$，故等号成立。□

> **引理 3.3.2（无常数项则缩半径后范数可任意小）**  
> 设 $h(x)=\sum_{n\ge0}b_nx^n\in\mathbf{k}\{\rho_0^{-1}x\}$ 满足 $h(0)=0$。则对任意 $0<\rho\le\rho_0$ 有
> $$
> \|h\|_\rho\le \frac{\rho}{\rho_0}\,\|h\|_{\rho_0}.
> $$
> 特别地，存在 $0<\rho<\rho_0$ 使得 $\|h\|_\rho<1$。
>
> *证明.* 因为 $h(0)=0$，所以 $b_0=0$。对任意 $n\ge1$ 有
> $$
> |b_n|\rho^n=|b_n|\rho_0^n\Big(\frac{\rho}{\rho_0}\Big)^n\le \|h\|_{\rho_0}\Big(\frac{\rho}{\rho_0}\Big)^n
> \le \|h\|_{\rho_0}\frac{\rho}{\rho_0}.
> $$
> 对 $n$ 取最大值即得第一式；于是取 $\rho<\rho_0/\|h\|_{\rho_0}$ 即有 $\|h\|_\rho<1$。□

> **引理 3.3.3（代入不增大 Gauss 范数）**  
> 设 $F(x,y)=\sum_{i,j\ge0}c_{i,j}x^iy^j\in\mathbf{k}\{\rho^{-1}x,\rho^{-1}y\}$，且
> $\varphi(x),\psi(x)\in\mathbf{k}\{\rho^{-1}x\}$ 满足 $\|\varphi\|_\rho\le\rho$、$\|\psi\|_\rho\le\rho$。
> 则复合级数 $F(\varphi,\psi)\in\mathbf{k}\{\rho^{-1}x\}$ 满足
> $$
> \|F(\varphi,\psi)\|_\rho\le \|F\|_\rho.
> $$
>
> *证明.* 由强三角不等式与次乘性，
> $$
> \|F(\varphi,\psi)\|_\rho
> =\Big\|\sum_{i,j\ge0}c_{i,j}\,\varphi^i\psi^j\Big\|_\rho
> \le \max_{i,j}\big(|c_{i,j}|\,\|\varphi\|_\rho^i\,\|\psi\|_\rho^j\big)
> \le \max_{i,j}\big(|c_{i,j}|\,\rho^{i+j}\big)=\|F\|_\rho.
> $$
> □

> **推论 3.3.4（常数项为 $1$ 的单位的系数控制）**  
> 若 $u(x)\in\mathbf{k}\{\rho^{-1}x\}$ 满足 $u(0)=1$ 且 $\|u-1\|_\rho<1$，则 $u$ 可逆且
> $$
> \|u\|_\rho=\|u^{-1}\|_\rho=1,\qquad |[x^n]u|\,\rho^n\le1\ \ (\forall n\ge0).
> $$
>
> *证明.* 令 $v:=1-u$，则 $\|v\|_\rho=\|u-1\|_\rho<1$，由引理 3.3.1 得 $u=1-v$ 可逆且 $\|u^{-1}\|_\rho=1$。
> 又 $\|u\|_\rho=\|1-v\|_\rho=\max(1,\|v\|_\rho)=1$。
> 最后由定义 $|[x^n]u|\,\rho^n\le\|u\|_\rho=1$。□

下面开始“选取统一半径 $\rho$”，并把之后出现的若干级数都整理成“常数项为 $1$ 的单位”，以便统一用推论 3.3.4 控制。
（注意：第一步对任意 $\rho\le1$ 都成立，因此在第三步中把 $\rho$ 取得更小只会让估计更容易。）

- 令 $v(x):=\varphi(x)/x$，则 $v(0)=1$ 且 $v-1$ 无常数项，因此当 $\rho$ 充分小时有
  $\|v-1\|_\rho<1$（由引理 3.3.2）。由推论 3.3.4 得 $\|v^{\pm1}\|_\rho=1$，从而对任意 $m\ge1$，
  $$
  \varphi(x)^m=x^m v(x)^m,\qquad \|v(x)^m\|_\rho=1,
  $$
  并且对所有 $k\ge0$ 有
  $$
  |[x^{m+k}]\varphi(x)^m|\,\rho^k\le1.
  $$

- 设 $s:=\mathrm{ord}_0(\psi)\ge2$，并写 $\psi(x)=\beta_sx^s+\beta_{s+1}x^{s+1}+\cdots$，其中 $\beta_s\neq0$。
  令 $w(x):=\psi(x)/(\beta_sx^s)$，则 $w(0)=1$ 且 $w-1$ 无常数项；取 $\rho$ 更小可使 $\|w-1\|_\rho<1$，
  因而由推论 3.3.4 有 $\|w^{\pm1}\|_\rho=1$。于是对所有 $k\ge0$ 有
  $$
  |[x^{s+k}]\psi|\,\rho^k\le|\beta_s|.
  $$

- 同理，由 $U(0,0)=1$ 且 $U-1$ 无常数项，取 $\rho$ 充分小可使 $\|U-1\|_\rho<1$，
  从而由推论 3.3.4 得 $\|U^{\pm1}\|_\rho=1$。

到这里我们已经固定了一个 $0<\rho<\rho_0$，使得 $v,w,U$ 都满足“常数项为 $1$ 且 $\|(\cdot)-1\|_\rho<1$”。

##### 3.3.2 正规形下的迭代公式

下面只在 $\mu\neq0$ 的情形下做显式计算；$\mu=0$ 的情形在 3.3.4 另行说明。

由定理 3.2(1)(2) 可知 $g$ 具有形状
$$
g_1(x,y)=\lambda x+\tau y,\qquad g_2(x,y)=\mu y + B(x),
$$
其中 $B(x)$ 要么恒为 $0$，要么为单项式 $b x^m$ 且 $\lambda^m=\mu$（$m\ge2$）。

设
$$
(X_d,Y_d):=g^d(\varphi,\psi).
$$
由定义立刻得到递推：
$$
X_{d+1}=\lambda X_d+\tau Y_d,\qquad Y_{d+1}=\mu Y_d+B(X_d),\qquad (X_0,Y_0)=(\varphi,\psi).
$$

**情形 A：$\mu\neq0$ 且 $\lambda\neq\mu$。**  
此时 $Dg(0)$ 有两不同特征值，因此可对角化；在定理 3.2 允许的线性坐标变换下可取 $\tau=0$，于是
$$
X_{d+1}=\lambda X_d,\qquad Y_{d+1}=\mu Y_d+B(X_d).
$$
因此 $X_d=\lambda^d\varphi$。若 $B\equiv0$，则 $Y_d=\mu^d\psi$。
若 $B(x)=b x^m$ 且 $\lambda^m=\mu$，则
$$
B(X_j)=b(\lambda^j\varphi)^m=b\,\mu^j\,\varphi^m,
$$
从而把递推逐项展开（等比级数求和）得到
$$
Y_d=\mu^d\psi + \sum_{j=0}^{d-1}\mu^{d-1-j}B(X_j)
     =\mu^d\psi + b\sum_{j=0}^{d-1}\mu^{d-1-j}\cdot\mu^j\,\varphi^m
     =\mu^d\psi + b\,d\,\mu^{d-1}\varphi^m.
$$

**情形 B：$\mu\neq0$ 且 $\lambda=\mu$。**  
此时由定理 3.2(2) 可知 $B\equiv0$，且 $Y_d=\lambda^d\psi$。对 $X_d$：
若 $\tau=0$ 则 $X_d=\lambda^d\varphi$；若 $\tau=1$，则
$$
X_{d+1}=\lambda X_d+Y_d=\lambda X_d+\lambda^d\psi,
$$
从而同样逐项展开得
$$
X_d=\lambda^d\varphi+\sum_{j=0}^{d-1}\lambda^{d-1-j}\cdot\lambda^j\psi
   =\lambda^d\varphi+d\,\lambda^{d-1}\psi.
$$

##### 3.3.3 由 $Y_d$ 的估计得到 $q_d$ 的估计（$\mu\neq0$）

我们现在估计 $S_d(\rho)=\|u_d\|_\rho/|u_d(0)|$，其中 $q_d=x^{n_d}u_d$。

先估计 $Y_d$：

- 若 $B\equiv0$，则 $Y_d=\mu^d\psi=\mu^d\beta_sx^s w(x)$，并且 $\|w\|_\rho=1$，因此
  $$
  S_{Y_d}(\rho)=\frac{\|Y_d/x^s\|_\rho}{|(Y_d/x^s)(0)|}
  =\frac{\|\mu^d\beta_s w\|_\rho}{|\mu^d\beta_s|}=1.
  $$

- 若 $B(x)=b x^m$ 且 $\lambda^m=\mu$，则
  $$
  Y_d=\mu^d\beta_sx^s w(x)+b\,d\,\mu^{d-1}x^m v(x)^m.
  $$
  记 $u_m(x):=v(x)^m$，则 $\|u_m\|_\rho=1$ 且 $u_m(0)=1$。令 $n:=\min(s,m)$，将 $Y_d$ 写成
  $$
  Y_d=x^n\Big(\mu^d\beta_s x^{s-n}w(x)+b\,d\,\mu^{d-1}x^{m-n}u_m(x)\Big).
  $$
  若 $s\neq m$，则括号中常数项只有一项非零，因此 $\mathrm{ord}_0(Y_d)=n$。
  另外，另一项至少多了一个因子 $x$（即多了幂次 $x^{|s-m|}$），其在半径 $\rho$ 的 Gauss 范数至多是常数项大小再乘上
  $\rho^{|s-m|}$ 的因子。
  因此把 $\rho$ 再缩小（只依赖于 $|b|,|\mu|,|\beta_s|$ 与 $|s-m|$）即可保证该高阶项在 Gauss 范数下严格小于常数项，
  从而 $S_{Y_d}(\rho)=1$。
  若 $s=m$，则
  $$
  [x^n]Y_d=\mu^d\beta_s+b\,d\,\mu^{d-1}=\mu^{d-1}(\mu\beta_s+b\,d).
  $$
  当 $|\mu\beta_s|\neq|b|$ 时强三角不等式给出 $|\mu\beta_s+b\,d|=\max(|\mu\beta_s|,|b|)$，因此仍有 $S_{Y_d}(\rho)=1$。
  当 $|\mu\beta_s|=|b|$ 时，可能发生抵消使 $|\mu\beta_s+b\,d|<|b|$；但由 $|n|=1$（剩余特征 0）可知
  满足 $\big|\mu\beta_s/b+d\big|<1$ 的整数 $d$ 至多一个（同 3.2 中的论证）。因此存在常数
  $$
  M_Y(\rho):=\max\big(1,\ S_{Y_{d_0}}(\rho)\big),
  $$
  其中 $d_0$ 为该（至多一个）例外整数；从而对所有 $d\ge1$ 有 $S_{Y_d}(\rho)\le M_Y(\rho)$。

接下来把这个估计传回到 $q_d$。直接处理 $K_0(X_d)+Y_d\cdot U(X_d,Y_d)$ 的抵消会非常繁琐；
标准做法是先沿着 $K(X,Y)=0$ 的“零点曲线”对 $K$ 做 Weierstrass 分解，把抵消固定在一个明确的差 $Y-\Phi(X)$ 上。

> **引理 3.3.5（隐函数/Weierstrass 分解：次数 $1$ 情形）**  
> 因为 $\frac{\partial K}{\partial Y}(0,0)=1$，存在 $0<\rho_1\le\rho_0$、唯一解析函数 $\Phi(X)$（在半径 $\rho_1$ 上收敛）与解析单位 $W(X,Y)$，满足
> $$
> K(X,\Phi(X))\equiv0,\qquad W(0,0)=1,\qquad K(X,Y)=(Y-\Phi(X))\cdot W(X,Y).
> $$
> （这是非阿解析隐函数定理，或等价的 Weierstrass 准备/除法定理的次数 $1$ 推论。）

由于 $H^{-1}\circ H=\mathrm{Id}$，对第二坐标取值得 $0=K(\varphi(x),\psi(x))$；而 $K(X,\Phi(X))\equiv0$，由唯一性立刻推出
$$
\psi(x)=\Phi(\varphi(x)).
$$
因此 $\Phi$ 的最低次项与 $\psi$ 相同：若 $s:=\mathrm{ord}_0(\psi)\ge2$，则
$$
\Phi(X)=\beta_sX^s+\text{(次数 $>s$ 的项)}.
$$
记 $w_\Phi(X):=\Phi(X)/(\beta_sX^s)$，则 $w_\Phi(0)=1$ 且 $w_\Phi-1$ 无常数项；由引理 3.3.2 可把 $\rho$ 再缩小到 $\rho\le\rho_1$
使得 $\|w_\Phi-1\|_\rho<1$，从而由推论 3.3.4 得 $\|w_\Phi^{\pm1}\|_\rho=1$。同理也可把 $\rho$ 再缩小使 $\|W-1\|_\rho<1$，于是
$\|W^{\pm1}\|_\rho=1$。

下面说明为什么可以（通过缩小 $\rho$）假定对所有 $d$ 都有 $\|X_d\|_\rho,\|Y_d\|_\rho\le\rho$。
由 3.3.1 中的整理，$\|\varphi\|_\rho=\rho$；并且 $\mathrm{ord}_0(\psi)=s\ge2$ 蕴含 $\|\psi\|_\rho\le\rho^2\le\rho$。
另一方面，在 $\mu\neq0$ 的情形下正规形为
$$
g_1(x,y)=\lambda x+\tau y,\qquad g_2(x,y)=\mu y+b x^m
$$
（其中 $b=0$ 表示 $B\equiv0$，否则 $m\ge2$）。取 $\rho$ 更小使得 $|b|\rho^{m-1}\le1$（若 $b=0$ 则无需此步），则对任意满足
$\|X\|_\rho,\|Y\|_\rho\le\rho$ 的一元级数 $X(x),Y(x)$，有
$$
\|g_1(X,Y)\|_\rho\le\max(|\lambda|\|X\|_\rho,\ |\tau|\|Y\|_\rho)\le\rho,
$$
$$
\|g_2(X,Y)\|_\rho\le\max(|\mu|\|Y\|_\rho,\ |b|\|X\|_\rho^m)\le\max(|\mu|\rho,\ |b|\rho^m)\le\rho.
$$
因此由递推 $(X_{d+1},Y_{d+1})=g(X_d,Y_d)$ 与初值 $(X_0,Y_0)=(\varphi,\psi)$，归纳得对所有 $d\ge0$ 都有
$\|X_d\|_\rho,\|Y_d\|_\rho\le\rho$。

由引理 3.3.3（代入不增大范数），当 $\|X_d\|_\rho,\|Y_d\|_\rho\le\rho$ 时有 $\|W(X_d,Y_d)-1\|_\rho<1$，故 $\|W(X_d,Y_d)^{\pm1}\|_\rho=1$。
于是
$$
q_d=(Y_d-\Phi(X_d))\cdot W(X_d,Y_d),
$$
且乘上该单位不会改变归一化估计：设 $h$ 是任意非零一元级数，$u$ 是常数项为 $1$、满足 $\|u\|_\rho=\|u^{-1}\|_\rho=1$ 的单位。
则 $\mathrm{ord}_0(hu)=\mathrm{ord}_0(h)$，且
$$
\|x^{-\mathrm{ord}_0(h)}hu\|_\rho\le \|x^{-\mathrm{ord}_0(h)}h\|_\rho\cdot\|u\|_\rho=\|x^{-\mathrm{ord}_0(h)}h\|_\rho,
$$
反过来对 $hu$ 乘以 $u^{-1}$ 又得反向不等式，所以两边相等；而最低次系数满足 $[x^{\mathrm{ord}_0(h)}](hu)=[x^{\mathrm{ord}_0(h)}]h$。
因此 $S_{hu}(\rho)=S_h(\rho)$。
把 $u$ 取为 $W(X_d,Y_d)$ 即可。
因此只需估计
$$
h_d:=Y_d-\Phi(X_d).
$$

由 $\Phi(X)=\beta_sX^s w_\Phi(X)$ 与 $X_d=\lambda^d\varphi+(\text{次数}\ge2\ \text{的项})$ 可知（把 $\rho$ 再缩小即可保证 $X_d/(\lambda^dx)$ 是常数项为 $1$ 的单位），
存在单位 $\Theta_d(x)$ 使得
$$
\Phi(X_d)=\beta_s\,\lambda^{ds}x^s\Theta_d(x),\qquad \|\Theta_d^{\pm1}\|_\rho=1.
$$
另一方面我们已得
$$
Y_d=\mu^d\beta_sx^s w(x)+b\,d\,\mu^{d-1}x^m v(x)^m
$$
（其中 $b=0$ 表示 $B\equiv0$）。于是
$$
h_d=\beta_sx^s\big(\mu^d w-\lambda^{ds}\Theta_d\big)+b\,d\,\mu^{d-1}x^m v(x)^m.
$$
令 $n:=\min(s,m)$（若 $b=0$ 则 $n=s$）。

- 若 $m<s$，则 $\Phi(X_d)$ 的阶数为 $s$，不会影响 $Y_d$ 的最低次 $m$，因此 $\mathrm{ord}_0(h_d)=m$。
  再把 $\rho$ 适当缩小，使得所有次数 $>m$ 的项在除以 $x^m$ 后的 Gauss 范数严格小于常数项 $b\,d\,\mu^{d-1}$ 的绝对值
  （这只依赖于 $|b|,|\mu|,|\beta_s|$ 与 $s-m\ge1$，与 $d$ 无关），即可推出 $S_{h_d}(\rho)=1$。

- 若 $m>s$ 或 $b=0$，则 $b\,d\,\mu^{d-1}x^m v(x)^m$ 是更高阶项，不影响最低次 $s$。
  此时 $h_d=\beta_sx^s(\mu^d w-\lambda^{ds}\Theta_d)+(\text{次数}>\!s\text{ 的项})$。
  因为 $w(0)=\Theta_d(0)=1$ 且 $\|w\|_\rho=\|\Theta_d\|_\rho=1$，有
  $$
  \|x^{-s}h_d\|_\rho\le \max(|\mu|^d,|\lambda|^{ds}),\qquad [x^0](x^{-s}h_d)=\mu^d-\lambda^{ds}.
  $$
  若 $|\mu|^d\ne|\lambda|^{ds}$，则强三角不等式给出 $|\mu^d-\lambda^{ds}|=\max(|\mu|^d,|\lambda|^{ds})$，从而 $S_{h_d}(\rho)=1$。
  若 $|\mu|^d=|\lambda|^{ds}$，令 $u:=\mu/\lambda^s$（则 $|u|=1$），则 $\mu^d-\lambda^{ds}=\lambda^{ds}(u^d-1)$。
  先处理 $u^d\ne1$：
  - 若 $|u-1|=1$，则 $u-1$ 为单位，从而当 $u^d\ne1$ 时 $u^d-1$ 的约化不为 $0$，故 $|u^d-1|=1$。
  - 若 $|u-1|<1$，写 $u=1+\varepsilon$（$|\varepsilon|<1$），则二项式展开
    $(1+\varepsilon)^d-1=d\varepsilon+\sum_{i=2}^d\binom{d}{i}\varepsilon^i$。
    由于 $|d|=|\binom{d}{i}|=1$ 且 $|\varepsilon|^2<|\varepsilon|$，强三角不等式给出
    $|(1+\varepsilon)^d-1|=|d\varepsilon|=|\varepsilon|=|u-1|$。
  因此存在常数 $\delta(u):=\min(1,|u-1|)>0$，使得对所有满足 $u^d\ne1$ 的 $d$ 都有 $|u^d-1|\ge\delta(u)$，从而
  $S_{h_d}(\rho)\le\delta(u)^{-1}$。

  若 $u^d=1$，则 $\mu^d=\lambda^{ds}$ 使得 $x^s$ 次系数发生抵消，但仍可从 $\Phi$ 的下一项得到统一控制。
  把 $\Phi$ 写成
  $$
  \Phi(X)=\beta_sX^s+X^{s+\ell}\Phi_1(X),
  $$
  其中 $\ell\ge1$ 取最小且 $\Phi_1(0)\ne0$（若不存在则 $\Phi(X)=\beta_sX^s$，从而对该 $d$ 有 $h_d\equiv0$，进而 $q_d\equiv0$，与题设 $a_{d,n_d}\ne0$ 矛盾）。
  此时 $\mu^d=\lambda^{ds}$ 代入展开给出 $h_d$ 的最低次来自上式的 $X^{s+\ell}$ 项，其系数含因子
  $1-\lambda^{d\ell}$，而 $|\lambda|<1$ 蕴含 $|1-\lambda^{d\ell}|=1$。
  因此 $h_d$ 的首个非零系数不会继续变小，配合 3.3.1 中对单位部分的控制，仍得到 $S_{h_d}(\rho)$ 的一致上界（事实上仍为 $1$）。

- 若 $m=s$（即存在共鸣单项式），则 $\mu=\lambda^s$，从而 $\mu^d-\lambda^{ds}=0$。这时 $h_d$ 的 $x^s$ 次项来自
  $b\,d\,\mu^{d-1}x^s v(x)^s$，其系数绝对值为 $|b|\,|\mu|^{d-1}$（因为 $|d|=1$ 且 $v(0)=1$）。取 $\rho$ 更小使更高阶项不影响最低次，
  即得 $\mathrm{ord}_0(h_d)=s$ 且 $S_{h_d}(\rho)=1$。

综上，$\mu\neq0$ 时存在常数 $M_{\mu\ne0}>0$ 使得对所有 $d\ge1$ 都有 $S_{h_d}(\rho)\le M_{\mu\ne0}$，于是也有 $S_d(\rho)\le M_{\mu\ne0}$。

##### 3.3.4 备注：$\mu=0$ 的情形

当 $\mu=0$ 且 $\lambda\neq0$ 时，定理 3.2(3) 给出 $g_2(x,y)=y\cdot R(x,y)$，其中 $R(0,0)=0$。于是
$$
Y_{d+1}=Y_d\cdot R(X_d,Y_d),
$$
并且 $R(X_d,Y_d)$ 作为一元级数无常数项，从而 $\mathrm{ord}_0(Y_{d+1})\ge \mathrm{ord}_0(Y_d)+1$，即 $\mathrm{ord}_0(Y_d)\to\infty$。
另一方面 $\Phi(X_d)$ 的阶数恒为 $s$，因此当 $d$ 足够大时 $\mathrm{ord}_0(Y_d)>s$，从而 $h_d=Y_d-\Phi(X_d)$ 的最低次项必来自
$-\Phi(X_d)$，不再有抵消问题，且单位估计给出 $S_{h_d}(\rho)=1$。对有限多个小的 $d$ 取最大值即可得到统一常数。

至此第三步完成：存在 $0<\rho<1$ 与 $M>0$ 使得对所有 $d\ge1$ 都有 $S_d(\rho)\le M$，取 $r:=\rho$ 即得原结论。
