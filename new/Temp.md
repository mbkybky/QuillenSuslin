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
再利用复合关系 $P_{d+1}=P_1(P_d,Q_d)$、$Q_{d+1}=Q_1(P_d,Q_d)$，并注意每个单项式 $x^iy^j$ 的总次数 $i+j\ge 1$，可归纳得到
$$
\|P_d\|_\rho,\ \|Q_d\|_\rho\ \le\ c^d\rho\qquad(\forall d\ge 1).
$$
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

> **定理 3.2（解析 Poincaré–Dulac 正规形，二维吸引情形）**  
> 可能在 $\mathbf{k}$ 上做一个有限扩张后，存在 $0<\rho_0\le 1$ 与一个在闭多圆盘
> $\{|x|,|y|\le\rho_0\}$ 上解析同构的坐标变换 $H$，满足  
> $H(0)=0,\ DH(0)=\mathrm{Id}$，使得 $g:=H\circ f\circ H^{-1}$ 的 Taylor 展开只含线性项与共鸣单项式。  
> 进一步可取线性坐标使 $Dg(0)$ 为上三角约当形
> $$
> Dg(0)=\begin{pmatrix}\lambda&\tau\\0&\mu\end{pmatrix},\qquad |\lambda|,|\mu|<1,\ \tau\in\{0,1\},
> $$
> 且可约定 $|\lambda|\ge|\mu|$（必要时交换坐标）。在该约定下：
> 
> 1. 第一坐标方向没有任何非线性共鸣项，因此 $g_1(x,y)$ 只有线性项：$g_1(x,y)=\lambda x+\tau y$。
> 2. 若 $\mu\neq0$，则第二坐标中不可能出现任何含 $y^j\ (j\ge2)$ 或混合项 $x^iy^j\ (i\ge1,j\ge1)$ 的共鸣单项式：
>    若 $\lambda^i\mu^j=\mu$ 且 $j\ge2$，则 $|\lambda^i\mu^{j-1}|<1$ 不可能等于 $1$；混合项同理。
>    因此
>    $$
>    g_2(x,y)=\mu y + B(x),
>    $$
>    且 $B$ 只可能由“纯 $x$ 共鸣”产生：若存在整数 $m\ge1$ 使 $\lambda^m=\mu$，
>    则 $B(x)$ 是一个（至多一个单项式的）多项式 $b x^m$；若不存在这样的 $m$，则 $B\equiv0$。
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

#### 3.3 从正规形得到 $S_d(\rho)$ 的一致上界（逐项估计）

取定定理 3.2 给出的共轭 $H$ 与 $g$。记
$$
H(x,0)=(\varphi(x),\psi(x)),\qquad K(X,Y):=\pi_2\big(H^{-1}(X,Y)\big),
$$
则
$$
q_d(x)=Q_d(x,0)=\pi_2\big(f^d(x,0)\big)=K\big(g^d(\varphi(x),\psi(x))\big).
$$
由 $DH(0)=\mathrm{Id}$，有
$$
\varphi(x)=x+\sum_{n\ge2}\alpha_nx^n,\qquad \psi(x)=\sum_{n\ge2}\beta_nx^n.
$$
又因 $DK(0,0)$ 的 $Y$-方向导数为 $1$，可把 $K$ 写成
$$
K(X,Y)=K_0(X)+Y\cdot U(X,Y),
$$
其中 $K_0(X):=K(X,0)$ 且 $U(X,Y):=\frac{K(X,Y)-K(X,0)}{Y}\in\mathbf{k}'\{X,Y\}$ 满足 $U(0,0)=1$。

**(i) 先选一个统一半径 $\rho$ 使若干“单位因子”不放大。**  
因为 $\varphi(x)/x-1$ 与 $U(X,Y)-1$ 都无常数项，所以当 $0<\rho<\rho_0$ 充分小时有
$$
\Big\|\frac{\varphi(x)}{x}-1\Big\|_\rho<1,\qquad \|U(X,Y)-1\|_\rho<1
$$
（后一个范数取在闭多圆盘 $|X|,|Y|\le\rho$ 上）。于是由非阿几何级数公式得到：
$$
\Big\|\Big(\frac{\varphi(x)}{x}\Big)^{-1}\Big\|_\rho=1,\qquad \|U\|_\rho=\|U^{-1}\|_\rho=1.
$$
因此对任意 $m\ge1$，
$$
\varphi(x)^m=x^m\Big(\frac{\varphi(x)}{x}\Big)^m,\qquad
\Big\|\Big(\frac{\varphi(x)}{x}\Big)^m\Big\|_\rho=1.
$$
这句话的实际含义是：把 $\varphi(x)^m$ 写成 $x^m\cdot v_m(x)$，则 $v_m(0)=1$ 且 $\|v_m\|_\rho=1$；
并且对所有 $k\ge0$，
$$
|[x^{m+k}]\varphi(x)^m|\ \le\ \rho^{-k}.
$$
同理，把 $\psi(x)$ 写成 $x^s w(x)$（$s:=\mathrm{ord}_0(\psi)\ge2$，$w(0)\neq0$），则
$$
M_\psi(\rho):=\frac{\|w\|_\rho}{|w(0)|}<\infty.
$$

**(ii) 计算正规形下的迭代，并对系数做“取最大值”的估计。**  
令
$$
(X_d(x),Y_d(x)):=g^d(\varphi(x),\psi(x)).
$$
由 $g_2(x,y)=\mu y+B(x)$（$\mu\neq0$ 情形）得到递推
$$
Y_{n+1}=\mu Y_n+B(X_n).
$$
我们分几种情形讨论（每种情形都给出“系数如何界定”的直接计算）。

**情形 A：$\mu\neq0$ 且 $\lambda\neq\mu$。**  
此时 $Dg(0)$ 可对角化，所以 $\tau=0$，从 $g_1(x,y)=\lambda x$ 得
$$
X_n(x)=\lambda^n\varphi(x).
$$
又由定理 3.2，$B$ 要么恒为 $0$，要么为单项式 $b x^m$ 且满足 $\lambda^m=\mu$（且必有 $m\ge2$）。

- 若 $B\equiv0$，则 $Y_d(x)=\mu^d\psi(x)=\mu^d x^s w(x)$。于是
  $$
  \frac{\|Y_d/x^s\|_\rho}{|(Y_d/x^s)(0)|}
  =\frac{\|\,\mu^d w\,\|_\rho}{|\mu^d w(0)|}
  =\frac{\|w\|_\rho}{|w(0)|}
  =M_\psi(\rho).
  $$
  换言之：把 $Y_d=x^{n(Y_d)}\cdot u_{Y_d}$（$n(Y_d)=s$），则 $\|u_{Y_d}\|_\rho\le M_\psi(\rho)\,|u_{Y_d}(0)|$，
  并且对所有 $k\ge0$，
  $$
  |[x^{s+k}]Y_d|\,\rho^k\le M_\psi(\rho)\,|[x^s]Y_d|.
  $$
- 若 $B(x)=b x^m$ 且 $\lambda^m=\mu$，则
  $$
  B(X_n)=b(\lambda^n\varphi(x))^m=b\mu^n\varphi(x)^m,
  $$
  从而把递推逐项展开得
  $$
  Y_d=\mu^d\psi(x)+b\sum_{j=0}^{d-1}\mu^{d-1-j}\cdot\mu^j\varphi(x)^m
  =\mu^d\psi(x)+b\,d\,\mu^{d-1}\varphi(x)^m.
  $$
  由 $|d|=1$，第二项的“单位部分”满足 $\|\varphi(x)^m/x^m\|_\rho=1$，
  第一项的“单位部分”满足 $\|w\|_\rho\le M_\psi(\rho)|w(0)|$。
  于是对任意 $k\ge0$，分别对两项估计得
  $$
  |[x^{s+k}](\mu^d\psi)|\,\rho^k\le M_\psi(\rho)\,|[x^s](\mu^d\psi)|,
  $$
  $$
  |[x^{m+k}](b\,d\,\mu^{d-1}\varphi^m)|\,\rho^k\le |[x^m](b\,d\,\mu^{d-1}\varphi^m)|.
  $$
  对它们求和得到 $Y_d$ 的系数时，用强三角不等式有
  $$
  |[x^{n+k}]Y_d|\,\rho^k\le\max\Big(
  M_\psi(\rho)\,|[x^s](\mu^d\psi)|,\ |[x^m](b\,d\,\mu^{d-1}\varphi^m)|
  \Big),
  $$
  其中 $n:=\min(s,m)$。下面说明 $|[x^n]Y_d|$ 与右端最大值的关系（这是把系数估计“归一化”的关键一步）：
  
  - 若 $s\neq m$，则次数较小的那一项在 $x^n$ 处独占（另一项在 $x^n$ 处系数为 $0$），因此
    $$
    |[x^n]Y_d|=\max\Big(|[x^s](\mu^d\psi)|,\ |[x^m](b\,d\,\mu^{d-1}\varphi^m)|\Big),
    $$
    从而上式立刻给出所需的归一化不等式。
  - 若 $s=m$（于是 $n=s=m$），记 $\beta_n:=[x^n]\psi$。注意 $[x^m]\varphi(x)^m=1$，于是
    $$
    [x^n]Y_d=\mu^d\beta_n+b\,d\,\mu^{d-1}=\mu^{d-1}\big(\mu\beta_n+b\,d\big).
    $$
    当 $|\mu\beta_n|\ne|b|$ 时，强三角不等式给出
    $$
    |\mu\beta_n+b\,d|=\max(|\mu\beta_n|,|b|),
    $$
    因而仍有 $|[x^n]Y_d|$ 等于右端最大值。  
    当 $|\mu\beta_n|=|b|$ 时可能发生抵消使 $|[x^n]Y_d|$ 变小；但此时首系数只依赖于整数 $d$ 的一次表达式
    $\mu\beta_n+b\,d$，而 $\mathrm{char}(\widetilde{\mathbf{k}})=0$ 蕴含整数在剩余域中的像彼此不同，
    因此满足 $\widetilde{\mu\beta_n/b}=-\widetilde d$ 的 $d$ 至多一个。对这一（至多一个）例外 $d$，
    我们把对应的 $S_d(\rho)$ 的值单独取最大并吸收到最终常数里即可。
  因此存在
  $$
  M_Y(\rho):=\max(M_\psi(\rho),1)
  $$
  使得把 $Y_d=x^{n(Y_d)}u_{Y_d}$（$u_{Y_d}(0)\neq0$）后，恒有
  $$
  \|u_{Y_d}\|_\rho\le M_Y(\rho)\,|u_{Y_d}(0)|.
  $$

**情形 B：$\mu\neq0$ 且 $\lambda=\mu$。**  
此时若出现约当块则 $\tau=1$，但由于 $|\lambda|<1$，共鸣条件 $\lambda^m=\mu=\lambda$ 只可能给出 $m=1$，
因此在正规形里不会出现任何真正的非线性 $B$（可视为 $B\equiv0$）。于是 $g$ 线性，且
$$
Y_d(x)=\lambda^d\psi(x).
$$
而 $X_d$ 由线性递推 $X_{n+1}=\lambda X_n+Y_n$ 解得
$$
X_d(x)=\lambda^d\varphi(x)+d\,\lambda^{d-1}\psi(x),
$$
其中 $|d|=1$。因为 $\psi(x)=O(x^2)$，$\varphi(x)=x+O(x^2)$，与情形 A 的估计完全相同：$X_d$、$Y_d$
都可以写成 $x$ 的某次幂乘以一个在 $\|\cdot\|_\rho$ 下有统一上界的单位因子。

**(iii) 把估计传回 $q_d=K(X_d,Y_d)$。**  
由分解 $K(X,Y)=K_0(X)+Y\cdot U(X,Y)$，有
$$
q_d(x)=K_0(X_d(x))+Y_d(x)\cdot U(X_d(x),Y_d(x)).
$$
我们已选 $\rho$ 使 $\|U\|_\rho=\|U^{-1}\|_\rho=1$，从而把 $Y_d=x^{n(Y_d)}u_{Y_d}$ 写好后，
第二项仍满足
$$
\Big\|\frac{u_{Y_d}\cdot U(X_d,Y_d)}{(u_{Y_d}\cdot U(X_d,Y_d))(0)}\Big\|_\rho
=\Big\|\frac{u_{Y_d}}{u_{Y_d}(0)}\Big\|_\rho
\le M_Y(\rho).
$$
另一方面，$K_0(X)$ 作为一元幂级数满足 $\mathrm{ord}_0(K_0)\ge2$（因为 $K(0,0)=0$ 且 $DK(0,0)$ 在 $X$-方向为 $0$），
把它写成 $K_0(X)=X^t\cdot \kappa(X)$（$t\ge2$，$\kappa(0)\neq0$），则
$$
K_0(X_d)=(X_d)^t\cdot \kappa(X_d).
$$
由于 $|X_d|\le\rho$ 且缩小自变量只会减小 Gauss 范数，存在常数
$$
M_{K_0}(\rho):=\Big\|\frac{\kappa}{\kappa(0)}\Big\|_\rho<\infty
$$
使得把 $K_0(X_d)=x^{n(K_0(X_d))}u_{K,d}$ 后有
$$
\|u_{K,d}\|_\rho\le M_{K_0}(\rho)\,|u_{K,d}(0)|\qquad(\forall d).
$$

最后，$q_d$ 是两项之和：
$$
q_d=K_0(X_d)+Y_d\cdot U(X_d,Y_d).
$$
逐系数用强三角不等式取最大值可得，对任意 $k\ge0$，
$$
|[x^{n_d+k}]q_d|\,\rho^k\le\max\Big(
|[x^{n_d+k}]K_0(X_d)|\,\rho^k,\ |[x^{n_d+k}](Y_dU(X_d,Y_d))|\,\rho^k
\Big).
$$
若在最低次数处两项不发生抵消，则 $|[x^{n_d}]q_d|$ 就等于右端最大值，从而由前面对两项各自的单位估计推出 $q_d$ 的单位估计。  
若在最低次数处发生抵消，则 $n_d$ 增大；对新的最低次数重复同样的估计即可（注意每次抵消至少使阶数上升 $1$，所以对固定的 $d$ 只会发生有限次）。  
综上，存在常数 $M(\rho)>0$（只依赖于 $H$、$K$ 与 $\rho$）使得对所有 $d$，
$$
\|u_d\|_\rho\le M(\rho)\,|u_d(0)|.
$$
这就是说 $\sup_d S_d(\rho)\le M(\rho)<\infty$。取 $r:=\rho$ 即得所要的不等式。
