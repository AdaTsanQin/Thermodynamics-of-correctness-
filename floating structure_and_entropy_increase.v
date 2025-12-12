(* ========================================================== *)
(* Coq Model: PDF-Based Ensemble Float (Final Version)        *)
(* 修复：Proof Irrelevance, Unification, Placeholder Errors   *)
(* ========================================================== *)

Require Import Reals.
Require Import Psatz.
(* [修复1] 引入证明无关性公理，这是证明区间相等的关键 *)
Require Import Coq.Logic.ProofIrrelevance.

Open Scope R_scope.

(* ========================================================== *)
(* 1. 基础定义                                                *)
(* ========================================================== *)

Definition PDF := R -> R.

Record Interval := mkInterval {
    lower : R;
    upper : R;
    valid_int : lower < upper
}.

(* [修复2] 显式引理：解决占位符无法推导的问题 *)
Lemma valid_bounds : forall mu delta, 0 < delta -> mu - delta < mu + delta.
Proof.
  intros. lra.
Qed.

(* [修复3] 区间相等引理：如果边界数值相等，则区间对象相等 *)
(* 这解决了 Unification Error，让 Coq 承认 (a+b) 和 (c+d) 构成的区间是同一个 *)
Lemma interval_eq : forall (I1 I2 : Interval),
  lower I1 = lower I2 -> upper I1 = upper I2 -> I1 = I2.
Proof.
  intros. destruct I1, I2. simpl in *. subst.
  (* 使用 proof_irrelevance 忽略证明项的差异 *)
  assert (valid_int0 = valid_int1). { apply proof_irrelevance. } 
  subst. reflexivity.
Qed.

Parameter is_supported_on : PDF -> Interval -> Prop.

(* 均匀分布 *)
Parameter UniformPDF : Interval -> PDF.

Axiom Uniform_is_supported : forall (I : Interval),
  is_supported_on (UniformPDF I) I.

(* 熵 *)
Parameter Entropy : PDF -> R.

(* 【公理 1】：最大熵原理 *)
Axiom Max_Entropy_Bound : forall (p : PDF) (I : Interval),
  is_supported_on p I -> Entropy p <= Entropy (UniformPDF I).

(* ========================================================== *)
(* 2. 卷积与运算公理                                          *)
(* ========================================================== *)

Parameter Convolution : PDF -> PDF -> PDF.

(* 区间加法 *)
Program Definition add_interval (I1 I2 : Interval) : Interval :=
  mkInterval (lower I1 + lower I2) (upper I1 + upper I2) _.
Next Obligation. destruct I1, I2; simpl; lra. Qed.

(* 卷积的支撑集是区间之和 *)
Axiom Convolution_Support : forall (p1 p2 : PDF) (I1 I2 : Interval),
  is_supported_on p1 I1 ->
  is_supported_on p2 I2 ->
  is_supported_on (Convolution p1 p2) (add_interval I1 I2).

(* 【公理 2】：卷积熵减原理 *)
(* 两个均匀分布卷积后的熵，严格小于其总区间上均匀分布的熵 *)
Axiom Convolution_Lose_Entropy : forall (I1 I2 : Interval),
  Entropy (Convolution (UniformPDF I1) (UniformPDF I2)) < 
  Entropy (UniformPDF (add_interval I1 I2)).

(* ========================================================== *)
(* 3. 浮点数模型 (FloatEnsemble)                              *)
(* ========================================================== *)

Record FloatEnsemble := mkFloat {
    mu : R;
    delta : R;
    valid_delta : 0 < delta;
    
    density : PDF;
    
    (* 使用显式引理 *)
    support_proof : is_supported_on density 
       (mkInterval (mu - delta) (mu + delta) (valid_bounds mu delta valid_delta))
}.

(* ========================================================== *)
(* 4. 运算定义                                                *)
(* ========================================================== *)

(* --- 4.1 粗粒化 (Coarse Graining) --- *)
(* 将任意分布强制重置为均匀分布 *)
Program Definition coarse_grain (F : FloatEnsemble) : FloatEnsemble :=
  mkFloat 
    (mu F) 
    (delta F) 
    (valid_delta F)
    (UniformPDF (mkInterval (mu F - delta F) (mu F + delta F) 
                (valid_bounds (mu F) (delta F) (valid_delta F))))
    _.
Next Obligation.
  apply Uniform_is_supported.
Qed.

(* --- 4.2 精确加法 (Exact Addition) --- *)
Program Definition exact_add (X Y : FloatEnsemble) : FloatEnsemble :=
  mkFloat
    (mu X + mu Y)
    (delta X + delta Y)
    _ (* Obligation 1: 证明新的 delta > 0 *)
    (Convolution (density X) (density Y))
    _. (* Obligation 2: 证明 Support 匹配 *)

(* 证明 Obligation 1: 新的误差半径为正 *)
Next Obligation.
  destruct X, Y; simpl; lra.
Qed.

(* 证明 Obligation 2: 解决 Unification Error 的核心 *)
Next Obligation.
  (* 1. 获取卷积的原始性质 *)
  (* 注意：I_conv 的边界是 (mu X - delta X) + (mu Y - delta Y) *)
  pose proof (Convolution_Support (density X) (density Y) 
    (mkInterval (mu X - delta X) (mu X + delta X) (valid_bounds (mu X) (delta X) (valid_delta X)))
    (mkInterval (mu Y - delta Y) (mu Y + delta Y) (valid_bounds (mu Y) (delta Y) (valid_delta Y)))
    (support_proof X) (support_proof Y)) as H_conv.
  
  (* 2. 定义目标区间 (即 mkFloat 要求的区间) *)
  (* 目标区间的边界是 (mu X + mu Y) - (delta X + delta Y) *)
  set (I_target := mkInterval (mu X + mu Y - (delta X + delta Y)) 
                              (mu X + mu Y + (delta X + delta Y)) 
                              (valid_bounds (mu X + mu Y) (delta X + delta Y) (exact_add_obligation_1 X Y))).
  
  (* 3. 定义卷积公理生成的区间 *)
  set (I_source := add_interval 
      (mkInterval (mu X - delta X) (mu X + delta X) (valid_bounds (mu X) (delta X) (valid_delta X))) 
      (mkInterval (mu Y - delta Y) (mu Y + delta Y) (valid_bounds (mu Y) (delta Y) (valid_delta Y)))).

  (* 4. 证明这两个区间是相等的 (I_target = I_source) *)
  assert (H_interval_eq : I_target = I_source).
  {
    apply interval_eq.
    - (* 证明 lower 相等: (mx+my)-(dx+dy) = (mx-dx)+(my-dy) *)
      unfold I_target, I_source. simpl. lra.
    - (* 证明 upper 相等 *)
      unfold I_target, I_source. simpl. lra.
  }

  (* 5. 使用 rewrite 替换目标，完成匹配 *)
  (* 将目标中的 I_target 替换为 I_source，这样 H_conv 就能直接应用了 *)
  rewrite H_interval_eq.
  exact H_conv.
Qed.

(* --- 4.3 浮点加法定义 --- *)
Definition float_add (X Y : FloatEnsemble) : FloatEnsemble :=
  coarse_grain (exact_add X Y).

(* ========================================================== *)
(* 5. 熵增证明                                                *)
(* ========================================================== *)

(* 辅助定义：提取 FloatEnsemble 的区间 *)
Definition get_interval (X : FloatEnsemble) :=
  mkInterval (mu X - delta X) (mu X + delta X) (valid_bounds (mu X) (delta X) (valid_delta X)).

Theorem Entropy_Increase_Proof : forall (X Y : FloatEnsemble),
  (* 假设输入是粗粒化过的（均匀分布） *)
  density X = UniformPDF (get_interval X) ->
  density Y = UniformPDF (get_interval Y) ->
  
  Entropy (density (exact_add X Y)) < Entropy (density (float_add X Y)).
Proof.
  intros X Y Hx Hy.
  
  (* 1. 展开定义 *)
  unfold float_add, coarse_grain, exact_add, get_interval in *.
  simpl.
  
  (* 2. 观察不等式 *)
  (* 左边: Entropy (Convolution (density X) (density Y)) *)
  (* 右边: Entropy (UniformPDF ...) *)
  
  (* 3. 代入假设 Hx, Hy *)
  (* 由于 density 是 PDF 函数，直接 rewrite 即可 *)
  match goal with
  | [ |- Entropy ?L < Entropy ?R ] => 
      replace L with (Convolution (density X) (density Y)) by reflexivity
  end.
  rewrite Hx, Hy.
  
  (* 4. 准备应用公理 Convolution_Lose_Entropy *)
  (* 问题：公理右边是 Entropy (UniformPDF (add_interval ...)) *)
  (* 当前目标右边是 Entropy (UniformPDF (mkInterval ...)) *)
  (* 我们再次利用区间相等性 *)
  
  (* 设 I_sum 为 add_interval 的结果 *)
  set (I_sum := add_interval 
    (mkInterval (mu X - delta X) (mu X + delta X) (valid_bounds (mu X) (delta X) (valid_delta X))) 
    (mkInterval (mu Y - delta Y) (mu Y + delta Y) (valid_bounds (mu Y) (delta Y) (valid_delta Y)))).
    
  (* 目标右边的区间 *)
  match goal with
  | [ |- _ < Entropy (UniformPDF ?I_float) ] => 
      assert (H_eq: I_float = I_sum)
  end.
  {
    apply interval_eq; simpl; lra.
  }
  
  (* 替换右边的区间 *)
  rewrite H_eq.
  
  (* 5. 直接应用公理 *)
  apply Convolution_Lose_Entropy.
Qed.

(* 验证完成：成功证明粗粒化导致熵增 *)
Print Entropy_Increase_Proof.