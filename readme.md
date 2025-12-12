# Coq Formal Verification: Entropy Increase in Ensemble Floating-Point Arithmetic


> **A formal proof verifying that floating-point coarse-graining acts as an entropy-increasing process in information theory.**
---


**Author**: Ada Qin

## 1. Motivation

Traditional analysis of floating-point arithmetic typically focuses on **Worst-case Error Bounds**, treating numbers as points or strict intervals on the real number line. However, this perspective overlooks the **probability distribution information** inherent in numerical errors.

* **The Problem**: Mathematically, arithmetic operations on random variables (such as adding two numbers with uniform error distributions) tend to concentrate the probability mass (e.g., forming a triangular distribution via convolution), thereby reducing uncertainty.
* **The Paradox**: Computer hardware cannot store these complex distribution shapes. It must "forget" the history and store the result in a standard format (Nominal Value + Error Bound).
* **The Goal**: This project models floating-point numbers as statistical **Ensembles**. We formally prove in Coq that the process of storing a calculation result—defined here as **"Coarse Graining"**—inevitably leads to an increase in thermodynamic entropy (information loss).

## 2. Mathematical Modeling: The Ensemble Float

In this project, a floating-point number is not a scalar, but a probabilistic structure defined as a quadruple:

$$F = (\mu, \delta, \text{Valid}, p)$$

Where:
* **$\mu$ (Mu)**: The expectation (nominal value stored in the register).
* **$\delta$ (Delta)**: The error radius, defining the support interval $[\mu - \delta, \mu + \delta]$.
* **$\text{Valid}$**: A proof term guaranteeing $\delta > 0$.
* **$p$ (Density)**: The Probability Density Function (PDF), $p: \mathbb{R} \to \mathbb{R}$.

### The Principle of Maximum Entropy
We adopt the **MaxEnt** principle as a core axiom: When a number is stored as a floating-point value, all information about its internal probability distribution is lost. Therefore, the most honest representation of the stored number is the **Uniform Distribution** over its error interval.

## 3. Mathematical Principles of Proof

The proof compares the entropy of the **Exact Mathematical Result** versus the **Stored Floating-Point Result**.

### 3.1 The Process Decomposition
A floating-point addition $Z = X + Y$ is modeled as a two-step process:

1.  **Exact Operation (Convolution)**:
    The sum of two independent random variables corresponds to the convolution of their PDFs:
    $$\mathrm{Supp}(p_X * p_Y) = \mathrm{Supp}(p_X) + \mathrm{Supp}(p_Y)$$
    If $X$ and $Y$ are uniform (rectangular distributions), $p_{exact}$ becomes a trapezoidal or triangular distribution.

2.  **Coarse Graining (Storage)**:
    To fit the result back into the `FloatEnsemble` model, we force the distribution back to Uniform over the new support interval:

    $$
    p_{\mathrm{float}} = U_{[\mu_{\mathrm{new}}-\delta_{\mathrm{new}}, \mu_{\mathrm{new}}+\delta_{\mathrm{new}}]}
    $$

### 3.2 Key Axioms & Inequalities
The formal verification relies on establishing:

1.  **Support Conservation**: The physical interval of the convolution is algebraically identical to the interval calculated by floating-point arithmetic.
    $$\text{Supp}(p_X * p_Y) = \text{Supp}(p_X) + \text{Supp}(p_Y)$$
    
2.  **Entropy Gap**: For two uniform distributions, their convolution has strictly lower differential entropy than a uniform distribution covering the same total width.
    $$H(U_1 * U_2) < H(U_{sum})$$

**Conclusion**: $H(\text{float\_add}) > H(\text{exact\_add})$.

## 4. Code Structure

The project is self-contained and relies only on the Coq Standard Library.

* **Dependencies**: `Reals`, `Psatz` (for linear arithmetic), `Coq.Logic.ProofIrrelevance`.

### Module Breakdown

| Section | Description |
| :--- | :--- |
| **Definitions** | Defines `PDF`, `Interval`, and the `Entropy` functional. |
| **Axioms** | Formalizes `Max_Entropy_Bound` and `Convolution_Lose_Entropy`. |
| **Model** | Defines the `FloatEnsemble` record with explicit proof terms for interval validity. |
| **Operations** | Implements `exact_add` (convolution) and `coarse_grain` (reset to Uniform). |
| **Theorems** | The main proof script connecting the operations to the entropy axioms. |

## 5. Execution Results

The code compiles successfully under **Coq 8.x**. The main theorem `Entropy_Increase_Proof` is fully proven without pending subgoals.

### Key Theorem Definition
```coq
Theorem Entropy_Increase_Proof : forall (X Y : FloatEnsemble),
  (* Premise: Inputs are standard floats (Uniform) *)
  density X = UniformPDF (get_interval X) ->
  density Y = UniformPDF (get_interval Y) ->
  
  (* Conclusion: Stored entropy is strictly greater than exact entropy *)
  Entropy (density (exact_add X Y)) < Entropy (density (float_add X Y)).
```

### Verification
Running `Print Entropy_Increase_Proof.` in Coq yields the full proof term, confirming that the logical construction relies correctly on the specified axioms and arithmetic proofs provided by `lra`.

## 6. Conclusion

This formal verification project demonstrates that:

1.  **Floating-point arithmetic is dissipative**: Beyond precision loss, it actively injects entropy into the system by "flattening" probability distributions.
2.  **Validity of the Ensemble Model**: Treating floating-point numbers as ensembles provides a rigorous framework for analyzing information flow in numerical algorithms.
3.  **Formal Rigor**: By handling `ProofIrrelevance` and complex type unification, we have bridged the gap between mathematical intuition (interval equality) and formal type theory.

