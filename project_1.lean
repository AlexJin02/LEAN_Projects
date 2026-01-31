/-
This project aims to investigate the contintuity and  the uniform conintuity
of the function `f(x) = x^2` using `ε-δ` definitions.
-/

import Mathlib.Tactic

/--
The definition of continuity for a function `f` at a specific point `x₀`.
i.e. `∀ ε>0, ∃ δ>0, such that ∀ x, |x - x₀| < δ → |f(x) - f(x₀)| < ε`
-/
def my_continuous_at (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

/--
The definition of uniform continuity for a function `f` over the real line.
i.e. `∀ ε>0, ∃ δ>0, such that ∀ x, y ∈ ℝ, |x - y| < δ → |f(x) - f(y)| < ε`
Note the difference from continuity: `δ` depends only on `ε`, not on `x`.
-/
def my_uniformly_continuous (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y, |x - y| < δ → |f x - f y| < ε

/--
The function we are investigating: `f(x) = x²`.
-/
def sq_fun (x : ℝ) : ℝ := x^2

/--
A lemma that simplifies the sq_fun.
-/
lemma abs_sq_fun (x y : ℝ) : |sq_fun x - sq_fun y| = |x - y| * |x + y| := by
  simp [sq_fun]
  rw[← abs_mul]
  ring_nf

/--
Triangle inequality for bounding the `|x + y|` part.
-/
theorem my_tri_ineq (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  -- Here I tried to prove the triangle inequality mannually using the following tactics:
  -- apply abs_le.mpr
  --constructor
  -- · have h1: -|x| ≤ x := neg_abs_le x
  --  have h2: -|y| ≤ y := neg_abs_le y
  --  linarith
  -- · have h3: x ≤ |x| := le_abs_self x
  --  have h4: y ≤ |y| := le_abs_self y
  --  linarith
  -- It works fine but quite lengthy。
  -- So I googled how to prove it and it turns out I can just call the built-in tactic.
  exact abs_add x y

/--
Then we start to prove the continuity of `f(x)=x^2` on the whole real line.
The strategy is choosing `δ = min(1, ε / (2|x₀| + 1))`.
-/
theorem sq_fun_continuous (x₀ : ℝ) : my_continuous_at sq_fun x₀ := by
  intro ε hε
  -- Define a constant c = 2|x₀| + 1
  -- `+1` ensures c > 0
  let c := 2 * |x₀| + 1
  have hc_pos : c > 0 := by
    simp [c]
    have h0 : 0 ≤ 2 * |x₀| := by
      exact mul_nonneg (by norm_num) (abs_nonneg x₀)
    exact add_pos_of_nonneg_of_pos h0 (by norm_num)

  -- Choose `δ = min(1, ε / (2 * |x₀| + 1))`
  use min 1 (ε / c)

  constructor
  · apply lt_min
    · norm_num
    · exact div_pos hε hc_pos -- Thanks to apply?
  · intro X hX
    rw[abs_sq_fun]
    -- Prove `|x - x₀| < 1`
    have h_le_1 : |X - x₀| < 1:= by
      apply lt_of_lt_of_le hX
      exact min_le_left 1 (ε / c)

    -- Prove `|x - x₀| < ε / c`
    have h_le_eps_c : |X - x₀| < ε / c := by
      apply lt_of_lt_of_le hX
      apply min_le_right 1 (ε / c)

    -- Bound the term `|x + x₀|`
    have h_upper_bound : |X + x₀| < c := by
      calc |X + x₀|
        _ = |X - x₀ + 2 * x₀| := by ring_nf
        _ ≤ |X - x₀| + |2 * x₀| := my_tri_ineq (X - x₀) (2 * x₀)
        _ < 1 + |2 * x₀| := by linarith
        _ = 1 + 2 * |x₀| := by rw[abs_mul, abs_two]
        _ = c := by ring

    calc |X - x₀| * |X + x₀|
      -- a < b and c < d → ac < bd
      -- Here I tried to apply mul_lt_mul but cannot figure out the right tactic
      -- So I asked ChatGPT and it provided me with a new tactic mul_lt_mul''.
      _ < (ε / c) * c := by
        apply mul_lt_mul'' h_le_eps_c h_upper_bound (abs_nonneg _) (abs_nonneg _)
      _ = ε := by simp[div_eq_mul_inv, mul_assoc, hc_pos.ne']

/--
However, the function `f(x) = x^2` is not uniformly continuous on the whole real line.
The strategy of the proof is prove the negation of the definition.
We pick `ε = 1`. Then `∀ δ > 0`, we choose `x = 1/δ and y = 1/δ + δ/2`.
These are `δ/2` apart, but their images differ by more than `1`.
-/
theorem sq_fun_not_uniform_on_r : ¬ (my_uniformly_continuous sq_fun) := by
  unfold my_uniformly_continuous
  -- Use push_neg tactic to negate the whole definition
  push_neg

  -- Choose `ε = 1`
  use 1
  constructor
  · norm_num
  · intro δ hδ
    -- Choose `x = 1/δ and y = 1/δ + δ/2`
    use 1 / δ, 1 / δ + δ / 2
    constructor
    · rw [abs_sub_comm]
      ring_nf
      rw [abs_of_pos]
      · linarith
      · linarith
    · rw [abs_sq_fun]
      -- Simplify `|x-y| and |x+y|` seperately
      have h_diff : |1/δ - (1/δ + δ/2)| = δ/2 := by
        ring_nf
        rw [abs_mul, abs_of_pos hδ]
        norm_num
      have h_sum : |1/δ + (1/δ + δ/2)| = 2/δ + δ/2 := by
        ring_nf
        rw [abs_of_pos]
        apply add_pos
        · nlinarith
        · exact mul_pos (inv_pos.2 hδ) (by norm_num)

      rw [h_diff, h_sum]
      calc δ / 2 * (2 / δ + δ / 2)
        _ = (δ / 2) * (2 / δ) + (δ / 2) * (δ / 2) := by rw [mul_add]
        _ = 1 + δ^2 / 4 := by
        -- I tried to use simp to simplify the expression. However, it became more and more goals to prove.
        -- So I asked ChatGPT and learned the new tactic field_simp here.
          field_simp [hδ.ne']
          ring
        _ ≥ 1 := by
          apply le_add_of_nonneg_right
          apply div_nonneg
          · exact sq_nonneg δ
          · norm_num

/--
But we could prove that `f(x)=x^2` is uniformly continuous on `[0, 1]`.
-/
theorem sq_fun_uniform_on_01 :
  ∀ ε > 0, ∃ δ > 0, ∀ x y,
  (0 ≤ x ∧ x ≤ 1) → (0 ≤ y ∧ y ≤ 1) → |x - y| < δ → |sq_fun x - sq_fun y| < ε := by
  intro ε hε
  use ε / 2
  constructor
  · linarith
  · intro x y hx hy h
    rw [abs_sq_fun]
    have h_bound_fun : |x + y| ≤ 2 := by
      obtain ⟨x_lower, x_upper⟩ := hx
      obtain ⟨y_lower, y_upper⟩ := hy
      apply le_trans (my_tri_ineq x y)
      rw [abs_of_nonneg x_lower]
      rw [abs_of_nonneg y_lower]
      linarith

    apply lt_of_le_of_lt (b := |x - y| * 2)
    · apply mul_le_mul_of_nonneg_left
      · exact h_bound_fun
      · exact abs_nonneg (x - y)

    -- Use the same technique in section02 Sheet06
    exact (lt_div_iff₀ two_pos).mp h

#lint
