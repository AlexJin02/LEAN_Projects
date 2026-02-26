/-
This project is divided into two sections.
The first section formalises the proof of Banach Fixed Point Theorem using standard Picard iteration.
The second section is an extension for the stability bound.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic

open Filter Topology Set Metric

variable {X : Type*} [MetricSpace X]

section Banach_Fixed_Point_Theorem
/--
A map `f` is a contraction if it shrinks distances by a factor `K < 1`.
-/
def is_contraction (f : X → X) (K : ℝ) : Prop :=
  0 ≤ K ∧ K < 1 ∧ ∀ x y, dist (f x) (f y) ≤ K * dist x y

/--
The definition of Picard iteration x_{n+1} = f(x_n)
-/
def iteration_seq (f : X → X) (x₀ : X) : ℕ → X
  | 0 => x₀
  | n + 1 => f (iteration_seq f x₀ n)
  -- I learned how to define this sequence in the following website:
  -- https://proofassistants.stackexchange.com/questions/438/how-to-define-a-recursive-sequence-in-lean

/-
Then we need a lemma to prove that if a map is contracting then it is Cauchy.
-/

lemma cauchy_seq_of_contraction {f : X → X} {K : ℝ} (hf : is_contraction f K) (x₀ : X) :
  CauchySeq (iteration_seq f x₀) := by
  -- I found 'CauchySeq' by searching cauchy sequence in leansearch
  -- First we need to unpack the def 'is contraction'
  rcases hf with ⟨hK_nonneg, hK_lt_one, h_dist⟩
  -- We want to use the property of contraction maps to get d(x_n, x_{n+1}) ≤ K^n * d(x_0, x_1)
  -- I found this by searching contracting map implies cauchy in leansearch
  apply cauchySeq_of_le_geometric K (dist x₀ (f x₀)) hK_lt_one
  intro n
  induction n with
    | zero =>
      simp [iteration_seq]
    | succ n h_induction =>
      apply (h_dist _ _).trans
      rw[pow_succ]
      nlinarith

-- I used to declare metric space X to be nonempty and complete before the above lemma.
-- However there was a message indicating that I can omit them.

-- Here I have to declare it because I need to use this restriction in the main proof.
variable [Nonempty X] [CompleteSpace X]

/--
Banach Fixed Point Theorem: Any contraction on a complete metric space has a unique fixed point.
-/
theorem banach_fixed_point {f : X → X} {K : ℝ} (hf : is_contraction f K) :
  ∃! x, f x = x := by
  -- Pick a nonnegative starting point x₀
  obtain ⟨x₀⟩ := ‹Nonempty X›
  -- Define the sequence and use the lemma to prove it is Cauchy
  let seq := iteration_seq f x₀
  have h_cauchy := cauchy_seq_of_contraction hf x₀

  rcases hf with ⟨hK_nonneg, hK_lt_one, h_dist⟩
  -- Since X is a complete metric space, the Cauchy sequence converges to some point x
  -- hx_lim is interpreted as the following:

  obtain ⟨x, hx_lim⟩ := cauchySeq_tendsto_of_complete h_cauchy
  -- The Picard iteration xₙ tends to the neighborhood of x as n goes to infinity.

  -- Now we need to prove its existence and uniqueness of the fixed point

  -- 1. We prove the existence
  have h_existence : f x = x := by

    have h_lipschitz : LipschitzWith ⟨K, hK_nonneg⟩ f := by
      exact LipschitzWith.of_dist_le_mul h_dist -- exact?
    have h_continuous : Continuous f := h_lipschitz.continuous

    -- Limit 1 is f(xₙ) → f(x)
    have h_lim1 : Tendsto (fun n ↦ f (iteration_seq f x₀ n)) atTop (𝓝 (f x)) :=
      -- xₙ → x and f is continuous => f(xₙ) → f(x)
      Tendsto.comp h_continuous.continuousAt hx_lim

    -- Limit 2 is x_{n+1} → x
    have h_lim2 : Tendsto (fun n ↦ iteration_seq f x₀ (n + 1)) atTop (𝓝 x) :=
      -- xₙ → x => x_{n+1} → x
      hx_lim.comp (tendsto_add_atTop_nat 1)

    -- Limit is unique
    -- f(x) = x
    exact tendsto_nhds_unique h_lim1 h_lim2

  -- 7. use x and the above lemma to prove the whole theorem
  use x
  constructor
  · exact h_existence
  · -- Uniqueness
    intro y hy_fixed
    by_contra h_neq -- assume y ≠ x
    -- Then d(x, y)
    have h_dist_pos : 0 < dist x y :=
      dist_pos.mpr (Ne.symm h_neq)

    have h_ineq : dist x y ≤ K * dist x y := by
      nth_rw 1 [← hy_fixed, ← h_existence]
      exact h_dist x y  -- exact?

    -- 1. h_dist_pos : 0 < dist x y
    -- 2. h_ineq : dist x y ≤ K * dist x y
    -- 3. hK_lt_one : K < 1
    nlinarith

end Banach_Fixed_Point_Theorem

section Banach_Stability

variable {P X : Type*} [MetricSpace P] [MetricSpace X] [Nonempty X] [CompleteSpace X]

/--
Theorem: Stability of the fixed point with respect to a parameter.
If f(p, x) is a uniform contraction in x and Lipschitz in p,
then the fixed point depends Lipschitz continuously on p.
-/

theorem banach_stability
  (F : P → X → X) -- right associative; F p : X → X; F p x : X
  (K L : ℝ) -- K is the contraction constant (uniform in p); L is the Lipschitz constant
  (hK : 0 ≤ K ∧ K < 1)
  (h_contr : ∀ p, is_contraction (F p) K)
  (h_lip : ∀ p q x, dist (F p x) (F q x) ≤ L * dist p q) :
  -- The selection of fixed points across parameter p
  ∃ (x_star : P → X),
    (∀ p, F p (x_star p) = x_star p) ∧
    -- The sensitivity bound
    (∀ p q, dist (x_star p) (x_star q) ≤ (L / (1 - K)) * dist p q) := by

  -- Step 1: Fixed point existence
  have h_exists : ∀ p, ∃ x, F p x = x := by
    intro p
    obtain ⟨x, hx, _⟩ := banach_fixed_point (h_contr p)
    exact ⟨x, hx⟩
  choose x_star hx_star using h_exists

  use x_star
  constructor
  · exact hx_star
  · -- Step 2: Establish the key inequality
    intro p q
    have h_key : dist (x_star p) (x_star q) ≤ K * dist (x_star p) (x_star q) + L * dist p q := by
      calc dist (x_star p) (x_star q)
        _ = dist (F p (x_star p)) (F q (x_star q)) := by
          nth_rw 1 [← hx_star p, ← hx_star q]
        _ ≤ dist (F p (x_star p)) (F p (x_star q)) + dist (F p (x_star q)) (F q (x_star q)) :=
          dist_triangle _ _ _
        _ ≤ K * dist (x_star p) (x_star q) + L * dist p q := by
          have ⟨_, _, h_dist_p⟩ := h_contr p
          exact add_le_add (h_dist_p (x_star p) (x_star q)) (h_lip p q (x_star q))

    -- Step 3: Rearrange and divide by (1 - K)
    have h_pos : 0 < 1 - K := by nlinarith

    calc dist (x_star p) (x_star q)
      _ ≤ (L * dist p q) / (1 - K) := by
        rw[le_div_iff₀ h_pos]
        linarith
      _ = (L / (1 - K)) * dist p q := by ring

end Banach_Stability

#lint
