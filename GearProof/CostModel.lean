/-
  CostModel.lean -- PrimeAtlas v7.1/v7.2: the gear's threshold p* and block factor f* are the
  optimum of the engines' cost model (work_plan_v7_1.py, work_plan_v7_2.py).
  Separate from JumpGear.lean (correctness), which it does not use.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace CostModel

/-! ## 22. The threshold and the block factor are the optimum of the cost model

The cost model of `work_plan_v7_1.py` / `work_plan_v7_2.py`, per unit of `q`, in units of
the cost of one classic sieving prime: the classic path costs `1 / ln q` (one prime per
`ln q` numbers), the gear `C / q` with `C = a sqrt(F/W) + b W`. In v7.2, at block factor
`f`: `C(f) = α / f + β (1 + f^2/2)` with `α = 0.5 a sqrt(F/W)`, `β = b W / 1.125`.
Proven here, for that model:
* the pointwise rule: the gear is the cheaper path exactly from the fixed point
  `p* = C ln p*` on (`gear_cheaper_above`, `classic_cheaper_below`);
* so the split at `p*` is the cheapest of *all* assignments of the `q` to the two paths
  (`threshold_optimal`);
* the code's iteration `p ← max(C ln p, 3)` from `max(C, 3)` rises to `p*`, with error
  `≤ (1 / ln C)^k · p*` after `k + 1` steps (`iterP_le`, `iterP_mono`, `iterP_error`), and
  a fixed point `≥ C` exists (`fixedPoint_exists`);
* `f* = (α/β)^(1/3)` minimises `C(f)`, also after clamping to `[0.05, 64]`
  (`blockCost_min`, `blockCost_clamp_min`), and `(f*, p*(f*))` together beat every block
  factor with every assignment (`model_optimal`).
The constants `a`, `b` are fitted to measurements; the model itself is not a theorem. -/

open Real in
lemma div_log_mono {x y : ℝ} (hx : exp 1 ≤ x) (hxy : x ≤ y) : x / log x ≤ y / log y := by
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 1) hx
  have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
  have hlx : 1 ≤ log x := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) hx
  have hly : 1 ≤ log y := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) (le_trans hx hxy)
  have h := log_div_self_antitoneOn (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (le_trans hx hxy)) hxy
  simp only at h
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  rw [div_le_div_iff₀ hy0 hx0] at h
  nlinarith

open Real in
/-- Above the fixed point the gear is the cheaper path. -/
theorem gear_cheaper_above {C p q : ℝ} (hp : exp 1 ≤ p) (hfix : p = C * log p) (hq : p ≤ q) :
    C / q ≤ 1 / log q := by
  have hp0 : 0 < p := lt_of_lt_of_le (exp_pos 1) hp
  have hq0 : 0 < q := lt_of_lt_of_le hp0 hq
  have hlp : 1 ≤ log p := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) hp
  have hlq : 0 < log q := by
    have : 1 ≤ log q := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) (le_trans hp hq)
    linarith
  have hC : C = p / log p := by field_simp; linarith
  have hm := div_log_mono hp hq
  rw [div_le_div_iff₀ hq0 hlq, one_mul, hC]
  rw [div_le_div_iff₀ (by linarith) hlq] at hm
  calc p / log p * log q = p * log q / log p := by ring
    _ ≤ q := by rw [div_le_iff₀ (by linarith)]; linarith

open Real in
/-- Between `e` and the fixed point the classic path is the cheaper one. -/
theorem classic_cheaper_below {C p q : ℝ} (hq : exp 1 ≤ q) (hfix : p = C * log p)
    (hqp : q ≤ p) : 1 / log q ≤ C / q := by
  have hq0 : 0 < q := lt_of_lt_of_le (exp_pos 1) hq
  have hp0 : 0 < p := lt_of_lt_of_le hq0 hqp
  have hlq : 1 ≤ log q := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) hq
  have hlp : 1 ≤ log p := by rw [← log_exp 1]; exact log_le_log (exp_pos 1) (le_trans hq hqp)
  have hC : C = p / log p := by field_simp; linarith
  have hm := div_log_mono hq hqp
  rw [div_le_div_iff₀ (by linarith) hq0, one_mul, hC]
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at hm
  calc q = q * log p / log p := by field_simp
    _ ≤ p * log q / log p := by
        apply div_le_div_of_nonneg_right _ (by linarith); linarith
    _ = p / log p * log q := by ring

/-- Cost of assigning each `q` of a finite set (with weights `w q ≥ 0`, e.g. how many numbers
it stands for) to the gear (`true`) or the classic path (`false`). -/
noncomputable def modelCost (C : ℝ) (S : Finset ℝ) (w : ℝ → ℝ) (σ : ℝ → Bool) : ℝ :=
  ∑ q ∈ S, w q * (if σ q then C / q else 1 / Real.log q)

open Real in
/-- **The split at `p*` is optimal**: no assignment of the `q ≥ e` to the two paths is cheaper
in the model than "gear from `p*` on". -/
theorem threshold_optimal {C p : ℝ} (hp : exp 1 ≤ p) (hfix : p = C * log p) (S : Finset ℝ)
    (hS : ∀ q ∈ S, exp 1 ≤ q) (w : ℝ → ℝ) (hw : ∀ q, 0 ≤ w q) (σ : ℝ → Bool) :
    modelCost C S w (fun q => decide (p ≤ q)) ≤ modelCost C S w σ := by
  unfold modelCost
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left _ (hw q)
  by_cases h : p ≤ q
  · simp only [h, decide_true, ↓reduceIte]
    cases σ q
    · exact gear_cheaper_above hp hfix h
    · exact le_refl _
  · simp only [h, decide_false]
    cases σ q
    · exact le_refl _
    · exact classic_cheaper_below (hS q hq) hfix (le_of_lt (not_le.mp h))

/-- The code's iteration (`work_plan_v7_1.jump_from`): `p = max(c, 3)`, then
`p = max(c ln p, 3)`. -/
noncomputable def iterP (C : ℝ) : ℕ → ℝ
  | 0 => max C 3
  | k + 1 => max (C * Real.log (iterP C k)) 3


open Real in
theorem iterP_ge_three (C : ℝ) : ∀ k, 3 ≤ iterP C k := by
  intro k; cases k <;> simp [iterP]

open Real in
theorem iterP_le {C p : ℝ} (hC : 3 ≤ C) (hp3 : 3 ≤ p) (hfix : p = C * log p) :
    ∀ k, iterP C k ≤ p := by
  have hlp : 1 ≤ log p := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_three])
  intro k
  induction k with
  | zero => simp only [iterP]; exact max_le (by nlinarith) hp3
  | succ k ih =>
    simp only [iterP]
    apply max_le _ hp3
    have h0 : 0 < iterP C k := lt_of_lt_of_le (by norm_num) (iterP_ge_three C k)
    calc C * log (iterP C k) ≤ C * log p :=
          mul_le_mul_of_nonneg_left (log_le_log h0 ih) (by linarith)
      _ = p := hfix.symm

open Real in
theorem iterP_mono {C : ℝ} (hC : 3 ≤ C) : ∀ k, iterP C k ≤ iterP C (k + 1) := by
  intro k
  induction k with
  | zero =>
    simp only [iterP, max_eq_left hC]
    have : 1 ≤ log C := by
      rw [← log_exp 1]; exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_three])
    exact le_max_of_le_left (by nlinarith)
  | succ k ih =>
    simp only [iterP] at ih ⊢
    apply max_le_max _ (le_refl _)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact log_le_log (lt_of_lt_of_le (by norm_num) (iterP_ge_three C k)) ih

open Real in
/-- **Convergence of the code's iteration**: after `k + 1` steps the error is at most
`(1 / ln C)^k · p*` (for `C ≥ 10^8`, `1 / ln C < 0.055`, so 60 steps exhaust a double). -/
theorem iterP_error {C p : ℝ} (hC : 3 ≤ C) (hp3 : 3 ≤ p) (hfix : p = C * log p) :
    ∀ k, p - iterP C (k + 1) ≤ (1 / log C) ^ k * p := by
  have hlC : 1 ≤ log C := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_three])
  have hle := iterP_le hC hp3 hfix
  -- each step: p - C ln x ≤ (C / x)(p - x) ≤ (1 / ln C)(p - x) for x ≥ C ln C
  have hstep : ∀ x, C * log C ≤ x → x ≤ p → p - C * log x ≤ (1 / log C) * (p - x) := by
    intro x hx hxp
    have hx0 : 0 < x := lt_of_lt_of_le (by nlinarith) hx
    have hlog : log p - log x ≤ (p - x) / x := by
      have := log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < p) hx0)
      rw [log_div (by linarith) hx0.ne'] at this
      have e : p / x - 1 = (p - x) / x := by field_simp
      rw [e] at this
      exact this
    have h1 : p - C * log x = C * (log p - log x) := by rw [mul_sub, ← hfix]
    rw [h1]
    calc C * (log p - log x) ≤ C * ((p - x) / x) := mul_le_mul_of_nonneg_left hlog (by linarith)
      _ = (C / x) * (p - x) := by ring
      _ ≤ (1 / log C) * (p - x) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          rw [div_le_div_iff₀ hx0 (by linarith)]; linarith
  have h1 : C * log C ≤ iterP C 1 := by simp only [iterP, max_eq_left hC]; exact le_max_left _ _
  have hge : ∀ k, C * log C ≤ iterP C (k + 1) := by
    intro k
    induction k with
    | zero => exact h1
    | succ k ih => exact le_trans ih (iterP_mono hC (k + 1))
  intro k
  induction k with
  | zero =>
    simp only [pow_zero, one_mul]
    have := iterP_ge_three C 1
    linarith
  | succ k ih =>
    have hs := hstep (iterP C (k + 1)) (hge k) (hle (k + 1))
    have hnext : C * log (iterP C (k + 1)) ≤ iterP C (k + 2) := by
      show C * log (iterP C (k + 1)) ≤ max (C * log (iterP C (k + 1))) 3
      exact le_max_left _ _
    have hpos : 0 ≤ 1 / log C := by positivity
    calc p - iterP C (k + 2) ≤ p - C * log (iterP C (k + 1)) := by linarith
      _ ≤ (1 / log C) * (p - iterP C (k + 1)) := hs
      _ ≤ (1 / log C) * ((1 / log C) ^ k * p) := mul_le_mul_of_nonneg_left ih hpos
      _ = (1 / log C) ^ (k + 1) * p := by ring

open Real in
/-- A fixed point `p = C ln p` with `C ≤ p ≤ C^3` exists for `C ≥ 3`. -/
theorem fixedPoint_exists {C : ℝ} (hC : 3 ≤ C) : ∃ p, C ≤ p ∧ p ≤ C ^ 3 ∧ p = C * log p := by
  have hC0 : 0 < C := by linarith
  have hlC : 1 ≤ log C := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_three])
  have hle : C ≤ C ^ 3 := by
    have h1 : 1 ≤ C ^ 2 := by nlinarith
    calc C = C * 1 := by ring
      _ ≤ C * C ^ 2 := mul_le_mul_of_nonneg_left h1 hC0.le
      _ = C ^ 3 := by ring
  have hcont : ContinuousOn (fun x => x - C * log x) (Set.Icc C (C ^ 3)) := by
    apply ContinuousOn.sub continuousOn_id
    apply ContinuousOn.mul continuousOn_const
    apply continuousOn_log.mono
    intro x hx; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hx.1]
  have ha : C - C * log C ≤ 0 := by nlinarith
  have hb : 0 ≤ C ^ 3 - C * log (C ^ 3) := by
    rw [log_pow]; push_cast
    have h1 := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hC0) hC0.le
    have h2 : 0 ≤ C * ((C - 3 / 2) ^ 2 + 3 / 4) := by positivity
    nlinarith
  obtain ⟨p, ⟨hp1, hp2⟩, hp⟩ := intermediate_value_Icc hle hcont ⟨ha, hb⟩
  exact ⟨p, hp1, hp2, by simp only at hp; linarith⟩

/-- v7.2's gear cost per unit `q` at block factor `f` (`effective_costs` + `jump_cost`). -/
noncomputable def blockCost (α β f : ℝ) : ℝ := α / f + β * (1 + f ^ 2 / 2)

lemma blockCost_diff {α β x y fs : ℝ} (hβ : 0 < β) (hfs : α = β * fs ^ 3) (hx : 0 < x)
    (hy : 0 < y) :
    blockCost α β y - blockCost α β x = (y - x) * β * ((x + y) / 2 - fs ^ 3 / (x * y)) := by
  unfold blockCost; rw [hfs]; field_simp; ring

/-- **`f*` minimises the gear's cost**: with `β f*^3 = α` (the code's
`f* = (0.5625 a sqrt(F/W) / (b W))^(1/3)`), `C(f*) ≤ C(f)` for every `f > 0`. -/
theorem blockCost_min {α β fs f : ℝ} (hβ : 0 < β) (hfs0 : 0 < fs) (hfs : α = β * fs ^ 3)
    (hf : 0 < f) : blockCost α β fs ≤ blockCost α β f := by
  have e : blockCost α β f - blockCost α β fs = β * (f - fs) ^ 2 * (f + 2 * fs) / (2 * f) := by
    unfold blockCost; rw [hfs]; field_simp; ring
  have : 0 ≤ β * (f - fs) ^ 2 * (f + 2 * fs) / (2 * f) := by positivity
  linarith

/-- The clamp of `f*` to `[lo, hi]` (the code's `[0.05, 64]`) is the best factor in `[lo, hi]`. -/
theorem blockCost_clamp_min {α β fs lo hi f : ℝ} (hβ : 0 < β) (hfs0 : 0 < fs)
    (hfs : α = β * fs ^ 3) (hlo : 0 < lo) (hlohi : lo ≤ hi) (hf1 : lo ≤ f) (hf2 : f ≤ hi) :
    blockCost α β (min (max fs lo) hi) ≤ blockCost α β f := by
  have hf0 : 0 < f := lt_of_lt_of_le hlo hf1
  -- C is antitone on (0, fs] and monotone on [fs, ∞)
  have up : ∀ x y, fs ≤ x → x ≤ y → blockCost α β x ≤ blockCost α β y := by
    intro x y hx hxy
    have hx0 : 0 < x := lt_of_lt_of_le hfs0 hx
    have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
    have d := blockCost_diff (α := α) hβ hfs hx0 hy0
    have h1 : fs ^ 3 / (x * y) ≤ fs := by
      rw [div_le_iff₀ (by positivity)]
      have : fs * fs ≤ x * y := mul_le_mul hx (le_trans hx hxy) hfs0.le hx0.le
      nlinarith
    have : 0 ≤ (y - x) * β * ((x + y) / 2 - fs ^ 3 / (x * y)) := by
      apply mul_nonneg (mul_nonneg (by linarith) hβ.le); linarith
    linarith
  have down : ∀ x y, 0 < x → x ≤ y → y ≤ fs → blockCost α β y ≤ blockCost α β x := by
    intro x y hx0 hxy hy
    have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
    have d := blockCost_diff (α := α) hβ hfs hx0 hy0
    have h1 : fs ≤ fs ^ 3 / (x * y) := by
      rw [le_div_iff₀ (by positivity)]
      have : x * y ≤ fs * fs := mul_le_mul (le_trans hxy hy) hy hy0.le hfs0.le
      nlinarith
    have : (y - x) * β * ((x + y) / 2 - fs ^ 3 / (x * y)) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) hβ.le); linarith
    linarith
  rcases le_or_gt fs lo with h1 | h1
  · rw [max_eq_right h1, min_eq_left hlohi]; exact up lo f h1 hf1
  · rcases le_or_gt fs hi with h2 | h2
    · rw [max_eq_left h1.le, min_eq_left h2]; exact blockCost_min hβ hfs0 hfs hf0
    · rw [max_eq_left h1.le, min_eq_right (le_of_lt h2)]
      exact down f hi hf0 hf2 (le_of_lt h2)

open Real in
/-- **Joint optimum of the model**: the block factor `f*` with the threshold `p*` of
`C(f*)` costs no more than any block factor `f` with any assignment of the `q` to the paths. -/
theorem model_optimal {α β fs p f : ℝ} (hβ : 0 < β) (hfs0 : 0 < fs) (hfs : α = β * fs ^ 3)
    (hf : 0 < f) (hp : exp 1 ≤ p) (hfix : p = blockCost α β fs * log p) (S : Finset ℝ)
    (hS : ∀ q ∈ S, exp 1 ≤ q) (w : ℝ → ℝ) (hw : ∀ q, 0 ≤ w q) (σ : ℝ → Bool) :
    modelCost (blockCost α β fs) S w (fun q => decide (p ≤ q)) ≤
      modelCost (blockCost α β f) S w σ := by
  refine le_trans (threshold_optimal hp hfix S hS w hw σ) ?_
  unfold modelCost
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left _ (hw q)
  have hq0 : 0 < q := lt_of_lt_of_le (exp_pos 1) (hS q hq)
  cases σ q
  · exact le_refl _
  · simp only [↓reduceIte]
    exact div_le_div_of_nonneg_right (blockCost_min hβ hfs0 hfs hf) hq0.le

end CostModel
