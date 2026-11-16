/-
  JumpGear.lean -- correctness of the PrimeAtlas jump gear (v7), engines v7.0, v7.1 and v7.2.

  The C routines are transcribed as functions on ℕ; the agreement of this model with the
  compiled code rests on the transcription and on the engines' identity tests
  (test_engine_v7_*_identity).

  Contents:
    1. landing_iff         -- q has a multiple in [F, F+W)  ↔  (q - F % q) % q < W
    2. at_most_one         -- for q ≥ W that multiple is unique
    3. composite_harmless  -- a mark from any q (composite included) never hits a prime
    4. prime_coprime_30    -- every prime ≥ 7 lies in one of the 8 classes mod 30
    5. sieve_correct       -- a complete set of sieving numbers ⇒ a correct sieve
    6. tangent_identity,
       tangent_error_bounds -- the tangent line on a block q = Q + d and its error bounds
    7. candidate_of_landing,
       gear_candidate      -- every landing satisfies the candidate condition (a superset)
    8. block_complete      -- assembly: superset + complete enumeration ⇒ no landing is lost

    9. fract_neg_div, landing_iff_fract, landing_is_candidate -- bridge ℕ ↔ ℝ
   10. step_lands, step_first, enumeration_complete -- three-gap steps
   11. firstIn_spec        -- jump_first_in (Euclid-like recursion) returns the least
                              solution, or none exactly when there is none
   12. firstRange_spec     -- jump_first_range (window shifted by b, possibly wrapped)
                              gives the least j0, ga, gc
   13. firstRange64_spec   -- the 64-bit search of engine v7.2 (jump_first_in64,
                              jump_first_in_top, jump_first_range64) = the same, cut at 2^64
   14. jumpGaps_spec       -- jump_gaps (v7.2): one Euclid walk gives ga, gc
                              satisfying GearRot (lattice argument, determinant M)
   15. jump_block_complete       -- v7.0 / v7.1: the loop of jump_block() visits every
                                    candidate j < J
       jump_block_quick_complete -- v7.2: the same for jump_block_quick()
       cStep_eq                  -- the loop arithmetic in C (alpha, beta, test v + alpha >= v)
                                    = gearStep
   16. landing_candidate_fixed -- bridge: landing ⇒ (A + B j) mod 2^64 < T in 64.64
                                  fixed point (truncations of X0 and S, slack, tangent error)
   17. cX0_eq, cS_eq      -- the u128 operations are exact when 30·first < 2^128;
       cS_overflow        -- counterexample: first = 1.2·10^37 (gear enabled, S wrong)
   18. t_double_ok        -- T computed in double (IEEE-754 model, u = 2^-53) suffices for the bridge
   19. cLanding_eq, estimate_safe -- the exact check in jump_landing, without u128 wraparound
   20. jump_block_quick_exact (v7.2), jump_block_exact (v7.0/v7.1) -- END TO END:
       every landing j < J of the block is visited and has its exact offset, under
         8 ≤ Q,  Q + 30 J < 2^64,  Q ≤ first < 2^62 Q,  60 J ≤ Q,  1 ≤ span ≤ 2^48,
         30·first < 2^128  (first < 2^128/30 ≈ 1.134·10^37)  ← the engine bound
   21. gaps_certificate   -- a cheap certificate: a pair (ga, gc) satisfying the inequalities and
                             ga·dc + gc·da = 2^64 IS the least pair (e.g. kept from the previous block)
  Models: C as functions on ℕ with explicit mod 2^64 / 2^128; double by the standard model
  (every operation x(1+δ), |δ| ≤ 2^-53, no underflow).
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace JumpGear

/-! ### 1. The landing criterion -/

theorem landing_iff (F W q : ℕ) (hq : 0 < q) :
    (∃ m, F ≤ m ∧ m < F + W ∧ q ∣ m) ↔ (q - F % q) % q < W := by
  have hdm : q * (F / q) + F % q = F := Nat.div_add_mod F q
  have hr : F % q < q := Nat.mod_lt F hq
  by_cases h0 : F % q = 0
  · have hoff : (q - F % q) % q = 0 := by rw [h0, Nat.sub_zero, Nat.mod_self]
    rw [hoff]
    constructor
    · rintro ⟨m, h1, h2, -⟩
      omega
    · intro hW
      exact ⟨F, le_refl F, by omega, Nat.dvd_of_mod_eq_zero h0⟩
  · have hoff : (q - F % q) % q = q - F % q := Nat.mod_eq_of_lt (by omega)
    rw [hoff]
    constructor
    · rintro ⟨m, h1, h2, t, rfl⟩
      have ht : F / q < t := by
        by_contra hc
        have hc' : t ≤ F / q := Nat.le_of_not_lt hc
        have := Nat.mul_le_mul_left q hc'
        omega
      have hge : q * (F / q + 1) ≤ q * t := Nat.mul_le_mul_left q ht
      rw [Nat.mul_add, Nat.mul_one] at hge
      omega
    · intro hW
      refine ⟨q * (F / q + 1), ?_, ?_, dvd_mul_right q _⟩
      · rw [Nat.mul_add, Nat.mul_one]
        omega
      · rw [Nat.mul_add, Nat.mul_one]
        omega

/-! ### 2. At most one multiple when q ≥ W -/

theorem at_most_one {F W q m₁ m₂ : ℕ} (hW : W ≤ q)
    (h1 : F ≤ m₁) (h1' : m₁ < F + W) (h2 : F ≤ m₂) (h2' : m₂ < F + W)
    (d1 : q ∣ m₁) (d2 : q ∣ m₂) : m₁ = m₂ := by
  obtain ⟨a, rfl⟩ := d1
  obtain ⟨b, rfl⟩ := d2
  rcases lt_trichotomy a b with h | h | h
  · have := Nat.mul_le_mul_left q (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this
    omega
  · rw [h]
  · have := Nat.mul_le_mul_left q (Nat.succ_le_of_lt h)
    rw [Nat.mul_succ] at this
    omega

/-! ### 3. A mark from any q (composite included) does not hit a prime -/

theorem composite_harmless {F q m : ℕ} (hq : 2 ≤ q) (hqF : q < F) (hm : F ≤ m)
    (hd : q ∣ m) : ¬ m.Prime := by
  intro hp
  rcases hp.eq_one_or_self_of_dvd q hd with h | h <;> omega

/-! ### 4. Wheel 30: every prime ≥ 7 is coprime to 30 -/

theorem prime_coprime_30 {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) : Nat.Coprime p 30 := by
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro h
  have hle : p ≤ 30 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> first | omega | norm_num at hp

/-! ### 5. A complete set of divisors ⇒ a correct sieve

`marked S n`: n is struck out by some d ∈ S, 2 ≤ d < n.
The hypothesis `hcomplete` is completeness: every prime p with p² < F + W that has a
multiple in the window belongs to S. S may contain composite numbers as well
(the jump gear takes every q coprime to 30): this does no harm. -/

abbrev marked (S : Set ℕ) (n : ℕ) : Prop := ∃ d ∈ S, 2 ≤ d ∧ d < n ∧ d ∣ n

theorem sieve_correct (S : Set ℕ) (F W : ℕ)
    (hcomplete : ∀ p, p.Prime → p * p < F + W →
      (∃ m, F ≤ m ∧ m < F + W ∧ p ∣ m) → p ∈ S)
    (n : ℕ) (hn2 : 2 ≤ n) (hF : F ≤ n) (hW : n < F + W) :
    ¬ marked S n ↔ n.Prime := by
  constructor
  · intro hnm
    by_contra hnp
    apply hnm
    have hpos : 0 < n := by omega
    have hmin : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hsq : Nat.minFac n ^ 2 ≤ n := Nat.minFac_sq_le_self hpos hnp
    rw [sq] at hsq
    have hdvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
    have h2 : 2 ≤ Nat.minFac n := hmin.two_le
    have h2p : 2 * Nat.minFac n ≤ Nat.minFac n * Nat.minFac n :=
      Nat.mul_le_mul_right _ h2
    exact ⟨Nat.minFac n, hcomplete _ hmin (by omega) ⟨n, hF, hW, hdvd⟩,
      h2, by omega, hdvd⟩
  · intro hp hm
    obtain ⟨d, -, hd2, hdn, hdvd⟩ := hm
    rcases hp.eq_one_or_self_of_dvd d hdvd with h | h <;> omega

/-! ### 6. The tangent line on a block q = Q + d and its error bounds -/

theorem tangent_identity (F Q d : ℝ) (hQ : 0 < Q) (hd : 0 ≤ d) :
    F / (Q + d) = F / Q - F * d / Q ^ 2 + F * d ^ 2 / (Q ^ 2 * (Q + d)) := by
  have hQd : Q + d ≠ 0 := (by linarith : (0 : ℝ) < Q + d).ne'
  have hQ0 : Q ≠ 0 := hQ.ne'
  field_simp
  ring

theorem tangent_error_bounds (F Q d : ℝ) (hF : 0 ≤ F) (hQ : 0 < Q) (hd : 0 ≤ d) :
    0 ≤ F * d ^ 2 / (Q ^ 2 * (Q + d)) ∧
      F * d ^ 2 / (Q ^ 2 * (Q + d)) ≤ F * d ^ 2 / Q ^ 3 := by
  have hnum : 0 ≤ F * d ^ 2 := mul_nonneg hF (sq_nonneg d)
  constructor
  · exact div_nonneg hnum (mul_nonneg (sq_nonneg Q) (by linarith))
  · have hQ3 : 0 < Q ^ 3 := pow_pos hQ 3
    have hden : Q ^ 3 ≤ Q ^ 2 * (Q + d) := by
      nlinarith [mul_nonneg (sq_nonneg Q) hd]
    exact div_le_div_of_nonneg_left hnum hQ3 hden

/-! ### 7. Every landing is a candidate

Landing: fract(-(F/q)) < W/q. The engine knows only an approximation L with F/q = L + e,
0 ≤ e ≤ E (tangent and truncation error). Then fract(-L) < W/Q + E for q ≥ Q:
the candidate condition is a superset of the landings, so no landing is dropped. -/

theorem candidate_of_landing (x e E τ : ℝ) (hland : Int.fract x < τ)
    (he0 : 0 ≤ e) (heE : e ≤ E) : Int.fract (x + e) < τ + E := by
  have h1 : Int.fract (x + e) ≤ Int.fract x + Int.fract e := Int.fract_add_le x e
  have hfl : e - (⌊e⌋ : ℝ) = Int.fract e := Int.self_sub_floor e
  have h0 : (0 : ℝ) ≤ (⌊e⌋ : ℝ) := by exact_mod_cast Int.floor_nonneg.mpr he0
  linarith

theorem gear_candidate (F q L e E W Q : ℝ) (hQ : 0 < Q) (hq : Q ≤ q) (hW : 0 ≤ W)
    (hsplit : F / q = L + e) (he0 : 0 ≤ e) (heE : e ≤ E)
    (hland : Int.fract (-(F / q)) < W / q) :
    Int.fract (-L) < W / Q + E := by
  have h := candidate_of_landing (-(F / q)) e E (W / q) hland he0 heE
  have hL : -(F / q) + e = -L := by linarith
  rw [hL] at h
  have hWq : W / q ≤ W / Q := div_le_div_of_nonneg_left hW hQ hq
  linarith

/-! ### 8. Assembly for one block

`land j`: q = Q + 30 j has a multiple in the run. `cand j`: the candidate condition.
`visited j`: the enumeration (Euclid + three-gap steps) visits j.
hsup is item 7, henum is item 10. -/

theorem block_complete {J : ℕ} (land cand visited : ℕ → Prop)
    (hsup : ∀ j < J, land j → cand j) (henum : ∀ j < J, cand j → visited j) :
    ∀ j < J, land j → visited j :=
  fun j hj hl => henum j hj (hsup j hj hl)

/-! ### 9. Bridge ℕ ↔ ℝ

The offset of the first multiple, computed in ℕ as (q - F % q) % q, is after division
by q exactly fract(-(F/q)). Hence the landing criterion in the form the jump gear uses,
and a direct input to gear_candidate. -/

theorem fract_neg_div (F q : ℕ) (hq : 0 < q) :
    Int.fract (-((F : ℝ) / q)) = (((q - F % q) % q : ℕ) : ℝ) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := hqR.ne'
  have hdm : (F : ℝ) = q * ((F / q : ℕ) : ℝ) + ((F % q : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod F q).symm
  have hr : F % q < q := Nat.mod_lt F hq
  have hsplit : -((F : ℝ) / q) =
      ((-((F / q : ℕ) : ℤ) : ℤ) : ℝ) + (-(((F % q : ℕ) : ℝ) / q)) := by
    rw [hdm, Int.cast_neg, Int.cast_natCast]
    field_simp
    ring
  rw [hsplit, Int.fract_intCast_add]
  by_cases h0 : F % q = 0
  · rw [h0]
    simp
  · have hpos : 0 < F % q := Nat.pos_of_ne_zero h0
    have hrq0 : (0 : ℝ) < ((F % q : ℕ) : ℝ) / q := div_pos (by exact_mod_cast hpos) hqR
    have hrq1 : ((F % q : ℕ) : ℝ) / q < 1 := by
      rw [div_lt_one hqR]
      exact_mod_cast hr
    have hfr : Int.fract (((F % q : ℕ) : ℝ) / q) = ((F % q : ℕ) : ℝ) / q :=
      Int.fract_eq_self.mpr ⟨hrq0.le, hrq1⟩
    rw [Int.fract_neg (by rw [hfr]; exact hrq0.ne'), hfr,
      Nat.mod_eq_of_lt (by omega : q - F % q < q), Nat.cast_sub hr.le]
    field_simp

theorem landing_iff_fract (F W q : ℕ) (hq : 0 < q) :
    (∃ m, F ≤ m ∧ m < F + W ∧ q ∣ m) ↔ Int.fract (-((F : ℝ) / q)) < (W : ℝ) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [landing_iff F W q hq, fract_neg_div F q hq, div_lt_div_iff_of_pos_right hqR]
  exact Nat.cast_lt.symm

/-- The closed chain: a true landing (in ℕ) satisfies the candidate condition of the jump gear. -/
theorem landing_is_candidate (F W q : ℕ) (L e E Q : ℝ) (hq : 0 < q) (hQ : 0 < Q)
    (hQq : Q ≤ q) (hsplit : (F : ℝ) / q = L + e) (he0 : 0 ≤ e) (heE : e ≤ E)
    (hland : ∃ m, F ≤ m ∧ m < F + W ∧ q ∣ m) :
    Int.fract (-L) < (W : ℝ) / Q + E :=
  gear_candidate (F : ℝ) (q : ℝ) L e E (W : ℝ) Q hQ hQq (Nat.cast_nonneg W) hsplit he0 heE
    ((landing_iff_fract F W q hq).mp hland)

/-! ### 10. The step rule of the three-gap theorem

Model of the enumeration of jump_block(): w g = (B·g) mod M is the phase shift after g steps,
the current position is v < T. ga is the least step with w < T, gc the least with w > M − T
(α = w ga, β = M − w gc). Step: ga if v + α < T, gc if v ≥ β, otherwise ga + gc.
Theorems: a step lands below T again (step_lands) and skips no landing
(step_first), so the sequence of steps from the first landing visits every landing
(enumeration_complete). For every T ≤ M, including T > M/2, which the engine allows. -/

theorem addmod_cases {M x y : ℕ} (hx : x < M) (hy : y < M) :
    ((x + y) % M = x + y ∧ x + y < M) ∨ ((x + y) % M = x + y - M ∧ M ≤ x + y) := by
  by_cases h : x + y < M
  · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
  · have h' : M ≤ x + y := Nat.le_of_not_lt h
    refine Or.inr ⟨?_, h'⟩
    rw [Nat.mod_eq_sub_mod h', Nat.mod_eq_of_lt (by omega)]

/-- Assumptions on the rotation and on the steps ga, gc (the least ones, as in jump_block()). -/
structure GearRot (M T ga gc : ℕ) (w : ℕ → ℕ) : Prop where
  hTM : T ≤ M
  hw : ∀ g, w g < M
  hadd : ∀ a b, w (a + b) = (w a + w b) % M
  ga1 : 1 ≤ ga
  gaT : w ga < T
  gamin : ∀ g, 1 ≤ g → g < ga → T ≤ w g
  gc1 : 1 ≤ gc
  gcT : M < w gc + T
  gcmin : ∀ g, 1 ≤ g → g < gc → w g + T ≤ M

/-- A step of the jump gear from position v, exactly as in the loop of jump_block(). -/
def gearStep (M T ga gc : ℕ) (w : ℕ → ℕ) (v : ℕ) : ℕ :=
  if v + w ga < T then ga else if M - w gc ≤ v then gc else ga + gc

theorem GearRot.split {M T ga gc : ℕ} {w : ℕ → ℕ} (h : GearRot M T ga gc w)
    {a b : ℕ} (hab : b ≤ a) :
    (w a = w (a - b) + w b ∧ w (a - b) + w b < M) ∨
      (w a = w (a - b) + w b - M ∧ M ≤ w (a - b) + w b) := by
  have e := h.hadd (a - b) b
  rw [Nat.sub_add_cancel hab] at e
  rw [e]
  exact addmod_cases (h.hw _) (h.hw _)

theorem step_lands {M T ga gc v : ℕ} {w : ℕ → ℕ} (h : GearRot M T ga gc w) (hv : v < T) :
    (v + w (gearStep M T ga gc w v)) % M < T := by
  have hTM := h.hTM
  have hga := h.gaT
  have hgc := h.gcT
  have hwga := h.hw ga
  have hwgc := h.hw gc
  unfold gearStep
  split_ifs with h1 h2
  · rw [Nat.mod_eq_of_lt (by omega)]
    exact h1
  · rcases addmod_cases (by omega : v < M) hwgc with ⟨e, he⟩ | ⟨e, he⟩ <;> rw [e] <;> omega
  · rw [h.hadd, Nat.add_mod_mod]
    have hre : v + (w ga + w gc) = (v + w gc) + w ga := by omega
    rw [hre]
    rcases addmod_cases (by omega : v + w gc < M) hwga with ⟨e, he⟩ | ⟨e, he⟩ <;> rw [e] <;> omega

theorem step_first {M T ga gc v : ℕ} {w : ℕ → ℕ} (h : GearRot M T ga gc w) (hv : v < T) :
    ∀ g, 1 ≤ g → g < gearStep M T ga gc w v → T ≤ (v + w g) % M := by
  intro g hg1 hglt
  have hTM := h.hTM
  have hga := h.gaT
  have hgc := h.gcT
  have hwga := h.hw ga
  have hwgc := h.hw gc
  have hwg := h.hw g
  by_contra hret
  have hret' : (v + w g) % M < T := Nat.lt_of_not_le hret
  unfold gearStep at hglt
  rcases addmod_cases (by omega : v < M) hwg with ⟨e, he⟩ | ⟨e, he⟩ <;> rw [e] at hret'
  · -- no carry: w g < T, so g ≥ ga
    have hgga : ga ≤ g := by
      by_contra hc
      have := h.gamin g hg1 (Nat.lt_of_not_le hc)
      omega
    split_ifs at hglt with h1 h2
    · omega
    · rcases Nat.eq_or_lt_of_le hgga with hgeq | hgt
      · subst hgeq
        omega
      · have hm := h.gcmin (g - ga) (by omega) (by omega)
        have hw' := h.hw (g - ga)
        rcases h.split hgga with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;> omega
    · rcases Nat.eq_or_lt_of_le hgga with hgeq | hgt
      · subst hgeq
        omega
      · have hm := h.gcmin (g - ga) (by omega) (by omega)
        have hw' := h.hw (g - ga)
        rcases h.split hgga with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;> omega
  · -- with carry: w g > M − T, so g ≥ gc
    have hggc : gc ≤ g := by
      by_contra hc
      have := h.gcmin g hg1 (Nat.lt_of_not_le hc)
      omega
    split_ifs at hglt with h1 h2
    · have hm := h.gamin (ga - g) (by omega) (by omega)
      have hw' := h.hw (ga - g)
      rcases h.split (by omega : g ≤ ga) with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;> omega
    · omega
    · rcases Nat.eq_or_lt_of_le hggc with hgeq | hgt
      · subst hgeq
        omega
      · have hm := h.gamin (g - gc) (by omega) (by omega)
        have hw' := h.hw (g - gc)
        rcases h.split hggc with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;> omega

theorem gearStep_pos {M T ga gc : ℕ} {w : ℕ → ℕ} (h : GearRot M T ga gc w) (v : ℕ) :
    1 ≤ gearStep M T ga gc w v := by
  have := h.ga1
  have := h.gc1
  unfold gearStep
  split_ifs <;> omega

/-- The sequence of visited j: start at j0, then successive steps from position V j. -/
def visitSeq (M T ga gc : ℕ) (w V : ℕ → ℕ) (j0 : ℕ) : ℕ → ℕ
  | 0 => j0
  | k + 1 => visitSeq M T ga gc w V j0 k + gearStep M T ga gc w (V (visitSeq M T ga gc w V j0 k))

theorem visitSeq_succ (M T ga gc : ℕ) (w V : ℕ → ℕ) (j0 k : ℕ) :
    visitSeq M T ga gc w V j0 (k + 1) =
      visitSeq M T ga gc w V j0 k + gearStep M T ga gc w (V (visitSeq M T ga gc w V j0 k)) :=
  rfl

/-- The enumeration is complete: from the first landing j0 the steps visit every j with V j < T. -/
theorem enumeration_complete {M T ga gc j0 : ℕ} {w V : ℕ → ℕ} (h : GearRot M T ga gc w)
    (hV : ∀ j g, V (j + g) = (V j + w g) % M)
    (h0 : V j0 < T) (hfirst : ∀ j < j0, T ≤ V j) :
    ∀ j, V j < T → ∃ k, visitSeq M T ga gc w V j0 k = j := by
  have hinS : ∀ k, V (visitSeq M T ga gc w V j0 k) < T := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      rw [visitSeq_succ, hV]
      exact step_lands h ih
  have hgrow : ∀ k, j0 + k ≤ visitSeq M T ga gc w V j0 k := by
    intro k
    induction k with
    | zero => exact le_refl j0
    | succ k ih =>
      rw [visitSeq_succ]
      have := gearStep_pos h (V (visitSeq M T ga gc w V j0 k))
      omega
  intro j hj
  have hj0 : j0 ≤ j := by
    by_contra hc
    have := hfirst j (Nat.lt_of_not_le hc)
    omega
  have hex : ∃ k, j < visitSeq M T ga gc w V j0 (k + 1) :=
    ⟨j, by have := hgrow (j + 1); omega⟩
  classical
  obtain ⟨k, hk, hmin⟩ : ∃ k, j < visitSeq M T ga gc w V j0 (k + 1) ∧
      ∀ m < k, ¬ j < visitSeq M T ga gc w V j0 (m + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hlo : visitSeq M T ga gc w V j0 k ≤ j := by
    cases k with
    | zero => exact hj0
    | succ k' => exact Nat.le_of_not_lt (hmin k' (Nat.lt_succ_self k'))
  refine ⟨k, ?_⟩
  by_contra hne
  have hlt : visitSeq M T ga gc w V j0 k < j := lt_of_le_of_ne hlo hne
  rw [visitSeq_succ] at hk
  have hret := step_first h (hinS k) (j - visitSeq M T ga gc w V j0 k) (by omega) (by omega)
  rw [← hV, Nat.add_sub_of_le hlo] at hret
  omega

/-- The engine's concrete rotation: w g = (B·g) mod M, V j = (A + B·j) mod M. -/
theorem concrete_hadd (B M : ℕ) (a b : ℕ) :
    B * (a + b) % M = (B * a % M + B * b % M) % M := by
  rw [Nat.mul_add, Nat.add_mod]

theorem concrete_hV (A B M : ℕ) (j g : ℕ) :
    (A + B * (j + g)) % M = ((A + B * j) % M + B * g % M) % M := by
  rw [Nat.mul_add, ← Nat.add_assoc, Nat.add_mod (A + B * j) (B * g) M]

/-! ## 11. Euclid-style first-solution search (`jump_first_in`) -/

/-- `x` lands in `[l, r]` under multiplication by `a` modulo `m`. -/
def okIn (a m l r x : ℕ) : Prop := l ≤ a * x % m ∧ a * x % m ≤ r

/-- Faithful model of `jump_first_in` from `engine_jump_gear.h`
(unbounded naturals, so no u128 overflow is modelled). -/
def firstIn (a m l r : ℕ) : Option ℕ :=
  if hm : m = 0 then none
  else if l = 0 then some 0
  else if a % m = 0 then none
  else if a % m * ((l + a % m - 1) / (a % m)) ≤ r then some ((l + a % m - 1) / (a % m))
  else (firstIn (m % (a % m)) (a % m) ((a % m - r % (a % m)) % (a % m))
          ((a % m - l % (a % m)) % (a % m))).map (fun y => (l + m * y + a % m - 1) / (a % m))
termination_by m
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero hm)

/-- What the search must return: the least solution, or `none` if there is none. -/
def FirstSpec (a m l r : ℕ) : Option ℕ → Prop
  | some x => okIn a m l r x ∧ ∀ x' < x, ¬ okIn a m l r x'
  | none => ∀ x, ¬ okIn a m l r x

lemma divmod_of {b : ℕ} (hb : 0 < b) {Q c : ℕ} (hc : c < b) :
    (b * Q + c) / b = Q ∧ (b * Q + c) % b = c := by
  constructor
  · rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hc, add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

/-- Shape of the recursive case: `l` and `r` sit in one block of length `b`. -/
lemma rec_setup {b l r : ℕ} (hb : 0 < b) (hlr : l ≤ r)
    (hk : r < b * ((l + b - 1) / b)) :
    0 < l % b ∧ l % b ≤ r % b ∧ r % b < b ∧ r / b = l / b := by
  have h1 := Nat.div_add_mod l b
  have h2 := Nat.div_add_mod r b
  have h3 := Nat.div_add_mod (l + b - 1) b
  have h4 := Nat.mod_lt l hb
  have h5 := Nat.mod_lt r hb
  have h6 := Nat.mod_lt (l + b - 1) hb
  have hlam : 0 < l % b := by
    by_contra h0
    have hK : (l + b - 1) / b < l / b + 1 := Nat.lt_of_mul_lt_mul_left (a := b) (by
      have : b * (l / b + 1) = b * (l / b) + b := by ring
      omega)
    have := Nat.mul_le_mul_left b (Nat.lt_succ_iff.mp hK)
    omega
  have hqK : l / b < (l + b - 1) / b := Nat.lt_of_mul_lt_mul_left (a := b) (by omega)
  have hrq1 : r / b < (l + b - 1) / b := Nat.lt_of_mul_lt_mul_left (a := b) (by omega)
  have hK2 : (l + b - 1) / b < l / b + 2 := Nat.lt_of_mul_lt_mul_left (a := b) (by
      have : b * (l / b + 2) = b * (l / b) + 2 * b := by ring
      omega)
  have hrq2 : l / b < r / b + 1 := Nat.lt_of_mul_lt_mul_left (a := b) (by
      have : b * (r / b + 1) = b * (r / b) + b := by ring
      omega)
  have hrq : r / b = l / b := by omega
  refine ⟨hlam, ?_, h5, hrq⟩
  rw [hrq] at h2
  omega

/-- Backward: every solution `x` maps to a solution `y = b*x/m` of the reduced
problem, and `x` is recovered from `y` by the C formula. -/
lemma rec_back {b m l r x : ℕ} (hb : 0 < b) (hlam : 0 < l % b)
    (hlr' : l % b ≤ r % b) (hrb : r % b < b) (hrq : r / b = l / b)
    (hx : okIn b m l r x) :
    okIn (m % b) b ((b - r % b) % b) ((b - l % b) % b) (b * x / m) ∧
      (l + m * (b * x / m) + b - 1) / b = x := by
  obtain ⟨hx1, hx2⟩ := hx
  have e1 := Nat.div_add_mod (b * x) m
  have el := Nat.div_add_mod l b
  have er := Nat.div_add_mod r b
  rw [hrq] at er
  have hxq : l / b < x := Nat.lt_of_mul_lt_mul_left (a := b) (by omega)
  obtain ⟨u, hu⟩ : ∃ u, x = l / b + 1 + u := ⟨x - l / b - 1, by omega⟩
  have ex : b * x = b * (l / b) + b + b * u := by rw [hu]; ring
  have emy : m * (b * x / m) = b * u + (b + b * (l / b) - b * x % m) := by omega
  have hc : b + b * (l / b) - b * x % m < b := by omega
  obtain ⟨-, hm'⟩ := divmod_of hb (Q := u) hc
  constructor
  · unfold okIn
    rw [Nat.mod_mul_mod, emy, hm', Nat.mod_eq_of_lt (by omega : b - r % b < b),
      Nat.mod_eq_of_lt (by omega : b - l % b < b)]
    omega
  · rw [emy]
    have ex2 : b * (l / b + 1 + u) = b * (l / b) + b + b * u := by ring
    rw [show l + (b * u + (b + b * (l / b) - b * x % m)) + b - 1
        = b * (l / b + 1 + u) + (l + b - 1 - b * x % m) by omega]
    rw [(divmod_of hb (by omega : l + b - 1 - b * x % m < b)).1, hu]

/-- Forward: a solution `y` of the reduced problem gives a solution of the
original one via the C formula, and `y` is recovered as `b*x/m`. -/
lemma rec_fwd {b m l r y : ℕ} (hb : 0 < b) (hrm : r < m) (hlam : 0 < l % b)
    (hlr' : l % b ≤ r % b) (hrb : r % b < b) (hrq : r / b = l / b)
    (hy : okIn (m % b) b ((b - r % b) % b) ((b - l % b) % b) y) :
    okIn b m l r ((l + m * y + b - 1) / b) ∧ b * ((l + m * y + b - 1) / b) / m = y := by
  unfold okIn at hy
  rw [Nat.mod_mul_mod, Nat.mod_eq_of_lt (by omega : b - r % b < b),
    Nat.mod_eq_of_lt (by omega : b - l % b < b)] at hy
  obtain ⟨hy1, hy2⟩ := hy
  have e := Nat.div_add_mod (m * y) b
  have el := Nat.div_add_mod l b
  have er := Nat.div_add_mod r b
  rw [hrq] at er
  have ex2 : b * (l / b + 1 + m * y / b) = b * (l / b) + b + b * (m * y / b) := by ring
  have hx : (l + m * y + b - 1) / b = l / b + 1 + m * y / b := by
    rw [show l + m * y + b - 1 = b * (l / b + 1 + m * y / b) + (l % b + m * y % b - 1) by omega]
    exact (divmod_of hb (by omega)).1
  rw [hx]
  have ebx : b * (l / b + 1 + m * y / b) = m * y + (b * (l / b) + b - m * y % b) := by omega
  have ht : b * (l / b) + b - m * y % b < m := by omega
  obtain ⟨d1, d2⟩ := divmod_of (b := m) (Q := y) (by omega) ht
  unfold okIn
  rw [ebx, d2, d1]
  omega

/-- **Correctness of `jump_first_in`**: on `l ≤ r < m` it returns the least `x`
with `l ≤ a*x mod m ≤ r`, or `none` exactly when no such `x` exists. -/
theorem firstIn_spec (m : ℕ) : ∀ a l r, l ≤ r → r < m → FirstSpec a m l r (firstIn a m l r) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a l r hlr hrm
  have hm : m ≠ 0 := by omega
  have hok : ∀ x, okIn a m l r x ↔ okIn (a % m) m l r x := fun x => by
    unfold okIn; rw [Nat.mod_mul_mod]
  have hbm : a % m < m := Nat.mod_lt _ (by omega)
  rw [firstIn]
  split_ifs with hm0 hl hb0 hk
  · exact absurd hm0 hm
  · subst hl
    dsimp only [FirstSpec]
    exact ⟨by simp [okIn], fun x' hx' => absurd hx' (Nat.not_lt_zero _)⟩
  · dsimp only [FirstSpec]
    intro x hx
    rw [hok] at hx
    unfold okIn at hx
    rw [hb0] at hx
    simp at hx
    omega
  · dsimp only [FirstSpec]
    have hbpos : 0 < a % m := Nat.pos_of_ne_zero hb0
    have h3 := Nat.div_add_mod (l + a % m - 1) (a % m)
    have h6 := Nat.mod_lt (l + a % m - 1) hbpos
    constructor
    · rw [hok]; unfold okIn
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · intro x' hx' h
      rw [hok] at h; unfold okIn at h
      have := Nat.mul_le_mul_left (a % m) (Nat.succ_le_of_lt hx')
      have := Nat.mod_le (a % m * x') m
      have : a % m * (x' + 1) = a % m * x' + a % m := by ring
      rw [Nat.succ_eq_add_one] at *
      omega
  · have hbpos : 0 < a % m := Nat.pos_of_ne_zero hb0
    obtain ⟨hlam, hlr', hrb, hrq⟩ := rec_setup hbpos hlr (Nat.lt_of_not_le hk)
    have hspec := ih (a % m) hbm (m % (a % m)) ((a % m - r % (a % m)) % (a % m))
      ((a % m - l % (a % m)) % (a % m))
      (by rw [Nat.mod_eq_of_lt (by omega : a % m - r % (a % m) < a % m),
        Nat.mod_eq_of_lt (by omega : a % m - l % (a % m) < a % m)]; omega)
      (Nat.mod_lt _ hbpos)
    cases hfi : firstIn (m % (a % m)) (a % m) ((a % m - r % (a % m)) % (a % m))
        ((a % m - l % (a % m)) % (a % m)) with
    | none =>
      rw [hfi] at hspec
      dsimp only [FirstSpec] at hspec
      simp only [Option.map_none]
      dsimp only [FirstSpec]
      intro x hx
      rw [hok] at hx
      exact hspec _ (rec_back hbpos hlam hlr' hrb hrq hx).1
    | some y =>
      rw [hfi] at hspec
      dsimp only [FirstSpec] at hspec
      obtain ⟨hy, hmin⟩ := hspec
      simp only [Option.map_some]
      dsimp only [FirstSpec]
      refine ⟨(hok _).2 (rec_fwd hbpos hrm hlam hlr' hrb hrq hy).1, ?_⟩
      intro x' hx' h
      rw [hok] at h
      obtain ⟨hy', hx'eq⟩ := rec_back hbpos hlam hlr' hrb hrq h
      have hyle : y ≤ a % m * x' / m := Nat.le_of_not_lt (fun hlt => hmin _ hlt hy')
      have hmono : (l + m * y + a % m - 1) / (a % m)
          ≤ (l + m * (a % m * x' / m) + a % m - 1) / (a % m) :=
        Nat.div_le_div_right (by have := Nat.mul_le_mul_left m hyle; omega)
      omega

/-! ## 12. Wrapped window (`jump_first_range`): what produces `j0`, `ga`, `gc` -/

/-- Least solution of an arbitrary predicate, `none` meaning there is none. -/
def Least (P : ℕ → Prop) : Option ℕ → Prop
  | some x => P x ∧ ∀ x' < x, ¬ P x'
  | none => ∀ x, ¬ P x

lemma firstSpec_iff (a m l r : ℕ) (o : Option ℕ) : FirstSpec a m l r o ↔ Least (okIn a m l r) o := by
  cases o <;> rfl

lemma Least.congr {P Q : ℕ → Prop} (h : ∀ x, P x ↔ Q x) {o : Option ℕ} (hP : Least P o) :
    Least Q o := by
  cases o with
  | none => intro x hx; exact hP x ((h x).2 hx)
  | some x => exact ⟨(h x).1 hP.1, fun x' hx' hq => hP.2 x' hx' ((h x').2 hq)⟩

/-- `x1 < x2 ? x1 : x2` with `JUMP_NONE` acting as +∞. -/
def optMin : Option ℕ → Option ℕ → Option ℕ
  | none, o => o
  | o, none => o
  | some x, some y => some (min x y)

lemma Least.optMin {P Q : ℕ → Prop} {o1 o2 : Option ℕ} (h1 : Least P o1) (h2 : Least Q o2) :
    Least (fun x => P x ∨ Q x) (optMin o1 o2) := by
  cases o1 with
  | none =>
    cases o2 with
    | none => intro x hx; rcases hx with hx | hx; exacts [h1 x hx, h2 x hx]
    | some y =>
      exact ⟨Or.inr h2.1, fun x' hx' hq => hq.elim (h1 x') (h2.2 x' hx')⟩
  | some x =>
    cases o2 with
    | none =>
      exact ⟨Or.inl h1.1, fun x' hx' hq => hq.elim (h1.2 x' hx') (h2 x')⟩
    | some y =>
      refine ⟨?_, fun x' hx' hq => hq.elim (h1.2 x' (by omega)) (h2.2 x' (by omega))⟩
      rcases Nat.le_total x y with hxy | hxy
      · rw [min_eq_left hxy]; exact Or.inl h1.1
      · rw [min_eq_right hxy]; exact Or.inr h2.1

lemma mod_cases2 {x m : ℕ} (h : x < 2 * m) :
    (x < m ∧ x % m = x) ∨ (m ≤ x ∧ x % m = x - m) := by
  by_cases hx : x < m
  · exact Or.inl ⟨hx, Nat.mod_eq_of_lt hx⟩
  · refine Or.inr ⟨by omega, ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Shifting by `b` turns the window `[lo, hi]` into `[s, e]` with `s = (lo - b) mod m`,
`e = s + (hi - lo)`; when `e ≥ m` the window wraps into `[s, m-1] ∪ [0, e-m]`. -/
lemma shift_window {m b lo hi v : ℕ} (hb : b < m) (hlo : lo ≤ hi) (hhi : hi < m) (hv : v < m) :
    (lo ≤ (v + b) % m ∧ (v + b) % m ≤ hi) ↔
      ((lo + m - b) % m ≤ v ∧ v ≤ (lo + m - b) % m + (hi - lo)) ∨
        v + m ≤ (lo + m - b) % m + (hi - lo) := by
  rcases mod_cases2 (x := v + b) (m := m) (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases mod_cases2 (x := lo + m - b) (m := m) (by omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  rw [h2, h4] <;> omega

/-- Model of `jump_first_range` for a modulus `m` (the engine uses `m = 2^64`). -/
def firstRange (a b m lo hi : ℕ) : Option ℕ :=
  if (lo + m - b) % m + (hi - lo) < m then
    firstIn a m ((lo + m - b) % m) ((lo + m - b) % m + (hi - lo))
  else
    optMin (firstIn a m ((lo + m - b) % m) (m - 1))
      (firstIn a m 0 ((lo + m - b) % m + (hi - lo) - m))

/-- **Correctness of `jump_first_range`**: it returns the least `x` with
`lo ≤ (a*x + b) mod m ≤ hi`, or `none` exactly when there is no such `x`. -/
theorem firstRange_spec {a b m lo hi : ℕ} (hb : b < m) (hlo : lo ≤ hi) (hhi : hi < m) :
    Least (fun x => lo ≤ (a * x + b) % m ∧ (a * x + b) % m ≤ hi) (firstRange a b m lo hi) := by
  have hm : 0 < m := by omega
  have hs : (lo + m - b) % m < m := Nat.mod_lt _ hm
  have key : ∀ x, (lo ≤ (a * x + b) % m ∧ (a * x + b) % m ≤ hi) ↔
      ((lo + m - b) % m ≤ a * x % m ∧ a * x % m ≤ (lo + m - b) % m + (hi - lo)) ∨
        a * x % m + m ≤ (lo + m - b) % m + (hi - lo) := by
    intro x
    rw [← shift_window hb hlo hhi (Nat.mod_lt _ hm), Nat.add_mod, Nat.mod_eq_of_lt hb]
  unfold firstRange
  split_ifs with he
  · refine Least.congr (fun x => ?_) ((firstSpec_iff _ _ _ _ _).1
      (firstIn_spec m a _ _ (by omega) he))
    rw [key x]; unfold okIn
    have := Nat.mod_lt (a * x) hm
    omega
  · refine Least.congr (fun x => ?_) (Least.optMin
      ((firstSpec_iff _ _ _ _ _).1 (firstIn_spec m a _ (m - 1) (by omega) (by omega)))
      ((firstSpec_iff _ _ _ _ _).1 (firstIn_spec m a 0 _ (by omega) (by omega))))
    rw [key x]; unfold okIn
    have := Nat.mod_lt (a * x) hm
    omega


/-! ## 13. The 64-bit search of engine v7.2 (`jump_first_in64`, `_top`, `jump_first_range64`)

`M` stands for `2^64`. `none` models `JUMP_NONE64`; a result `x ≥ 2^64` at the top level
becomes `none` (`x >> 64`), which `cap` expresses. -/

/-- Results at or above `C` dropped (`JUMP_NONE64` behaves as +∞). -/
def cap (C : ℕ) (o : Option ℕ) : Option ℕ := o.bind (fun x => if x < C then some x else none)

lemma ceil_eq {a l : ℕ} (ha : 0 < a) : l / a + (if l % a = 0 then 0 else 1) = (l + a - 1) / a := by
  have e := Nat.div_add_mod l a
  have hr := Nat.mod_lt l ha
  split_ifs with h0
  · rw [show l + a - 1 = a * (l / a) + (a - 1) by omega, (divmod_of ha (by omega)).1]; rfl
  · rw [show l + a - 1 = a * (l / a + 1) + (l % a - 1) by rw [Nat.mul_add]; omega,
      (divmod_of ha (by omega)).1]

/-- `jump_first_in64` (precondition `a < m`, so no `a %= m`; ceiling as `l/a + (l%a != 0)`). -/
def firstIn64 (a m l r : ℕ) : Option ℕ :=
  if l = 0 then some 0
  else if ha : a = 0 then none
  else if a * (l / a + if l % a = 0 then 0 else 1) ≤ r then
    some (l / a + if l % a = 0 then 0 else 1)
  else (firstIn64 (m % a) a ((a - r % a) % a) ((a - l % a) % a)).map
    (fun y => (l + m * y + a - 1) / a)
termination_by a
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ha)

theorem firstIn64_eq (m : ℕ) : ∀ a l r, a < m → firstIn64 a m l r = firstIn a m l r := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro a l r ham
  have hm : ¬ m = 0 := by omega
  rw [firstIn64, firstIn]
  by_cases hl : l = 0
  · simp [hl, hm]
  by_cases ha : a = 0
  · simp [hl, ha, hm]
  simp only [hm, hl, ha, Nat.mod_eq_of_lt ham, ceil_eq (Nat.pos_of_ne_zero ha), ↓reduceIte,
    ↓reduceDIte]
  rw [ih a ham (m % a) _ _ (Nat.mod_lt _ (Nat.pos_of_ne_zero ha))]

/-- `jump_first_in_top`: the top level for `m = 2^64` in 128 bits, `(0 - a) % a = 2^64 mod a`. -/
def firstInTop (M a l r : ℕ) : Option ℕ :=
  if l = 0 then some 0
  else if a = 0 then none
  else if a * (l / a + if l % a = 0 then 0 else 1) ≤ r then
    some (l / a + if l % a = 0 then 0 else 1)
  else (firstIn64 ((M - a) % a) a ((a - r % a) % a) ((a - l % a) % a)).bind
    (fun y => if (l + M * y + a - 1) / a < M then some ((l + M * y + a - 1) / a) else none)

theorem firstInTop_eq {M a l r : ℕ} (ham : a < M) (hrM : r < M) :
    firstInTop M a l r = cap M (firstIn a M l r) := by
  have hm : ¬ M = 0 := by omega
  rw [firstInTop, firstIn]
  by_cases hl : l = 0
  · have : 0 < M := by omega
    simp [hl, hm, cap, this]
  by_cases ha : a = 0
  · simp [hl, ha, hm, cap]
  have hapos : 0 < a := Nat.pos_of_ne_zero ha
  simp only [hm, hl, ha, Nat.mod_eq_of_lt ham, ceil_eq hapos, ↓reduceIte, ↓reduceDIte]
  split_ifs with hk
  · have : (l + a - 1) / a ≤ a * ((l + a - 1) / a) := Nat.le_mul_of_pos_left _ hapos
    simp only [cap, Option.bind_some]
    split_ifs <;> first | rfl | omega
  · have hMa : (M - a) % a = M % a := by
      conv_rhs => rw [← Nat.sub_add_cancel ham.le]
      rw [Nat.add_mod_right]
    rw [hMa, firstIn64_eq a _ _ _ (Nat.mod_lt _ hapos)]
    cases firstIn (M % a) a ((a - r % a) % a) ((a - l % a) % a) <;> rfl

lemma cap_optMin (C : ℕ) (o1 o2 : Option ℕ) :
    cap C (optMin o1 o2) = optMin (cap C o1) (cap C o2) := by
  cases o1 with
  | none => cases o2 <;> rfl
  | some x =>
    cases o2 with
    | none => by_cases hx : x < C <;> simp [optMin, cap, hx]
    | some y =>
      by_cases hx : x < C <;> by_cases hy : y < C <;>
        simp [optMin, cap, hx, hy, min_lt_iff] <;> omega

/-- `jump_first_range64`: `s = lo - b` and `s + width` wrap modulo `2^64`. -/
def firstRange64 (M a b lo hi : ℕ) : Option ℕ :=
  if (lo + M - b) % M + (hi - lo) < M then
    firstInTop M a ((lo + M - b) % M) ((lo + M - b) % M + (hi - lo))
  else
    optMin (firstInTop M a ((lo + M - b) % M) (M - 1))
      (firstInTop M a 0 ((lo + M - b) % M + (hi - lo) - M))

theorem firstRange64_eq {M a b lo hi : ℕ} (ham : a < M) (hb : b < M) (hlo : lo ≤ hi)
    (hhi : hi < M) : firstRange64 M a b lo hi = cap M (firstRange a b M lo hi) := by
  have hs : (lo + M - b) % M < M := Nat.mod_lt _ (by omega)
  unfold firstRange64 firstRange
  split_ifs with he
  · exact firstInTop_eq ham he
  · rw [cap_optMin, firstInTop_eq ham (by omega), firstInTop_eq ham (by omega)]

lemma Least.capped {P : ℕ → Prop} {o : Option ℕ} (C : ℕ) (h : Least P o) :
    match cap C o with
    | some x => P x ∧ ∀ x' < x, ¬ P x'
    | none => ∀ x < C, ¬ P x := by
  cases o with
  | none => intro x _; exact h x
  | some x =>
    by_cases hx : x < C
    · have e : cap C (some x) = some x := by simp [cap, hx]
      rw [e]; exact h
    · have e : cap C (some x) = none := by simp [cap, hx]
      rw [e]
      intro x' hx' hp
      exact h.2 x' (by omega) hp

/-- **Correctness of `jump_first_range64`**: `some j` is the least `j` with
`lo ≤ (a j + b) mod 2^64 ≤ hi`; `none` means there is no such `j` below `2^64`. -/
theorem firstRange64_spec {M a b lo hi : ℕ} (ham : a < M) (hb : b < M) (hlo : lo ≤ hi)
    (hhi : hi < M) :
    match firstRange64 M a b lo hi with
    | some x => (lo ≤ (a * x + b) % M ∧ (a * x + b) % M ≤ hi) ∧
        ∀ x' < x, ¬ (lo ≤ (a * x' + b) % M ∧ (a * x' + b) % M ≤ hi)
    | none => ∀ x < M, ¬ (lo ≤ (a * x + b) % M ∧ (a * x + b) % M ≤ hi) := by
  rw [firstRange64_eq ham hb hlo hhi]
  exact (firstRange_spec hb hlo hhi).capped M

/-! ## 14. Three-gap steps by one subtractive Euclid walk (`jump_gaps`, engine v7.2) -/

lemma gaps_dec {x y k : ℕ} (hk : k ≠ 0) (hle : k ≤ (x - 1) / y) : x - k * y + y < x + y := by
  have hy : y ≠ 0 := by
    rintro rfl
    simp at hle
    omega
  have h1 : (x - 1) / y * y ≤ x - 1 := Nat.div_mul_le_self _ _
  have h2 : k * y ≤ (x - 1) / y * y := Nat.mul_le_mul_right _ hle
  have h3 : y ≤ k * y := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hk)
  omega

/-- Model of the loop of `jump_gaps`: `qa, da = B qa mod 2^64` and `qc, dc = -B qc mod 2^64`;
`none` is the C `return 0` (the caller falls back to `jump_block`). -/
def gapsLoop (T qa da qc dc : ℕ) : Option (ℕ × ℕ) :=
  if da < T ∧ dc < T then some (qa, qc)
  else if dc ≤ da then
    if _hk : min ((da - T) / dc + 1) ((da - 1) / dc) = 0 then none
    else gapsLoop T (qa + min ((da - T) / dc + 1) ((da - 1) / dc) * qc)
      (da - min ((da - T) / dc + 1) ((da - 1) / dc) * dc) qc dc
  else
    if _hk : min ((dc - T) / da + 1) ((dc - 1) / da) = 0 then none
    else gapsLoop T qa da (qc + min ((dc - T) / da + 1) ((dc - 1) / da) * qa)
      (dc - min ((dc - T) / da + 1) ((dc - 1) / da) * da)
termination_by da + dc
decreasing_by
  · exact gaps_dec _hk (min_le_right _ _)
  · have := gaps_dec _hk (min_le_right _ _); omega

/-- `jump_gaps(B, T, &ga, &gc)` with `M = 2^64`: `da = B`, `dc = 0 - B`. -/
def jumpGaps (M B T : ℕ) : Option (ℕ × ℕ) :=
  if B = 0 then none else gapsLoop T 1 B 1 (M - B)

/-- Lattice fact: `(qa, da)` and `(qc, -dc)` span all pairs `(g, r)` with `r ≡ B g (mod M)`. -/
lemma lattice_coords {M B a c da dc g r t1 t2 t3 : ℤ} (hM : M ≠ 0)
    (hdet : a * dc + c * da = M) (h1 : B * a = da + M * t1) (h2 : B * c = -dc + M * t2)
    (h3 : B * g = r + M * t3) :
    ∃ x y : ℤ, g = x * a + y * c ∧ r = x * da - y * dc := by
  have e1 : a * t2 - c * t1 = 1 := by
    have : M * (a * t2 - c * t1 - 1) = 0 := by linear_combination c * h1 - a * h2 + hdet
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hM
    · linarith
  have e2 : da * t2 + dc * t1 = B := by
    have : M * (da * t2 + dc * t1 - B) = 0 := by linear_combination -da * h2 - dc * h1 + B * hdet
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hM
    · linarith
  refine ⟨g * t2 - t3 * c, t3 * a - g * t1, ?_, ?_⟩
  · linear_combination (-g) * e1
  · linear_combination -h3 - g * e2 + t3 * hdet

lemma ga_min_core {a c da dc g r x y T : ℤ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hda : 1 ≤ da)
    (hdc : 1 ≤ dc) (hT : T ≤ da + dc) (hg1 : 1 ≤ g) (hga : g < a) (hr0 : 0 ≤ r)
    (hrT : r < T) (hg : g = x * a + y * c) (hr : r = x * da - y * dc) : False := by
  rcases le_or_gt x 0 with hx | hx <;> rcases le_or_gt y 0 with hy | hy
  · nlinarith
  · nlinarith
  · rcases eq_or_lt_of_le hy with hy0 | hy0
    · subst hy0; nlinarith
    · have : y ≤ -1 := by omega
      nlinarith
  · nlinarith

lemma gc_min_core {a c da dc g r x y T : ℤ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hda : 1 ≤ da)
    (hdc : 1 ≤ dc) (hT : T ≤ da + dc) (hg1 : 1 ≤ g) (hgc : g < c) (hr0 : r < 0)
    (hrT : -T < r) (hg : g = x * a + y * c) (hr : r = x * da - y * dc) : False := by
  rcases le_or_gt x 0 with hx | hx <;> rcases le_or_gt y 0 with hy | hy
  · nlinarith
  · rcases eq_or_lt_of_le hx with hx0 | hx0
    · subst hx0; nlinarith
    · have : x ≤ -1 := by omega
      nlinarith
  · nlinarith
  · nlinarith

/-- Loop invariant of `jump_gaps`. -/
structure GapInv (M B T qa da qc dc : ℕ) : Prop where
  qa1 : 1 ≤ qa
  qc1 : 1 ≤ qc
  da1 : 1 ≤ da
  dc1 : 1 ≤ dc
  ha : ∃ t : ℤ, (B : ℤ) * qa = da + M * t
  hc : ∃ t : ℤ, (B : ℤ) * qc = -(dc : ℤ) + M * t
  det : qa * dc + qc * da = M
  hT : T ≤ da + dc

/-- When the walk stops (`da < T`, `dc < T`), `qa` and `qc` are exactly the three-gap steps
`ga`, `gc` that `GearRot` asks for. -/
theorem GapInv.gearRot {M B T qa da qc dc : ℕ} (h : GapInv M B T qa da qc dc)
    (hda : da < T) (hdc : dc < T) : GearRot M T qa qc (fun g => B * g % M) := by
  have q1 := h.qa1; have q2 := h.qc1; have d1 := h.da1; have d2 := h.dc1
  have det := h.det
  have hMpos : 0 < M := by nlinarith
  have hdaM : da < M := by nlinarith
  have hdcM : dc < M := by nlinarith
  have hTM : T ≤ M := by have := h.hT; nlinarith
  obtain ⟨t1, ht1⟩ := h.ha
  obtain ⟨t2, ht2⟩ := h.hc
  have hdetZ : (qa : ℤ) * dc + qc * da = M := by exact_mod_cast det
  have hwa : B * qa % M = da := by
    have : ((B * qa % M : ℕ) : ℤ) = da := by
      push_cast
      rw [ht1, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity)
        (by exact_mod_cast hdaM)]
    exact_mod_cast this
  have hwc : B * qc % M = M - dc := by
    have : ((B * qc % M : ℕ) : ℤ) = (M : ℤ) - dc := by
      push_cast
      rw [show (B : ℤ) * qc = ((M : ℤ) - dc) + M * (t2 - 1) by linear_combination ht2,
        Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  have hsplit : ∀ g, (B : ℤ) * g = ((B * g % M : ℕ) : ℤ) + M * ((B * g / M : ℕ) : ℤ) := by
    intro g
    have := Nat.div_add_mod (B * g) M
    have : ((M * (B * g / M) + B * g % M : ℕ) : ℤ) = ((B * g : ℕ) : ℤ) := by rw [this]
    push_cast at this ⊢
    linarith
  refine ⟨hTM, fun g => Nat.mod_lt _ hMpos, fun a b => concrete_hadd B M a b, q1, ?_, ?_, q2,
    ?_, ?_⟩
  · simp only [hwa]; exact hda
  · intro g hg1 hgq
    by_contra hlt
    obtain ⟨x, y, hg, hr⟩ := lattice_coords (by exact_mod_cast hMpos.ne') hdetZ ht1 ht2 (hsplit g)
    exact ga_min_core (by exact_mod_cast q1) (by exact_mod_cast q2) (by exact_mod_cast d1)
      (by exact_mod_cast d2) (T := (T : ℤ)) (by exact_mod_cast h.hT) (by exact_mod_cast hg1)
      (by exact_mod_cast hgq) (by positivity) (by exact_mod_cast Nat.lt_of_not_le hlt) hg hr
  · simp only [hwc]; omega
  · intro g hg1 hgc
    by_contra hlt
    have hmod := Nat.mod_lt (B * g) hMpos
    have hs : (B : ℤ) * g = (((B * g % M : ℕ) : ℤ) - M) + M * ((B * g / M : ℕ) + 1 : ℤ) := by
      rw [hsplit g]; ring
    obtain ⟨x, y, hg, hr⟩ := lattice_coords (by exact_mod_cast hMpos.ne') hdetZ ht1 ht2 hs
    exact gc_min_core (by exact_mod_cast q1) (by exact_mod_cast q2) (by exact_mod_cast d1)
      (by exact_mod_cast d2) (T := (T : ℤ)) (by exact_mod_cast h.hT) (by exact_mod_cast hg1)
      (by exact_mod_cast hgc) (by omega) (by omega) hg hr

theorem GapInv.step_a {M B T qa da qc dc k : ℕ} (h : GapInv M B T qa da qc dc)
    (hk1 : k ≤ (da - T) / dc + 1) (hk2 : k ≤ (da - 1) / dc) (hTd : T ≤ da) :
    GapInv M B T (qa + k * qc) (da - k * dc) qc dc := by
  have d2 := h.dc1
  have e1 : k * dc ≤ da - 1 := (Nat.le_div_iff_mul_le (show 0 < dc by omega)).1 hk2
  have e2 : (da - T) / dc * dc ≤ da - T := Nat.div_mul_le_self _ _
  have e3 : k * dc ≤ ((da - T) / dc + 1) * dc := Nat.mul_le_mul_right _ hk1
  have e4 : ((da - T) / dc + 1) * dc = (da - T) / dc * dc + dc := by ring
  obtain ⟨t1, ht1⟩ := h.ha
  obtain ⟨t2, ht2⟩ := h.hc
  have hkd : k * dc ≤ da := by omega
  have hq1 := h.qa1
  have hT2 : T ≤ da - k * dc + dc := by omega
  have := h.da1
  have hd1 : 1 ≤ da - k * dc := by omega
  have hq2 : 1 ≤ qa + k * qc := by omega
  refine ⟨hq2, h.qc1, hd1, d2, ⟨t1 + k * t2, ?_⟩, h.hc, ?_, hT2⟩
  · push_cast [hkd]
    linear_combination ht1 + (k : ℤ) * ht2
  · have := h.det
    zify [hkd] at this ⊢
    linear_combination this

theorem GapInv.step_c {M B T qa da qc dc k : ℕ} (h : GapInv M B T qa da qc dc)
    (hk1 : k ≤ (dc - T) / da + 1) (hk2 : k ≤ (dc - 1) / da) (hTd : T ≤ dc) :
    GapInv M B T qa da (qc + k * qa) (dc - k * da) := by
  have d1 := h.da1
  have e1 : k * da ≤ dc - 1 := (Nat.le_div_iff_mul_le (show 0 < da by omega)).1 hk2
  have e2 : (dc - T) / da * da ≤ dc - T := Nat.div_mul_le_self _ _
  have e3 : k * da ≤ ((dc - T) / da + 1) * da := Nat.mul_le_mul_right _ hk1
  have e4 : ((dc - T) / da + 1) * da = (dc - T) / da * da + da := by ring
  obtain ⟨t1, ht1⟩ := h.ha
  obtain ⟨t2, ht2⟩ := h.hc
  have hkd : k * da ≤ dc := by omega
  have hq1 := h.qc1
  have hT2 : T ≤ da + (dc - k * da) := by omega
  have := h.dc1
  have hd1 : 1 ≤ dc - k * da := by omega
  have hq2 : 1 ≤ qc + k * qa := by omega
  refine ⟨h.qa1, hq2, d1, hd1, h.ha, ⟨t2 + k * t1, ?_⟩, ?_, hT2⟩
  · push_cast [hkd]
    linear_combination ht2 + (k : ℤ) * ht1
  · have := h.det
    zify [hkd] at this ⊢
    linear_combination this

theorem gapsLoop_spec {M B T : ℕ} (n : ℕ) :
    ∀ qa da qc dc, da + dc = n → GapInv M B T qa da qc dc → ∀ ga gc,
      gapsLoop T qa da qc dc = some (ga, gc) → GearRot M T ga gc (fun g => B * g % M) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro qa da qc dc hn hinv ga gc hres
  rw [gapsLoop] at hres
  split_ifs at hres with h1 h2 hk hk
  · simp only [Option.some.injEq, Prod.mk.injEq] at hres
    obtain ⟨rfl, rfl⟩ := hres
    exact hinv.gearRot h1.1 h1.2
  · exact ih _ (by have := gaps_dec hk (min_le_right _ _); omega) _ _ _ _ rfl
      (hinv.step_a (min_le_left _ _) (min_le_right _ _) (by omega)) ga gc hres
  · exact ih _ (by have := gaps_dec hk (min_le_right _ _); omega) _ _ _ _ rfl
      (hinv.step_c (min_le_left _ _) (min_le_right _ _) (by omega)) ga gc hres

/-- **Correctness of `jump_gaps`**: when it returns 1, `ga` and `gc` are the smallest
three-gap steps, i.e. `GearRot` holds and the step rule of `jump_block_quick` is complete. -/
theorem jumpGaps_spec {M B T ga gc : ℕ} (hB : B < M) (hT : T ≤ M)
    (h : jumpGaps M B T = some (ga, gc)) : GearRot M T ga gc (fun g => B * g % M) := by
  unfold jumpGaps at h
  split_ifs at h with hB0
  refine gapsLoop_spec _ 1 B 1 (M - B) rfl ⟨le_refl _, le_refl _, by omega, by omega,
    ⟨0, by ring⟩, ⟨1, by push_cast [hB.le]; ring⟩, by omega, by omega⟩ ga gc h

/-! ## 15. Assembly: the whole enumeration of a block, v7.0/v7.1 (`jump_block`) and v7.2
(`jump_block_quick`)

The candidate condition of a block is `V j = (A + B j) mod 2^64 < T`. Below: the C loop's
own arithmetic (`cStep`, with `alpha = B ga`, `beta = -B gc` and the overflow test
`v + alpha >= v`) follows `gearStep`, and with `j0`, `ga`, `gc` from the searches it visits
every candidate `j < J` before it breaks. -/

/-- One pass of the C loop body in 64-bit arithmetic: `(step in j, new v)`. -/
def cStep (M T ga gc alpha beta v : ℕ) : ℕ × ℕ :=
  if (v + alpha) % M < T ∧ v ≤ (v + alpha) % M then (ga, (v + alpha) % M)
  else if beta ≤ v then (gc, v - beta)
  else (ga + gc, (v + alpha + M - beta) % M)

theorem cStep_eq {M T ga gc v : ℕ} {w : ℕ → ℕ} (h : GearRot M T ga gc w) (hv : v < T) :
    cStep M T ga gc (w ga) (M - w gc) v =
      (gearStep M T ga gc w v, (v + w (gearStep M T ga gc w v)) % M) := by
  have hTM := h.hTM
  have hwa := h.hw ga
  have hwc := h.hw gc
  have hgcT := h.gcT
  by_cases c1 : v + w ga < T
  · have e : (v + w ga) % M = v + w ga := Nat.mod_eq_of_lt (by omega)
    have l1 : (v + w ga) % M < T ∧ v ≤ (v + w ga) % M := by omega
    simp only [cStep, gearStep, l1, c1, and_self, ↓reduceIte]
  · have l1 : ¬((v + w ga) % M < T ∧ v ≤ (v + w ga) % M) := by
      rcases addmod_cases (by omega : v < M) hwa with ⟨e, he⟩ | ⟨e, he⟩ <;> omega
    by_cases c2 : M - w gc ≤ v
    · simp only [cStep, gearStep, l1, c1, c2, ↓reduceIte, Prod.mk.injEq, true_and]
      rcases addmod_cases (by omega : v < M) hwc with ⟨e, he⟩ | ⟨e, he⟩ <;> omega
    · simp only [cStep, gearStep, l1, c1, c2, ↓reduceIte, Prod.mk.injEq, true_and]
      rw [h.hadd, Nat.add_mod_mod, show v + w ga + M - (M - w gc) = v + (w ga + w gc) by omega]

/-- The C loop from `(j0, v0)`: the sequence of `(j, v)` it walks through. -/
def cSeq (M T ga gc alpha beta j0 v0 : ℕ) : ℕ → ℕ × ℕ
  | 0 => (j0, v0)
  | k + 1 =>
    ((cSeq M T ga gc alpha beta j0 v0 k).1 +
        (cStep M T ga gc alpha beta (cSeq M T ga gc alpha beta j0 v0 k).2).1,
      (cStep M T ga gc alpha beta (cSeq M T ga gc alpha beta j0 v0 k).2).2)

theorem cSeq_eq {M T ga gc j0 : ℕ} {w V : ℕ → ℕ} (h : GearRot M T ga gc w)
    (hV : ∀ j g, V (j + g) = (V j + w g) % M) (h0 : V j0 < T) :
    ∀ k, cSeq M T ga gc (w ga) (M - w gc) j0 (V j0) k =
      (visitSeq M T ga gc w V j0 k, V (visitSeq M T ga gc w V j0 k)) := by
  have hinS : ∀ k, V (visitSeq M T ga gc w V j0 k) < T := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih => rw [visitSeq_succ, hV]; exact step_lands h ih
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [cSeq, ih, cStep_eq h (hinS k), visitSeq_succ, Prod.mk.injEq, true_and]
    rw [hV]

theorem visitSeq_mono {M T ga gc j0 : ℕ} {w V : ℕ → ℕ} {i k : ℕ}
    (hik : i ≤ k) : visitSeq M T ga gc w V j0 i ≤ visitSeq M T ga gc w V j0 k := by
  induction k with
  | zero => rw [Nat.le_zero.1 hik]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hik with rfl | hlt
    · exact le_refl _
    · have := ih (Nat.lt_succ_iff.1 hlt)
      rw [visitSeq_succ]
      omega

/-- The common core: with the least first candidate `j0` and steps satisfying `GearRot`,
the C loop reaches every candidate `j < J` without breaking before it. -/
theorem cLoop_complete {M T ga gc j0 J : ℕ} {w V : ℕ → ℕ} (h : GearRot M T ga gc w)
    (hV : ∀ j g, V (j + g) = (V j + w g) % M) (h0 : V j0 < T) (hfirst : ∀ j < j0, T ≤ V j) :
    ∀ j < J, V j < T → ∃ k, (cSeq M T ga gc (w ga) (M - w gc) j0 (V j0) k).1 = j ∧
      ∀ i ≤ k, (cSeq M T ga gc (w ga) (M - w gc) j0 (V j0) i).1 < J := by
  intro j hjJ hj
  obtain ⟨k, hk⟩ := enumeration_complete h hV h0 hfirst j hj
  refine ⟨k, by rw [cSeq_eq h hV h0, hk], fun i hi => ?_⟩
  rw [cSeq_eq h hV h0]
  have := visitSeq_mono (M := M) (T := T) (ga := ga) (gc := gc) (w := w) (V := V) (j0 := j0) hi
  omega

/-- v7.0 / v7.1: `ga`, `gc` from two `jump_first_range` searches (`ga += 1`, `gc += 1`)
satisfy `GearRot`. (The engine's `T` is at least `2 (2 J + 8) + 1`, so `2 ≤ T` holds.) -/
theorem gearRot_of_ranges {M T B xa xc : ℕ} (hB : B < M) (hT : 2 ≤ T) (hTM : T ≤ M)
    (ha : firstRange B B M 0 (T - 1) = some xa)
    (hc : firstRange B B M (M - T + 1) (M - 1) = some xc) :
    GearRot M T (xa + 1) (xc + 1) (fun g => B * g % M) := by
  have hM : 0 < M := by omega
  have sa := firstRange_spec (a := B) hB (Nat.zero_le (T - 1)) (by omega : T - 1 < M)
  have sc := firstRange_spec (a := B) hB (by omega : M - T + 1 ≤ M - 1) (by omega : M - 1 < M)
  rw [ha] at sa
  rw [hc] at sc
  obtain ⟨⟨-, a1⟩, a2⟩ := sa
  obtain ⟨⟨c1, -⟩, c2⟩ := sc
  have hshift : ∀ x, B * (x + 1) % M = (B * x + B) % M := fun x => by rw [Nat.mul_succ]
  refine ⟨hTM, fun g => Nat.mod_lt _ hM, fun a b => concrete_hadd B M a b, by omega, ?_, ?_,
    by omega, ?_, ?_⟩
  · show B * (xa + 1) % M < T
    rw [hshift]; omega
  · intro g hg1 hg
    by_contra hlt
    apply a2 (g - 1) (by omega)
    rw [← hshift, Nat.sub_add_cancel hg1]
    exact ⟨Nat.zero_le _, by omega⟩
  · show M < B * (xc + 1) % M + T
    rw [hshift]; omega
  · intro g hg1 hg
    by_contra hlt
    apply c2 (g - 1) (by omega)
    rw [← hshift, Nat.sub_add_cancel hg1]
    have := Nat.mod_lt (B * g) hM
    exact ⟨by omega, by omega⟩

/-- **Engine v7.0 / v7.1, `jump_block()`**: with `j0`, `ga`, `gc` from `jump_first_range`,
the loop visits every candidate `j < J` of the block (and when `j0` is `none` there is
no candidate at all). -/
theorem jump_block_complete {M T A B J j0 xa xc : ℕ} (hA : A < M) (hB : B < M) (hT : 2 ≤ T)
    (hTM : T ≤ M) (h0 : firstRange B A M 0 (T - 1) = some j0)
    (ha : firstRange B B M 0 (T - 1) = some xa)
    (hc : firstRange B B M (M - T + 1) (M - 1) = some xc) :
    ∀ j < J, (A + B * j) % M < T →
      ∃ k, (cSeq M T (xa + 1) (xc + 1) (B * (xa + 1) % M) (M - B * (xc + 1) % M) j0
          ((A + B * j0) % M) k).1 = j ∧
        ∀ i ≤ k, (cSeq M T (xa + 1) (xc + 1) (B * (xa + 1) % M) (M - B * (xc + 1) % M) j0
          ((A + B * j0) % M) i).1 < J := by
  have s0 := firstRange_spec (a := B) hA (Nat.zero_le (T - 1)) (by omega : T - 1 < M)
  rw [h0] at s0
  obtain ⟨⟨-, f1⟩, f2⟩ := s0
  have hc' : ∀ x, (B * x + A) % M = (A + B * x) % M := fun x => by rw [Nat.add_comm]
  exact cLoop_complete (V := fun j => (A + B * j) % M) (w := fun g => B * g % M)
    (gearRot_of_ranges hB hT hTM ha hc) (fun j g => concrete_hV A B M j g)
    (by simp only [← hc']; omega)
    (fun j hj => by
      by_contra hlt
      exact f2 j hj ⟨Nat.zero_le _, by rw [hc']; omega⟩)

theorem jump_block_none {M T A B : ℕ} (hA : A < M) (hT : 1 ≤ T) (hTM : T ≤ M)
    (h0 : firstRange B A M 0 (T - 1) = none) : ∀ j, ¬ (A + B * j) % M < T := by
  have s0 := firstRange_spec (a := B) hA (Nat.zero_le (T - 1)) (by omega : T - 1 < M)
  rw [h0] at s0
  intro j hj
  exact s0 j ⟨Nat.zero_le _, by rw [Nat.add_comm]; omega⟩

/-- **Engine v7.2, `jump_block_quick()`**: with `j0` from `jump_first_range64` and `ga`,
`gc` from `jump_gaps`, the loop visits every candidate `j < J` of the block. If
`jump_gaps` returns 0 the block goes to `jump_block()` (theorem above); if `j0` is
`JUMP_NONE64`, `jump_block_quick_none` shows there is no candidate below `2^64`. -/
theorem jump_block_quick_complete {M T A B J j0 ga gc : ℕ} (hA : A < M) (hB : B < M)
    (hT : 1 ≤ T) (hTM : T ≤ M) (h0 : firstRange64 M B A 0 (T - 1) = some j0)
    (hg : jumpGaps M B T = some (ga, gc)) :
    ∀ j < J, (A + B * j) % M < T →
      ∃ k, (cSeq M T ga gc (B * ga % M) (M - B * gc % M) j0 ((A + B * j0) % M) k).1 = j ∧
        ∀ i ≤ k, (cSeq M T ga gc (B * ga % M) (M - B * gc % M) j0 ((A + B * j0) % M) i).1 < J := by
  have s0 := firstRange64_spec (a := B) hB hA (Nat.zero_le (T - 1)) (by omega : T - 1 < M)
  rw [h0] at s0
  obtain ⟨⟨-, f1⟩, f2⟩ := s0
  have hc' : ∀ x, (B * x + A) % M = (A + B * x) % M := fun x => by rw [Nat.add_comm]
  exact cLoop_complete (V := fun j => (A + B * j) % M) (w := fun g => B * g % M)
    (jumpGaps_spec hB hTM hg) (fun j g => concrete_hV A B M j g)
    (by simp only [← hc']; omega)
    (fun j hj => by
      by_contra hlt
      exact f2 j hj ⟨Nat.zero_le _, by rw [hc']; omega⟩)

theorem jump_block_quick_none {M T A B : ℕ} (hA : A < M) (hB : B < M) (hT : 1 ≤ T)
    (hTM : T ≤ M) (h0 : firstRange64 M B A 0 (T - 1) = none) :
    ∀ j < M, ¬ (A + B * j) % M < T := by
  have s0 := firstRange64_spec (a := B) hB hA (Nat.zero_le (T - 1)) (by omega : T - 1 < M)
  rw [h0] at s0
  intro j hj hlt
  exact s0 j hj ⟨Nat.zero_le _, by rw [Nat.add_comm]; omega⟩


/-! ## 16. Bridge: a landing satisfies the 64.64 candidate condition `(A + B j) mod 2^64 < T`

Exact integer model of the block setup in `jump_block()` / `jump_block_quick()` (`M` is the
fixed-point unit and modulus `2^64`; no u128 overflow, see section 17):
`X0 = (first / Q) M + (first mod Q) M / Q`, `a = 30 first / Q`, `r1 = 30 first mod Q`,
`S = (a / Q) M + (a mod Q) M / Q + r1 M / Q^2`, `A = slack - X0 mod M`, `B = S mod M`.
(`(K0 << 64) | low` equals `K0 M + low` because `low < M`.) -/

def fixX0 (first Q M : ℕ) : ℕ := first / Q * M + first % Q * M / Q

def fixS (first Q M : ℕ) : ℕ :=
  30 * first / Q / Q * M + 30 * first / Q % Q * M / Q + 30 * first % Q * M / (Q * Q)

lemma split_div {Q : ℕ} (hQ : 0 < Q) (x M : ℕ) : x / Q * M + x % Q * M / Q = x * M / Q := by
  conv_rhs => rw [← Nat.div_add_mod x Q]
  rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_add_div hQ]

lemma fixX0_eq {first Q M : ℕ} (hQ : 0 < Q) : fixX0 first Q M = first * M / Q :=
  split_div hQ first M

/-- `S` underestimates `30 first M / Q^2` by less than 2 units. -/
lemma fixS_bounds {first Q M : ℕ} (hQ : 0 < Q) :
    fixS first Q M * (Q * Q) ≤ 30 * first * M ∧ 30 * first * M < (fixS first Q M + 2) * (Q * Q) := by
  have hS : fixS first Q M = 30 * first / Q * M / Q + 30 * first % Q * M / (Q * Q) := by
    unfold fixS; rw [split_div hQ]
  rw [hS]
  have hQQ : 0 < Q * Q := Nat.mul_pos hQ hQ
  have e0 := Nat.div_add_mod (30 * first) Q
  have e1 := Nat.div_add_mod (30 * first / Q * M) Q
  have e1' := Nat.mod_lt (30 * first / Q * M) hQ
  have e2 := Nat.div_add_mod (30 * first % Q * M) (Q * Q)
  have e2' := Nat.mod_lt (30 * first % Q * M) hQQ
  set a := 30 * first / Q
  set r := 30 * first % Q
  set u := a * M / Q
  set v := r * M / (Q * Q)
  have h30 : 30 * first * M = Q * (a * M) + r * M := by rw [← e0]; ring
  rw [Nat.mul_comm Q u] at e1
  rw [Nat.mul_comm (Q * Q) v] at e2
  have hu : u * Q ≤ a * M := by omega
  have hv : v * (Q * Q) ≤ r * M := by omega
  have hu2 : a * M < (u + 1) * Q := by rw [Nat.add_mul]; omega
  have hv2 : r * M < (v + 1) * (Q * Q) := by rw [Nat.add_mul]; omega
  have r1 : (u + v) * (Q * Q) = u * Q * Q + v * (Q * Q) := by ring
  have r2 : Q * (a * M) = a * M * Q := by ring
  have r3 : (u + v + 2) * (Q * Q) = (u + 1) * Q * Q + (v + 1) * (Q * Q) := by ring
  have m1 : u * Q * Q ≤ a * M * Q := Nat.mul_le_mul_right Q hu
  have m2 : a * M * Q < (u + 1) * Q * Q := Nat.mul_lt_mul_of_pos_right hu2 hQ
  constructor <;> omega

/-- `(q - first mod q) mod q` is the offset `g` of the one multiple: `q ∣ first + g`. -/
lemma offset_dvd {first q : ℕ} (hq : 0 < q) :
    first + (q - first % q) % q = q * (first / q + if first % q = 0 then 0 else 1) := by
  have e := Nat.div_add_mod first q
  have hr := Nat.mod_lt first hq
  split_ifs with h0
  · rw [h0, Nat.sub_zero, Nat.mod_self]; simp only [Nat.add_zero]; omega
  · rw [Nat.mod_eq_of_lt (by omega : q - first % q < q), Nat.mul_add]; omega

/-- **Bridge.** If the multiple of `q = Q + 30 j` lands at offset `g < span`, then
`(A + B j) mod M < T`, as long as `slack ≥ 2 j`, `T ≤ M` and
`T ≥ slack + 1 + E + (span - 1) M / Q` with `E ≥ first (30 j)^2 M / Q^3` (the tangent error). -/
theorem landing_candidate_fixed {M first span Q j T slack : ℕ} {E : ℚ} (hQ : 0 < Q)
    (hM : 0 < M) (hslack : 2 * j ≤ slack) (hTM : T ≤ M)
    (hE : (first : ℚ) * (30 * j) ^ 2 * M ≤ E * Q ^ 3)
    (hT : ((slack : ℚ) + 1 + E) * Q + ((span - 1 : ℕ) : ℚ) * M ≤ T * Q)
    (hland : (Q + 30 * j - first % (Q + 30 * j)) % (Q + 30 * j) < span) :
    ((slack + M - fixX0 first Q M % M) % M + fixS first Q M % M * j) % M < T := by
  set q := Q + 30 * j with hqdef
  have hq : 0 < q := by omega
  set g := (q - first % q) % q with hgdef
  set k := first / q + (if first % q = 0 then 0 else 1)
  have hk : first + g = q * k := offset_dvd hq
  set X0 := fixX0 first Q M
  set S := fixS first Q M
  have hX0 : X0 = first * M / Q := fixX0_eq hQ
  obtain ⟨hS1, hS2⟩ := fixS_bounds (first := first) (M := M) hQ
  have hX1 : X0 * Q ≤ first * M := by rw [hX0]; exact Nat.div_mul_le_self _ _
  have hX2 : first * M < (X0 + 1) * Q := by
    rw [hX0]; have := Nat.div_add_mod (first * M) Q; have := Nat.mod_lt (first * M) hQ; nlinarith
  have hgs : g ≤ span - 1 := by omega
  -- the integer w = slack + k M - X0 + S j, a representative of A + B j
  set w : ℤ := slack + k * M - X0 + S * j with hw
  -- rational facts
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hkq : (k : ℚ) * M = ((first : ℚ) + g) * M / q := by
    rw [show ((first : ℚ) + g) = (q : ℚ) * k by exact_mod_cast hk]; field_simp
  have hqQ : (q : ℚ) = Q + 30 * j := by rw [hqdef]; push_cast; ring
  -- tangent identity: first M / q = first M / Q - j (30 first M / Q^2) + first (30j)^2 M / (Q^2 q)
  have htan : (first : ℚ) * M / q =
      first * M / Q - j * (30 * first * M / Q ^ 2) + first * (30 * j) ^ 2 * M / (Q ^ 2 * q) := by
    rw [hqQ]; field_simp; ring
  have hX1q : (X0 : ℚ) * Q ≤ first * M := by exact_mod_cast hX1
  have hX2q : (first : ℚ) * M < (X0 + 1) * Q := by exact_mod_cast hX2
  have hS1q : (S : ℚ) * (Q * Q) ≤ 30 * first * M := by exact_mod_cast hS1
  have hS2q : (30 : ℚ) * first * M < (S + 2) * (Q * Q) := by exact_mod_cast hS2
  have hgq : (g : ℚ) ≤ ((span - 1 : ℕ) : ℚ) := by exact_mod_cast hgs
  have hjq : (0 : ℚ) ≤ j := by positivity
  have hwq : (w : ℚ) = slack + (first * M / q - X0 + S * j) + g * M / q := by
    rw [hw]; push_cast; rw [hkq]; field_simp; ring
  -- pieces of δ = first M / q - X0 + S j
  have d1 : (0 : ℚ) ≤ first * M / Q - X0 := by
    rw [sub_nonneg, le_div_iff₀ hQq]; exact hX1q
  have d2 : (first : ℚ) * M / Q - X0 < 1 := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hQq]; linarith
  have d3 : (0 : ℚ) ≤ 30 * first * M / Q ^ 2 - S := by
    rw [sub_nonneg, le_div_iff₀ (by positivity)]; nlinarith
  have d4 : (30 : ℚ) * first * M / Q ^ 2 - S ≤ 2 := by
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]; nlinarith
  have hEj0 : (0 : ℚ) ≤ first * (30 * j) ^ 2 * M / (Q ^ 2 * q) := by positivity
  have hEj : (first : ℚ) * (30 * j) ^ 2 * M / (Q ^ 2 * q) ≤ E := by
    rw [div_le_iff₀ (by positivity)]
    have : (Q : ℚ) ^ 3 ≤ Q ^ 2 * q := by rw [hqQ]; nlinarith
    have hE0 : 0 ≤ E := by
      by_contra hneg
      have : E * (Q : ℚ) ^ 3 < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) (by positivity)
      have : (0 : ℚ) ≤ first * (30 * j) ^ 2 * M := by positivity
      linarith
    exact le_trans hE (mul_le_mul_of_nonneg_left this hE0)
  have hgM : (g : ℚ) * M / q ≤ ((span - 1 : ℕ) : ℚ) * M / Q := by
    rw [div_le_div_iff₀ hqq hQq]
    have : (Q : ℚ) ≤ q := by rw [hqQ]; linarith
    calc (g : ℚ) * M * Q ≤ ((span - 1 : ℕ) : ℚ) * M * Q := by gcongr
      _ ≤ ((span - 1 : ℕ) : ℚ) * M * q := by gcongr
  have hjd : (j : ℚ) * (30 * first * M / Q ^ 2 - S) ≤ 2 * j := by
    have := mul_le_mul_of_nonneg_left d4 hjq; linarith
  have hjd0 : (0 : ℚ) ≤ j * (30 * first * M / Q ^ 2 - S) := mul_nonneg hjq d3
  have hslq : (2 : ℚ) * j ≤ slack := by exact_mod_cast hslack
  have hTq : (slack : ℚ) + 1 + E + ((span - 1 : ℕ) : ℚ) * M / Q ≤ T := by
    rw [← sub_nonneg]
    have : (T : ℚ) - (slack + 1 + E + ((span - 1 : ℕ) : ℚ) * M / Q) =
        (T * Q - ((slack + 1 + E) * Q + ((span - 1 : ℕ) : ℚ) * M)) / Q := by
      field_simp
    rw [this]
    exact div_nonneg (by linarith) hQq.le
  have hgM0 : (0 : ℚ) ≤ g * M / q := by positivity
  have hw0q : (0 : ℚ) ≤ w := by rw [hwq]; linarith
  have hwTq : (w : ℚ) < T := by rw [hwq]; linarith
  have hw0 : (0 : ℤ) ≤ w := by exact_mod_cast hw0q
  have hwT : w < (T : ℤ) := by exact_mod_cast hwTq
  have hXlt := Nat.mod_lt X0 hM
  have eA := Nat.div_add_mod (slack + M - X0 % M) M
  have eX := Nat.div_add_mod X0 M
  have eS := Nat.div_add_mod S M
  have key : (((slack + M - X0 % M) % M + S % M * j : ℕ) : ℤ) =
      w + M * (1 + ((X0 / M : ℕ) : ℤ) - ((slack + M - X0 % M) / M : ℕ) - ((S / M : ℕ) : ℤ) * j
        - k) := by
    have hle : X0 % M ≤ slack + M := by omega
    zify [hle] at eA eX eS ⊢
    rw [hw]
    linear_combination eA - eX + (j : ℤ) * eS
  have hfin : (((slack + M - X0 % M) % M + S % M * j) % M : ℕ) = (w : ℤ) := by
    rw [Int.natCast_mod, key, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt hw0 (by have h : (T : ℤ) ≤ M := (by exact_mod_cast hTM); omega)]
  have : ((((slack + M - X0 % M) % M + S % M * j) % M : ℕ) : ℤ) < T := by rw [hfin]; exact hwT
  exact_mod_cast this

/-! ## 17. u128: when the C setup computes exactly `fixX0` and `fixS` — the bound

The C expressions with every u128 operation reduced mod `2^128` (u64 casts mod `2^64`).
They equal the exact `fixX0`, `fixS` of section 16 when `Q < 2^64`, `first < 2^62 Q`
(the caller's `jump_from ≥ first / 2^62 + 1`), `Q ≥ 8` and **`30 first < 2^128`**, i.e.
`first < 2^128 / 30 ≈ 1.134·10^37`. The caller only switches the gear off from
`first ≥ 2^126`; `cS_overflow` shows a case in between where `S` is wrong. -/

/-- `X0 = (K0 << 64) | (uint64_t)((R0 << 64) / Q)` in u128. -/
def cX0 (first Q : ℕ) : ℕ :=
  (first / Q) <<< 64 % 2 ^ 128 ||| ((first - first / Q * Q) <<< 64 % 2 ^ 128) / Q % 2 ^ 64

/-- `S = ((a / Q) << 64) + ((a % Q) << 64) / Q + (r1 << 64) / (Q * Q)` in u128,
with `f30 = 30 * first`, `a = f30 / Q`, `r1 = f30 - a * Q`. -/
def cS (first Q : ℕ) : ℕ :=
  ((30 * first % 2 ^ 128 / Q / Q) <<< 64 % 2 ^ 128 +
      ((30 * first % 2 ^ 128 / Q % Q) <<< 64 % 2 ^ 128) / Q +
      ((30 * first % 2 ^ 128 - 30 * first % 2 ^ 128 / Q * Q) <<< 64 % 2 ^ 128) / (Q * Q % 2 ^ 128))
    % 2 ^ 128

theorem cX0_eq {first Q : ℕ} (hQ : 0 < Q) (hQ64 : Q < 2 ^ 64) (hK : first < 2 ^ 62 * Q) :
    cX0 first Q = fixX0 first Q (2 ^ 64) := by
  have hK0 : first / Q < 2 ^ 62 := by rw [Nat.div_lt_iff_lt_mul hQ]; linarith
  have hR : first - first / Q * Q = first % Q := by
    have := Nat.div_add_mod first Q; rw [Nat.mul_comm] at this; omega
  have hRlt : first % Q < Q := Nat.mod_lt _ hQ
  have hlow : first % Q * 2 ^ 64 / Q < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul hQ]; nlinarith
  unfold cX0 fixX0
  rw [hR, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by nlinarith : first / Q * 2 ^ 64 < 2 ^ 128),
    Nat.mod_eq_of_lt (by nlinarith : first % Q * 2 ^ 64 < 2 ^ 128), Nat.mod_eq_of_lt hlow,
    Nat.mul_comm (first / Q), ← Nat.two_pow_add_eq_or_of_lt hlow, Nat.mul_comm]

theorem cS_eq {first Q : ℕ} (hQ8 : 8 ≤ Q) (hQ64 : Q < 2 ^ 64) (hK : first < 2 ^ 62 * Q)
    (h30 : 30 * first < 2 ^ 128) : cS first Q = fixS first Q (2 ^ 64) := by
  have hQ : 0 < Q := by omega
  have hQQ : Q * Q < 2 ^ 128 := by
    calc Q * Q < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' hQ64 hQ64
      _ = 2 ^ 128 := by norm_num
  have hr : 30 * first - 30 * first / Q * Q = 30 * first % Q := by
    have h1 := Nat.div_add_mod (30 * first) Q
    have h2 : Q * (30 * first / Q) = 30 * first / Q * Q := Nat.mul_comm _ _
    omega
  set a := 30 * first / Q
  have hr1 : 30 * first % Q < Q := Nat.mod_lt _ hQ
  have hamod : a % Q < Q := Nat.mod_lt _ hQ
  -- a / Q < 2^64 because 30 first / Q^2 < 30 · 2^62 / Q ≤ 2^64
  have haQ : a / Q < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul hQ, Nat.div_lt_iff_lt_mul hQ]
    nlinarith
  unfold cS
  rw [Nat.mod_eq_of_lt h30, hr, Nat.mod_eq_of_lt hQQ, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by nlinarith : a / Q * 2 ^ 64 < 2 ^ 128),
    Nat.mod_eq_of_lt (by nlinarith : a % Q * 2 ^ 64 < 2 ^ 128),
    Nat.mod_eq_of_lt (by nlinarith : 30 * first % Q * 2 ^ 64 < 2 ^ 128)]
  have hfix : a / Q * 2 ^ 64 + a % Q * 2 ^ 64 / Q + 30 * first % Q * 2 ^ 64 / (Q * Q)
      = fixS first Q (2 ^ 64) := rfl
  rw [hfix]
  apply Nat.mod_eq_of_lt
  have hb := (fixS_bounds (first := first) (M := 2 ^ 64) hQ).1
  have : 30 * first * 2 ^ 64 < 2 ^ 128 * (Q * Q) := by nlinarith
  by_contra hge
  have := Nat.mul_le_mul_right (Q * Q) (Nat.le_of_not_lt hge)
  omega

/-- Between `2^128 / 30` and `2^126` the guard lets the gear run, but `S` is wrong:
here `first = 1.2·10^37` (gear on: `first < 2^126`, `first / 2^62 < Q ≤ √first`). -/
theorem cS_overflow :
    let first := 12 * 10 ^ 36
    let Q := 3 * 10 ^ 18 + 1
    first < 2 ^ 126 ∧ first / 2 ^ 62 + 1 ≤ Q ∧ Q * Q ≤ first ∧
      cS first Q ≠ fixS first Q (2 ^ 64) := by
  decide


/-! ## 18. The threshold `T` in `double`: rounding never pushes it below what the bridge needs

Standard model of IEEE-754 round-to-nearest without underflow (every value here is 0 or above
`10^-36`): each operation and each u64→double conversion returns `x (1 + δ)`, `|δ| ≤ u = 2^-53`.
The C expressions, evaluated left to right:
`e_ulp = first * d * d / (Q * Q * Q) * 2^64`,
`t_d = span / Q * 2^64 + e_ulp * 1.001 + 2.0 * slack + 1`.
Result (`t_double_ok`): `t_d ≥ slack + 2 + E + (span - 1) 2^64 / Q`, `E = first d^2 2^64 / Q^3`,
for `1 ≤ span ≤ 2^48`, `Q ≥ 1`, `slack ≥ 3`. -/

/-- `y` is `x` rounded with relative error at most `u`. -/
def Rnd (u x y : ℝ) : Prop := |y - x| ≤ u * |x|

lemma rnd_lb {u x y : ℝ} (hx : 0 ≤ x) (h : Rnd u x y) : (1 - u) * x ≤ y := by
  unfold Rnd at h; rw [abs_of_nonneg hx] at h; linarith [(abs_le.mp h).1]

lemma rnd_ub {u x y : ℝ} (hx : 0 ≤ x) (h : Rnd u x y) : y ≤ (1 + u) * x := by
  unfold Rnd at h; rw [abs_of_nonneg hx] at h; linarith [(abs_le.mp h).2]

lemma lb_mul {u a b y A B α β : ℝ} (hu1 : 0 ≤ 1 - u) (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (ha : α * A ≤ a) (hb : β * B ≤ b) (h : Rnd u (a * b) y) :
    α * β * (1 - u) * (A * B) ≤ y := by
  have hab : α * β * (A * B) ≤ a * b :=
    calc α * β * (A * B) = (α * A) * (β * B) := by ring
      _ ≤ a * b := mul_le_mul ha hb (mul_nonneg hβ hB) (le_trans (mul_nonneg hα hA) ha)
  have h0 : 0 ≤ a * b := le_trans (mul_nonneg (mul_nonneg hα hβ) (mul_nonneg hA hB)) hab
  calc α * β * (1 - u) * (A * B) = (1 - u) * (α * β * (A * B)) := by ring
    _ ≤ (1 - u) * (a * b) := mul_le_mul_of_nonneg_left hab hu1
    _ ≤ y := rnd_lb h0 h

lemma lb_div {u a d y A D α γ : ℝ} (hu1 : 0 ≤ 1 - u) (hA : 0 ≤ A) (hα : 0 ≤ α) (hD : 0 < D)
    (hγ : 0 < γ) (ha : α * A ≤ a) (hd0 : 0 < d) (hd : d ≤ γ * D) (h : Rnd u (a / d) y) :
    α / γ * (1 - u) * (A / D) ≤ y := by
  have ha0 : 0 ≤ a := le_trans (mul_nonneg hα hA) ha
  have hq : α / γ * (A / D) ≤ a / d :=
    calc α / γ * (A / D) = (α * A) / (γ * D) := by field_simp
      _ ≤ a / (γ * D) := div_le_div_of_nonneg_right ha (mul_pos hγ hD).le
      _ ≤ a / d := div_le_div_of_nonneg_left ha0 hd0 hd
  have h0 : 0 ≤ α / γ * (A / D) := mul_nonneg (div_nonneg hα hγ.le) (div_nonneg hA hD.le)
  calc α / γ * (1 - u) * (A / D) = (1 - u) * (α / γ * (A / D)) := by ring
    _ ≤ (1 - u) * (a / d) := mul_le_mul_of_nonneg_left hq hu1
    _ ≤ y := rnd_lb (le_trans h0 hq) h

lemma ub_mul {u a b y A B α β : ℝ} (hu : 0 ≤ u) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hα : 0 ≤ α)
    (hA : 0 ≤ A) (ha : a ≤ α * A) (hb : b ≤ β * B) (h : Rnd u (a * b) y) :
    y ≤ α * β * (1 + u) * (A * B) := by
  have hab : a * b ≤ α * β * (A * B) :=
    calc a * b ≤ (α * A) * (β * B) := mul_le_mul ha hb hb0 (mul_nonneg hα hA)
      _ = α * β * (A * B) := by ring
  calc y ≤ (1 + u) * (a * b) := rnd_ub (mul_nonneg ha0 hb0) h
    _ ≤ (1 + u) * (α * β * (A * B)) := mul_le_mul_of_nonneg_left hab (by linarith)
    _ = α * β * (1 + u) * (A * B) := by ring

lemma lb_add {u a b y P R : ℝ} (hu1 : 0 ≤ 1 - u) (hP : 0 ≤ P) (hR : 0 ≤ R) (ha : P ≤ a)
    (hb : R ≤ b) (h : Rnd u (a + b) y) : (1 - u) * (P + R) ≤ y :=
  calc (1 - u) * (P + R) ≤ (1 - u) * (a + b) := mul_le_mul_of_nonneg_left (by linarith) hu1
    _ ≤ y := rnd_lb (by linarith) h

theorem t_double_ok {span Q first d slack spanD QD firstD dD slackD p1 p2 q1 q2 e1 eU c e2
      s1 s2 a1 b1 a2 t : ℝ} (M u : ℝ) (hu : u = 1 / 2 ^ 53) (hM : M = 2 ^ 64)
    (hspan : 1 ≤ span) (hspan48 : span ≤ 2 ^ 48) (hQ : 1 ≤ Q) (hf : 0 ≤ first) (hd : 0 ≤ d)
    (hsl : 3 ≤ slack)
    (r1 : Rnd u span spanD) (r2 : Rnd u Q QD) (r3 : Rnd u first firstD) (r4 : Rnd u d dD)
    (r5 : Rnd u slack slackD) (r6 : Rnd u (firstD * dD) p1) (r7 : Rnd u (p1 * dD) p2)
    (r8 : Rnd u (QD * QD) q1) (r9 : Rnd u (q1 * QD) q2) (r10 : Rnd u (p2 / q2) e1)
    (r11 : Rnd u (e1 * M) eU) (r12 : Rnd u 1.001 c) (r13 : Rnd u (eU * c) e2)
    (r14 : Rnd u (spanD / QD) s1) (r15 : Rnd u (s1 * M) s2) (r16 : Rnd u (s2 + e2) a1)
    (r17 : Rnd u (2 * slackD) b1) (r18 : Rnd u (a1 + b1) a2) (r19 : Rnd u (a2 + 1) t) :
    slack + 2 + first * d ^ 2 * M / Q ^ 3 + (span - 1) * M / Q ≤ t := by
  have hu0 : 0 ≤ u := by rw [hu]; norm_num
  have hv : 0 ≤ 1 - u := by rw [hu]; norm_num
  have hw : 0 < 1 + u := by rw [hu]; norm_num
  have hM0 : 0 ≤ M := by rw [hM]; norm_num
  have hQ0 : 0 < Q := by linarith
  have hsp0 : 0 ≤ span := by linarith
  have hsl0 : 0 ≤ slack := by linarith
  have one : (1 : ℝ) * M ≤ M := by linarith
  -- conversions
  have l_sp : (1 - u) * span ≤ spanD := rnd_lb hsp0 r1
  have l_Q : (1 - u) * Q ≤ QD := rnd_lb hQ0.le r2
  have u_Q : QD ≤ (1 + u) * Q := rnd_ub hQ0.le r2
  have l_f : (1 - u) * first ≤ firstD := rnd_lb hf r3
  have l_d : (1 - u) * d ≤ dD := rnd_lb hd r4
  have l_sl : (1 - u) * slack ≤ slackD := rnd_lb hsl0 r5
  have hQD : 0 < QD := lt_of_lt_of_le (mul_pos (by rw [hu]; norm_num) hQ0) l_Q
  have hdD : 0 ≤ dD := le_trans (mul_nonneg hv hd) l_d
  -- e_ulp
  have l_p1 := lb_mul hv hf hd hv hv l_f l_d r6
  have l_p2 := lb_mul hv (mul_nonneg hf hd) hd (by positivity) hv l_p1 l_d r7
  have u_q1 := ub_mul hu0 hQD.le hQD.le hw.le hQ0.le u_Q u_Q r8
  have l_q1 := lb_mul hv hQ0.le hQ0.le hv hv l_Q l_Q r8
  have hq1 : 0 < q1 :=
    lt_of_lt_of_le (mul_pos (by rw [hu]; norm_num) (mul_pos hQ0 hQ0)) l_q1
  have u_q2 := ub_mul hu0 hq1.le hQD.le (by positivity) (mul_nonneg hQ0.le hQ0.le) u_q1 u_Q r9
  have l_q2 := lb_mul hv (mul_nonneg hQ0.le hQ0.le) hQ0.le (by positivity) hv l_q1 l_Q r9
  have hq2 : 0 < q2 := lt_of_lt_of_le (by
    have h3 : 0 < Q * Q * Q := by positivity
    have : 0 < (1 - u) * (1 - u) * (1 - u) * (1 - u) * (1 - u) := by rw [hu]; norm_num
    positivity) l_q2
  have l_e1 := lb_div hv (mul_nonneg (mul_nonneg hf hd) hd) (by positivity)
    (by positivity : (0 : ℝ) < Q * Q * Q) (by positivity) l_p2 hq2 u_q2 r10
  have l_eU := lb_mul hv (by positivity) hM0 (by
      have : 0 ≤ (1 - u) * (1 - u) * (1 - u) * (1 - u) * (1 - u) := by positivity
      positivity) zero_le_one l_e1 one r11
  have l_c : (1 - u) * 1.001 ≤ c := rnd_lb (by norm_num) r12
  have l_e2 := lb_mul hv (by positivity) (by norm_num : (0 : ℝ) ≤ 1.001) (by
      have : 0 ≤ (1 - u) * (1 - u) * (1 - u) * (1 - u) * (1 - u) := by positivity
      positivity) hv l_eU l_c r13
  -- span / Q * 2^64 and 2 * slack
  have l_s1 := lb_div hv hsp0 hv hQ0 hw l_sp hQD u_Q r14
  have l_s2 := lb_mul hv (div_nonneg hsp0 hQ0.le) hM0 (by positivity) zero_le_one l_s1 one r15
  have l_b1 := lb_mul hv (by norm_num : (0 : ℝ) ≤ 2) hsl0 zero_le_one hv
    (by linarith : (1 : ℝ) * 2 ≤ 2) l_sl r17
  -- sums
  have l_a1 := lb_add hv (by positivity) (by positivity) l_s2 l_e2 r16
  have l_a2 := lb_add hv (by positivity) (by positivity) l_a1 l_b1 r18
  have l_t := lb_add hv (by positivity) zero_le_one l_a2 (le_refl 1) r19
  -- collect: t ≥ αs X + αe E + αb slack + α1
  set X := span / Q * M with hX
  set E := first * d * d / (Q * Q * Q) * M with hE
  have hX0 : 0 ≤ X := by positivity
  have hE0 : 0 ≤ E := by positivity
  set αs := (1 - u) * ((1 - u) * ((1 - u) * ((1 - u) / (1 + u) * (1 - u) * 1 * (1 - u))))
  set αe := (1 - u) * ((1 - u) * ((1 - u) *
    ((1 - u) * (1 - u) * (1 - u) * (1 - u) * (1 - u) / ((1 + u) * (1 + u) * (1 + u) * (1 + u) * (1 + u))
      * (1 - u) * 1 * (1 - u) * (1 - u) * (1 - u) * 1.001)))
  set αb := (1 - u) * ((1 - u) * (1 * (1 - u) * (1 - u) * 2))
  have collect : αs * X + αe * E + αb * slack + (1 - u) ≤ t := by
    have e : αs * X + αe * E + αb * slack + (1 - u) =
      (1 - u) * ((1 - u) * ((1 - u) * ((1 - u) / (1 + u) * (1 - u) * 1 * (1 - u) * X +
        (1 - u) * (1 - u) * (1 - u) * (1 - u) * (1 - u) /
          ((1 + u) * (1 + u) * (1 + u) * (1 + u) * (1 + u)) * (1 - u) * 1 * (1 - u) * (1 - u) *
            (1 - u) * (E * 1.001)) + 1 * (1 - u) * (1 - u) * (2 * slack)) + 1) := by ring
    rw [e]; exact l_t
  -- numeric factors with u = 2^-53
  have fs : 1 - 1 / 2 ^ 49 ≤ αs := by simp only [αs]; rw [hu]; norm_num
  have fe : 1 ≤ αe := by simp only [αe]; rw [hu]; norm_num
  have fb : 2 - 1 / 2 ^ 49 ≤ αb := by simp only [αb]; rw [hu]; norm_num
  have f1 : 1 - 1 / 2 ^ 52 ≤ 1 - u := by rw [hu]; norm_num
  -- the target in the same terms
  have hEt : first * d ^ 2 * M / Q ^ 3 = E := by rw [hE]; field_simp
  have hXt : (span - 1) * M / Q = X - M / Q := by rw [hX]; field_simp
  rw [hEt, hXt]
  have hY0 : 0 ≤ M / Q := by positivity
  have hXY : X = span * (M / Q) := by rw [hX]; ring
  have g1 : (1 - 1 / 2 ^ 49) * X ≤ αs * X := mul_le_mul_of_nonneg_right fs hX0
  have g2 : E ≤ αe * E := by have := mul_le_mul_of_nonneg_right fe hE0; linarith
  have g3 : (2 - 1 / 2 ^ 49) * slack ≤ αb * slack := mul_le_mul_of_nonneg_right fb hsl0
  have g4 : 1 / 2 ^ 49 * X ≤ M / Q := by
    rw [hXY]
    have := mul_le_mul_of_nonneg_right hspan48 hY0
    have h48 : (1 : ℝ) / 2 ^ 49 * (2 ^ 48 * (M / Q)) ≤ M / Q :=
      calc (1 : ℝ) / 2 ^ 49 * (2 ^ 48 * (M / Q)) = (1 / 2 ^ 49 * 2 ^ 48) * (M / Q) := by ring
        _ ≤ 1 * (M / Q) := mul_le_mul_of_nonneg_right (by norm_num) hY0
        _ = M / Q := one_mul _
    calc 1 / 2 ^ 49 * (span * (M / Q)) ≤ 1 / 2 ^ 49 * (2 ^ 48 * (M / Q)) :=
          mul_le_mul_of_nonneg_left this (by norm_num)
      _ ≤ M / Q := h48
  linarith only [collect, g1, g2, g3, g4, f1, hsl]

/-! ## 19. `jump_landing`: the checked offset is exact, and its u128 estimate does not wrap -/

/-- `jump_landing(first, q, k)`: both while loops in closed form
(add `q` until `kq ≥ first`, then subtract `q` while `kq - first ≥ q`). -/
def cLanding (first q k : ℕ) : ℕ :=
  (if k * q < first then k * q + q * ((first - k * q + q - 1) / q) else k * q) -
    q * (((if k * q < first then k * q + q * ((first - k * q + q - 1) / q) else k * q) - first) / q)
    - first

lemma sub_mod_of_mul {first q m : ℕ} (hq : 0 < q) (hge : first ≤ q * m) :
    (q * m - first) % q = (q - first % q) % q := by
  have hk := offset_dvd (first := first) hq
  set g := (q - first % q) % q
  set k0 := first / q + if first % q = 0 then 0 else 1
  have hg : g < q := Nat.mod_lt _ hq
  have hmk : k0 ≤ m := by
    by_contra h
    have : q * (m + 1) ≤ q * k0 := Nat.mul_le_mul_left q (by omega)
    have : q * (m + 1) = q * m + q := by ring
    omega
  obtain ⟨t, rfl⟩ : ∃ t, m = k0 + t := ⟨m - k0, by omega⟩
  have e : q * (k0 + t) - first = q * t + g := by
    have : q * (k0 + t) = q * k0 + q * t := by ring
    omega
  rw [e, (divmod_of hq hg).2]

/-- **The exact check**: whatever the estimate `k`, `jump_landing` returns `(-first) mod q`. -/
theorem cLanding_eq {first q k : ℕ} (hq : 0 < q) : cLanding first q k = (q - first % q) % q := by
  unfold cLanding
  set kq1 := if k * q < first then k * q + q * ((first - k * q + q - 1) / q) else k * q
  have hm : ∃ m, kq1 = q * m := by
    simp only [kq1]; split_ifs
    · exact ⟨k + (first - k * q + q - 1) / q, by ring⟩
    · exact ⟨k, by ring⟩
  have hge : first ≤ kq1 := by
    simp only [kq1]; split_ifs with h
    · have e := Nat.div_add_mod (first - k * q + q - 1) q
      have := Nat.mod_lt (first - k * q + q - 1) hq
      omega
    · omega
  obtain ⟨m, hmq⟩ := hm
  have e := Nat.div_add_mod (kq1 - first) q
  have : kq1 - q * ((kq1 - first) / q) - first = (kq1 - first) % q := by omega
  rw [this, hmq, sub_mod_of_mul hq (hmq ▸ hge)]

/-- The estimate `x = X0 - S j` does not underflow and `k = x / 2^64 + 1` keeps every `kq`
of the loops below `2^128`, if `60 j ≤ Q`, `first ≥ Q` and `30 first < 2^128`. -/
theorem estimate_safe {first Q j : ℕ} (hQ : 0 < Q) (hfQ : Q ≤ first) (hj : 60 * j ≤ Q)
    (h30 : 30 * first < 2 ^ 128) (hQ64 : Q < 2 ^ 64) :
    fixS first Q (2 ^ 64) * j ≤ fixX0 first Q (2 ^ 64) ∧
      ((fixX0 first Q (2 ^ 64) - fixS first Q (2 ^ 64) * j) / 2 ^ 64 + 1) * (Q + 30 * j)
        + (Q + 30 * j) ≤ 2 * first + 2 * (Q + 30 * j) ∧ 2 * first + 2 * (Q + 30 * j) < 2 ^ 128 := by
  set M : ℕ := 2 ^ 64
  have hM : 0 < M := by positivity
  obtain ⟨hS1, -⟩ := fixS_bounds (first := first) (M := M) hQ
  rw [fixX0_eq hQ]
  set S := fixS first Q M
  have hX2 := Nat.div_add_mod (first * M) Q
  have hXr := Nat.mod_lt (first * M) hQ
  set X := first * M / Q
  -- S j Q^2 ≤ 30 j first M ≤ (Q/2) first M, and X Q > first M - Q
  have h1 : S * j * (Q * Q) ≤ 30 * first * M * j := by
    have := Nat.mul_le_mul_right j hS1; nlinarith
  have h2 : 30 * first * M * j * 2 ≤ first * M * Q := by
    have := Nat.mul_le_mul_left (first * M) hj; nlinarith
  have hSX : S * j ≤ X := by
    -- S j Q^2 * 2 ≤ first M Q < (X + 1) Q * Q, and first M ≥ Q M ≥ 2 Q
    have h3 : first * M < (X + 1) * Q := by nlinarith
    have h4 : S * j * (Q * Q) * 2 ≤ first * M * Q := by nlinarith
    have h5 : 2 * Q ≤ first * M := by nlinarith
    by_contra hc
    have h6 : (X + 1) * (Q * Q) ≤ S * j * (Q * Q) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  refine ⟨hSX, ?_, by omega⟩
  -- k = (X - S j)/M + 1 ≤ X / M + 1 ≤ first / Q + 1
  have hk1 : (X - S * j) / M ≤ first / Q := by
    calc (X - S * j) / M ≤ X / M := Nat.div_le_div_right (Nat.sub_le _ _)
      _ = first / Q := by
        rw [Nat.div_div_eq_div_mul, Nat.mul_comm Q M, ← Nat.div_div_eq_div_mul,
          Nat.mul_div_cancel _ hM]
  have hq1 : (first / Q + 1) * (Q + 30 * j) ≤ 2 * first + (Q + 30 * j) := by
    have r : (first / Q + 1) * (Q + 30 * j) = first / Q * Q + first / Q * (30 * j) + (Q + 30 * j) := by
      ring
    have m1 : first / Q * Q ≤ first := Nat.div_mul_le_self first Q
    have m2 : first / Q * (60 * j) ≤ first / Q * Q := Nat.mul_le_mul_left _ hj
    have r2 : first / Q * (60 * j) = 2 * (first / Q * (30 * j)) := by ring
    omega
  have := Nat.mul_le_mul_right (Q + 30 * j) (Nat.succ_le_succ hk1)
  rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one] at this
  omega


/-! ## 20. The whole block, end to end: every landing `j < J` is found (engines v7.0 – v7.2)

Combines 16 (bridge), 17 (u128 setup exact), 18 (`double` threshold), 19 (exact check) with
15 (enumeration). Preconditions, all explicit: `8 ≤ Q`, `Q + 30 J < 2^64`, `Q ≤ first`,
`first < 2^62 Q` (the caller's `jump_from`), `60 J ≤ Q`, `1 ≤ span ≤ 2^48`, and
**`30 first < 2^128`**, i.e. `first < 2^128 / 30 ≈ 1.134·10^37`. -/

/-- A search result is below the modulus: `x mod m` is a solution too, so the least one is
`< m` (this is why the C casts of the results to `uint64_t` lose nothing). -/
theorem firstIn_lt {a m l r x : ℕ} (hlr : l ≤ r) (hrm : r < m)
    (h : firstIn a m l r = some x) : x < m := by
  have hs := firstIn_spec m a l r hlr hrm
  rw [h] at hs
  obtain ⟨⟨h1, h2⟩, hmin⟩ := hs
  by_contra hc
  apply hmin (x % m) (lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (Nat.le_of_not_lt hc))
  unfold okIn
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  exact ⟨h1, h2⟩

/-- The `double` evaluation of `t_d` (section 18) for a block with `slack = 2 J + 8` and
`d_max = 30 (J - 1)`. -/
def TdTrace (span Q first J : ℕ) (t : ℝ) : Prop :=
  ∃ spanD QD firstD dD slackD p1 p2 q1 q2 e1 eU c e2 s1 s2 a1 b1 a2 : ℝ,
    Rnd (1 / 2 ^ 53) span spanD ∧ Rnd (1 / 2 ^ 53) Q QD ∧ Rnd (1 / 2 ^ 53) first firstD ∧
    Rnd (1 / 2 ^ 53) ((30 * (J - 1) : ℕ) : ℝ) dD ∧ Rnd (1 / 2 ^ 53) ((2 * J + 8 : ℕ) : ℝ) slackD ∧
    Rnd (1 / 2 ^ 53) (firstD * dD) p1 ∧ Rnd (1 / 2 ^ 53) (p1 * dD) p2 ∧
    Rnd (1 / 2 ^ 53) (QD * QD) q1 ∧ Rnd (1 / 2 ^ 53) (q1 * QD) q2 ∧
    Rnd (1 / 2 ^ 53) (p2 / q2) e1 ∧ Rnd (1 / 2 ^ 53) (e1 * 2 ^ 64) eU ∧
    Rnd (1 / 2 ^ 53) 1.001 c ∧ Rnd (1 / 2 ^ 53) (eU * c) e2 ∧
    Rnd (1 / 2 ^ 53) (spanD / QD) s1 ∧ Rnd (1 / 2 ^ 53) (s1 * 2 ^ 64) s2 ∧
    Rnd (1 / 2 ^ 53) (s2 + e2) a1 ∧ Rnd (1 / 2 ^ 53) (2 * slackD) b1 ∧
    Rnd (1 / 2 ^ 53) (a1 + b1) a2 ∧ Rnd (1 / 2 ^ 53) (a2 + 1) t

/-- From the `double` trace: `T = (uint64_t) t_d` is large enough for the bridge, and
`1 ≤ T ≤ 2^64` when `t_d < 1.8·10^19` (the C fallback test). -/
theorem threshold_ok {span Q first J T : ℕ} {t : ℝ} (hspan : 1 ≤ span) (hspan48 : span ≤ 2 ^ 48)
    (hQ : 1 ≤ Q) (htr : TdTrace span Q first J t) (ht : t < 1.8e19) (hT : T = ⌊t⌋₊) :
    1 ≤ T ∧ T ≤ 2 ^ 64 ∧
      (((2 * J + 8 : ℕ) : ℚ) + 1 + (first : ℚ) * ((30 * (J - 1) : ℕ) : ℚ) ^ 2 * (2 ^ 64 : ℕ) / Q ^ 3)
        * Q + ((span - 1 : ℕ) : ℚ) * (2 ^ 64 : ℕ) ≤ T * Q := by
  obtain ⟨spanD, QD, firstD, dD, slackD, p1, p2, q1, q2, e1, eU, c, e2, s1, s2, a1, b1, a2,
    r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19⟩ := htr
  have key := t_double_ok (2 ^ 64) (1 / 2 ^ 53) rfl rfl (by exact_mod_cast hspan)
    (by exact_mod_cast hspan48) (by exact_mod_cast hQ) (Nat.cast_nonneg first)
    (Nat.cast_nonneg _) (by push_cast; linarith) r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14
    r15 r16 r17 r18 r19
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hE0 : (0 : ℝ) ≤ (first : ℝ) * ((30 * (J - 1) : ℕ) : ℝ) ^ 2 * 2 ^ 64 / (Q : ℝ) ^ 3 := by
    positivity
  have hsY : (0 : ℝ) ≤ ((span : ℝ) - 1) * 2 ^ 64 / Q := by
    have : (1 : ℝ) ≤ span := by exact_mod_cast hspan
    have : (0 : ℝ) ≤ (span : ℝ) - 1 := by linarith
    positivity
  have hfl : t < (T : ℝ) + 1 := by rw [hT]; exact Nat.lt_floor_add_one t
  have hsl8 : (8 : ℝ) ≤ ((2 * J + 8 : ℕ) : ℝ) := by exact_mod_cast (by omega : 8 ≤ 2 * J + 8)
  have ht0 : 10 ≤ t := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have : (9 : ℝ) < T := by linarith
    exact_mod_cast (show (1 : ℝ) ≤ T by linarith)
  · have : (T : ℝ) ≤ t := by rw [hT]; exact Nat.floor_le (by linarith)
    have : (T : ℝ) < 2 ^ 64 := by
      have : (1.8e19 : ℝ) < 2 ^ 64 := by norm_num
      linarith
    exact_mod_cast this.le
  · have hR : ((((2 * J + 8 : ℕ) : ℝ) + 1 +
        (first : ℝ) * ((30 * (J - 1) : ℕ) : ℝ) ^ 2 * 2 ^ 64 / (Q : ℝ) ^ 3) * Q +
        ((span : ℝ) - 1) * 2 ^ 64 ≤ (T : ℝ) * Q) := by
      have h1 : ((2 * J + 8 : ℕ) : ℝ) + 1 + (first : ℝ) * ((30 * (J - 1) : ℕ) : ℝ) ^ 2 * 2 ^ 64 /
          (Q : ℝ) ^ 3 + ((span : ℝ) - 1) * 2 ^ 64 / Q ≤ T := by linarith
      have e : ((span : ℝ) - 1) * 2 ^ 64 / Q * Q = ((span : ℝ) - 1) * 2 ^ 64 := by field_simp
      have := mul_le_mul_of_nonneg_right h1 hQr.le
      rw [add_mul, e] at this
      exact this
    have hsub : ((span - 1 : ℕ) : ℝ) = (span : ℝ) - 1 := by
      rw [Nat.cast_sub hspan]; simp
    rw [← hsub] at hR
    have hRq : (((((2 * J + 8 : ℕ) : ℚ) + 1 + (first : ℚ) * ((30 * (J - 1) : ℕ) : ℚ) ^ 2 *
        (2 ^ 64 : ℕ) / Q ^ 3) * Q + ((span - 1 : ℕ) : ℚ) * (2 ^ 64 : ℕ) : ℚ) : ℝ) ≤
        (((T : ℚ) * Q : ℚ) : ℝ) := by
      push_cast; push_cast at hR; linarith
    exact_mod_cast hRq

/-- **Engine v7.2 (`jump_block_quick`), end to end.** For a block `q = Q + 30 j`, `j < J`, with
the u128 setup of the C code (`cX0`, `cS`), `T = (uint64_t) t_d` from the `double` trace,
`j0` from `jump_first_range64` and `ga, gc` from `jump_gaps`: every `j < J` whose multiple
lands in `[first, first + span)` is visited by the C loop (before it breaks), and the exact
check there returns the true offset. -/
theorem jump_block_quick_exact {first span Q J T j0 ga gc : ℕ} {t : ℝ}
    (hQ8 : 8 ≤ Q) (hQ64 : Q + 30 * J < 2 ^ 64) (hfQ : Q ≤ first) (hK : first < 2 ^ 62 * Q)
    (h30 : 30 * first < 2 ^ 128) (hJQ : 60 * J ≤ Q) (hspan : 1 ≤ span)
    (hspan48 : span ≤ 2 ^ 48)
    (htr : TdTrace span Q first J t) (ht : t < 1.8e19) (hT : T = ⌊t⌋₊)
    (h0 : firstRange64 (2 ^ 64) (cS first Q % 2 ^ 64)
      ((2 * J + 8 + 2 ^ 64 - cX0 first Q % 2 ^ 64) % 2 ^ 64) 0 (T - 1) = some j0)
    (hg : jumpGaps (2 ^ 64) (cS first Q % 2 ^ 64) T = some (ga, gc)) :
    ∀ j < J, (Q + 30 * j - first % (Q + 30 * j)) % (Q + 30 * j) < span →
      (∃ k, (cSeq (2 ^ 64) T ga gc (cS first Q % 2 ^ 64 * ga % 2 ^ 64)
            (2 ^ 64 - cS first Q % 2 ^ 64 * gc % 2 ^ 64) j0
            (((2 * J + 8 + 2 ^ 64 - cX0 first Q % 2 ^ 64) % 2 ^ 64 + cS first Q % 2 ^ 64 * j0)
              % 2 ^ 64) k).1 = j ∧
        ∀ i ≤ k, (cSeq (2 ^ 64) T ga gc (cS first Q % 2 ^ 64 * ga % 2 ^ 64)
            (2 ^ 64 - cS first Q % 2 ^ 64 * gc % 2 ^ 64) j0
            (((2 * J + 8 + 2 ^ 64 - cX0 first Q % 2 ^ 64) % 2 ^ 64 + cS first Q % 2 ^ 64 * j0)
              % 2 ^ 64) i).1 < J) ∧
      (cS first Q * j ≤ cX0 first Q ∧
        ((cX0 first Q - cS first Q * j) / 2 ^ 64 + 1) * (Q + 30 * j) + (Q + 30 * j) < 2 ^ 128) ∧
      ∀ k, cLanding first (Q + 30 * j) k = (Q + 30 * j - first % (Q + 30 * j)) % (Q + 30 * j) := by
  intro j hj hland
  have hQ : 0 < Q := by omega
  obtain ⟨hT1, hTM, hTq⟩ := threshold_ok hspan hspan48 (by omega) htr ht hT
  have hX := cX0_eq hQ (by omega) hK
  have hS := cS_eq hQ8 (by omega) hK h30
  obtain ⟨e1, e2, e3⟩ := estimate_safe hQ hfQ (by omega : 60 * j ≤ Q) h30 (by omega)
  refine ⟨?_, ⟨by rw [hX, hS]; exact e1, by rw [hX, hS]; omega⟩, fun k => cLanding_eq (by omega)⟩
  apply jump_block_quick_complete (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
    hT1 hTM h0 hg j hj
  rw [hX, hS]
  apply landing_candidate_fixed (E := (first : ℚ) * ((30 * (J - 1) : ℕ) : ℚ) ^ 2 * (2 ^ 64 : ℕ) / Q ^ 3)
    hQ (by positivity) (by omega) hTM _ hTq hland
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hjJ : ((30 * j : ℕ) : ℚ) ≤ ((30 * (J - 1) : ℕ) : ℚ) := by exact_mod_cast (by omega)
  have hsq : ((30 * j : ℕ) : ℚ) ^ 2 ≤ ((30 * (J - 1) : ℕ) : ℚ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hjJ 2
  rw [div_mul_cancel₀ _ (by positivity)]
  have e : (first : ℚ) * (30 * j) ^ 2 * ((2 ^ 64 : ℕ) : ℚ) =
      (first : ℚ) * ((30 * j : ℕ) : ℚ) ^ 2 * ((2 ^ 64 : ℕ) : ℚ) := by push_cast; ring
  rw [e]
  gcongr

/-- **Engines v7.0 / v7.1 (`jump_block`), end to end**: the same with `j0`, `ga`, `gc` from
the three u128 `jump_first_range` searches (`ga += 1`, `gc += 1`). -/
theorem jump_block_exact {first span Q J T j0 xa xc : ℕ} {t : ℝ}
    (hQ8 : 8 ≤ Q) (hQ64 : Q + 30 * J < 2 ^ 64) (hfQ : Q ≤ first) (hK : first < 2 ^ 62 * Q)
    (h30 : 30 * first < 2 ^ 128) (hJQ : 60 * J ≤ Q) (hspan : 1 ≤ span)
    (hspan48 : span ≤ 2 ^ 48)
    (htr : TdTrace span Q first J t) (ht : t < 1.8e19) (hT : T = ⌊t⌋₊)
    (h0 : firstRange (cS first Q % 2 ^ 64)
      ((2 * J + 8 + 2 ^ 64 - cX0 first Q % 2 ^ 64) % 2 ^ 64) (2 ^ 64) 0 (T - 1) = some j0)
    (ha : firstRange (cS first Q % 2 ^ 64) (cS first Q % 2 ^ 64) (2 ^ 64) 0 (T - 1) = some xa)
    (hc : firstRange (cS first Q % 2 ^ 64) (cS first Q % 2 ^ 64) (2 ^ 64) (2 ^ 64 - T + 1)
      (2 ^ 64 - 1) = some xc) :
    ∀ j < J, (Q + 30 * j - first % (Q + 30 * j)) % (Q + 30 * j) < span →
      (∃ k, (cSeq (2 ^ 64) T (xa + 1) (xc + 1) (cS first Q % 2 ^ 64 * (xa + 1) % 2 ^ 64)
            (2 ^ 64 - cS first Q % 2 ^ 64 * (xc + 1) % 2 ^ 64) j0
            (((2 * J + 8 + 2 ^ 64 - cX0 first Q % 2 ^ 64) % 2 ^ 64 + cS first Q % 2 ^ 64 * j0)
              % 2 ^ 64) k).1 = j ∧
        ∀ i ≤ k, (cSeq (2 ^ 64) T (xa + 1) (xc + 1) (cS first Q % 2 ^ 64 * (xa + 1) % 2 ^ 64)
            (2 ^ 64 - cS first Q % 2 ^ 64 * (xc + 1) % 2 ^ 64) j0
            (((2 * J + 8 + 2 ^ 64 - cX0 first Q % 2 ^ 64) % 2 ^ 64 + cS first Q % 2 ^ 64 * j0)
              % 2 ^ 64) i).1 < J) ∧
      (cS first Q * j ≤ cX0 first Q ∧
        ((cX0 first Q - cS first Q * j) / 2 ^ 64 + 1) * (Q + 30 * j) + (Q + 30 * j) < 2 ^ 128) ∧
      ∀ k, cLanding first (Q + 30 * j) k = (Q + 30 * j - first % (Q + 30 * j)) % (Q + 30 * j) := by
  intro j hj hland
  have hQ : 0 < Q := by omega
  obtain ⟨hT1, hTM, hTq⟩ := threshold_ok hspan hspan48 (by omega) htr ht hT
  have hT2 : 2 ≤ T := by
    obtain ⟨spanD, QD, firstD, dD, slackD, p1, p2, q1, q2, e1, eU, c, e2, s1, s2, a1, b1, a2,
      r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19⟩ := htr
    have key := t_double_ok (2 ^ 64) (1 / 2 ^ 53) rfl rfl (by exact_mod_cast hspan)
      (by exact_mod_cast hspan48) (by exact_mod_cast (by omega : 1 ≤ Q)) (Nat.cast_nonneg first)
      (Nat.cast_nonneg _) (by push_cast; linarith) r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13
      r14 r15 r16 r17 r18 r19
    have hE0 : (0 : ℝ) ≤ (first : ℝ) * ((30 * (J - 1) : ℕ) : ℝ) ^ 2 * 2 ^ 64 / (Q : ℝ) ^ 3 := by
      positivity
    have hsY : (0 : ℝ) ≤ ((span : ℝ) - 1) * 2 ^ 64 / Q := by
      have : (1 : ℝ) ≤ span := by exact_mod_cast hspan
      have : (0 : ℝ) ≤ (span : ℝ) - 1 := by linarith
      positivity
    have hsl8 : (8 : ℝ) ≤ ((2 * J + 8 : ℕ) : ℝ) := by exact_mod_cast (by omega : 8 ≤ 2 * J + 8)
    have hfl : t < (T : ℝ) + 1 := by rw [hT]; exact Nat.lt_floor_add_one t
    have : (2 : ℝ) ≤ T := by linarith
    exact_mod_cast this
  have hX := cX0_eq hQ (by omega) hK
  have hS := cS_eq hQ8 (by omega) hK h30
  obtain ⟨e1, e2, e3⟩ := estimate_safe hQ hfQ (by omega : 60 * j ≤ Q) h30 (by omega)
  refine ⟨?_, ⟨by rw [hX, hS]; exact e1, by rw [hX, hS]; omega⟩, fun k => cLanding_eq (by omega)⟩
  apply jump_block_complete (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
    hT2 hTM h0 ha hc j hj
  rw [hX, hS]
  apply landing_candidate_fixed (E := (first : ℚ) * ((30 * (J - 1) : ℕ) : ℚ) ^ 2 * (2 ^ 64 : ℕ) / Q ^ 3)
    hQ (by positivity) (by omega) hTM _ hTq hland
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hjJ : ((30 * j : ℕ) : ℚ) ≤ ((30 * (J - 1) : ℕ) : ℚ) := by exact_mod_cast (by omega)
  have hsq : ((30 * j : ℕ) : ℚ) ^ 2 ≤ ((30 * (J - 1) : ℕ) : ℚ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hjJ 2
  rw [div_mul_cancel₀ _ (by positivity)]
  have e : (first : ℚ) * (30 * j) ^ 2 * ((2 ^ 64 : ℕ) : ℚ) =
      (first : ℚ) * ((30 * j : ℕ) : ℚ) ^ 2 * ((2 ^ 64 : ℕ) : ℚ) := by push_cast; ring
  rw [e]
  gcongr


/-! ## 21. A certificate for `(ga, gc)`: reusing the previous block's steps without the walk

Any pair `(ga, gc)` passing these checks *is* the pair of smallest three-gap steps for the
block's `(B, T)`, however it was obtained (e.g. kept from the previous block):
`da = B ga mod 2^64`, `dc = 2^64 - (B gc mod 2^64)`, `1 ≤ da < T`, `dc < T`, `T ≤ da + dc`,
`ga dc + gc da = 2^64`. In C: two u64 multiplies, two u128 multiply-adds and compares. -/

theorem gaps_certificate {M B T ga gc : ℕ} (hga : 1 ≤ ga) (hgc : 1 ≤ gc)
    (hda1 : 1 ≤ B * ga % M) (hdaT : B * ga % M < T)
    (hdcT : M - B * gc % M < T)
    (hsum : T ≤ B * ga % M + (M - B * gc % M))
    (hdet : ga * (M - B * gc % M) + gc * (B * ga % M) = M) :
    GearRot M T ga gc (fun g => B * g % M) := by
  have hM : 0 < M := by
    have : 1 * 1 ≤ gc * (B * ga % M) := Nat.mul_le_mul hgc hda1
    omega
  have hlt := Nat.mod_lt (B * gc) hM
  have ea := Nat.div_add_mod (B * ga) M
  have ec := Nat.div_add_mod (B * gc) M
  refine GapInv.gearRot (da := B * ga % M) (dc := M - B * gc % M) ⟨hga, hgc, hda1, by omega,
    ⟨((B * ga / M : ℕ) : ℤ), ?_⟩, ⟨((B * gc / M : ℕ) : ℤ) + 1, ?_⟩, hdet, hsum⟩ hdaT hdcT
  · have : ((B * ga : ℕ) : ℤ) = ((M * (B * ga / M) + B * ga % M : ℕ) : ℤ) := by rw [ea]
    push_cast at this ⊢; linarith
  · have : ((B * gc : ℕ) : ℤ) = ((M * (B * gc / M) + B * gc % M : ℕ) : ℤ) := by rw [ec]
    push_cast [Nat.cast_sub hlt.le] at this ⊢; linarith

end JumpGear
