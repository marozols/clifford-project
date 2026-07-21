import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import CliffordProject.Tools.MatrixAlgebra

variable (d : ℕ) [hnezero : NeZero d]


lemma d_invertible : IsUnit (d : ℂ) := by
  simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero]
  exact NeZero.ne d

noncomputable
def ω : ℂˣ := .mk
  (Complex.exp (2 * Real.pi * Complex.I / d))
  (Complex.exp (- 2 * Real.pi * Complex.I / d))
  (by rw[<- Complex.exp_add]; simp; ring; rw[Complex.exp_zero])
  (by rw[<- Complex.exp_add]; simp; ring; rw[Complex.exp_zero])


@[simp]
lemma omega_one : (ω 1) = 1 := by
  ext; unfold ω; simp;

omit [NeZero d] in
@[simp]
lemma omega_one' (hd : d = 1) : ω d = 1 := by
  rw[hd]; simp


@[simp]
lemma omega_pow_d_eq_one : (ω d)^d = 1 := by
  unfold ω; ext; simp
  rw [← Complex.exp_nat_mul]
  rw [IsUnit.mul_div_cancel]
  · exact Complex.exp_two_pi_mul_I
  · exact d_invertible d

@[simp]
lemma omega_val_pow_d_eq_one : ((ω d).val) ^ d = 1 := by
  rw[<- Units.val_pow_eq_pow_val, omega_pow_d_eq_one]; simp

omit [NeZero d] in
@[simp]
lemma omega_star : star ((ω d).val) = (ω d).val⁻¹
 := by rw[Complex.inv_def]; simp; unfold ω; simp;
        rw[<- Complex.sq_norm, Complex.norm_exp]; simp

omit [NeZero d] in
@[simp]
lemma omega_pow_star (i : ℕ) : star (((ω d).val) ^ i) = ((ω d).val ^ i)⁻¹
  := by simp;

lemma order_omega : orderOf (ω d) = d := by
  rw[orderOf_eq_iff]; apply And.intro; apply omega_pow_d_eq_one;
  intro m hm hm'; intro hAbs; rw[Units.ext_iff] at hAbs; simp at hAbs;
  unfold ω at hAbs; simp at hAbs; rw[<- Complex.exp_nsmul] at hAbs; simp at hAbs;
  rw[Complex.exp_eq_one_iff] at hAbs; obtain ⟨n, hn⟩ := hAbs;

  have calc_md : (m : ℝ) / (d : ℝ) = (n : ℂ) := by rw[mul_div_left_comm, mul_comm] at hn; simp at hn; apply hn
  have d_ge_zero : 0 < d := by apply Nat.zero_lt_of_ne_zero; apply hnezero.out;
  have ratio_between : (m : ℝ) / (d : ℝ) > 0 ∧ (m : ℝ) / d < 1 := by sorry; -- apply And.intro;
  simp at calc_md;
  --rw[calc_md] at ratio_between;
  sorry;
  apply Nat.zero_lt_of_ne_zero; apply hnezero.out
  -- apply d_ge_zero; rw[div_lt_one m d]

lemma omega_pow_n_mod_d :
  ∀ n : Nat, (ω d) ^ n = (ω d) ^ (n % d) := by
    intro n
    nth_rw 1 [←(Nat.mod_add_div n d)]
    rw [pow_add, pow_mul, omega_pow_d_eq_one,
      one_pow, mul_one]

lemma omega_val_pow_n_mod_d :
  ∀ n : Nat, (ω d).val ^ n = (ω d).val ^ (n % d) := by
    intro n
    nth_rw 1 [←(Nat.mod_add_div n d)]
    rw [pow_add, pow_mul, omega_val_pow_d_eq_one,
      one_pow, mul_one]

lemma omega_pow_k_mod_d_eq_pow_k_int :
  ∀ k : ℤ, (ω d) ^ k = (ω d) ^ (k % d) := by
    intro k; --unfold ω; ext; simp
    nth_rw 1 [← (Int.emod_add_ediv_mul k d)]
    rw[zpow_add]; simp
    rw[mul_comm, zpow_mul]
    simp

lemma omega_pow_k_mod_d_eq_pow_k_zmod :
  ∀ k : Int, (ω d) ^ k = (ω d) ^ (k : ZMod d).val := by
    intro k
    rw [omega_pow_k_mod_d_eq_pow_k_int]
    rw [(Eq.symm (ZMod.val_intCast k))]
    exact zpow_natCast (ω d) (k : ZMod d).val

noncomputable
def τ : ℂˣ := .mk
  (- Complex.exp (Real.pi * Complex.I / d))
  (- Complex.exp (- Real.pi * Complex.I / d))
  (by simp; rw[<- Complex.exp_add]; ring; rw[Complex.exp_zero])
  (by simp; rw[<- Complex.exp_add]; ring; rw[Complex.exp_zero])

@[simp]
lemma tau_sq_eq_omega (d : ℕ) [NeZero d] : (τ d)^2 = ω d := by
  unfold τ ω; ext; simp; rw[<- Complex.exp_nsmul]; simp; rw[mul_assoc, <- mul_div_assoc];

@[simp]
lemma tau_pow_d_eq_one_of_odd (hodd : Odd d) :
    (τ d)^d = 1 := by
    unfold τ; ext; simp; rw [← neg_one_mul, mul_pow, neg_one_pow_odd d hodd]
    rw[<- Complex.exp_nsmul]; simp;
    rw[mul_comm]; simp
    where
    neg_one_pow_odd : ∀ x : ℕ, Odd x → (((-1) : ℂ)) ^ x = (-1) :=
      by intro x hoddx; rw[neg_one_pow_eq_neg_one_iff_odd]; apply hoddx; norm_num


lemma tau_pow_d2_one : (τ d) ^ (d ^ 2) = 1 := by
  unfold τ; ext; simp
  rw [← neg_one_mul]
  rw [pow_two]
  rw [mul_pow];
  rw [← Complex.exp_nat_mul]
  rw [Nat.cast_mul]
  rw [mul_assoc]
  rw [IsUnit.mul_div_cancel]
  rw [Complex.exp_nat_mul]
  rw [Complex.exp_pi_mul_I]
  rw [← pow_add]
  rw [← mul_add_one]
  rw [neg_one_pow_eq_one_iff_even]
  exact Nat.even_mul_succ_self d
  · norm_num
  · exact d_invertible d


lemma mod_d_nonneg (a : ℤ) : 0 ≤ a % ↑d := by
    apply Int.emod_nonneg
    exact Nat.cast_ne_zero.mpr (NeZero.ne d)

theorem tau_pow_n_mod_d_of_d_odd
    (n d : ℕ) (hodd : Odd d) [NeZero d] :
    τ d ^ n = τ d ^ (n % ↑d) :=
  pow_eq_pow_mod n (tau_pow_d_eq_one_of_odd d hodd)

theorem tau_star
    (d : ℕ) (n : ℤ) [NeZero d] :
    star (τ d ^ n)  = (τ d)^(-n) := by
  unfold τ; ext; simp; rw[← Complex.exp_conj]; simp;
  rw [← neg_one_mul, mul_zpow]; nth_rw 3 [← neg_one_mul]; rw[mul_zpow]; simp;
  rw [<- Complex.exp_int_mul, <- Complex.exp_int_mul, <- Complex.exp_neg];
  rw [mul_comm, ← neg_one_mul]; nth_rw 3 [← neg_one_mul]; sorry -- rw[Units.inv_pow_eq_pow_inv (-1) n]
