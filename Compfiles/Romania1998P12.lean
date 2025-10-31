/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Algebra] }

/-!
# Romanian Mathematical Olympiad 1998, Problem 12

Find all functions u : ℝ → ℝ for which there exists a strictly monotonic
function f : ℝ → ℝ such that

  ∀ x,y ∈ ℝ, f(x + y) = f(x)u(y) + f(y)
-/

namespace Romania1998P12

snip begin

/-
# Solution

f(x) = eᵏˣ for some k : ℝ.
-/

lemma extend_function_mono
   (u : ℝ → ℝ)
   (f : ℝ → ℝ)
   (u_mono : Monotone u)
   (f_cont : Continuous f)
   (h : ∀ x : ℚ, u x = f x) :
   ∀ x : ℝ, u x = f x := by
  -- suppose not.
  by_contra! hn

  -- then there is y such that u y ≠ f y
  obtain ⟨y, hy⟩ := hn
  let ε : ℝ := |u y - f y|
  have hε : 0 < ε := abs_sub_pos.mpr hy

  -- then find a δ such that for all z, |z-y| < δ implies that
  -- |f z - f y| < ε.
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuous_iff.mp f_cont y ε hε

  obtain h1 | h2 | h3 := lt_trichotomy (u y) (f y)
  · -- pick a rational point less than y that's in the ball s,
    have : ∃ z : ℚ, (z:ℝ) < y ∧ dist (z:ℝ) y < δ := by
      have hyδ : y - δ < y := sub_lt_self y hδ0
      obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn hyδ
      refine ⟨z, hz2, ?_⟩
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr hz2)]
      exact sub_lt_comm.mp hz1

    obtain ⟨z, h_z_lt_y, hyz⟩ := this
    -- then dist (f z) (f y) < ε.
    have hbzb := hδ z hyz
    rw [←h z] at hbzb
    have huzuy : u y < u z := by
      have hufp : u y - f y < 0 := by linarith
      have hua : ε = -(u y - f y) := abs_of_neg hufp
      rw [hua, Real.dist_eq] at hbzb
      obtain h5 | h6 := em (f y < u z)
      · linarith
      · have : u z - f y ≤ 0 := by linarith
        rw[abs_eq_neg_self.mpr this] at hbzb
        linarith
    -- so u(z) < u(y), contradicting u_mono.
    have h_y_le_z := le_of_lt  h_z_lt_y
    have := u_mono h_y_le_z
    linarith
  · exact hy h2

  · -- pick a rational point z greater than y that's in the ball s,
    have : ∃ z : ℚ, y < z ∧ dist (z:ℝ) y < δ := by
      have hyδ : y < y + δ := lt_add_of_pos_right y hδ0
      obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn hyδ
      refine ⟨z, hz1, ?_⟩
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hz1)]
      exact sub_left_lt_of_lt_add hz2
    obtain ⟨z, h_y_lt_z, hyz⟩ := this
    -- then dist (f z) (f y) < ε.
    have hbzb := hδ z hyz
    rw [←h z] at hbzb
    have huzuy : u z < u y := by
      have hufp : 0 < u y - f y := by linarith
      have hua : ε = u y - f y := abs_of_pos hufp
      rw [hua, Real.dist_eq] at hbzb
      cases em (f y < u z)
      · have : 0 ≤ u z - f y := by linarith
        rw[abs_eq_self.mpr this] at hbzb
        linarith
      · linarith
    -- so u(z) < u(y), contradicting u_mono.
    have h_y_le_z := le_of_lt h_y_lt_z
    have := u_mono h_y_le_z
    linarith

lemma extend_function_anti
   (u : ℝ → ℝ)
   (f : ℝ → ℝ)
   (u_anti : Antitone u)
   (f_cont : Continuous f)
   (h : ∀ x : ℚ, u x = f x) :
   ∀ x : ℝ, u x = f x := by
  -- suppose not.
  by_contra! hn

  -- then there is y such that u y ≠ f y
  obtain ⟨y, hy⟩ := hn
  let ε : ℝ := |u y - f y|
  have hε : 0 < ε := abs_sub_pos.mpr hy

  -- then find a δ such that for all z, |z-y| < δ implies that
  -- |f z - f y| < ε.
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuous_iff.mp f_cont y ε hε

  obtain h1 | h2 | h3 := lt_trichotomy (u y) (f y)
  · -- pick a rational point z greater than y that's in the ball s,
    have : ∃ z : ℚ, y < z ∧ dist (z:ℝ) y < δ := by
      have hyδ : y < y + δ := lt_add_of_pos_right y hδ0
      obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn hyδ
      refine ⟨z, hz1, ?_⟩
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hz1)]
      exact sub_left_lt_of_lt_add hz2

    obtain ⟨z, h_y_lt_z, hyz⟩ := this
    -- then dist (f z) (f y) < ε.
    have hbzb := hδ z hyz
    rw [← h z] at hbzb
    have huzuy : u y < u z := by
      have hufp : u y - f y < 0 := by linarith
      have hua : ε = -(u y - f y) := abs_of_neg hufp
      rw [hua, Real.dist_eq] at hbzb
      cases em (f y < u z)
      · linarith
      · have : u z - f y ≤ 0 := by linarith
        rw[abs_eq_neg_self.mpr this] at hbzb
        linarith
    have h_y_le_z := le_of_lt h_y_lt_z
    have := u_anti h_y_le_z
    linarith
  · exact hy h2
  · -- pick a rational point less than y that's in the ball s,
    have : ∃ z : ℚ, (z:ℝ) < y ∧ dist (z:ℝ) y < δ := by
      have hyδ : y - δ < y := sub_lt_self y hδ0
      obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn hyδ
      refine ⟨z, hz2, ?_⟩
      rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr hz2)]
      exact sub_lt_comm.mp hz1

    obtain ⟨z, h_z_lt_y, hyz⟩ := this
    -- then dist (f z) (f y) < ε.
    have hzb : (↑z) ∈ Metric.ball y δ := Metric.mem_ball.mpr hyz
    have hbzb := hδ z hzb
    rw[← h z] at hbzb
    have huzuy : u z < u y := by
      have hufp : 0 < u y - f y := by linarith
      have hua : ε = u y - f y := abs_of_pos hufp
      rw [hua, Real.dist_eq] at hbzb
      obtain h5 | h6 := em (f y < u z)
      · have : 0 ≤ u z - f y := by linarith
        rw[abs_eq_self.mpr this] at hbzb
        linarith
      · linarith only [h3, h6]
    have h_z_le_y := le_of_lt h_z_lt_y
    have := u_anti h_z_le_y
    linarith
  -- in either case, we end up contradicting u_anti.

lemma int_dichotomy (z : ℤ) : ∃ n : ℕ, (n:ℤ) = z ∨ -(n:ℤ) = z := by
  cases z with
  | ofNat z => use z; left; simp only [Int.ofNat_eq_coe]
  | negSucc z =>  use z + 1; right; rfl

lemma exp_characterization
    (u : ℝ → ℝ)
    (hu : ∀ x y : ℝ, u (x + y) = u x * u y)
    (hu0 : u 0 = 1)
    (hm : StrictMono u ∨ StrictAnti u) :
    (∃ k : ℝ, ∀ x : ℝ, u x = Real.exp (k * x)) := by
  -- We have u(nx) = u(x)ⁿ for all n ∈ ℤ, x ∈ ℝ.
  have h1 : ∀ n : ℕ, ∀ x : ℝ, u (n * x) = (u x) ^ n := by
    intro n
    induction' n with pn hpn
    · intro x
      simp only [CharP.cast_eq_zero, zero_mul]
      exact hu0
    · intro x
      have hp1: ↑(pn.succ) * x = ↑pn * x + x := by
        have : ↑pn * x + x = (↑pn + 1) * x := by ring
        rw[this, Nat.cast_succ]
      rw[hp1, hu (↑pn * x) x, hpn x, mul_comm]
      exact (pow_succ' (u x) pn).symm

  have h2 : ∀ x, (u x) * u (-x) = 1 := by
    intro x
    have := hu x (-x)
    rw [add_neg_cancel] at this
    rw [←this]
    exact hu0

  have hunz : ∀ x, 0 < u x := fun x ↦ by
    by_contra! H
    obtain hlt | heq | hgt := lt_trichotomy x 0
    · have h10 := h2 x
      have hx0 : 0 < -x := neg_pos.mpr hlt
      obtain hm | hm := hm <;> nlinarith[hm hx0, hm hlt]
    · rw [heq, hu0] at H; linarith
    · have h10 := h2 x
      have hx0 : -x < 0 := neg_lt_zero.mpr hgt
      obtain hm | hm := hm <;> nlinarith [hm hx0, hm hgt]

  have h3 : ∀ x, u (-x) = 1 / (u x) :=
    fun x ↦ eq_one_div_of_mul_eq_one_right (h2 x)

  have h4 : ∀ z : ℤ, ∀ x : ℝ, u (z * x) = (u x) ^ z := by
    intro z x
    obtain ⟨n, hn⟩ := int_dichotomy z
    rcases hn with rfl | hn
    · have := h1 n x
      norm_cast at this
    · have h10 := h1 n x
      rw [←hn]
      have h11: ↑(-((↑n):ℤ)) * x = - (n * x) := by norm_num
      rw [h11, h3 _]
      rw [h10, one_div]
      simp

  -- Let eᵏ = u(1);
  obtain ⟨k, hk⟩ : ∃ k, Real.exp k = u 1 := by
    use Real.log (u 1); exact Real.exp_log (hunz 1)

  -- then u(n) = eᵏⁿ for all n ∈ ℕ
  have hnexp : ∀ n : ℕ, u n = Real.exp (k * n) := by
    intro n
    have h10 := h4 n 1
    rw [←hk, mul_one] at h10
    norm_cast at h10
    rw [h10, mul_comm]
    exact (Real.exp_nat_mul _ _).symm

  -- and u(p/q) = (u(p))^(1/q) = e^(k(p/q))
  -- for all p ∈ ℤ, q ∈ ℕ, so u(x) = e^(kx) for all x ∈ ℚ.
  have hzexp : ∀ z : ℤ, u z = Real.exp (k * z) := by
    intro z
    obtain ⟨n, hn⟩ := int_dichotomy z
    rcases hn with rfl | rfl
    · norm_cast
      exact hnexp n
    · have := h4 (-↑n) 1
      rw[mul_one] at this
      rw[this, ←hk]
      rw [Real.exp_mul]
      exact (Real.rpow_intCast _ _).symm

  have hp : ∀ p : ℕ, 0 < p → ∀ x : ℝ, u (x / p) = (u x) ^ (1 / (p:ℝ)) := by
    intro p hp x
    cases p with
    | zero => exfalso; exact Nat.lt_asymm hp hp
    | succ p =>
    have h12: ∀ n : ℕ, (u (x / p.succ))^n = u (x * n / p.succ) := by
      intro n
      induction' n with pn hpn
      · simp [hu0.symm]
      · have h10: x * ↑(pn.succ) / ↑(p.succ) = x * ↑pn / ↑(p.succ) + x / ↑(p.succ) := by
          simp [field]
        rw [h10]
        have h11 := hu (x * ↑pn / ↑(p.succ)) (x / ↑(p.succ))
        rw [h11, ← hpn]
        norm_cast
    replace h12 := h12 p.succ
    have h13 : x * ↑(p.succ) / ↑(p.succ) = x := mul_div_cancel_of_invertible _ _
    rw [h13] at h12
    rw [← h12]
    have h14: u (x / ↑(p.succ)) ^ p.succ = u (x / ↑(p.succ)) ^ (p.succ:ℝ) := by norm_cast
    rw [h14]
    have h15 := le_of_lt (hunz (x / ↑(p.succ)))
    rw [←Real.rpow_mul h15 _]
    field_simp
    simp

  have hq : ∀ q : ℚ, u q = Real.exp (k * q) := fun q ↦ by
    rw [Rat.cast_def q, hp q.den q.pos q.num, hzexp q.num, ←Real.exp_mul]
    ring_nf

  use k

  -- Since u in monotonic and the rationals are dense in ℝ, we have u(x) = e^(kx) for all x ∈ ℝ.
  -- Therefore all solutions of the form u(x) = e^(kx), k ∈ ℝ.
  let f := fun x ↦ Real.exp (k * x)
  have hf : ∀ q : ℚ, u q = f q := fun q ↦ hq q
  have hfm : Continuous f := by continuity
  obtain hm | hm := hm
  · have hmu : Monotone u := StrictMono.monotone hm
    exact extend_function_mono u f hmu hfm hf
  · have hau : Antitone u := StrictAnti.antitone hm
    exact extend_function_anti u f hau hfm hf


lemma exp_strict_mono' (k x y : ℝ) (hkp : 0 < k) (h : x < y) :
    Real.exp (k * x) < Real.exp (k * y) :=
  Real.exp_lt_exp.mpr ((mul_lt_mul_iff_right₀ hkp).mpr h)

lemma exp_strict_anti' (k x y : ℝ) (hkp : k < 0) (h : x < y) :
    Real.exp (k * y) < Real.exp (k * x) :=
  Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left h hkp)

lemma romania1998_p12_mp (u : ℝ → ℝ) :
    (∃ f : ℝ → ℝ, (StrictMono f ∨ StrictAnti f)
        ∧ ∀ x y : ℝ, f (x + y) = f x * u y + f y) →
    (∃ k : ℝ, ∀ x : ℝ, u x = Real.exp (k * x)) := by
  intro h
  obtain ⟨f, hm, hf⟩ := h
  -- First, letting y = 0, we obtain f(x) = f(x)u(0) + f(0) for all x ∈ ℝ,
  have hy0 : ∀ x : ℝ, f x = f x * u 0 + f 0 := by
    intro x; have := hf x 0; rw [add_zero] at this; exact this

  -- thus u(0) ≠ 1 would imply f(x) = f(0) / (1 - u(0)) for all x,
  have h0 : (u 0 ≠ 1) → ∀ x : ℝ, f x = f 0 / (1 - u 0) := by
    intro hu0 x
    have hy0x1 :=
                calc f 0 = f x - f x * u 0 := (sub_eq_of_eq_add' (hy0 x)).symm
                _ = f x * (1 - u 0) := by ring
    rw[hy0x1]
    have : 1 - u 0 ≠ 0 := sub_ne_zero.mpr hu0.symm
    field_simp

  -- which implies that f is constant, which we know is not the case
  have h0' : (u 0 ≠ 1) → False := by
    intro hu0
    have hu0' := h0 hu0
    obtain hm | hm := hm <;>
    · have hu00 := hu0' 0
      have hu01 := hu0' 1
      have hm0 := @hm 0 1 (by norm_num)
      linarith

  -- so we must have u(0) = 1
  have h00 : u 0 = 1 := not_not.mp h0'
  clear h0 h0'
  rw [h00] at hy0

  -- and f(0) = 0.
  have hf0 : f 0 = 0 := by have := hy0 0; linarith

  -- Then f(x) ≠ 0 for all x ≠ 0.
  have hfx0 : ∀ x, x ≠ 0 → f x ≠ 0 := by
    intro x hx
    obtain hm1 | hm2 := hm
    · obtain h1 | h2 | h3 := lt_trichotomy x 0
      · rw [←hf0];
        exact ne_of_lt (hm1 h1)
      · exfalso; exact hx h2
      · rw [←hf0]
        exact (ne_of_lt (hm1 h3)).symm
    · obtain h1 | h2 | h3 := lt_trichotomy x 0
      · have := hm2 h1
        rw [hf0] at this
        exact (ne_of_lt this).symm
      · exfalso; exact hx h2
      · have := hm2 h3
        rw [hf0] at this
        exact (ne_of_lt this)

  -- Next, we have
  -- f(x)u(y) + f(y) = f (x + y) = f(x) + f(y)u(x)
  have h1 : ∀ x y : ℝ, f x * u y + f y = f x + f y * u x := by
    intro x y
    rw [←hf, add_comm]
    linarith[hf y x]

  -- so f(x)(u(y) - 1) = f(y)(u(x) - 1) for all x,y ∈ ℝ.
  have h2 : ∀ x y : ℝ, f x * (u y - 1) = f y * (u x - 1) := by
    intro x y; linarith [h1 x y]

  -- Thus for any x ≠ 0, y ≠ 0, we have (u(x) - 1) / f(x) = (u(y) - 1) / f(y).
  have h3 : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → (u x - 1) / f x =  (u y - 1) / f y := by
    intro x y hx hy
    have hx1 := hfx0 x hx
    have hy1 := hfx0 y hy
    have := h2 x y
    field_simp
    linarith

  -- So there exists C ∈ ℝ such that (u(x) - 1) / f(x) = C for all x ≠ 0.
  have h4: ∃ C : ℝ, ∀ x : ℝ, x ≠ 0 → (u x - 1) / f x = C := by
    use (u 1 - 1) / f 1
    intro x hx
    exact h3 x 1 hx one_ne_zero
  obtain ⟨C, hC⟩ := h4

  -- So u(x) = 1 + C f(x) for x ≠ 0;
  have h5 : ∀ x : ℝ, x ≠ 0 → u x = 1 + C * f x := by
    intro x hx
    have hc1 := hC x hx
    have hx1 := hfx0 x hx
    field_simp at hc1
    linarith

  -- since u(0) = 1, f(0) = 0, this equation also holds for x = 0.
  have h6 : ∀ x : ℝ, u x = 1 + C * f x := by
    intro x
    rcases em (x = 0) with rfl | hnz
    · rw [hf0, h00]; ring
    · exact h5 x hnz

  -- If C = 0, then u(x) = 1 for all x and we are done.
  obtain hCz | hCnz := em (C = 0)
  · use 0
    intro x
    rw [zero_mul, Real.exp_zero]
    have := h6 x
    rwa [hCz, zero_mul, add_zero] at this

  -- Otherwise, observe
  --     u(x + y) = 1 + C f(x + y)
  --              = 1 + C f(x) u(y) + f(y)
  --              = u(y) + C f(x) u(y)
  --              = u(x) u(y)
  -- for all x,y ∈ ℝ.
  have h7 : ∀ x y : ℝ, u (x + y) = u x * u y := by
    intro x y
    calc u (x + y) = 1 + C * f (x + y) := h6 (x + y)
         _         = 1 + C * (f x * u y  + f y) := by rw [hf x y]
         _         = u y + C * f x * u y := by rw [h6 y]; ring
         _         = u y * (1 + C * f x) := by ring
         _         = u y * u x := by rw [h6 x]
         _         = u x * u y := mul_comm (u y) (u x)

  have hum : (StrictMono u ∨ StrictAnti u) := by
    obtain hm | hm := hm
    · obtain h1 | h2 | h3 := lt_trichotomy C 0
      · right; intro x y hxy; nlinarith [hm hxy, h6 x, h6 y]
      · rw [h2] at hCnz; exfalso; apply hCnz; rfl
      · left; intro x y hxy; nlinarith [hm hxy, h6 x, h6 y]
    · obtain h1 | h2 | h3 := lt_trichotomy C 0
      · left; intro x y hxy; nlinarith [hm hxy, h6 x, h6 y]
      · rw [h2] at hCnz; exfalso; apply hCnz; rfl
      · right; intro x y hxy; nlinarith [hm hxy, h6 x, h6 y]

  exact exp_characterization u h7 h00 hum

lemma romania1998_p12_mpr (u : ℝ → ℝ) :
 (∃ k : ℝ, ∀ x : ℝ, u x = Real.exp (k * x)) →
    (∃ f : ℝ → ℝ, (StrictMono f ∨ StrictAnti f)
        ∧ ∀ x y : ℝ, f (x + y) = f x * u y + f y) := by
  rintro ⟨k, hk⟩
  obtain rfl | hknz := eq_or_ne k 0
  · -- k = 0
    use id
    constructor
    · left; exact strictMono_id
    · intro x y
      rw [hk y, zero_mul, Real.exp_zero, mul_one, id_def, id_def, id_def]
  · -- k ≠ 0
    let f : ℝ → ℝ := fun x ↦ Real.exp (k * x) - 1
    have hfm : (StrictMono f ∨ StrictAnti f) := by
      by_cases hkp : 0 < k
      · left
        intro x y hxy
        have := exp_strict_mono' k x y hkp hxy
        exact sub_lt_sub_right this 1
      · right
        intro x y hxy
        have hkn' : k < 0 := by
          simp only [not_lt] at *
          exact Ne.lt_of_le hknz hkp
        have := exp_strict_anti' k x y hkn' hxy
        exact sub_lt_sub_right this 1
    use f
    use hfm
    intro x y
    rw [hk y]
    calc Real.exp (k * (x + y)) - 1
             = Real.exp (k * x + k * y) - 1 := by rw [mul_add]
           _ = Real.exp (k * x) * Real.exp (k * y) - 1 := by rw [Real.exp_add]
           _ = (Real.exp (k * x) - 1) * Real.exp (k * y) +
                  (Real.exp (k * y) - 1) := by ring

snip end

determine solution_set : Set (ℝ → ℝ) :=
  { u | ∃ k : ℝ, ∀ x : ℝ, u x = Real.exp (k * x) }

problem romania1998_p12 (u : ℝ → ℝ) :
    (∃ f : ℝ → ℝ, (StrictMono f ∨ StrictAnti f)
          ∧ ∀ x y : ℝ, f (x + y) = f x * u y + f y) ↔
    u ∈ solution_set :=
⟨romania1998_p12_mp u, romania1998_p12_mpr u⟩


end Romania1998P12
