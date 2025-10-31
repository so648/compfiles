/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Stream.Defs
import Mathlib.Data.Stream.Init
import Mathlib.Tactic

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!

Puzzle referenced from this tweet: https://twitter.com/sigfpe/status/1474173467016589323

From the book _Out of their Minds: The Lives and Discoveries of 15 Great Computer Scientists_
by Dennis Shasha and Cathy Lazere.


Problem: Suppose each (finite) word is either "decent" or "indecent". Given an infinite
sequence of characters, can you always break it into finite words so that all of them
except perhaps the first one belong to the same class?

-/

namespace KolmogorovStreams
open scoped Stream'

variable {α : Type}

def break_into_words :
   (Stream' ℕ) → -- word lengths
   (Stream' α) → -- original sequence
   (Stream' (List α)) -- sequence of words
 := Function.curry
     (Stream'.corec
       (fun ⟨lengths, a'⟩ ↦ a'.take lengths.head)
       (fun ⟨lengths, a'⟩ ↦ ⟨lengths.tail, a'.drop lengths.head⟩))

snip begin

--#eval ((break_into_words id id).take 10 )

/--
Dropping the first word is equivalent to dropping `first_length` symbols of the original stream.
-/
lemma break_into_words_cons
    (lengths : Stream' ℕ)
    (first_length : ℕ)
    (a : Stream' α) :
    (break_into_words (first_length::lengths) a).tail =
           break_into_words lengths (a.drop first_length) := by
  simp [break_into_words, Stream'.corec, Stream'.tail_map, Stream'.tail_iterate]

lemma break_into_words_closed_form
    (lengths : Stream' ℕ)
    (a : Stream' α)
   : break_into_words lengths a =
      (fun i ↦ Stream'.take (lengths i) (Stream'.drop (∑ j ∈ Finset.range i, lengths j) a)) := by
  funext n
  convert_to ((Stream'.corec (fun x ↦ Stream'.take (x.fst.head) x.snd)
                 (fun x ↦ ⟨x.fst.tail, Stream'.drop (x.fst.head) x.snd⟩)) :
                  Stream' ℕ × Stream' α → Stream' (List α)) ⟨lengths, a⟩ n =
             Stream'.take (lengths n) (Stream'.drop (∑ j ∈ Finset.range n, lengths j) a)
  rw [Stream'.corec_def,Stream'.map]
  congr
  · revert a lengths
    induction n with
    | zero => intro a b; rfl
    | succ pn hpn =>
      intro a b
      rw [Stream'.get_succ, Stream'.iterate_eq, Stream'.tail_cons, hpn]
      rfl
  · revert a lengths
    induction n with
    | zero => intro a b; rfl
    | succ pn hpn =>
      intro a b
      rw [Stream'.get_succ, Stream'.iterate_eq, Stream'.tail_cons, hpn,
          Stream'.drop_drop, Finset.sum_range_succ']
      rw [Nat.add_comm]
      congr


def all_prefixes (p : List α → Prop) (a : Stream' α) : Prop := a.inits.All p

lemma take_prefix
    (is_decent : List α → Prop)
    (a : Stream' α)
    (ha : all_prefixes is_decent a)
    (n : ℕ)
    (hn : 0 < n) : is_decent (a.take n) := by
  cases n with
  | zero => exfalso; exact Nat.lt_asymm hn hn
  | succ n =>
    have ht := ha n
    rwa [Stream'.get_inits] at ht

structure decent_word (a : Stream' α) (is_decent : List α → Prop) : Type where
  (start : ℕ)
  (length : ℕ)
  (nonempty : 0 < length)
  (h : is_decent ((a.drop start).take length))

structure decent_accumulator (a : Stream' α) (is_decent : List α → Prop) : Type where
  (start : ℕ)
  (prefix_decent : all_prefixes is_decent (a.drop start))

noncomputable def choose_decent_words
    (is_decent : List α → Prop)
    (a : Stream' α)
    (hinit : all_prefixes is_decent a)
    (hnot : ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
            all_prefixes is_decent (a.drop (n + k)))
     : Stream' (decent_word a is_decent) :=
  Stream'.corec (fun (acc: decent_accumulator a is_decent) ↦
                  let new_word_length := Classical.choose (hnot acc.start)
                  let new_word_nonempty := (Classical.choose_spec (hnot acc.start)).1
                  ⟨acc.start, new_word_length, new_word_nonempty,
                   take_prefix
                    is_decent _ acc.prefix_decent new_word_length new_word_nonempty⟩)
             (fun acc ↦ ⟨acc.start + Classical.choose (hnot acc.start),
                         (Classical.choose_spec (hnot acc.start)).2⟩)
             ⟨0, hinit⟩

lemma chosen_decent_closed_form
    (is_decent : List α → Prop)
    (a : Stream' α)
    (hinit : all_prefixes is_decent a)
    (hnot : ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
            all_prefixes is_decent (a.drop (n + k)))
    : ∀ n : ℕ, (((choose_decent_words is_decent a hinit hnot).get n).start =
              ∑ j ∈ Finset.range n, ((choose_decent_words is_decent a hinit hnot).get j).length)
            := by
  intro n
  induction n with
  | zero => rfl
  | succ n pn => rw [Finset.sum_range_succ, ← pn]; rfl

lemma check_decent_words
    (is_decent : List α → Prop)
    (a : Stream' α)
    (hinit : all_prefixes is_decent a)
    (hnot : ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
             all_prefixes is_decent (a.drop (n + k)))
    : Stream'.All
      is_decent
      (break_into_words
          (fun i ↦ ((choose_decent_words is_decent a hinit hnot).get i).length) a) := by
  rw [break_into_words_closed_form]
  simp_rw [←chosen_decent_closed_form]
  intro j
  exact ((choose_decent_words is_decent a hinit hnot).get j).h

structure indecent_word (a : Stream' α) (is_decent : List α → Prop) : Type where
  (start : ℕ)
  (length : ℕ)
  (nonempty : 0 < length)
  (h : ¬is_decent ((a.drop start).take length))

lemma not_all_prefixes
    (is_decent : List α → Prop)
    (a : Stream' α)
    (h : ¬ all_prefixes is_decent a) :
    ∃ n, ¬ is_decent (a.take (Nat.succ n)) := by
  simp[all_prefixes, Stream'.all_def] at h
  exact h

/-
 accumulator is: n, the number of symbols consumed so far
-/
noncomputable def choose_indecent_words
    (is_decent : List α → Prop)
    (a : Stream' α)
    (h : ∀ (k : ℕ), ¬all_prefixes is_decent (a.drop k))
     : Stream' (indecent_word a is_decent) :=
Stream'.corec (fun n ↦ let hd := not_all_prefixes is_decent (a.drop n) (h n)
                       let new_word_length := Nat.succ (Classical.choose hd)
                       let hh := (Classical.choose_spec hd)
                       ⟨n, new_word_length, Nat.succ_pos _, hh⟩
              )
              (fun n ↦ let hd := not_all_prefixes is_decent (a.drop n) (h n)
                       let new_word_length := Nat.succ (Classical.choose hd)
                       n + new_word_length)
              0

lemma chosen_indecent_closed_form
    (is_decent : List α → Prop)
    (a : Stream' α)
    (h : ∀ (k : ℕ), ¬all_prefixes is_decent (a.drop k))
    : ∀ n : ℕ, (((choose_indecent_words is_decent a h).get n).start =
                ∑ j ∈ Finset.range n, ((choose_indecent_words is_decent a h).get j).length)
             := by
  intro n
  induction n with
  | zero => rfl
  | succ n pn =>
    rw [Finset.sum_range_succ, ← pn]
    rfl

lemma check_indecent_words
    (is_decent : List α → Prop)
    (a : Stream' α)
    (h : ∀ (k : ℕ), ¬all_prefixes is_decent (a.drop k))
    : Stream'.All
      (fun x ↦ ¬ is_decent x)
      (break_into_words
          (fun i ↦ ((choose_indecent_words is_decent a h).get i).length)
          a) := by
  rw [break_into_words_closed_form]
  simp_rw [←chosen_indecent_closed_form]
  intro j
  exact ((choose_indecent_words is_decent a h).get j).h

snip end

def all_same_class
    (is_decent : List α → Prop)
    (b : Stream' (List α))
    : Prop :=
  b.All is_decent ∨ b.All (fun w ↦ ¬is_decent w)

problem kolmogorov_streams
    (is_decent : List α → Prop)
    (a : Stream' α)
    : (∃ (lengths : Stream' ℕ),
       (lengths.All (0 < ·) ∧
        all_same_class is_decent (break_into_words lengths a).tail)) := by
  let p : Prop :=
     (∃ (n : ℕ), ∀ (k : ℕ), 0 < k → ¬all_prefixes is_decent (a.drop (n + k)))

  obtain h | hnot := Classical.em p
  · obtain ⟨n, hn⟩ := h
    let a' := a.drop (n + 1)
    have hn' : ∀ (k : ℕ), ¬all_prefixes is_decent (a'.drop k) := by
      intro k
      have hnk := hn (k + 1) (Nat.succ_pos _)
      rwa [Stream'.drop_drop, Nat.add_right_comm]
    let d := choose_indecent_words is_decent a' hn'
    use n.succ::(fun i ↦ (d.get i).length)
    constructor
    · intro i
      cases i with
      | zero => exact Nat.succ_pos n
      | succ i => exact (d.get i).nonempty
    · right
      rw [break_into_words_cons]
      exact check_indecent_words is_decent a' hn'

  · unfold p at hnot; push_neg at hnot
    obtain ⟨k, hkp, hinit⟩ := hnot 0
    have hdka : a.drop (0 + k) = a.drop k := by { rw [←Stream'.drop_drop]; rfl }
    rw [hdka] at hinit
    let a' := a.drop k
    have hnot' : ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧ all_prefixes is_decent (a'.drop (n + k)) := by
      intro n'
      obtain ⟨k', hk0', hk'⟩ := hnot (k + n')
      use k'
      constructor
      · exact hk0'
      · have hd: (a.drop (k + n' + k')) = (a'.drop (n' + k')) := by
          rw [Stream'.drop_drop]
          ring_nf
        rwa [←hd]
    let d := choose_decent_words is_decent a' hinit hnot'
    use k::(fun i ↦ (d.get i).length)
    constructor
    · intro i
      cases i with
      | zero => exact hkp
      | succ i => exact (d.get i).nonempty
    · left
      rw [break_into_words_cons]
      exact check_decent_words is_decent a' hinit hnot'


end KolmogorovStreams
