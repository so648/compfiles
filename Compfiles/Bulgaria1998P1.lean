/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

import ProblemExtraction

problem_file { tags := [.Combinatorics] }

/-!
# Bulgarian Mathematical Olympiad 1998, Problem 1

We will be considering colorings in 2 colors of n (distinct) points
A₁, A₂, ..., Aₙ. Call such a coloring "good" if there exist three points
Aᵢ, Aⱼ, A₂ⱼ₋ᵢ, 1 ≤ i < 2j - i ≤ n, which are colored the same color.

Find the least natural number n (n ≥ 3) such that all colorings
of n points are good.
-/

--n 個の異なる点 A₁, A₂, …, Aₙ を 2 色で塗り分けることを考える。
--このとき、すべて同じ色で塗られているような 3 点 Aᵢ, Aⱼ, A₂ⱼ₋ᵢ（ただし 1 ≤ i < 2j - i ≤ n）
--が存在するとき
--その塗り分けを「良い（good）」と呼ぶ。
--すべての塗り分けが「良い」になるような最小の自然数 n（n ≥ 3）を求めよ。

namespace Bulgaria1998P1

abbrev coloring_is_good {m : ℕ} (color : Set.Icc 1 m → Fin 2) : Prop :=
  ∃ i j : Set.Icc 1 m,
    i < j ∧
    ∃ h3 : 2 * j.val - i ∈ Set.Icc 1 m,
    color i = color j ∧ color i = color ⟨2 * j - i, h3⟩
--塗分けが良い(coloring_is_good)とはどういうことかをLean上で定義している。
--abbrevは略記的な、defにしても機能した
--color は、1からmまでの整数を 2色で塗り分ける写像
--Fin 2 は {0, 1} の2元集合
--iはjより小さい かつ
--h3: 2 * j - i という整数も [1, m] に含まれる。
--j.valはSet.Icc 1 m の要素を普通の自然数として取り出したもの
--iとjは同じ色に塗られている。
--かつ、iと2j - i も同じ色に塗られている。
--最後の ⟨2*j - i, h3⟩ は「2j-i が区間に入っている」という証明付きのペアで、color に入力できる形にしている

abbrev all_colorings_are_good (m : ℕ) : Prop :=
  3 ≤ m ∧ ∀ color : Set.Icc 1 m → Fin 2, coloring_is_good color
--3以上のmに対し、整数の区間 [1, m] を 2 色で塗ると、どんな塗り分け(color)でも必ず
--i, j, 2j - i が同色になるような組が存在する

snip begin

lemma lemma1 {m n : ℕ} (hmn : m ≤ n) (hm : all_colorings_are_good m) :
--lemma1 m ≤ n の仮定、区間 [1, m] に対して、すべての 2 色塗りがgood
    all_colorings_are_good n := by    --それなら、区間 [1, n] に対してもすべての 2 色塗りがgoodを示す
  constructor    --3 ≤ n、任意の彩色 c が coloring_is_goodのペアなのでconstructor で分解
  · exact hm.1.trans hmn    --hm.1 は 3 ≤ m, hmn は m ≤ n なので推移律より 3 ≤ n
  · intro c   --c : Set.Icc 1 n → Fin 2 は [1, n] の彩色
    let c' : Set.Icc 1 m → Fin 2 :=
      fun x ↦ c ⟨x.val, by rw [Set.mem_Icc]; exact ⟨x.prop.1, x.prop.2.trans hmn⟩⟩
    --[1, m] に制限した彩色 c' を作る
    --x : Set.Icc 1 m から x.val : ℕ を取り出して、それが [1, n] に含まれることを確認
    --x.prop.1の部分は「1 ≤ x」
    --x.prop.2.trans hmn の部分は「x ≤ m かつ m ≤ n ⇒ x ≤ n」を保証。よって、1 ≤ x ≤ n
    obtain ⟨⟨i, hi1, hi2⟩, ⟨j, hj1, hj2⟩, hij1, hij2, hc1, hc2⟩ := hm.2 c'
    --hm.2 は「任意の [1 ,m] の彩色は good」という性質。
    --c' を入れると「c' の中に good なペア (i,j) がある」と分解できる
    --i,j ∈ Set.Icc 1 m で、i < j、かつ「3項等差数列が同色」という条件を満たす
    use ⟨i, hi1, hi2.trans hmn⟩
    use ⟨j, hj1, hj2.trans hmn⟩
    --[1, m] にいた i, j を [1, n] の要素に埋め込み直す
    --その理由は、Set.Icc 1 m と Set.Icc 1 n は別の型なので
    simp only [Subtype.mk_lt_mk, Set.mem_Icc, tsub_le_iff_right, exists_and_left]
    --⟨i,hi⟩<⟨j,hj⟩⟺i < j  x∈[a, b]⟺a≤x∧x≤b   2∗j−i≤m ⟺ 2∗j≤m+i  (∃x,A∧B)⟺(∃x,A)∧B
    simp only [Subtype.mk_lt_mk] at hij1
    --⟨i,hi⟩<⟨j,hj⟩⟺i < j より、hij1 : i < j となる
    refine ⟨hij1, ?_⟩  -- i < j は示せたので、もう1つを示す
    simp only [Set.mem_Icc, tsub_le_iff_right] at hij2
    --2j - i ∈ Set.Icc 1 m を 1 ≤ 2j - i ∧ 2j ≤ m + iに書き換え(Leanの面倒な部分？)
    simp only [c'] at hc1
    --hc1 を c に展開して，c i = c j を得る（simp only [ c'] at hc1）
    refine ⟨hc1, ?_⟩
    have hij2' : 1 ≤ 2 * j - i ∧ 2 * j ≤ n + i :=
       ⟨hij2.1, le_add_of_le_add_right hij2.2 hmn⟩
    use hij2' --よって区間 [1, n] に対してもすべての 2 色塗りがgood

def coloring_of_eight {n : ℕ} : Set.Icc 1 n → Fin 2
| ⟨1, _⟩ => 0
| ⟨2, _⟩ => 1
| ⟨3, _⟩ => 0
| ⟨4, _⟩ => 1
| ⟨5, _⟩ => 1
| ⟨6, _⟩ => 0
| ⟨7, _⟩ => 1
| ⟨8, _⟩ => 0
| _ => 0 -- unreachable  (9以上の部分は0)
--長さ8の場合、goodではない例が存在した。
--⟨k, _⟩ の _ は「1 ≤ k ≤ n の証明」です。その数が範囲 [1 , n] に含まれているという証拠も
--含んだペアとして扱う

lemma lemma2 :
    ∃ f : Set.Icc 1 8 → Fin 2, ¬coloring_is_good f := by
  --区間 [1 ,8] に対してある 2 色塗りが存在し、その塗り分けは good ではない（同色の 3 項等差が存在しない）
  use coloring_of_eight
  intro h
  obtain ⟨⟨i, hi1, hi2⟩, ⟨j, hj1, hj2⟩, hij1, hij2, hc1, hc2⟩ := h
  dsimp [coloring_of_eight] at *
  interval_cases i <;> interval_cases j <;> sorry --aesop (simp_config := {decide := true})

snip end

determine solution_value : ℕ := 9

problem bulgaria1998_p1 : IsLeast { m | all_colorings_are_good m } solution_value := by
--[1 ,m] の任意の2色塗りで good が必ずできる最小の自然数 m は solution_value(9) である
  constructor
  --solution_value ∈ S と、solution_value より小さい自然数は S に入らない　に分解
  · rw [Set.mem_setOf_eq]  --all_colorings_are_good m を証明すればよい。
    refine ⟨by norm_num, ?_⟩  --by norm_num で 3 ≤ solution_value を証明している
                             --?_ の部分が次の「任意の coloring が good であること」を証明する箇所
    intro color  --「任意の coloring」を取る準備
    sorry
  · rw [mem_lowerBounds]  --「IsLeast の定義」により、全ての下界 n について考える
    intro n hn  --「solution_value より小さい n が S に入ると仮定」
    rw [Set.mem_setOf_eq] at hn
    by_contra! H
    have h1 : n ≤ solution_value - 1 := Nat.le_pred_of_lt H
    have ⟨h2, h3⟩ := lemma1 h1 hn
    obtain ⟨f, hf⟩ := lemma2
    exact (hf (h3 f)).elim


end Bulgaria1998P1
