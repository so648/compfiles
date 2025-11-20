/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Data.Set.Lattice
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

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
--長さ8で、上の例を挙げる(これをcoloring_of_eightとする)
--⟨k, _⟩ の _ は1 ≤ k ≤ n で、その数が範囲 [1 , n] に含まれているという証拠も
--含んだペアとして扱う

lemma lemma2 :
    ∃ f : Set.Icc 1 8 → Fin 2, ¬coloring_is_good f := by
  --[1, 8]を2色に塗り分けても、goodにならない例が存在することの証明
  use coloring_of_eight-- 上で定義した coloring_of_eight を使う
  intro h -- good (h) と仮定して矛盾を導く
  rcases h with ⟨⟨i, hi⟩, ⟨j, hj⟩, hij1, h_k, hc1, hc2⟩
  -- i と j を ℕ として取り出し、その範囲の仮定 hi, hj を得る
  simp only [Set.mem_Icc] at hi hj
  -- hi (i ∈ [1, 8]) を 1 ≤ i ∧ i ≤ 8 に書き換える
  cases hi; cases hj
  -- interval_cases i のためにhiを (1 ≤ i) と (i ≤ 8) に分解する。jについても同様
  interval_cases i <;> interval_cases j
  --i と j の 8x8=64 通りの場合分けを行う
  all_goals
  -- 64個のゴールすべて (all_goals) に
  -- 以下のタクティク (;) を順番に適用する
    (simp only [coloring_of_eight] at *;
    -- まず、my_coloring_of_eight の定義のみ
    -- 仮定とゴール (at *) で展開する。
     simp at *)
    -- 次に、残りの仮定 (hij1 や h_k) と、
    -- 前段階でで生成された 0 = 1 などをすべてsimpする
    -- これにより、仮定 (1<1 とか 9≤8 とか 0=1) の
    -- どれかが False となりok

snip end

determine solution_value : ℕ := 9

-- 【メインの証明】9 が条件を満たす最小の数であることを証明する
problem bulgaria1998_p1 : IsLeast { m | all_colorings_are_good m } solution_value := by
  constructor
  · -- ステップ1: n=9 のとき、すべての塗り分けが良いことを証明する
    change all_colorings_are_good 9
    dsimp [all_colorings_are_good]
    constructor
    · norm_num -- 3 ≤ 9 は自明
    · intro color
      -- 背理法開始: もし「良くない (goodでない)」塗り分けが存在すると仮定する
      by_contra h_bad

      -- 記述を簡単にするため、color ⟨k, ...⟩ を c k と書けるようにする
      let c (k : ℕ) (hk : k ∈ Set.Icc 1 9) := color ⟨k, hk⟩

      -- [補題A] 鳩の巣原理の変形: 「2色が等しくないなら、残りの色と等しい」
      -- (x!=z かつ y!=z ならば、x,yは共にzじゃない方の色なので x=y)
      have fin2_claim : ∀ (x y z : Fin 2), x ≠ z → y ≠ z → x = y := by
        intro x y z hx hy
        revert x y z hx hy
        decide -- Fin 2 は有限なので計算で証明完了

      -- [補題B] 「同色の等差数列を作ってはいけない」という制約
      -- c(i)=c(j) ならば、3点目 c(k) はそれと異なる色でなければならない
      have no_ap : ∀ (i j k : ℕ) (hi : i ∈ Set.Icc 1 9) (hj : j ∈ Set.Icc 1 9) (hk : k ∈ Set.Icc 1 9),
          i < j → 2 * j - i = k → c i hi = c j hj → c k hk ≠ c j hj := by
        intro i j k hi hj hk hij heq h_ci_cj h_ck_cj_eq
        -- もし c(k) = c(j) なら、i, j, k は同色等差数列になる
        -- これは「良くない塗り分け」という仮定 h_bad に矛盾する
        apply h_bad
        -- 矛盾する構成要素 (i, j, 証明) を渡す
        refine ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, ?_⟩
        -- 3点目(2j-i)が範囲内にあることの証明
        have h_idx : 2 * j - i = k := heq
        refine ⟨h_idx.symm ▸ hk, ?_⟩
        -- 色が一致することの証明
        simp [c] at h_ci_cj h_ck_cj_eq
        constructor
        · exact h_ci_cj
        · rw [h_ci_cj, ←h_ck_cj_eq]
          congr
          exact h_idx.symm

      -- ここから具体的な背理法による探索
      -- 1~9 が範囲内であることの証明をあらかじめ用意
      let n1 : 1 ∈ Set.Icc 1 9 := by norm_num
      let n2 : 2 ∈ Set.Icc 1 9 := by norm_num
      let n3 : 3 ∈ Set.Icc 1 9 := by norm_num
      let n4 : 4 ∈ Set.Icc 1 9 := by norm_num
      let n5 : 5 ∈ Set.Icc 1 9 := by norm_num
      let n6 : 6 ∈ Set.Icc 1 9 := by norm_num
      let n7 : 7 ∈ Set.Icc 1 9 := by norm_num
      let n8 : 8 ∈ Set.Icc 1 9 := by norm_num
      let n9 : 9 ∈ Set.Icc 1 9 := by norm_num

      -- [論証1] 中心に近い c(3) と c(5) は異なる色でなければならない
      have c3_ne_c5 : c 3 n3 ≠ c 5 n5 := by
        intro h -- 仮定: c(3) = c(5)
        -- 1, 3, 5 は等差数列。c(1)はc(3)と異なる
        have c1_ne : c 1 n1 ≠ c 3 n3 := by
          intro h1
          exact no_ap 1 3 5 n1 n3 n5 (by norm_num) (by norm_num) h1 h.symm
        -- 3, 5, 7 は等差数列。c(7)はc(5)と異なる
        have c7_ne : c 7 n7 ≠ c 5 n5 :=
          no_ap 3 5 7 n3 n5 n7 (by norm_num) (by norm_num) h
        -- 3, 4, 5 は等差数列。c(4)はc(3)と異なる
        have c4_ne : c 4 n4 ≠ c 3 n3 := by
          intro h4
          apply no_ap 3 4 5 n3 n4 n5 (by norm_num) (by norm_num) h4.symm
          rw [h4, h]
        -- c(1), c(4), c(7) はすべて c(3) と異なる色。よってこれら3つは同色。
        have c1_eq_c4 : c 1 n1 = c 4 n4 := fin2_claim _ _ (c 3 n3) c1_ne c4_ne
        have c4_eq_c7 : c 4 n4 = c 7 n7 := by
           rw [←h] at c7_ne
           exact fin2_claim _ _ (c 3 n3) c4_ne c7_ne
        -- しかし 1, 4, 7 も等差数列なので、これらが同色だと矛盾
        apply no_ap 1 4 7 n1 n4 n7 (by norm_num) (by norm_num) c1_eq_c4
        exact c4_eq_c7.symm

      -- [論証2] 対称性より c(5) と c(7) も異なる色でなければならない
      have c5_ne_c7 : c 5 n5 ≠ c 7 n7 := by
        intro h -- 仮定: c(5) = c(7)
        -- 以下、論証1と同様のロジック
        have c3_ne : c 3 n3 ≠ c 5 n5 := by
           intro h3
           exact no_ap 3 5 7 n3 n5 n7 (by norm_num) (by norm_num) h3 h.symm
        have c9_ne : c 9 n9 ≠ c 7 n7 :=
           no_ap 5 7 9 n5 n7 n9 (by norm_num) (by norm_num) h
        have c6_ne : c 6 n6 ≠ c 5 n5 := by
           intro h6
           apply no_ap 5 6 7 n5 n6 n7 (by norm_num) (by norm_num) h6.symm
           rw [h6, h]
        -- c(3), c(6), c(9) が同色になり、3-6-9 で矛盾
        have c3_eq_c6 : c 3 n3 = c 6 n6 := fin2_claim _ _ (c 5 n5) c3_ne c6_ne
        have c6_eq_c9 : c 6 n6 = c 9 n9 := by
           rw [←h] at c9_ne
           exact fin2_claim _ _ (c 5 n5) c6_ne c9_ne
        apply no_ap 3 6 9 n3 n6 n9 (by norm_num) (by norm_num) c3_eq_c6
        exact c6_eq_c9.symm

      -- [まとめ] c(3) != c(5) かつ c(7) != c(5) なので、c(3) == c(7)
      have c3_eq_c7 : c 3 n3 = c 7 n7 := fin2_claim _ _ (c 5 n5) c3_ne_c5 (Ne.symm c5_ne_c7)

      -- 最後に c(4) の色で場合分けをして矛盾を追い詰める
      by_cases h45 : c 4 n4 = c 5 n5
      · -- ケース1: c(4) == c(5) の場合
        -- 4,5,6 より c(6)!=c(5)
        have c6_ne : c 6 n6 ≠ c 5 n5 := no_ap 4 5 6 n4 n5 n6 (by norm_num) (by norm_num) h45
        -- c(6)!=c(5) かつ c(3)!=c(5) より c(6)=c(3)=c(7)
        have c6_eq_c3 : c 6 n6 = c 3 n3 := fin2_claim _ _ (c 5 n5) c6_ne c3_ne_c5

        -- 3,6,9 より c(9)!=c(6)=c(3)=c(7)。よって c(9)=c(5)
        have c9_ne : c 9 n9 ≠ c 6 n6 := by
           intro h
           apply no_ap 3 6 9 n3 n6 n9 (by norm_num) (by norm_num) c6_eq_c3.symm
           exact h
        have c9_eq : c 9 n9 = c 5 n5 := fin2_claim _ _ (c 6 n6) c9_ne (Ne.symm c6_ne)

        -- 1,5,9 より c(1)!=c(5)。よって c(1)=c(3)=c(6)
        have c1_ne : c 1 n1 ≠ c 5 n5 := by
           intro h
           have contra := no_ap 1 5 9 n1 n5 n9 (by norm_num) (by norm_num) h
           exact contra c9_eq
        have c1_eq : c 1 n1 = c 3 n3 := fin2_claim _ _ (c 5 n5) c1_ne c3_ne_c5

        -- 1,2,3 より c(2)!=c(1)=c(3)。よって c(2)=c(5)
        have c2_ne : c 2 n2 ≠ c 1 n1 := by
           intro h
           apply no_ap 1 2 3 n1 n2 n3 (by norm_num) (by norm_num) h.symm
           rw [←c1_eq]
           exact h.symm
        have c2_eq : c 2 n2 = c 5 n5 := fin2_claim _ _ (c 1 n1) c2_ne (Ne.symm c1_ne)

        -- 2,5,8 より c(8)!=c(5)=c(2)。よって c(8)=c(1)=c(3)=c(6)=c(7)
        have c8_ne : c 8 n8 ≠ c 5 n5 := by
           apply no_ap 2 5 8 n2 n5 n8 (by norm_num) (by norm_num) c2_eq
        have c8_eq : c 8 n8 = c 3 n3 := fin2_claim _ _ (c 5 n5) c8_ne c3_ne_c5

        -- 6, 7, 8 がすべて c(3) と同色になり、長さ3の同色AP完成 → 矛盾
        apply no_ap 6 7 8 n6 n7 n8 (by norm_num) (by norm_num)
        · rw [c6_eq_c3, c3_eq_c7]
        · rw [c8_eq, c3_eq_c7]

      · -- ケース2: c(4) != c(5) の場合 (つまり c(4) = c(3))
        have c4_eq : c 4 n4 = c 3 n3 := fin2_claim _ _ (c 5 n5) h45 c3_ne_c5

        -- 1,4,7 は c(1), c(3), c(3) なので c(1)!=c(3)。よって c(1)=c(5)
        have c1_ne : c 1 n1 ≠ c 4 n4 := by
          intro h
          have := no_ap 1 4 7 n1 n4 n7 (by norm_num) (by norm_num) h
          rw [c4_eq, c3_eq_c7] at this
          exact this rfl
        have c1_eq : c 1 n1 = c 5 n5 := fin2_claim _ _ (c 4 n4) c1_ne (Ne.symm h45)

        -- 1,5,9 は c(5), c(5), c(9) なので c(9)!=c(5)。よって c(9)=c(3)
        have c9_ne : c 9 n9 ≠ c 5 n5 := by
           intro h
           apply no_ap 1 5 9 n1 n5 n9 (by norm_num) (by norm_num) c1_eq
           exact h
        have c9_eq : c 9 n9 = c 3 n3 := fin2_claim _ _ (c 5 n5) c9_ne c3_ne_c5

        -- 3,6,9 は c(3), c(6), c(3) なので c(6)!=c(3)。よって c(6)=c(5)
        have c6_ne : c 6 n6 ≠ c 3 n3 := by
           intro h
           apply no_ap 3 6 9 n3 n6 n9 (by norm_num) (by norm_num) h.symm
           rw [h, c9_eq]
        have c6_eq : c 6 n6 = c 5 n5 := fin2_claim _ _ (c 3 n3) c6_ne (Ne.symm c3_ne_c5)

        -- 7,8,9 は c(3), c(8), c(3) なので c(8)!=c(3)。よって c(8)=c(5)
        have c8_ne : c 8 n8 ≠ c 7 n7 := by
          intro h
          have := no_ap 7 8 9 n7 n8 n9 (by norm_num) (by norm_num) h.symm
          rw [c9_eq, c3_eq_c7] at this
          rw [h] at this
          exact this rfl
        have c8_eq : c 8 n8 = c 5 n5 := fin2_claim _ _ (c 7 n7) c8_ne c5_ne_c7

        -- 2,5,8 は c(2), c(5), c(5) なので c(2)!=c(5)。よって c(2)=c(3)
        have c2_ne : c 2 n2 ≠ c 5 n5 := by
           intro h
           apply no_ap 2 5 8 n2 n5 n8 (by norm_num) (by norm_num) h
           exact c8_eq
        have c2_eq : c 2 n2 = c 3 n3 := fin2_claim _ _ (c 5 n5) c2_ne c3_ne_c5

        -- 2, 3, 4 がすべて c(3) と同色になり、矛盾
        apply no_ap 2 3 4 n2 n3 n4 (by norm_num) (by norm_num) c2_eq
        exact c4_eq

  · -- ステップ2: 9 が最小であることを証明する
    rw [mem_lowerBounds]
    intro n hn
    rw [Set.mem_setOf_eq] at hn
    -- もし n < 9 で成り立つなら (つまり n <= 8 なら)
    by_contra! H
    have h1 : n ≤ 8 := Nat.le_pred_of_lt H
    -- lemma1 より n=8 でも成り立たなければならない
    have h_all_good_8 := lemma1 h1 hn
    -- しかし lemma2 で反例を示したので矛盾する
    obtain ⟨f, hf⟩ := lemma2
    exact hf (h_all_good_8.2 f)
end Bulgaria1998P1
