/-
Copyright (c) 2023 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Midpoint
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Triangle

import ProblemExtraction

problem_file { tags := [.Geometry] }

/-!
# Bulgarian Mathematical Olympiad 1998, Problem 2

A convex quadrilateral ABCD has AD = CD and ∠DAB = ∠ABC < 90°.
The line through D and the midpoint of BC intersects line AB
in point E. Prove that ∠BEC = ∠DAC. (Note: The problem is valid
without the assumption ∠ABC < 90°.)
-/

--凸四角形ABCDにおいて、AD=CDかつ∠DAB = ∠ABC < 90°、BCの中点をMとし、DMとABの
--交点をEとするとき、∠BEC = ∠DAC を証明せよ

namespace Bulgaria1998P2

open EuclideanGeometry
--ユークリッド幾何学に関する定義・補題をそのまま使えるようにする。

problem bulgaria1998_p2
    (A B C D E M : EuclideanSpace ℝ (Fin 2))
    (H1 : dist D A = dist D C)
    (H2 : ∠ D A B = ∠ A B C)
    (H3 : M = midpoint ℝ B C):
    ∠ B E C = ∠ D A C := by
  let x := ∠ D A C
  have : ∠ D A C = ∠ D C A := EuclideanGeometry.angle_eq_angle_of_dist_eq H1
  --H1（AD = CD）から、三角形 ADC が二等辺三角形なので ∠DAC = ∠DCA になるという補題を使う
  let y := ∠ C A B
  have : ∠ A B C = x + y := by rw [←H2]; sorry -- need to switch to oangles?
  sorry

end Bulgaria1998P2
