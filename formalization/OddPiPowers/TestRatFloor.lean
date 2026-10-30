import Mathlib.Data.Rat.Floor
example : Rat.floor (0 : ℚ) = 0 := by
  rw [Rat.floor_def]
  norm_num
example : Rat.floor ((0 : ℚ) * (1 / 69)) = 0 := by
  rw [Rat.floor_def]
  norm_num
example : Rat.floor (0 : ℚ) = 0 := by
  simp [Rat.floor]
