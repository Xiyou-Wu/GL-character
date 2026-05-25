import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic

def hello := "world"

-- Test that mathlib definitions are available
#check (1 : ℕ)
#check Group

-- A simple theorem using mathlib
example : 1 + 1 = 2 := by rfl
