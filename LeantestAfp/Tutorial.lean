-- Tutorial: Your First Lean 4 Proofs
-- This file walks through basic Lean 4 concepts step by step

-- 1. SIMPLE FUNCTION DEFINITIONS
-- Functions in Lean are defined with 'def'

def double (n : Nat) : Nat := n * 2

-- Test it:
#eval double 5  -- Should output 10

-- 2. BASIC TYPES AND STRUCTURES
-- You can define custom types using 'structure'

structure Student where
  name : String
  age : Nat
  grade : String

-- Create an instance:
def alice : Student := ⟨"Alice", 20, "A"⟩

-- 3. SIMPLE THEOREMS
-- Theorems are propositions that we prove to be true

-- This theorem says that for any number n, n + 0 equals n
theorem zero_add (n : Nat) : n + 0 = n := by
  -- Lean knows this is true, so we can use 'rfl' (reflexivity)
  rfl

-- This theorem says addition is commutative
theorem my_add_comm (a b : Nat) : a + b = b + a := by
  -- We can use existing theorems from Lean's library
  exact Nat.add_comm a b

-- 4. CONDITIONAL FUNCTIONS
-- Functions can have different behavior based on conditions

def describe_age (age : Nat) : String :=
  if age < 13 then "child"
  else if age < 20 then "teenager"
  else "adult"

#eval describe_age 15  -- Should output "teenager"

-- 5. WORKING WITH LISTS
-- Lists are a fundamental data structure

def my_numbers : List Nat := [1, 2, 3, 4, 5]

-- Function to add 1 to each element
def increment_all (lst : List Nat) : List Nat :=
  lst.map (fun x => x + 1)

#eval increment_all my_numbers  -- Should output [2, 3, 4, 5, 6]

-- 6. RECURSIVE FUNCTIONS
-- Functions can call themselves

def countdown (n : Nat) : List Nat :=
  match n with
  | 0 => [0]
  | n + 1 => (n + 1) :: countdown n

#eval countdown 5  -- Should output [5, 4, 3, 2, 1, 0]

-- 7. SIMPLE PROOFS BY INDUCTION
-- Many theorems about natural numbers are proved by induction

theorem add_zero_right (n : Nat) : n + 0 = n := by
  -- This is built into Lean, but we could prove it by induction:
  induction n with
  | zero => rfl  -- Base case: 0 + 0 = 0
  | succ n ih =>
    calc
      Nat.succ n + 0 = Nat.succ (n + 0) := by simp [Nat.succ_add]
      _ = Nat.succ n := by
        exact congrArg Nat.succ ih

-- This is a template for you to try your own proofs!
-- Try proving: theorem double_add (n : Nat) : n + n = 2 * n
