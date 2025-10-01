-- Basic Lean 4 examples demonstrating theorems and proofs

-- Simple example of type definitions
structure Point where
  x : Float
  y : Float

-- Basic function definition
def distance (p1 p2 : Point) : Float :=
  Float.sqrt ((p1.x - p2.x)^2 + (p1.y - p2.y)^2)

-- Simple theorem: addition is commutative
theorem add_comm_example (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

-- Simple theorem: zero is the additive identity
theorem add_zero_example (n : Nat) : n + 0 = n := by
  exact Nat.add_zero n

-- Example of list operations
def example_list : List Nat := [1, 2, 3, 4, 5]

-- Function to double all elements in a list
def double_list (l : List Nat) : List Nat :=
  l.map (fun x => x * 2)

-- Example computation
#eval double_list example_list

-- Simple addition function
def add_two (n : Nat) : Nat := n + 2

-- Example usage
#eval add_two 5

-- Simple conditional function
def is_even (n : Nat) : Bool :=
  n % 2 = 0

-- Example usage
#eval is_even 4
#eval is_even 5
