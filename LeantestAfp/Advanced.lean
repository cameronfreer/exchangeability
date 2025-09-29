-- Advanced examples for those who want to explore more
namespace Advanced

-- Example of a simple inductive type
inductive Color where
  | red
  | green
  | blue

-- Pattern matching function
def color_to_string (c : Color) : String :=
  match c with
  | Color.red => "Red"
  | Color.green => "Green"
  | Color.blue => "Blue"

-- Example with recursion on natural numbers
def factorial (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- Example computation
#eval factorial 5

-- Simple theorem about factorial
theorem factorial_positive (n : Nat) : factorial n > 0 := by
  induction n with
  | zero => simp [factorial]
  | succ n ih =>
    have ih' : 0 < factorial n := by
      simpa using ih
    have pos := Nat.mul_pos (Nat.succ_pos n) ih'
    simpa [factorial] using pos

-- Example of dependent types
def vector (α : Type) (n : Nat) : Type :=
  { l : List α // l.length = n }

-- Helper function to create a vector
def mk_vector {α : Type} (l : List α) : vector α l.length :=
  ⟨l, rfl⟩

end Advanced
