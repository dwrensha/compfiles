/-!
# IMO 2018 Q3

An anti-Pascal triangle is an equilateral triangular array of numbers such that,
except for the numbers in the bottom row, each number is the absolute value
of the difference of the two numbers immediately below it. For example,
the following array is an anti-Pascal triangle with four rows
which contains every integer from 1 to 10:

                  4
                2   6
              5   7   1
            8   3  10   9

Does there exist an anti-Pascal triangle with 2018 rows which contains every
integer from 1 to 1 + 2 + ... + 2018?

# Solution
No.

-/


structure Coords where
(row : Nat) (col : Nat)

def left_child (c : Coords) : Coords :=
 ⟨c.row.succ, c.col⟩

def right_child (c : Coords) : Coords :=
  ⟨c.row.succ, c.col.succ⟩

/--
antipascal triangle with n rows
-/
structure antipascal_triangle (n : Nat) where
(f : Coords → Nat)
(antipascal : ∀ x: Coords, x.row.succ < n ∧ x.col ≤ x.row →
  f x + f (left_child x) = f (right_child x) ∨
  f x + f (right_child x) = f (left_child x))

structure a_and_b where
(a : Coords) (b : Coords)

def range : Nat → List Nat
| 0 => []
| n+1 => (n+1)::(range n)

def sumList : List Nat → Nat
| [] => 0
| a :: as => a + sumList as

theorem imo2018_q3 (t : antipascal_triangle 2018)
  (h_contains_all : ∀ n, n ≤ sumList (range 2018) →
    ∃ r, r ≤ 2018 ∧ ∃ c, c < r ∧ t.f ⟨r,c⟩ = n) :
  False := by admit
