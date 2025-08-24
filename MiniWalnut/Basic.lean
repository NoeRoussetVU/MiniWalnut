def hello := "world"


/-
-- FOR LOOP PATTERNS IN LEAN

-- ========================================
-- 1. BASIC ITERATION PATTERNS
-- ========================================

-- Iterate over a range of numbers (0 to n-1)
def sum_range (n : Nat) : Nat :=
  (List.range n).foldl (· + ·) 0

#eval sum_range 10  -- 45 (sum of 0+1+2+...+9)

-- Iterate over a range with a function
def squares_up_to (n : Nat) : List Nat :=
  (List.range n).map (· ^ 2)

#eval squares_up_to 5  -- [0, 1, 4, 9, 16]

-- ========================================
-- 2. FOR EACH PATTERNS
-- ========================================

-- Apply function to each element (like for-each)
def double_all (l : List Nat) : List Nat :=
  l.map (· * 2)

#eval double_all [1, 2, 3, 4, 5]  -- [2, 4, 6, 8, 10]

-- Process each element with side effects (conceptually)
def print_each (l : List String) : IO Unit :=
  l.forM (fun s => IO.println s)

-- Transform each element with index
def with_indices (l : List α) : List (Nat × α) :=
  l.enum

#eval with_indices ['a', 'b', 'c', 'd']  -- [(0, 'a'), (1, 'b'), (2, 'c'), (3, 'd')]

-- ========================================
-- 3. MONADIC FOR LOOPS
-- ========================================

-- For loop in IO monad
def io_for_loop : IO Unit := do
  for i in List.range 5 do
    IO.println s!"Iteration {i}"

-- For loop with accumulator
def sum_with_for (l : List Nat) : Nat := Id.run do
  let mut total := 0
  for x in l do
    total := total + x
  return total

#eval sum_with_for [1, 2, 3, 4, 5]  -- 15

-- For loop building a list
def build_list_with_for (n : Nat) : List Nat := Id.run do
  let mut result := []
  for i in List.range n do
    result := (i * i) :: result
  return result.reverse

#eval build_list_with_for 5  -- [0, 1, 4, 9, 16]

-- ========================================
-- 4. RANGE-BASED ITERATIONS
-- ========================================

-- Iterate from start to end (exclusive)
def range_sum (start stop : Nat) : Nat :=
  if start >= stop then 0
  else (List.range' start (stop - start)).foldl (· + ·) 0

#eval range_sum 5 10  -- 35 (5+6+7+8+9)

-- Iterate with step
def range_with_step (start stop step : Nat) : List Nat :=
  if step = 0 then []
  else
    let count := (stop - start + step - 1) / step
    (List.range count).map (fun i => start + i * step)

#eval range_with_step 0 10 2  -- [0, 2, 4, 6, 8]
#eval range_with_step 1 11 3  -- [1, 4, 7, 10]

-- ========================================
-- 5. WHILE LOOP PATTERNS
-- ========================================

-- While loop using recursion
partial def while_loop {α : Type} (condition : α → Bool) (body : α → α) (initial : α) : α :=
  if condition initial then
    while_loop condition body (body initial)
  else
    initial

-- Example: find first power of 2 greater than n
def next_power_of_2 (n : Nat) : Nat :=
  while_loop (· ≤ n) (· * 2) 1

#eval next_power_of_2 100  -- 128

-- ========================================
-- 6. NESTED LOOPS
-- ========================================

-- Nested loops for matrix operations
def matrix_multiply (a b : List (List Nat)) : List (List Nat) :=
  a.map (fun row =>
    (List.range (b.head?.map List.length |>.getD 0)).map (fun col =>
      (row.zip (b.map (·.get! col))).foldl (fun acc (x, y) => acc + x * y) 0
    )
  )

-- Simple nested loop - multiplication table
def multiplication_table (n : Nat) : List (List Nat) :=
  (List.range n).map (fun i =>
    (List.range n).map (fun j =>
      i * j
    )
  )

#eval multiplication_table 4
-- [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 4, 6], [0, 3, 6, 9]]

-- ========================================
-- 7. MONADIC DO-STYLE LOOPS
-- ========================================

-- Using State monad for stateful loops
def stateful_loop (n : Nat) : StateM Nat (List Nat) := do
  let mut result := []
  let mut current ← get
  for _ in List.range n do
    result := current :: result
    current := current + 1
    set current
  return result.reverse

#eval (stateful_loop 5).run' 10  -- [10, 11, 12, 13, 14]

-- Using ReaderT for environment-based loops
def reader_loop (multiplier : Nat) (l : List Nat) : ReaderM Nat (List Nat) := do
  let factor ← read
  return l.map (· * factor * multiplier)

#eval (reader_loop 2 [1, 2, 3, 4]).run 3  -- [6, 12, 18, 24]

-- ========================================
-- 8. FUNCTIONAL EQUIVALENTS OF COMMON LOOPS
-- ========================================

-- C-style: for(int i = 0; i < n; i++)
def c_style_for (n : Nat) (f : Nat → α) : List α :=
  (List.range n).map f

#eval c_style_for 5 (· ^ 2)  -- [0, 1, 4, 9, 16]

-- C-style: for(int i = start; i < end; i += step)
def c_style_for_step (start end step : Nat) (f : Nat → α) : List α :=
  (range_with_step start end step).map f

-- Python-style: for item in collection
def python_style_for (l : List α) (f : α → β) : List β :=
  l.map f

-- Python-style: for i, item in enumerate(collection)
def python_enumerate_for (l : List α) (f : Nat → α → β) : List β :=
  l.enum.map (fun (i, x) => f i x)

#eval python_enumerate_for ['a', 'b', 'c'] (fun i c => s!"{i}: {c}")
-- ["0: a", "1: b", "2: c"]

-- ========================================
-- 9. LOOP WITH EARLY TERMINATION
-- ========================================

-- Find first element satisfying condition
def find_first (l : List α) (p : α → Bool) : Option α :=
  l.find? p

#eval find_first [1, 2, 3, 4, 5] (· > 3)  -- some 4

-- Take while condition holds
def take_while (l : List α) (p : α → Bool) : List α :=
  l.takeWhile p

#eval take_while [1, 2, 3, 4, 5, 2, 1] (· < 4)  -- [1, 2, 3]

-- Drop while condition holds
def drop_while (l : List α) (p : α → Bool) : List α :=
  l.dropWhile p

#eval drop_while [1, 2, 3, 4, 5] (· < 3)  -- [3, 4, 5]

-- ========================================
-- 10. ADVANCED LOOP PATTERNS
-- ========================================

-- Fold with early termination
def fold_until (l : List α) (init : β) (f : β → α → β) (stop : β → Bool) : β :=
  match l with
  | [] => init
  | x :: xs =>
    let next := f init x
    if stop next then next
    else fold_until xs next f stop

#eval fold_until [1, 2, 3, 4, 5] 0 (· + ·) (· > 6)  -- 10 (stops at 1+2+3+4)

-- Zip with index (enumerate pattern)
def zip_with_index (l : List α) : List (Nat × α) :=
  l.enum

-- Sliding window iteration
def sliding_window (l : List α) (size : Nat) (f : List α → β) : List β :=
  if size > l.length then []
  else (List.range (l.length - size + 1)).map (fun i =>
    f (l.drop i |>.take size))

#eval sliding_window [1, 2, 3, 4, 5] 3 (·.sum)  -- [6, 9, 12]

-- Pairwise iteration
def pairwise (l : List α) (f : α → α → β) : List β :=
  match l with
  | [] | [_] => []
  | x :: y :: rest => f x y :: pairwise (y :: rest) f

#eval pairwise [1, 2, 3, 4, 5] (· + ·)  -- [3, 5, 7, 9]

-- ========================================
-- SUMMARY: LOOP EQUIVALENTS
-- ========================================

/-
IMPERATIVE LOOP          →  LEAN EQUIVALENT
─────────────────────────────────────────────────
for i in 0..n           →  List.range n |>.map f
for x in collection     →  collection.map f
for i, x in enumerate   →  collection.enum.map (uncurry f)
while condition         →  while_loop condition body initial
do...while             →  Custom recursive function
nested for loops       →  Nested maps or cartesian products
break/continue         →  takeWhile/dropWhile/find?
accumulator loops      →  foldl/foldr
stateful loops         →  State monad with for...do

KEY PRINCIPLES:
- Use map for transformations
- Use foldl/foldr for accumulation
- Use for...do in monads for side effects
- Use recursion for complex control flow
- Use takeWhile/dropWhile for early termination
-/



/-- Alternative recursive implementation -/
def combinations_rec {α : Type} (l : List α) : List (List α) :=
  match l with
  | [] => []
  | x :: xs =>
    let sub_combos := combinations_rec xs
    [x] :: sub_combos.map (x :: ·) ++ sub_combos

/-- More explicit recursive implementation showing the logic -/
def combinations_explicit {α : Type} (l : List α) : List (List α) :=
  match l with
  | [] => []
  | x :: xs =>
    let rest_combinations := combinations_explicit xs
    -- For each element, we can either include it or not in each existing combination
    [x] :: rest_combinations ++ rest_combinations.map (x :: ·)

#eval combinations_rec [1, 2, 3]


def processFinInt (n : Fin 3) : String := -- accepts 0-9 only
  match n with
  | 0 => "hawk"
  | 1 => "tu"
  | 2 => "ha"

theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp

/- Define some constants. -/

def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

/- Check their types. -/

#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
-- "&&" is the Boolean and
#check b1 && b2
-- Boolean or
#check b1 || b2
-- Boolean "true"
#check true

/- Evaluate -/
#eval 5 * 4
#eval m + 2
#eval b1 && b2

#check Nat → Nat
#check Nat -> Nat
#check Nat × Nat
#check Prod Nat Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat × Nat → Nat
#check (Nat → Nat) → Nat

#check Nat.succ
#check (0, 1)
#check Nat.add
#check Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
#check (5, 9).1
#check (5, 9).2
#eval Nat.succ 2
#eval Nat.add 5 2
#eval (5, 9).1
#eval (5, 9).2

#check fun (x : Nat) => x + 5
-- λ and fun mean the same thing
#check λ (x : Nat) => x + 5

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2
-/
