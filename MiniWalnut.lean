--import MiniWalnut.Basic
import Std.Data.HashSet
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

-- Create an empty HashSet
def empty : Std.HashSet Nat := Std.HashSet.emptyWithCapacity

-- Create with initial capacity
def emptyWithCap : Std.HashSet String := Std.HashSet.emptyWithCapacity 100

-- Insert elements
def set1 := empty.insert 1
def set2 := set1.insert 2 |>.insert 3

-- Check membership
#eval set2.contains 2  -- true
#eval set2.contains 5  -- false

-- Size
#eval set2.size  -- 3

-- Remove elements
def set3 := set2.erase 2
#eval set3.contains 2  -- false

-- Check if empty
#eval set3.isEmpty  -- false
#eval empty.isEmpty  -- true

structure Point where
  x : Int
  y : Int
  deriving BEq, Hashable

def points : Std.HashSet Point :=
  Std.HashSet.emptyWithCapacity
    |>.insert ⟨1, 2⟩
    |>.insert ⟨3, 4⟩
    |>.insert ⟨1, 2⟩  -- Duplicate, won't add again

#eval points.size  -- 2

#eval points.toList.map (fun p => p.x + p.y)
#eval Std.HashSet.ofList (points.toList.map (fun p => p.x + p.y))


-- Insert from a List
def set_a : Std.HashSet Nat := Std.HashSet.emptyWithCapacity
def set_b := set_a.insertMany [1, 2, 3, 4, 5]
#eval set_b.size  -- 5

-- Insert from an Array
def arr : Array String := #["hello", "world", "lean"]
def set_c := Std.HashSet.emptyWithCapacity.insertMany arr
#eval set_c.contains "lean"  -- true

-- Insert from a Range
def set4 := Std.HashSet.emptyWithCapacity.insertMany (List.range 10)
#eval set4.size  -- 10 (contains 0..9)

-- tuah

-- Create empty Finset
def empty' : Finset Nat := ∅

-- Insert elements (returns new Finset)
def s2 : Finset Nat := {1, 2, 3}  -- Literal syntax

-- Membership
#eval 2 ∈ s2  -- true
#eval 5 ∈ s2  -- false

-- Size
#eval s2.card  -- 3 (card, not size)

-- Convert from List
def s3 := [1, 2, 2, 3].toFinset  -- Automatically removes duplicates


#eval true → true
#eval true → false
#eval false → true
#eval false → false

#eval true ↔ true
#eval true ↔ false
#eval false ↔ true
#eval false ↔ false

#eval Bool.xor true false
#eval Bool.xor true true
#eval Bool.xor false false
#eval Bool.xor false true
