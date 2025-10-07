-- This module serves as the root of the `DocTest` library.
-- Import modules here that should be built as part of the library.
import MiniWalnut.Basic
import Mathlib.Computability.DFA

/-!

  # Nothing interesting

-/

/-- this is very interesting-/
def what : DFA Nat Nat:=
{
  step := fun x y => y
  start := 0
  accept := {x | x=100}
}
