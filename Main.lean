-- The `main` function is the entry point of your program.
-- Its type is `IO Unit` because it can perform `IO` operations (side effects).
def main : IO Unit :=
  -- Define a list of names
  let names := ["One", "Two", "Three"]

  -- Print the list of greetings
  for name in names do
    IO.println name
