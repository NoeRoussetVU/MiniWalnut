import MiniWalnut.Examples

def conversion (b : B2) : Int :=
  match b with
  | B2.zero => 0
  | B2.one => 1
-- prints graphvis format
def printDFADot : IO Unit := do

  let res := paltm

  IO.println s!"vars {res.vars}"

  IO.println "digraph graph {"
  IO.println "  rankdir=LR;"
  IO.println "  node [shape=circle];"

  -- Mark accept states with double circle
  IO.print "  node [shape=doublecircle]; "
  for state in res.states do
    if state ∈ res.states_accept then
      IO.print s!"{repr state} "
  IO.println ";"

  IO.println "  node [shape=circle];"

  -- Invisible start node
  IO.println "  __start [shape=none, label=\"\"];"
  IO.println s!"  __start -> {res.automata.start};"

  let mut transitions : Std.HashMap (Nat × Nat) (List (List B2)) := Std.HashMap.emptyWithCapacity

  -- Transitions
  for state in res.states do
    for symbol in res.alphabet do
      let next := res.automata.step state symbol
      if transitions.contains (state, next) then
        transitions := transitions.insert  (state, next) ((transitions[(state, next)]!) ++ [symbol] )
      else transitions := transitions.insert (state, next) [symbol]

  for (state, next) in transitions.keys do
    let transition := (transitions[(state,next)]!).map (fun x => x.map (fun y => conversion y) )
    IO.println s!"  {repr state} -> {repr next} [label=\"{transition}\"];"


  IO.println "}"

#time #eval printDFADot

-- The `main` function is the entry point of your program.
-- Its type is `IO Unit` because it can perform `IO` operations (side effects).
--set_option trace.compiler.ir.result true in
def main : IO Unit := do

  let res := paltm

  IO.println s!"vars {res.vars}"

  IO.println "digraph paltm {"
  IO.println "  rankdir=LR;"
  IO.println "  node [shape=circle];"

  -- Mark accept states with double circle
  IO.print "  node [shape=doublecircle]; "
  for state in res.states do
    if state ∈ res.states_accept then
      IO.print s!"{repr state} "
  IO.println ";"

  IO.println "  node [shape=circle];"

  -- Invisible start node
  IO.println "  __start [shape=none, label=\"\"];"
  IO.println s!"  __start -> {res.automata.start};"

  let mut transitions : Std.HashMap (Nat × Nat) (List (List B2)) := Std.HashMap.emptyWithCapacity

  -- Transitions
  for state in res.states do
    for symbol in res.alphabet do
      let next := res.automata.step state symbol
      if transitions.contains (state, next) then
        transitions := transitions.insert  (state, next) ((transitions[(state, next)]!) ++ [symbol] )
      else transitions := transitions.insert (state, next) [symbol]

  for (state, next) in transitions.keys do
    let transition := (transitions[(state,next)]!).map (fun x => x.map (fun y => conversion y) )
    IO.println s!"  {repr state} -> {repr next} [label=\"{transition}\"];"


  IO.println "}"
