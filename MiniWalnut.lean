import MiniWalnut.Basic
import Mathlib.Computability.DFA

/-!

  # MiniWalnut

  This library implements the main operations needed to conduct the decision algorithm in
  Walnut. More information on the original Walnut software can be found
  [here](https://cs.uwaterloo.ca/~shallit/walnut.html).

  ## Automata

  Implements the necessary components to support base-2 operations in Walnut, as well as the
  complement and state renaming operations.

  ### Main Components

  - **Binary alphabet**: Custom type to implement base-2 input for automata
  - **Extended DFA structure**: DFA with fields necessary for the decision algorithm
  - **Basic Automata**: DFA implementing base-2 operations
  - **Automatic Sequence DFAO**: Thue-Morse sequence automaton
  - **DFA construction**: Functions initializing DFAs in their extended structure
  - **Operations**: Complement and state renaming

  ## Crossproduct

  This file implements cross product operations over DFAs, which is used
  to represent logical operators between two automata languages, and comparison operations for
  DFAOs representing automatic languages.

  ### Main Components

  - **Operation Types**: Logical and comparison operators
  - **Helper Functions**: Variable alignment and alphabet manipulation
  - **Cross Product Construction**: Building product automata from two DFAs

  ## Quantification Operations for DFAs

  This file implements existential (∃) and universal (∀) quantification over automata,
  which is fundamental for building first-order formulas in automata-based decision procedures.

  ### Main Components

  - **Quantification Operator Type**: Custom type implementing operators ∃ and ∀
  - **Reachability Analysis**: Finding states reachable with leading zeros
  - **Determinization**: Converting NFA to DFA
  - **Quantification Operations**: ∃ and ∀ operators over an automaton

  ## DFA Minimization

  This file implements DFA minimization using Hopcroft's algorithm, which is the
  most efficient algorithm for minimizing DFAs (O(n log n) where n is the number of states).

  ### Main Components

  - **Set Operations**: Helper functions for set difference and intersection
  - **Hopcroft's Algorithm**: Core minimization algorithm
  - **Unreachable State Removal**: BFS to find reachable states
-/
