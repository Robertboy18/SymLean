/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Numerics.PackedSlots

/-!
# Word trees as arrays

`Binary64WordTree.toList` lists the words of a tree from left to right, so that compiled code
that reads many words of a table can read them from an array.

## Main definitions

* `Binary64WordTree.toList`: the words of a tree, from left to right.

## Main results

* `Binary64WordTree.length_toList`: the word list of a tree of `n` words has length `n`.

## Implementation notes

Reading a word from the array of this list costs one array access, while
`Binary64WordTree.getNat` descends the tree, and a tree built by `ofPackedSlots` that is not
kept evaluated first recomputes the masked and shifted parts of its packed number at each call.
A computation that reads many words therefore lists the tree once, and `length_toList`, proved
by induction on the tree, lets a `Fin n` index address the array.
-/

@[expose] public section

namespace CAS.Numerics.Binary64WordTree

/-- The words of a tree, from left to right. -/
def toList {n : ℕ} : Binary64WordTree n → List ℕ
  | .empty => []
  | .singleton word => [word]
  | .append left right => left.toList ++ right.toList

/-- The word list of a tree of `n` words has length `n`. -/
theorem length_toList {n : ℕ} (t : Binary64WordTree n) : t.toList.length = n := by
  induction t with
  | empty => rfl
  | singleton word => rfl
  | append left right ihl ihr => simp [toList, ihl, ihr]

end CAS.Numerics.Binary64WordTree
