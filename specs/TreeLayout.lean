import Clear.ReasoningPrinciple
import specs.KeccakDeterminism
import specs.FoldIndexBridge

/-! # The tree's storage layout: level arrays are big enough

Everything else the fold needs is proved. This file supplies the one fact that is about the
tree's REPRESENTATION rather than its code: at every level, the level array is longer than
the largest node index at that level.

`FullMerkle` stores `bytes32[][] _nodes`. Solidity lays that out as

    _nodes.length            at  S
    _nodes[i].length         at  keccak(S) + i
    _nodes[i][j]             at  keccak(keccak(S) + i) + j

and the compiled accessor computes exactly the middle line: `mstore(0, S); keccak256(0, 32)`
then `+ i`, which is why the predicate below is phrased with `keccakOut`. It is the same
expression `storage_array_index_access_..._val` produces, so it composes directly with it.

**This is an ASSUMPTION about the tree, not a theorem about the fold.** `pushNewLeaf`
maintains it — it pushes onto `_nodes[i]` exactly when level `i`'s max node number grows,
which `scripts/check-source-invariants.sh` pins — but that has NOT been proved here. Until
it is, results using `LevelsSized` are conditional, and honestly so: the fold cannot
establish it because the fold never grows an array.

What it buys: `hlt`, the accessor's bounds hypothesis, at every level of the fold. The
arithmetic half (`index ≤ maxNodeNumber`, halved together) is already proved from the
contract's own guard — see SECURITY_VERIFICATION.md Part H.
-/

namespace Clear.TreeLayout

open Clear Clear.KeccakDeterminism

/-- **LEVEL ARRAYS ARE BIG ENOUGH.**  At every level `i` below the tree's height, the array
`_nodes[i]` is longer than that level's largest node index, `maxNode / 2 ^ i`.

The slot read is the one the compiled accessor computes for `_nodes[i]`'s length. -/
def LevelsSized (σ : EVMState) (nodesSlot maxNode height : UInt256) : Prop :=
  ∀ i : ℕ, i < height.val →
    maxNode.val / 2 ^ i
      < (EVMState.sload σ ((keccakOut (σ.mstore 0 nodesSlot) 0 32).1 + (i : UInt256))).val

/-- **THE ACCESSOR'S BOUNDS HYPOTHESIS, at any level.**

`hlt` for the level-`i` array follows from the layout assumption plus the fold's own
arithmetic: the index at level `i` is at most `maxNode / 2 ^ i`, which is what
`ABody_..._index_le_max` and `FoldIndexBridge.idxAt_val` give (both halve together, and
`idxAt` at level `i` has value `idx / 2 ^ i`). -/
theorem hlt_of_levelsSized {σ : EVMState} {nodesSlot maxNode height : UInt256} {i : ℕ}
    {idx : UInt256}
    (h : LevelsSized σ nodesSlot maxNode height) (hi : i < height.val)
    (hidx : idx.val ≤ maxNode.val / 2 ^ i) :
    idx < EVMState.sload σ ((keccakOut (σ.mstore 0 nodesSlot) 0 32).1 + (i : UInt256)) := by
  have hv := h i hi
  simp only [Fin.lt_def]
  exact lt_of_le_of_lt hidx hv

/-- The fold's index at level `i` is within its level's bound, given the entry guard's
`index ≤ maxNode`.  `idxAt` and `/ 2 ^ i` are identified by `FoldIndexBridge.idxAt_val`. -/
theorem idxAt_le_maxAt {idx maxNode : UInt256} (h : idx.val ≤ maxNode.val) (i : ℕ) :
    (Clear.FoldRightPeel.idxAt idx i).val ≤ maxNode.val / 2 ^ i := by
  rw [Clear.FoldIndexBridge.idxAt_val]
  exact Nat.div_le_div_right h

end Clear.TreeLayout
