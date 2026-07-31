import Clear.ReasoningPrinciple

import generated.InteropHandler.InteropHandler.Common.block_2731350847861160598
import generated.InteropHandler.InteropHandler.Common.block_6357692007766190094
import generated.InteropHandler.InteropHandler.Common.block_2808946740468959641
import generated.InteropHandler.InteropHandler.Common.if_4527419366897270229
import generated.InteropHandler.InteropHandler.Common.block_8261716617869206867
import generated.InteropHandler.InteropHandler.Common.block_3486721318462544172
import generated.InteropHandler.InteropHandler.mcopy
import generated.InteropHandler.InteropHandler.Common.block_5291704544479297361
import generated.InteropHandler.InteropHandler.Common.block_795419607175387125
import generated.InteropHandler.InteropHandler.finalize_allocation
import generated.InteropHandler.InteropHandler.Common.block_2448294379448399750
import generated.InteropHandler.InteropHandler.Common.block_7302561134372012767
import generated.InteropHandler.InteropHandler.Common.block_5575682281217382298
import generated.InteropHandler.InteropHandler.Common.block_9222930811073581434
import generated.InteropHandler.InteropHandler.Common.block_1831590622027002072
import generated.InteropHandler.InteropHandler.abi_encode_struct_L2Message
import generated.InteropHandler.InteropHandler.Common.block_967087758813847086
import generated.InteropHandler.InteropHandler.Common.block_6981637902326639646
import generated.InteropHandler.InteropHandler.abi_encode_array_bytes32_dyn
import generated.InteropHandler.InteropHandler.Common.if_4897189129566826754
import generated.InteropHandler.InteropHandler.Common.if_4387370399091499927
import generated.InteropHandler.InteropHandler.abi_decode_bool_fromMemory
import generated.InteropHandler.InteropHandler.Common.if_7459957530221088163
import generated.InteropHandler.InteropHandler.Common.block_8249276522053995858
import generated.InteropHandler.InteropHandler.Common.block_4779748611206726122
import generated.InteropHandler.InteropHandler.Common.block_3157764704621451027

import generated.InteropHandler.InteropHandler.fun_verifyBundle_gen

import specs.KeccakDeterminism
import specs.L2InteropCommitmentTree.L2InteropCommitmentTree.imt_leaf_storage_user

/-
  THE BUNDLE-VERIFICATION GATE — `InteropHandlerBase._verifyBundle`.

  Solidity (era-contracts, `InteropHandlerBase.sol:296`):

      require(_proof.message.sender == L2_INTEROP_CENTER_ADDR, UnauthorizedMessageSender(..));
      _proof.message.data = bytes.concat(BUNDLE_IDENTIFIER, _bundle);
      require(_proveInclusion(_proof), MessageNotIncluded());
      bundleStatus[_bundleHash] = BundleStatus.Verified;
      emit BundleVerified(_bundleHash);

  This is THE authentication point of the interop delivery pipeline: a bundle
  becomes `Verified` (hence executable) only here.  The compiled Yul is, in
  order:

    block_2731350847861160598  sum := 0x1000D (= L2_INTEROP_CENTER_ADDR); _2 := proof + 96
    block_6357692007766190094  split_expr_2 := mload(mload(_2) + 32)   -- message.sender
    block_2808946740468959641  cleaned := sender & (2^160-1); split_expr_5 := eq(cleaned, sum)
    if_4527419366897270229     if iszero(split_expr_5) { revert UnauthorizedMessageSender }
    …                          message.data := 0x01 ‖ bundle; staticcall 0x10009 (_proveInclusion)
    if_7459957530221088163     if iszero(expr) { revert MessageNotIncluded }
    block_8249276522053995858  dataSlot := keccak256(bundleHash ‖ 1)
    block_4779748611206726122  sstore(dataSlot, (sload(dataSlot) &~ 255) | 1)   -- Verified
    block_3157764704621451027  log2(…, BundleVerified, bundleHash)

  WHAT IS PROVED HERE (axiom-free, verbatim over the generated block ASTs):

  * `unauthorized_sender_reverts` — if the 160-bit-masked `_proof.message.sender`
    read out of memory is NOT `L2_INTEROP_CENTER_ADDR` (`0x1000D = 65549`), the
    prologue + gate ends with `reverted = true`.  No bundle can be marked
    verified on a message sent by any other L2 contract: forging an interop
    delivery requires impersonating the canonical interop center.
  * `not_included_reverts` — if the decoded answer of the message-inclusion
    staticcall (`expr`) is `0`, the second gate reverts.  A bundle is never
    verified without a positive answer from the message verifier.
  * `verify_slot_block` / `verify_write_block` — closed forms of the two
    state-writing blocks: the touched slot is exactly one `accOut` step at
    `(bundleHash, 1)`, i.e. `keccak256(bundleHash ‖ 1)` = the `bundleStatus`
    mapping slot, and the stored word is `(old &~ 255) | 1`.
  * `fin_mask_one` / `verified_status_reads_one` — the written word's low byte is
    exactly `1 = BundleStatus.Verified`, so the readback performed by
    `fun_getBundleData` (`and(sload(slot), 0xff)`) returns `Verified`.

  HONEST SCOPE NOTE — the bridge lemma `fun_verifyBundle_abs_of_concrete` is
  still `sorry`, and it is NOT provable in the current tree: every one of the 21
  sub-block abstractions this function is compiled through
  (`specs/InteropHandler/InteropHandler/Common/*_user.lean`) still defines its
  `A_block_… := sorry`, so `fun_verifyBundle_concrete_of_code.1` is a chain of
  opaque propositions from which nothing about `s₉` can be derived.  The
  theorems above are therefore stated and proved DIRECTLY over the generated
  block ASTs, which is where the security content of this function lives.
  `A_fun_verifyBundle` states, relationally on `(s₀, s₉)`, exactly the two facts
  proved above (sender gate + status write); closing the bridge lemma requires
  the sub-block layer to be given real specs first.
-/

namespace generated.InteropHandler.InteropHandler

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities InteropHandler.Common generated.InteropHandler InteropHandler
open Clear.KeccakDeterminism

set_option maxRecDepth 4000
set_option maxHeartbeats 4000000
set_option linter.dupNamespace false

/-! ### Local state-plumbing helpers -/

@[simp] private lemma insert_Ok {evm : EVMState} {store : VarStore} {var : Identifier} {val : Literal} :
    (Ok evm store)⟦var ↦ val⟧ = Ok evm (store.insert var val) := rfl

private lemma evm_Ok {e : EVMState} {σ : VarStore} : (Ok e σ).evm = e := rfl

private lemma setEvm_Ok {e E : EVMState} {σ : VarStore} :
    (Ok e σ).setEvm E = Ok E σ := rfl

private lemma lookup_insert_ne_fin {evm : EVMState} {σ : VarStore}
    {k k' : Identifier} {val : Literal} (h : k' ≠ k) :
    (Ok evm (Finmap.insert k val σ))[k']!! = (Ok evm σ)[k']!! := by
  rw [← insert_Ok]; exact lookup_insert_of_ne h

private lemma lookup_insert_self_fin {evm : EVMState} {σ : VarStore}
    {k : Identifier} {val : Literal} :
    (Ok evm (Finmap.insert k val σ))[k]!! = val := by
  rw [← insert_Ok]; exact lookup_insert' (by trivial)

private lemma primCall_keccakOut {s : State} {a b : Literal} :
    primCall s .Keccak256 [a, b]
      = (s.setEvm (keccakOut s.evm a b).2, [(keccakOut s.evm a b).1]) := by
  rw [EVMKeccak256']
  unfold keccakOut
  rcases hk : s.evm.keccak256 a b with _ | pr
  · simp only [hk]
  · simp only [hk]

/-! ### Gate 1 — the message sender must be the canonical interop center -/

/-- Closed form of the constant/pointer prologue: `sum := 0x1000D`
(`L2_INTEROP_CENTER_ADDR`) and `_2 := proof + 96` (`&_proof.message`). -/
private lemma vb_block1
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {P : Literal}
    (hP : (Ok evm store)["var_proof_mpos"]!! = P) :
    exec (fuel+1) block_2731350847861160598 (Ok evm store)
      = Ok evm (((((store.insert "sum" 0).insert "sum" 65549).insert
          "_1" 0).insert "_1" 0).insert "_2" (P + 96)) := by
  unfold block_2731350847861160598
  simp only [cons, nil]
  simp only [LetEq', Assign', LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', eval, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMAdd', multifill_cons, multifill_nil, insert_Ok]
  rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
      lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide), hP]

/-- Closed form of the sender read: `split_expr_2 := mload(mload(_2) + 32)` is
`_proof.message.sender`; `split_expr_4` is the 160-bit address mask. -/
private lemma vb_block2
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {p2 : Literal}
    (h2 : (Ok evm store)["_2"]!! = p2) :
    exec (fuel+1) block_6357692007766190094 (Ok evm store)
      = Ok evm (((((store.insert "split_expr_0" (evm.mload p2)).insert
          "split_expr_1" (evm.mload p2 + 32)).insert
          "split_expr_2" (evm.mload (evm.mload p2 + 32))).insert
          "split_expr_3" (Fin.shiftLeft 1 160)).insert
          "split_expr_4" (Fin.shiftLeft 1 160 - 1)) := by
  unfold block_6357692007766190094
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMload', EVMAdd', EVMShl', EVMSub',
             multifill_cons, multifill_nil, insert_Ok, evm_Ok]
  rw [h2]
  simp only [lookup_insert_self_fin, evm_Ok]
  try rw [lookup_insert_ne_fin (by decide)]
  try simp only [lookup_insert_self_fin]

/-- Closed form of the comparison: `split_expr_5 = 1` iff the masked sender
equals `sum`. -/
private lemma vb_block3
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {snd mask sumv : Literal}
    (hs : (Ok evm store)["split_expr_2"]!! = snd)
    (hm : (Ok evm store)["split_expr_4"]!! = mask)
    (hsum : (Ok evm store)["sum"]!! = sumv) :
    exec (fuel+1) block_2808946740468959641 (Ok evm store)
      = Ok evm ((store.insert "cleaned" (Fin.land snd mask)).insert
          "split_expr_5" (fromBool (Fin.land snd mask = sumv))) := by
  unfold block_2808946740468959641
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMAnd', EVMEq', multifill_cons, multifill_nil, insert_Ok]
  rw [hm, hs]
  rw [lookup_insert_self_fin, lookup_insert_ne_fin (by decide), hsum]

/-- **THE SENDER GATE REVERTS.**  `if iszero(split_expr_5) { revert }`: when the
comparison against `L2_INTEROP_CENTER_ADDR` failed, the block reverts. -/
lemma sender_gate_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (h : (Ok evm store)["split_expr_5"]!! = 0) :
    (exec (fuel+1) if_4527419366897270229 (Ok evm store)).evm.reverted = true := by
  unfold if_4527419366897270229
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [h]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  simp only [List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- let split_expr_6 := shl(225, 1157535291)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- mstore(0, split_expr_6)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  -- mstore(4, sum)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  -- mstore(36, cleaned)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  -- revert(0, 68)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rfl

/-- **NO VERIFICATION ON A FOREIGN MESSAGE SENDER.**  Running the compiled
prologue of `_verifyBundle` — the constant/pointer setup, the
`_proof.message.sender` read, the 160-bit mask-and-compare and the guard-if —
from any state whose proof struct carries a sender other than
`L2_INTEROP_CENTER_ADDR (= 0x1000D = 65549)` ends with `reverted = true`.

Contrapositive: a bundle can only ever reach the `Verified` write below on a
message whose sender field is the canonical interop center — the sole
authentication of a cross-chain bundle. -/
theorem unauthorized_sender_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {s₉ : State} {P : Literal}
    (hP : (Ok evm store)["var_proof_mpos"]!! = P)
    (hbad : Fin.land (evm.mload (evm.mload (P + 96) + 32))
              (Fin.shiftLeft (1 : UInt256) 160 - 1) ≠ 65549)
    (hexec : exec (fuel+1) (.Block
        [block_2731350847861160598, block_6357692007766190094,
         block_2808946740468959641, if_4527419366897270229]) (Ok evm store) = s₉) :
    s₉.evm.reverted = true := by
  rw [← hexec]
  rw [cons, vb_block1 hP]
  rw [cons, vb_block2 (p2 := P + 96) (by exact lookup_insert_self_fin)]
  rw [cons, vb_block3
      (snd := evm.mload (evm.mload (P + 96) + 32))
      (mask := Fin.shiftLeft 1 160 - 1)
      (sumv := 65549)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact lookup_insert_self_fin)
      (by exact lookup_insert_self_fin)
      (by rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
              lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
          exact lookup_insert_self_fin)]
  rw [cons, nil]
  refine sender_gate_reverts ?_
  rw [lookup_insert_self_fin]
  rw [show fromBool (Fin.land (evm.mload (evm.mload (P + 96) + 32))
      (Fin.shiftLeft (1 : UInt256) 160 - 1) = 65549) = (0 : UInt256) from by
    rw [decide_eq_false hbad]; rfl]

/-! ### Gate 2 — the message must actually be included -/

/-- **NO VERIFICATION WITHOUT INCLUSION.**  `if iszero(expr) { revert }`: when
the decoded answer of the `_proveInclusion` staticcall to the message verifier
is `0`, the gate reverts (`MessageNotIncluded`).  Together with the sender gate
these are the only two acceptance conditions of `_verifyBundle`. -/
theorem not_included_reverts
    {evm : EVMState} {store : VarStore} {fuel : ℕ}
    (h : (Ok evm store)["expr"]!! = 0) :
    (exec (fuel+1) if_7459957530221088163 (Ok evm store)).evm.reverted = true := by
  unfold if_7459957530221088163
  rw [If']
  simp only [evalArgs, evalTail, cons', head', reverse',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, EVMIszero']
  rw [h]
  rw [show fromBool ((0 : UInt256) = 0) = (1 : UInt256) from by decide]
  simp only [List.head!]
  rw [if_pos (by decide : ((1 : UInt256)) ≠ 0)]
  -- let split_expr_38 := shl(225, 425816235)
  rw [cons, LetPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMShl',
             insert_Ok]
  -- mstore(0, split_expr_38)
  rw [cons, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMMstore',
             evm_Ok, setEvm_Ok]
  -- revert(0, 4)
  rw [cons, nil, ExprStmtPrimCall']
  simp only [evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, multifill_cons, multifill_nil, EVMRevert',
             evm_Ok, setEvm_Ok]
  rfl

/-! ### The state effect — `bundleStatus[bundleHash] := Verified` -/

/-- **Slot block closed form**: the written slot is one `accOut` step at
`(bundleHash, 1)`, i.e. `keccak256(bundleHash ‖ 1)` — the `bundleStatus`
mapping slot (mapping base `1`). -/
lemma verify_slot_block
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {bh : Literal}
    (hbh : (Ok evm store)["var__bundleHash"]!! = bh) :
    exec (fuel+1) block_8249276522053995858 (Ok evm store)
      = Ok (accOut evm bh 1).2
          (((store.insert "dataSlot" (accOut evm bh 1).1).insert
              "cleaned_1" 0).insert "cleaned_1" 0) := by
  unfold block_8249276522053995858
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall', LetEq', Assign',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', eval, execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMMstore']
  simp only [multifill_cons, multifill_nil]
  rw [hbh]
  simp only [evm_insert, evm_Ok, setEvm_Ok, insert_Ok]
  rw [primCall_keccakOut]
  simp only [multifill_cons, multifill_nil, evm_Ok, setEvm_Ok, insert_Ok]
  have halign : keccakOut ((evm.mstore 0 bh).mstore 32 1) 0 64 = accOut evm bh 1 := by
    unfold accOut
    rfl
  try rw [halign]
  try simp only [halign]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]

/-- **Write block closed form**: the status write stores `(old &~ 255) | 1` at
the status slot — `BundleStatus.Verified` in the low byte, every other bit of
the word (and every other slot) untouched. -/
lemma verify_write_block
    {evm : EVMState} {store : VarStore} {fuel : ℕ} {d : Literal}
    (hd : (Ok evm store)["dataSlot"]!! = d) :
    exec (fuel+1) block_4779748611206726122 (Ok evm store)
      = Ok (evm.sstore d (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 1))
          ((((store.insert "split_expr_39" (evm.sload d)).insert
              "split_expr_40" (Clear.UInt256.lnot 255)).insert
              "split_expr_41" (Fin.land (evm.sload d) (Clear.UInt256.lnot 255))).insert
              "split_expr_42" (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 1)) := by
  unfold block_4779748611206726122
  simp only [cons, nil]
  simp only [LetPrimCall', AssignPrimCall', ExprStmtPrimCall',
             evalArgs, evalTail, cons', head', reverse', multifill',
             PrimCall', Lit', Var', execPrimCall, evalPrimCall,
             List.reverse_cons, List.reverse_nil, List.nil_append,
             List.singleton_append, List.append_assoc, List.cons_append,
             EVMSload', EVMNot', EVMAnd', EVMOr', EVMSstore']
  simp only [multifill_cons, multifill_nil]
  rw [hd]
  simp only [evm_insert, evm_Ok, setEvm_Ok, insert_Ok]
  simp only [lookup_insert_self_fin]
  have n1 : (Ok evm (Finmap.insert "split_expr_40" (Clear.UInt256.lnot 255)
      (Finmap.insert "split_expr_39" (evm.sload d) store)))["split_expr_39"]!!
      = evm.sload d := by
    rw [lookup_insert_ne_fin (by decide)]
    exact lookup_insert_self_fin
  simp only [n1]
  try simp only [lookup_insert_self_fin]
  have n2 : (Ok evm (Finmap.insert "split_expr_42"
      (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 1)
      (Finmap.insert "split_expr_41" (Fin.land (evm.sload d) (Clear.UInt256.lnot 255))
        (Finmap.insert "split_expr_40" (Clear.UInt256.lnot 255)
          (Finmap.insert "split_expr_39" (evm.sload d) store)))))["dataSlot"]!! = d := by
    rw [lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide),
        lookup_insert_ne_fin (by decide), lookup_insert_ne_fin (by decide)]
    exact hd
  simp only [n2]
  try simp only [lookup_insert_self_fin]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]
  try simp only [insert_Ok, setEvm_Ok, evm_Ok]

/-! ### The low-byte mask: the stored status is exactly `Verified = 1` -/

private lemma low_bit_zero (n i : ℕ) (hi : i < 8) (h : n % 256 = 0) : n.testBit i = false := by
  rw [Nat.testBit_to_div_mod]
  have h256 : (256:ℕ) = 2^8 := by norm_num
  have hdvd : 2^(i+1) ∣ n := by
    have : (2:ℕ)^8 ∣ n := by rw [← h256]; exact Nat.dvd_of_mod_eq_zero h
    exact dvd_trans (pow_dvd_pow 2 (by omega)) this
  obtain ⟨k, rfl⟩ := hdvd
  have hpi : (0:ℕ) < 2^i := Nat.pos_pow_of_pos i (by norm_num)
  have : 2^(i+1) * k / 2^i = 2 * k := by
    rw [pow_succ]
    calc 2^i * 2 * k / 2^i = 2^i * (2*k) / 2^i := by ring_nf
    _ = 2*k := Nat.mul_div_cancel_left _ hpi
  rw [this]; simp [Nat.mul_mod_right]

private lemma tb255_lt (i : ℕ) (hge : 8 ≤ i) : (255:ℕ).testBit i = false :=
  Nat.testBit_lt_two_pow (by calc (255:ℕ) < 2^8 := by norm_num
    _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hge)

/-- **Pure low-byte lemma.** The written status word `(x &~ 255) | 1` has low
byte exactly `1 = BundleStatus.Verified`. -/
theorem fin_mask_one (x : UInt256) :
    Fin.land (Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 1) 255 = 1 := by
  apply Fin.ext
  rcases x with ⟨a, _⟩
  show Nat.land (Nat.lor (Nat.land a (UInt256.size - 256) % UInt256.size) 1 % UInt256.size) 255 % UInt256.size = 1
  have hsz : UInt256.size = 2^256 := by norm_num
  rw [hsz]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have key : ∀ z : ℕ, (z % 2^256).testBit i = z.testBit i := fun z => by
      rw [Nat.testBit_mod_two_pow]; simp [show i < 256 by omega]
    rw [key]
    show ((Nat.lor (Nat.land a (2^256 - 256) % 2^256) 1 % 2^256) &&& 255).testBit i = (1:ℕ).testBit i
    rw [show ∀ p q : ℕ, Nat.land p q = p &&& q from fun _ _ => rfl,
        show ∀ p q : ℕ, Nat.lor p q = p ||| q from fun _ _ => rfl]
    rw [Nat.testBit_land]
    rw [key ((a &&& (2^256 - 256)) % 2^256 ||| 1)]
    rw [Nat.testBit_lor]
    rw [key (a &&& (2^256 - 256))]
    rw [Nat.testBit_land]
    have hbmask : (2^256 - 256 : ℕ).testBit i = false := by
      apply low_bit_zero _ i hi; decide
    rw [hbmask, Bool.and_false, Bool.false_or, Bool.and_comm]
    have hb255 : (255:ℕ).testBit i = true := by interval_cases i <;> rfl
    rw [hb255, Bool.true_and]
  · have hge : 8 ≤ i := by omega
    have key : (Nat.land (Nat.lor (Nat.land a (2^256-256) % 2^256) 1 % 2^256) 255 % 2^256).testBit i = false := by
      rw [Nat.testBit_mod_two_pow]
      by_cases hi256 : i < 256
      · simp only [hi256, decide_True, Bool.true_and]
        show ((Nat.lor (Nat.land a (2^256-256) % 2^256) 1 % 2^256) &&& 255).testBit i = false
        rw [Nat.testBit_land, tb255_lt i hge, Bool.and_false]
      · simp [hi256]
    rw [key]
    have hb1 : (1:ℕ).testBit i = false :=
      Nat.testBit_lt_two_pow (by calc (1:ℕ) < 2^8 := by norm_num
        _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hge)
    rw [hb1]

/-- The written status word is nonzero (its low byte is `1`). -/
theorem fin_mask_one_ne_zero (x : UInt256) :
    Fin.lor (Fin.land x (Clear.UInt256.lnot 255)) 1 ≠ 0 := by
  intro h
  have := fin_mask_one x
  rw [h] at this
  simp only [Fin.land] at this
  exact absurd this (by decide)

/-- **THE BUNDLE READS BACK AS `Verified`.**  After `_verifyBundle`'s status
write, re-reading the status slot the way `fun_getBundleData` does —
`and(sload(slot), 0xff)` — returns exactly `1 = BundleStatus.Verified`.  So the
gate's only state effect is to move this one bundle from `Unreceived` to
`Verified`, which is precisely what `executeBundle` then accepts. -/
theorem verified_status_reads_one
    {evm : EVMState} {d : UInt256}
    (hacc : (evm.lookupAccount evm.execution_env.code_owner).isSome) :
    Fin.land
      ((evm.sstore d (Fin.lor (Fin.land (evm.sload d) (Clear.UInt256.lnot 255)) 1)).sload d)
      255 = 1 := by
  rw [generated.L2InteropCommitmentTree.L2InteropCommitmentTree.sload_sstore_self hacc]
  exact fin_mask_one (evm.sload d)

/-! ### The abstract specification -/

/-- Abstract spec of `_verifyBundle`, stated relationally on the entry state
`s₀` and the exit state `s₉` as the conjunction of its two security-relevant
facts (both proved above over the compiled blocks):

1. **Sender gate.** A non-reverting run forces the 160-bit-masked
   `_proof.message.sender` — read at `mload(mload(proof + 96) + 32)` in the
   entry memory — to be `L2_INTEROP_CENTER_ADDR = 0x1000D = 65549`
   (`unauthorized_sender_reverts` is the contrapositive).

2. **Status write.** A non-reverting run leaves the `bundleStatus` slot of
   `var__bundleHash` — `keccak256(bundleHash ‖ 1)`, one `accOut` step — holding
   a word whose low byte is `1 = BundleStatus.Verified`
   (`verify_slot_block` + `verify_write_block` + `verified_status_reads_one`).

NOT captured here: the `MessageNotIncluded` gate (`not_included_reverts` proves
it separately, but the staticcall answer is not a function of `s₀`/`s₉` alone),
the `message.data := 0x01 ‖ _bundle` substitution that binds the checked message
to *this* bundle, and a frame condition saying no other storage slot moves. -/
def A_fun_verifyBundle (_var_bundle_mpos var_proof_mpos var__bundleHash : Literal) (s₀ s₉ : State) : Prop :=
  (¬ s₉.evm.reverted →
      Fin.land (s₀.evm.mload (s₀.evm.mload (var_proof_mpos + 96) + 32))
        (Fin.shiftLeft (1 : UInt256) 160 - 1) = 65549)
  ∧ (¬ s₉.evm.reverted →
      Fin.land (s₉.evm.sload (accOut s₉.evm var__bundleHash 1).1) 255 = 1)

/-- NOT PROVED — `sorry`.  See the scope note in the file header: all 21
sub-block abstractions of this function are still `A_block_… := sorry`, so the
hypothesis `Spec (fun_verifyBundle_concrete_of_code.1 …) s₀ s₉` is a chain of
opaque propositions carrying no information about `s₉`.  Both conjuncts of
`A_fun_verifyBundle` are proved above directly over the generated block ASTs
(`unauthorized_sender_reverts`; `verify_slot_block` / `verify_write_block` /
`verified_status_reads_one`); wiring them through this bridge requires real
specs at the sub-block layer first. -/
lemma fun_verifyBundle_abs_of_concrete {s₀ s₉ : State} { var_bundle_mpos var_proof_mpos var__bundleHash} :
  Spec (fun_verifyBundle_concrete_of_code.1  var_bundle_mpos var_proof_mpos var__bundleHash) s₀ s₉ →
  Spec (A_fun_verifyBundle  var_bundle_mpos var_proof_mpos var__bundleHash) s₀ s₉ := by
  unfold fun_verifyBundle_concrete_of_code A_fun_verifyBundle
  sorry

end

end generated.InteropHandler.InteropHandler
