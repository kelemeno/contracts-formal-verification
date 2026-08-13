import Clear.ReasoningPrinciple
import specs.StateOk

import generated.L1Bridgehub.L1Bridgehub.Common.if_2328457584417225796
import generated.L1Bridgehub.L1Bridgehub.Common.if_2352170140006762975

import generated.L1Bridgehub.L1Bridgehub.Common.switch_8539157929318587848_gen


namespace L1Bridgehub.Common

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1Bridgehub.Common 

/-- **`EnumerableSet.add`, compiled** — what each branch RETURNS.

```
    case 0:  var := 0; leave                       -- already present: return false
    default: oldLen := sload(208)                  -- the set's array length
             reject oldLen ≥ 2^64                  -- Panic 65
             sstore(208, oldLen + 1)               -- length++
             reject ¬(oldLen < oldLen + 1)         -- Panic 50, the wrap check
             sstore(keccak(208) + oldLen, value)   -- array[oldLen] := value
             sstore(keccak(value ‖ 209), sload(208))  -- indexes[value] := new length
             var := 1; leave                       -- added: return true
```

This spec pins the CONTROL FLOW and the return value, and carries both guards in the
chain: whichever branch runs, the result is a `leave` state (`🚪`) — so this construct
returns from the enclosing function rather than falling through — carrying `var = 0` when
`_1` is zero and `var = 1` otherwise.

DELIBERATELY WEAKER THAN THE OTHER SPECS HERE: the default branch's store chain is stated
existentially rather than transcribed.  Its emitted form is a ~69k-line term (two
keccak-derived slots, four stores, each re-spelling every prefix state), and a transcription
that misses one `evm` source fails to typecheck with no useful diagnostic.  What is lost is
the ability to say WHERE the value landed; what is kept is that the array length is bounded
and wrap-checked before any write, and that the branch returns true.

The two writes are the two halves of an OpenZeppelin set — the array at slot 208 and the
1-based index mapping at slot 209 — and stating that relationship is the natural next step
for whoever needs `fun_registerNewZKChain_value_survives_fun_add` to depend on it. -/
def A_switch_8539157929318587848 (s₀ s₉ : State) : Prop :=
  let g1 := s₀⟦"oldLen" ↦ Clear.EVMState.sload s₀.evm 208⟧
  let gc1 := g1⟦"split_expr_2" ↦ (decide (g1["oldLen"]!! < 18446744073709551616)).toUInt256⟧
  ∃ s₁, Spec A_if_2328457584417225796 gc1 s₁ ∧
    (let inc := s₁⟦"_2" ↦ s₁["oldLen"]!! + 1⟧
     let st := inc🇪⟦Clear.EVMState.sstore s₁.evm 208 (inc["_2"]!!)⟧
     let gc2 := st⟦"split_expr_4" ↦ (decide (st["oldLen"]!! < (st["_2"]!!))).toUInt256⟧
     ∃ s₂, Spec A_if_2352170140006762975 gc2 s₂ ∧
       ((s₀["_1"]!! = 0 → s₉ = 🚪(s₀⟦"var" ↦ 0⟧)) ∧
        (s₀["_1"]!! ≠ 0 → ∃ t, s₉ = 🚪(t⟦"var" ↦ 1⟧))))

lemma switch_8539157929318587848_abs_of_concrete {s₀ s₉ : State} :
  Spec switch_8539157929318587848_concrete_of_code s₀ s₉ →
  Spec A_switch_8539157929318587848 s₀ s₉ := by
  unfold switch_8539157929318587848_concrete_of_code A_switch_8539157929318587848
  rcases s₀ with ⟨evm, store⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _hne hc
  obtain ⟨s₁, h₁, s₂, h₂, heq⟩ := hc
  refine ⟨s₁, h₁, s₂, h₂, ?_, ?_⟩
  · intro hg
    rw [← heq]
    simp [hg]
  · intro hg
    -- the witness is the default branch's state; let unification find it by matching
    -- `🚪(?t⟦"var" ↦ 1⟧)` against the branch term, rather than writing it out
    rw [if_neg (Ne.symm hg)] at heq
    exact ⟨_, heq.symm⟩

end

end L1Bridgehub.Common
