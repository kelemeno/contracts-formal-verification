import Clear.ReasoningPrinciple

import generated.L1AssetRouter.L1AssetRouter.Common.if_7928665324398554026
import generated.L1AssetRouter.L1AssetRouter.array_allocation_size_bytes
import generated.L1AssetRouter.L1AssetRouter.finalize_allocation
import generated.L1AssetRouter.L1AssetRouter.Common.if_5631566510356250141
import generated.L1AssetRouter.L1AssetRouter.mcopy

import generated.L1AssetRouter.L1AssetRouter.abi_decode_bytes_fromMemory_gen


namespace generated.L1AssetRouter.L1AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L1AssetRouter.Common generated.L1AssetRouter L1AssetRouter

def abi_decode_bytes_entry_state (s₀ : State) (offset end_clear_sanitised_hrafn : Literal) : State :=
  s₀☎️⟦["offset", "end_clear_sanitised_hrafn"], [offset, end_clear_sanitised_hrafn]⟧

def abi_decode_bytes_length_state (s : State) : State :=
  s⟦"length" ↦ EVMState.mload s.evm (s["offset"]!!)⟧

def abi_decode_bytes_mem_state (s : State) : State :=
  s⟦"memPtr" ↦ EVMState.mload s.evm 64⟧

def abi_decode_bytes_after_header_state (s : State) : State :=
  s🇪⟦s.evm.mstore (s["memPtr"]!!) (s["length"]!!)⟧

def abi_decode_bytes_callstate (s : State) : State :=
  let s := s⟦"split_expr_0" ↦ s["memPtr"]!! + 32⟧
  s⟦"split_expr_1" ↦ s["offset"]!! + 32⟧

def abi_decode_bytes_return_state (s₀ s_copy : State) (array : Identifier) : State :=
  let s := s_copy⟦"split_expr_2" ↦ s_copy["memPtr"]!! + (s_copy["length"]!!)⟧
  let s := s⟦"split_expr_3" ↦ s["split_expr_2"]!! + 32⟧
  let s := s🇪⟦s_copy.evm.mstore (s["split_expr_3"]!!) 0⟧
  let s := s⟦"array" ↦ s["memPtr"]!!⟧
  (🧟s)🏪⟦s₀⟧⟦array ↦ s["array"]!!⟧

def A_abi_decode_bytes_fromMemory (array : Identifier) (offset end_clear_sanitised_hrafn : Literal) (s₀ s₉ : State) : Prop :=
  ∃ ss_head,
    Spec
      A_if_7928665324398554026
      (abi_decode_bytes_entry_state s₀ offset end_clear_sanitised_hrafn)
      ss_head ∧
    ∃ s_alloc,
      Spec
        (A_array_allocation_size_bytes "_1" ((abi_decode_bytes_length_state ss_head)["length"]!!))
        (abi_decode_bytes_length_state ss_head)
        s_alloc ∧
      ∃ s_finalize,
        Spec
          (A_finalize_allocation
            ((abi_decode_bytes_mem_state s_alloc)["memPtr"]!!)
            ((abi_decode_bytes_mem_state s_alloc)["_1"]!!))
          (abi_decode_bytes_mem_state s_alloc)
          s_finalize ∧
        ∃ ss_tail,
          Spec
            A_if_5631566510356250141
            (abi_decode_bytes_after_header_state s_finalize)
            ss_tail ∧
          ∃ s_copy,
            Spec
              (A_mcopy
                ((abi_decode_bytes_callstate ss_tail)["split_expr_0"]!!)
                ((abi_decode_bytes_callstate ss_tail)["split_expr_1"]!!)
                ((abi_decode_bytes_callstate ss_tail)["length"]!!))
              (abi_decode_bytes_callstate ss_tail)
              s_copy ∧
            abi_decode_bytes_return_state s₀ s_copy array = s₉

set_option maxHeartbeats 1200000 in
lemma abi_decode_bytes_fromMemory_abs_of_concrete {s₀ s₉ : State} {array offset end_clear_sanitised_hrafn} :
  Spec (abi_decode_bytes_fromMemory_concrete_of_code.1 array offset end_clear_sanitised_hrafn) s₀ s₉ →
  Spec (A_abi_decode_bytes_fromMemory array offset end_clear_sanitised_hrafn) s₀ s₉ := by
  unfold abi_decode_bytes_fromMemory_concrete_of_code A_abi_decode_bytes_fromMemory
  rcases s₀ with ⟨evm, varstore⟩ | _ | _ <;> [skip; aesop_spec; aesop_spec]
  apply spec_eq
  intro _ hconcrete
  clr_funargs at hconcrete
  simpa [
    abi_decode_bytes_entry_state, abi_decode_bytes_length_state, abi_decode_bytes_mem_state,
    abi_decode_bytes_after_header_state, abi_decode_bytes_callstate, abi_decode_bytes_return_state
  ] using hconcrete

end

end generated.L1AssetRouter.L1AssetRouter
