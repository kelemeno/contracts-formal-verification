import Clear.ReasoningPrinciple

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_2600721580863995212
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.panic_error_0x32
import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.Common.if_8420097433966466210

import generated.L2InteropCommitmentTree.L2InteropCommitmentTree.fun_root_gen


namespace generated.L2InteropCommitmentTree.L2InteropCommitmentTree

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities L2InteropCommitmentTree.Common generated.L2InteropCommitmentTree L2InteropCommitmentTree

def A_fun_root (var : Identifier)  (s₀ s₉ : State) : Prop := fun_root_concrete_of_code.1 var s₀ s₉

lemma fun_root_abs_of_concrete {s₀ s₉ : State} {var } :
  Spec (fun_root_concrete_of_code.1 var ) s₀ s₉ →
  Spec (A_fun_root var ) s₀ s₉ := by
  intro h
  simpa [A_fun_root] using h

end

end generated.L2InteropCommitmentTree.L2InteropCommitmentTree
