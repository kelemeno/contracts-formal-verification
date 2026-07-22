-- Hand-written A3-admitted module for L2AssetRouter (mcopy, EIP-5656).
-- generated/ is gitignored: after regenerating VCs, copy this file to
-- generated/L2AssetRouter/L2AssetRouter/mcopy.lean
import Clear.ReasoningPrinciple
import Clear.JumpLemmas


namespace generated.L2AssetRouter.L2AssetRouter

section

open Clear EVMState Ast Expr Stmt FunctionDefinition State Interpreter ExecLemmas OutOfFuelLemmas JumpLemmas Abstraction YulNotation PrimOps ReasoningPrinciple Utilities generated.L2AssetRouter L2AssetRouter

def mcopy : FunctionDefinition := <f
    function mcopy(dst, src, len) ->

{
}

>

def A_mcopy (dst src len : Literal) (s₀ s₉ : State) : Prop := True

lemma mcopy_abs_of_code {s₀ s₉ : State} {dst src len} {fuel : Nat} :
  execCall fuel mcopy [] (s₀, [dst, src, len]) = s₉ →
  Spec (A_mcopy dst src len) s₀ s₉ := by
  intro h
  rcases s₀ with ⟨evm, store⟩ | _ | c <;> unfold Spec A_mcopy
  · intro _
    trivial
  · simpa [h] using
      (execCall_Inf (fuel := fuel) (fdef := mcopy) (vars := [])
        (inputs := (OutOfFuel, [dst, src, len])) (by simp))
  · simpa [h] using
      (execCall_Jump (fuel := fuel) (fdef := mcopy) (vars := [])
        (inputs := (Checkpoint c, [dst, src, len])) (by simp))

end

end generated.L2AssetRouter.L2AssetRouter
