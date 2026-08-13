import Clear.ReasoningPrinciple

/-! # `isOk` for a revived function return

Every compiled Yul function ends by reviving its callee state and restoring the
caller's store:

    🧟 ss 🏪⟦s₀⟧ ⟦out₁ ↦ …⟧ ⟦out₂ ↦ …⟧ = s₉

To show such an `s₉` is `Ok`, the tempting route is to walk the callee's `Spec`
chain and case each intermediate as `Ok` / `OutOfFuel` / `Checkpoint`.  That is
unnecessary.  `reviveJump` maps `Checkpoint c` to `revive c`, which is `Ok` for
every jump kind, and is the identity elsewhere — so the ONLY way the result fails
to be `Ok` is `ss = OutOfFuel`, and that is excluded by the `¬ ❓ s₉` hypothesis
the caller already has (it propagates backwards through insert / setStore /
reviveJump).

So the whole obligation reduces to `isOk_reviveJump_of_not_isOutOfFuel` below,
independent of how many blocks the function body has.
-/

namespace Clear

section

open Clear EVMState State Abstraction

/-- A state that is not out of fuel revives to an `Ok` state.  `Ok` revives to
itself, `Checkpoint c` revives to `revive c` which is `Ok` in all three jump
cases, and `OutOfFuel` is excluded by hypothesis. -/
lemma isOk_reviveJump_of_not_isOutOfFuel {s : State} (h : ¬ ❓ s) : isOk (🧟 s) := by
  rcases s with ⟨evm, store⟩ | _ | c
  · simp [isOk, State.reviveJump]
  · exact absurd (by simp [State.isOutOfFuel]) h
  · rcases c <;> simp [isOk, State.reviveJump, State.revive]

/-- `Spec` propagates out-of-fuel FORWARD: its `OutOfFuel` branch is literally `❓ s₁`.

This is what lets a block's `isOk` proof refute a bad intermediate instead of
reasoning about it.  Walking a chain `s₀ → s₁ → … → s₉`, an intermediate that is
out of fuel forces every later state out of fuel, contradicting the `¬ ❓ s₉` the
caller supplies — so each intermediate can be assumed `Ok` without a case split
on it.  (`Checkpoint` intermediates cannot arise after a function call, since a
call's result is `🧟`-shaped and `reviveJump` never returns a `Checkpoint`.) -/
lemma isOutOfFuel_of_Spec_of_isOutOfFuel {P : State → State → Prop} {a b : State}
    (h : Spec P a b) (ha : ❓ a) : ❓ b := by
  rcases a with ⟨evm, store⟩ | _ | c
  · exact absurd ha (by simp [State.isOutOfFuel])
  · exact h
  · exact absurd ha (by simp [State.isOutOfFuel])

/-- A variable lookup ignores `setEvm`: the varstore is untouched.  Clear has no
such lemma, and without it a lookup sitting under the `mstore`s that a keccak
accessor emits cannot be reduced. -/
lemma lookup_setEvm {s : State} {e : EVM} {v : Ast.Identifier} (h : isOk s) :
    (s🇪⟦e⟧)[v]!! = s[v]!! := by
  rcases s with ⟨evm, store⟩ | _ | _
  · rfl
  · exact absurd h (by simp [isOk])
  · exact absurd h (by simp [isOk])

/-- `Spec` propagates a `Checkpoint` FORWARD unchanged: its `Checkpoint c` branch is
literally `s₁.isJump c`.

This is the counterpart of `isOutOfFuel_of_Spec_of_isOutOfFuel` for the OTHER
non-`Ok` constructor, and it is what a loop body containing `continue` needs: once
the skip guard yields a `Continue` checkpoint, every later step in the body carries
that same checkpoint through, so the body's output is still a `Continue`. -/
lemma isJump_of_Spec_of_isJump {P : State → State → Prop} {a b : State} {c : Jump}
    (h : Spec P a b) (ha : isJump c a) : isJump c b := by
  rcases a with ⟨evm, store⟩ | _ | c'
  · exact absurd ha (by simp [State.isJump])
  · exact absurd ha (by simp [State.isJump])
  · simp only [State.isJump] at ha
    subst ha
    exact h

/-- A state carrying a `Continue` jump is not a `Break`.  Together with the lemma
above this is how `ABreak` closes for a body whose skip path continues rather than
reverting: the output is either `Ok` (no skip) or a `Continue` checkpoint (skip),
and neither is a `Break`. -/
lemma not_isBreak_of_isJump_Continue {s : State} {evm : EVM} {store : VarStore}
    (h : isJump (.Continue evm store) s) : ¬ isBreak s := by
  rcases s with ⟨e, st⟩ | _ | c
  · simp [State.isBreak]
  · simp [State.isBreak]
  · rcases c with ⟨e, st⟩ | ⟨e, st⟩ | ⟨e, st⟩ <;>
      simp only [State.isJump] at h <;> simp [State.isBreak]

end

end Clear
