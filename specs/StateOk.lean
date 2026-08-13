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

/-- Once a step carries a checkpoint, REVIVING its output gives the same state as
reviving its input.

This is what a `break`-exiting loop needs.  When a body's guard breaks, the rest of
the body still runs as `Spec` steps, but each one merely carries the checkpoint
along; so the state the loop finally revives is the one that existed AT THE BREAK,
not something the later steps produced.  Chaining this lemma across the remaining
steps moves the goal back to the breaking guard, where the branch condition is
known. -/
lemma reviveJump_eq_of_Spec_of_isJump {P : State → State → Prop} {a b : State} {c : Jump}
    (h : Spec P a b) (ha : isJump c a) : 🧟 b = 🧟 a := by
  rcases a with ⟨evm, store⟩ | _ | c'
  · exact absurd ha (by simp [State.isJump])
  · exact absurd ha (by simp [State.isJump])
  · simp only [State.isJump] at ha
    subst ha
    -- on a Checkpoint input, `Spec P a b` IS `b.isJump c` -- exhibit it before casing,
    -- or the case analysis has nothing reduced to work with
    have hb : isJump c b := h
    rcases b with ⟨e, st⟩ | _ | c''
    · simp [State.isJump] at hb
    · simp [State.isJump] at hb
    · simp only [State.isJump] at hb
      subst hb
      simp [State.reviveJump]

/-- A `Break` state exhibits its jump, so the lemmas above apply to it. -/
lemma isJump_Break_of_isBreak {s : State} (h : isBreak s) :
    ∃ evm store, isJump (.Break evm store) s := by
  rcases s with ⟨e, st⟩ | _ | c
  · simp [State.isBreak] at h
  · simp [State.isBreak] at h
  · rcases c with ⟨e, st⟩ | ⟨e, st⟩ | ⟨e, st⟩
    · simp [State.isBreak] at h
    · exact ⟨e, st, by simp [State.isJump]⟩
    · simp [State.isBreak] at h

/-- Reviving a break undoes it: `🧟(💔 t) = t` for an `Ok` state.  So a loop that
exits by breaking hands back exactly the state that was live when the guard fired. -/
lemma reviveJump_setBreak {t : State} (h : isOk t) : 🧟 (💔 t) = t := by
  rcases t with ⟨e, st⟩ | _ | _
  · rfl
  · exact absurd h (by simp [isOk])
  · exact absurd h (by simp [isOk])

/-- A freshly broken `Ok` state is a `Break`. -/
lemma isBreak_setBreak {t : State} (h : isOk t) : isBreak (💔 t) := by
  rcases t with ⟨e, st⟩ | _ | _
  · simp [State.isBreak, State.setBreak]
  · exact absurd h (by simp [isOk])
  · exact absurd h (by simp [isOk])

/-- The evm of a `setEvm` is the evm set, for any `Ok` state.  Clear has this only for a
literal `Ok evm store` (`evm_setEvm_ok` in specs/RevertModel.lean), which does not apply
when the state is an insert chain -- as it is inside every function body. -/
lemma evm_setEvm_of_isOk {t : State} {e : EVM} (h : isOk t) : (t🇪⟦e⟧).evm = e := by
  rcases t with ⟨a, b⟩ | _ | _
  · rfl
  · exact absurd h (by simp [isOk])
  · exact absurd h (by simp [isOk])

/-- **Looking up a parameter right after `initcall`.**  `initcall` is
`setStore default` then `multifill`, and `multifill` inserts the parameters in order --
so the LAST parameter ends up outermost.  These two cover the shapes that occur: a
one-parameter call, and the two-parameter case for each position.

Clear has no such lemma, and without one the value of a function's own argument cannot be
recovered inside its spec -- which is what blocks stating an accessor's result in terms of
its inputs. -/
lemma lookup_initcall_one {s : State} {v : Ast.Identifier} {x : UInt256} (h : isOk s) :
    (s☎️⟦[v],[x]⟧)[v]!! = x := by
  rcases s with ⟨evm, store⟩ | _ | _
  · simp only [State.initcall, multifill_cons, multifill_nil]
    rw [lookup_insert' (isOk_setStore_of_isOk (by simp [isOk]))]
  · exact absurd h (by simp [isOk])
  · exact absurd h (by simp [isOk])

/-- Second of two parameters.  `multifill` inserts the FIRST parameter LAST
(`multifill (v::vs) (a::as) s = (multifill vs as s)⟦v ↦ a⟧`), so the second is one insert
down and the lookup has to skip the first -- hence the `≠`. -/
lemma lookup_initcall_snd {s : State} {u v : Ast.Identifier} {x y : UInt256} (h : isOk s)
    (hne : v ≠ u) : (s☎️⟦[u, v],[x, y]⟧)[v]!! = y := by
  rcases s with ⟨evm, store⟩ | _ | _
  · simp only [State.initcall, multifill_cons, multifill_nil]
    rw [lookup_insert_of_ne hne,
      lookup_insert' (isOk_setStore_of_isOk (by simp [isOk]))]
  · exact absurd h (by simp [isOk])
  · exact absurd h (by simp [isOk])

/-- First of two parameters: inserted LAST, so outermost, so a direct `lookup_insert'`. -/
lemma lookup_initcall_fst {s : State} {u v : Ast.Identifier} {x y : UInt256} (h : isOk s) :
    (s☎️⟦[u, v],[x, y]⟧)[u]!! = x := by
  rcases s with ⟨evm, store⟩ | _ | _
  · simp only [State.initcall, multifill_cons, multifill_nil]
    rw [lookup_insert' (by simp only [isOk_insert]; exact isOk_setStore_of_isOk (by simp [isOk]))]
  · exact absurd h (by simp [isOk])
  · exact absurd h (by simp [isOk])

end

end Clear
