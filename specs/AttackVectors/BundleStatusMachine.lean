import Mathlib.Tactic

/-
  THE BUNDLE STATUS MACHINE — one delivery per bundle, by two routes that exclude each other.

  `InteropHandlerBase` spreads its transitions across four functions, each with its own guard:

      verifyBundle        require(status == Unreceived)                      -> Verified
      executeBundle       require(status == Unreceived || status == Verified) -> FullyExecuted
      unbundleBundle      require(status == Verified  || status == Unbundled) -> Unbundled
      executeAtomicBundle require(status == Unreceived)                      -> FullyExecuted

  Read one at a time these are guards; read together they are a state machine, and the safety property
  is a REACHABILITY claim no single function states: a bundle is delivered at most once, and the
  whole-bundle route and the per-call unbundled route cannot both happen.  That matters because each
  route delivers the same calls -- doing both would deliver twice.

  The file also names a cross-contract dependency that the guards make load-bearing but do not state.
-/

namespace AttackVectors.BundleStatusMachine

inductive Status
  | Unreceived | Verified | FullyExecuted | Unbundled
  deriving DecidableEq, Repr

/-- The transitions, one constructor per deployed edge. -/
inductive Step : Status → Status → Prop
  | verify : Step .Unreceived .Verified
  | executeFresh : Step .Unreceived .FullyExecuted
  | executeVerified : Step .Verified .FullyExecuted
  | unbundleFirst : Step .Verified .Unbundled
  | unbundleAgain : Step .Unbundled .Unbundled
  | executeAtomic : Step .Unreceived .FullyExecuted

/-- Reflexive-transitive closure: the states a bundle can reach. -/
inductive Reach : Status → Status → Prop
  | refl (s : Status) : Reach s s
  | tail {a b c : Status} : Reach a b → Step b c → Reach a c

/-! ## Safety -/

/-- **DELIVERY IS TERMINAL.**  No guard admits `FullyExecuted`, so nothing follows it — the CEI write
that precedes the calls is what makes a reentrant or repeated execution hit a closed door. -/
theorem fullyExecuted_terminal {t : Status} : ¬ Step .FullyExecuted t := by
  rintro ⟨⟩

/-- Hence a delivered bundle stays delivered. -/
theorem reach_from_fullyExecuted {t : Status} (h : Reach .FullyExecuted t) : t = .FullyExecuted := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) fullyExecuted_terminal

/-- **THE UNBUNDLED ROUTE IS ABSORBING TOO.**  Once unbundled, the whole-bundle execution path is
closed: the only edge out of `Unbundled` returns to `Unbundled`. -/
theorem reach_from_unbundled {t : Status} (h : Reach .Unbundled t) : t = .Unbundled := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    cases hstep
    rfl

/-- **THE TWO DELIVERY ROUTES EXCLUDE EACH OTHER.**  A bundle cannot be both executed as a whole and
unbundled for per-call execution, in either order — so the same call cannot be delivered twice by
taking one route and then the other. -/
theorem routes_exclusive :
    (¬ Reach .FullyExecuted .Unbundled) ∧ (¬ Reach .Unbundled .FullyExecuted) := by
  constructor
  · intro h; exact absurd (reach_from_fullyExecuted h) (by decide)
  · intro h; exact absurd (reach_from_unbundled h) (by decide)

/-- Both delivery states are reachable from a fresh bundle, so the exclusivity above is not vacuous —
each route is genuinely available until the other is taken. -/
theorem both_routes_available :
    Reach .Unreceived .FullyExecuted ∧ Reach .Unreceived .Unbundled :=
  ⟨.tail (.refl _) .executeFresh, .tail (.tail (.refl _) .verify) .unbundleFirst⟩

/-! ## The cross-contract dependency the guards rely on

`executeAtomicBundle` is stricter than `executeBundle`: it admits ONLY `Unreceived`, where
`executeBundle` also admits `Verified`.  So an atomic bundle that ever reached `Verified` could never
be executed atomically — the source funds are already burned, and the flow could only end in the
timeout path, whose recovery `RecoveryLimits` shows is partial.

The guard is nonetheless safe, and the reason is not in this contract:

  * `verifyBundle` reaches `Verified` only through `_verifyBundle`, which requires `_proveInclusion` —
    an L1 message inclusion proof.
  * Atomic bundles are NEVER published to L1: `InteropCenter._dispatchBundle` takes the `isAtomic`
    branch to `append` and skips `_sendBundleToL1` entirely.
  * So no valid inclusion proof for an atomic bundle exists, `verifyBundle` cannot succeed on one, and
    the `Unreceived -> Verified` edge is unreachable for atomic bundles.

That is a liveness dependency spanning two contracts, and it is of the same fragile species as
`LocalHonesty.sole_call_site`: nothing in the type system enforces it, and a future change that
published atomic bundles to L1 — for observability, say — would make `verifyBundle` succeed on them
and permanently brick their execution.  Recorded, not reported as a defect: the current code is
correct. -/

/-- **THE CONDITIONAL.**  If an atomic bundle ever reached `Verified`, atomic execution would be
permanently unavailable — `Verified` has no edge to `FullyExecuted` via the atomic entry point, whose
only enabling state is `Unreceived`, and no edge returns to `Unreceived`. -/
theorem verified_blocks_atomic_execution : ¬ Step .Verified .Unreceived := by
  rintro ⟨⟩

/-- And no state returns to `Unreceived` at all: it is the machine's unique initial state, so a bundle
that leaves it can never be treated as fresh again. -/
theorem unreceived_unreachable {s : Status} : ¬ Step s .Unreceived := by
  cases s <;> rintro ⟨⟩

/-! ## The per-call machine — where a double delivery would actually land

Bundle-level exclusivity says a bundle takes one route.  It does NOT by itself say a CALL is delivered
once: the unbundled route processes calls individually, across as many `unbundleBundle` transactions as
the unbundler likes (`Unbundled -> Unbundled` is a legal edge).  The per-call guard is what closes it:

    if (requested == Executed)  { require(recorded == Unprocessed, CallNotExecutable);  recorded = Executed; }
    else if (requested == Cancelled) { require(recorded != Executed, CallAlreadyExecuted);
                                       if (recorded == Unprocessed) recorded = Cancelled; }
    // any other request is skipped

Note the asymmetry in the second branch: cancelling is IDEMPOTENT (re-cancelling a `Cancelled` call is
a silent no-op, not a revert), while executing is not.  That is what lets an unbundler resubmit a
status array without the transaction reverting on already-cancelled entries. -/

inductive CallStatus
  | Unprocessed | Executed | Cancelled
  deriving DecidableEq, Repr

/-- The per-call transitions, one constructor per reachable edge of the loop above. -/
inductive CallStep : CallStatus → CallStatus → Prop
  | execute : CallStep .Unprocessed .Executed
  | cancel : CallStep .Unprocessed .Cancelled
  | cancelAgain : CallStep .Cancelled .Cancelled

inductive CallReach : CallStatus → CallStatus → Prop
  | refl (s : CallStatus) : CallReach s s
  | tail {a b c : CallStatus} : CallReach a b → CallStep b c → CallReach a c

/-- **A CALL IS EXECUTED AT MOST ONCE.**  `Executed` has no outgoing edge: the `require(recorded ==
Unprocessed)` on the execute branch is what makes a second execution of the same call impossible, no
matter how many `unbundleBundle` transactions are submitted. -/
theorem callExecuted_terminal {t : CallStatus} : ¬ CallStep .Executed t := by
  rintro ⟨⟩

theorem callReach_from_executed {t : CallStatus} (h : CallReach .Executed t) : t = .Executed := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact absurd (ih ▸ hstep) callExecuted_terminal

/-- **AND A CANCELLED CALL IS NEVER EXECUTED.**  The execute branch demands `Unprocessed`, so
cancellation is a one-way door — `Cancelled` only loops to itself. -/
theorem callReach_from_cancelled {t : CallStatus} (h : CallReach .Cancelled t) : t = .Cancelled := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    cases hstep
    rfl

/-- The per-call counterpart of `routes_exclusive`: executed and cancelled are mutually unreachable. -/
theorem call_outcomes_exclusive :
    (¬ CallReach .Executed .Cancelled) ∧ (¬ CallReach .Cancelled .Executed) := by
  constructor
  · intro h; exact absurd (callReach_from_executed h) (by decide)
  · intro h; exact absurd (callReach_from_cancelled h) (by decide)

/-- Both outcomes are reachable from a fresh call, so the exclusivity is not vacuous. -/
theorem call_outcomes_available :
    CallReach .Unprocessed .Executed ∧ CallReach .Unprocessed .Cancelled :=
  ⟨.tail (.refl _) .execute, .tail (.refl _) .cancel⟩

/-- **CANCELLATION IS IDEMPOTENT, EXECUTION IS NOT.**  Re-cancelling is a legal edge; there is no
`Executed -> Executed`.  The asymmetry is deliberate in the source (a resubmitted status array must not
revert on entries already cancelled) and it is why `Cancelled` needs its self-loop while `Executed`
does not. -/
theorem cancel_idempotent_execute_not :
    CallStep .Cancelled .Cancelled ∧ ¬ CallStep .Executed .Executed :=
  ⟨.cancelAgain, callExecuted_terminal⟩

/-! ## The two levels compose

A call reaches `Executed` by exactly one of two routes:

* the whole-bundle route, where `executeBundle` / `executeAtomicBundle` set every call to `Executed` in
  one transaction, from bundle status `Unreceived` or `Verified`; or
* the unbundled route, where each call transitions individually, from bundle status `Unbundled`.

`routes_exclusive` rules out taking both, and `callReach_from_executed` rules out repeating either.
Neither alone suffices: bundle-level exclusivity says nothing about repeated per-call execution within
the unbundled route, and the per-call guard says nothing about a bundle being both fully executed and
unbundled.  Together they give "each call is delivered at most once", which is the property the
destination side of no-theft needs. -/

end AttackVectors.BundleStatusMachine
