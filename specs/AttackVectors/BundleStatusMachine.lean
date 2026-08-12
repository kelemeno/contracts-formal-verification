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

end AttackVectors.BundleStatusMachine
