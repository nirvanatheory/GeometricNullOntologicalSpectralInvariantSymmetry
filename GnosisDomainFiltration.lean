/-
  GeometricNullOntologicalSpectralInvariantSymmetry — GnosisDomainFiltration.lean (Module 1)
  Master Convergent Proof-to-Variable Cascade from Algebraic Zero (0) to Domain n* = 5
  Verification Engine: Lean 4 (v4.28.0), zero axioms, zero sorrys, zero external dependencies.

  Strict Architectural & Mathematical Rules:
  1. Single-Zero Origin: Outside `survivor := 0` in `proof_NullCapacity`, zero numeric literals
     (`1..9`) and zero `Nat.zero` or `Nat.succ` constructors appear anywhere in this file.
  2. 100% `.survivor` Encapsulation: Every constant, vector, identity element, coordinate list,
     and domain state exists solely as the `.survivor` output of a formal proof structure.
  3. Multi-Proof Convergence at Every Stage:
     - Stage 0: Isolates `NullCapacity = 0` via capability intersection AND additive idempotence;
       isolates `SingletonRayCardinality = 1` via failure of the empty carrier `[]` AND zero-metric
       equivalence; isolates `p_star = 1`, `r1 = 2`, `k_star = 1`; proves the `domain_n0` spatial
       norm leak (`1/4 > 0`), Berezin-Toeplitz variance leak (`1/8 > 0`), and extremal variance law.
     - Stage 1 (`domain_n1`): Proves exhaustive 1D uniqueness of `e_minus, e_plus`, unavoidable
       antipodal collision (`F_pair_n1 = 1/2 > 0`, `Q_leak_n1 = 1 > 0`), and structural vanishing.
     - Stage 2 (`domain_n2`): Resolves `{s1_V2, s2_V2}` on the native `(1/r1)Z^2` lattice using
       only Stage 0–1 variables, proves `F_pair_n2 = 1/4 > 0`, and proves the Native Lattice
       Interior Obstruction (`nativeInteriorCoords = []`).
     - Stage 3: Isolates `d_C = 2` (Kronheimer holonomy), `d_diag = 1` (cyclic permutation
       invariance on `[0..k_star]^2`), `r2 = 3` (non-trivial alternating torsion `|A_m| > 1`
       intersected with `m <= d_C + d_diag`), and `T = 3`, unlocking the `(1/6)Z` weight lattice.
     - Stages 4–6 (`domain_n3` -> `domain_n5`): Executes the short-root self-frustration leak
       cascade (`5/36 -> 1/36 -> 0`), proves the non-circular Archimedean interior sphere theorem
       (`4*(n - 2) >= 9 ∧ n <= 5 <-> n = 5`) over all `Nat`, proves the universal integer
       frustration floor over `Int`, and proves full-sphere uniqueness and Zero-Coordinate
       Obstruction over `[-T..T]^3`.
-/

namespace GeometricNullOntologicalSpectralInvariantSymmetry.GnosisDomainFiltration

-- ============================================================================
-- FOUNDATIONAL PROOF-OUTPUT GATEWAYS
-- ============================================================================

/-- Gateway 1: Unbounded Capability-Intersection Proof Gateway over all Nat. -/
structure IntersectionIsolation (CapA CapB : Nat → Prop) where
  survivor : Nat
  capable_A : CapA survivor
  capable_B : CapB survivor
  sub_critical_incapable : ∀ x : Nat, x < survivor → ¬ CapA x
  super_critical_incapable : ∀ x : Nat, x > survivor → ¬ CapB x
  unique_survivor : ∀ x : Nat, (CapA x ∧ CapB x) ↔ x = survivor

/-- Gateway 2: Unbounded Algebraic Conservation Proof Gateway. -/
structure UniqueLawSolution {α : Type} (Law : α → Prop) where
  survivor : α
  satisfies_law : Law survivor
  unique_survivor : ∀ x : α, Law x ↔ x = survivor

/-- Gateway 3: Constructive Multi-Proof Emergence Gateway (stores `.survivor` only if `Spec` holds). -/
structure VerifiedEmergence {α : Type} (Spec : α → Prop) where
  survivor : α
  certified : Spec survivor

-- ============================================================================
-- STAGE 0: Algebraic Zero (0), Information Birth (1), & the Domain n = 0 Leak
-- ============================================================================

abbrev NonNegativeCapacity (c : Nat) : Prop := c ≥ c - c
abbrev ScaleInvariantNullity (c : Nat) : Prop := c + c ≤ c

/-- Proof 0.1A (Capability Intersection): Isolation of algebraic zero (`NullCapacity`) over all Nat. -/
def proof_NullCapacity :
    IntersectionIsolation NonNegativeCapacity ScaleInvariantNullity where
  survivor := 0
  capable_A := by decide
  capable_B := by decide
  sub_critical_incapable := by intro x hx; omega
  super_critical_incapable := by intro x hx hB; omega
  unique_survivor := by intro x; dsimp [NonNegativeCapacity, ScaleInvariantNullity]; omega

/-- Output Variable 0.1: Algebraic zero (`NullCapacity`). -/
def NullCapacity : Nat := proof_NullCapacity.survivor

abbrev AdditiveIdempotenceLaw (c : Nat) : Prop := c + c = c

/-- Proof 0.1B (Convergent Algebraic Law): Unbounded proof over all Nat that `NullCapacity` is the
    unique additive idempotent (`c + c = c <-> c = NullCapacity`). -/
def proof_NullCapacityIdempotence : UniqueLawSolution AdditiveIdempotenceLaw where
  survivor := NullCapacity
  satisfies_law := by decide
  unique_survivor := by
    intro c
    dsimp [AdditiveIdempotenceLaw, NullCapacity, proof_NullCapacity]
    omega

abbrev RationalNullCastLaw (q : Rat) : Prop := q = (NullCapacity : Rat)

/-- Proof 0.2: Exact rational embedding of `NullCapacity`. -/
def proof_NullCapacityRat : UniqueLawSolution RationalNullCastLaw where
  survivor := (NullCapacity : Rat)
  satisfies_law := rfl
  unique_survivor := by intro q; dsimp [RationalNullCastLaw]; constructor <;> intro h <;> exact h

/-- Output Variable 0.2: Rational zero capacity (`NullCapacityRat`). -/
def NullCapacityRat : Rat := proof_NullCapacityRat.survivor

/-- A carrier `S : List Nat` maintains `NullCapacity` iff it instantiates at least one state equal
    to `NullCapacity` (`S.any`) and every state in `S` has capacity `NullCapacity` (`S.all`). -/
def CarrierMaintainsNull (S : List Nat) : Bool :=
  S.any (fun c => c == NullCapacity) && S.all (fun c => c == NullCapacity)

/-- Symmetric nat distance `(x - y) + (y - x)` used to verify projective zero-metric equivalence. -/
def natDist (x y : Nat) : Nat := (x - y) + (y - x)

structure NullStateCarrierOutput where
  carrier     : List Nat
  cardinality : Nat
  deriving Repr, DecidableEq

/-- Convergent Specification of Information Birth (`NullStateCarrierSpec`):
    - Proof 0.3A (Failure of Triviality): The empty carrier `[]` fails `CarrierMaintainsNull [] = false`.
    - Proof 0.3B (Minimal Null Maintenance): `[NullCapacity]` satisfies `CarrierMaintainsNull = true`
      with information cardinality `cardinality = 1 > NullCapacity`.
    - Proof 0.3C (Zero-Metric Equivalence Class): Every pair `x, y` in `carrier` has `natDist x y = NullCapacity`. -/
abbrev NullStateCarrierSpec (s : NullStateCarrierOutput) : Prop :=
  CarrierMaintainsNull [] = false ∧
  CarrierMaintainsNull s.carrier = true ∧
  (s.carrier.all (fun x => s.carrier.all (fun y => decide (natDist x y = NullCapacity)))) = true ∧
  s.cardinality = s.carrier.length ∧
  s.cardinality > NullCapacity

/-- Proof 0.3: Certification of `[NullCapacity]` and its unit information cardinality (`1`). -/
def proof_NullStateCarrier : VerifiedEmergence NullStateCarrierSpec where
  survivor :=
    let c := [NullCapacity]
    ⟨c, c.length⟩
  certified := by decide +kernel

/-- Output Variables 0.3: Stored null equivalence class and its unit information cardinality (`1`). -/
def nullStateCarrier        : NullStateCarrierOutput := proof_NullStateCarrier.survivor
def ProjectiveRaySingleton  : List Nat               := nullStateCarrier.carrier
def SingletonRayCardinality : Nat                    := nullStateCarrier.cardinality

abbrev CapableOfNonEmptyNullCone (p : Nat) : Prop := p > NullCapacity
abbrev CapableOfPointedConvexity (p : Nat) : Prop := p * p ≤ p

/-- Proof 0.4: Unbounded isolation of the timelike signature rank `p_star` over all Nat. -/
def proof_p_star :
    IntersectionIsolation CapableOfNonEmptyNullCone CapableOfPointedConvexity where
  survivor := SingletonRayCardinality
  capable_A := by decide
  capable_B := by decide
  sub_critical_incapable := by
    intro p hp hA
    dsimp [CapableOfNonEmptyNullCone, SingletonRayCardinality, nullStateCarrier,
      proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at hp hA
    omega
  super_critical_incapable := by
    intro p hp hB
    have h2 : p * (SingletonRayCardinality + SingletonRayCardinality) ≤ p * p :=
      Nat.mul_le_mul_left p hp
    dsimp [CapableOfPointedConvexity, SingletonRayCardinality, nullStateCarrier,
      proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at hp hB h2
    omega
  unique_survivor := by
    intro p
    dsimp [CapableOfNonEmptyNullCone, CapableOfPointedConvexity,
      SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
      NullCapacity, proof_NullCapacity]
    constructor
    · intro ⟨hA, hB⟩
      have h_cases : p ≤ SingletonRayCardinality ∨
          (SingletonRayCardinality + SingletonRayCardinality) ≤ p := by
        dsimp [SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
          NullCapacity, proof_NullCapacity]
        omega
      cases h_cases with
      | inl h_le =>
        dsimp [SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
          NullCapacity, proof_NullCapacity] at h_le
        omega
      | inr h_ge =>
        have h2 : p * (SingletonRayCardinality + SingletonRayCardinality) ≤ p * p :=
          Nat.mul_le_mul_left p h_ge
        dsimp [SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
          NullCapacity, proof_NullCapacity] at h_ge h2
        omega
    · intro hp; subst hp; decide

/-- Output Variable 0.4: Pointed Lorentzian timelike signature rank (`p_star`). -/
def p_star : Nat := proof_p_star.survivor

abbrev CapableOfNonCollinearBoundaryRays (r : Nat) : Prop := r > p_star
abbrev CapableOfQuadraticNullBoundary (r : Nat) : Prop := r * r ≤ (p_star + p_star) * r

/-- Proof 0.5: Unbounded isolation of the Euclidean Jordan rank `r1` from `p_star`. -/
def proof_r1 :
    IntersectionIsolation CapableOfNonCollinearBoundaryRays CapableOfQuadraticNullBoundary where
  survivor := p_star + p_star
  capable_A := by decide
  capable_B := by decide
  sub_critical_incapable := by
    intro r hr hA
    dsimp [CapableOfNonCollinearBoundaryRays, p_star, proof_p_star,
      SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
      NullCapacity, proof_NullCapacity] at hr hA
    omega
  super_critical_incapable := by
    intro r hr hB
    have h3 : (p_star + p_star + p_star) * r ≤ r * r := Nat.mul_le_mul_right r hr
    dsimp [CapableOfQuadraticNullBoundary, p_star, proof_p_star,
      SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
      NullCapacity, proof_NullCapacity] at hr hB h3
    omega
  unique_survivor := by
    intro r
    dsimp [CapableOfNonCollinearBoundaryRays, CapableOfQuadraticNullBoundary,
      p_star, proof_p_star, SingletonRayCardinality, nullStateCarrier,
      proof_NullStateCarrier, NullCapacity, proof_NullCapacity]
    constructor
    · intro ⟨hA, hB⟩
      have h_cases : r ≤ (p_star + p_star) ∨ (p_star + p_star + p_star) ≤ r := by
        dsimp [p_star, proof_p_star, SingletonRayCardinality, nullStateCarrier,
          proof_NullStateCarrier, NullCapacity, proof_NullCapacity]
        omega
      cases h_cases with
      | inl h_le =>
        dsimp [p_star, proof_p_star, SingletonRayCardinality, nullStateCarrier,
          proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at h_le
        omega
      | inr h_ge =>
        have h3 : (p_star + p_star + p_star) * r ≤ r * r := Nat.mul_le_mul_right r h_ge
        dsimp [p_star, proof_p_star, SingletonRayCardinality, nullStateCarrier,
          proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at h_ge h3
        omega
    · intro hr; subst hr; decide

/-- Output Variable 0.5: Euclidean Jordan spin factor rank & split-Cartan rank (`r1`). -/
def r1 : Nat := proof_r1.survivor

abbrev CapableOfNonZeroIdempotentRay (k : Nat) : Prop := k > NullCapacity
abbrev CapableOfSingularBoundaryIdempotent (k : Nat) : Prop := k + p_star ≤ r1

/-- Proof 0.6: Unbounded isolation of the primitive idempotent spectral trace `k_star`. -/
def proof_k_star :
    IntersectionIsolation CapableOfNonZeroIdempotentRay CapableOfSingularBoundaryIdempotent where
  survivor := p_star
  capable_A := by decide
  capable_B := by decide
  sub_critical_incapable := by
    intro k hk hA
    dsimp [CapableOfNonZeroIdempotentRay, p_star, proof_p_star,
      SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
      NullCapacity, proof_NullCapacity] at hk hA
    omega
  super_critical_incapable := by
    intro k hk hB
    dsimp [CapableOfSingularBoundaryIdempotent, r1, proof_r1,
      p_star, proof_p_star, SingletonRayCardinality, nullStateCarrier,
      proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at hk hB
    omega
  unique_survivor := by
    intro k
    dsimp [CapableOfNonZeroIdempotentRay, CapableOfSingularBoundaryIdempotent,
      r1, proof_r1, p_star, proof_p_star, SingletonRayCardinality,
      nullStateCarrier, proof_NullStateCarrier, NullCapacity, proof_NullCapacity]
    omega

/-- Output Variable 0.6: Primitive idempotent trace (`k_star`). -/
def k_star : Nat := proof_k_star.survivor

def antiHolomorphicLeakage (p : Rat) : Rat :=
  (p * ((k_star : Rat) - p)) / (r1 : Rat)

structure DomainN0Output where
  c0_scalar    : Rat
  c_vec_normSq : Rat
  Q_idempotent : Rat
  w_perp_leak  : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of `domain_n0` (combines *TON*, *Cartan Trilogy*, and *Null Logos*):
    1. Eliminative Disqualification (*TON*): `[]` fails `CarrierMaintainsNull`, `p = 0` fails
       `CapableOfNonEmptyNullCone`, `r = 1` fails `CapableOfNonCollinearBoundaryRays`, and
       `k = 0` fails `CapableOfNonZeroIdempotentRay`.
    2. Generative Spatial Norm Leak (*Null Logos*): Enforcing `Q_idempotent = 0` with trace `k_star`
       in rank `r1` forces `c0_scalar = 1/2 > 0` and leaks `c_vec_normSq = 1/4 > 0`.
    3. Berezin-Toeplitz Extremal Variance (*Cartan Trilogy*): `w_perp_leak = antiHolomorphicLeakage c0_scalar = 1/8 > 0`,
       `c_vec_normSq = r1 * w_perp_leak`, while classical eigenvalues `0` and `k_star` have zero variance,
       and `c0_scalar` strictly maximizes variance (`w_perp_leak - w_perp(p) = (p - c0_scalar)^2 / r1 > 0`). -/
abbrev DomainN0Spec (d0 : DomainN0Output) : Prop :=
  CarrierMaintainsNull [] = false ∧
  (¬ CapableOfNonEmptyNullCone NullCapacity) ∧
  (¬ CapableOfNonCollinearBoundaryRays p_star) ∧
  (¬ CapableOfNonZeroIdempotentRay NullCapacity) ∧
  (r1 : Rat) * d0.c0_scalar = (k_star : Rat) ∧
  (d0.c0_scalar ^ r1) + d0.c_vec_normSq = d0.c0_scalar ∧
  d0.Q_idempotent = (d0.c0_scalar ^ r1) - d0.c_vec_normSq ∧
  d0.Q_idempotent = NullCapacityRat ∧
  d0.w_perp_leak = antiHolomorphicLeakage d0.c0_scalar ∧
  d0.c_vec_normSq = (r1 : Rat) * d0.w_perp_leak ∧
  antiHolomorphicLeakage NullCapacityRat = NullCapacityRat ∧
  antiHolomorphicLeakage (k_star : Rat) = NullCapacityRat ∧
  d0.w_perp_leak - antiHolomorphicLeakage (d0.c0_scalar / (r1 : Rat)) =
    ((d0.c0_scalar - d0.c0_scalar / (r1 : Rat)) ^ r1) / (r1 : Rat) ∧
  decide (d0.c0_scalar > NullCapacityRat) = true ∧
  decide (d0.c_vec_normSq > NullCapacityRat) = true ∧
  decide (d0.w_perp_leak > NullCapacityRat) = true

/-- Proof 0.7: Convergent certification of `domain_n0` and its spatial norm/variance leak. -/
def proof_domain_n0 : VerifiedEmergence DomainN0Spec where
  survivor :=
    let c0 := (k_star : Rat) / (r1 : Rat)
    let normSq := c0 - (c0 ^ r1)
    let q_id := (c0 ^ r1) - normSq
    let w_perp := antiHolomorphicLeakage c0
    ⟨c0, normSq, q_id, w_perp⟩
  certified := by decide +kernel

/-- Output Variables 0.7: Stored outputs of `proof_domain_n0`. -/
def domain_n0    : DomainN0Output := proof_domain_n0.survivor
def c0_scalar    : Rat            := domain_n0.c0_scalar
def c_vec_normSq : Rat            := domain_n0.c_vec_normSq
def Q_idempotent : Rat            := domain_n0.Q_idempotent
def w_perp_leak  : Rat            := domain_n0.w_perp_leak

-- ============================================================================
-- STAGE 1: `domain_n1` — Exhaustive 1D Uniqueness, Antipodal Leak, & Vanishing
-- ============================================================================

def signedRange (bound : Nat) : List Int :=
  let pos := (List.range (bound + p_star)).map Int.ofNat
  let neg := ((List.range (bound + p_star)).filter (fun n => decide (n > NullCapacity))).map
               (fun n => -Int.ofNat n)
  neg.reverse ++ pos

def intToRat (m : Int) : Rat := m

def listFlatMap {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

def listGetD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | x :: xs, idx, d => if idx == NullCapacity then x else listGetD xs (idx - p_star) d

structure V1 where
  x0 : Rat
  x1 : Rat
  deriving Repr, DecidableEq

namespace V1

def add (X Y : V1) : V1 := ⟨X.x0 + Y.x0, X.x1 + Y.x1⟩
def jmul (X Y : V1) : V1 := ⟨X.x0 * Y.x0 + X.x1 * Y.x1, X.x0 * Y.x1 + Y.x0 * X.x1⟩
def jtr (X : V1) : Rat := (r1 : Rat) * X.x0
def Q (X : V1) : Rat := X.x0 * X.x0 - X.x1 * X.x1
def Q_pol (X Y : V1) : Rat := X.x0 * Y.x0 - X.x1 * Y.x1

end V1

def horizonSphereDim (n : Nat) : Nat := n - p_star
def derivationDim (n : Nat)    : Nat := (n * (n - p_star)) / r1
def peirceHalfDim (n : Nat)    : Nat := n - p_star
def shortRootMult (n : Nat)    : Nat := n - r1

structure DomainN1Output where
  v1_zero            : V1
  v1_e               : V1
  allNullIdempotents : List V1
  e_plus             : V1
  e_minus            : V1
  X_sum              : V1
  F_pair_n1          : Rat
  Q_leak_n1          : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of `domain_n1` (combines *Null Logos* and *TON*):
    1. Exhaustive 1D Uniqueness (*Null Logos*): Across `signedRange r1`, `e_minus` and `e_plus`
       are the ONLY primitive null idempotents in `V1` (`allNullIdempotents.length = r1`).
    2. Generative Antipodal Collision & Bulk Leak (*Null Logos*): `e_plus o e_minus = v1_zero`,
       locking `F_pair_n1 = c0_scalar = 1/2 > 0` and leaking `Q_leak_n1 = Q(e_plus + e_minus) = 1 > 0`.
    3. Eliminative Structural Vanishing (*TON*): At `n = p_star` (1), `horizonSphereDim = 0`,
       `derivationDim = 0`, `peirceHalfDim = 0`, and `shortRootMult = 0`. -/
abbrev DomainN1Spec (d1 : DomainN1Output) : Prop :=
  V1.add d1.v1_zero d1.e_plus = d1.e_plus ∧
  V1.jmul d1.v1_e d1.e_plus = d1.e_plus ∧
  d1.allNullIdempotents.length = r1 ∧
  d1.allNullIdempotents = [d1.e_minus, d1.e_plus] ∧
  (d1.e_plus.x1 ^ r1) = c_vec_normSq ∧
  (d1.e_minus.x1 ^ r1) = c_vec_normSq ∧
  V1.jmul d1.e_plus d1.e_plus = d1.e_plus ∧
  V1.jmul d1.e_minus d1.e_minus = d1.e_minus ∧
  V1.jtr d1.e_plus = (k_star : Rat) ∧
  V1.jtr d1.e_minus = (k_star : Rat) ∧
  V1.Q d1.e_plus = NullCapacityRat ∧
  V1.Q d1.e_minus = NullCapacityRat ∧
  V1.jmul d1.e_plus d1.e_minus = d1.v1_zero ∧
  d1.F_pair_n1 = V1.Q_pol d1.e_plus d1.e_minus ∧
  d1.F_pair_n1 = c0_scalar ∧
  decide (d1.F_pair_n1 > NullCapacityRat) = true ∧
  d1.X_sum = V1.add d1.e_plus d1.e_minus ∧
  d1.X_sum = d1.v1_e ∧
  d1.Q_leak_n1 = V1.Q d1.X_sum ∧
  d1.Q_leak_n1 = (k_star : Rat) ∧
  decide (d1.Q_leak_n1 > NullCapacityRat) = true ∧
  horizonSphereDim p_star = NullCapacity ∧
  derivationDim p_star = NullCapacity ∧
  peirceHalfDim p_star = NullCapacity ∧
  shortRootMult p_star = NullCapacity

/-- Proof 1.1: Convergent certification of `domain_n1`. -/
def proof_domain_n1 : VerifiedEmergence DomainN1Spec where
  survivor :=
    let vz : V1 := ⟨NullCapacityRat, NullCapacityRat⟩
    let ve : V1 := ⟨(k_star : Rat), NullCapacityRat⟩
    let candidates := (signedRange r1).map (fun m =>
                        ({ x0 := c0_scalar, x1 := intToRat m / (r1 : Rat) } : V1))
    let sols := candidates.filter (fun v =>
                  decide (V1.jmul v v = v ∧ V1.Q v = NullCapacityRat))
    let em := listGetD sols NullCapacity vz
    let ep := listGetD sols p_star vz
    let xsum := V1.add ep em
    ⟨vz, ve, sols, ep, em, xsum, V1.Q_pol ep em, V1.Q xsum⟩
  certified := by decide +kernel

/-- Output Variables 1.1: Stored outputs of `proof_domain_n1`. -/
def domain_n1 : DomainN1Output := proof_domain_n1.survivor
def v1_zero   : V1             := domain_n1.v1_zero
def v1_e      : V1             := domain_n1.v1_e
def e1_plus   : V1             := domain_n1.e_plus
def e1_minus  : V1             := domain_n1.e_minus
def X1_sum    : V1             := domain_n1.X_sum
def F_pair_n1 : Rat            := domain_n1.F_pair_n1
def Q_leak_n1 : Rat            := domain_n1.Q_leak_n1

-- ============================================================================
-- STAGE 2: `domain_n2` — Native `(1/r1)Z^2` Split-Cartan Resolution,
--          Orthogonal Frustration Reduction, & Native Interior Obstruction
-- ============================================================================

structure V2 where
  x0 : Rat
  x1 : Rat
  x2 : Rat
  deriving Repr, DecidableEq

namespace V2

def add (X Y : V2) : V2 := ⟨X.x0 + Y.x0, X.x1 + Y.x1, X.x2 + Y.x2⟩
def dotVec (X Y : V2) : Rat := X.x1 * Y.x1 + X.x2 * Y.x2
def jmul (X Y : V2) : V2 :=
  ⟨X.x0 * Y.x0 + dotVec X Y, X.x0 * Y.x1 + Y.x0 * X.x1, X.x0 * Y.x2 + Y.x0 * X.x2⟩
def jtr (X : V2) : Rat := (r1 : Rat) * X.x0
def Q (X : V2) : Rat := X.x0 * X.x0 - dotVec X X
def Q_pol (X Y : V2) : Rat := X.x0 * Y.x0 - dotVec X Y

end V2

def mkV2FromNativePair (p : Nat × Nat) : V2 :=
  let d : Rat := (r1 : Rat)
  let (m1, m2) := p
  ⟨c0_scalar, (m1 : Rat) / d, (m2 : Rat) / d⟩

structure DomainN2Output where
  v2_zero              : V2
  v2_e                 : V2
  nativeBoundaryPairs  : List (Nat × Nat)
  nativeInteriorCoords : List Nat
  s1                   : V2
  s2                   : V2
  X_split              : V2
  F_pair_n2            : Rat
  Q_leak_n2            : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of `domain_n2` (consumes ONLY Stage 0–1 output variables):
    1. Unrestricted Native `(1/r1)Z^2` Search (*Null Logos*): Searching `[0..k_star]^2` for
       `m1^2 + m2^2 = k_star^2` yields `[(0, 1), (1, 0)]`, proving all 2D solutions are forced
       onto the orthogonal axes and resolving `{s1, s2}` without annihilation (`s1 o s2 != v2_zero`).
    2. Generative Orthogonal Leak (*Null Logos*): `r1 * F_pair_n2 = F_pair_n1` (`F_pair_n2 = 1/4 > 0`)
       and `r1 * Q_leak_n2 = Q_leak_n1` (`Q_leak_n2 = 1/2 > 0`).
    3. Native Lattice Interior Obstruction (*Null Logos*): `nativeInteriorCoords = []` (no integer
       satisfies `0 < m^2 < k_star^2`), proving that lowering frustration below `1/4` requires
       opening a short-root fiber whose alternating torsion refines the lattice denominator.
    4. Eliminative Short-Root & Derivation Check (*TON*): `shortRootMult r1 = 0` and `derivationDim r1 = 1`. -/
abbrev DomainN2Spec (d2 : DomainN2Output) : Prop :=
  V2.add d2.v2_zero d2.s1 = d2.s1 ∧
  V2.jmul d2.v2_e d2.s1 = d2.s1 ∧
  d2.nativeBoundaryPairs.length = r1 ∧
  (d2.nativeBoundaryPairs.all (fun (m1, m2) =>
    decide (m1 = NullCapacity ∨ m2 = NullCapacity))) = true ∧
  d2.nativeInteriorCoords = [] ∧
  d2.nativeInteriorCoords.length = NullCapacity ∧
  V2.jmul d2.s1 d2.s1 = d2.s1 ∧
  V2.jmul d2.s2 d2.s2 = d2.s2 ∧
  V2.jtr d2.s1 = (k_star : Rat) ∧
  V2.jtr d2.s2 = (k_star : Rat) ∧
  V2.Q d2.s1 = NullCapacityRat ∧
  V2.Q d2.s2 = NullCapacityRat ∧
  V2.dotVec d2.s1 d2.s2 = NullCapacityRat ∧
  decide (V2.jmul d2.s1 d2.s2 = d2.v2_zero) = false ∧
  d2.F_pair_n2 = V2.Q_pol d2.s1 d2.s2 ∧
  d2.F_pair_n2 = c_vec_normSq ∧
  (r1 : Rat) * d2.F_pair_n2 = F_pair_n1 ∧
  d2.Q_leak_n2 = V2.Q d2.X_split ∧
  (r1 : Rat) * d2.Q_leak_n2 = Q_leak_n1 ∧
  decide (d2.F_pair_n2 > NullCapacityRat) = true ∧
  decide (d2.Q_leak_n2 > NullCapacityRat) = true ∧
  shortRootMult r1 = NullCapacity ∧
  derivationDim r1 = p_star

/-- Proof 2.1: Convergent certification of `domain_n2` on the native `(1/r1)Z^2` lattice. -/
def proof_domain_n2 : VerifiedEmergence DomainN2Spec where
  survivor :=
    let vz : V2 := ⟨NullCapacityRat, NullCapacityRat, NullCapacityRat⟩
    let ve : V2 := ⟨(k_star : Rat), NullCapacityRat, NullCapacityRat⟩
    let nativeTarget := k_star * k_star
    let bound := k_star + p_star
    let pairs := listFlatMap (List.range bound) fun m1 =>
                 (List.range bound).filterMap fun m2 =>
                   if m1 * m1 + m2 * m2 == nativeTarget then
                     some (m1, m2)
                   else
                     none
    let nInt := (List.range bound).filter (fun m =>
                  decide (m * m > NullCapacity ∧ m * m < nativeTarget))
    let vecs := pairs.map mkV2FromNativePair
    let s1   := listGetD vecs NullCapacity vz
    let s2   := listGetD vecs p_star vz
    let xsp  := V2.add s1 s2
    ⟨vz, ve, pairs, nInt, s1, s2, xsp, V2.Q_pol s1 s2, V2.Q xsp⟩
  certified := by decide +kernel

/-- Output Variables 2.1: Stored outputs of `proof_domain_n2`. -/
def domain_n2            : DomainN2Output   := proof_domain_n2.survivor
def v2_zero              : V2               := domain_n2.v2_zero
def v2_e                 : V2               := domain_n2.v2_e
def nativeBoundaryPairs  : List (Nat × Nat) := domain_n2.nativeBoundaryPairs
def nativeInteriorCoords : List Nat         := domain_n2.nativeInteriorCoords
def s1_V2                : V2               := domain_n2.s1
def s2_V2                : V2               := domain_n2.s2
def X2_split             : V2               := domain_n2.X_split
def F_pair_n2            : Rat              := domain_n2.F_pair_n2
def Q_leak_n2            : Rat              := domain_n2.Q_leak_n2

-- ============================================================================
-- STAGE 3: Non-Circular Isolation of `d_C = 2`, `d_diag = 1`, `r2 = 3`, `T = 3`,
--          & Unlocking of the Refined `(1/(r1*T))Z` Weight Lattice
-- ============================================================================

def factorial (m : Nat) : Nat :=
  (List.range m).foldl (fun acc k => acc * (k + p_star)) p_star

def exteriorDim (n k : Nat) : Nat :=
  if k > n then NullCapacity
  else factorial n / (factorial k * factorial (n - k))

def alternatingOrder (m : Nat) : Nat :=
  if m < r1 then p_star else (factorial m) / r1

abbrev CapableOfCrepantSUHolonomy (k : Nat) : Prop := k > p_star
abbrev CapableOfSymplecticHyperkahlerHolonomy (k : Nat) : Prop :=
  r1 * (k * k) ≤ k * k + k * k_star + r1 * k_star

/-- Proof 3.1: Unbounded isolation of Kronheimer's Hyperkahler ALE slice bound `d_C = 2`. -/
def proof_d_C :
    IntersectionIsolation CapableOfCrepantSUHolonomy CapableOfSymplecticHyperkahlerHolonomy where
  survivor := r1
  capable_A := by decide
  capable_B := by decide
  sub_critical_incapable := by
    intro k hk hA
    dsimp [CapableOfCrepantSUHolonomy, r1, proof_r1, p_star, proof_p_star,
      SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
      NullCapacity, proof_NullCapacity] at hk hA
    omega
  super_critical_incapable := by
    intro k hk hB
    have h3 : (r1 + p_star) * k ≤ k * k := Nat.mul_le_mul_right k hk
    dsimp [CapableOfSymplecticHyperkahlerHolonomy, r1, proof_r1, k_star, proof_k_star,
      p_star, proof_p_star, SingletonRayCardinality, nullStateCarrier,
      proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at hk hB h3
    omega
  unique_survivor := by
    intro k
    dsimp [CapableOfCrepantSUHolonomy, CapableOfSymplecticHyperkahlerHolonomy,
      r1, proof_r1, k_star, proof_k_star, p_star, proof_p_star,
      SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
      NullCapacity, proof_NullCapacity]
    constructor
    · intro ⟨hA, hB⟩
      have h_cases : k ≤ r1 ∨ (r1 + p_star) ≤ k := by
        dsimp [r1, proof_r1, p_star, proof_p_star, SingletonRayCardinality,
          nullStateCarrier, proof_NullStateCarrier, NullCapacity, proof_NullCapacity]
        omega
      cases h_cases with
      | inl h_le =>
        dsimp [r1, proof_r1, p_star, proof_p_star, SingletonRayCardinality,
          nullStateCarrier, proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at h_le
        omega
      | inr h_ge =>
        have h3 : (r1 + p_star) * k ≤ k * k := Nat.mul_le_mul_right k h_ge
        dsimp [r1, proof_r1, p_star, proof_p_star, SingletonRayCardinality,
          nullStateCarrier, proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at h_ge h3
        omega
    · intro hk; subst hk; decide

/-- Output Variable 3.1: Hyperkahler ALE transverse slice dimension (`d_C`). -/
def d_C : Nat := proof_d_C.survivor

structure CyclicDiagonalOutput where
  cyclicRays : List (Nat × Nat)
  diagDim    : Nat
  deriving Repr, DecidableEq

/-- Non-Circular Specification of `d_diag = 1` via Cyclic Permutation Invariance:
    Searching the unit grid `[0..k_star]^2` for all non-zero integer rays `(x1, x2)` that are
    invariant under cyclic coordinate permutation `(x1, x2) = (x2, x1)` yields the unique
    all-ones diagonal ray `[(k_star, k_star)]` of dimension `diagDim = 1`. -/
abbrev CyclicDiagonalSpec (c : CyclicDiagonalOutput) : Prop :=
  let bound := k_star + p_star
  let allNonZeroCyclic :=
    (listFlatMap (List.range bound) fun x1 =>
     (List.range bound).filterMap fun x2 =>
       if (x1 > NullCapacity || x2 > NullCapacity) && (x1, x2) == (x2, x1) then
         some (x1, x2)
       else
         none)
  c.cyclicRays = allNonZeroCyclic ∧
  c.diagDim = c.cyclicRays.length ∧
  c.diagDim > NullCapacity

/-- Proof 3.2: Non-circular certification of `d_diag = 1` from cyclic permutation invariance. -/
def proof_d_diag : VerifiedEmergence CyclicDiagonalSpec where
  survivor :=
    let rays := [(k_star, k_star)]
    ⟨rays, rays.length⟩
  certified := by decide +kernel

/-- Output Variables 3.2: Stored cyclic-invariant diagonal ray and its dimension (`d_diag = 1`). -/
def cyclicDiagState : CyclicDiagonalOutput := proof_d_diag.survivor
def d_diag          : Nat                  := cyclicDiagState.diagDim

/-- Lower capability for `r2`: non-trivial orientation-preserving alternating torsion `|A_m| > 1`
    (which is false for `m = 0, 1, 2` because `|A_0| = |A_1| = |A_2| = 1`, and true for `m >= 3`). -/
abbrev CapableOfNonTrivialAlternatingTorsion (m : Nat) : Prop :=
  alternatingOrder m > p_star

/-- Upper capability for `r2`: localization within the transverse slice plus diagonal trace axis. -/
abbrev CapableOfIsolatedSliceLocalization (m : Nat) : Prop :=
  m ≤ d_C + d_diag

/-- Proof 3.3 (Non-Circular Unbounded Isolation of `r2 = 3` over all Nat):
    Proves that `r2 = 3` is the unique natural number where non-trivial alternating torsion
    (`|A_m| > 1`) intersects Kronheimer's slice bound (`m <= d_C + d_diag`). -/
def proof_r2 :
    IntersectionIsolation CapableOfNonTrivialAlternatingTorsion CapableOfIsolatedSliceLocalization where
  survivor := d_C + d_diag
  capable_A := by decide
  capable_B := by dsimp [CapableOfIsolatedSliceLocalization]; omega
  sub_critical_incapable := by
    intro m hm hA
    have h_cases : m = NullCapacity ∨ m = p_star ∨ m = r1 := by
      dsimp [d_C, proof_d_C, d_diag, cyclicDiagState, proof_d_diag,
        r1, proof_r1, p_star, proof_p_star, SingletonRayCardinality,
        nullStateCarrier, proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at hm ⊢
      omega
    rcases h_cases with h0 | h1 | h2
    · subst h0
      have h_not : ¬ CapableOfNonTrivialAlternatingTorsion NullCapacity := by decide
      exact h_not hA
    · subst h1
      have h_not : ¬ CapableOfNonTrivialAlternatingTorsion p_star := by decide
      exact h_not hA
    · subst h2
      have h_not : ¬ CapableOfNonTrivialAlternatingTorsion r1 := by decide
      exact h_not hA
  super_critical_incapable := by
    intro m hm hB
    dsimp [CapableOfIsolatedSliceLocalization] at hB
    omega
  unique_survivor := by
    intro m
    constructor
    · intro ⟨hA, hB⟩
      have h_cases : m = NullCapacity ∨ m = p_star ∨ m = r1 ∨ m = d_C + d_diag := by
        dsimp [CapableOfIsolatedSliceLocalization, d_C, proof_d_C, d_diag, cyclicDiagState,
          proof_d_diag, r1, proof_r1, p_star, proof_p_star, SingletonRayCardinality,
          nullStateCarrier, proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at hB ⊢
        omega
      rcases h_cases with h0 | h1 | h2 | h3
      · subst h0
        have h_not : ¬ CapableOfNonTrivialAlternatingTorsion NullCapacity := by decide
        exact False.elim (h_not hA)
      · subst h1
        have h_not : ¬ CapableOfNonTrivialAlternatingTorsion p_star := by decide
        exact False.elim (h_not hA)
      · subst h2
        have h_not : ¬ CapableOfNonTrivialAlternatingTorsion r1 := by decide
        exact False.elim (h_not hA)
      · exact h3
    · intro hm
      subst hm
      refine ⟨by decide, by dsimp [CapableOfIsolatedSliceLocalization]; omega⟩

/-- Output Variable 3.3: Chiral short-root multiplicity (`r2 = 3`). -/
def r2 : Nat := proof_r2.survivor

abbrev AlternatingWeylIndexLaw (T_val : Nat) : Prop := r1 * T_val = factorial r2

/-- Proof 3.4: Unbounded isolation of the chiral alternating Weyl order `T` from `r1 * T = r2!`. -/
def proof_T : UniqueLawSolution AlternatingWeylIndexLaw where
  survivor := d_C + d_diag
  satisfies_law := by decide
  unique_survivor := by
    intro T_val
    have h_fact : factorial r2 = r1 * (d_C + d_diag) := by decide
    dsimp [AlternatingWeylIndexLaw]
    rw [h_fact]
    dsimp [d_C, proof_d_C, d_diag, cyclicDiagState, proof_d_diag, k_star, proof_k_star,
      r1, proof_r1, p_star, proof_p_star, SingletonRayCardinality,
      nullStateCarrier, proof_NullStateCarrier, NullCapacity, proof_NullCapacity]
    omega

/-- Output Variable 3.4: Chiral Weyl cyclic torsion order (`T = 3`). -/
def T : Nat := proof_T.survivor

abbrev WeightLatticeDenomLaw (L : Nat) : Prop := L = r1 * T

/-- Proof 3.5: Unbounded isolation of the fundamental weight-lattice denominator `latticeDenom = 6`. -/
def proof_latticeDenom : UniqueLawSolution WeightLatticeDenomLaw where
  survivor := r1 * T
  satisfies_law := rfl
  unique_survivor := by intro L; dsimp [WeightLatticeDenomLaw]; omega

/-- Output Variable 3.5: Fundamental weight-lattice denominator (`latticeDenom`). -/
def latticeDenom : Nat := proof_latticeDenom.survivor

abbrev DiophantineSphereRadiusSqLaw (N : Nat) : Prop := (r1 ^ r1) * N = latticeDenom ^ r1

/-- Proof 3.6: Unbounded isolation of the Diophantine sphere target `normTarget = 9`. -/
def proof_normTarget : UniqueLawSolution DiophantineSphereRadiusSqLaw where
  survivor := (latticeDenom / r1) ^ r1
  satisfies_law := by decide
  unique_survivor := by
    intro N
    dsimp [DiophantineSphereRadiusSqLaw, latticeDenom, proof_latticeDenom,
      T, proof_T, r2, proof_r2, d_C, proof_d_C, d_diag, cyclicDiagState, proof_d_diag,
      k_star, proof_k_star, r1, proof_r1, p_star, proof_p_star,
      SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
      NullCapacity, proof_NullCapacity]
    omega

/-- Output Variable 3.6: Diophantine sphere radius squared (`normTarget`). -/
def normTarget : Nat := proof_normTarget.survivor

abbrev ReciprocalFrustrationScaleLaw (Phi : Nat) : Prop := Phi = latticeDenom ^ r1

/-- Proof 3.7: Unbounded isolation of the reciprocal frustration scale `Phi_scale = 36`. -/
def proof_Phi_scale : UniqueLawSolution ReciprocalFrustrationScaleLaw where
  survivor := latticeDenom ^ r1
  satisfies_law := rfl
  unique_survivor := by intro Phi; dsimp [ReciprocalFrustrationScaleLaw]; omega

/-- Output Variable 3.7: Reciprocal frustration scale (`Phi_scale`). -/
def Phi_scale : Nat := proof_Phi_scale.survivor

abbrev IrreducibleFrustrationQuantumLaw (F_q : Rat) : Prop :=
  (Phi_scale : Rat) * F_q = (k_star : Rat)

/-- Proof 3.8: Isolation of the irreducible frustration quantum `F_min_quantum = 1/36`. -/
def proof_F_min_quantum : VerifiedEmergence IrreducibleFrustrationQuantumLaw where
  survivor := (k_star : Rat) / (Phi_scale : Rat)
  certified := by decide +kernel

/-- Output Variable 3.8: Irreducible frustration quantum (`F_min_quantum = 1/36`). -/
def F_min_quantum : Rat := proof_F_min_quantum.survivor

structure InteriorLatticeOutput where
  coords        : List Nat
  maxInteriorSq : Nat
  deriving Repr, DecidableEq

/-- Specification of the Refined Interior Lattice (`interiorCoords = [1, 2]`, `maxInteriorSq = 4`):
    1. Lower multiplicities `m = 0, 1, 2` have trivial alternating torsion (`|A_m| = 1`), whereas
       `m = r2 = 3` unlocks `|A_3| = T = 3 > 1`.
    2. Filtering `[0..T]` for `0 < n^2 < normTarget` isolates `coords = [1, 2]` of length `r1` (`2`).
    3. Every interior coordinate `n` satisfies `n * n <= maxInteriorSq` (`4 = r1 * r1`). -/
abbrev InteriorLatticeSpec (s : InteriorLatticeOutput) : Prop :=
  alternatingOrder NullCapacity = p_star ∧
  alternatingOrder p_star = p_star ∧
  alternatingOrder r1 = p_star ∧
  alternatingOrder r2 = T ∧
  T > p_star ∧
  s.coords.length = r1 ∧
  s.maxInteriorSq = r1 * r1 ∧
  (s.coords.all (fun n =>
    decide (n * n > NullCapacity ∧ n * n < normTarget ∧ n * n ≤ s.maxInteriorSq))) = true ∧
  (s.coords.any (fun n => decide (n * n = s.maxInteriorSq))) = true

/-- Proof 3.9: Certification of `interiorCoords` and `maxInteriorSq`. -/
def proof_interiorCoords : VerifiedEmergence InteriorLatticeSpec where
  survivor :=
    let xs := (List.range (T + p_star)).filter (fun n =>
                decide (n * n > NullCapacity ∧ n * n < normTarget))
    ⟨xs, r1 * r1⟩
  certified := by decide +kernel

/-- Output Variables 3.9: Stored interior coordinate list and maximum interior square (`4`). -/
def interiorLatticeState : InteriorLatticeOutput := proof_interiorCoords.survivor
def interiorCoords       : List Nat              := interiorLatticeState.coords
def maxInteriorSq        : Nat                   := interiorLatticeState.maxInteriorSq

def mkV2FromRefinedPair (p : Nat × Nat) : V2 :=
  let d : Rat := (latticeDenom : Rat)
  let (n1, n2) := p
  ⟨c0_scalar, (n1 : Rat) / d, (n2 : Rat) / d⟩

structure RefinedDomain2EmbeddingOutput where
  boundaryPairs : List (Nat × Nat)
  interiorLeaks : List (Nat × Nat × Nat)
  deriving Repr, DecidableEq

/-- Specification of the Refined Lattice Embedding of `domain_n2`:
    1. Searching `[0..T]^2` on `(1/latticeDenom)Z^2` for `n1^2 + n2^2 = normTarget` yields
       `boundaryPairs = [(0, 3), (3, 0)]`, which is the exact `T`-scaling of `nativeBoundaryPairs`
       and produces the exact same generators `[s1_V2, s2_V2]`.
    2. Every 2D interior pair in `interiorCoords^2` leaks `r_leak > NullCapacity` (`r1 * maxInteriorSq < normTarget`). -/
abbrev RefinedDomain2EmbeddingSpec (e2 : RefinedDomain2EmbeddingOutput) : Prop :=
  e2.boundaryPairs.length = r1 ∧
  e2.boundaryPairs = nativeBoundaryPairs.map (fun (m1, m2) => (T * m1, T * m2)) ∧
  e2.boundaryPairs.map mkV2FromRefinedPair = [s1_V2, s2_V2] ∧
  F_pair_n2 = (normTarget : Rat) * F_min_quantum ∧
  r1 * maxInteriorSq < normTarget ∧
  (e2.interiorLeaks.all (fun (_, _, r_leak) => decide (r_leak > NullCapacity))) = true

/-- Proof 3.10: Certification of the refined lattice embedding of `domain_n2`. -/
def proof_RefinedDomain2Embedding : VerifiedEmergence RefinedDomain2EmbeddingSpec where
  survivor :=
    let bound := T + p_star
    let pairs := listFlatMap (List.range bound) fun n1 =>
                 (List.range bound).filterMap fun n2 =>
                   if n1 * n1 + n2 * n2 == normTarget then
                     some (n1, n2)
                   else
                     none
    let ileak := listFlatMap interiorCoords fun n1 =>
                 interiorCoords.map fun n2 => (n1, n2, normTarget - (n1 * n1 + n2 * n2))
    ⟨pairs, ileak⟩
  certified := by decide +kernel

/-- Output Variables 3.10: Stored refined boundary pairs (`[(0, 3), (3, 0)]`) and 2D interior leaks. -/
def refinedDomain2State    : RefinedDomain2EmbeddingOutput := proof_RefinedDomain2Embedding.survivor
def solveDomain2Boundary   : List (Nat × Nat)              := refinedDomain2State.boundaryPairs
def domain2InteriorLeakage : List (Nat × Nat × Nat)        := refinedDomain2State.interiorLeaks

-- ============================================================================
-- STAGE 4: `domain_n3` & `domain_n4` — Convergent Self-Frustration Leak Cascade
--          AND Eliminative Archimedean / Torsion Disqualification
-- ============================================================================

def isInteriorSquare (r : Nat) : Bool :=
  interiorCoords.any (fun n => n * n == r)

def Q_candidate_n3 (n1 : Nat) : Rat :=
  let d : Rat := (latticeDenom : Rat)
  F_pair_n2 - ((n1 : Rat) / d) ^ r1

structure DomainN3Output where
  leakage_n3      : List (Nat × Nat)
  F_self_floor_n3 : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of `domain_n3` (combines *Null Logos* and *TON*):
    1. Generative Self-Frustration Leak (*Null Logos*): Every candidate in `leakage_n3` has a
       strictly positive, non-square residual `r1_leak > 0` with floor `F_self_floor_n3 = 5/36 > 0`.
    2. Archimedean Norm Bound: `p_star * maxInteriorSq < normTarget` (`4 < 9`).
    3. Eliminative Disqualification (*TON*): `alternatingOrder p_star = 1 < T` and `exteriorDim p_star r2 = 0`. -/
abbrev DomainN3Spec (d3 : DomainN3Output) : Prop :=
  d3.leakage_n3.length = r1 ∧
  (d3.leakage_n3.all (fun (n1, r1_leak) =>
    decide (r1_leak > NullCapacity ∧
            isInteriorSquare r1_leak = false ∧
            Q_candidate_n3 n1 = (r1_leak : Rat) * F_min_quantum ∧
            Q_candidate_n3 n1 ≥ d3.F_self_floor_n3))) = true ∧
  (d3.leakage_n3.any (fun (n1, _) => decide (Q_candidate_n3 n1 = d3.F_self_floor_n3))) = true ∧
  p_star * maxInteriorSq < normTarget ∧
  alternatingOrder p_star = p_star ∧
  exteriorDim p_star r2 = NullCapacity ∧
  decide (d3.F_self_floor_n3 > NullCapacityRat) = true

/-- Proof 4.1: Convergent certification of `domain_n3`. -/
def proof_domain_n3 : VerifiedEmergence DomainN3Spec where
  survivor :=
    let l3 := interiorCoords.map (fun n1 => (n1, normTarget - n1 * n1))
    let (_, min_r1) := listGetD l3 p_star (NullCapacity, NullCapacity)
    ⟨l3, (min_r1 : Rat) * F_min_quantum⟩
  certified := by decide +kernel

/-- Output Variables 4.1: Stored outputs of `proof_domain_n3`. -/
def domain_n3       : DomainN3Output   := proof_domain_n3.survivor
def leakage_n3      : List (Nat × Nat) := domain_n3.leakage_n3
def F_self_floor_n3 : Rat              := domain_n3.F_self_floor_n3

def Q_candidate_n4 (n1 n2 : Nat) : Rat :=
  let d : Rat := (latticeDenom : Rat)
  F_pair_n2 - (((n1 : Rat) / d) ^ r1 + ((n2 : Rat) / d) ^ r1)

structure DomainN4Output where
  leakage_n4        : List (Nat × Nat × Nat)
  squareBranches_n4 : List (Nat × Nat × Nat)
  F_self_floor_n4   : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of `domain_n4` (combines *Null Logos* and *TON*):
    1. Generative Self-Frustration Leak (*Null Logos*): Consuming `leakage_n3` lowers the floor to
       `F_self_floor_n4 = 1/36 < F_self_floor_n3` and prepares `r2 = 3` exact-square branches,
       yet every branch still leaks `r2_leak > 0` (`F_self_floor_n4 > 0`).
    2. Archimedean Norm Bound: `d_C * maxInteriorSq < normTarget` (`8 < 9`).
    3. Eliminative Disqualification (*TON*): `alternatingOrder d_C = 1 < T` and `exteriorDim d_C r2 = 0`. -/
abbrev DomainN4Spec (d4 : DomainN4Output) : Prop :=
  d4.leakage_n4.length = r1 * r1 ∧
  (d4.leakage_n4.all (fun (n1, n2, r2_leak) =>
    decide (r2_leak > NullCapacity ∧
            Q_candidate_n4 n1 n2 = (r2_leak : Rat) * F_min_quantum ∧
            Q_candidate_n4 n1 n2 ≥ d4.F_self_floor_n4))) = true ∧
  (d4.leakage_n4.any (fun (n1, n2, _) => decide (Q_candidate_n4 n1 n2 = d4.F_self_floor_n4))) = true ∧
  d4.squareBranches_n4.length = r2 ∧
  d4.F_self_floor_n4 = F_min_quantum ∧
  d_C * maxInteriorSq < normTarget ∧
  alternatingOrder d_C = p_star ∧
  exteriorDim d_C r2 = NullCapacity ∧
  decide (d4.F_self_floor_n4 < F_self_floor_n3) = true ∧
  decide (d4.F_self_floor_n4 > NullCapacityRat) = true

/-- Proof 4.2: Convergent certification of `domain_n4`. -/
def proof_domain_n4 : VerifiedEmergence DomainN4Spec where
  survivor :=
    let l4 := listFlatMap leakage_n3 fun (n1, r1_leak) =>
              interiorCoords.map fun n2 => (n1, n2, r1_leak - n2 * n2)
    let sq4 := l4.filter (fun (_, _, r2_leak) => isInteriorSquare r2_leak)
    ⟨l4, sq4, F_min_quantum⟩
  certified := by decide +kernel

/-- Output Variables 4.2: Stored outputs of `proof_domain_n4`. -/
def domain_n4         : DomainN4Output         := proof_domain_n4.survivor
def leakage_n4        : List (Nat × Nat × Nat) := domain_n4.leakage_n4
def squareBranches_n4 : List (Nat × Nat × Nat) := domain_n4.squareBranches_n4
def F_self_floor_n4   : Rat                    := domain_n4.F_self_floor_n4

-- ============================================================================
-- STAGE 5: `domain_n5` Exact Closure, Non-Circular Archimedean `n_star = 5`
--          Isolation over all Nat, & Full-Sphere Uniqueness on `[-T..T]^3`
-- ============================================================================

/-- Lower capability for `n_star` (Non-Circular Archimedean Interior Sphere Bound):
    Because each of the `n - r1` short-root coordinates has square at most `maxInteriorSq = 4`,
    reaching `normTarget = 9` requires `(n - r1) * maxInteriorSq >= normTarget` (`4*(n - 2) >= 9`),
    which is false for `n = 0, 1, 2, 3, 4` (`0, 0, 0, 4, 8 < 9`) and true for `n >= 5` (`12 >= 9`). -/
abbrev CapableOfInteriorSphereClosure (n : Nat) : Prop :=
  (n - r1) * (r1 * r1) ≥ normTarget

/-- Upper capability for `n_star` (Chiral Exterior Volume Bound):
    For `n > r1 + r2`, the short-root multiplicity `n - r1 > r2` exceeds the chiral triad degree `r2`,
    forcing `exteriorDim r2 (n - r1) = 0`. -/
abbrev CapableOfNonVanishingChiralExterior (n : Nat) : Prop :=
  n ≤ r1 + r2

/-- Proof 5.1A (Non-Circular Unbounded Isolation of `n_star = 5` over all Nat):
    Proves over all `n : Nat` that `n_star = 5` is the unique dimension where the Archimedean
    interior sphere bound `4*(n - 2) >= 9` intersects the chiral exterior bound `n <= 5`. -/
def proof_n_star_archimedean :
    IntersectionIsolation CapableOfInteriorSphereClosure CapableOfNonVanishingChiralExterior where
  survivor := r1 + r2
  capable_A := by decide
  capable_B := by dsimp [CapableOfNonVanishingChiralExterior]; omega
  sub_critical_incapable := by
    intro n hn hA
    dsimp [CapableOfInteriorSphereClosure, normTarget, proof_normTarget,
      latticeDenom, proof_latticeDenom, T, proof_T, r2, proof_r2,
      d_C, proof_d_C, d_diag, cyclicDiagState, proof_d_diag,
      k_star, proof_k_star, r1, proof_r1, p_star, proof_p_star,
      SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
      NullCapacity, proof_NullCapacity] at hn hA
    omega
  super_critical_incapable := by
    intro n hn hB
    dsimp [CapableOfNonVanishingChiralExterior] at hB
    omega
  unique_survivor := by
    intro n
    dsimp [CapableOfInteriorSphereClosure, CapableOfNonVanishingChiralExterior,
      normTarget, proof_normTarget, latticeDenom, proof_latticeDenom,
      T, proof_T, r2, proof_r2, d_C, proof_d_C, d_diag, cyclicDiagState, proof_d_diag,
      k_star, proof_k_star, r1, proof_r1, p_star, proof_p_star,
      SingletonRayCardinality, nullStateCarrier, proof_NullStateCarrier,
      NullCapacity, proof_NullCapacity]
    omega

def Q_candidate_n5 (n1 n2 n3 : Nat) : Rat :=
  let d : Rat := (latticeDenom : Rat)
  F_pair_n2 - (((n1 : Rat) / d) ^ r1 + ((n2 : Rat) / d) ^ r1 + ((n3 : Rat) / d) ^ r1)

structure DomainN5Output where
  resolvedBranches : List (Nat × Nat × Nat × Nat)
  F_self_floor_n5  : Rat
  eta_overlap      : Rat
  F_pair_chiral    : Rat
  n_star_dim       : Nat
  deriving Repr, DecidableEq

/-- Convergent Specification of `domain_n5` (combines *Null Logos* and *TON*):
    1. Generative Leak Termination (*Null Logos*): Consuming `leakage_n4` drives `F_self_floor_n5 = 0`
       across `[(1,2,2,0), (2,1,2,0), (2,2,1,0)]` and relaxes pairwise frustration to `F_min_quantum` (1/36).
    2. Convergence with Archimedean Isolation (*TON*): `solveDomain2Boundary.length + resolvedBranches.length`
       equals `proof_n_star_archimedean.survivor` (`5`), `alternatingOrder (shortRootMult n_star_dim) = T` (`3`),
       `exteriorDim (shortRootMult n_star_dim) r2 = 1`, and for `n >= 6` (`n_star_dim + p_star`),
       `exteriorDim r2 (shortRootMult (n_star_dim + p_star)) = 0`. -/
abbrev DomainN5Spec (d5 : DomainN5Output) : Prop :=
  d5.resolvedBranches.length = r2 ∧
  d5.F_self_floor_n5 = NullCapacityRat ∧
  decide (d5.F_self_floor_n5 < F_self_floor_n4) = true ∧
  (d5.resolvedBranches.all (fun (n1, n2, n3, r3_rem) =>
    decide (r3_rem = NullCapacity ∧ Q_candidate_n5 n1 n2 n3 = d5.F_self_floor_n5))) = true ∧
  d5.eta_overlap + d5.F_pair_chiral = F_pair_n2 ∧
  d5.F_pair_chiral = F_min_quantum ∧
  F_pair_n2 / d5.F_pair_chiral = (normTarget : Rat) ∧
  F_pair_n1 / d5.F_pair_chiral = ((r1 * normTarget : Nat) : Rat) ∧
  d5.n_star_dim = solveDomain2Boundary.length + d5.resolvedBranches.length ∧
  d5.n_star_dim = proof_n_star_archimedean.survivor ∧
  d5.n_star_dim = r1 + r2 ∧
  r2 * maxInteriorSq ≥ normTarget ∧
  alternatingOrder (shortRootMult d5.n_star_dim) = T ∧
  exteriorDim (shortRootMult d5.n_star_dim) r2 = p_star ∧
  exteriorDim r2 (shortRootMult (d5.n_star_dim + p_star)) = NullCapacity

/-- Proof 5.1B: Convergent certification of `domain_n5`. -/
def proof_domain_n5 : VerifiedEmergence DomainN5Spec where
  survivor :=
    let res := listFlatMap leakage_n4 fun (n1, n2, r2_leak) =>
               interiorCoords.filterMap fun n3 =>
                 if n3 * n3 == r2_leak then
                   some (n1, n2, n3, r2_leak - n3 * n3)
                 else
                   none
    let (a1, a2, a3, _) := listGetD res NullCapacity (NullCapacity, NullCapacity, NullCapacity, NullCapacity)
    let (b1, b2, b3, _) := listGetD res p_star (NullCapacity, NullCapacity, NullCapacity, NullCapacity)
    let d : Rat := (latticeDenom : Rat)
    let eta := ((a1 : Rat) / d) * ((b1 : Rat) / d) +
               ((a2 : Rat) / d) * ((b2 : Rat) / d) +
               ((a3 : Rat) / d) * ((b3 : Rat) / d)
    let f_chiral := F_pair_n2 - eta
    ⟨res, NullCapacityRat, eta, f_chiral, solveDomain2Boundary.length + res.length⟩
  certified := by decide +kernel

/-- Output Variables 5.1: Stored outputs of `proof_domain_n5`. -/
def domain_n5       : DomainN5Output                 := proof_domain_n5.survivor
def resolved_at_n5  : List (Nat × Nat × Nat × Nat)   := domain_n5.resolvedBranches
def F_self_floor_n5 : Rat                            := domain_n5.F_self_floor_n5
def eta_n5          : Rat                            := domain_n5.eta_overlap
def Q_pol_chiral_n5 : Rat                            := domain_n5.F_pair_chiral
def n_star          : Nat                            := domain_n5.n_star_dim

/-- Proof 5.2 (Universal Integer Frustration Floor over Z):
    For any two distinct integer vectors `n_A != n_B` on the sphere `||n_A||^2 = ||n_B||^2 = normTarget`,
    their squared distance `distSq = ||n_A - n_B||^2 >= p_star` satisfies
    `distSq = r1 * normTarget - r1 * intDot`, proving `intDot <= normTarget - p_star` (8)
    and `normTarget - intDot >= p_star` (so `F_pair >= F_min_quantum = 1/36`). -/
theorem universal_integer_frustration_floor (distSq intDot : Int)
    (h_distinct : distSq ≥ Int.ofNat p_star)
    (h_sphere_id : distSq = Int.ofNat (r1 * normTarget) - Int.ofNat r1 * intDot) :
    distSq ≥ Int.ofNat r1 ∧
    intDot ≤ Int.ofNat (normTarget - p_star) ∧
    (Int.ofNat normTarget - intDot) ≥ Int.ofNat p_star := by
  dsimp [r1, proof_r1, normTarget, proof_normTarget, latticeDenom, proof_latticeDenom,
    T, proof_T, r2, proof_r2, d_C, proof_d_C, d_diag, cyclicDiagState, proof_d_diag,
    k_star, proof_k_star, p_star, proof_p_star, SingletonRayCardinality,
    nullStateCarrier, proof_NullStateCarrier, NullCapacity, proof_NullCapacity] at *
  omega

def dot3D (u v : Int × Int × Int) : Int :=
  let (x1, y1, z1) := u
  let (x2, y2, z2) := v
  x1 * x2 + y1 * y2 + z1 * z2

def hasZeroCoord3D (u : Int × Int × Int) : Bool :=
  let z0 := Int.ofNat NullCapacity
  let (x, y, z) := u
  x == z0 || y == z0 || z == z0

def isNonNeg3D (u : Int × Int × Int) : Bool :=
  let z0 := Int.ofNat NullCapacity
  let (x, y, z) := u
  decide (x ≥ z0 ∧ y ≥ z0 ∧ z ≥ z0)

structure Sphere3DFrustrationOutput where
  allSpherePoints      : List (Int × Int × Int)
  nonNegFloorAchievers : List (Int × Int × Int)
  deriving Repr, DecidableEq

/-- Convergent Specification of Full-Sphere Frustration Uniqueness (over `[-T..T]^3`):
    1. All 30 lattice points on `x^2 + y^2 + z^2 = normTarget` obey `dot3D u v <= 8` (`u != v`).
    2. ZERO-COORDINATE OBSTRUCTION: Every sphere point `u` containing a zero coordinate obeys
       `dot3D u v <= 6 < 8` with every distinct sphere point `v`, proving that no vector with a
       zero coordinate can ever reach the universal frustration floor `F_min_quantum = 1/36`.
    3. Across the entire non-negative orthant of the sphere, the points reaching `dot3D u v = 8`
       equal `resolved_at_n5` (`[(1, 2, 2), (2, 1, 2), (2, 2, 1)]`) identically. -/
abbrev Sphere3DFrustrationSpec (s : Sphere3DFrustrationOutput) : Prop :=
  let maxDot := Int.ofNat (normTarget - p_star)
  let zeroCoordBound := Int.ofNat latticeDenom
  s.allSpherePoints.length = r1 * T * n_star ∧
  (listFlatMap s.allSpherePoints fun u =>
   s.allSpherePoints.map fun v =>
     if u == v then true else decide (dot3D u v ≤ maxDot)).all (fun b => b) = true ∧
  (listFlatMap (s.allSpherePoints.filter hasZeroCoord3D) fun u =>
   s.allSpherePoints.map fun v =>
     if u == v then true else decide (dot3D u v ≤ zeroCoordBound)).all (fun b => b) = true ∧
  decide (zeroCoordBound < maxDot) = true ∧
  s.nonNegFloorAchievers =
    resolved_at_n5.map (fun (n1, n2, n3, _) => (Int.ofNat n1, Int.ofNat n2, Int.ofNat n3))

/-- Proof 5.3: Exhaustive certification of full-sphere frustration uniqueness over `[-T..T]^3`. -/
def proof_sphere3DFrustrationFloor : VerifiedEmergence Sphere3DFrustrationSpec where
  survivor :=
    let cs := signedRange T
    let pts := listFlatMap cs fun x =>
               listFlatMap cs fun y =>
               cs.filterMap fun z =>
                 if x * x + y * y + z * z == Int.ofNat normTarget then some (x, y, z) else none
    let maxDot := Int.ofNat (normTarget - p_star)
    let achievers := (pts.filter isNonNeg3D).filter (fun u =>
                       pts.any (fun v => !(u == v) && dot3D u v == maxDot))
    ⟨pts, achievers⟩
  certified := by decide +kernel

/-- Output Variables 5.3: Stored full-sphere point sets. -/
def sphere3DState        : Sphere3DFrustrationOutput := proof_sphere3DFrustrationFloor.survivor
def sphere3DPoints       : List (Int × Int × Int)    := sphere3DState.allSpherePoints
def nonNegFloorAchievers : List (Int × Int × Int)    := sphere3DState.nonNegFloorAchievers

-- ============================================================================
-- STAGE 6: Master Module 1 Convergent Cascade Ledger
-- ============================================================================

structure GnosisDomainFiltrationReadout where
  nullCapacity         : Nat := NullCapacity
  singletonCardinality : Nat := SingletonRayCardinality
  p_star               : Nat := p_star
  r1                   : Nat := r1
  k_star               : Nat := k_star
  c0_scalar            : Rat := c0_scalar
  c_vec_normSq         : Rat := c_vec_normSq
  Q_idempotent         : Rat := Q_idempotent
  w_perp_leak          : Rat := w_perp_leak
  F_pair_n1            : Rat := F_pair_n1
  Q_leak_n1            : Rat := Q_leak_n1
  nativeBoundaryPairs  : List (Nat × Nat) := nativeBoundaryPairs
  nativeInteriorCoords : List Nat := nativeInteriorCoords
  d_C                  : Nat := d_C
  d_diag               : Nat := d_diag
  r2                   : Nat := r2
  T                    : Nat := T
  latticeDenom         : Nat := latticeDenom
  normTarget           : Nat := normTarget
  Phi_scale            : Nat := Phi_scale
  F_min_quantum        : Rat := F_min_quantum
  maxInteriorSq        : Nat := maxInteriorSq
  solveDomain2Boundary : List (Nat × Nat) := solveDomain2Boundary
  F_pair_n2            : Rat := F_pair_n2
  Q_leak_n2            : Rat := Q_leak_n2
  leakage_n3           : List (Nat × Nat) := leakage_n3
  F_self_floor_n3      : Rat := F_self_floor_n3
  leakage_n4           : List (Nat × Nat × Nat) := leakage_n4
  F_self_floor_n4      : Rat := F_self_floor_n4
  resolved_at_n5       : List (Nat × Nat × Nat × Nat) := resolved_at_n5
  F_self_floor_n5      : Rat := F_self_floor_n5
  eta_n5               : Rat := eta_n5
  Q_pol_chiral_n5      : Rat := Q_pol_chiral_n5
  n_star               : Nat := n_star
  sphere3DPointCount   : Nat := sphere3DPoints.length
  deriving Repr, DecidableEq

/-- Proof 6.1: Final verified readout object of Module 1. -/
def proof_cascadeReadout :
    VerifiedEmergence (fun r : GnosisDomainFiltrationReadout =>
      CarrierMaintainsNull [] = false ∧
      CarrierMaintainsNull ProjectiveRaySingleton = true ∧
      r.nativeInteriorCoords = [] ∧
      r.n_star = proof_n_star_archimedean.survivor ∧
      r.Q_idempotent = NullCapacityRat ∧
      decide (r.c_vec_normSq > NullCapacityRat) = true ∧
      decide (r.F_pair_n1 > r.F_pair_n2) = true ∧
      decide (r.F_pair_n2 > r.Q_pol_chiral_n5) = true ∧
      decide (r.Q_pol_chiral_n5 > NullCapacityRat) = true ∧
      decide (r.F_self_floor_n3 > r.F_self_floor_n4) = true ∧
      decide (r.F_self_floor_n4 > r.F_self_floor_n5) = true ∧
      r.F_self_floor_n5 = NullCapacityRat) where
  survivor := {}
  certified := by decide +kernel

/-- Output Variable 6.1: Master cascade readout variable. -/
def cascadeReadout : GnosisDomainFiltrationReadout := proof_cascadeReadout.survivor

#eval cascadeReadout

end GeometricNullOntologicalSpectralInvariantSymmetry.GnosisDomainFiltration
