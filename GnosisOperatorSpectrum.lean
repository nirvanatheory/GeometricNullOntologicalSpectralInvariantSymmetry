/-
  GeometricNullOntologicalSpectralInvariantSymmetry — GnosisOperatorSpectrum.lean (Module 2)
  Master Convergent Proof-to-Variable Cascade: V_5 Frame, Adjugate Gram Inverse, & Operator Spectrum
  Verification Engine: Lean 4 (v4.28.0), zero axioms, zero sorrys, zero external dependencies.

  Strict Architectural & Mathematical Rules:
  1. Zero Numeric Literals & Zero Constructors: No digits (`0..9`) and no `Nat.zero` or `Nat.succ`
     constructors appear anywhere in this module; every input is a certified `.survivor` variable
     inherited from `GnosisDomainFiltration.lean` or a preceding proof structure in this file.
  2. 100% `.survivor` Encapsulation: Every vector, identity element, orthonormal basis frame,
     signed spatial trace, matrix inverse entry, and operator invariant is declared exclusively
     as the `.survivor` output of a `VerifiedEmergence` proof structure.
  3. Multi-Proof Convergence at Every Stage:
     - Stage 1 (`proof_FrustrationQuanta`): Certifies the Frustration Partition Law
       `eta_quantum + F_min = F_split` and locks the four fundamental quanta (`1/36`, `2/9`, `1/4`, `17/36`).
     - Stage 2 (`proof_V5OrthonormalFrame`): Certifies `Vec5.zero`, `V5.zero`, `V5.e`, the 6D frame
       `v5OrthonormalBasis`, the 5D spatial frame `spatialOrthonormalBasis`, the 36-pair Lorentzian/Jordan
       orthonormality identities, and the signed spatial traces (`euclideanSpatialTrace = +5`,
       `lorentzianSpatialTrace = -5`).
     - Stage 3 (`proof_V5BasisState`): Synthesizes `V_5 = Q e ⊕ Q^5`, proves equivalence of the
       native `(1/2)Z^2` and refined `(1/6)Z^2` split-Cartan pairs, and proves the 25-pair
       Frustration-Overlap Partition Identity across all generators.
     - Stage 4 (`proof_GramSpectrumState`): Proves the chiral Gram spectrum and `1836` baryon core
       via three convergent methods: (A) spectral eigenvalues (`1/36`, `25/36`), (B) explicit 3x3
       adjugate matrix inverse `G_short * G_short^(-1) = I_3` (`gInvDiag = 612/25`, `gInvOff = -288/25`),
       and (C) frustration quantum factorization (`51 * 36 = 1836`).
     - Stage 5 (`proof_OperatorSpectrumState`): Proves the sector norms, longitudinal operator
       pencils, 6D trace vs. difference-of-squares inner derivation curvature (`17/1296`),
       triad derivation sum (`25/216`), Bergman polynomial (`-275/36`), and Koszul-Vinberg moduli.
-/

import GnosisDomainFiltration

namespace GeometricNullOntologicalSpectralInvariantSymmetry.GnosisOperatorSpectrum

open GeometricNullOntologicalSpectralInvariantSymmetry.GnosisDomainFiltration

-- ============================================================================
-- STAGE 1: Proof-to-Variable Isolation of the Four Fundamental Frustration Quanta
-- ============================================================================

structure FrustrationQuantaOutput where
  F_min           : Rat
  Phi_inv         : Rat
  F_split         : Rat
  eta_quantum     : Rat
  overlapQuanta   : Nat
  traceQuanta     : Nat
  tau_chiral_pair : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of the Frustration Partition Law:
    - `F_min` is the universal chiral pairwise frustration floor `Q_pol_chiral_n5` (1/36),
    - `Phi_inv` is the reciprocal frustration scale `Phi_scale` (36),
    - `F_split` is the orthogonal split-Cartan frustration `F_pair_n2` (9 * F_min = 1/4),
    - `eta_quantum` is the chiral overlap `eta_n5` (`overlapQuanta * F_min = 8/36 = 2/9`),
    - `tau_chiral_pair` is the chiral Jordan trace (`traceQuanta * F_min = 17/36`). -/
abbrev FrustrationQuantaSpec (q : FrustrationQuantaOutput) : Prop :=
  q.F_min = F_min_quantum ∧
  q.F_min = Q_pol_chiral_n5 ∧
  q.Phi_inv = (Phi_scale : Rat) ∧
  q.F_min * q.Phi_inv = (k_star : Rat) ∧
  q.F_split = F_pair_n2 ∧
  q.F_split = (normTarget : Rat) * q.F_min ∧
  q.eta_quantum = eta_n5 ∧
  q.overlapQuanta + p_star = normTarget ∧
  q.eta_quantum = (q.overlapQuanta : Rat) * q.F_min ∧
  q.eta_quantum + q.F_min = q.F_split ∧
  q.traceQuanta = normTarget + q.overlapQuanta ∧
  q.tau_chiral_pair = q.F_split + q.eta_quantum ∧
  q.tau_chiral_pair = (q.traceQuanta : Rat) * q.F_min ∧
  q.tau_chiral_pair + q.F_min = (r1 : Rat) * q.F_split

/-- Proof 1.1: Certification of the four fundamental frustration quanta. -/
def proof_FrustrationQuanta : VerifiedEmergence FrustrationQuantaSpec where
  survivor :=
    let ovQ := normTarget - p_star
    let trQ := normTarget + ovQ
    ⟨Q_pol_chiral_n5, (Phi_scale : Rat), F_pair_n2, eta_n5, ovQ, trQ, F_pair_n2 + eta_n5⟩
  certified := by decide +kernel

/-- Output Variables 1.1: Stored outputs of `proof_FrustrationQuanta`. -/
def frustrationQuanta : FrustrationQuantaOutput := proof_FrustrationQuanta.survivor
def F_min             : Rat                     := frustrationQuanta.F_min
def Phi_inv           : Rat                     := frustrationQuanta.Phi_inv
def F_split           : Rat                     := frustrationQuanta.F_split
def eta_quantum       : Rat                     := frustrationQuanta.eta_quantum
def overlapQuanta     : Nat                     := frustrationQuanta.overlapQuanta
def traceQuanta       : Nat                     := frustrationQuanta.traceQuanta
def tau_chiral_pair   : Rat                     := frustrationQuanta.tau_chiral_pair

-- ============================================================================
-- STAGE 2: Proof-to-Variable Certification of the 6D Orthonormal Frame
--          & Signed Euclidean/Lorentzian Spatial Traces (+5 vs. -5)
-- ============================================================================

structure Vec5 where
  x1 : Rat
  x2 : Rat
  x3 : Rat
  x4 : Rat
  x5 : Rat
  deriving Repr, DecidableEq

structure V5 where
  x0  : Rat
  vec : Vec5
  deriving Repr, DecidableEq

namespace Vec5

def add (u v : Vec5) : Vec5 :=
  ⟨u.x1 + v.x1, u.x2 + v.x2, u.x3 + v.x3, u.x4 + v.x4, u.x5 + v.x5⟩

def sub (u v : Vec5) : Vec5 :=
  ⟨u.x1 - v.x1, u.x2 - v.x2, u.x3 - v.x3, u.x4 - v.x4, u.x5 - v.x5⟩

def neg (u : Vec5) : Vec5 :=
  ⟨-u.x1, -u.x2, -u.x3, -u.x4, -u.x5⟩

def smul (c : Rat) (u : Vec5) : Vec5 :=
  ⟨c * u.x1, c * u.x2, c * u.x3, c * u.x4, c * u.x5⟩

def dot (u v : Vec5) : Rat :=
  u.x1 * v.x1 + u.x2 * v.x2 + u.x3 * v.x3 + u.x4 * v.x4 + u.x5 * v.x5

def normSq (u : Vec5) : Rat := dot u u

end Vec5

namespace V5

def add (X Y : V5) : V5 := ⟨X.x0 + Y.x0, Vec5.add X.vec Y.vec⟩
def sub (X Y : V5) : V5 := ⟨X.x0 - Y.x0, Vec5.sub X.vec Y.vec⟩
def smul (c : Rat) (X : V5) : V5 := ⟨c * X.x0, Vec5.smul c X.vec⟩
def conj (X : V5) : V5 := ⟨X.x0, Vec5.neg X.vec⟩

def jmul (X Y : V5) : V5 :=
  ⟨X.x0 * Y.x0 + Vec5.dot X.vec Y.vec,
   Vec5.add (Vec5.smul X.x0 Y.vec) (Vec5.smul Y.x0 X.vec)⟩

def jtr (X : V5) : Rat := (r1 : Rat) * X.x0
def tau (X Y : V5) : Rat := (jmul X Y).x0
def Q (X : V5) : Rat := X.x0 * X.x0 - Vec5.normSq X.vec
def Q_pol (X Y : V5) : Rat := X.x0 * Y.x0 - Vec5.dot X.vec Y.vec
def jinv (X : V5) : V5 := smul ((k_star : Rat) / Q X) (conj X)

end V5

open Vec5 V5

structure V5OrthonormalFrameOutput where
  vec5_zero              : Vec5
  v5_zero                : V5
  v5_e                   : V5
  b0                     : V5
  b1                     : V5
  b2                     : V5
  b3                     : V5
  b4                     : V5
  b5                     : V5
  basis6D                : List V5
  spatialBasis           : List V5
  euclideanSpatialTrace  : Rat
  lorentzianSpatialTrace : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of the 6D Lorentzian/Jordan Frame & Signed Spatial Traces:
    1. `basis6D = [b0, b1, b2, b3, b4, b5]` has length `p_star + n_star` (6), and
       `spatialBasis = [b1, b2, b3, b4, b5]` has length `n_star` (5).
    2. `v5_zero` is the additive identity and `v5_e = b0` is the Jordan multiplicative identity.
    3. Across all 36 pairs `(i, j)` of `basis6D`, `tau b_i b_j = delta_{ij}` (`I_6`) and
       `Q_pol b_i b_j = diag(+1, -1, -1, -1, -1, -1)` of exact signature `(p_star, n_star) = (1, 5)`.
    4. SIGNED SPATIAL TRACE LOCK: Summing `tau b b` over `spatialBasis` yields
       `euclideanSpatialTrace = +5`, while summing `Q b` over `spatialBasis` yields
       `lorentzianSpatialTrace = -5`, with `euclideanSpatialTrace + lorentzianSpatialTrace = 0`. -/
abbrev V5OrthonormalFrameSpec (f : V5OrthonormalFrameOutput) : Prop :=
  f.basis6D = [f.b0, f.b1, f.b2, f.b3, f.b4, f.b5] ∧
  f.basis6D.length = p_star + n_star ∧
  f.spatialBasis = [f.b1, f.b2, f.b3, f.b4, f.b5] ∧
  f.spatialBasis.length = n_star ∧
  f.v5_e = f.b0 ∧
  jtr f.v5_e = (r1 : Rat) ∧
  Q f.b0 = (k_star : Rat) ∧
  (f.spatialBasis.all (fun b =>
    decide (b.x0 = NullCapacityRat ∧ Q b = -(k_star : Rat) ∧ tau b b = (k_star : Rat)))) = true ∧
  (f.basis6D.all (fun b =>
    decide (V5.add f.v5_zero b = b ∧ V5.jmul f.v5_e b = b))) = true ∧
  f.euclideanSpatialTrace = f.spatialBasis.foldl (fun acc b => acc + tau b b) NullCapacityRat ∧
  f.euclideanSpatialTrace = (n_star : Rat) ∧
  f.lorentzianSpatialTrace = f.spatialBasis.foldl (fun acc b => acc + Q b) NullCapacityRat ∧
  f.lorentzianSpatialTrace = -(n_star : Rat) ∧
  f.euclideanSpatialTrace + f.lorentzianSpatialTrace = NullCapacityRat ∧
  (listFlatMap (List.range f.basis6D.length) fun i =>
   (List.range f.basis6D.length).map fun j =>
     let bi := listGetD f.basis6D i f.v5_zero
     let bj := listGetD f.basis6D j f.v5_zero
     let expectedTau := if i == j then (k_star : Rat) else NullCapacityRat
     let expectedQ   := if i == j then (if i == NullCapacity then (k_star : Rat) else -(k_star : Rat))
                        else NullCapacityRat
     decide (tau bi bj = expectedTau ∧ Q_pol bi bj = expectedQ)).all (fun ok => ok) = true

/-- Proof 2.1: Certification of the 6D orthonormal frame and signed spatial traces of V_5. -/
def proof_V5OrthonormalFrame : VerifiedEmergence V5OrthonormalFrameSpec where
  survivor :=
    let z0 := NullCapacityRat
    let u1 := (k_star : Rat)
    let vz5 : Vec5 := ⟨z0, z0, z0, z0, z0⟩
    let vz  : V5   := ⟨z0, vz5⟩
    let e0  : V5   := ⟨u1, vz5⟩
    let e1  : V5   := ⟨z0, ⟨u1, z0, z0, z0, z0⟩⟩
    let e2  : V5   := ⟨z0, ⟨z0, u1, z0, z0, z0⟩⟩
    let e3  : V5   := ⟨z0, ⟨z0, z0, u1, z0, z0⟩⟩
    let e4  : V5   := ⟨z0, ⟨z0, z0, z0, u1, z0⟩⟩
    let e5  : V5   := ⟨z0, ⟨z0, z0, z0, z0, u1⟩⟩
    let b6  : List V5 := [e0, e1, e2, e3, e4, e5]
    let sp5 : List V5 := [e1, e2, e3, e4, e5]
    let eucTr := sp5.foldl (fun acc b => acc + tau b b) z0
    let lorTr := sp5.foldl (fun acc b => acc + Q b) z0
    ⟨vz5, vz, e0, e0, e1, e2, e3, e4, e5, b6, sp5, eucTr, lorTr⟩
  certified := by decide +kernel

/-- Output Variables 2.1: Stored identity elements, frames, and signed spatial traces. -/
def v5FrameState           : V5OrthonormalFrameOutput := proof_V5OrthonormalFrame.survivor
def Vec5.zero              : Vec5                     := v5FrameState.vec5_zero
def V5.zero                : V5                       := v5FrameState.v5_zero
def V5.e                   : V5                       := v5FrameState.v5_e
def b0                     : V5                       := v5FrameState.b0
def b1                     : V5                       := v5FrameState.b1
def b2                     : V5                       := v5FrameState.b2
def b3                     : V5                       := v5FrameState.b3
def b4                     : V5                       := v5FrameState.b4
def b5                     : V5                       := v5FrameState.b5
def v5OrthonormalBasis     : List V5                  := v5FrameState.basis6D
def spatialOrthonormalBasis : List V5                 := v5FrameState.spatialBasis
def euclideanSpatialTrace  : Rat                      := v5FrameState.euclideanSpatialTrace
def lorentzianSpatialTrace : Rat                      := v5FrameState.lorentzianSpatialTrace

-- ============================================================================
-- STAGE 3: Proof-to-Variable Synthesis of V_5 Generator Basis & Sector Ensembles
-- ============================================================================

def mkChiralFromResolved (q : Nat × Nat × Nat × Nat) : V5 :=
  let d : Rat := (latticeDenom : Rat)
  let (n1, n2, n3, _) := q
  ⟨c0_scalar, ⟨(n1 : Rat) / d, (n2 : Rat) / d, (n3 : Rat) / d, NullCapacityRat, NullCapacityRat⟩⟩

def mkSplitFromBoundary (p : Nat × Nat) : V5 :=
  let d : Rat := (latticeDenom : Rat)
  let (n4, n5) := p
  ⟨c0_scalar, ⟨NullCapacityRat, NullCapacityRat, NullCapacityRat, (n4 : Rat) / d, (n5 : Rat) / d⟩⟩

def mkSplitFromNative (p : Nat × Nat) : V5 :=
  let d : Rat := (r1 : Rat)
  let (m4, m5) := p
  ⟨c0_scalar, ⟨NullCapacityRat, NullCapacityRat, NullCapacityRat, (m4 : Rat) / d, (m5 : Rat) / d⟩⟩

structure V5BasisOutput where
  chiralBasis : List V5
  splitBasis  : List V5
  allBasis5   : List V5
  c0          : V5
  c1          : V5
  c2          : V5
  s0          : V5
  s1          : V5
  X_short     : V5
  X_split     : V5
  X_total     : V5
  deriving Repr, DecidableEq

/-- Convergent Specification of the V_5 Generator Basis & 25-Pair Partition Identity:
    1. `chiralBasis` has length `r2` (3), `splitBasis` has length `r1` (2), and `allBasis5` has length `n_star` (5).
    2. `splitBasis` synthesized from `solveDomain2Boundary` on `(1/6)Z^2` equals `nativeBoundaryPairs.map mkSplitFromNative`
       on `(1/2)Z^2` identically.
    3. Every synthesized generator is a primitive null idempotent (`g o g = g`, `tr = k_star`, `Q = 0`).
    4. Universal 25-Pair Frustration-Overlap Partition Identity across all `(g1, g2)` in `allBasis5^2`:
       `Vec5.dot g1.vec g2.vec + Q_pol g1 g2 = F_split` and `tau g1 g2 + Q_pol g1 g2 = r1 * F_split`. -/
abbrev V5BasisSpec (b : V5BasisOutput) : Prop :=
  b.chiralBasis.length = r2 ∧
  b.splitBasis.length = r1 ∧
  b.splitBasis = nativeBoundaryPairs.map mkSplitFromNative ∧
  b.allBasis5 = b.chiralBasis ++ b.splitBasis ∧
  b.allBasis5.length = n_star ∧
  (b.allBasis5.all (fun g =>
    decide (jmul g g = g ∧ jtr g = (k_star : Rat) ∧ Q g = NullCapacityRat))) = true ∧
  (listFlatMap b.allBasis5 fun g1 =>
   b.allBasis5.map fun g2 =>
     decide (Vec5.dot g1.vec g2.vec + Q_pol g1 g2 = F_split ∧
             tau g1 g2 + Q_pol g1 g2 = (r1 : Rat) * F_split)).all (fun ok => ok) = true ∧
  Vec5.dot b.c0.vec b.c1.vec = eta_quantum ∧
  Q_pol b.c0 b.c1 = F_min ∧
  tau b.c0 b.c1 = tau_chiral_pair ∧
  Vec5.dot b.s0.vec b.s1.vec = NullCapacityRat ∧
  Q_pol b.s0 b.s1 = F_split ∧
  Vec5.dot b.c0.vec b.s0.vec = NullCapacityRat ∧
  b.X_short = b.chiralBasis.foldl V5.add V5.zero ∧
  b.X_split = b.splitBasis.foldl V5.add V5.zero ∧
  b.X_total = V5.add b.X_short b.X_split

/-- Proof 3.1: Certification of the V_5 basis synthesized from `resolved_at_n5` and `solveDomain2Boundary`. -/
def proof_V5BasisState : VerifiedEmergence V5BasisSpec where
  survivor :=
    let cb := resolved_at_n5.map mkChiralFromResolved
    let sb := solveDomain2Boundary.map mkSplitFromBoundary
    let all5 := cb ++ sb
    let c0 := listGetD cb NullCapacity V5.zero
    let c1 := listGetD cb p_star V5.zero
    let c2 := listGetD cb r1 V5.zero
    let s0 := listGetD sb NullCapacity V5.zero
    let s1 := listGetD sb p_star V5.zero
    let xsh := cb.foldl V5.add V5.zero
    let xsp := sb.foldl V5.add V5.zero
    let xtot := V5.add xsh xsp
    ⟨cb, sb, all5, c0, c1, c2, s0, s1, xsh, xsp, xtot⟩
  certified := by decide +kernel

/-- Output Variables 3.1: Stored outputs of `proof_V5BasisState`. -/
def v5BasisState : V5BasisOutput := proof_V5BasisState.survivor
def chiralBasis  : List V5       := v5BasisState.chiralBasis
def splitBasis   : List V5       := v5BasisState.splitBasis
def allBasis5    : List V5       := v5BasisState.allBasis5
def c_gen_0      : V5            := v5BasisState.c0
def c_gen_1      : V5            := v5BasisState.c1
def c_gen_2      : V5            := v5BasisState.c2
def s_gen_0      : V5            := v5BasisState.s0
def s_gen_1      : V5            := v5BasisState.s1
def X_short      : V5            := v5BasisState.X_short
def X_split      : V5            := v5BasisState.X_split
def X_total      : V5            := v5BasisState.X_total

def c_gen (i : Nat) : V5 := listGetD chiralBasis i V5.zero
def s_gen (i : Nat) : V5 := listGetD splitBasis i V5.zero

-- ============================================================================
-- STAGE 4: Three-Way Convergent Proof of the Chiral Gram Spectrum, Explicit 3x3
--          Adjugate Inverse `G_short * G_short^(-1) = I_3`, & `1836` Baryon Core
-- ============================================================================

def det2 (a11 a12 a21 a22 : Rat) : Rat := a11 * a22 - a12 * a21

def det3 (a11 a12 a13 a21 a22 a23 a31 a32 a33 : Rat) : Rat :=
  a11 * (a22 * a33 - a23 * a32) -
  a12 * (a21 * a33 - a23 * a31) +
  a13 * (a21 * a32 - a22 * a31)

structure GramSpectrumOutput where
  lambda_perp_G    : Rat
  lambda_par_G     : Rat
  anisotropyRatio  : Rat
  det_C_short      : Rat
  det_C_split      : Rat
  det_C            : Rat
  det_G_short      : Rat
  gInvDiag         : Rat
  gInvOff          : Rat
  baryonCoreQuanta : Nat
  tr_G_short_inv   : Rat
  M_minus1_core    : Rat
  deriving Repr, DecidableEq

/-- Three-Way Convergent Specification of the Chiral Gram Spectrum & `1836` Baryon Core:
    1. Spectral Proof (*Null Logos*): `lambda_perp_G = F_min` (1/36), `lambda_par_G = n_star^2 * F_min` (25/36),
       `anisotropyRatio = n_star^2` (25), and `tr_G_short_inv = 1/lambda_par_G + 2/lambda_perp_G` (1836/25).
    2. Explicit 3x3 Adjugate Matrix Inverse Proof (*Cartan Trilogy*):
       - Diagonal cofactor divided by `det_G_short` yields `gInvDiag = 612/25`;
       - Off-diagonal cofactor divided by `det_G_short` yields `gInvOff = -288/25`;
       - Exact matrix product `G_short * G_short^(-1) = I_3`:
         `F_split * gInvDiag + r1 * eta_quantum * gInvOff = k_star` (1) and
         `F_split * gInvOff + eta_quantum * gInvDiag + eta_quantum * gInvOff = NullCapacityRat` (0);
       - Exact matrix trace agreement: `r2 * gInvDiag = tr_G_short_inv` (1836/25).
    3. Frustration Quantum Factorization (*Null Logos*):
       `baryonCoreQuanta = r1 * n_star^2 + p_star = r2 * traceQuanta` (51), and
       `M_minus1_core = anisotropyRatio * tr_G_short_inv = baryonCoreQuanta * Phi_inv` (1836). -/
abbrev GramSpectrumSpec (g : GramSpectrumOutput) : Prop :=
  g.lambda_perp_G = F_min ∧
  g.lambda_par_G = ((n_star * n_star : Nat) : Rat) * F_min ∧
  g.anisotropyRatio = g.lambda_par_G / g.lambda_perp_G ∧
  g.anisotropyRatio = ((n_star * n_star : Nat) : Rat) ∧
  g.det_G_short = g.det_C_short * g.det_C_short ∧
  g.det_G_short = g.lambda_par_G * (g.lambda_perp_G ^ r1) ∧
  g.det_G_short = ((n_star * n_star : Nat) : Rat) * (F_min ^ r2) ∧
  g.det_C_split = F_split ∧
  g.det_C = g.det_C_short * g.det_C_split ∧
  F_split * g.gInvDiag + (r1 : Rat) * eta_quantum * g.gInvOff = (k_star : Rat) ∧
  F_split * g.gInvOff + eta_quantum * g.gInvDiag + eta_quantum * g.gInvOff = NullCapacityRat ∧
  (r2 : Rat) * g.gInvDiag = g.tr_G_short_inv ∧
  g.baryonCoreQuanta = r1 * n_star * n_star + p_star ∧
  g.baryonCoreQuanta = r2 * traceQuanta ∧
  g.tr_G_short_inv = ((k_star : Rat) / g.lambda_par_G) + (r1 : Rat) * ((k_star : Rat) / g.lambda_perp_G) ∧
  g.tr_G_short_inv = ((g.baryonCoreQuanta : Rat) / g.anisotropyRatio) * Phi_inv ∧
  g.M_minus1_core = g.anisotropyRatio * g.tr_G_short_inv ∧
  g.M_minus1_core = (g.baryonCoreQuanta : Rat) * Phi_inv

/-- Proof 4.1: Three-way convergent certification of the chiral Gram spectrum and `1836` core. -/
def proof_GramSpectrumState : VerifiedEmergence GramSpectrumSpec where
  survivor :=
    let g_ii   := Vec5.normSq c_gen_0.vec
    let g_ij   := Vec5.dot c_gen_0.vec c_gen_1.vec
    let l_perp := g_ii - g_ij
    let l_par  := g_ii + (r1 : Rat) * g_ij
    let aniso  := l_par / l_perp
    let raw_sh := det3 c_gen_0.vec.x1 c_gen_0.vec.x2 c_gen_0.vec.x3
                       c_gen_1.vec.x1 c_gen_1.vec.x2 c_gen_1.vec.x3
                       c_gen_2.vec.x1 c_gen_2.vec.x2 c_gen_2.vec.x3
    let det_sh := if decide (raw_sh < NullCapacityRat) then -raw_sh else raw_sh
    let raw_sp := det2 s_gen_0.vec.x4 s_gen_0.vec.x5 s_gen_1.vec.x4 s_gen_1.vec.x5
    let det_sp := if decide (raw_sp < NullCapacityRat) then -raw_sp else raw_sp
    let det_c  := det_sh * det_sp
    let det_g  := det_sh * det_sh
    let cof_diag := det2 g_ii g_ij g_ij g_ii
    let cof_off  := det2 g_ij g_ii g_ij g_ij
    let inv_diag := cof_diag / det_g
    let inv_off  := cof_off / det_g
    let b_quanta := r1 * n_star * n_star + p_star
    let tr_inv := ((k_star : Rat) / l_par) + (r1 : Rat) * ((k_star : Rat) / l_perp)
    let m_core := aniso * tr_inv
    ⟨l_perp, l_par, aniso, det_sh, det_sp, det_c, det_g, inv_diag, inv_off, b_quanta, tr_inv, m_core⟩
  certified := by decide +kernel

/-- Output Variables 4.1: Stored outputs of `proof_GramSpectrumState`. -/
def gramSpectrumState : GramSpectrumOutput := proof_GramSpectrumState.survivor
def lambda_perp_G     : Rat                := gramSpectrumState.lambda_perp_G
def lambda_par_G      : Rat                := gramSpectrumState.lambda_par_G
def anisotropyRatio   : Rat                := gramSpectrumState.anisotropyRatio
def det_C_short       : Rat                := gramSpectrumState.det_C_short
def det_C_split       : Rat                := gramSpectrumState.det_C_split
def det_C             : Rat                := gramSpectrumState.det_C
def det_G_short       : Rat                := gramSpectrumState.det_G_short
def gInvDiag          : Rat                := gramSpectrumState.gInvDiag
def gInvOff           : Rat                := gramSpectrumState.gInvOff
def baryonCoreQuanta  : Nat                := gramSpectrumState.baryonCoreQuanta
def tr_G_short_inv    : Rat                := gramSpectrumState.tr_G_short_inv
def M_minus1_core     : Rat                := gramSpectrumState.M_minus1_core

-- ============================================================================
-- STAGE 5: Proof-to-Variable Isolation of V_5 Operators, Derivations, & Moduli
-- ============================================================================

def trace6D (F : V5 → V5) : Rat :=
  v5OrthonormalBasis.foldl (fun acc b => acc + tau b (F b)) NullCapacityRat

def L_op (X Y : V5) : V5 := jmul X Y
def P_op (X Y : V5) : V5 := V5.sub (V5.smul (r1 : Rat) (L_op X (L_op X Y))) (L_op (jmul X X) Y)
def D_op (X Y Z : V5) : V5 := V5.sub (L_op X (L_op Y Z)) (L_op Y (L_op X Z))

def omegaSq (U V : V5) : Rat := -c0_scalar * trace6D (fun Z => D_op U V (D_op U V Z))
def secCurvature (U V : V5) : Rat := -omegaSq U V / (tau U U * tau V V - (tau U V) ^ r1)
def h_poly (X Y : V5) : Rat := (k_star : Rat) - (r1 : Rat) * tau X Y + Q X * Q Y
def g_KV (X U V : V5) : Rat := tau (P_op (jinv X) U) V

structure OperatorSpectrumOutput where
  Q_short_val          : Rat
  Q_split_val          : Rat
  det_J_Pi2            : Rat
  det_M_Pi2            : Rat
  det_J_par            : Rat
  det_M_par            : Rat
  tr_M_par             : Rat
  omegaSq_chiral_pair  : Rat
  secCurv_chiral_pair  : Rat
  chiralDerivationSum  : Rat
  h_poly_short         : Rat
  Q_pol_total_chiral   : Rat
  Q_pol_total_split    : Rat
  mu_1_frust           : Rat
  mu_2_frust           : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of the V_5 Operator Spectrum:
    1. `Q(X_short) = latticeDenom * F_min` (1/6) and `Q(X_split) = (r1 * normTarget) * F_min` (1/2).
    2. `tr_M_par = (r1 + normTarget) * F_min` (11/36), `det_M_par = -(normTarget + d_C * r1) * F_min` (-13/36),
       and `det_J_par = (baryonCoreQuanta * c0_scalar) * F_min` (17/24).
    3. Convergent Inner Derivation Curvature: `omegaSq(c_0, c_1)` computed via 6D operator trace
       equals both `(F_split - eta_quantum) * (F_split + eta_quantum)` and `F_min * tau_chiral_pair` (17/1296).
    4. `h_poly(X_short, X_short) = -(n_star^2 * (r1 + normTarget)) * F_min` (-275/36) < 0.
    5. `mu_1_frust = 25/81` and `mu_2_frust = c0_scalar + eta_quantum^r1 = 89/162`. -/
abbrev OperatorSpectrumSpec (s : OperatorSpectrumOutput) : Prop :=
  trace6D (fun Z => Z) = ((p_star + n_star : Nat) : Rat) ∧
  s.Q_short_val = Q X_short ∧
  s.Q_short_val = (latticeDenom : Rat) * F_min ∧
  s.Q_split_val = Q X_split ∧
  s.Q_split_val = ((r1 * normTarget : Nat) : Rat) * F_min ∧
  s.Q_split_val / s.Q_short_val = (T : Rat) ∧
  s.tr_M_par = ((r1 + normTarget : Nat) : Rat) * F_min ∧
  s.det_M_par = -(((normTarget + d_C * r1 : Nat) : Rat) * F_min) ∧
  s.det_J_par = ((baryonCoreQuanta : Rat) * c0_scalar) * F_min ∧
  (((d_C * r1 * latticeDenom : Nat) : Rat) * s.det_J_par) = (traceQuanta : Rat) ∧
  s.omegaSq_chiral_pair = (F_split - eta_quantum) * (F_split + eta_quantum) ∧
  s.omegaSq_chiral_pair = F_min * tau_chiral_pair ∧
  s.omegaSq_chiral_pair = (traceQuanta : Rat) * (F_min ^ r1) ∧
  s.chiralDerivationSum = lambda_par_G / (latticeDenom : Rat) ∧
  s.h_poly_short = -(((n_star * n_star * (r1 + normTarget) : Nat) : Rat) * F_min) ∧
  decide (s.h_poly_short < NullCapacityRat) = true ∧
  s.Q_pol_total_chiral = ((d_C * r1 * n_star : Nat) : Rat) * F_min ∧
  s.Q_pol_total_split = Phi_inv * F_min ∧
  s.Q_pol_total_split = (k_star : Rat) ∧
  s.mu_1_frust = (s.Q_pol_total_chiral / s.Q_pol_total_split) ^ r1 ∧
  s.mu_2_frust = c0_scalar + (eta_quantum ^ r1)

/-- Proof 5.1: Convergent certification of the V_5 operator spectrum and Koszul-Vinberg moduli. -/
def proof_OperatorSpectrumState : VerifiedEmergence OperatorSpectrumSpec where
  survivor :=
    let q_sh := Q X_short
    let q_sp := Q X_split
    let dj2  := det2 (tau X_short X_short) (tau X_short X_split)
                     (tau X_split X_short) (tau X_split X_split)
    let dm2  := det2 (Q_pol X_short X_short) (Q_pol X_short X_split)
                     (Q_pol X_split X_short) (Q_pol X_split X_split)
    let dj_p := dj2 / ((r1 * r2 : Nat) : Rat)
    let dm_p := dm2 / ((r1 * r2 : Nat) : Rat)
    let tr_m := q_sh / (r2 : Rat) + q_sp / (r1 : Rat)
    let om_pair := omegaSq c_gen_0 c_gen_1
    let sc_pair := secCurvature c_gen_0 c_gen_1
    let om_sum  := omegaSq X_short c_gen_0 + omegaSq X_short c_gen_1 + omegaSq X_short c_gen_2
    let hp_sh   := h_poly X_short X_short
    let q_tot_c := Q_pol X_total c_gen_0
    let q_tot_s := Q_pol X_total s_gen_0
    let mu1     := g_KV X_total c_gen_0 c_gen_0 / g_KV X_total s_gen_0 s_gen_0
    let mu2     := ((r1 : Rat) * g_KV X_total X_short X_short) /
                   ((jtr X_short ^ r1) * g_KV X_total s_gen_0 s_gen_0)
    ⟨q_sh, q_sp, dj2, dm2, dj_p, dm_p, tr_m, om_pair, sc_pair, om_sum, hp_sh, q_tot_c, q_tot_s, mu1, mu2⟩
  certified := by decide +kernel

/-- Output Variables 5.1: Stored outputs of `proof_OperatorSpectrumState`. -/
def operatorSpectrumState : OperatorSpectrumOutput := proof_OperatorSpectrumState.survivor
def Q_short_val           : Rat                    := operatorSpectrumState.Q_short_val
def Q_split_val           : Rat                    := operatorSpectrumState.Q_split_val
def det_J_Pi2             : Rat                    := operatorSpectrumState.det_J_Pi2
def det_M_Pi2             : Rat                    := operatorSpectrumState.det_M_Pi2
def det_J_par             : Rat                    := operatorSpectrumState.det_J_par
def det_M_par             : Rat                    := operatorSpectrumState.det_M_par
def tr_M_par              : Rat                    := operatorSpectrumState.tr_M_par
def omegaSq_chiral_pair   : Rat                    := operatorSpectrumState.omegaSq_chiral_pair
def secCurv_chiral_pair   : Rat                    := operatorSpectrumState.secCurv_chiral_pair
def chiralDerivationSum   : Rat                    := operatorSpectrumState.chiralDerivationSum
def h_poly_short          : Rat                    := operatorSpectrumState.h_poly_short
def Q_pol_total_chiral    : Rat                    := operatorSpectrumState.Q_pol_total_chiral
def Q_pol_total_split     : Rat                    := operatorSpectrumState.Q_pol_total_split
def mu_1_frust            : Rat                    := operatorSpectrumState.mu_1_frust
def mu_2_frust            : Rat                    := operatorSpectrumState.mu_2_frust

-- ============================================================================
-- STAGE 6: Master Module 2 Readout & Proof-Output Verification
-- ============================================================================

structure GnosisOperatorSpectrumReadout where
  F_min                  : Rat := F_min
  Phi_inv                : Rat := Phi_inv
  F_split                : Rat := F_split
  eta_quantum            : Rat := eta_quantum
  overlapQuanta          : Nat := overlapQuanta
  traceQuanta            : Nat := traceQuanta
  tau_chiral_pair        : Rat := tau_chiral_pair
  euclideanSpatialTrace  : Rat := euclideanSpatialTrace
  lorentzianSpatialTrace : Rat := lorentzianSpatialTrace
  lambda_perp_G          : Rat := lambda_perp_G
  lambda_par_G           : Rat := lambda_par_G
  det_C_short            : Rat := det_C_short
  det_C_split            : Rat := det_C_split
  det_C                  : Rat := det_C
  gInvDiag               : Rat := gInvDiag
  gInvOff                : Rat := gInvOff
  baryonCoreQuanta       : Nat := baryonCoreQuanta
  tr_G_short_inv         : Rat := tr_G_short_inv
  M_minus1_core          : Rat := M_minus1_core
  Q_short_val            : Rat := Q_short_val
  Q_split_val            : Rat := Q_split_val
  tr_M_par               : Rat := tr_M_par
  det_M_par              : Rat := det_M_par
  det_J_par              : Rat := det_J_par
  omegaSq_chiral_pair    : Rat := omegaSq_chiral_pair
  secCurv_chiral_pair    : Rat := secCurv_chiral_pair
  chiralDerivationSum    : Rat := chiralDerivationSum
  h_poly_short           : Rat := h_poly_short
  Q_pol_total_chiral     : Rat := Q_pol_total_chiral
  Q_pol_total_split      : Rat := Q_pol_total_split
  mu_1_frust             : Rat := mu_1_frust
  mu_2_frust             : Rat := mu_2_frust
  deriving Repr, DecidableEq

/-- Proof 6.1: Final verified readout object of Module 2. -/
def proof_spectrumCascadeReadout :
    VerifiedEmergence (fun r : GnosisOperatorSpectrumReadout =>
      r.eta_quantum + r.F_min = r.F_split ∧
      r.euclideanSpatialTrace + r.lorentzianSpatialTrace = NullCapacityRat ∧
      r.lambda_perp_G = r.F_min ∧
      (r2 : Rat) * r.gInvDiag = r.tr_G_short_inv ∧
      r.M_minus1_core = (r.baryonCoreQuanta : Rat) * r.Phi_inv ∧
      r.omegaSq_chiral_pair = r.F_min * r.tau_chiral_pair ∧
      r.mu_1_frust = (r.Q_pol_total_chiral / r.Q_pol_total_split) ^ r1) where
  survivor := {}
  certified := by decide +kernel

/-- Output Variable 6.1: Master operator spectrum cascade readout. -/
def spectrumCascadeReadout : GnosisOperatorSpectrumReadout :=
  proof_spectrumCascadeReadout.survivor

#eval spectrumCascadeReadout

end GeometricNullOntologicalSpectralInvariantSymmetry.GnosisOperatorSpectrum
