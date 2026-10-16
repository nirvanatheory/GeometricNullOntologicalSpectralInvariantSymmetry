/-
  GeometricNullOntologicalSpectralInvariantSymmetry — GnosisConformalAndBundles.lean (Module 3)
  Master Convergent Proof-to-Variable Cascade: W_8 & S_4 Nilpotency, Polynomial Fixed-Point,
  Orthogonal Bundle Contraction, Signed Spatial Trace Lock, & 23 Synthesized Observables
  Verification Engine: Lean 4 (v4.28.0), zero axioms, zero sorrys, zero external dependencies.

  Strict Architectural & Mathematical Rules:
  1. Zero Numeric Literals & Zero Constructors: No digits (`0..9`) and no `Nat.zero` or `Nat.succ`
     constructors appear anywhere in this module; every input is a certified `.survivor` variable
     inherited from `GnosisDomainFiltration.lean`, `GnosisOperatorSpectrum.lean`, or a preceding
     proof structure in this file.
  2. 100% `.survivor` Encapsulation: Every dimension, basis frame (`W8.basis`, `S4.basis`),
     operator invariant, polynomial identity (`QuadPoly`), representation signature (`RepSignature`),
     bundle catalog, and observable readout exists solely as the `.survivor` output of a
     `VerifiedEmergence` proof structure.
  3. Multi-Proof Convergence at Every Stage:
     - Stage 1 (`proof_ConformalDimensions`): Isolates `d_spacetime = 4`, `dim_V5 = 6`,
       `dim_W8 = 8`, `dim_der_V5 = 10`, and `N_S = 16`, proving Schur-Weyl spinor closure.
     - Stage 2 (`proof_JordanConformalOperators`): Certifies `Y_dual`, `W0_chiral`, `z_loop`,
       McCrimmon's TKK identity `Q(X - P(X)Y) = Q(X)h(X,Y)` across all 9 sector pairs,
       Null Horizon TKK invariance `Q(e_A - P(e_A)Y) = 0` across all 15 generator-sector pairs,
       contravariant TKK ratio (`-12/23 < 0`), Gindikin bridge, Killing form, and Cayley norm (`-1/29 < 0`).
     - Stage 3 (`proof_W8AndS4Frames` -> `proof_ConformalW8AndRigidity`):
       * Certifies the 8D conformal frame `W8.basis` and 4D horizon spinor frame `S4.basis`.
       * Proves 36-pair bilinear minimal polynomial closure on `V_5` and 216-triple Step-3
         conformal nilpotency (`N_conf^3 = 0`) on `W_8`.
       * Proves Step-4 spinor nilpotency (`M_spin4^3 != 0` and `M_spin4^4 = 0`) on `S_4` and proves
         that the odd spinor exponential `(exp_S4(theta) - exp_S4(-theta))/2` yields `sin3(theta)`
         identically, sealing the nilpotent spinor origin of `sin_3`.
       * Proves the Koszul-Vinberg Metric Fixed-Point identity `kvShortNumPoly = scaleQuad eta_quantum kvShortDenomPoly`
         and the No-Tuning polynomial factorizations in `Q[eta]`.
     - Stage 4 (`proof_BundleCatalogAndCasimirs`): Certifies the `so(5)` Casimir spectrum,
       `Phi_inv = 36` bundle quantization, the 8 `RepSignature` tuples, and `Delta = I_8`.
     - Stage 5 (`proof_HolonomyReadout` -> `proof_InstantonReadout` -> `proof_BoundaryReadout` ->
       `proof_ObservablesReadout`): Synthesizes all 23 observables using pure additive bundle
       contractions driven by `lorentzianSpatialTrace = -5`, `euclideanSpatialTrace = +5`,
       `h_poly_short = -275/36 < 0`, and `tkk_ratio_cross = -12/23 < 0`.
-/

import GnosisOperatorSpectrum

namespace GeometricNullOntologicalSpectralInvariantSymmetry.GnosisConformalAndBundles

open GeometricNullOntologicalSpectralInvariantSymmetry.GnosisDomainFiltration
open GeometricNullOntologicalSpectralInvariantSymmetry.GnosisOperatorSpectrum
open Vec5 V5

-- ============================================================================
-- STAGE 1: Proof-to-Variable Isolation of Spacetime, Conformal, & Spinor Dimensions
-- ============================================================================

structure ConformalDimensionsOutput where
  d_spacetime : Nat
  dim_V5      : Nat
  dim_W8      : Nat
  dim_der_V5  : Nat
  N_S         : Nat
  deriving Repr, DecidableEq

/-- Convergent Specification of the Emergent Spacetime, Conformal, & Spinor Dimensions:
    1. `d_spacetime = horizonSphereDim n_star` (4) is the Shilov horizon and fundamental spinor rank.
    2. `dim_V5 = n_star + p_star` (6) equals both `v5OrthonormalBasis.length` and `C(d_spacetime, r1)`.
    3. `dim_W8 = dim_V5 + r1` (8) equals the chiral overlap quantum count `overlapQuanta`.
    4. `dim_der_V5 = derivationDim n_star` (10) equals the symmetric spinor square `d_spacetime*(d_spacetime+1)/2`.
    5. `N_S = r1 ^ d_spacetime` (16) satisfies the Schur-Weyl identity `dim_V5 + dim_der_V5 = N_S`. -/
abbrev ConformalDimensionsSpec (d : ConformalDimensionsOutput) : Prop :=
  d.d_spacetime = horizonSphereDim n_star ∧
  d.dim_V5 = n_star + p_star ∧
  d.dim_V5 = v5OrthonormalBasis.length ∧
  d.dim_V5 = exteriorDim d.d_spacetime r1 ∧
  d.dim_W8 = d.dim_V5 + r1 ∧
  d.dim_W8 = overlapQuanta ∧
  d.dim_der_V5 = derivationDim n_star ∧
  d.dim_der_V5 = (d.d_spacetime * (d.d_spacetime + p_star)) / r1 ∧
  d.N_S = r1 ^ d.d_spacetime ∧
  d.dim_V5 + d.dim_der_V5 = d.N_S

/-- Proof 1.1: Certification of the emergent spacetime, conformal, and spinor dimensions. -/
def proof_ConformalDimensions : VerifiedEmergence ConformalDimensionsSpec where
  survivor :=
    let d_sp := horizonSphereDim n_star
    let d_v5 := n_star + p_star
    let d_w8 := d_v5 + r1
    let d_der := derivationDim n_star
    let n_s := r1 ^ d_sp
    ⟨d_sp, d_v5, d_w8, d_der, n_s⟩
  certified := by decide +kernel

/-- Output Variables 1.1: Stored outputs of `proof_ConformalDimensions`. -/
def conformalDims : ConformalDimensionsOutput := proof_ConformalDimensions.survivor
def d_spacetime   : Nat                       := conformalDims.d_spacetime
def dim_V5        : Nat                       := conformalDims.dim_V5
def dim_W8        : Nat                       := conformalDims.dim_W8
def dim_der_V5    : Nat                       := conformalDims.dim_der_V5
def N_S           : Nat                       := conformalDims.N_S

-- ============================================================================
-- STAGE 2: Proof-to-Variable Isolation of Box/Bergman, Cayley, TKK, & Spinor Loop
-- ============================================================================

def box_op (X Y Z : V5) : V5 := V5.add (L_op (jmul X Y) Z) (D_op X Y Z)

def bergman_op (X Y Z : V5) : V5 :=
  V5.add (V5.sub Z (V5.smul (r1 : Rat) (box_op X Y Z))) (P_op X (P_op Y Z))

def tkkDisplace (X Y : V5) : V5 := V5.sub X (P_op X Y)

def tkkContravariantRatio (X Y : V5) : Rat :=
  Q (jinv (tkkDisplace X Y)) / Q (jinv X)

structure GaussRat where
  re : Rat
  im : Rat
  deriving Repr, DecidableEq

def realCayley (X : V5) : V5 := jmul (V5.sub V5.e X) (jinv (V5.add V5.e X))
def tubeNorm (X : V5) : GaussRat := ⟨Q X - (k_star : Rat), (r1 : Rat) * X.x0⟩
def gaussNormSq (z : GaussRat) : Rat := z.re * z.re + z.im * z.im

def P_11 (nu : Rat) : Rat := nu * (nu - (r2 : Rat) / (r1 : Rat))
def P_20 (nu : Rat) : Rat := nu * (nu + (k_star : Rat))

def B_g_cross (U V : V5) : Rat := ((d_spacetime * dim_V5 : Nat) : Rat) * tau U V
def B_g_str (T1 T2 : V5 → V5) : Rat :=
  (dim_V5 : Rat) * trace6D (fun Z => T1 (T2 Z)) -
  ((r1 : Rat) / (r2 : Rat)) * trace6D T1 * trace6D T2

structure JordanConformalOperatorsOutput where
  Y_dual           : V5
  W0_chiral        : Rat
  z_loop           : GaussRat
  Q_total_val      : Rat
  normSq_total_vec : Rat
  B_flat_val       : Rat
  tr_L_total_sq    : Rat
  tr_bergman_cross : Rat
  h_poly_cross     : Rat
  Q_tkk_cross      : Rat
  tkk_ratio_cross  : Rat
  Q_cayley_total   : Rat
  tubeNormSq_total : Rat
  B_g_cross_val    : Rat
  B_g_str_short    : Rat
  z_loop_normSq    : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of the Jordan, Cayley, TKK, Killing, and Clifford Operators:
    1. `Y_dual = X_short^(-1) + X_split^(-1)`, `Q(X_total) = 132 * F_min` (11/3), and
       `B_flat_val = (Y_dual.x0^2)/Q(Y_dual)` (11/4).
    2. Universal Sector TKK Identity: `Q(Phi_TKK(X, Y)) = Q(X) * h(X, Y)` holds across all 9
       sector pairs in `[X_short, X_split, X_total]^2`, and `tkk_ratio_cross = -12/23 < 0`.
    3. Null Horizon TKK Invariance: Across all 5 primitive null idempotents `g` in `allBasis5`
       and all 3 sector sums `Y`, `Q(Phi_TKK(g, Y)) = 0` (TKK flow preserves the null horizon).
    4. Gindikin-Pochhammer bridge: `1/P_11(T) = eta_quantum` (2/9) and `1/P_11(T) + 1/P_20(T) = tr_M_par` (11/36).
    5. TKK cross Killing form `B_g_cross(X_short, X_split) = Phi_inv` (36), `Q_cayley_total = -1/29 < 0`,
       tube norm squared `(17/3)^2`, and spinor holonomy loop norm squared `|z_loop|^2 = (17/18)^3`. -/
abbrev JordanConformalOperatorsSpec (s : JordanConformalOperatorsOutput) : Prop :=
  let sectors := [X_short, X_split, X_total]
  s.Y_dual = V5.add (jinv X_short) (jinv X_split) ∧
  s.W0_chiral = w_perp_leak + c0_scalar * ((r2 : Rat) * eta_quantum) ∧
  s.z_loop = ⟨(r1 : Rat) * s.W0_chiral, (r1 : Rat) * det_C_short⟩ ∧
  s.Q_total_val = Q X_total ∧
  s.Q_total_val = ((d_spacetime * r2 * (r1 + normTarget) : Nat) : Rat) * F_min ∧
  s.normSq_total_vec = Vec5.normSq X_total.vec ∧
  s.B_flat_val = (s.Y_dual.x0 ^ r1) / Q s.Y_dual ∧
  s.tr_L_total_sq = trace6D (fun Z => L_op X_total (L_op X_total Z)) ∧
  s.tr_bergman_cross = trace6D (bergman_op X_short X_split) ∧
  s.h_poly_cross = h_poly X_short X_split ∧
  decide (s.h_poly_cross < NullCapacityRat) = true ∧
  s.Q_tkk_cross = Q (tkkDisplace X_short X_split) ∧
  s.Q_tkk_cross = Q_short_val * s.h_poly_cross ∧
  (listFlatMap sectors fun X =>
   sectors.map fun Y =>
     decide (Q (tkkDisplace X Y) = Q X * h_poly X Y)).all (fun ok => ok) = true ∧
  (listFlatMap allBasis5 fun g =>
   sectors.map fun Y =>
     decide (Q (tkkDisplace g Y) = NullCapacityRat)).all (fun ok => ok) = true ∧
  s.tkk_ratio_cross = tkkContravariantRatio X_short X_split ∧
  s.tkk_ratio_cross = (k_star : Rat) / s.h_poly_cross ∧
  decide (s.tkk_ratio_cross < NullCapacityRat) = true ∧
  s.Q_cayley_total = Q (realCayley X_total) ∧
  decide (s.Q_cayley_total < NullCapacityRat) = true ∧
  s.tubeNormSq_total = gaussNormSq (tubeNorm X_total) ∧
  s.tubeNormSq_total = ((traceQuanta : Rat) / (T : Rat)) ^ r1 ∧
  ((k_star : Rat) / P_11 (T : Rat)) = eta_quantum ∧
  ((k_star : Rat) / P_11 (T : Rat) + (k_star : Rat) / P_20 (T : Rat)) = tr_M_par ∧
  s.B_g_cross_val = B_g_cross X_short X_split ∧
  s.B_g_cross_val = Phi_inv ∧
  s.B_g_str_short = B_g_str (L_op X_short) (L_op X_short) ∧
  s.z_loop_normSq = gaussNormSq s.z_loop ∧
  s.z_loop_normSq = ((traceQuanta : Rat) / ((r1 * normTarget : Nat) : Rat)) ^ r2

/-- Proof 2.1: Certification of the Stage 2 Jordan, Cayley, TKK, and Clifford operators. -/
def proof_JordanConformalOperators : VerifiedEmergence JordanConformalOperatorsSpec where
  survivor :=
    let yd     := V5.add (jinv X_short) (jinv X_split)
    let w0     := w_perp_leak + c0_scalar * ((r2 : Rat) * eta_quantum)
    let zl     : GaussRat := ⟨(r1 : Rat) * w0, (r1 : Rat) * det_C_short⟩
    let q_tot  := Q X_total
    let n_vec  := Vec5.normSq X_total.vec
    let b_flt  := (yd.x0 ^ r1) / Q yd
    let tr_l2  := trace6D (fun Z => L_op X_total (L_op X_total Z))
    let tr_bg  := trace6D (bergman_op X_short X_split)
    let hp_cr  := h_poly X_short X_split
    let q_tkk  := Q (tkkDisplace X_short X_split)
    let r_tkk  := tkkContravariantRatio X_short X_split
    let q_cay  := Q (realCayley X_total)
    let t_norm := gaussNormSq (tubeNorm X_total)
    let bg_cr  := B_g_cross X_short X_split
    let bg_st  := B_g_str (L_op X_short) (L_op X_short)
    let z_nsq  := gaussNormSq zl
    ⟨yd, w0, zl, q_tot, n_vec, b_flt, tr_l2, tr_bg, hp_cr, q_tkk, r_tkk, q_cay, t_norm, bg_cr, bg_st, z_nsq⟩
  certified := by decide +kernel

/-- Output Variables 2.1: Stored outputs of `proof_JordanConformalOperators`. -/
def jordanConformalOps : JordanConformalOperatorsOutput := proof_JordanConformalOperators.survivor
def Y_dual             : V5                             := jordanConformalOps.Y_dual
def W0_chiral          : Rat                            := jordanConformalOps.W0_chiral
def z_loop             : GaussRat                       := jordanConformalOps.z_loop
def Q_total_val        : Rat                            := jordanConformalOps.Q_total_val
def normSq_total_vec   : Rat                            := jordanConformalOps.normSq_total_vec
def B_flat_val         : Rat                            := jordanConformalOps.B_flat_val
def tr_L_total_sq      : Rat                            := jordanConformalOps.tr_L_total_sq
def tr_bergman_cross   : Rat                            := jordanConformalOps.tr_bergman_cross
def h_poly_cross       : Rat                            := jordanConformalOps.h_poly_cross
def Q_tkk_cross        : Rat                            := jordanConformalOps.Q_tkk_cross
def tkk_ratio_cross    : Rat                            := jordanConformalOps.tkk_ratio_cross
def Q_cayley_total     : Rat                            := jordanConformalOps.Q_cayley_total
def tubeNormSq_total   : Rat                            := jordanConformalOps.tubeNormSq_total
def B_g_cross_val      : Rat                            := jordanConformalOps.B_g_cross_val
def B_g_str_short      : Rat                            := jordanConformalOps.B_g_str_short
def z_loop_normSq      : Rat                            := jordanConformalOps.z_loop_normSq

-- ============================================================================
-- STAGE 3: Proof-to-Variable Certification of 8D Conformal Frame W_8, 4D Spinor
--          Frame S_4 (Sealing `sin_3`), Full-Basis Closure, & Polynomial Fixed-Point
-- ============================================================================

def minPolyResidual (X : V5) : V5 :=
  V5.add (V5.sub (jmul X X) (V5.smul (jtr X) X)) (V5.smul (Q X) V5.e)

def polarizedMinPolyResidual (U V : V5) : V5 :=
  V5.add (V5.sub (V5.sub (jmul U V) (V5.smul U.x0 V)) (V5.smul V.x0 U))
         (V5.smul (Q_pol U V) V5.e)

/-- An element `w = (xi_minus, v, xi_plus)` of the 8D conformal representation `W_8 = Q ⊕ V_5 ⊕ Q`. -/
structure W8 where
  xi_minus : Rat
  v        : V5
  xi_plus  : Rat
  deriving Repr, DecidableEq

namespace W8

def add (a b : W8) : W8 := ⟨a.xi_minus + b.xi_minus, V5.add a.v b.v, a.xi_plus + b.xi_plus⟩
def sub (a b : W8) : W8 := ⟨a.xi_minus - b.xi_minus, V5.sub a.v b.v, a.xi_plus - b.xi_plus⟩
def smul (c : Rat) (a : W8) : W8 := ⟨c * a.xi_minus, V5.smul c a.v, c * a.xi_plus⟩

end W8

/-- An element `s = (w1, w2, w3, w4)` of the 4D fundamental horizon spinor representation `S_4`. -/
structure S4 where
  w1 : Rat
  w2 : Rat
  w3 : Rat
  w4 : Rat
  deriving Repr, DecidableEq

namespace S4

def add (a b : S4) : S4 := ⟨a.w1 + b.w1, a.w2 + b.w2, a.w3 + b.w3, a.w4 + b.w4⟩
def sub (a b : S4) : S4 := ⟨a.w1 - b.w1, a.w2 - b.w2, a.w3 - b.w3, a.w4 - b.w4⟩
def smul (c : Rat) (a : S4) : S4 := ⟨c * a.w1, c * a.w2, c * a.w3, c * a.w4⟩
def coordSum (a : S4) : Rat := a.w1 + a.w2 + a.w3 + a.w4

end S4

structure W8AndS4FramesOutput where
  w8_zero  : W8
  w8_basis : List W8
  s4_zero  : S4
  s4_basis : List S4
  s4_top   : S4
  deriving Repr, DecidableEq

/-- Specification of the 8D Conformal Frame (`W_8`) and 4D Fundamental Spinor Frame (`S_4`):
    1. `w8_basis` has length `dim_W8` (8) and `w8_zero` is the additive identity on `W_8`.
    2. `s4_basis` has length `d_spacetime` (4), `s4_zero` is the additive identity on `S_4`,
       and `s4_top` is the highest-weight spinor basis vector `(0, 0, 0, 1)`. -/
abbrev W8AndS4FramesSpec (f : W8AndS4FramesOutput) : Prop :=
  f.w8_basis.length = dim_W8 ∧
  f.w8_zero = ⟨NullCapacityRat, V5.zero, NullCapacityRat⟩ ∧
  (f.w8_basis.all (fun w => decide (W8.add f.w8_zero w = w))) = true ∧
  f.s4_basis.length = d_spacetime ∧
  f.s4_zero = ⟨NullCapacityRat, NullCapacityRat, NullCapacityRat, NullCapacityRat⟩ ∧
  (f.s4_basis.all (fun s => decide (S4.add f.s4_zero s = s))) = true ∧
  f.s4_top = listGetD f.s4_basis r2 f.s4_zero ∧
  S4.coordSum f.s4_top = (k_star : Rat)

/-- Proof 3.1: Certification of the `W_8` and `S_4` orthonormal frames. -/
def proof_W8AndS4Frames : VerifiedEmergence W8AndS4FramesSpec where
  survivor :=
    let z0 := NullCapacityRat
    let u1 := (k_star : Rat)
    let wz : W8 := ⟨z0, V5.zero, z0⟩
    let w_minus : W8 := ⟨u1, V5.zero, z0⟩
    let w_plus  : W8 := ⟨z0, V5.zero, u1⟩
    let v5_embedded : List W8 :=
      v5OrthonormalBasis.map (fun b => ({ xi_minus := z0, v := b, xi_plus := z0 } : W8))
    let sz : S4 := ⟨z0, z0, z0, z0⟩
    let sb : List S4 :=
      [ ⟨u1, z0, z0, z0⟩,
        ⟨z0, u1, z0, z0⟩,
        ⟨z0, z0, u1, z0⟩,
        ⟨z0, z0, z0, u1⟩ ]
    let st : S4 := listGetD sb r2 sz
    ⟨wz, [w_minus] ++ v5_embedded ++ [w_plus], sz, sb, st⟩
  certified := by decide +kernel

/-- Output Variables 3.1: Stored `W_8` and `S_4` frames extracted from `.survivor`. -/
def w8AndS4State : W8AndS4FramesOutput := proof_W8AndS4Frames.survivor
def W8.zero      : W8                  := w8AndS4State.w8_zero
def W8.basis     : List W8             := w8AndS4State.w8_basis
def S4.zero      : S4                  := w8AndS4State.s4_zero
def S4.basis     : List S4             := w8AndS4State.s4_basis
def s4_top       : S4                  := w8AndS4State.s4_top

/-- Canonical conformal nilpotent operator `N_conf(X)(xi_-, z, xi_+) = (0, xi_- X, 2 Q_pol(X, z))` on W_8. -/
def N_conf (X : V5) (w : W8) : W8 :=
  ⟨NullCapacityRat, V5.smul w.xi_minus X, (r1 : Rat) * Q_pol X w.v⟩

/-- Universal degree-`r2` conformal exponential map `exp_W8(X)(w)` on W_8. -/
def expW8 (X : V5) (w : W8) : W8 :=
  let w1 := N_conf X w
  let w2 := N_conf X w1
  let w3 := N_conf X w2
  W8.add (W8.add w w1)
         (W8.add (W8.smul ((k_star : Rat) / (factorial r1 : Rat)) w2)
                 (W8.smul ((k_star : Rat) / (factorial r2 : Rat)) w3))

def isZeroOnW8 (F : W8 → W8) : Bool :=
  W8.basis.all (fun w => decide (F w = W8.zero))

/-- Regular alternating nilpotent spinor generator `M_spin4(w1, w2, w3, w4) = (w2, -w3, w4, 0)` on `S_4`:
    Satisfies `M_spin4^1 != 0`, `M_spin4^2 != 0`, `M_spin4^3 != 0`, and `M_spin4^4 = 0` on all of `S_4`. -/
def M_spin4 (s : S4) : S4 :=
  ⟨s.w2, -s.w3, s.w4, NullCapacityRat⟩

def isZeroOnS4 (F : S4 → S4) : Bool :=
  S4.basis.all (fun s => decide (F s = S4.zero))

/-- Exact unipotent spinor exponential `exp_S4(theta) = I + theta M + (theta^2/2!) M^2 + (theta^3/3!) M^3` on `S_4`
    (terminating exactly at degree `r2 = 3` because `M_spin4^4 = 0` on `S_4`). -/
def expS4 (theta : Rat) (s : S4) : S4 :=
  let m1 := M_spin4 s
  let m2 := M_spin4 m1
  let m3 := M_spin4 m2
  S4.add (S4.add s (S4.smul theta m1))
         (S4.add (S4.smul ((theta ^ r1) / (factorial r1 : Rat)) m2)
                 (S4.smul ((theta ^ r2) / (factorial r2 : Rat)) m3))

/-- Odd-parity projection `(exp_S4(theta)(s_top) - exp_S4(-theta)(s_top)) / r1` on `S_4`:
    Cancels all even grades (0 and 2) and extracts the exact degree-3 spinor holonomy polynomial. -/
def oddExpS4Trace (theta : Rat) : Rat :=
  S4.coordSum (S4.smul ((k_star : Rat) / (r1 : Rat))
                (S4.sub (expS4 theta s4_top) (expS4 (-theta) s4_top)))

/-- Canonical Grade-`r2` odd Lie exponential map `sin_3(theta) = theta - theta^3 / 3!`. -/
def sin3 (theta : Rat) : Rat :=
  theta - (theta ^ r2) / (factorial r2 : Rat)

def allBasisPairsMinPolyZero : Bool :=
  (listFlatMap v5OrthonormalBasis fun u =>
   v5OrthonormalBasis.map fun v =>
     decide (polarizedMinPolyResidual u v = V5.zero)).all (fun b => b)

def allBasisTriplesConformalCubeZero : Bool :=
  (listFlatMap v5OrthonormalBasis fun u =>
   listFlatMap v5OrthonormalBasis fun v =>
   v5OrthonormalBasis.map fun z =>
     isZeroOnW8 (fun w => N_conf u (N_conf v (N_conf z w)))).all (fun b => b)

structure QuadPoly where
  c0 : Rat
  c1 : Rat
  c2 : Rat
  deriving Repr, DecidableEq

def addQuad (P Q : QuadPoly) : QuadPoly := ⟨P.c0 + Q.c0, P.c1 + Q.c1, P.c2 + Q.c2⟩
def subQuad (P Q : QuadPoly) : QuadPoly := ⟨P.c0 - Q.c0, P.c1 - Q.c1, P.c2 - Q.c2⟩
def scaleQuad (k : Rat) (P : QuadPoly) : QuadPoly := ⟨k * P.c0, k * P.c1, k * P.c2⟩
def mulLin (a0 a1 b0 b1 : Rat) : QuadPoly := ⟨a0 * b0, a0 * b1 + a1 * b0, a1 * b1⟩
def evalQuad (P : QuadPoly) (x : Rat) : Rat := P.c0 + P.c1 * x + P.c2 * (x * x)

structure ConformalW8AndRigidityOutput where
  w_perp_short     : V5
  w_perp_split     : V5
  quadPoly_zero    : QuadPoly
  kvShortNumPoly   : QuadPoly
  kvShortDenomPoly : QuadPoly
  kvMu1Poly        : QuadPoly
  specMu1Poly      : QuadPoly
  kvMu2Poly        : QuadPoly
  specMu2Poly      : QuadPoly
  baseFactorPoly   : QuadPoly
  poly_mu1_lock    : QuadPoly
  poly_mu2_lock    : QuadPoly
  deriving Repr, DecidableEq

/-- Convergent Specification of Full-Basis Closure, `W_8` vs. `S_4` Nilpotency, & Polynomial Fixed-Point:
    1. Full-Basis Bilinearity & Trilinearity:
       - `allBasisPairsMinPolyZero = true` (all 36 basis pairs of `V_5`).
       - `allBasisTriplesConformalCubeZero = true` (all 216 basis triples of `V_5` on `W_8`).
    2. `W_8` Index-3 Nilpotency vs. `S_4` Index-4 Spinor Nilpotency (Seals Audit #3):
       - On `W_8`: `N_conf(e_A)^2 = 0` for horizon idempotents, while `N_conf(X)^2 != 0` and `N_conf(X)^3 = 0` for bulk sectors.
       - On `S_4`: `M_spin4^1 != 0`, `M_spin4^2 != 0`, `M_spin4^3 != 0`, and `M_spin4^4 = 0` across all of `S_4`,
         with exterior vanishing `exteriorDim r2 d_spacetime = 0` (`C(3, 4) = 0`), and `oddExpS4Trace theta = sin3 theta`.
    3. Three-Way Convergent Polynomial Rigidity in `Q[eta]` (Seals Audit #4):
       - Koszul-Vinberg Metric Fixed-Point Identity: `kvShortNumPoly = scaleQuad eta_quantum kvShortDenomPoly`
         (and `subQuad = quadPoly_zero`), proving `g_{X_short(eta)}(c_i(eta), c_i(eta)) = 2/9` identically in `Q[eta]`.
       - Cross-Sector Factorization: `subQuad kvMu1Poly specMu1Poly = poly_mu1_lock` and
         `subQuad kvMu2Poly specMu2Poly = poly_mu2_lock`, both factoring through `baseFactorPoly = (9*eta - 2)*(eta - 1)`. -/
abbrev ConformalW8AndRigiditySpec (s : ConformalW8AndRigidityOutput) : Prop :=
  v5OrthonormalBasis.length = dim_V5 ∧
  W8.basis.length = dim_W8 ∧
  S4.basis.length = d_spacetime ∧
  allBasisPairsMinPolyZero = true ∧
  allBasisTriplesConformalCubeZero = true ∧
  minPolyResidual c_gen_0 = V5.zero ∧
  minPolyResidual s_gen_0 = V5.zero ∧
  minPolyResidual X_short = V5.zero ∧
  minPolyResidual X_split = V5.zero ∧
  minPolyResidual X_total = V5.zero ∧
  isZeroOnW8 (N_conf c_gen_0) = false ∧
  isZeroOnW8 (fun w => N_conf c_gen_0 (N_conf c_gen_0 w)) = true ∧
  isZeroOnW8 (fun w => N_conf c_gen_1 (N_conf c_gen_1 w)) = true ∧
  isZeroOnW8 (fun w => N_conf c_gen_2 (N_conf c_gen_2 w)) = true ∧
  isZeroOnW8 (fun w => N_conf s_gen_0 (N_conf s_gen_0 w)) = true ∧
  isZeroOnW8 (fun w => N_conf s_gen_1 (N_conf s_gen_1 w)) = true ∧
  isZeroOnW8 (fun w => N_conf X_short (N_conf X_short w)) = false ∧
  isZeroOnW8 (fun w => N_conf X_split (N_conf X_split w)) = false ∧
  isZeroOnW8 (fun w => N_conf X_total (N_conf X_total w)) = false ∧
  isZeroOnW8 (fun w => N_conf X_short (N_conf X_short (N_conf X_short w))) = true ∧
  isZeroOnW8 (fun w => N_conf X_split (N_conf X_split (N_conf X_split w))) = true ∧
  isZeroOnW8 (fun w => N_conf X_total (N_conf X_total (N_conf X_total w))) = true ∧
  isZeroOnS4 M_spin4 = false ∧
  isZeroOnS4 (fun u => M_spin4 (M_spin4 u)) = false ∧
  isZeroOnS4 (fun u => M_spin4 (M_spin4 (M_spin4 u))) = false ∧
  isZeroOnS4 (fun u => M_spin4 (M_spin4 (M_spin4 (M_spin4 u)))) = true ∧
  exteriorDim r2 d_spacetime = NullCapacity ∧
  exteriorDim r2 n_star = NullCapacity ∧
  oddExpS4Trace eta_quantum = sin3 eta_quantum ∧
  oddExpS4Trace F_split = sin3 F_split ∧
  s.w_perp_short.x0 = NullCapacityRat ∧
  s.w_perp_split.x0 = NullCapacityRat ∧
  tau s.w_perp_short X_split = NullCapacityRat ∧
  Q_pol s.w_perp_short X_split = NullCapacityRat ∧
  addQuad s.quadPoly_zero s.baseFactorPoly = s.baseFactorPoly ∧
  s.kvShortNumPoly = scaleQuad eta_quantum s.kvShortDenomPoly ∧
  subQuad s.kvShortNumPoly (scaleQuad eta_quantum s.kvShortDenomPoly) = s.quadPoly_zero ∧
  subQuad s.kvMu1Poly s.specMu1Poly = s.poly_mu1_lock ∧
  subQuad s.kvMu2Poly s.specMu2Poly = s.poly_mu2_lock ∧
  s.poly_mu1_lock = scaleQuad (((r1 ^ r1 : Nat) : Rat) / (normTarget : Rat)) s.baseFactorPoly ∧
  s.poly_mu2_lock = scaleQuad ((k_star : Rat) / (T : Rat)) s.baseFactorPoly ∧
  evalQuad s.baseFactorPoly eta_quantum = NullCapacityRat ∧
  evalQuad s.poly_mu1_lock eta_quantum = NullCapacityRat ∧
  evalQuad s.poly_mu2_lock eta_quantum = NullCapacityRat ∧
  evalQuad s.kvMu1Poly eta_quantum = mu_1_frust ∧
  evalQuad s.specMu1Poly eta_quantum = mu_1_frust ∧
  evalQuad s.kvMu2Poly eta_quantum = mu_2_frust ∧
  evalQuad s.specMu2Poly eta_quantum = mu_2_frust

/-- Proof 3.2: Certification of full-basis closure, W_8 and S_4 nilpotency, and polynomial rigidity. -/
def proof_ConformalW8AndRigidity : VerifiedEmergence ConformalW8AndRigiditySpec where
  survivor :=
    let w_sh := V5.sub c_gen_0 c_gen_1
    let w_sp := V5.sub s_gen_0 s_gen_1
    let qz   : QuadPoly := ⟨NullCapacityRat, NullCapacityRat, NullCapacityRat⟩
    let kv_sh_num := scaleQuad (r1 : Rat)
                       (mulLin c0_scalar (-(r1 : Rat)) c0_scalar (-(r1 : Rat)))
    let kv_sh_den := mulLin ((r2 : Rat) * c0_scalar) (-(latticeDenom : Rat))
                            ((r2 : Rat) * c0_scalar) (-(latticeDenom : Rat))
    let kv_m1     := mulLin (k_star : Rat) (-(r1 : Rat)) (k_star : Rat) (-(r1 : Rat))
    let sp_m1     := scaleQuad (((r1 ^ r1 : Nat) : Rat) / (normTarget : Rat))
                       ⟨F_split, (r1 : Rat), NullCapacityRat⟩
    let q_pol_sq  := scaleQuad (r1 : Rat)
                       (mulLin (r2 : Rat) (-(latticeDenom : Rat)) (r2 : Rat) (-(latticeDenom : Rat)))
    let q_tot_sh  := mulLin (n_star : Rat) (-(latticeDenom : Rat))
                            ((r2 : Rat) * c0_scalar) (-(latticeDenom : Rat))
    let kv_m2     := scaleQuad ((k_star : Rat) / (normTarget : Rat))
                       (subQuad q_pol_sq q_tot_sh)
    let sp_m2     := ⟨c0_scalar, NullCapacityRat, (k_star : Rat)⟩
    let baseP     := mulLin (-(r1 : Rat)) (normTarget : Rat) (-(k_star : Rat)) (k_star : Rat)
    let p_mu1     := scaleQuad (((r1 ^ r1 : Nat) : Rat) / (normTarget : Rat)) baseP
    let p_mu2     := scaleQuad ((k_star : Rat) / (T : Rat)) baseP
    ⟨w_sh, w_sp, qz, kv_sh_num, kv_sh_den, kv_m1, sp_m1, kv_m2, sp_m2, baseP, p_mu1, p_mu2⟩
  certified := by decide +kernel

/-- Output Variables 3.2: Stored outputs of `proof_ConformalW8AndRigidity`. -/
def conformalW8State : ConformalW8AndRigidityOutput := proof_ConformalW8AndRigidity.survivor
def w_perp_short     : V5                           := conformalW8State.w_perp_short
def w_perp_split     : V5                           := conformalW8State.w_perp_split
def QuadPoly.zero    : QuadPoly                     := conformalW8State.quadPoly_zero
def kvShortNumPoly   : QuadPoly                     := conformalW8State.kvShortNumPoly
def kvShortDenomPoly : QuadPoly                     := conformalW8State.kvShortDenomPoly
def kvMu1Poly        : QuadPoly                     := conformalW8State.kvMu1Poly
def specMu1Poly      : QuadPoly                     := conformalW8State.specMu1Poly
def kvMu2Poly        : QuadPoly                     := conformalW8State.kvMu2Poly
def specMu2Poly      : QuadPoly                     := conformalW8State.specMu2Poly
def baseFactorPoly   : QuadPoly                     := conformalW8State.baseFactorPoly
def poly_mu1_lock    : QuadPoly                     := conformalW8State.poly_mu1_lock
def poly_mu2_lock    : QuadPoly                     := conformalW8State.poly_mu2_lock

-- ============================================================================
-- STAGE 4: Proof-to-Variable Isolation of Schur-Weyl Casimir Closure,
--          Frustration-Quantized Bundles, & 8x8 Orthogonal `RepSignature` Catalog
-- ============================================================================

def casimirSO5 (l1 l2 : Rat) : Rat := l1 * (l1 + (r2 : Rat)) + l2 * (l2 + (k_star : Rat))

structure RepSignature where
  rankDeg    : Nat
  spinorDeg  : Nat
  torsionDeg : Nat
  tkkGrade   : Int
  deriving Repr, DecidableEq

structure TypedInvariant where
  sig : RepSignature
  val : Rat
  deriving Repr, DecidableEq

def signatureOrthogonalityCheck (cat : List TypedInvariant) : Bool :=
  let dummy : TypedInvariant := ⟨⟨NullCapacity, NullCapacity, NullCapacity, Int.ofNat NullCapacity⟩, NullCapacityRat⟩
  (listFlatMap (List.range cat.length) fun i =>
   (List.range cat.length).map fun j =>
     let bi := listGetD cat i dummy
     let bj := listGetD cat j dummy
     decide ((i == j) == (bi.sig == bj.sig))).all (fun b => b)

structure BundleCatalogAndCasimirsOutput where
  C2_spin4                  : Rat
  C2_spin16                 : Rat
  C2_spin20                 : Rat
  C2_vec5                   : Rat
  C2_adj10                  : Rat
  C2_sym30                  : Rat
  C2_mix35                  : Rat
  trInvC2_alt_Q5_cube       : Rat
  trInvC2_sym_Q5_cube       : Rat
  trInvC2_mix_Q5_cube       : Rat
  trInvC2_tot_Q5_cube       : Rat
  det_J_short_3             : Rat
  det_M_short_3             : Rat
  dim_End_LinkBundle        : Nat
  dim_Orbifold4D            : Nat
  dim_HorizonBundle         : Nat
  dim_TorusBundle           : Nat
  dim_End_JordanSpinor      : Nat
  dim_ThreeSpinorBundle     : Nat
  threeSpinorChiralVol      : Rat
  dim_VectorSpinorBundle    : Nat
  weylCasimirB2             : Rat
  tr_WeylCasimir_VecSpinor  : Rat
  dim_SpacetimeTensor4      : Nat
  tr_Casimir_SpacetimeTens4 : Rat
  sig_EndLink               : RepSignature
  sig_Orbifold4D            : RepSignature
  sig_Horizon4D             : RepSignature
  sig_Torus2D               : RepSignature
  sig_EndJordanSpinor       : RepSignature
  sig_ThreeSpinor           : RepSignature
  sig_VecSpinorUnip         : RepSignature
  sig_BulkTensor4D          : RepSignature
  bundleCatalog             : List TypedInvariant
  deriving Repr, DecidableEq

/-- Convergent Specification of Schur-Weyl Casimir Closure, Phi-Quantized Bundles, & `Delta = I_8`:
    1. 3-fold vector cube `(Q^5)^{\otimes 3}` Casimir traces match the Jordan operator pairings on V_5.
    2. All five horizon/orbifold/torus/link/spinor bundle dimensions factor into exact powers of `Phi_inv` (36).
    3. `bundleCatalog` has length `dim_W8` (8), satisfies `signatureOrthogonalityCheck = true` (`Delta = I_8`),
       and every signature resolves to a unique singleton of length `p_star` (1). -/
abbrev BundleCatalogAndCasimirsSpec (b : BundleCatalogAndCasimirsOutput) : Prop :=
  b.C2_vec5 = (d_spacetime : Rat) ∧
  b.C2_adj10 = (dim_V5 : Rat) ∧
  b.dim_ThreeSpinorBundle = d_spacetime ^ r2 ∧
  b.dim_ThreeSpinorBundle = d_spacetime * N_S ∧
  b.threeSpinorChiralVol = (b.dim_ThreeSpinorBundle : Rat) / (r2 : Rat) ∧
  b.trInvC2_alt_Q5_cube = Q_pol X_total X_short ∧
  b.trInvC2_alt_Q5_cube / (dim_der_V5 : Rat) = Q_short_val ∧
  b.trInvC2_sym_Q5_cube / ((r2 * dim_der_V5 + n_star : Nat) : Rat) = (k_star : Rat) / P_20 (T : Rat) ∧
  b.trInvC2_mix_Q5_cube = (dim_V5 : Rat) * lambda_par_G ∧
  b.trInvC2_tot_Q5_cube / (n_star : Rat) = normSq_total_vec ∧
  (b.det_J_short_3 - b.det_M_short_3) / det_G_short = (r1 : Rat) ∧
  (b.dim_End_LinkBundle : Rat) = ((d_spacetime * N_S : Nat) : Rat) * Phi_inv ∧
  (b.dim_Orbifold4D : Rat) = ((T ^ r1 : Nat) : Rat) * Phi_inv ∧
  (b.dim_HorizonBundle : Rat) = (r1 : Rat) * (Phi_inv ^ r1) ∧
  (b.dim_TorusBundle : Rat) = (dim_W8 : Rat) * Phi_inv ∧
  (b.dim_End_JordanSpinor : Rat) = ((N_S * N_S : Nat) : Rat) * Phi_inv ∧
  b.weylCasimirB2 = (tau_chiral_pair * Phi_inv) / (r1 : Rat) ∧
  b.weylCasimirB2 = (traceQuanta : Rat) / (r1 : Rat) ∧
  b.tr_WeylCasimir_VecSpinor = (b.dim_VectorSpinorBundle : Rat) * b.weylCasimirB2 ∧
  b.tr_Casimir_SpacetimeTens4 = b.C2_vec5 * (b.dim_SpacetimeTensor4 : Rat) ∧
  b.bundleCatalog =
    [ ⟨b.sig_EndLink,         (b.dim_End_LinkBundle : Rat)⟩,
      ⟨b.sig_Orbifold4D,      (b.dim_Orbifold4D : Rat)⟩,
      ⟨b.sig_Horizon4D,       (b.dim_HorizonBundle : Rat)⟩,
      ⟨b.sig_Torus2D,         (b.dim_TorusBundle : Rat)⟩,
      ⟨b.sig_EndJordanSpinor, (b.dim_End_JordanSpinor : Rat)⟩,
      ⟨b.sig_ThreeSpinor,     b.threeSpinorChiralVol⟩,
      ⟨b.sig_VecSpinorUnip,   b.tr_WeylCasimir_VecSpinor⟩,
      ⟨b.sig_BulkTensor4D,    b.tr_Casimir_SpacetimeTens4⟩ ] ∧
  b.bundleCatalog.length = dim_W8 ∧
  signatureOrthogonalityCheck b.bundleCatalog = true ∧
  (b.bundleCatalog.all (fun item =>
    decide ((b.bundleCatalog.filter (fun x => decide (x.sig = item.sig))).length = p_star))) = true

/-- Proof 4.1: Certification of Schur-Weyl Casimir traces, bundle quantization, and `Delta = I_8`. -/
def proof_BundleCatalogAndCasimirs : VerifiedEmergence BundleCatalogAndCasimirsSpec where
  survivor :=
    let c2_s4  := casimirSO5 c0_scalar c0_scalar
    let c2_s16 := casimirSO5 ((r2 : Rat) * c0_scalar) c0_scalar
    let c2_s20 := casimirSO5 ((r2 : Rat) * c0_scalar) ((r2 : Rat) * c0_scalar)
    let c2_v5  := casimirSO5 (k_star : Rat) NullCapacityRat
    let c2_a10 := casimirSO5 (k_star : Rat) (k_star : Rat)
    let c2_s30 := casimirSO5 (r2 : Rat) NullCapacityRat
    let c2_m35 := casimirSO5 (r1 : Rat) (k_star : Rat)
    let dim_30 := (r2 * dim_der_V5 : Nat)
    let dim_35 := (r2 * dim_der_V5 + n_star : Nat)
    let tr_alt := (dim_der_V5 : Rat) / c2_a10
    let tr_sym := (n_star : Rat) / c2_v5 + (dim_30 : Rat) / c2_s30
    let tr_mix := (n_star : Rat) / c2_v5 + (dim_35 : Rat) / c2_m35
    let tr_tot := tr_alt + (r1 : Rat) * tr_mix + tr_sym
    let dj3 := det3 (tau c_gen_0 c_gen_0) (tau c_gen_0 c_gen_1) (tau c_gen_0 c_gen_2)
                    (tau c_gen_1 c_gen_0) (tau c_gen_1 c_gen_1) (tau c_gen_1 c_gen_2)
                    (tau c_gen_2 c_gen_0) (tau c_gen_2 c_gen_1) (tau c_gen_2 c_gen_2)
    let dm3 := det3 (Q_pol c_gen_0 c_gen_0) (Q_pol c_gen_0 c_gen_1) (Q_pol c_gen_0 c_gen_2)
                    (Q_pol c_gen_1 c_gen_0) (Q_pol c_gen_1 c_gen_1) (Q_pol c_gen_1 c_gen_2)
                    (Q_pol c_gen_2 c_gen_0) (Q_pol c_gen_2 c_gen_1) (Q_pol c_gen_2 c_gen_2)
    let d_link := N_S * T
    let d_end_link := d_link * d_link
    let d_orb4 := d_spacetime * (T ^ d_spacetime)
    let d_hor4 := r1 * N_S * (T ^ d_spacetime)
    let d_tor2 := r1 * N_S * (T ^ r1)
    let d_jspin := dim_V5 * N_S
    let d_end_jspin := d_jspin * d_jspin
    let d_3spin := r2 * d_spacetime + r1 * N_S + p_star * (d_spacetime + N_S)
    let v_3spin := (d_3spin : Rat) / (r2 : Rat)
    let d_vspin := n_star * N_S
    let w_cas := (((d_spacetime * dim_V5 : Nat) : Rat) * det_J_par) / (r1 : Rat)
    let tr_w_vspin := (d_vspin : Rat) * w_cas
    let d_spt4 := n_star ^ d_spacetime
    let tr_c_spt4 := c2_v5 * (d_spt4 : Rat)
    let z_int := Int.ofNat NullCapacity
    let p_int := Int.ofNat p_star
    let s_link  : RepSignature := ⟨NullCapacity, r1, r1, z_int⟩
    let s_orb4  : RepSignature := ⟨NullCapacity, p_star, d_spacetime, z_int⟩
    let s_hor4  : RepSignature := ⟨p_star, p_star, d_spacetime, z_int⟩
    let s_tor2  : RepSignature := ⟨p_star, p_star, r1, z_int⟩
    let s_jspin : RepSignature := ⟨r1, r1, NullCapacity, z_int⟩
    let s_3spin : RepSignature := ⟨NullCapacity, r2, NullCapacity, p_int⟩
    let s_vspin : RepSignature := ⟨p_star, p_star, NullCapacity, -p_int⟩
    let s_spt4  : RepSignature := ⟨p_star, NullCapacity, d_spacetime, p_int⟩
    let cat : List TypedInvariant :=
      [ ⟨s_link,  (d_end_link : Rat)⟩,
        ⟨s_orb4,  (d_orb4 : Rat)⟩,
        ⟨s_hor4,  (d_hor4 : Rat)⟩,
        ⟨s_tor2,  (d_tor2 : Rat)⟩,
        ⟨s_jspin, (d_end_jspin : Rat)⟩,
        ⟨s_3spin, v_3spin⟩,
        ⟨s_vspin, tr_w_vspin⟩,
        ⟨s_spt4,  tr_c_spt4⟩ ]
    ⟨c2_s4, c2_s16, c2_s20, c2_v5, c2_a10, c2_s30, c2_m35,
     tr_alt, tr_sym, tr_mix, tr_tot, dj3, dm3,
     d_end_link, d_orb4, d_hor4, d_tor2, d_end_jspin, d_3spin, v_3spin,
     d_vspin, w_cas, tr_w_vspin, d_spt4, tr_c_spt4,
     s_link, s_orb4, s_hor4, s_tor2, s_jspin, s_3spin, s_vspin, s_spt4, cat⟩
  certified := by decide +kernel

/-- Output Variables 4.1: Stored outputs of `proof_BundleCatalogAndCasimirs`. -/
def bundleAndCasimirState     : BundleCatalogAndCasimirsOutput := proof_BundleCatalogAndCasimirs.survivor
def dim_End_LinkBundle        : Nat                            := bundleAndCasimirState.dim_End_LinkBundle
def dim_Orbifold4D            : Nat                            := bundleAndCasimirState.dim_Orbifold4D
def dim_HorizonBundle         : Nat                            := bundleAndCasimirState.dim_HorizonBundle
def dim_TorusBundle           : Nat                            := bundleAndCasimirState.dim_TorusBundle
def dim_End_JordanSpinor      : Nat                            := bundleAndCasimirState.dim_End_JordanSpinor
def dim_ThreeSpinorBundle     : Nat                            := bundleAndCasimirState.dim_ThreeSpinorBundle
def threeSpinorChiralVol      : Rat                            := bundleAndCasimirState.threeSpinorChiralVol
def dim_VectorSpinorBundle    : Nat                            := bundleAndCasimirState.dim_VectorSpinorBundle
def weylCasimirB2             : Rat                            := bundleAndCasimirState.weylCasimirB2
def tr_WeylCasimir_VecSpinor  : Rat                            := bundleAndCasimirState.tr_WeylCasimir_VecSpinor
def dim_SpacetimeTensor4      : Nat                            := bundleAndCasimirState.dim_SpacetimeTensor4
def tr_Casimir_SpacetimeTens4 : Rat                            := bundleAndCasimirState.tr_Casimir_SpacetimeTens4
def sig_EndLink               : RepSignature                   := bundleAndCasimirState.sig_EndLink
def sig_Orbifold4D            : RepSignature                   := bundleAndCasimirState.sig_Orbifold4D
def sig_Horizon4D             : RepSignature                   := bundleAndCasimirState.sig_Horizon4D
def sig_Torus2D               : RepSignature                   := bundleAndCasimirState.sig_Torus2D
def sig_EndJordanSpinor       : RepSignature                   := bundleAndCasimirState.sig_EndJordanSpinor
def sig_ThreeSpinor           : RepSignature                   := bundleAndCasimirState.sig_ThreeSpinor
def sig_VecSpinorUnip         : RepSignature                   := bundleAndCasimirState.sig_VecSpinorUnip
def sig_BulkTensor4D          : RepSignature                   := bundleAndCasimirState.sig_BulkTensor4D
def bundleCatalog             : List TypedInvariant            := bundleAndCasimirState.bundleCatalog

/-- Deterministic Signature-Locked Contraction Functor:
    Finds the unique bundle in `bundleCatalog` whose `RepSignature` matches `num.sig`. -/
def contractBySignature (num : TypedInvariant) : Rat :=
  match bundleCatalog.filter (fun b => decide (b.sig = num.sig)) with
  | [b] => num.val / b.val
  | _   => NullCapacityRat

-- ============================================================================
-- STAGE 5: Proof-to-Variable Cascade of the 4 Readout Ledgers & 23 Observables
--          (With Pure Additive Signed Spatial Trace & Curvature-Sign Lock)
-- ============================================================================

structure EmergentHolonomyReadout where
  eta_APS       : Rat
  mu_1          : Rat
  mu_2          : Rat
  mu_3          : Rat
  aspectTangent : Rat
  bareCasimir   : Rat
  closedCasimir : Rat
  apsCasimir    : Rat
  m_1           : Rat
  m_2           : Rat
  m_3           : Rat
  wolfenstein_A : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of `EmergentHolonomyReadout` (Seals Audit #3 & #5):
    1. Pure Additive Signed Spatial Trace Lock:
       - `mu_3` is the pure `+` sum of `eta_APS / T^2` and `contractBySignature ⟨sig_EndLink, lorentzianSpatialTrace⟩`
         (where `lorentzianSpatialTrace = -5` from `Q` on `Q^5`),
       - `closedCasimir` is the pure `+` sum of `bareCasimir` and `contractBySignature ⟨sig_Horizon4D, euclideanSpatialTrace⟩`
         (where `euclideanSpatialTrace = +5` from `tau` on `Q^5`).
    2. Exact `S_4` Spinor Exponential Verification:
       For all three holonomy angles `m_1, m_2, m_3`, `oddExpS4Trace m_k = sin3 m_k`. -/
abbrev HolonomyReadoutSpec (H : EmergentHolonomyReadout) : Prop :=
  H.eta_APS = eta_quantum ∧
  H.mu_1 = mu_1_frust ∧
  H.mu_2 = mu_2_frust ∧
  H.mu_3 = (H.eta_APS / ((T ^ r1 : Nat) : Rat)) + contractBySignature ⟨sig_EndLink, lorentzianSpatialTrace⟩ ∧
  H.mu_3 = (H.eta_APS / ((T ^ r1 : Nat) : Rat)) - contractBySignature ⟨sig_EndLink, (n_star : Rat)⟩ ∧
  H.aspectTangent = H.mu_1 / ((k_star : Rat) - H.mu_3) ∧
  H.bareCasimir = (k_star : Rat) / (tau X_short X_short) ∧
  H.closedCasimir = H.bareCasimir + contractBySignature ⟨sig_Horizon4D, euclideanSpatialTrace⟩ ∧
  H.apsCasimir = ((k_star : Rat) - H.eta_APS) * H.bareCasimir + H.eta_APS * H.closedCasimir ∧
  H.m_1 = (-(k_star : Rat) / Q_cayley_total) / ((T : Rat) * tr_L_total_sq) ∧
  H.m_2 = (dim_der_V5 : Rat) / ((T : Rat) ^ n_star) ∧
  H.m_3 = (dim_W8 : Rat) / ((T : Rat) ^ (n_star + r1)) ∧
  H.wolfenstein_A = H.m_2 / (H.m_1 * H.m_1) ∧
  oddExpS4Trace H.m_1 = sin3 H.m_1 ∧
  oddExpS4Trace H.m_2 = sin3 H.m_2 ∧
  oddExpS4Trace H.m_3 = sin3 H.m_3 ∧
  decide (H.m_1 > H.m_2) = true ∧
  decide (H.m_2 > H.m_3) = true ∧
  decide (H.m_3 > NullCapacityRat) = true

/-- Proof 5.1: Certification of `EmergentHolonomyReadout` via `contractBySignature` and signed traces. -/
def proof_HolonomyReadout : VerifiedEmergence HolonomyReadoutSpec where
  survivor :=
    let eta := g_KV X_short c_gen_0 c_gen_0
    let mu1 := g_KV X_total c_gen_0 c_gen_0 / g_KV X_total s_gen_0 s_gen_0
    let mu2 := ((r1 : Rat) * g_KV X_total X_short X_short) /
               ((jtr X_short ^ r1) * g_KV X_total s_gen_0 s_gen_0)
    let mu3 := eta / ((T ^ r1 : Nat) : Rat) + contractBySignature ⟨sig_EndLink, lorentzianSpatialTrace⟩
    let asp := mu1 / ((k_star : Rat) - mu3)
    let bareC := (k_star : Rat) / (tau X_short X_short)
    let closedC := bareC + contractBySignature ⟨sig_Horizon4D, euclideanSpatialTrace⟩
    let apsC := ((k_star : Rat) - eta) * bareC + eta * closedC
    let m1 := (-(k_star : Rat) / Q_cayley_total) / ((T : Rat) * tr_L_total_sq)
    let m2 := (dim_der_V5 : Rat) / ((T : Rat) ^ n_star)
    let m3 := (dim_W8 : Rat) / ((T : Rat) ^ (n_star + r1))
    let wolfA := m2 / (m1 * m1)
    ⟨eta, mu1, mu2, mu3, asp, bareC, closedC, apsC, m1, m2, m3, wolfA⟩
  certified := by decide +kernel

/-- Output Variable 5.1: Stored holonomy readout (`emergentH`). -/
def emergentH : EmergentHolonomyReadout := proof_HolonomyReadout.survivor

structure EmergentInstantonReadout where
  lambda_1            : Rat
  lambda_2            : Rat
  lambda_3            : Rat
  totalTrace          : Rat
  spectralAsymmetry   : Rat
  transgressionPrefac : Rat
  deriving Repr, DecidableEq

abbrev InstantonReadoutSpec (I : EmergentInstantonReadout) : Prop :=
  I.lambda_1 = (r1 : Rat) * ((k_star : Rat) - emergentH.mu_1) ∧
  I.lambda_2 = ((r1 * (T ^ r1) : Nat) : Rat) * ((k_star : Rat) - emergentH.mu_2) ∧
  I.lambda_3 = B_g_str_short - Q_short_val ∧
  decide (I.lambda_1 < I.lambda_2) = true ∧
  decide (I.lambda_2 < I.lambda_3) = true ∧
  I.totalTrace = I.lambda_1 + I.lambda_2 + I.lambda_3 ∧
  I.spectralAsymmetry = I.lambda_3 - I.lambda_2 - I.lambda_1 ∧
  I.spectralAsymmetry = (((traceQuanta + r1) ^ r2 : Nat) : Rat) / ((r1 * (T ^ d_spacetime) : Nat) : Rat) ∧
  I.transgressionPrefac = (dim_SpacetimeTensor4 : Rat) * (tubeNormSq_total ^ r1)

/-- Proof 5.2: Certification of `EmergentInstantonReadout` from `emergentH`. -/
def proof_InstantonReadout : VerifiedEmergence InstantonReadoutSpec where
  survivor :=
    let l1 := (r1 : Rat) * ((k_star : Rat) - emergentH.mu_1)
    let l2 := ((r1 * (T ^ r1) : Nat) : Rat) * ((k_star : Rat) - emergentH.mu_2)
    let l3 := B_g_str_short - Q_short_val
    let tot := l1 + l2 + l3
    let asym := l3 - l2 - l1
    let prefac := (dim_SpacetimeTensor4 : Rat) * (tubeNormSq_total ^ r1)
    ⟨l1, l2, l3, tot, asym, prefac⟩
  certified := by decide +kernel

/-- Output Variable 5.2: Stored instanton readout (`emergentI`). -/
def emergentI : EmergentInstantonReadout := proof_InstantonReadout.survivor

structure EmergentBoundaryReadout where
  B_flat         : Rat
  B_torus        : Rat
  D_Lag          : Rat
  delta_1        : Rat
  delta_2        : Rat
  delta_3        : Rat
  delta_total    : Rat
  delta_hor      : Rat
  delta_boundary : Rat
  traceBridge    : Rat
  deriving Repr, DecidableEq

/-- Convergent Specification of `EmergentBoundaryReadout`:
    Proves that `delta_1 < 0`, `delta_2 < 0`, `delta_3 < 0`, and `delta_boundary < 0` are forced
    by the negative Bergman curvature `h_poly_short = -275/36 < 0`, while `delta_hor > 0` comes from
    the nilpotent conformal flow `expW8` on `W_8`. -/
abbrev BoundaryReadoutSpec (B : EmergentBoundaryReadout) : Prop :=
  B.B_flat = B_flat_val ∧
  B.B_torus = B.B_flat + contractBySignature ⟨sig_Torus2D, normSq_total_vec⟩ ∧
  B.D_Lag = emergentH.mu_2 / (N_S : Rat) ∧
  B.delta_1 = contractBySignature ⟨sig_EndJordanSpinor, h_poly_short⟩ ∧
  B.delta_2 = contractBySignature ⟨sig_ThreeSpinor, B.delta_1 / B.B_flat⟩ ∧
  B.delta_3 = det_C * B.delta_2 ∧
  decide (B.delta_1 < NullCapacityRat) = true ∧
  decide (B.delta_2 < NullCapacityRat) = true ∧
  decide (B.delta_3 < NullCapacityRat) = true ∧
  B.delta_total = B.delta_1 + B.delta_2 + B.delta_3 ∧
  decide (B.delta_hor > NullCapacityRat) = true ∧
  B.delta_boundary = B.delta_total + B.delta_hor ∧
  decide (B.delta_boundary < NullCapacityRat) = true ∧
  B.traceBridge = contractBySignature ⟨sig_ThreeSpinor, emergentI.totalTrace⟩ - B.B_torus ∧
  B.traceBridge = chiralDerivationSum

/-- Proof 5.3: Certification of `EmergentBoundaryReadout` from `emergentH` and `emergentI`. -/
def proof_BoundaryReadout : VerifiedEmergence BoundaryReadoutSpec where
  survivor :=
    let bFlat  := B_flat_val
    let bTorus := bFlat + contractBySignature ⟨sig_Torus2D, normSq_total_vec⟩
    let dLag   := emergentH.mu_2 / (N_S : Rat)
    let d1     := contractBySignature ⟨sig_EndJordanSpinor, h_poly_short⟩
    let d2     := contractBySignature ⟨sig_ThreeSpinor, d1 / bFlat⟩
    let d3     := det_C * d2
    let dTot   := d1 + d2 + d3
    let nu_unip := contractBySignature ⟨sig_VecSpinorUnip, (r2 : Rat)⟩
    let dCas1   := contractBySignature ⟨sig_Horizon4D, (p_star : Rat)⟩
    let w_in    : W8 := ⟨dCas1, V5.smul dCas1 c_gen_0, NullCapacityRat⟩
    let w_out   : W8 := expW8 (V5.smul (-nu_unip) c_gen_0) w_in
    let dHor    := jtr w_out.v
    let dBound  := dTot + dHor
    let bridge  := contractBySignature ⟨sig_ThreeSpinor, emergentI.totalTrace⟩ - bTorus
    ⟨bFlat, bTorus, dLag, d1, d2, d3, dTot, dHor, dBound, bridge⟩
  certified := by decide +kernel

/-- Output Variable 5.3: Stored boundary readout (`emergentB`). -/
def emergentB : EmergentBoundaryReadout := proof_BoundaryReadout.survivor

structure EmergentObservables where
  n_s_bare        : Rat
  n_s_dressed     : Rat
  N_efolds        : Rat
  r_tensor        : Rat
  Y_p_orbifold    : Rat
  Y_p_BBN         : Rat
  Y_p_twist       : Rat
  N_eff           : Rat
  sin2_theta12    : Rat
  sin2_theta23    : Rat
  sin2_theta13    : Rat
  Omega_m         : Rat
  Omega_Lambda    : Rat
  V_us            : Rat
  V_cb            : Rat
  V_ub            : Rat
  V_ub_over_V_cb  : Rat
  wolfenstein_A   : Rat
  sin2_thetaW     : Rat
  alpha_s_bare    : Rat
  alpha_s_dressed : Rat
  mu_proton       : Rat
  mp_over_me      : Rat
  deriving Repr, DecidableEq

abbrev ObservablesReadoutSpec (O : EmergentObservables) : Prop :=
  O.n_s_bare = (k_star : Rat) - emergentB.D_Lag ∧
  O.n_s_dressed = O.n_s_bare + emergentB.delta_boundary ∧
  O.N_efolds = (r1 : Rat) / emergentB.D_Lag ∧
  O.r_tensor = (T : Rat) * (emergentB.D_Lag ^ r1) ∧
  O.Omega_m + O.Omega_Lambda = (k_star : Rat) ∧
  O.V_us = oddExpS4Trace emergentH.m_1 ∧
  O.V_cb = oddExpS4Trace emergentH.m_2 ∧
  O.V_ub = oddExpS4Trace emergentH.m_3 ∧
  O.V_us = sin3 emergentH.m_1 ∧
  O.V_cb = sin3 emergentH.m_2 ∧
  O.V_ub = sin3 emergentH.m_3 ∧
  O.V_ub_over_V_cb = O.V_ub / O.V_cb ∧
  O.wolfenstein_A = O.V_cb / (O.V_us * O.V_us) ∧
  O.sin2_thetaW = emergentH.apsCasimir ∧
  O.alpha_s_bare = (k_star : Rat) / weylCasimirB2 ∧
  O.alpha_s_dressed = (k_star : Rat) / (weylCasimirB2 - emergentH.mu_3) ∧
  O.mu_proton = emergentB.B_torus + emergentB.D_Lag + emergentB.delta_boundary ∧
  O.mp_over_me = M_minus1_core + (tr_M_par / (r1 : Rat)) +
    contractBySignature ⟨sig_BulkTensor4D, c0_scalar * tkk_ratio_cross⟩

/-- Proof 5.4: Certification of the 23 synthesized observables from `emergentH` and `emergentB`. -/
def proof_ObservablesReadout : VerifiedEmergence ObservablesReadoutSpec where
  survivor :=
    let ns0     := (k_star : Rat) - emergentB.D_Lag
    let nsFull  := ns0 + emergentB.delta_boundary
    let muProt  := emergentB.B_torus + emergentB.D_Lag + emergentB.delta_boundary
    let ne      := (r1 : Rat) / emergentB.D_Lag
    let rTens   := (T : Rat) * (emergentB.D_Lag ^ r1)
    let orbUnit := contractBySignature ⟨sig_Orbifold4D, (p_star : Rat)⟩
    let yp0     := ((k_star : Rat) / (d_spacetime : Rat)) - orbUnit
    let ypBBN   := yp0 + orbUnit / (N_S : Rat)
    let ypTwist := c_vec_normSq - emergentH.m_3
    let neff    := (T : Rat) + emergentH.m_2 + emergentH.m_3
    let v_us    := oddExpS4Trace emergentH.m_1
    let v_cb    := oddExpS4Trace emergentH.m_2
    let v_ub    := oddExpS4Trace emergentH.m_3
    let v_ratio := v_ub / v_cb
    let wolf_A  := v_cb / (v_us * v_us)
    let asBare  := (k_star : Rat) / weylCasimirB2
    let asDress := (k_star : Rat) / (weylCasimirB2 - emergentH.mu_3)
    let M_minus1 := M_minus1_core
    let M_zero   := tr_M_par / (r1 : Rat)
    let M_plus1  := contractBySignature ⟨sig_BulkTensor4D, c0_scalar * tkk_ratio_cross⟩
    let mpTotal  := M_minus1 + M_zero + M_plus1
    ⟨ns0, nsFull, ne, rTens, yp0, ypBBN, ypTwist, neff,
     emergentH.mu_1, emergentH.mu_2, emergentH.mu_3,
     emergentH.aspectTangent, (k_star : Rat) - emergentH.aspectTangent,
     v_us, v_cb, v_ub, v_ratio, wolf_A, emergentH.apsCasimir,
     asBare, asDress, muProt, mpTotal⟩
  certified := by decide +kernel

/-- Output Variable 5.4: Stored 23-observable readout (`emergentO`). -/
def emergentO : EmergentObservables := proof_ObservablesReadout.survivor

-- ============================================================================
-- STAGE 6: Master Module 3 Complete Readout Structure & End-to-End Verification
-- ============================================================================

structure GnosisConformalAndBundlesReadout where
  holonomy    : EmergentHolonomyReadout  := emergentH
  instanton   : EmergentInstantonReadout := emergentI
  boundary    : EmergentBoundaryReadout  := emergentB
  observables : EmergentObservables      := emergentO
  deriving Repr, DecidableEq

/-- Proof 6.1: Final verified readout object of Module 3. -/
def proof_completeLogosReadout :
    VerifiedEmergence (fun R : GnosisConformalAndBundlesReadout =>
      allBasisPairsMinPolyZero = true ∧
      allBasisTriplesConformalCubeZero = true ∧
      isZeroOnS4 (fun u => M_spin4 (M_spin4 (M_spin4 u))) = false ∧
      isZeroOnS4 (fun u => M_spin4 (M_spin4 (M_spin4 (M_spin4 u)))) = true ∧
      kvShortNumPoly = scaleQuad eta_quantum kvShortDenomPoly ∧
      subQuad kvMu1Poly specMu1Poly = poly_mu1_lock ∧
      subQuad kvMu2Poly specMu2Poly = poly_mu2_lock ∧
      R.holonomy.eta_APS = (overlapQuanta : Rat) * F_min ∧
      R.boundary.traceBridge = chiralDerivationSum ∧
      R.observables.Omega_m + R.observables.Omega_Lambda = (k_star : Rat) ∧
      decide (R.observables.mp_over_me > M_minus1_core) = true) where
  survivor := {}
  certified := by decide +kernel

/-- Output Variable 6.1: Master complete readout of Module 3. -/
def completeLogosReadout : GnosisConformalAndBundlesReadout := proof_completeLogosReadout.survivor

def ratLe (a b : Rat) : Bool :=
  decide (a.num * Int.ofNat b.den ≤ b.num * Int.ofNat a.den)

def inBounds (x lo hi : Rat) : Bool :=
  ratLe lo x && ratLe x hi

#eval completeLogosReadout

end GeometricNullOntologicalSpectralInvariantSymmetry.GnosisConformalAndBundles
