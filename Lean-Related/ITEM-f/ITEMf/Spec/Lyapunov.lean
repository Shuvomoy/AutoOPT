import ITEMf.Spec.Algorithm

/-!
# Proof-free ITEM-f Lyapunov specification

This module translates the finite coefficient and two-state algorithm data
into the scalar coordinates, block vectors, interpolation gaps, compact
potential, and exact public theorem contracts used by the manuscript proof.
It contains definitions and structures only, so it is safe for the trusted
Comparator challenge import closure.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : Nat}

/-- Manuscript coefficient index `k`, where the Lean index `i : Fin N`
represents `k = i + 1`. -/
def lyapCoeffIndex (i : Fin N) : Fin (N + 2) :=
  idxInterior i

/-- Manuscript coefficient index `k+1`, where `k = i+1`. -/
def lyapNextCoeffIndex (i : Fin N) : Fin (N + 2) :=
  ⟨i.1 + 2, by omega⟩

/-- The `φ_{N-k}` index attached to the Lyapunov index `k=i+1`. -/
def lyapPhiIndex (i : Fin N) : Fin (N + 1) :=
  ⟨N - i.1 - 1, by omega⟩

/-- Embed an interior Lyapunov index `k=1,...,N-1` into `k=1,...,N`. -/
def interiorLyapIndex (i : Fin (N - 1)) : Fin N :=
  ⟨i.1, by omega⟩

/-- The successor of an interior Lyapunov index, still in `Fin N`. -/
def nextInteriorLyapIndex (i : Fin (N - 1)) : Fin N :=
  ⟨i.1 + 1, by omega⟩

/-- The final Lyapunov index, representing manuscript index `k=N`. -/
def terminalLyapIndex (hN : 1 ≤ N) : Fin N :=
  ⟨N - 1, by omega⟩

/-- The first Lyapunov index, representing manuscript index `k=1`. -/
def firstLyapIndex (hN : 1 ≤ N) : Fin N :=
  ⟨0, by omega⟩

/-- The scalar `cₖ = 1 - q a_{k+1}/Upsilon`. -/
noncomputable def cCoeff
    (q : ℝ) (C : CoeffData N) (i : Fin N) : ℝ :=
  1 - q * C.a (lyapNextCoeffIndex i) / C.Upsilon

/-- The scalar
`sₖ = sqrt(q) a_{k+1} φ_{N-k}/Upsilon`. -/
noncomputable def sCoeff
    (q : ℝ) (C : CoeffData N) (i : Fin N) : ℝ :=
  Real.sqrt q * C.a (lyapNextCoeffIndex i) *
      phi q C (lyapPhiIndex i) / C.Upsilon

/-- Squared Euclidean norm on a two-block vector.  We use this explicit sum
instead of Lean's product max norm. -/
noncomputable def blockNormSq (z : E × E) : ℝ :=
  ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2

/-- Inner product on a two-block vector. -/
noncomputable def blockInner (z w : E × E) : ℝ :=
  ⟪z.1, w.1⟫_ℝ + ⟪z.2, w.2⟫_ℝ

/-- Scalar multiplication of a two-block vector. -/
def blockScale (r : ℝ) (z : E × E) : E × E :=
  (r • z.1, r • z.2)

/-- Subtraction of two-block vectors. -/
def blockSub (z w : E × E) : E × E :=
  (z.1 - w.1, z.2 - w.2)

/-- The manuscript rotation matrix acting on a two-block vector. -/
def blockRotate (c s : ℝ) (z : E × E) : E × E :=
  (c • z.1 + s • z.2, (-s) • z.1 + c • z.2)

/-- The block vector `Wₖ`, with `i : Fin N` representing `k=i+1`. -/
noncomputable def W
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (i : Fin N) : E × E :=
  let k := i.1 + 1
  let previousPlus := itemfPreviousPlus M C x0 k - xStar
  let xk := itemfIterate M C x0 k - xStar
  let ak := C.a (lyapCoeffIndex i)
  let ak1 := C.a (lyapNextCoeffIndex i)
  let ck := cCoeff M.q C i
  let sk := sCoeff M.q C i
  (ak • previousPlus,
    sk⁻¹ • (((1 - M.q) * ak1) • xk - (ck * ak) • previousPlus))

/-- The two-block shifted-gradient vector occurring in one norm decrement. -/
noncomputable def gapBlock
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (i : Fin N) : E × E :=
  let g := M.shiftedGrad xStar (itemfIterate M C x0 (i.1 + 1))
  ((cCoeff M.q C i - 1) • g, sCoeff M.q C i • g)

/-- The compact Lyapunov quantity `Vₖ`, with `i : Fin N` representing
`k=i+1`. -/
noncomputable def potential
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (i : Fin N) : ℝ :=
  C.a (lyapCoeffIndex i) *
      M.shiftedGap xStar (itemfIterate M C x0 i.1) xStar +
    M.μ / (2 * (1 - M.q) * C.Upsilon) *
      blockNormSq (W M C x0 xStar i)

/-- Exact scalar-coordinate, symmetry, and endpoint package used by the
Lyapunov proof. -/
structure CoordinateRelationsResult
    (q : ℝ) (C : CoeffData N) (hN : 1 ≤ N) : Prop where
  forward :
    ∀ i : Fin N,
      cCoeff q C i * C.a (lyapCoeffIndex i) +
          sCoeff q C i * C.b (lyapCoeffIndex i) =
        (1 - q) * C.a (lyapNextCoeffIndex i)
  inverse :
    ∀ i : Fin (N - 1),
      let j := interiorLyapIndex i
      C.a (lyapCoeffIndex j) =
        (cCoeff q C j + q) * C.a (lyapNextCoeffIndex j) -
          sCoeff q C j * C.b (lyapNextCoeffIndex j)
  interior_unit :
    ∀ i : Fin (N - 1),
      let j := interiorLyapIndex i
      sCoeff q C j ^ 2 + cCoeff q C j ^ 2 = 1
  mirror_next :
    ∀ i : Fin (N - 1),
      let j := interiorLyapIndex i
      C.a (lyapNextCoeffIndex j) *
          C.a (reverseIndex (lyapNextCoeffIndex j)) = 1
  first_last :
    C.a (lyapCoeffIndex (firstLyapIndex hN)) *
        C.a (idxN N) = 1
  first_b :
    C.a (lyapCoeffIndex (firstLyapIndex hN)) *
        C.b (idxN N) =
      C.b (lyapCoeffIndex (firstLyapIndex hN))
  terminal_c :
    cCoeff q C (terminalLyapIndex hN) = 1 - q
  terminal_s :
    sCoeff q C (terminalLyapIndex hN) =
      Real.sqrt q * Real.sqrt (1 - q)

/-- The three exact squared-norm identities in the manuscript. -/
structure NormIdentitiesResult
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N) : Prop where
  initial :
    blockNormSq (W M C x0 xStar (firstLyapIndex hN)) =
      (1 - M.q) * ‖x0 - xStar‖ ^ 2 -
        (2 * C.Upsilon / M.μ) *
          (C.a (lyapCoeffIndex (firstLyapIndex hN)) -
            C.a (idxZero N)) *
          ⟪M.gradientStep x0 - xStar, M.shiftedGrad xStar x0⟫_ℝ +
        (C.Upsilon * C.a (idxZero N) / (M.μ * M.L)) *
          ‖M.shiftedGrad xStar x0‖ ^ 2
  interior :
    ∀ i : Fin (N - 1),
      let j := interiorLyapIndex i
      blockNormSq (W M C x0 xStar (nextInteriorLyapIndex i)) =
        blockNormSq
          (blockSub (W M C x0 xStar j)
            (blockScale (C.Upsilon / M.μ)
              (gapBlock M C x0 xStar j)))
  terminal :
    blockNormSq (W M C x0 xStar (terminalLyapIndex hN)) =
      (1 - M.q) * C.Upsilon ^ 2 *
          ‖itemfIterate M C x0 N - xStar‖ ^ 2 +
        (1 / M.q) *
          ‖((1 - M.q) * C.Upsilon) •
                (itemfIterate M C x0 N - xStar) -
            C.a (idxN N) •
                (itemfPreviousPlus M C x0 N - xStar)‖ ^ 2

/-- The exact decrement and finite nonincreasing-chain package. -/
structure LyapunovMonotoneResult
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) : Prop where
  decrement :
    ∀ i : Fin (N - 1),
      let j := interiorLyapIndex i
      potential M C x0 xStar j -
          potential M C x0 xStar (nextInteriorLyapIndex i) =
        C.a (lyapCoeffIndex j) *
            M.shiftedGap xStar
              (itemfIterate M C x0 j.1)
              (itemfIterate M C x0 (j.1 + 1)) +
          (C.a (lyapNextCoeffIndex j) -
              C.a (lyapCoeffIndex j)) *
            M.shiftedGap xStar xStar
              (itemfIterate M C x0 (j.1 + 1))
  nonnegative :
    ∀ i : Fin (N - 1),
      let j := interiorLyapIndex i
      0 ≤ potential M C x0 xStar j -
        potential M C x0 xStar (nextInteriorLyapIndex i)
  chain :
    ∀ {i j : Fin N}, i.1 ≤ j.1 →
      potential M C x0 xStar j ≤ potential M C x0 xStar i

end ITEMf
