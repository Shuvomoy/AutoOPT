import ITEMf.Algorithm.Coordinates
import ITEMf.Construction.ShootingNecessary
import ITEMf.Lyapunov.Rotations

/-!
# ITEM-f norm identities

The terminal identity is proved by a direct two-block expansion.  Interior
rotations are handled only on `Fin (N-1)`; the terminal coefficient is never
treated as an orthogonal rotation.
-/

open scoped InnerProductSpace
open InnerProductSpace

set_option autoImplicit false

namespace ITEMf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {N : Nat}

private theorem itemf_first_update
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN) :
    itemfIterate M C x0 1 =
      M.gradientStep x0 -
        (phi M.q C (⟨N - 1, by omega⟩ : Fin (N + 1)) /
          (C.Upsilon * Real.sqrt (1 - M.q)) * M.L⁻¹) •
          M.grad x0 := by
  let k := firstLyapIndex hN
  let a1 := C.a (lyapCoeffIndex k)
  let aN := C.a (idxN N)
  let φprev :=
    phi M.q C (⟨N - 1, by omega⟩ : Fin (N + 1))
  have hN0 : N ≠ 0 := by omega
  have hcurrent :
      phiCurrentIndex k = (⟨N, by omega⟩ : Fin (N + 1)) := by
    apply Fin.ext
    simp [phiCurrentIndex, k, firstLyapIndex]
  have hprevious :
      phiPreviousIndex k =
        (⟨N - 1, by omega⟩ : Fin (N + 1)) := by
    apply Fin.ext
    simp [phiPreviousIndex, k, firstLyapIndex]
  have ha1N : a1 * aN = 1 := by
    simpa [a1, aN, k] using hcoord.first_last
  have hsqrt :
      Real.sqrt (1 - M.q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 M.one_sub_q_pos)
  have hsqrtSq :
      Real.sqrt (1 - M.q) ^ 2 = 1 - M.q :=
    Real.sq_sqrt M.one_sub_q_pos.le
  have ha1 : a1 ≠ 0 := by
    dsimp [a1]
    exact hC.a_ne_zero _
  have hU : C.Upsilon ≠ 0 := hC.upsilon_ne_zero
  have h1q : 1 - M.q ≠ 0 := M.one_sub_q_ne_zero
  have hden :
      (1 - M.q) * C.Upsilon + aN ≠ 0 := by
    exact ne_of_gt (add_pos
      (mul_pos M.one_sub_q_pos hC.upsilon_pos)
      (by
        dsimp [aN]
        exact hC.a_pos _))
  have haNinv : aN = 1 / a1 := by
    field_simp [ha1]
    nlinarith [ha1N]
  have hden' :
      (1 - M.q) * C.Upsilon + 1 / a1 ≠ 0 := by
    rw [← haNinv]
    exact hden
  have hscaled :
      1 - M.q * C.Upsilon * a1 + C.Upsilon * a1 ≠ 0 := by
    have ha1pos : 0 < a1 := by
      dsimp [a1]
      exact hC.a_pos _
    have hprod :
        0 < (1 - M.q) * C.Upsilon * a1 :=
      mul_pos (mul_pos M.one_sub_q_pos hC.upsilon_pos) ha1pos
    apply ne_of_gt
    nlinarith
  have hφcurrent :
      phi M.q C (phiCurrentIndex k) =
        ((1 - M.q) * C.Upsilon + aN) /
          Real.sqrt (1 - M.q) := by
    rw [hcurrent, phi_terminal, if_neg hN0]
  have hφcurrent0 :
      phi M.q C (phiCurrentIndex k) ≠ 0 := by
    rw [hφcurrent]
    exact div_ne_zero
      (ne_of_gt (add_pos
        (mul_pos M.one_sub_q_pos hC.upsilon_pos)
        (hC.a_pos (idxN N))))
      hsqrt
  have hcoefficient :
      (itemfMomentumCoefficients M.q C).first k +
          (itemfMomentumCoefficients M.q C).second k =
        φprev / (C.Upsilon * Real.sqrt (1 - M.q)) := by
    change
      C.a (idxChordLeft (Fin.castSucc k)) *
            phi M.q C (phiPreviousIndex k) /
          ((1 - M.q) * C.a (idxChordRight (Fin.castSucc k)) *
            phi M.q C (phiCurrentIndex k)) +
        phi M.q C (phiPreviousIndex k) /
          phi M.q C (phiCurrentIndex k) =
        φprev / (C.Upsilon * Real.sqrt (1 - M.q))
    have hleft :
        idxChordLeft (Fin.castSucc k) = idxZero N := by
      apply Fin.ext
      rfl
    have hright :
        idxChordRight (Fin.castSucc k) = lyapCoeffIndex k := by
      apply Fin.ext
      rfl
    rw [hleft, hright, hprevious, hφcurrent, hC.a_zero]
    dsimp only [φprev]
    rw [haNinv]
    change
      1 / C.Upsilon * φprev /
            ((1 - M.q) * a1 *
              (((1 - M.q) * C.Upsilon + 1 / a1) /
                Real.sqrt (1 - M.q))) +
          φprev /
            (((1 - M.q) * C.Upsilon + 1 / a1) /
              Real.sqrt (1 - M.q)) =
        φprev / (C.Upsilon * Real.sqrt (1 - M.q))
    field_simp [h1q, hU, hsqrt, ha1, hden', hscaled]
    rw [hsqrtSq]
    ring_nf
    field_simp [hscaled]
    ring
  have hstep := itemfIterate_succ M C x0 k
  have hk : k.1 = 0 := rfl
  rw [hk, itemfIterate_zero, itemfPreviousPlus_zero] at hstep
  rw [show (0 : Nat) + 1 = 1 by rfl] at hstep
  calc
    itemfIterate M C x0 1 =
        M.gradientStep x0 +
          ((itemfMomentumCoefficients M.q C).first k +
            (itemfMomentumCoefficients M.q C).second k) •
            (M.gradientStep x0 - x0) := by
              rw [hstep]
              module
    _ = M.gradientStep x0 +
          (φprev / (C.Upsilon * Real.sqrt (1 - M.q))) •
            (M.gradientStep x0 - x0) := by rw [hcoefficient]
    _ = M.gradientStep x0 -
        (φprev / (C.Upsilon * Real.sqrt (1 - M.q)) * M.L⁻¹) •
          M.grad x0 := by
            simp only [StronglyConvexSmoothModel.gradientStep]
            module

private theorem first_W_formula
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN) :
    let k := firstLyapIndex hN
    let a1 := C.a (lyapCoeffIndex k)
    let b1 := C.b (lyapCoeffIndex k)
    let u := M.gradientStep x0 - xStar
    W M C x0 xStar k =
      (a1 • u,
        b1 • u -
          (Real.sqrt (1 - M.q) / Real.sqrt M.q * M.L⁻¹) •
            M.grad x0) := by
  dsimp only
  let k := firstLyapIndex hN
  let s := sCoeff M.q C k
  let c := cCoeff M.q C k
  let a1 := C.a (lyapCoeffIndex k)
  let a2 := C.a (lyapNextCoeffIndex k)
  let b1 := C.b (lyapCoeffIndex k)
  let φprev :=
    phi M.q C (⟨N - 1, by omega⟩ : Fin (N + 1))
  let u := M.gradientStep x0 - xStar
  have hk : k.1 + 1 = 1 := rfl
  have hphi :
      lyapPhiIndex k =
        (⟨N - 1, by omega⟩ : Fin (N + 1)) := by
    apply Fin.ext
    simp [lyapPhiIndex, k, firstLyapIndex]
  have hs : s ≠ 0 := by
    dsimp [s, k]
    exact s_ne_zero_of_relations M.q_unit hC hN hcoord _
  have hsqrtq :
      Real.sqrt M.q ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 M.q_pos)
  have hsqrt1q :
      Real.sqrt (1 - M.q) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 M.one_sub_q_pos)
  have hsqrt1qSq :
      Real.sqrt (1 - M.q) ^ 2 = 1 - M.q :=
    Real.sq_sqrt M.one_sub_q_pos.le
  have ha2 : a2 ≠ 0 := by
    dsimp [a2]
    exact hC.a_ne_zero _
  have hU : C.Upsilon ≠ 0 := hC.upsilon_ne_zero
  have hφprev : φprev ≠ 0 := by
    intro hzero
    apply hs
    change
      Real.sqrt M.q * a2 *
          phi M.q C (lyapPhiIndex k) / C.Upsilon = 0
    rw [hphi]
    change
      Real.sqrt M.q * a2 * φprev / C.Upsilon = 0
    rw [hzero]
    ring
  have hforward :
      c * a1 + s * b1 = (1 - M.q) * a2 := by
    simpa [c, s, a1, a2, b1, k] using hcoord.forward k
  have hscale :
      s⁻¹ * ((1 - M.q) * a2) *
          (φprev / (C.Upsilon * Real.sqrt (1 - M.q)) *
            M.L⁻¹) =
        Real.sqrt (1 - M.q) / Real.sqrt M.q * M.L⁻¹ := by
    change
      (Real.sqrt M.q * a2 * φprev / C.Upsilon)⁻¹ *
          ((1 - M.q) * a2) *
          (φprev / (C.Upsilon * Real.sqrt (1 - M.q)) *
            M.L⁻¹) =
        Real.sqrt (1 - M.q) / Real.sqrt M.q * M.L⁻¹
    field_simp [hs, hsqrtq, hsqrt1q, ha2, hU, hφprev]
    ring_nf
    field_simp [ha2, hφprev]
    rw [hsqrt1qSq]
    ring
  have hupdate :=
    itemf_first_update M C x0 hN hC hcoord
  apply Prod.ext
  · unfold W
    dsimp only
    rw [hk, itemfPreviousPlus_succ, itemfIterate_zero]
  · unfold W
    dsimp only
    rw [hk, itemfPreviousPlus_succ, itemfIterate_zero, hupdate]
    change
      s⁻¹ •
          (((1 - M.q) * a2) •
              ((M.gradientStep x0 -
                (φprev / (C.Upsilon * Real.sqrt (1 - M.q)) *
                  M.L⁻¹) • M.grad x0) - xStar) -
            (c * a1) • u) =
        b1 • u -
          (Real.sqrt (1 - M.q) / Real.sqrt M.q * M.L⁻¹) •
            M.grad x0
    have hx :
        (M.gradientStep x0 -
            (φprev / (C.Upsilon * Real.sqrt (1 - M.q)) *
              M.L⁻¹) • M.grad x0) - xStar =
          u -
            (φprev / (C.Upsilon * Real.sqrt (1 - M.q)) *
              M.L⁻¹) • M.grad x0 := by
      module
    rw [hx]
    simp only [smul_sub, smul_smul]
    calc
      _ =
          (s⁻¹ * (((1 - M.q) * a2) - c * a1)) • u -
            (s⁻¹ * ((1 - M.q) * a2) *
              (φprev / (C.Upsilon * Real.sqrt (1 - M.q)) *
                M.L⁻¹)) • M.grad x0 := by module
      _ = b1 • u -
          (Real.sqrt (1 - M.q) / Real.sqrt M.q * M.L⁻¹) •
            M.grad x0 := by
              rw [hscale]
              have hb :
                  s⁻¹ * (((1 - M.q) * a2) - c * a1) =
                    b1 := by
                field_simp [hs]
                nlinarith [hforward]
              rw [hb]

private theorem initial_norm_identity_of_terminal_coordinates
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (haN :
      C.a (idxN N) =
        C.Upsilon - radius C.Upsilon * Real.sqrt M.q)
    (hbN :
      C.b (idxN N) =
        radius C.Upsilon * Real.sqrt (1 - M.q)) :
    blockNormSq (W M C x0 xStar (firstLyapIndex hN)) =
      (1 - M.q) * ‖x0 - xStar‖ ^ 2 -
        (2 * C.Upsilon / M.μ) *
          (C.a (lyapCoeffIndex (firstLyapIndex hN)) -
            C.a (idxZero N)) *
          ⟪M.gradientStep x0 - xStar, M.shiftedGrad xStar x0⟫_ℝ +
        (C.Upsilon * C.a (idxZero N) / (M.μ * M.L)) *
          ‖M.shiftedGrad xStar x0‖ ^ 2 := by
  let k := firstLyapIndex hN
  let a0 := C.a (idxZero N)
  let a1 := C.a (lyapCoeffIndex k)
  let aN := C.a (idxN N)
  let b1 := C.b (lyapCoeffIndex k)
  let bN := C.b (idxN N)
  let u := M.gradientStep x0 - xStar
  let g := M.grad x0
  let gtilde := M.shiftedGrad xStar x0
  let rho := Real.sqrt (1 - M.q) / Real.sqrt M.q
  have hsqrtq :
      Real.sqrt M.q ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 M.q_pos)
  have hsqrtqSq :
      Real.sqrt M.q ^ 2 = M.q :=
    Real.sq_sqrt M.q_pos.le
  have hsqrt1qSq :
      Real.sqrt (1 - M.q) ^ 2 = 1 - M.q :=
    Real.sq_sqrt M.one_sub_q_pos.le
  have hmu : M.μ = M.q * M.L := M.q_mul_L.symm
  have hL : M.L ≠ 0 := ne_of_gt M.hL
  have hq : M.q ≠ 0 := M.q_ne_zero
  have hU : C.Upsilon ≠ 0 := hC.upsilon_ne_zero
  have ha1N : a1 * aN = 1 := by
    simpa [a1, aN, k] using hcoord.first_last
  have hb1N : a1 * bN = b1 := by
    simpa [a1, b1, bN, k] using hcoord.first_b
  have haNlocal :
      aN = C.Upsilon - radius C.Upsilon * Real.sqrt M.q := by
    exact haN
  have hbNlocal :
      bN = radius C.Upsilon * Real.sqrt (1 - M.q) := by
    exact hbN
  have hUa1 :
      C.Upsilon * a1 - 1 =
        Real.sqrt M.q * radius C.Upsilon * a1 := by
    calc
      C.Upsilon * a1 - 1 =
          a1 * (C.Upsilon - aN) := by nlinarith [ha1N]
      _ = Real.sqrt M.q * radius C.Upsilon * a1 := by
            rw [haNlocal]
            ring
  have hb1 :
      b1 = rho * (C.Upsilon * a1 - 1) := by
    calc
      b1 = a1 * bN := hb1N.symm
      _ = a1 * (radius C.Upsilon *
          Real.sqrt (1 - M.q)) := by
            rw [hbNlocal]
      _ = rho * (C.Upsilon * a1 - 1) := by
            rw [hUa1]
            dsimp [rho]
            field_simp [hsqrtq]
  have hidx :
      idxInterior k = lyapCoeffIndex k := by
    apply Fin.ext
    rfl
  have hcircleRaw := hC.circle k
  have hcircle :
      a1 ^ 2 + b1 ^ 2 = 2 * C.Upsilon * a1 - 1 := by
    rw [hidx] at hcircleRaw
    change
      (a1 - C.Upsilon) ^ 2 + b1 ^ 2 =
        radiusSq C.Upsilon at hcircleRaw
    unfold radiusSq at hcircleRaw
    nlinarith
  have ha0 : C.Upsilon * a0 = 1 := by
    dsimp [a0]
    rw [hC.a_zero]
    field_simp [hU]
  have hrhoSq :
      rho ^ 2 = (1 - M.q) / M.q := by
    dsimp [rho]
    field_simp [hsqrtq, hq]
    rw [hsqrtqSq, hsqrt1qSq]
    ring
  have hcircle' :
      a1 ^ 2 + b1 ^ 2 =
        1 + 2 * C.Upsilon * (a1 - a0) := by
    nlinarith [hcircle, ha0]
  have hcross :
      b1 * rho * M.L⁻¹ =
        C.Upsilon / M.μ * (a1 - a0) * (1 - M.q) := by
    rw [hb1, hmu]
    field_simp [hq, hL, hU, hsqrtq]
    rw [hrhoSq]
    field_simp [hq]
    nlinarith [ha0]
  have hW :=
    first_W_formula M C x0 xStar hN hC hcoord
  dsimp only at hW
  have hfirst :
      blockNormSq (W M C x0 xStar k) =
        ‖u‖ ^ 2 +
          ((1 - M.q) / (M.q * M.L ^ 2)) * ‖g‖ ^ 2 -
          (2 * C.Upsilon / M.μ) * (a1 - a0) *
            ⟪u, gtilde⟫_ℝ := by
    rw [hW]
    unfold blockNormSq
    change
      ‖a1 • u‖ ^ 2 +
          ‖b1 • u - (rho * M.L⁻¹) • g‖ ^ 2 =
        ‖u‖ ^ 2 +
          ((1 - M.q) / (M.q * M.L ^ 2)) * ‖g‖ ^ 2 -
          (2 * C.Upsilon / M.μ) * (a1 - a0) *
            ⟪u, gtilde⟫_ℝ
    have hshift :
        gtilde =
          (1 - M.q) • g + (-M.μ) • u := by
      simpa [gtilde, g, u] using M.shiftedGrad_eq xStar x0
    rw [hshift]
    change
      ‖a1 • u‖ ^ 2 +
          ‖b1 • u - (rho * M.L⁻¹) • g‖ ^ 2 =
        ‖u‖ ^ 2 +
          ((1 - M.q) / (M.q * M.L ^ 2)) * ‖g‖ ^ 2 -
          (2 * C.Upsilon / M.μ) * (a1 - a0) *
            ⟪u, (1 - M.q) • g + (-M.μ) • u⟫_ℝ
    simp only [norm_smul, Real.norm_eq_abs, norm_sub_sq_real,
      real_inner_smul_left, real_inner_smul_right,
      inner_add_right, real_inner_self_eq_norm_sq,
      mul_pow, sq_abs]
    calc
      a1 ^ 2 * ‖u‖ ^ 2 +
          (b1 ^ 2 * ‖u‖ ^ 2 -
            2 * (rho * M.L⁻¹ * (b1 * ⟪u, g⟫_ℝ)) +
            rho ^ 2 * M.L⁻¹ ^ 2 * ‖g‖ ^ 2) =
          (a1 ^ 2 + b1 ^ 2) * ‖u‖ ^ 2 +
            rho ^ 2 * M.L⁻¹ ^ 2 * ‖g‖ ^ 2 -
            2 * (b1 * rho * M.L⁻¹) * ⟪u, g⟫_ℝ := by ring
      _ = ‖u‖ ^ 2 +
          (1 - M.q) / (M.q * M.L ^ 2) * ‖g‖ ^ 2 -
          2 * C.Upsilon / M.μ * (a1 - a0) *
            ((1 - M.q) * ⟪u, g⟫_ℝ +
              (-M.μ) * ‖u‖ ^ 2) := by
                rw [hcircle', hrhoSq, hcross]
                field_simp [hq, hL, ne_of_gt M.hμ]
                ring
  have hu :
      u = (x0 - xStar) - M.L⁻¹ • g := by
    dsimp [u, g]
    simp only [StronglyConvexSmoothModel.gradientStep]
    module
  have hgtilde :
      gtilde = g - M.μ • (x0 - xStar) := by
    rfl
  have hbase :
      ‖u‖ ^ 2 +
          ((1 - M.q) / (M.q * M.L ^ 2)) * ‖g‖ ^ 2 =
        (1 - M.q) * ‖x0 - xStar‖ ^ 2 +
          (1 / (M.q * M.L ^ 2)) * ‖gtilde‖ ^ 2 := by
    rw [hu, hgtilde]
    simp only [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      real_inner_smul_left, real_inner_smul_right,
      mul_pow, sq_abs]
    rw [hmu]
    field_simp [hq, hL]
    rw [real_inner_comm g (x0 - xStar)]
    ring
  have hlastCoefficient :
      C.Upsilon * a0 / (M.μ * M.L) =
        1 / (M.q * M.L ^ 2) := by
    rw [hmu]
    field_simp [hq, hL, hU]
    exact ha0
  change
    blockNormSq (W M C x0 xStar k) =
      (1 - M.q) * ‖x0 - xStar‖ ^ 2 -
        (2 * C.Upsilon / M.μ) * (a1 - a0) *
          ⟪u, gtilde⟫_ℝ +
        (C.Upsilon * a0 / (M.μ * M.L)) * ‖gtilde‖ ^ 2
  rw [hfirst, hbase, hlastCoefficient]
  ring

private theorem interior_norm_identity
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN)
    (i : Fin (N - 1)) :
    let j := interiorLyapIndex i
    blockNormSq (W M C x0 xStar (nextInteriorLyapIndex i)) =
      blockNormSq
        (blockSub (W M C x0 xStar j)
          (blockScale (C.Upsilon / M.μ)
            (gapBlock M C x0 xStar j))) := by
  dsimp only
  rw [interior_W_rotation M C x0 xStar hN hC hcoord i]
  exact blockRotate_norm_sq (hcoord.interior_unit i) _

private theorem terminal_norm_identity
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN) :
    blockNormSq (W M C x0 xStar (terminalLyapIndex hN)) =
      (1 - M.q) * C.Upsilon ^ 2 *
          ‖itemfIterate M C x0 N - xStar‖ ^ 2 +
        (1 / M.q) *
          ‖((1 - M.q) * C.Upsilon) •
                (itemfIterate M C x0 N - xStar) -
            C.a (idxN N) •
                (itemfPreviousPlus M C x0 N - xStar)‖ ^ 2 := by
  let t := terminalLyapIndex hN
  have ht : t.1 + 1 = N := by
    dsimp [t, terminalLyapIndex]
    omega
  have hak : lyapCoeffIndex t = idxN N :=
    lyapCoeffIndex_terminal hN
  have hak1 : lyapNextCoeffIndex t = idxLast N :=
    lyapNextCoeffIndex_terminal hN
  have hc : cCoeff M.q C t = 1 - M.q :=
    hcoord.terminal_c
  have hs : sCoeff M.q C t =
      Real.sqrt M.q * Real.sqrt (1 - M.q) :=
    hcoord.terminal_s
  have hsquare :
      sCoeff M.q C t ^ 2 = M.q * (1 - M.q) := by
    rw [hs, mul_pow, Real.sq_sqrt M.q_pos.le,
      Real.sq_sqrt M.one_sub_q_pos.le]
  have hblock :=
    terminal_block_identity M.q C.Upsilon (C.a (idxN N))
      (sCoeff M.q C t) M.q_pos M.q_lt_one hsquare
      (itemfIterate M C x0 N - xStar)
      (itemfPreviousPlus M C x0 N - xStar)
  unfold blockNormSq W
  dsimp only
  rw [ht, hak, hak1, hc, hC.a_last]
  exact hblock

/-- Assemble all three norm identities once the scalar coordinate package has
been obtained from the construction. -/
theorem normIdentities_of_coordinateRelations
    (M : StronglyConvexSmoothModel E) (C : CoeffData N)
    (x0 xStar : E) (hN : 1 ≤ N)
    (hC : ValidCoefficients M.q C)
    (hcoord : CoordinateRelationsResult M.q C hN) :
    NormIdentitiesResult M C x0 xStar hN := by
  have hlastIndex :
      idxInterior (lastInteriorIndex N hN) = idxN N := by
    apply Fin.ext
    simp [lastInteriorIndex, idxInterior, idxN]
    omega
  have hbN :
      C.b (idxN N) =
        radius C.Upsilon * Real.sqrt (1 - M.q) := by
    have hterminal :=
      hC.b_lastInterior hN M.q_unit
    rw [hlastIndex] at hterminal
    nlinarith
  have haN :
      C.a (idxN N) =
        C.Upsilon - radius C.Upsilon * Real.sqrt M.q := by
    have hratio :=
      hC.terminal_ratio hN M.q_unit
    rw [hlastIndex] at hratio
    have hR :
        radius C.Upsilon ≠ 0 :=
      ne_of_gt (radius_pos hC.upsilon_gt_one)
    field_simp [hR] at hratio
    nlinarith
  exact
    {
      initial :=
        initial_norm_identity_of_terminal_coordinates
          M C x0 xStar hN hC hcoord haN hbN
      interior := interior_norm_identity M C x0 xStar hN hC hcoord
      terminal := terminal_norm_identity M C x0 xStar hN hC hcoord
    }

namespace Internal

/-- The three norm identities used by the ITEM-f Lyapunov argument. -/
theorem normIdentities
    (N : Nat) (hN : 1 ≤ N)
    (M : StronglyConvexSmoothModel E)
    (C : CoeffData N) (hC : ValidCoefficients M.q C)
    (x0 xStar : E) :
    NormIdentitiesResult M C x0 xStar hN := by
  exact
    normIdentities_of_coordinateRelations M C x0 xStar hN hC
      (ITEMf.Internal.coordinateRelations N M.q hN M.q_unit C hC)

end Internal

end ITEMf
