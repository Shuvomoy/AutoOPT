import ITEMf.Construction.ShootingNecessary
import ITEMf.Construction.Residual

/-!
# Fixed-parameter shooting equivalence and global construction

This module closes the geometric construction: a candidate table exists at a
fixed parameter exactly when the residual vanishes, and the residual has a
unique root.  The resulting finite coefficient table is therefore unique.
-/

set_option autoImplicit false

namespace ITEMf

lemma existsUnique_at_upsilon_of_residual
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon)
    (hres : shootingResidual N q Upsilon = 0) :
    ∃! C : CoeffData N,
      C.Upsilon = Upsilon ∧ ValidCoefficients q C := by
  let C := candidateData N q Upsilon
  have hvalid : ValidCoefficients q C := by
    dsimp only [C]
    exact candidateData_valid hN hq hUpsilon hres
  refine ⟨C, ⟨rfl, hvalid⟩, ?_⟩
  intro C' hC'
  have hrecover := hC'.2.eq_candidateData hN hq
  dsimp only [C]
  rw [hrecover, hC'.1]

lemma residual_of_existsUnique_at_upsilon
    {N : Nat} {q Upsilon : ℝ}
    (hN : 1 ≤ N) (hq : UnitRatio q)
    (hexists :
      ∃! C : CoeffData N,
        C.Upsilon = Upsilon ∧ ValidCoefficients q C) :
    shootingResidual N q Upsilon = 0 := by
  rcases hexists with ⟨C, hC, _⟩
  have hres := hC.2.shootingResidual_eq_zero hN hq
  rw [hC.1] at hres
  exact hres

namespace Internal

/-- Exact fixed-candidate shooting equivalence, including uniqueness of every
coordinate at a zero of the residual. -/
theorem shootingIffAdmissible
    (N : Nat) (q Upsilon : ℝ)
    (hN : 1 ≤ N) (hq : UnitRatio q) (hUpsilon : 1 < Upsilon) :
    ShootingIffAdmissibleResult N q Upsilon := by
  constructor
  · exact residual_of_existsUnique_at_upsilon hN hq
  · exact existsUnique_at_upsilon_of_residual hN hq hUpsilon

/-- Existence and uniqueness of the finite ITEM-f coefficient construction. -/
theorem coefficientsExistUnique
    (N : Nat) (q : ℝ) (hN : 1 ≤ N) (hq : UnitRatio q) :
    ∃! C : CoeffData N, ValidCoefficients q C := by
  rcases exists_residual_root hN hq with
    ⟨Upsilon, hUpsilon, hroot⟩
  let C := candidateData N q Upsilon
  have hvalid : ValidCoefficients q C := by
    dsimp only [C]
    exact candidateData_valid hN hq hUpsilon hroot
  refine ⟨C, hvalid, ?_⟩
  intro C' hC'
  have hroot' := hC'.shootingResidual_eq_zero hN hq
  have hUeq :
      C'.Upsilon = Upsilon :=
    residual_root_unique hN hq hC'.upsilon_gt_one hUpsilon hroot' hroot
  have hrecover := hC'.eq_candidateData hN hq
  dsimp only [C]
  rw [hrecover, hUeq]

end Internal
end ITEMf
