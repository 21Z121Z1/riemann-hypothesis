import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0089
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0056
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0105
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0106
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0032
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0099
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0028
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorSmooth
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0029
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0107
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0108
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0061
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTwoFramesComparison
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind

theorem stepCols_nonempty {N j : ℕ} (hj : j ≤ N) (i : Fin N) : (stepCols N j i).Nonempty := by
  by_cases h : (i : ℕ) + 1 ≤ j
  · refine ⟨⟨N - j, by have := i.2; omega⟩, ?_⟩
    simp [stepCols, h]
    omega
  · refine ⟨⟨0, by have := i.2; omega⟩, ?_⟩
    simp [stepCols, h]
    omega

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem coord_ne {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {q : Σ k, ι k}
    (hX : (X q : MRing ι) ∉ mCoordIdeal z) : x q ≠ 0 := by
  intro h
  apply hX
  have h1 : (X q : MRing ι) ∈ mCoordIdeal x := by
    show mConeMap x (X q) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h2 := hz.2 _ h1
  have h3 : z q = 0 := by simpa using h2
  show mConeMap z (X q) = 0
  rw [mConeMap, aeval_X, h3, map_zero, zero_mul]

theorem valMat_blockDiag {N j : ℕ} {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {A : Matrix (Fin N) (Fin N) Ω} (hA : IsBlockDiag j A) : IsBlockDiag j (valMat x z A) := fun a b h => by
  show valAt x (A a b) z = 0
  rw [hA a b h]
  exact map_zero (regVal x hz)

theorem reg_chain {N : ℕ} {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {A B C : Matrix (Fin N) (Fin N) Ω} (hB : B.det ≠ 0)
    (h₁ : ∀ a b, RegAt x (mCoordIdeal z) ((A⁻¹ * B) a b)) (h₂ : ∀ a b, RegAt x (mCoordIdeal z) ((B⁻¹ * C) a b)) :
    (∀ a b, RegAt x (mCoordIdeal z) ((A⁻¹ * C) a b)) ∧
      valMat x z (A⁻¹ * C) = valMat x z (A⁻¹ * B) * valMat x z (B⁻¹ * C) := by
  have e : A⁻¹ * C = (A⁻¹ * B) * (B⁻¹ * C) := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hB)]
  rw [e]
  exact regMat_mul hz h₁ h₂

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

theorem minor_of_plk (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : b ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal b)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {I : Finset (Fin N)} (hI : IsStepRows N j p.2 I) {g : Matrix (Fin N) (Fin N) ℂ}
    (hg : IsBlockDiag j g) :
    ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * plk M F b p.2 ⟨k, m⟩ g = minorIJ g I (stepCols N j p.2) := by
  have hi := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hz : ∀ I', ¬ IsStepRows N j p.2 I' → minorIJ g I' (stepCols N j p.2) = 0 := fun I' h =>
    (hi.2.1 g I' hg h).resolve_right (stepCols_nonempty M.j_le p.2).ne_empty
  have hv : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b = if I = I' then 1 else 0 := by
    intro I' hI'
    have h1 := hF.2.2.1 p k hk I I' hI hI'
    have h2 := (reg_sum hb Finset.univ (fun m : ι k => F.u' I ⟨k, m⟩ * F.u ⟨k, m⟩ I') fun m _ =>
      ValRing.regAt_mul (hG.2.1 _ _).2 (hG.2.1 _ _).1).2
    rw [h1] at h2
    rw [Finset.sum_congr rfl fun m _ => (reg_mul hb (hG.2.1 _ _).2 (hG.2.1 _ _).1).2.symm, ← h2]
    split_ifs
    · exact map_one (regVal M.x hb)
    · exact map_zero (regVal M.x hb)
  calc ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * plk M F b p.2 ⟨k, m⟩ g
      = ∑ I', (∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ I') b) *
          minorIJ g I' (stepCols N j p.2) := by
        simp only [plk, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = ∑ I', if I = I' then minorIJ g I' (stepCols N j p.2) else 0 := Finset.sum_congr rfl fun I' _ => by
        by_cases h : IsStepRows N j p.2 I'
        · rw [hv I' h]; split_ifs <;> simp
        · rw [hz I' h]; simp
    _ = minorIJ g I (stepCols N j p.2) := by simp

theorem minor_eq_of_plk (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk} {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : b ∈ mcPts (mCoordIdeal M.x)) (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal b)) {p : Ψ × Fin N} {k : K}
    (hk : M.blk p = some k) {g g₂ : Matrix (Fin N) (Fin N) ℂ} (hg : IsBlockDiag j g) (hg₂ : IsBlockDiag j g₂) {μ : ℂ}
    (h : ∀ m : ι k, plk M F b p.2 ⟨k, m⟩ g = μ * plk M F b p.2 ⟨k, m⟩ g₂) (I : Finset (Fin N)) :
    minorIJ g I (stepCols N j p.2) = μ * minorIJ g₂ I (stepCols N j p.2) := by
  by_cases hI : IsStepRows N j p.2 I
  · rw [← minor_of_plk M hb hF hG hk hI hg, ← minor_of_plk M hb hF hG hk hI hg₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h m]; ring
  · have hi := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
    have hne := (stepCols_nonempty M.j_le p.2).ne_empty
    rw [(hi.2.1 g I hg hI).resolve_right hne, (hi.2.1 g₂ I hg₂ hI).resolve_right hne, mul_zero]

end SlopeTestRemainingChoices

theorem plk_moved_indep : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F₁' F₂' : FrameData ι' Ψ N M'.Ω M'.blk) (F₁ F₂ : FrameData ι Ψ N M.Ω M.blk) (H₁ H₂ : Ψ → Matrix (Fin N) (Fin N) ℂ), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F₁' → M'.IsFrame F₂' → M.IsFrame F₁ → M.IsFrame F₂ → M'.GoodAt F₁' (mCoordIdeal b) → M'.GoodAt F₂' (mCoordIdeal b) → M.GoodAt F₁ (mCoordIdeal (b ∘ Cv.v)) → M.GoodAt F₂ (mCoordIdeal (b ∘ Cv.v)) → (∀ τ, IsBlockDiag j (H₁ τ)) → (∀ τ, IsBlockDiag j (H₂ τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', CovMap.LocImg.plk M' F₁' b p.2 ⟨k', m'⟩ (H₁ p.1) = a * CovMap.LocImg.plk M' F₂' b p.2 ⟨k', m'⟩ (H₂ p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.plk M F₁ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) = a * CovMap.LocImg.plk M F₂ (b ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F₂' F₂ b p.1 * H₂ p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv b F₁' F₂' F₁ F₂ H₁ H₂ hb hF₁' hF₂' hF₁ hF₂ hG₁' hG₂' hG₁ hG₂
    hH₁ hH₂ hyp p k hk
  obtain ⟨k', hk'⟩ := exists_blk_cover M' hk
  obtain ⟨hbv, hpt⟩ := GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv b hb
  have hi := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have dT₁' := (hF₁'.1 p.1).2
  have dP : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.IsFrame F → ((F.T p.1).map Cv.φ).det ≠ 0 := fun F hF => by
    have e : ((F.T p.1).map Cv.φ).det = Cv.φ (F.T p.1).det := (RingHom.map_det Cv.φ (F.T p.1)).symm
    rw [e]
    exact (map_ne_zero Cv.φ).2 (hF.1 p.1).2
  have r₁₁ := fun a c => Cv.agree b hb F₁' F₁ hF₁' hF₁ hG₁' hG₁ p.1 a c
  have r₁₂ := fun a c => Cv.agree b hb F₁' F₂ hF₁' hF₂ hG₁' hG₂ p.1 a c
  have r₂₁ := fun a c => Cv.agree b hb F₂' F₁ hF₂' hF₁ hG₂' hG₁ p.1 a c
  have r₂₂ := fun a c => Cv.agree b hb F₂' F₂ hF₂' hF₂ hG₂' hG₂ p.1 a c
  have c₁ := reg_chain hb (dP F₁ hF₁) (fun a c => (r₁₁ a c).2) (fun a c => (r₂₁ a c).1)
  have c₂ := reg_chain hb (dP F₁ hF₁) (fun a c => (r₂₁ a c).2) (fun a c => (r₁₁ a c).1)
  have c₃ := reg_chain hb dT₁' (fun a c => (r₁₁ a c).1) (fun a c => (r₁₂ a c).2)
  have c₄ := reg_chain hb dT₁' (fun a c => (r₁₂ a c).1) (fun a c => (r₁₁ a c).2)
  have c₅ := reg_chain hb dT₁' (fun a c => (r₁₁ a c).1) c₁.1
  have c₆ := reg_chain hb (dP F₂ hF₂) c₃.1 (fun a c => (r₂₂ a c).1)

  have eid : ∀ A : Matrix (Fin N) (Fin N) M'.Ω, A.map (RingHom.id M'.Ω) = A := fun A => by ext; rfl
  obtain ⟨c', hc'0, hc'⟩ := GlobalTheory.T.frame_change_under_field_map K' ι' Φ' y' Ψ N j M' (NonPluckerBlocks M'.blk) (baseIdx ι' M'.blk) M'.Ω M'.x
    (RingHom.id _) b F₁' F₂' hb hF₁' hF₂' (fun k => coord_ne hb (hG₁'.1 k)) (fun k => coord_ne hb (hG₂'.1 k)) p k' hk'
    (fun m I => ⟨(hG₁'.2.1 _ _).1, (hG₂'.2.1 _ _).1, (hG₁'.2.1 _ _).2, (hG₂'.2.1 _ _).2⟩)
    (fun a c => by simp only [eid]; exact ⟨c₁.1 a c, c₂.1 a c⟩)
  simp only [eid, RingHom.id_apply] at hc'
  obtain ⟨a, ha0, hA⟩ := hyp p k' hk'
  obtain ⟨S', hS'⟩ : ∃ S', S' = valMat M'.x b ((F₁'.T p.1)⁻¹ * F₂'.T p.1) := ⟨_, rfl⟩
  rw [← hS'] at hc'
  have bdS' : IsBlockDiag j S' := hS' ▸ valMat_blockDiag hb
    (((hF₁'.1 p.1).1.inv (isUnit_iff_ne_zero.2 dT₁')).mul (hF₂'.1 p.1).1)
  obtain ⟨μ, hμd⟩ : ∃ μ, μ = c' * a⁻¹ := ⟨_, rfl⟩
  have hμ : μ ≠ 0 := hμd ▸ mul_ne_zero hc'0 (inv_ne_zero ha0)
  have e₁ : ∀ m : ι' k', plk M' F₁' b p.2 ⟨k', m⟩ (S' * H₂ p.1) = μ * plk M' F₁' b p.2 ⟨k', m⟩ (H₁ p.1) := fun m => by
    rw [hA m, hμd, ← mul_assoc, mul_assoc c', inv_mul_cancel₀ ha0, mul_one]
    exact hc' (H₂ p.1) (hH₂ p.1) m
  have e₂ := minor_eq_of_plk M' hb hF₁' hG₁' hk' (bdS'.mul (hH₂ p.1)) (hH₁ p.1) e₁

  obtain ⟨S, hS⟩ : ∃ S, S = valMat M'.x b (((F₁.T p.1).map Cv.φ)⁻¹ * (F₂.T p.1).map Cv.φ) := ⟨_, rfl⟩
  have eT : Cv.trans F₁' F₁ b p.1 * S' = S * Cv.trans F₂' F₂ b p.1 := by
    rw [hS', hS]
    exact c₅.2.symm.trans c₆.2
  have e₃ : ∀ I, minorIJ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) I (stepCols N j p.2) =
      μ⁻¹ * minorIJ (S * (Cv.trans F₂' F₂ b p.1 * H₂ p.1)) I (stepCols N j p.2) := fun I => by
    rw [← Matrix.mul_assoc S, ← eT, Matrix.mul_assoc, hi.1 _ (S' * H₂ p.1), hi.1 _ (H₁ p.1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [e₂ I']
    field_simp

  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.frame_change_under_field_map K ι Φ y Ψ N j M (NonPluckerBlocks M'.blk) (baseIdx ι' M'.blk) M'.Ω M'.x Cv.φ b F₁ F₂
    hb hF₁ hF₂ (fun k => coord_ne hbv (hG₁.1 k)) (fun k => coord_ne hbv (hG₂.1 k)) p k hk
    (fun m I => ⟨(hpt _ (hG₁.2.1 _ _).1).1, (hpt _ (hG₂.2.1 _ _).1).1, (hpt _ (hG₁.2.1 _ _).2).1,
      (hpt _ (hG₂.2.1 _ _).2).1⟩)
    (fun a c => ⟨c₃.1 a c, c₄.1 a c⟩)
  rw [← hS] at hc
  have bdT₂ := (GlobalTheory.T.flag_cover_frame_compatibility K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv b F₂' F₂ hb hF₂' hF₂ hG₂' hG₂ p.1).1
  have hval : ∀ F : FrameData ι Ψ N M.Ω M.blk, M.GoodAt F (mCoordIdeal (b ∘ Cv.v)) → ∀ q I,
      valAt M'.x (Cv.φ (F.u q I)) b = valAt M.x (F.u q I) (b ∘ Cv.v) := fun F hG q I => (hpt _ (hG.2.1 q I).1).2
  refine ⟨μ⁻¹ * c, mul_ne_zero (inv_ne_zero hμ) hc0, fun m => ?_⟩
  have h3 := hc (Cv.trans F₂' F₂ b p.1 * H₂ p.1) (bdT₂.mul (hH₂ p.1)) m
  simp only [hval F₁ hG₁, hval F₂ hG₂] at h3
  simp only [plk]
  calc ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) (b ∘ Cv.v) *
        minorIJ (Cv.trans F₁' F₁ b p.1 * H₁ p.1) I (stepCols N j p.2)
      = μ⁻¹ * ∑ I, valAt M.x (F₁.u ⟨k, m⟩ I) (b ∘ Cv.v) *
        minorIJ (S * (Cv.trans F₂' F₂ b p.1 * H₂ p.1)) I (stepCols N j p.2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun I _ => by rw [e₃ I]; ring
    _ = _ := by rw [h3, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagGapSameBaseOrbitStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_gap_same_base_orbit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (x₀ : BM.Rb.X) (z z' : (Σ k, ι k) → ℂ), x₀ ∉ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → z' ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → basePart M.blk z = basePart M.blk z' → (∀ k, M.blk p = some k → ∀ m : ι k, z ⟨k, m⟩ = z' ⟨k, m⟩) → stepGap M BM p z = stepGap M BM p z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block | exact GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.StepW.stepGap_eq_of_base_block <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystem
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem genDeg_of_system (h : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement) :
    GenDegStatement :=
  GlobalTheory.T.generic_degree_of_projection_and_fibre_dim (GlobalTheory.T.coordinate_projection_of_arith_system h) fibreDim

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeRegularStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_change_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → FramesOK (aOf 𝔐 bW bO φ) x₀ m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_main | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameHeightFormulaStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_height_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ (h : ModelOK (aOf 𝔐 bW bO φ) x₀ m) (𝔐' : HodgeCpt Y S (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) (pr : 𝔐'.X ⟶ 𝔐.X) (j : 𝔐.Li →+ 𝔐'.Li) (Fl : 𝔐'.Flag), HodgeOver 𝔐' 𝔐 pr (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) j → Submodule.span (GenField Ω (rk (CMType H) D.p D.q)) (Set.range j) = ⊤ → (∀ s, 𝔐'.V s = (𝔐.V s).pull 𝔐'.ξ pr j) → ColFlags 𝔐 bW bO j Fl → ∃ xdeg : CMType H × Fin (D.p + D.q) → (K₀ ⊕ StepIx (CMType H) D.p D.q) → ℤ, Fl.RootLines xdeg (fun _ => 1) ∧ ∀ τ i, (model (aOf 𝔐 bW bO φ) x₀ m h).dy (τ, i) = -∑ k ∈ Finset.Iic i, xdeg (τ, k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots.rootLines | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots.rootLines | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Roots.rootLines <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeMetricFramePropertiesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_metric_frame_properties : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D), (∀ z ∈ mcPts (mCoordIdeal D.y), Nonempty (MuFrameAt Hd z)) ∧ (∀ z ∈ D.Xo, ∀ d : MuFrameAt Hd z, 0 < d.norm ∧ (muLine Hd).h z = d.norm) ∧ LogHom D Hd.aMu (phMu Hd) ∧ ConjOff D (phMu Hd) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_metric_frame_properties | exact GlobalTheory.CompanionTheory.Relay.hodge_metric_frame_properties | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_metric_frame_properties <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberMetricChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_metric_change : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing J)) (n : ℕ) (A B : HermLine J), IsFullIntersectionSystem II → IsArithVar P (n + 1) → IsSmoothHerm A → IsSmoothHerm B → B.a = A.a → II K J P (n + 1) (fun _ => B) = II K J P (n + 1) (fun _ => A) - ∑ i ∈ Finset.range (n + 1), ptsIntegral P (pot fun j : Fin n => if (j : ℕ) < i then B else A) (fun z => Real.log (A.h z) - Real.log (B.h z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tele.telescope | exact GlobalTheory.CompanionTheory.Ar.Tele.telescope | (intros; apply GlobalTheory.CompanionTheory.Ar.Tele.telescope <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionNumberTelescopingStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_telescoping : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P : Ideal (MRing ι)) (n : ℕ) (a a₀ A' : HermLine ι) (k : ℕ), IsArithVar P (n + 1) → IsSmoothHerm a → IsSmoothHerm a₀ → IsSmoothHerm A' → a.a = a₀.a → k ≤ n + 1 → I P (n + 1) (fun j => if (j : ℕ) < k then a else A') - I P (n + 1) (fun j => if (j : ℕ) < k then a₀ else A') = -∑ i ∈ Finset.range k, ptsIntegral P (pot (mixWord (n := n) a a₀ A' k i)) (logRatio a a₀) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.Tele.positionTelescope <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalSectionVerticalFactorStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Mix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_vertical_factor : ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (p : ℕ) (M : XModel D) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ), p ∈ D.S → IsOpen U → (∀ y ∈ U, s y ∈ mcPts (mCoordIdeal D.y)) → (∀ q, M.atlas.HoloOn U fun y => s y q) → ∀ y₀ ∈ U, ∃ V : Set M.Xc, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ U ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn V G ∧ ∀ y ∈ V, Real.log (D.vertFactor p (s y)) = (G y).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Mix.log_vertFactor_eq_re_holo | exact GlobalTheory.CompanionTheory.Ar.Giv.Mix.log_vertFactor_eq_re_holo | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Mix.log_vertFactor_eq_re_holo <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEigenFramePlurisubharmonicStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_det_eigen_frame_plurisubharmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (n : ℕ) (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ), IsOpen U → IsHolFam U R → IsCMFam σ → IsEigFrames U (fun t => (R t).B) σ b → ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t)) ∧ ReciprocityTheory.AnForm.A.IsPsh U (fun t => (R t).logDet (fun τ i => b τ i t) + (R t).cuspW σ) ∧ ContinuousOn (fun t => (R t).cuspW σ) U := by
  first | exact @GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic | exact GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic | (intros; apply GlobalTheory.CompanionTheory.Relay.log_det_eigen_frame_plurisubharmonic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFromOrbitCharts
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}

theorem analyticAt_eval {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : E → σ → ℂ} {w₀ : E}
    (hg : ∀ q, AnalyticAt ℂ (fun w => g w q) w₀) (f : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun w => eval (g w) f) w₀ := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    refine (hp.add hq).congr (Filter.Eventually.of_forall fun w => ?_)
    simp
  | mul_X p n hp =>
    refine (hp.mul (hg n)).congr (Filter.Eventually.of_forall fun w => ?_)
    simp

section Overlap

variable (hP : IsMultiHomogIdeal P) (C₁ C₂ : OrbitChart P e) (x₁ x₂ : PtsOf P)
include hP

theorem mem_O_of_mem_srcOf {w : Fin e → ℂ} (hw : w ∈ C₁.D) (h : clsT x₁ (C₁.φ w) ∈ srcOf C₂) : C₁.φ w ∈ C₂.O := by
  have h' : rep (cls (C₁.φ w) (C₁.mem w hw)) ∈ C₂.O := by
    rw [← clsT_of_mem x₁ (C₁.mem w hw)]
    exact h
  exact mem_O_of_orbit C₂ hP h' (Proj.orbit_symm (rep_cls_orbit _ _)) (rep_mem_mcPts _)

theorem rho_clsT {w : Fin e → ℂ} (hw : w ∈ C₁.D) (h : clsT x₁ (C₁.φ w) ∈ srcOf C₂) :
    C₂.ρ (rep (clsT x₁ (C₁.φ w))) = C₂.ρ (C₁.φ w) := by
  have hO := mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw h
  refine C₂.ρ_orbit _ hO _ h ?_
  rw [clsT_of_mem x₁ (C₁.mem w hw)]
  exact rep_cls_orbit _ _

theorem isOpen_overlap :
    IsOpen ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) :=
  (orbChart hP C₁ x₁).isOpen_inter_preimage_symm (isOpen_srcOf hP C₂)

theorem analytic_transition :
    AnalyticOnNhd ℂ (orbChart hP C₂ x₂ ∘ (orbChart hP C₁ x₁).symm)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' (orbChart hP C₂ x₂).source) := by
  have h1 : AnalyticOnNhd ℂ (fun w => C₂.ρ (C₁.φ w))
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) :=
    (GlobalTheory.T.orbit_chart_transition_analytic K ι P e C₁ C₂).mono fun w hw => ⟨hw.1, mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw.1 hw.2⟩
  exact h1.congr (isOpen_overlap hP C₁ C₂ x₁) fun w hw => (rho_clsT hP C₁ C₂ x₁ hw.1 hw.2).symm

theorem analytic_lift (p : Σ k, ι k) :
    AnalyticOnNhd ℂ ((fun y : PtsOf P => C₂.φ (C₂.ρ (rep y)) p) ∘ (orbChart hP C₁ x₁).symm)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) := by
  have h1 : AnalyticOnNhd ℂ (fun w => C₂.φ (C₂.ρ (C₁.φ w)) p)
      ((orbChart hP C₁ x₁).target ∩ (orbChart hP C₁ x₁).symm ⁻¹' srcOf C₂) := fun w hw => by
    have hO := mem_O_of_mem_srcOf hP C₁ C₂ x₁ hw.1 hw.2
    exact AnalyticAt.comp (g := fun v => C₂.φ v p) (f := fun w => C₂.ρ (C₁.φ w))
      (C₂.holo p _ (C₂.ρ_mem _ hO)) (GlobalTheory.T.orbit_chart_transition_analytic K ι P e C₁ C₂ w ⟨hw.1, hO⟩)
  refine h1.congr (isOpen_overlap hP C₁ C₂ x₁) fun w hw => ?_
  have e1 : C₂.ρ (rep (clsT x₁ (C₁.φ w))) = C₂.ρ (C₁.φ w) := rho_clsT hP C₁ C₂ x₁ hw.1 hw.2
  show C₂.φ (C₂.ρ (C₁.φ w)) p = C₂.φ (C₂.ρ (rep (clsT x₁ (C₁.φ w)))) p
  rw [e1]

theorem immersion_lift {x : PtsOf P} (hx₂ : x ∈ srcOf C₂) (hx₁ : x ∈ srcOf C₁) (p : (k : K) → ι k)
    (hp : ∀ k, C₂.φ (C₂.ρ (rep x)) ⟨k, p k⟩ ≠ 0) :
    (fderiv ℂ (fun y => affCoord p (C₂.φ (C₂.ρ (rep ((orbChart hP C₁ x₁).symm y)))))
      (orbChart hP C₁ x₁ x)).ker = ⊥ := by
  set ψ := orbChart hP C₁ x₁ with hψ
  have hw₀ : ψ x ∈ ψ.target := ψ.map_source hx₁
  have hsym : ψ.symm (ψ x) = x := ψ.left_inv hx₁
  have hV : ψ.target ∩ ψ.symm ⁻¹' srcOf C₂ ∈ 𝓝 (ψ x) :=
    (isOpen_overlap hP C₁ C₂ x₁).mem_nhds ⟨hw₀, by rw [Set.mem_preimage, hsym]; exact hx₂⟩
  have heq : (fun y => affCoord p (C₂.φ (C₂.ρ (rep (ψ.symm y))))) =ᶠ[𝓝 (ψ x)]
      fun y => affCoord p (C₁.φ y) := by
    filter_upwards [hV] with w hw
    have hm := C₁.mem w hw.1
    have h1 : SameOrbit (rep (ψ.symm w)) (C₁.φ w) := by
      show SameOrbit (rep (clsT x₁ (C₁.φ w))) (C₁.φ w)
      rw [clsT_of_mem x₁ hm]
      exact rep_cls_orbit _ hm
    exact Proj.affCoord_eq (Proj.orbit_trans (C₂.φ_ρ _ hw.2) h1) p
  rw [heq.fderiv_eq]
  have ho : SameOrbit (C₂.φ (C₂.ρ (rep x))) (C₁.φ (ψ x)) :=
    Proj.orbit_trans (C₂.φ_ρ _ hx₂) (Proj.orbit_symm (C₁.φ_ρ _ hx₁))
  exact C₁.immersion _ hw₀ p fun k => Proj.orbit_ne ho (hp k)

end Overlap

def atlasOf (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) : FinHolAtlas e (PtsOf P) where
  n := t.card
  chart j := orbChart hP (Cx (t.equivFin.symm j)) (t.equivFin.symm j)
  cover x := by
    obtain ⟨y, hy, hx⟩ := hcov x
    refine ⟨t.equivFin ⟨y, hy⟩, ?_⟩
    show x ∈ srcOf (Cx (t.equivFin.symm (t.equivFin ⟨y, hy⟩)))
    rw [Equiv.symm_apply_apply]
    exact hx
  holo j k := analytic_transition hP _ _ _ _

theorem isCompat_orbChart (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) (C : OrbitChart P e) (x₀ : PtsOf P) :
    IsCompatChart (atlasOf hP Cx t hcov) (orbChart hP C x₀) := fun _ =>
  ⟨analytic_transition hP _ _ _ _, analytic_transition hP _ _ _ _⟩

theorem holoOn_eval (hP : IsMultiHomogIdeal P) (Cx : PtsOf P → OrbitChart P e) (t : Finset (PtsOf P))
    (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) (C : OrbitChart P e) (f : MvPolynomial (Σ k, ι k) ℂ) :
    (atlasOf hP Cx t hcov).HoloOn (srcOf C) (fun y => eval (C.φ (C.ρ (rep y))) f) := fun j w hw =>
  analyticAt_eval (g := fun w => C.φ (C.ρ (rep (((atlasOf hP Cx t hcov).chart j).symm w))))
    (fun q => analytic_lift hP _ C _ q w hw) f

def resOf (hP : IsMultiHomogIdeal P) (hnd : ¬ (⊤ : Ideal (MRing ι)) ≤ P) (Cx : PtsOf P → OrbitChart P e)
    (hCx : ∀ x, x ∈ srcOf (Cx x)) (t : Finset (PtsOf P)) (hcov : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y)) :
    AnLogRes P ⊤ e where
  homog := ⟨{1}, fun f hf => ⟨0, by
    rw [Set.mem_singleton_iff.1 hf]
    intro m hm k
    have hm0 : m = 0 := by
      rw [MvPolynomial.support_one] at hm
      simpa using hm
    simp [hm0]⟩, by simp⟩
  nondeg := hnd
  X := PtsOf P
  top := inferInstance
  compact := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  t2 := inferInstance
  A := atlasOf hP Cx t hcov
  U x := srcOf (Cx x)
  isOpen_U x := isOpen_srcOf hP _
  mem_U := hCx
  lift x y := (Cx x).φ ((Cx x).ρ (rep y))
  holo x p j := analytic_lift hP _ _ _ p
  mem x y hy := (Cx x).mem _ ((Cx x).ρ_mem _ hy)
  compat x x' y hy := Proj.orbit_trans ((Cx x).φ_ρ _ hy.1) (Proj.orbit_symm ((Cx x').φ_ρ _ hy.2))
  surj z hz _ := ⟨cls z hz, Proj.orbit_trans ((Cx _).φ_ρ _ (hCx _)) (rep_cls_orbit z hz)⟩
  inj x x' _ h := pts_eq_of_orbit (Proj.orbit_trans (Proj.orbit_symm ((Cx x).φ_ρ _ (hCx x)))
    (Proj.orbit_trans h ((Cx x').φ_ρ _ (hCx x'))))
  immersion x _ p hp j hj := immersion_lift hP _ (Cx x) _ (hCx x) hj p hp
  snc f a _ _ hz := ⟨0, Fin.elim0, Fin.elim0, fun x => ⟨orbChart hP (Cx x) x, isCompat_orbChart hP Cx t hcov _ _,
    hCx x, subset_rfl, Fin.elim0, fun k => k.elim0, fun k => k.elim0,
    fun y => eval ((Cx x).φ ((Cx x).ρ (rep y))) (map (Int.castRingHom ℂ) f),
    holoOn_eval hP Cx t hcov (Cx x) _,
    fun y hy h0 => Proj.not_mem_mcPts_top _ (hz _ ((Cx x).mem _ ((Cx x).ρ_mem _ hy)) h0),
    fun y _ => by simp⟩⟩
  null j := by
    have : {x : PtsOf P | (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts (⊤ : Ideal (MRing ι))} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x => Proj.not_mem_mcPts_top _
    rw [this]
    simp

theorem exists_anLogRes_of_orbitCharts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ), Nonempty K → IsMultiHomogIdeal P → ¬ (⊤ : Ideal (MRing ι)) ≤ P → (∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) → ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ), IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧ ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := by
  intro K _ ι _ P e _ hP hnd hcov
  have h' : ∀ x : PtsOf P, ∃ C : OrbitChart P e, x ∈ srcOf C := fun x => hcov _ (rep_mem_mcPts x)
  choose Cx hCx using h'
  haveI : CompactSpace (PtsOf P) := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => srcOf (Cx x))
    (fun x _ => (isOpen_srcOf hP _).mem_nhds (hCx x))
  have hc : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y) := fun x => by
    simpa using ht.2 (Set.mem_univ x)
  refine ⟨resOf hP hnd Cx hCx t hc, fun C hne => ?_⟩
  obtain ⟨z, hz⟩ := hne
  have ho : ∀ x : PtsOf P, SameOrbit ((Cx x).φ ((Cx x).ρ (rep x))) (rep x) := fun x => (Cx x).φ_ρ _ (hCx x)
  have hm : ∀ x : PtsOf P, (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts P := fun x => (Cx x).mem _ ((Cx x).ρ_mem _ (hCx x))
  refine ⟨orbChart hP C (cls z hz), isCompat_orbChart hP Cx t hc C _, rfl, fun x => ?_, fun x hx => ?_⟩
  · exact ⟨fun h => mem_O_of_orbit C hP h (ho x) (rep_mem_mcPts x),
      fun h => mem_O_of_orbit C hP h (Proj.orbit_symm (ho x)) (hm x)⟩
  · exact Proj.orbit_trans (C.φ_ρ _ hx) (Proj.orbit_symm (ho x))

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFubiniStudyPositiveStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_resolution_fubini_study_positive : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P ⊤ D), (∀ A : HermLine ι, IsSmoothHerm A → IsPotential R.A (potOf R A)) ∧ IsSmoothHerm (fsHerm ι fun _ => 1) ∧ IsPosPot R.A (potOf R (fsHerm ι fun _ => 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential | exact GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.fs_pos_potential <;> assumption)
end

