import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0254
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0095
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0261
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0194
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0060
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStep
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0263

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallVolSuccSqStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ballVol_succ_sq_eq_pow_mul_prod : ∀ (P Q : ℕ) (r : ℝ), 0 < r → ballVol ((P + Q + 1) ^ 2) r = (2 : ℝ≥0∞) ^ (P + Q) * ((volume : Measure (ℝ × Sp P Q)).prod (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))) {p | tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} := by
  first | exact @GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq | exact GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq | (intros; apply GlobalTheory.GaugeQuot.BallProd.ballVol_succ_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockPerpEmbeddingOfDiagonalFrameStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockPerpEmbedding_of_diagonal_frame : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' → Formalism.REAL.UJ ε), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, Formalism.MainNotions.S.uMat (j g) *ᵥ x₀ = x₀ ∧ Formalism.MainNotions.S.uMat (j g) * B = B * Formalism.MainNotions.S.uMat g) → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n) (hf : Sorts ε f) (hf' : Sorts ε' f'), IsPerpEmb (fun i => x₀ (f i)) (B.submatrix f f') (fun g => hf.equiv.symm (j (hf'.equiv g))) := by
  first | exact @GlobalTheory.PerpSort.isPerpEmb_of_sorts | exact GlobalTheory.PerpSort.isPerpEmb_of_sorts | (intros; apply GlobalTheory.PerpSort.isPerpEmb_of_sorts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliEigenvalueKFiniteDiscreteSeriesCoeff
section
open Matrix PI.UpqRep

namespace GlobalTheory.CapelliEigenvalue

open PI.UnitaryGroupMassFormula.CapelliEig

theorem coefSm_of (hT : CapTransport) (hF : FunAct) (hD : PI.DSInfCharCap.DSInfCharCap) : CoefSm := by
  intro k r ε lam Hs _ _ _ σ Wp Wq _ _ _ _ _ _ hlam hds P Q hQ Y g hg
  obtain ⟨P₀, hcayU, hDS⟩ := hds
  obtain ⟨⟨hunit, hcay⟩, hPu⟩ := hcayU
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hleft : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hright : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm

  obtain ⟨hvec, hsm⟩ := smooth_translation k r ε Hs σ Wp Wq P₀ ⟨⟨hunit, hcay⟩, hPu⟩ P Q hQ

  have hgJ : Formalism.REAL.inUJ ε (P₀ * g * P₀⁻¹) := by
    have hg0 : gᴴ * (P₀ᴴ * Formalism.REAL.Jm ε * P₀) * g = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := by
      rw [← hH]; exact hg
    show (P₀ * g * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P₀ * g * P₀⁻¹) = Formalism.REAL.Jm ε
    calc (P₀ * g * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P₀ * g * P₀⁻¹)
        = (P₀⁻¹)ᴴ * (gᴴ * (P₀ᴴ * Formalism.REAL.Jm ε * P₀) * g) * P₀⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P₀⁻¹)ᴴ * (P₀ᴴ * Formalism.REAL.Jm ε * P₀) * P₀⁻¹ := by rw [hg0]
      _ = (P₀ * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P₀ * P₀⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by
          rw [hright, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hback : P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = g := by
    calc P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = (P₀⁻¹ * P₀) * g * (P₀⁻¹ * P₀) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hleft, Matrix.one_mul, Matrix.mul_one]

  have hu : Y + (((2 * r + k : ℕ) : ℂ)) / 2 = Y + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2 := by
    push_cast; ring

  have htr : Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk k r) (Y + (((2 * r + k : ℕ) : ℂ)) / 2)
      (fun x => P.comp ((σ x).comp Q)) g =
      Formalism.QuantumDeterminants.capelli ε (Y + (((2 * r + k : ℕ) : ℂ)) / 2)
        (fun x => P.comp ((σ (P₀⁻¹ * x * P₀)).comp Q)) (P₀ * g * P₀⁻¹) :=
    hT (2 * r + k + 1) ε (Wq →L[ℂ] Wp) (Formalism.QuantumDeterminants.Hpk k r) P₀ P₀⁻¹
      (fun x => P.comp ((σ x).comp Q)) _ g hleft hright hH hsm hg
  show Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk k r) (Y + (((2 * r + k : ℕ) : ℂ)) / 2)
      (fun x => P.comp ((σ x).comp Q)) g = _
  rw [htr]
  ext w
  rw [hF (2 * r + k + 1) ε lam Hs (fun x => σ (P₀⁻¹ * x * P₀)) Wp Wq hDS P Q hvec _ _ hgJ w]
  simp only [hback]
  rw [hu, hD (2 * r + k + 1) ε lam Hs (fun x => σ (P₀⁻¹ * x * P₀)) hlam hDS (Q w) (hvec w) Y]
  simp only [map_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]

theorem capEig_of_coefSm (hL : Loc) (hC : CoefSm) (hK : PI.KFinSmooth) : PI.CapelliEig.CapEig := by
  intro k r ε lam Hs _ _ _ σ Wp Wq _ _ _ _ _ _ hlam hds f hf Y g hg
  obtain ⟨a, ha, b, hb, P, Q, hQ, -, hfab⟩ := hf
  obtain ⟨hau, hainv, -⟩ := unitary_Hecke_group k r a ha
  obtain ⟨hbu, hbinv, -⟩ := unitary_Hecke_group k r b hb
  have hM := Hecke_multiplication k r ε lam Hs σ hds

  have hrep : ∀ x, Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) x →
      f x = (P.comp (σ a⁻¹)).comp ((σ x).comp ((σ b⁻¹).comp Q)) := by
    intro x hx
    have hxm : x ∈ UH (Hpk k r) := hx
    have hax : a⁻¹ * x ∈ UH (Hpk k r) := (unitary_Hecke_group k r a⁻¹ hainv).2.2 x hxm
    have hexp : a * (a⁻¹ * x * b⁻¹) * b = x := by
      calc a * (a⁻¹ * x * b⁻¹) * b = (a * a⁻¹) * x * (b⁻¹ * b) := by
            simp only [Matrix.mul_assoc]
        _ = x := by
            rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hau),
              Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hbu),
              Matrix.one_mul, Matrix.mul_one]
    have h1 : f (a * (a⁻¹ * x * b⁻¹) * b) = P.comp ((σ (a⁻¹ * x * b⁻¹)).comp Q) := hfab _
    rw [hexp, hM _ hax _ hbinv, hM _ hainv _ hxm] at h1
    rw [h1]
    ext v
    simp only [ContinuousLinearMap.comp_apply]

  have hQ' : ∀ w, ((σ b⁻¹).comp Q) w ∈ smoothVecs (k := k) (r := r) σ := fun w =>
    smooth_right_action k r ε lam Hs σ hds (Q w) (hK k r ε lam Hs σ hlam hds (Q w) (hQ w)) b⁻¹ hbinv
  obtain ⟨P₀, ⟨⟨hunit, hcay⟩, -⟩, -⟩ := id hds
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm
  calc PI.CapelliEig.capC (k := k) (r := r) Y f g
      = PI.CapelliEig.capC (k := k) (r := r) Y
          (fun x => (P.comp (σ a⁻¹)).comp ((σ x).comp ((σ b⁻¹).comp Q))) g :=
        hL (2 * r + k + 1) ε (Wq →L[ℂ] Wp) (Formalism.QuantumDeterminants.Hpk k r) P₀ P₀⁻¹ f _
          (Y + (((2 * r + k : ℕ) : ℂ)) / 2) g (Matrix.nonsing_inv_mul _ hdet)
          (Matrix.mul_nonsing_inv _ hdet) hH hrep hg
    _ = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y •
          (P.comp (σ a⁻¹)).comp ((σ g).comp ((σ b⁻¹).comp Q)) :=
        hC k r ε lam Hs σ Wp Wq hlam hds (P.comp (σ a⁻¹)) ((σ b⁻¹).comp Q) hQ' Y g hg
    _ = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • f g := by rw [hrep g hg]

theorem capEig (hK : PI.KFinSmooth) (hD : PI.DSInfCharCap.DSInfCharCap) : PI.CapelliEig.CapEig := by
  have hCoef : CoefSm := coefSm_of GlobalTheory.T.capelli_transport_unitary_conj GlobalTheory.T.capelli_operator_on_unitary_coefficient_eq_derived hD
  exact capEig_of_coefSm GlobalTheory.T.capelli_operator_unitaryGroup_local hCoef hK

end GlobalTheory.CapelliEigenvalue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DataConditionsOfGlobalAndRealRowsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Diag.PG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dataConditions_of_global_and_real_rows : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (D : D7) (Cg C0 : ℝ), Glob0 D x eps CD Cg → Nodes D x eps → ArithmeticConditionsOfDatum D → DuWin D C0 → StandingNumericalData D C0 := by
  first | exact @GlobalTheory.Diag.PG.data_of_rows | exact GlobalTheory.Diag.PG.data_of_rows | (intros; apply GlobalTheory.Diag.PG.data_of_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSignatureBlocksOfVectorAndFrameStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signature_blocks_of_vector_and_frame : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n), Sorts ε f → Sorts ε' f' → ∃ e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q), SignCompat e ∧ sg (e none) = GlobalTheory.GaussMean.sgn ℝ s := by
  first | exact @GlobalTheory.SignCount.exists_signCompat | exact GlobalTheory.SignCount.exists_signCompat | (intros; apply GlobalTheory.SignCount.exists_signCompat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentHaarMeasureRatio
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem exists_isRatioN : ∀ (k r : ℕ), ∃ cN : ℝ, IsRatioN k r cN := by
  intro k r
  have h1 : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) 1) :=
    GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r 1 one_pos ENNReal.one_lt_top
  have h2 : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (D.muN k r) :=
    ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r (D.muN k r)).2.1).2 (P.nilpotent_measure_is_haar k r)
  obtain ⟨c, c0, c1, e⟩ := GlobalTheory.BesselPeriodCompare.haar_unique (P.unipotent_radical_closed k r) h1 h2
  exact ⟨c.toReal, ENNReal.toReal_pos c0 c1, by rw [ENNReal.ofReal_toReal c1]; exact e⟩

end GlobalTheory.ThA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpInjectiveStrictUpperTriangular
section
open Matrix Filter Topology

namespace GlobalTheory.ExpStrictUpper

theorem conj_diagonal_eq {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i j, j ≤ i → X i j = 0)
    {τ : ℂ} (hτ : τ ≠ 0) :
    (Matrix.diagonal fun i : Fin m => (τ ^ (i : ℕ))⁻¹) * X *
      (Matrix.diagonal fun i : Fin m => τ ^ (i : ℕ)) =
      Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases h : j ≤ i
  · simp [hX i j h]
  · have hij : (i : ℕ) ≤ (j : ℕ) := by
      have := Fin.lt_def.mp (not_le.mp h)
      omega
    have hp : τ ^ (j : ℕ) = τ ^ (i : ℕ) * τ ^ ((j : ℕ) - (i : ℕ)) := by
      rw [← pow_add, Nat.add_sub_cancel' hij]
    rw [hp]
    calc (τ ^ (i : ℕ))⁻¹ * X i j * (τ ^ (i : ℕ) * τ ^ ((j : ℕ) - (i : ℕ)))
        = ((τ ^ (i : ℕ))⁻¹ * τ ^ (i : ℕ)) * (τ ^ ((j : ℕ) - (i : ℕ)) * X i j) := by ring
      _ = τ ^ ((j : ℕ) - (i : ℕ)) * X i j := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ hτ), one_mul]

theorem tendsto_scale {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i j, j ≤ i → X i j = 0) :
    Tendsto (fun τ : ℂ => (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j))
      (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun τ : ℂ => (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j)) :=
    continuous_matrix fun i j => by
      simp only [Matrix.of_apply]
      exact (continuous_pow _).mul continuous_const
  have h0 : (Matrix.of fun i j : Fin m => (0 : ℂ) ^ ((j : ℕ) - (i : ℕ)) * X i j) = 0 := by
    ext i j
    rw [Matrix.of_apply, Matrix.zero_apply]
    by_cases h : j ≤ i
    · rw [hX i j h, mul_zero]
    · have hn : (j : ℕ) - (i : ℕ) ≠ 0 := by
        have := Fin.lt_def.mp (not_le.mp h)
        omega
      rw [zero_pow hn, zero_mul]
  simpa only [h0] using hc.tendsto 0

theorem exp_inj_strictUpper : ∀ (m : ℕ) (X Y : Matrix (Fin m) (Fin m) ℂ),
    (∀ i j, j ≤ i → X i j = 0) → (∀ i j, j ≤ i → Y i j = 0) →
    NormedSpace.exp X = NormedSpace.exp Y → X = Y := by
  intro m X Y hX hY hXY
  obtain ⟨S, hS, hinj⟩ := (GlobalTheory.ExpBallNhds.exp_local_matrix (Fin m)).1
  have h1 : ∀ᶠ τ in 𝓝[≠] (0 : ℂ),
      (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j) ∈ S ∧
        (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * Y i j) ∈ S :=
    nhdsWithin_le_nhds (((tendsto_scale X hX).eventually_mem hS).and
      ((tendsto_scale Y hY).eventually_mem hS))
  have h2 : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), τ ≠ 0 := self_mem_nhdsWithin
  have hev := h1.and h2
  obtain ⟨τ, ⟨hxS, hyS⟩, hτ⟩ := hev.exists
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i : Fin m => τ ^ (i : ℕ) with hD
  set E : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i : Fin m => (τ ^ (i : ℕ))⁻¹ with hE
  have hDE : D * E = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (pow_ne_zero _ hτ)
  have hED : E * D = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (pow_ne_zero _ hτ)
  have hU : IsUnit D := ⟨⟨D, E, hDE, hED⟩, rfl⟩
  have hinv : D⁻¹ = E := Matrix.inv_eq_left_inv hED
  have hexp : ∀ Z : Matrix (Fin m) (Fin m) ℂ,
      NormedSpace.exp (E * Z * D) = E * NormedSpace.exp Z * D := by
    intro Z
    rw [← hinv]
    exact Matrix.exp_conj' D Z hU
  have hxS' : E * X * D ∈ S := by
    rw [hE, hD, conj_diagonal_eq X hX hτ]
    exact hxS
  have hyS' : E * Y * D ∈ S := by
    rw [hE, hD, conj_diagonal_eq Y hY hτ]
    exact hyS
  have key : E * X * D = E * Y * D :=
    hinj hxS' hyS' (by rw [hexp, hexp, hXY])
  calc X = (D * E) * X * (D * E) := by rw [hDE, one_mul, mul_one]
    _ = D * (E * X * D) * E := by simp only [mul_assoc]
    _ = D * (E * Y * D) * E := by rw [key]
    _ = (D * E) * Y * (D * E) := by simp only [mul_assoc]
    _ = Y := by rw [hDE, one_mul, mul_one]

end GlobalTheory.ExpStrictUpper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodModKLocalGen
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

open ValuativeRel Formalism.MainNotions.S.Loc IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DiffModProd

theorem different_ne_zero (F : Type) [Field F] [NumberField F] : differentIdeal ℤ (𝓞 F) ≠ 0 := by
  intro h
  have := absNorm_differentIdeal F (𝓞 F)
  rw [h, map_zero] at this
  exact discr_ne_zero F (Int.natAbs_eq_zero.1 this.symm)

theorem card_infinitePlace (D : D7) : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
  rw [← D.what₂.card_Tau]
  exact (Fintype.card_of_bijective
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))).symm

theorem rdE_pow (D : D7) :
    D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)) = |(NumberField.discr D.host.F : ℝ)| ^ 2 := by
  obtain ⟨h1, -⟩ := GlobalTheory.cm_discr_sq D.host.F D.host.E D.sp.cm
  have hpos : Module.finrank ℚ D.host.E ≠ 0 := Module.finrank_pos.ne'
  rw [card_infinitePlace, ← GlobalTheory.RealPlaces.finrank_E D]
  unfold Host.rdE
  rw [one_div, Real.rpow_inv_natCast_pow (abs_nonneg _) hpos]
  have h3 : |(discr D.host.E : ℝ)| = (discr D.host.F : ℝ) ^ 2 := by exact_mod_cast h1
  rw [h3, sq_abs]

theorem finprod_modK_localGen : ∀ (D : D7) (Z : LocDat D),
    (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))).Finite ∧
    ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (Z.δ p)) =
      (D.host.rdE ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹ := by
  intro D Z
  let A : GlobalTheory.HL.Places D.host.F D.host.E D.conjF :=
    { quad := D.sp.cm.deg2, loc := D.s.atP, L := fun p => (Z.M p).L, L_cj := fun p => Z.hcj p }
  have hex : ∀ p : PlF D, ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := fun p => by
    haveI := (D.s.atP p).lf
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ using hex
  have hδ : ∀ p, Z.δ p ≠ 0 := fun p => (Z.agree p).2.1
  have hI := different_ne_zero D.host.F
  set g : PlF D → ℝ := fun p =>
    (GlobalTheory.HL.resQ (ϖ p) : ℝ) ^ GlobalTheory.HL.vE (Z.M p).L (ϖ p) (algebraMap _ _ (Z.δ p)) with hg
  have hmod : ∀ p, (Z.M p).modK (algebraMap _ _ (Z.δ p)) = (g p ^ 2)⁻¹ := by
    intro p
    rw [(GlobalTheory.BaseModule.modK_algebraMap (Z.M p) (Z.agree p).1 (ϖ p) (hϖ p)).2 _ (hδ p), hg]
    dsimp only
    rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
    congr 1
    push_cast
    ring
  have hcount : ∀ p, GlobalTheory.HL.vE (Z.M p).L (ϖ p) (algebraMap _ _ (Z.δ p)) =
      ((Associates.mk p.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 D.host.F))).factors : ℕ) :=
    fun p => GlobalTheory.IdealResProd.vE_eq_count (D.s.atP p) (Z.M p).L (hϖ p) _ hI (hδ p) (GlobalTheory.T.span_different_eq_localGenerator D Z p)
  have hfin : (Function.mulSupport g).Finite := by
    refine (Ideal.finite_factors hI).subset fun p hp => ?_
    simp only [Set.mem_setOf_eq]
    by_contra h
    apply hp
    have h0 : (Associates.mk p.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 D.host.F))).factors = 0 := by
      by_contra hne
      exact h ((Associates.count_ne_zero_iff_dvd hI p.irreducible).1 hne)
    simp [g, hcount p, h0]
  have hprod : ∏ᶠ p, g p = |(NumberField.discr D.host.F : ℝ)| :=
    (GlobalTheory.IdealResProd.discr_and_level A ϖ hϖ).1 (fun p => Units.mk0 (Z.δ p) (hδ p))
      (fun p => GlobalTheory.T.span_different_eq_localGenerator D Z p)
  have hsupp : (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (Z.δ p))) ⊆
      Function.mulSupport g := fun p hp h => hp (by show (Z.M p).modK _ = 1; rw [hmod, h]; simp)
  refine ⟨hfin.subset hsupp, ?_⟩
  rw [finprod_congr hmod, finprod_inv_distrib, ← finprod_pow hfin, hprod, rdE_pow]

end GlobalTheory.DiffModProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlNormOneAdelicQuotientVolumeSiegelStepStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glNormOneAdelicQuotientVolume_siegel_step : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 2 ≤ j → glVol E (j - 1) < ⊤ → glVol E j = glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j) := by
  first | exact @GlobalTheory.FlagBase.SiegelStep.glVol_step | exact GlobalTheory.FlagBase.SiegelStep.glVol_step | (intros; apply GlobalTheory.FlagBase.SiegelStep.glVol_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalLevelUnitriangularIffStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_local_level_unitriangular_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (fr : GL (Fin n) (v.adicCompletion F)), (∀ j, c j ∈ loc v L) → (∀ j a, (sp (c j a)).2 = 0) → (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1) → (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ a, (sp (y a)).1 = x a) ↔ ∀ a, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x a ∈ v.adicCompletionIntegers F) → ∀ (t : ℕ), ∀ y ∈ levelVL cm.sig J v L, (∀ a b, ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b ∈ v.adicCompletionIntegers F) ∧ ((∀ i : Fin n, InModL (loc v L) g (c '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ c i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  first | exact @GlobalTheory.St.G.FirstColumn.unitriangular_iff | exact GlobalTheory.St.G.FirstColumn.unitriangular_iff | (intros; apply GlobalTheory.St.G.FirstColumn.unitriangular_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserCovolumeLeStatement
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_stabiliser_covolume_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (N : NF H r) (k : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (β : Fin r → ℕ) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (z z' : ι → Fin (2 * r + k + 1) → ℂ) (g : ι → Mat k r), IsPlaces σ → Module.finrank K V = 2 * r + k + 1 → (∀ v, IsFrameOf N k (σ v) (2 * Formalism.HermitianLatticesTheory.vInv K) β (Φ v) (z v) (z' v) (g v)) → (Ideal.absNorm N.𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∀ (gg : ℕ) (Λ : Submodule (𝓞 K) V) (Kf : Set (ι → Mt k r)), 1 ≤ gg → N.IsTerm gg Λ → IsFund (realPts Φ (N.Gam Λ : Set (V ≃ₗ[K] V))) (RP k r g) Kf → Measure.pi (fun _ : ι => lebR0 k r N.j β) Kf ≤ ENNReal.ofReal (N.om Λ * (Formalism.HermitianLatticesTheory.vInv K ^ (k * (r - N.j) * Fintype.card ι) * (8 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * (r + 1) ^ 2 * Fintype.card ι))) := by
  first | exact @GlobalTheory.DegVol.Cov.cov_le | exact GlobalTheory.DegVol.Cov.cov_le | (intros; apply GlobalTheory.DegVol.Cov.cov_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsDistSectionMulBlockStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ptSq_add_hsDist_comparable_hsDist_mul : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q), IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ (y : Sp P Q) (a : UpqT P Q), ptSq e y < δ → act a (baseVec e) = y → (∀ b, ‖UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) → (∀ i b, ‖(UpqT.mat a - 1) (e (some i)) (e (some b))‖ = ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) → ∀ g : UpqT P' Q', ptSq e y + hsDist g ≤ t * hsDist (a * j g) ∧ hsDist (a * j g) ≤ t * (ptSq e y + hsDist g) := by
  first | exact @GlobalTheory.SectionHsCompare.hsDist_section_mul_block | exact GlobalTheory.SectionHsCompare.hsDist_section_mul_block | (intros; apply GlobalTheory.SectionHsCompare.hsDist_section_mul_block <;> assumption)
end

