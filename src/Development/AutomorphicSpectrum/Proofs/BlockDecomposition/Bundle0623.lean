import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0590
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
import GroundTheory.GlobalFields.TateThesis.Bundle0002
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumByFirstVector
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem hE_cons (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a b c d : E)
    (x y : Fin M → E) :
    hE σ (hypOne J) (Fin.cons a (Fin.cons b x) : Fin (M + 2) → E)
        (Fin.cons c (Fin.cons d y) : Fin (M + 2) → E) = σ a * d + σ b * c + hE σ J x y := by
  simp only [hE, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  have e00 : hypOne J 0 0 = 0 := rfl
  have e01 : hypOne J 0 (Fin.succ 0) = 1 := rfl
  have e10 : hypOne J (Fin.succ 0) 0 = 1 := rfl
  have e11 : hypOne J (Fin.succ 0) (Fin.succ 0) = 0 := rfl
  have e0r : ∀ j : Fin M, hypOne J 0 j.succ.succ = 0 := fun _ => rfl
  have e1r : ∀ j : Fin M, hypOne J (Fin.succ 0) j.succ.succ = 0 := fun _ => rfl
  have er0 : ∀ i : Fin M, hypOne J i.succ.succ 0 = 0 := fun _ => rfl
  have er1 : ∀ i : Fin M, hypOne J i.succ.succ (Fin.succ 0) = 0 := fun _ => rfl
  have err : ∀ i j : Fin M, hypOne J i.succ.succ j.succ.succ = J i j := fun _ _ => rfl
  simp only [e00, e01, e10, e11, e0r, e1r, er0, er1, err]
  simp
  ring

theorem e0_cons (M : ℕ) : e0 E M 0 = Fin.cons 1 (Fin.cons 0 (fun _ => 0)) := by
  funext i
  refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i

theorem consA_zero {M n : ℕ} (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) :
    consA a Y 0 = Fin.cons 1 (Fin.cons 0 (fun _ => 0)) := by
  rw [← e0_cons]; rfl

theorem consA_succ {M n : ℕ} (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) (j : Fin n) :
    consA a Y j.succ = Fin.cons (a 0 j) (Fin.cons 0 (Y j)) := rfl

theorem consA_mem (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a : Fin 1 → Fin n → E) (Y : Fin n → Fin M → E) (hY : Y ∈ framesE σ J (0 : Matrix (Fin n) (Fin n) E)) :
    consA a Y ∈ framesOne σ J n := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hg : ∀ i j, hE σ J (Y i) (Y j) = 0 := fun i j => congrFun (congrFun hY.2 i) j
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    rw [Fin.sum_univ_succ] at hc
    have htail : ∀ k : Fin n, c k.succ = 0 := by
      refine Fintype.linearIndependent_iff.1 hY.1 (fun k => c k.succ) ?_
      funext i
      have := congrFun hc i.succ.succ
      simpa [Finset.sum_apply, consA_zero, consA_succ] using this
    have h0 : c 0 = 0 := by
      have := congrFun hc 0
      simpa [Finset.sum_apply, consA_zero, consA_succ, htail] using this
    intro k
    exact Fin.cases h0 htail k
  · ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [gramE, consA_zero, hE_cons, hz, BlockAlg.hE_zero_left]
    · simp [gramE, consA_zero, consA_succ, hE_cons, hz, BlockAlg.hE_zero_left]
    · simp [gramE, consA_zero, consA_succ, hE_cons, hz, BlockAlg.hE_zero_right]
    · simp [gramE, consA_succ, hE_cons, hg]
  · rfl

theorem sec_zero (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin (n + 1) → Fin (M + 2) → E) (hX : X ∈ framesOne σ J n) (a : Fin n) :
    X a.succ (Fin.succ 0) = 0 := by
  have hz : (fun _ : Fin M => (0 : E)) = 0 := rfl
  have hc : X a.succ = Fin.cons (X a.succ 0) (Fin.cons (X a.succ (Fin.succ 0)) (fun i => X a.succ i.succ.succ)) := by
    funext i
    refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i
  have h : hE σ (hypOne J) (X 0) (X a.succ) = 0 := congrFun (congrFun hX.1.2 0) a.succ
  rw [hX.2, e0_cons, hc, hE_cons, hz, BlockAlg.hE_zero_left] at h
  simpa using h

theorem tail_mem (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin (n + 1) → Fin (M + 2) → E) (hX : X ∈ framesOne σ J n) :
    (fun (a : Fin n) (i : Fin M) => X a.succ i.succ.succ) ∈ framesE σ J (0 : Matrix (Fin n) (Fin n) E) := by
  have hgr : ∀ a b, hE σ (hypOne J) (X a) (X b) = 0 := fun a b =>
    congrFun (congrFun hX.1.2 a) b
  have hc : ∀ a, X a = Fin.cons (X a 0) (Fin.cons (X a (Fin.succ 0)) (fun i => X a i.succ.succ)) :=
    fun a => by
      funext i
      refine Fin.cases rfl (fun i => Fin.cases rfl (fun k => rfl) i) i
  have hsec := sec_zero σ J X hX
  have h0 := hX.2.trans (e0_cons M)
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun c hc' a => ?_
    have h1 := Fintype.linearIndependent_iff.1 hX.1.1
      (Fin.cons (-∑ k, c k * X k.succ 0) c) (by
      rw [Fin.sum_univ_succ, h0]
      funext i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
      · simp [Finset.sum_apply]
      · have hsec' : ∀ a : Fin n, X a.succ 1 = 0 := hsec
        simp [Finset.sum_apply, hsec']
      · have := congrFun hc' k
        simpa [Finset.sum_apply] using this) a.succ
    simpa using h1
  · ext a b
    have h := hgr a.succ b.succ
    rw [hc a.succ, hc b.succ, hE_cons, hsec, hsec] at h
    simpa [gramE] using h

def framesOneEquiv (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (n : ℕ) :
    framesE σ J (0 : Matrix (Fin n) (Fin n) E) × (Fin 1 → Fin n → E) ≃ framesOne σ J n where
  toFun p := ⟨consA p.2 p.1.1, consA_mem σ J p.2 p.1.1 p.1.2⟩
  invFun X := (⟨fun a i => X.1 a.succ i.succ.succ, tail_mem σ J X.1 X.2⟩, fun _ a => X.1 a.succ 0)
  left_inv p := by
    obtain ⟨⟨Y, hY⟩, a⟩ := p
    refine Prod.ext (Subtype.ext ?_) ?_
    · rfl
    · funext i j
      have : i = 0 := Subsingleton.elim _ _
      subst this
      rfl
  right_inv X := by
    obtain ⟨X, hX⟩ := X
    refine Subtype.ext ?_
    funext k
    refine Fin.cases ?_ (fun k => ?_) k
    · exact hX.2.symm
    · funext i
      refine Fin.cases rfl (fun i => Fin.cases ?_ (fun l => rfl) i) i
      exact (sec_zero σ J X hX k).symm

theorem tsum_framesOne : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞), ∑' X : framesOne σ J n, f X.1 = ∑' Y : framesE σ J (0 : Matrix (Fin n) (Fin n) E), ∑' a : Fin 1 → Fin n → E, f (consA a Y.1) := by
  intro F E _ _ _ σ M J n f
  rw [← (framesOneEquiv σ J n).tsum_eq (fun X : framesOne σ J n => f X.1), ENNReal.tsum_prod']
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.FrOne
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FramesSumInvariantUnderStabiliser
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf

theorem linearIndependent_mulVec_unit {E : Type} [Field E] {M n : ℕ} (A : GL (Fin M) E)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (fun a => (A : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) := by
    intro x y hxy
    have h : ∀ z : Fin M → E,
        ((A⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ ((A : Matrix (Fin M) (Fin M) E) *ᵥ z) = z := by
      intro z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul]
      simp
    have hxy' : (A : Matrix (Fin M) (Fin M) E) *ᵥ x = (A : Matrix (Fin M) (Fin M) E) *ᵥ y := hxy
    rw [← h x, ← h y, hxy']
  exact hX.map' (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) (LinearMap.ker_eq_bot.2 hinj)

theorem linearIndependent_gact_unitary {F E : Type} [Field F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (g : UJ (σ : E →+* E) J) {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (gact σ g X) :=
  linearIndependent_mulVec_unit (g : GL (Fin M) E) hX

theorem gact_inv_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) : gact σ w⁻¹ (e0 E M) = e0 E M := by
  conv_lhs => rw [← hw]
  exact gact_inv_gact σ w _

theorem gact_zero_of_first {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (w : UJ (σ : E →+* E) (hypOne J))
    {X : Fin (n + 1) → Fin (M + 2) → E} (hX : X 0 = e0 E M 0) :
    gact σ w X 0 = gact σ w (e0 E M) 0 := by
  change ((w : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ X 0 =
    ((w : GL (Fin (M + 2)) E) : Matrix (Fin (M + 2)) (Fin (M + 2)) E) *ᵥ e0 E M 0
  rw [hX]

theorem gact_mem_framesOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) {X : Fin (n + 1) → Fin (M + 2) → E}
    (hX : X ∈ framesOne σ J n) : gact σ w X ∈ framesOne σ J n := by
  refine ⟨⟨linearIndependent_gact_unitary σ w hX.1.1, ?_⟩, ?_⟩
  · rw [gramE_gact]; exact hX.1.2
  · rw [gact_zero_of_first σ w hX.2, hw]

def framesOneEquiv {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (n : ℕ) {w : UJ (σ : E →+* E) (hypOne J)}
    (hw : gact σ w (e0 E M) = e0 E M) : framesOne σ J n ≃ framesOne σ J n where
  toFun X := ⟨gact σ w X.1, gact_mem_framesOne σ hw X.2⟩
  invFun X := ⟨gact σ w⁻¹ X.1, gact_mem_framesOne σ (gact_inv_e0 σ hw) X.2⟩
  left_inv X := Subtype.ext (gact_inv_gact σ w X.1)
  right_inv X := Subtype.ext (gact_gact_inv σ w X.1)

theorem tsum_gact_framesOne (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (w : UJ (σ : E →+* E) (hypOne J))
    (hw : gact σ w (e0 E M) = e0 E M) (f : (Fin (n + 1) → Fin (M + 2) → E) → ℝ≥0∞) :
    ∑' X : framesOne σ J n, f (gact σ w X.1) = ∑' X : framesOne σ J n, f X.1 :=
  (framesOneEquiv σ n hw).tsum_eq (fun X => f X.1)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescription
section
open NumberField MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain

open Ad3.R

theorem pri_eq_diagonal (α : ℚˣ) : pri α = diagonal ℚ α := rfl

theorem md_eq (a : Jd) : md a = (ideleModule ℚ a : ℝ) := rfl

theorem lintegral_posReal_weight_lt_top (τ : ℝ) (M : ℕ) (h0 : 0 < τ) (h1 : τ < M) :
    ∫⁻ t : {r : ℝ // 0 < r}, ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ) ∂posRealMeasure < ∞ := by
  have hF : Measurable (fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ)) := by
    fun_prop
  rw [posRealMeasure_eq_map_expPos, lintegral_map hF measurable_expPos]
  simp only [coe_expPos]
  rw [← lintegral_add_compl _ (measurableSet_Iic (a := (0 : ℝ))), Set.compl_Iic]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · refine (setLIntegral_mono (g := fun x => ENNReal.ofReal (Real.exp (τ * x))) (by fun_prop)
      fun x hx => ?_).trans_lt ?_
    · apply ENNReal.ofReal_le_ofReal
      have hm : min 1 (Real.exp x)⁻¹ ^ M ≤ 1 :=
        pow_le_one₀ (le_min zero_le_one (inv_nonneg.2 (Real.exp_pos x).le)) (min_le_left _ _)
      calc min 1 (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ ≤ 1 * Real.exp x ^ τ :=
            mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Real.exp_pos x).le _)
        _ = Real.exp (τ * x) := by rw [one_mul, mul_comm, Real.exp_mul]
    · exact Integrable.lintegral_lt_top (integrableOn_exp_mul_Iic h0 0)
  · refine (setLIntegral_mono (g := fun x => ENNReal.ofReal (Real.exp (-((M : ℝ) - τ) * x))) (by fun_prop)
      fun x hx => ?_).trans_lt ?_
    · apply ENNReal.ofReal_le_ofReal
      have hm : min 1 (Real.exp x)⁻¹ ^ M ≤ (Real.exp x)⁻¹ ^ M :=
        pow_le_pow_left₀ (le_min zero_le_one (inv_nonneg.2 (Real.exp_pos x).le)) (min_le_right _ _) M
      calc min 1 (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ ≤ (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ :=
            mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Real.exp_pos x).le _)
        _ = Real.exp (-((M : ℝ) - τ) * x) := by
          rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
          congr 1
          ring
    · exact Integrable.lintegral_lt_top (exp_neg_integrableOn_Ioi 0 (sub_pos.2 h1))

def fundD (w : InfinitePlace ℚ) : Set Jd :=
  (fun a => (normOneSplitting w a).1) ⁻¹' normOneFundamentalDomain ℚ

theorem measurableSet_fundD (w : InfinitePlace ℚ) : MeasurableSet (fundD w) := by
  exact (measurableSet_normOneFundamentalDomain ℚ).preimage (measurePreserving_normOneSplitting w).measurable.fst

theorem split_pri_mul (w : InfinitePlace ℚ) (α : ℚˣ) (a : Jd) :
    (normOneSplitting w (pri α * a)).1 = (normOneSplitting w a).1 * diagonalToNormOne ℚ α := by
  have hp : pri α = (normOneSplitting w).symm (diagonalToNormOne ℚ α, 1) := by
    simp only [normOneSplitting_symm_apply, map_one, mul_one, coe_diagonalToNormOne, pri_eq_diagonal]
  have key : normOneSplitting w (pri α) = (diagonalToNormOne ℚ α, 1) := by
    rw [hp]
    exact (normOneSplitting w).apply_symm_apply _
  rw [map_mul, Prod.fst_mul, key]
  exact mul_comm _ _

theorem existsUnique_pri_mul_mem (w : InfinitePlace ℚ) (a : Jd) :
    ∃! α : ℚˣ, pri α * a ∈ fundD w := by
  have h : ∀ α : ℚˣ, pri α * a ∈ fundD w ↔
      (normOneSplitting w a).1 * diagonalToNormOne ℚ α ∈ normOneFundamentalDomain ℚ := by
    intro α
    show (normOneSplitting w (pri α * a)).1 ∈ normOneFundamentalDomain ℚ ↔ _
    rw [split_pri_mul]
  exact (existsUnique_congr h).2 (existsUnique_mul_mem_normOneFundamentalDomain ℚ _)

theorem lintegral_fundD_lt_top (w : InfinitePlace ℚ) (τ : ℝ) (M : ℕ) (h0 : 0 < τ) (h1 : τ < M) :
    ∫⁻ a in fundD w, ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ) ∂ideleMeasure ℚ < ∞ := by
  have hφm : Measurable (fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ)) := by
    fun_prop
  have hIm : Measurable ((normOneFundamentalDomain ℚ).indicator (1 : normOneSubgroup ℚ → ℝ≥0∞)) :=
    measurable_one.indicator (measurableSet_normOneFundamentalDomain ℚ)
  have hpt : ∀ a : Jd, (fundD w).indicator (fun a => ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ)) a =
      (fun p : normOneSubgroup ℚ × {r : ℝ // 0 < r} => (normOneFundamentalDomain ℚ).indicator 1 p.1 *
        ENNReal.ofReal (min 1 (p.2 : ℝ)⁻¹ ^ M * (p.2 : ℝ) ^ τ)) (normOneSplitting w a) := by
    intro a
    by_cases ha : a ∈ fundD w
    · have ha' : (normOneSplitting w a).1 ∈ normOneFundamentalDomain ℚ := ha
      simp [Set.indicator_of_mem ha, Set.indicator_of_mem ha', normOneSplitting_apply_snd, md_eq]
    · have ha' : (normOneSplitting w a).1 ∉ normOneFundamentalDomain ℚ := ha
      simp [ha, ha']
  rw [← lintegral_indicator (measurableSet_fundD w), lintegral_congr hpt,
    (measurePreserving_normOneSplitting w).lintegral_comp
      (f := fun p : normOneSubgroup ℚ × {r : ℝ // 0 < r} => (normOneFundamentalDomain ℚ).indicator 1 p.1 *
        ENNReal.ofReal (min 1 (p.2 : ℝ)⁻¹ ^ M * (p.2 : ℝ) ^ τ))
      ((hIm.comp measurable_fst).mul (hφm.comp measurable_snd)),
    lintegral_prod_mul hIm.aemeasurable hφm.aemeasurable, lintegral_indicator_one (measurableSet_normOneFundamentalDomain ℚ)]
  exact ENNReal.mul_lt_top (normOneMeasure_normOneFundamentalDomain_lt_top ℚ)
    (lintegral_posReal_weight_lt_top τ M h0 h1)

theorem exists_idele_fundamentalDomain : Ad3.R.D0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  unfold Ad3.R.D0
  exact ⟨fundD w, measurableSet_fundD w, existsUnique_pri_mul_mem w,
    fun τ M h0 h1 => lintegral_fundD_lt_top w τ M h0 h1⟩

end GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianSchwartzBruhat
section
set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RankinSelberg

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Classical SchwartzMap

noncomputable section

theorem isEmpty_complexPlaces_rat : IsEmpty {w : InfinitePlace ℚ // IsComplex w} := by
  refine ⟨fun w => ?_⟩
  exact (not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2

theorem norm_sq_mixedToEuclidean_rat (x : mixedSpace ℚ) :
    ‖GroundTheory.Global.mixedToEuclidean ℚ x‖ ^ 2 = ∑ w, x.1 w ^ 2 := by
  haveI := isEmpty_complexPlaces_rat
  rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
  have h2 : ‖(GroundTheory.Global.mixedToEuclidean ℚ x).snd‖ = 0 := by
    rw [EuclideanSpace.norm_eq]
    simp
  rw [h2]
  have h1 : ∀ w, (GroundTheory.Global.mixedToEuclidean ℚ x).fst.ofLp w = x.1 w := fun _ => rfl
  simp only [h1, Real.norm_eq_abs, sq_abs]
  simp

theorem gaussian_exists : Ad3.R.GS := by
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (GroundTheory.Automorphic.Adele2.toEuclid2 ℚ)
    (GroundTheory.Global.gaussianSchwartz _), fun y => ?_⟩
  have h : ‖GroundTheory.Automorphic.Adele2.toEuclid2 ℚ y‖ ^ 2 = ∑ i, ∑ w, (y i).1 w ^ 2 := by
    rw [GroundTheory.Automorphic.Adele2.toEuclid2_apply, WithLp.prod_norm_sq_eq_of_L2, Fin.sum_univ_two]
    exact congrArg₂ (· + ·) (norm_sq_mixedToEuclidean_rat _) (norm_sq_mixedToEuclidean_rat _)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, h]

end

end GlobalTheory.CompanionTheory.RankinSelberg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericSubquotientIffWhittakerQuotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.PRep.WhitQuot

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem twKer_subQuot {ρ : Representation ℂ G V} (A B : Subrepresentation ρ) (U : Subgroup G) (χ : U →* ℂˣ) :
    twKer (subQuot A B) U χ =
      (twKer A.toRepresentation U χ).map (B.toSubmodule.comap A.toSubmodule.subtype).mkQ := by
  have key : ∀ (g : G) (v : A.toSubmodule),
      (subQuot A B) g ((B.toSubmodule.comap A.toSubmodule.subtype).mkQ v) =
        (B.toSubmodule.comap A.toSubmodule.subtype).mkQ (A.toRepresentation g v) := fun _ _ => rfl
  unfold twKer
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨n, w, rfl⟩
    obtain ⟨v, rfl⟩ := (B.toSubmodule.comap A.toSubmodule.subtype).mkQ_surjective w
    have h : (subQuot A B) n ((B.toSubmodule.comap A.toSubmodule.subtype).mkQ v) -
          ((χ n : ℂˣ) : ℂ) • (B.toSubmodule.comap A.toSubmodule.subtype).mkQ v =
        (B.toSubmodule.comap A.toSubmodule.subtype).mkQ
          (A.toRepresentation n v - ((χ n : ℂˣ) : ℂ) • v) := by
      rw [key, map_sub, map_smul]
    rw [h]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨n, v, rfl⟩)
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul, ← key]
    exact Submodule.subset_span ⟨n, _, rfl⟩

theorem coe_mem_twKer {ρ : Representation ℂ G V} (A : Subrepresentation ρ) (U : Subgroup G) (χ : U →* ℂˣ)
    {x : A.toSubmodule} (hx : x ∈ twKer A.toRepresentation U χ) : (x : V) ∈ twKer ρ U χ := by
  have h : twKer A.toRepresentation U χ ≤ (twKer ρ U χ).comap A.toSubmodule.subtype := by
    unfold twKer
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, v, rfl⟩
    exact Submodule.subset_span ⟨n, v, rfl⟩
  exact h hx

end General

theorem isGenericFor_subQuot_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → ∀ A B : Subrepresentation ρ, B ≤ A → (IsGenericFor ψ (subQuot A B) ↔ ¬ A.toSubmodule ≤ B.toSubmodule ⊔ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ A B hBA
  have hsm : IsSmooth A.toRepresentation := by
    intro v
    have h : {g : GL (Fin N) k | A.toRepresentation g v = v} = {g | ρ g (v : V) = v} :=
      Set.ext fun g => Subtype.ext_iff
    rw [h]
    exact hρ v
  show Nontrivial (_ ⧸ twKer (subQuot A B) (unipB k (Fin N)) (whitChar ψ N)) ↔ _
  rw [Submodule.Quotient.nontrivial_iff, twKer_subQuot, Ne, Submodule.map_mkQ_eq_top]
  refine not_congr ⟨fun h => ?_, fun h => ?_⟩
  · intro v hv
    have hmem : (⟨v, hv⟩ : A.toSubmodule) ∈ B.toSubmodule.comap A.toSubmodule.subtype ⊔
        twKer A.toRepresentation (unipB k (Fin N)) (whitChar ψ N) := by
      rw [h]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hmem
    have hv' : v = (y : V) + (z : V) := by rw [← Submodule.coe_add, hyz]
    rw [hv']
    exact Submodule.add_mem_sup hy (coe_mem_twKer A _ _ hz)
  · rw [eq_top_iff]
    rintro a -
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h a.2)
    have hyA : y ∈ A.toSubmodule := hBA hy
    have hzA : z ∈ A.toSubmodule := by
      have hz2 : z = (a : V) - y := by rw [← hyz]; abel
      rw [hz2]
      exact A.toSubmodule.sub_mem a.2 hyA
    have hz' : (⟨z, hzA⟩ : A.toSubmodule) ∈ twKer A.toRepresentation (unipB k (Fin N)) (whitChar ψ N) :=
      GlobalTheory.CompanionTheory.PRep.WhitExact.twKer_whitChar_reflect k ψ hψ N A.toRepresentation ρ hsm hρ
        A.toSubmodule.subtype A.toSubmodule.injective_subtype (fun _ _ => rfl) _ hz
    have ha : a = ⟨y, hyA⟩ + ⟨z, hzA⟩ := Subtype.ext hyz.symm
    rw [ha]
    exact Submodule.add_mem_sup hy hz'

end GlobalTheory.CompanionTheory.PRep.WhitQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodSetCompactLinearlyIndependentStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_set_compact_linearly_independent : ∀ (K W : Type) [CommRing K] [TopologicalSpace K] [Fintype W] (κ : K ≃+* (W → ℂ)), IsHomeomorph κ → ∀ n M : ℕ, (∀ r : Fin n → W → ℝ, IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) ∧ IsOpen {X : Fin n → Fin M → K | LinearIndependent K X} ∧ ∀ R ε : ℝ, 0 < ε → IsCompact (GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε) ∧ GlobalTheory.CompanionTheory.WhitFree.AvgInf.goodK (n := n) (M := M) κ R ε ⊆ {X : Fin n → Fin M → K | LinearIndependent K X} := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Topo.boxK_goodK_topology <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplex
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.GAUnimod

theorem isMulRightInvariant_haar_GA : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant :=
  fun E _ _ _ N _ _ μ _ => GlobalTheory.CompanionTheory.PairDom.isMulRightInvariant_GA E N μ

end GlobalTheory.CompanionTheory.GAUnimod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianFormPolynomialInStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_form_polynomial_in : ∀ (K : Type) [Field K] (σ : K →+* K) (n : ℕ) (A H₀ H : Matrix (Fin n) (Fin n) K), IsUnit A.det → A.charpoly.Separable → H₀.det ≠ 0 → cT σ A * H₀ * A = H₀ → cT σ A * H * A = H → ∃ m : K[X], H = H₀ * aeval A m := by
  first | exact @GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval | exact GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval | (intros; apply GlobalTheory.CompanionTheory.FormRatio.exists_eq_mul_aeval <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ISupFiniteProductTailLimitStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iSup_finite_product_tail_limit : ∀ (ι : Type) [DecidableEq ι] (Mv τ p : ι → ℝ) (S : Finset ι), Summable (fun v => |Mv v - 1|) → Summable (fun v => |τ v - 1|) → Summable (fun v => |p v - 1|) → (∀ v, 0 ≤ Mv v) → (∀ v, 0 ≤ τ v) → (∀ v, 0 ≤ p v) → (∀ v, v ∉ S → τ v * p v ≤ Mv v) → ⨆ S' : Finset ι, ENNReal.ofReal ((∏ v ∈ (S ∪ S') \ S, Mv v) * ((∏' v : {v // v ∉ S ∪ S'}, τ v.1) * ∏' v : {v // v ∉ S ∪ S'}, p v.1)) = ENNReal.ofReal (∏' v : {v // v ∉ S}, Mv v.1) := by
  first | exact @GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails | exact GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails | (intros; apply GlobalTheory.CompanionTheory.TailProd.iSup_partial_mul_tails <;> assumption)
end

