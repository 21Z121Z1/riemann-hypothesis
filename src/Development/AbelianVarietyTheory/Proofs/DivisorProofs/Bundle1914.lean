import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0881
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1869
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeDualWeylFibreLatticeGe
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibSlope

section Log

variable {K : Type} [Field K] {φ : K → ℝ} (hφ : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
include hφ

theorem log_one : φ 1 = 0 := by
  have := hφ 1 1 one_ne_zero one_ne_zero
  rw [mul_one] at this
  linarith

theorem log_prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i, f i ≠ 0) :
    φ (∏ i ∈ s, f i) = ∑ i ∈ s, φ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using log_one hφ
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons, hφ _ _ (hf i) (Finset.prod_ne_zero_iff.2 fun j _ => hf j), ih]

theorem log_pow {x : K} (hx : x ≠ 0) (n : ℕ) : φ (x ^ n) = n * φ x := by
  have := log_prod hφ (Finset.range n) (fun _ => x) fun _ => hx
  simpa using this

theorem log_det_rhoMat [CharZero K] {n : ℕ} {la : Fin n → ℕ} (hla : Antitone la) {g : Matrix (Fin n) (Fin n) K}
    (hg : g.det ≠ 0) : (rhoMat la g).det ≠ 0 ∧
      φ (rhoMat la g).det = (dim la : ℝ) * ((size la : ℝ) / (n : ℝ) * φ g.det) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Subsingleton.elim g 1, GlobalTheory.DefPt.Model.rhoMat_one, Matrix.det_one, log_one hφ]
    simp
  · have h := det_rhoMat_pow K n la hla g
    have h0 : (rhoMat la g).det ≠ 0 := fun h0 => by
      rw [h0, zero_pow hn.ne'] at h
      exact pow_ne_zero _ hg h.symm
    refine ⟨h0, ?_⟩
    have h1 := congrArg φ h
    rw [log_pow hφ h0, log_pow hφ hg] at h1
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    push_cast at h1
    field_simp
    linarith

theorem log_det_kron {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (J t)] {c : K} (hc : c ≠ 0) (M : ∀ t, Matrix (J t) (J t) K) (hM : ∀ t, (M t).det ≠ 0)
    (r : T → ℝ) (hr : ∀ t, φ (M t).det = Fintype.card (J t) * r t) :
    (c • kron M).det ≠ 0 ∧ φ (c • kron M).det = Fintype.card (∀ t, J t) * (φ c + ∑ t, r t) := by
  have hk := (kronFamily_mul_one_det T J K M M).2.2
  have hp : ∀ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) ≠ 0 := fun t => pow_ne_zero _ (hM t)
  have h0 : (kron M).det ≠ 0 := hk ▸ Finset.prod_ne_zero_iff.2 fun t _ => hp t
  rw [Matrix.det_smul]
  refine ⟨mul_ne_zero (pow_ne_zero _ hc) h0, ?_⟩
  rw [hφ _ _ (pow_ne_zero _ hc) h0, log_pow hφ hc, hk, log_prod hφ _ _ hp, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [log_pow hφ (hM t), hr, ← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ t),
    Fintype.card_pi]

end Log

section Val

variable {K : Type} [Field K] [NumberField K]

theorem vAdd_mul_real (w : HeightOneSpectrum (𝓞 K)) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (vAdd w (x * y) : ℝ) = vAdd w x + vAdd w y := by
  have h1 : w.valuation K x ≠ 0 := by simpa using hx
  have h2 : w.valuation K y ≠ 0 := by simpa using hy
  rw [← Int.cast_add, vAdd, vAdd, vAdd, map_mul, WithZero.log_mul h1 h2, neg_add]

theorem valuation_det_le {ι : Type} [Fintype ι] [DecidableEq ι] (w : HeightOneSpectrum (𝓞 K)) {M : Matrix ι ι K}
    (hM : IntAt w M) : w.valuation K M.det ≤ 1 := by
  rw [Matrix.det_apply']
  refine Valuation.map_sum_le _ fun σ _ => ?_
  rw [map_mul, map_prod]
  refine mul_le_one' ?_ (Finset.prod_le_one' fun i _ => hM _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem finite_vAdd_det {ι : Type} [Fintype ι] [DecidableEq ι] {A : HeightOneSpectrum (𝓞 K) → Matrix ι ι K}
    (hA : IsAdelic A) : (Function.support fun w => (vAdd w (A w).det : ℝ)).Finite := by
  refine hA.2.subset fun w hw h => hw ?_
  have h1 := valuation_det_le w h.1
  have h2 := valuation_det_le w h.2
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', map_inv₀] at h2
  have h0 : w.valuation K (A w).det ≠ 0 := by simpa using hA.1 w
  have h3 : w.valuation K (A w).det = 1 :=
    le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 h2)
  simp [vAdd, h3]

end Val

theorem log_norm_mul (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) : Real.log ‖x * y‖ = Real.log ‖x‖ + Real.log ‖y‖ := by
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy)]

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {la : ∀ t, Fin (N t) → ℕ}

theorem vAdd_det_fibA {K : Type} [Field K] [NumberField K] (hla : ∀ t, Antitone (la t)) (w : HeightOneSpectrum (𝓞 K))
    {a : K} (ha : a ≠ 0) {B : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K} (hB : ∀ t, (B t).det ≠ 0) :
    (vAdd w (fibA la a B).det : ℝ) =
      Fintype.card (TIdx la) * (vAdd w a + ∑ t, (size (la t) : ℝ) / (N t : ℝ) * vAdd w (B t).det) :=
  (log_det_kron (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) ha _
    (fun t => (log_det_rhoMat (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) (hla t) (hB t)).1) _
    (fun t => by
      rw [← dim_eq_card]
      exact (log_det_rhoMat (φ := fun x => (vAdd w x : ℝ)) (vAdd_mul_real w) (hla t) (hB t)).2)).2

theorem log_det_fibY (hla : ∀ t, Antitone (la t)) {s : ℝ} (hs : 0 < s) {X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ}
    (hX : ∀ t, (X t).det ≠ 0) : (fibY la s X).det ≠ 0 ∧ Real.log ‖(fibY la s X).det‖ =
      Fintype.card (TIdx la) * (Real.log s + ∑ t, (Real.log ‖(onMat (la t)).det‖ / dim (la t) +
        (size (la t) : ℝ) / (N t : ℝ) * Real.log ‖(X t).det‖)) := by
  have hρ := fun t => log_det_rhoMat (φ := fun x : ℂ => Real.log ‖x‖) log_norm_mul (hla t) (hX t)
  have ho := fun t => (GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim _ (la t) (hla t)).1
  have h := log_det_kron (φ := fun x : ℂ => Real.log ‖x‖) log_norm_mul (c := (s : ℂ))
    (Complex.ofReal_ne_zero.2 hs.ne') (fun t => onMat (la t) * rhoMat (la t) (X t))
    (fun t => by rw [Matrix.det_mul]; exact mul_ne_zero (ho t) (hρ t).1)
    (fun t => Real.log ‖(onMat (la t)).det‖ / dim (la t) + (size (la t) : ℝ) / (N t : ℝ) * Real.log ‖(X t).det‖)
    (fun t => by
      have hd : (dim (la t) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (dim_pos (hla t)).ne'
      have h2 := (hρ t).2
      rw [← dim_eq_card, Matrix.det_mul, log_norm_mul _ _ (ho t) (hρ t).1, h2, mul_add, mul_div_cancel₀ _ hd])
  simp only [Complex.norm_real, Real.norm_of_nonneg hs.le] at h
  exact h

theorem log_det_onMat_le {n : ℕ} {la : Fin n → ℕ} (hla : Antitone la) :
    Real.log ‖(onMat la).det‖ / dim la ≤ Real.log (dim la) / 2 := by
  obtain ⟨h0, h⟩ := GlobalTheory.T.dualWeyl_gramDeterminant_le_dim_pow_dim _ la hla
  have hd : (0 : ℝ) < dim la := Nat.cast_pos.2 (dim_pos hla)
  have h1 := Real.log_le_log (pow_pos (norm_pos_iff.2 h0) 2) h
  rw [Real.log_pow, Real.log_pow] at h1
  rw [div_le_iff₀ hd]
  push_cast at h1
  linarith

theorem slope_fibre_ge : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ) (la : ∀ t, Fin (N t) → ℕ), (∀ t, Antitone (la t)) → ∀ (a : HeightOneSpectrum (𝓞 K) → K) (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) (s : (K →+* ℂ) → ℝ) (X : (K →+* ℂ) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ), (∀ w, a w ≠ 0) → (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) → (∀ σ, 0 < s σ) → (∀ σ t, (X σ t).det ≠ 0) → (∀ σ, s ((starRingEnd ℂ).comp σ) = s σ) → (∀ σ t, ‖(X ((starRingEnd ℂ).comp σ) t).det‖ = ‖(X σ t).det‖) → (∀ σ, (fibY la (s σ) (X σ)).det ≠ 0) ∧ lineDeg s (fun w => (vAdd w (a w) : ℝ)) + ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * detDeg (fun w => B w t) (fun σ => X σ t) - Real.log (dim (la t)) / 2) ≤ slope_sq (matNorm fun σ => fibY la (s σ) (X σ)) (locLat fun w => fibA la (a w) (B w)) / 2 := by
  intro K _ _ _ T _ _ N la hla a B s X ha hfa hB hs hX hsc hXc
  have hY := fun σ => log_det_fibY hla (hs σ) (hX σ)
  refine ⟨fun σ => (hY σ).1, ?_⟩
  have hD : 0 < Fintype.card (TIdx la) := by
    rw [Fintype.card_pi]
    exact Finset.prod_pos fun t _ => dim_eq_card (la t) ▸ dim_pos (hla t)
  haveI : Nonempty (TIdx la) := Fintype.card_pos_iff.1 hD
  have hD' : (Fintype.card (TIdx la) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hD.ne'
  have hK : (0 : ℝ) < finrank ℚ K := Nat.cast_pos.mpr finrank_pos
  rw [GlobalTheory.T.latticeSlopeSq_localMatrices_eq_determinants K (TIdx la) _ _ (GlobalTheory.FibAdel.fibA_isAdelic K T N la a B ha hfa hB) (fun σ => (hY σ).1)
    (fun σ => Real.log_injOn_pos (norm_pos_iff.2 (hY _).1) (norm_pos_iff.2 (hY _).1) (by
      rw [(hY _).2, (hY _).2]; simp only [hsc, hXc]))]
  have hfa' : (Function.support fun w => (vAdd w (a w) : ℝ)).Finite := hfa.subset fun w hw h => hw (by
    simp only at h ⊢; rw [h, Int.cast_zero])
  have hfB := fun t => finite_vAdd_det (hB t)
  have hfin : ∑ᶠ w, (vAdd w (fibA la (a w) (B w)).det : ℝ) * lw K w = Fintype.card (TIdx la) *
      (∑ᶠ w, (vAdd w (a w) : ℝ) * lw K w +
        ∑ t, (size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w) := by
    have hsub : ∀ t, (Function.support fun w => (size (la t) : ℝ) / (N t : ℝ) *
        ((vAdd w (B w t).det : ℝ) * lw K w)).Finite := fun t =>
      (fin_mul (hfB t) (lw K)).subset (Function.support_mul_subset_right _ _)
    simp only [mul_finsum]
    rw [← finsum_sum_comm _ _ (fun t _ => hsub t), ← finsum_add_distrib (fin_mul hfa' _), mul_finsum]
    · refine finsum_congr fun w => ?_
      rw [vAdd_det_fibA hla w (ha w) (fun t => (hB t).1 w), mul_assoc, add_mul, Finset.sum_mul]
      simp only [mul_assoc]
    · exact (Set.finite_iUnion hsub).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (Finset.sum_eq_zero fun t _ => hn t)
  have hinf : ∑ σ, Real.log ‖(fibY la (s σ) (X σ)).det‖ = Fintype.card (TIdx la) *
      (∑ σ, Real.log (s σ) + ∑ t, (finrank ℚ K * (Real.log ‖(onMat (la t)).det‖ / dim (la t)) +
        (size (la t) : ℝ) / (N t : ℝ) * ∑ σ, Real.log ‖(X σ t).det‖)) := by
    simp only [(hY _).2]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Embeddings.card, nsmul_eq_mul,
      Finset.mul_sum]
  simp only [detDeg, lineDeg]
  rw [hfin, hinf]
  have key : ∀ u v : ℝ, 2 * (Fintype.card (TIdx la) * u - Fintype.card (TIdx la) * v / finrank ℚ K) /
      (Fintype.card (TIdx la) : ℝ) / 2 = u - v / finrank ℚ K := fun u v => by field_simp
  rw [key, add_div, Finset.sum_div (ι := T)]
  have hle : ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * ((∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w) -
      (∑ σ, Real.log ‖(X σ t).det‖) / finrank ℚ K) - Real.log (dim (la t)) / 2) ≤
      ∑ t, ((size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w -
        (finrank ℚ K * (Real.log ‖(onMat (la t)).det‖ / dim (la t)) +
        (size (la t) : ℝ) / (N t : ℝ) * ∑ σ, Real.log ‖(X σ t).det‖) / finrank ℚ K) :=
    Finset.sum_le_sum fun t _ => by
      have := log_det_onMat_le (hla t)
      rw [add_div, mul_div_cancel_left₀ _ hK.ne', mul_sub, mul_div_assoc]
      linarith
  rw [Finset.sum_sub_distrib (f := fun t => (size (la t) : ℝ) / (N t : ℝ) * ∑ᶠ w, (vAdd w (B w t).det : ℝ) * lw K w)]
    at hle
  linarith

end GlobalTheory.FibSlope

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuConductorExponentsPosProdEqModulusStatement
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareNuConductorExponents_pos_prod_eq_modulus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ →
  ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ),
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, GlobalTheory.CMVal.ExpAt (GlobalTheory.FunObj.SqNum.nuH G t i j) w (c w)) →
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, 0 < c w) ∧ ∏ w ∈ GlobalTheory.FunObj.locPl G t, w.asIdeal ^ c w = GlobalTheory.SqTop.modT G t := by
  first | exact @GlobalTheory.NuExpModulus.main | exact GlobalTheory.NuExpModulus.main | (intros; apply GlobalTheory.NuExpModulus.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1 := by
  first | exact @GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one | exact GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one | (intros; apply GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberMovedDatumSplittingScaleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairFirstMember_movedDatum_splittingScale : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (h : GA D WW) (x y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) →
    IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg A) WW) (heisO W.ψ (GlobalTheory.Grid.neg A) WW) (Y.e t)
      (latO (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ fun _ => True) 1 Y.vac
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) (Y.e t) (Y.ideal (locPl G) t) A WW
        X.rA.β X.rW.β)
      (((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) •
        Y.ω t (g⁻¹, h⁻¹) (Y.f t)) := by
  first | exact @GlobalTheory.BotFrames.move_fst | exact GlobalTheory.BotFrames.move_fst | (intros; apply GlobalTheory.BotFrames.move_fst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

def tensForm {k κ κ' : Type} (l₁ : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (l₂ : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ) : ((κ ⊕ κ' → k) → ℂ) →ₗ[ℂ] ℂ where
  toFun f := l₁ fun x₁ => l₂ fun x₂ => f (Sum.elim x₁ x₂)
  map_add' f g := by
    rw [← map_add]; congr 1; funext x₁; rw [Pi.add_apply, ← map_add]; rfl
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; funext x₁; rw [Pi.smul_apply, ← map_smul]; rfl

theorem tensForm_box {k κ κ' : Type} (l₁ : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (l₂ : ((κ' → k) → ℂ) →ₗ[ℂ] ℂ)
    (φ₁ : (κ → k) → ℂ) (φ₂ : (κ' → k) → ℂ) : tensForm l₁ l₂ (boxFun φ₁ φ₂) = l₁ φ₁ * l₂ φ₂ := by
  have e : (fun x₁ => l₂ fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = l₂ φ₂ • φ₁ := by
    funext x₁
    have : (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₁ x₁ • φ₂ := by funext x₂; rfl
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  change l₁ _ = _
  rw [e, map_smul, smul_eq_mul, mul_comm]

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def repl (v : Pl F) (y : κ → AF F) (x : κ → Fv F v) : κ → AF F :=
  fun i => y i - liftV v (evFin F v (y i)) + liftV v (x i)

def proj (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) : Module.End ℂ ((κ → AF F) → ℂ) where
  toFun Φ y := φ₀ (fun i => evFin F v (y i)) * l fun x => Φ (repl v y x)
  map_add' Φ Ψ := by
    funext y
    rw [Pi.add_apply, ← mul_add, ← map_add]; rfl
  map_smul' c Φ := by
    funext y
    rw [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm, ← smul_eq_mul c, ← map_smul]; rfl

theorem proj_apply (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (Φ : (κ → AF F) → ℂ)
    (y : κ → AF F) : proj v φ₀ l Φ y = φ₀ (fun i => evFin F v (y i)) * l fun x => Φ (repl v y x) := rfl

theorem evFin_repl (v : Pl F) (y : κ → AF F) (x : κ → Fv F v) (i : κ) : evFin F v (repl v y x i) = x i := by
  simp [repl, evFin_liftV]

theorem proj_tens (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (φ : (κ → Fv F v) → ℂ)
    (r : (κ → AF F) → ℂ) (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) :
    proj v φ₀ l (tens (evFin F v) φ r) = l φ • tens (evFin F v) φ₀ r := by
  funext y
  have e : (fun x => tens (evFin F v) φ r (repl v y x)) = r y • φ := by
    funext x
    have h1 : repl v y x = y + fun i => liftV v (x i - evFin F v (y i)) := by
      funext i; simp only [repl, Pi.add_apply, map_sub]; ring
    have h2 : r (repl v y x) = r y := by
      rw [h1]; exact hr _ _ fun u hu => funext fun i => at_liftV v _ u hu
    simp only [tens, evFin_repl, h2, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [proj_apply, e, map_smul]
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.MixedForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestDataTraceIdentityStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_data_trace_identity : ∀ {D : D7} {V : HSp D}, GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → ∀ {lam : D.what₂.Tau → Fin V.rank → ℤ} {S : D.what₂.Tau → SPar} {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V} {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)} {μ : Measure (GA D V)} {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}, IsTestData V lam M T U μa μf μ fa ff → ∀ (Φ : WittFrame V) (K : Subgroup (GA D V)) (γ : GF V) (Tr : A0 (wittIndex V)) (x : GA D V), kT Φ K {δ | IsConj γ δ} (tensor D.sp.cm.sig V.gram fa ff) Tr x = classKernel (GQ V) (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x := by
  first | exact @GlobalTheory.KTClass.kT_eq_classKernel | exact GlobalTheory.KTClass.kT_eq_classKernel | (intros; apply GlobalTheory.KTClass.kT_eq_classKernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCombinationJetsAlgebraicConjEqConjSeriesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCombinationJets_algebraic_conj_eq_conjSeries : ∀ (D : D7), GlobalTheory.NormSum.Inp D → ∀ (δ t0 : ℂ), Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D D.host.ccK δ) t0 →
    ∀ (a b : ℕ), Even (a * b) → ∀ (e0 : VC D a b → ℂ), oddE0 D D.host.ccK δ t0 a b e0 →
    ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
    ∀ (κ : ℂ), Mod1All κ → ∀ (k n : ℕ), 0 < k → ∀ (r : Fin n → Qbar) (s : Fin n → VC D a b),
    (∀ i, k • s i ∈ La D (tor0 D D.host.ccK δ) Ls Lt) → ∀ (ρ' : Qbar →ₐ[ℚ] ℂ) (m : Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ),
      GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
              (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) ∈ Qbar ∧
      Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
                (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z)) =
        GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) (fnConj D Qbar ρ' fun z => κ * ∑ i, (r i : ℂ) * U D (tor0 D D.host.ccK δ) (s i)
          (Iop D (tor0 D D.host.ccK δ) (La0 D (tor0 D D.host.ccK δ) _ _) (La D (tor0 D D.host.ccK δ) Ls Lt) e0) z) := by
  first | exact @GlobalTheory.ConjJetComb.conj_jet | exact GlobalTheory.ConjJetComb.conj_jet | (intros; apply GlobalTheory.ConjJetComb.conj_jet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModerateGrowthHeight
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ThetaModGrowthPair

theorem theta_modGrowth : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hlat := GlobalTheory.T.adelicThetaSum_norm_le_polynomial_scale
  have hfin := GlobalTheory.T.weilRep_rational_support_common_denominator
  have harch := GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨N₀, k₂, C₂, hL⟩ := hlat F (Fin n × Fin d)
  obtain ⟨C₁, k₁, hA⟩ := harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ N₀
  obtain ⟨C₃, k₃, hF⟩ := hfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨|C₂| * |C₁| * |C₃| ^ k₂, k₁ + k₃ * k₂, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hsupp⟩ := hF g h
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hb := hL (C₁ * H ^ k₁) m (om (g, h) Φ) hm1 (fun ξ => hA g h _) hsupp
  have hA0 : 0 ≤ C₁ * H ^ k₁ :=
    le_trans (by positivity) (hA g h (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₂ := by positivity
  have hmk : (m : ℝ) ^ k₂ ≤ (|C₃| * H ^ k₃) ^ k₂ :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _))) _
  have hC1 : C₁ * H ^ k₁ ≤ |C₁| * H ^ k₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
  show ‖thetaSum F (om (g, h) Φ)‖ ≤ _
  calc ‖thetaSum F (om (g, h) Φ)‖ ≤ C₂ * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ := hb
    _ ≤ |C₂| * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) hm0
    _ ≤ |C₂| * (|C₁| * H ^ k₁) * (|C₃| * H ^ k₃) ^ k₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC1 (abs_nonneg _)) hmk hm0 (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hH0 _)))
    _ = |C₂| * |C₁| * |C₃| ^ k₂ * H ^ (k₁ + k₃ * k₂) := by rw [pow_add, pow_mul]; ring

end GlobalTheory.ThetaModGrowthPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleMatchExistenceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_match_existence : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β → (∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') → ∀ (ωA : GlobalTheory.Grid.WRep W X) (ωB : GlobalTheory.Grid.WRep W₁ X), GlobalTheory.Grid.IsWeil ψ true W X β (β / α) ωA → GlobalTheory.Grid.IsWeil ψ false W₁ X α (α / β) ωB → ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  first | exact @GlobalTheory.TripleWeilTransfer.exists_isMatch | exact GlobalTheory.TripleWeilTransfer.exists_isMatch | (intros; apply GlobalTheory.TripleWeilTransfer.exists_isMatch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharacterIntegralFramePowEqOneStatement
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitDetCharacter_integralFrame_pow_eq_one : ∀ {D : D7} (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 → ∀ ν : (AE D)ˣ →* Circle, KillsCong ν 𝔪 →
  ∀ {n : ℕ} (β : GL (Fin n) (EAf D)), IsIntM β.val → IsIntM (β⁻¹).val → ∃ m : ℕ, 0 < m ∧ unitChar ν e β.val ^ m = 1 := by
  first | exact @GlobalTheory.StdRead.unitChar_pow_eq_one | exact GlobalTheory.StdRead.unitChar_pow_eq_one | (intros; apply GlobalTheory.StdRead.unitChar_pow_eq_one <;> assumption)
end

