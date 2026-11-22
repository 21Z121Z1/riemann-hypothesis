import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumKernelBallMeasureLeIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0039
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormChart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ProjField

def NormChart {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (N₀ : LB B.left) : Prop :=
  ∃ (W V : Over (Sp k)) (π : W ⟶ V) (a : W ⟶ B) (U : B.left.Opens) (N : LB (V ⊗ B).left) (n : N.Sec),
    IsFinite π.left ∧ IsOpenImmersion a.left ∧ Nonempty W.left ∧ LocallyOfFiniteType W.hom ∧
    IsAffineOpen U ∧ (U : Set B.left).Nonempty ∧ N.IsLB ∧ LBIso N (N₀.pull (snd V B).left) ∧
    ∀ x : (V ⊗ B).left, x ∈ Out.nonzeroLocus n ↔
      ∀ z : (W ⊗ B).left, (π ▷ B).left z = x → z ∈ ((fst W B ≫ a) * snd W B).left ⁻¹ᵁ U

end GlobalTheory.ProjField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDbarFormSubLogMetricLe
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

open Matrix Complex ComplexConjugate

namespace GlobalTheory.CurveDens

theorem proj_rank_two_identity (A Dr : ℝ) (C x y da q : ℂ) (hA : 0 < A) (hQpos : 0 < Dr - normSq C / A) :
    ‖(x * da + y * (A*q + da*((A:ℂ)⁻¹*C))) - (x * A + y * C) * (((A⁻¹:ℝ):ℂ) * da)‖^2 =
    (A * (x * A * conj x + x * conj C * conj y + y * C * conj x + y * Dr * conj y).re - ‖x*A + y*C‖^2) *
      (Real.pi * (2 * (-I * (kappa * ((((Dr - normSq C / A : ℝ)) : ℂ)⁻¹ * conj (-q) * A * (-q)))).re)) := by
  have e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
  have hX : (x * da + y * (A*q + da*((A:ℂ)⁻¹*C))) - (x * A + y * C) * (((A⁻¹:ℝ):ℂ) * da) = y * A * q := by
    have : (A:ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    push_cast; field_simp; ring
  have hT : (((Dr - normSq C / A : ℝ)) : ℂ)⁻¹ * conj (-q) * A * (-q) = ((A * normSq q / (Dr - normSq C / A) : ℝ) : ℂ) := by
    have h0 : conj (-q) * (-q) = (normSq q : ℂ) := by rw [map_neg, neg_mul_neg, mul_comm, Complex.mul_conj]
    have hQ0 : (Dr - normSq C / A) ≠ 0 := hQpos.ne'
    calc _ = (((Dr - normSq C / A : ℝ)) : ℂ)⁻¹ * A * (conj (-q) * (-q)) := by ring
      _ = _ := by rw [h0]; push_cast; field_simp
  rw [hX, hT, ← mul_assoc (-I) kappa, e, ← ofReal_mul, ofReal_re, Complex.sq_norm, Complex.sq_norm]
  have hF : (x * A * conj x + x * conj C * conj y + y * C * conj x + y * Dr * conj y).re =
      A * normSq x + 2 * (x * conj C * conj y).re + Dr * normSq y := by
    simp [normSq_apply, mul_re, mul_im, conj_re, conj_im]; ring
  have hK : A * (x * A * conj x + x * conj C * conj y + y * C * conj x + y * Dr * conj y).re - normSq (x*A + y*C) =
      A * normSq y * (Dr - normSq C / A) := by
    rw [hF]
    simp only [normSq_apply, mul_re, mul_im, conj_re, conj_im, add_re, add_im, ofReal_re, ofReal_im]
    field_simp
    ring
  rw [hK, normSq_mul, normSq_mul, normSq_ofReal]
  have hpi : 0 < Real.pi := Real.pi_pos
  generalize Dr - normSq C / A = Qr at hQpos ⊢
  field_simp

theorem norm_sq_dbar_proj_rank_two (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (G : E → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (s : E → Fin 1 ⊕ Fin 1 → ℂ) (ξ z : E) (hG : MContDiffAt 1 G z) (hP : ∀ᶠ x in 𝓝 z, (G x).PosDef) (hs : ∀ i, DifferentiableAt ℂ (fun x => s x i) z) : ‖dbar (fun x => form (G x) (s x) (Pi.single (Sum.inl 0) 1)) z ξ - form (G z) (s z) (Pi.single (Sum.inl 0) 1) * dbar (fun x => (Real.log (G x (Sum.inl 0) (Sum.inl 0)).re : ℂ)) z ξ‖ ^ 2 = ((G z (Sum.inl 0) (Sum.inl 0)).re * (form (G z) (s z) (s z)).re - ‖form (G z) (s z) (Pi.single (Sum.inl 0) 1)‖ ^ 2) * (Real.pi * (2 * diagVal (extTrace G z) ξ)) := by
  set i₁ : Fin 1 ⊕ Fin 1 := Sum.inl 0 with hi₁
  set i₂ : Fin 1 ⊕ Fin 1 := Sum.inr 0 with hi₂
  have hz : (G z).PosDef := hP.self_of_nhds
  have hform1 : ∀ x, form (G x) (s x) (Pi.single i₁ 1) = s x i₁ * G x i₁ i₁ + s x i₂ * G x i₂ i₁ :=
    fun x => by simp [i₁, i₂, form_eq_sum, Fintype.sum_sum_type, Pi.single_apply]
  have hformss : form (G z) (s z) (s z) = s z i₁ * G z i₁ i₁ * conj (s z i₁) + s z i₁ * G z i₁ i₂ * conj (s z i₂)
     + s z i₂ * G z i₂ i₁ * conj (s z i₁) + s z i₂ * G z i₂ i₂ * conj (s z i₂) := by
    simp [i₁, i₂, form_eq_sum, Fintype.sum_sum_type]; ring
  have hda : DifferentiableAt ℝ (fun x => G x i₁ i₁) z := (hG i₁ i₁).differentiableAt one_ne_zero
  have hdc : DifferentiableAt ℝ (fun x => G x i₂ i₁) z := (hG i₂ i₁).differentiableAt one_ne_zero
  have hsR : ∀ i, DifferentiableAt ℝ (fun x => s x i) z := fun i => (hs i).restrictScalars ℝ

  have h1 : dbar (fun x => form (G x) (s x) (Pi.single i₁ 1)) z ξ =
      s z i₁ * dbar (fun x => G x i₁ i₁) z ξ + s z i₂ * dbar (fun x => G x i₂ i₁) z ξ := by
    simp only [hform1]
    rw [dbar_add ((hsR i₁).fun_mul hda) ((hsR i₂).fun_mul hdc), ContinuousLinearMap.add_apply,
      dbar_mul (hsR i₁) hda, dbar_mul (hsR i₂) hdc, dbar_eq_zero (hs i₁), dbar_eq_zero (hs i₂)]
    simp

  have hreal : ∀ᶠ x in 𝓝 z, G x i₁ i₁ = ((G x i₁ i₁).re : ℂ) := hP.mono fun x hx => by
    have := (Complex.lt_def.1 (hx.diag_pos (i := i₁))).2
    exact Complex.ext (by simp) (by simp [← this])
  have hApos : 0 < (G z i₁ i₁).re := (Complex.lt_def.1 (hz.diag_pos (i := i₁))).1

  have h2 : dbar (fun x => (Real.log (G x i₁ i₁).re : ℂ)) z ξ =
      (((G z i₁ i₁).re)⁻¹ : ℝ) * dbar (fun x => G x i₁ i₁) z ξ := by
    have hg : DifferentiableAt ℝ (fun x => (G x i₁ i₁).re) z := (Complex.reCLM.differentiableAt).comp z hda
    rw [dbar_ofReal_comp (t := fun x => (G x i₁ i₁).re) (Real.hasDerivAt_log hApos.ne') hg,
      dbar_congr (hreal.mono fun x hx => hx.symm)]

  have hoc : ∀ x, orthCoeff (G x) 0 0 = (G x i₁ i₁)⁻¹ * G x i₂ i₁ := fun x => by
    simp [orthCoeff, Matrix.mul_apply, Matrix.inv_def, Matrix.det_unique, i₁, i₂]
    rfl
  have hane : ∀ᶠ x in 𝓝 z, G x i₁ i₁ ≠ 0 := hP.mono fun x hx => (hx.diag_pos (i := i₁)).ne'
  have hdoc : DifferentiableAt ℝ (fun x => (G x i₁ i₁)⁻¹ * G x i₂ i₁) z :=
    (hda.inv hane.self_of_nhds).fun_mul hdc
  have h3 : G z i₁ i₁ * dbar (fun x => (G x i₁ i₁)⁻¹ * G x i₂ i₁) z ξ
      + dbar (fun x => G x i₁ i₁) z ξ * ((G z i₁ i₁)⁻¹ * G z i₂ i₁) = dbar (fun x => G x i₂ i₁) z ξ := by
    rw [← dbar_mul hda hdoc]
    congr 1
    exact dbar_congr (hane.mono fun x hx => by simp only; field_simp)
  have hb : extForm G z ξ 0 0 = -dbar (fun x => (G x i₁ i₁)⁻¹ * G x i₂ i₁) z ξ := by
    rw [extForm_eq_neg_mdbar]
    simp only [Matrix.neg_apply, mdbar_apply, hoc]

  have htr : extTrace G z ξ ξ = kappa * ((quotGram (G z) 0 0)⁻¹ * conj (extForm G z ξ 0 0) * G z i₁ i₁ * extForm G z ξ 0 0) := by
    simp [extTrace, extFormAdj, adj, Matrix.trace_fin_one, Matrix.mul_apply, Matrix.inv_def, Matrix.det_unique, subGram, Matrix.toBlocks₁₁, i₁]
  have hQ : quotGram (G z) 0 0 = G z i₂ i₂ - G z i₂ i₁ * (G z i₁ i₁)⁻¹ * G z i₁ i₂ := by
    simp [quotGram, Matrix.mul_apply, Matrix.inv_def, Matrix.det_unique, i₁, i₂]
    rfl
  have hQpos := (Complex.lt_def.1 ((posDef_quotGram hz).diag_pos (i := 0))).1
  have hGb : G z i₁ i₂ = conj (G z i₂ i₁) := (hz.isHermitian.apply i₁ i₂).symm
  have hGd : G z i₂ i₂ = ((G z i₂ i₂).re : ℂ) := by
    have := (Complex.lt_def.1 (hz.diag_pos (i := i₂))).2
    exact Complex.ext (by simp) (by simp [← this])
  rw [diagVal, htr, hQ, hb, h1, h2, hform1 z, hformss, ← h3, hGb, hGd]
  obtain ⟨A, hGa⟩ : ∃ A : ℝ, G z i₁ i₁ = A := ⟨_, hreal.self_of_nhds⟩
  rw [hQ, hGb, hGd] at hQpos
  rw [hGa] at hQpos ⊢
  simp only [ofReal_re] at hQpos ⊢
  have hQC : ((G z i₂ i₂).re : ℂ) - G z i₂ i₁ * (A : ℂ)⁻¹ * conj (G z i₂ i₁) =
      (((G z i₂ i₂).re - normSq (G z i₂ i₁) / A : ℝ) : ℂ) := by
    rw [mul_comm (G z i₂ i₁), mul_assoc, Complex.mul_conj]; push_cast; ring
  rw [hQC] at hQpos ⊢
  rw [Complex.zero_re, ofReal_re] at hQpos
  rw [hGa, ofReal_re] at hApos
  exact proj_rank_two_identity A _ _ _ _ _ _ hApos hQpos

end GlobalTheory.CurveDens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPairRealPointsSmulAdelicVacuumDetPowStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pair_real_points_smul_adelic_vacuum_det_pow : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
    (∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))) →
    ∀ g ∈ GinfC X.A, X.om (g, 1) X.vac = (∏ τ, (compAt X.θ τ (Formalism.L2.Theta.mt X.A g)).det ^ P.n τ) • X.vac := by
  first | exact @GlobalTheory.NormDict.vacuum_smul_realA | exact GlobalTheory.NormDict.vacuum_smul_realA | (intros; apply GlobalTheory.NormDict.vacuum_smul_realA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPowLeConstMulOneAddSumAbsBasisCoordPow
section
open IsDedekindDomain NumberField
open scoped Classical

namespace GlobalTheory

theorem norm_pow_le_const_mul_one_add_sum_abs_coord_pow :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (i : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x‖ ^ i ≤ K * (1 + ∑ c, |b.coord c x| ^ i) := by
  intro E _ _ ι _ b i
  have hB1 : 1 ≤ 1 + ∑ c, ‖b c‖ := by
    have : 0 ≤ ∑ c, ‖b c‖ := Finset.sum_nonneg (fun c _ => norm_nonneg _)
    linarith
  refine ⟨(1 + ∑ c, ‖b c‖) ^ i, by positivity, fun x => ?_⟩
  have hS : 0 ≤ ∑ c, |b.coord c x| ^ i := Finset.sum_nonneg (fun c _ => by positivity)
  have hx : ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖ := by
    conv_lhs => rw [← b.sum_repr x]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, Module.Basis.coord_apply]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : ‖x‖ = 0 := by
      have : ∑ c, |b.coord c x| * ‖b c‖ = 0 := by simp
      linarith [norm_nonneg x]
    rw [h0]
    have hp : 1 ≤ (1 + ∑ c, ‖b c‖) ^ i := one_le_pow₀ hB1
    calc (0:ℝ) ^ i ≤ 1 := pow_le_one₀ le_rfl zero_le_one
      _ ≤ (1 + ∑ c, ‖b c‖) ^ i * (1 + ∑ c, |b.coord c x| ^ i) := by nlinarith
  · obtain ⟨c0, -, hc0⟩ := Finset.exists_max_image Finset.univ (fun c => |b.coord c x|)
      Finset.univ_nonempty
    have h1 : ‖x‖ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖) := by
      calc ‖x‖ ≤ ∑ c, |b.coord c x| * ‖b c‖ := hx
        _ ≤ ∑ c, |b.coord c0 x| * ‖b c‖ := Finset.sum_le_sum (fun c _ =>
            mul_le_mul_of_nonneg_right (hc0 c (Finset.mem_univ _)) (norm_nonneg _))
        _ = |b.coord c0 x| * ∑ c, ‖b c‖ := by rw [Finset.mul_sum]
        _ ≤ |b.coord c0 x| * (1 + ∑ c, ‖b c‖) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have h2 : |b.coord c0 x| ^ i ≤ ∑ c, |b.coord c x| ^ i :=
      Finset.single_le_sum (f := fun c => |b.coord c x| ^ i) (fun c _ => by positivity)
        (Finset.mem_univ c0)
    calc ‖x‖ ^ i ≤ (|b.coord c0 x| * (1 + ∑ c, ‖b c‖)) ^ i :=
          pow_le_pow_left₀ (norm_nonneg _) h1 i
      _ = (1 + ∑ c, ‖b c‖) ^ i * |b.coord c0 x| ^ i := by rw [mul_pow, mul_comm]
      _ ≤ (1 + ∑ c, ‖b c‖) ^ i * (1 + ∑ c, |b.coord c x| ^ i) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemDivUniformizerPow
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem not_mem_div_uniformizer_pow : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ π : R, Irreducible π → ∀ x : Ω, x ≠ 0 → ∃ n : ℕ, x / algebraMap K Ω (algebraMap R K π) ^ n ∉ V := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V hV π hπ x hx
  classical
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable

  have hRV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by
      rw [hV]; exact ⟨r, rfl⟩
    exact this

  have hKV : ∀ c : K, algebraMap K Ω c ∈ V → ∃ r : R, algebraMap R K r = c := by
    intro c hc
    have : c ∈ V.toSubring.comap (algebraMap K Ω) := hc
    rw [hV] at this
    exact this
  have halgK : IsAlgebraic K x⁻¹ := Algebra.IsAlgebraic.isAlgebraic _
  have halgR : IsAlgebraic R x⁻¹ := (IsFractionRing.isAlgebraic_iff R K Ω).2 halgK
  obtain ⟨d, hd0, hint⟩ := halgR.exists_integral_multiple
  let f : R →+* V := (algebraMap R Ω).codRestrict V.toSubring hRV
  letI : Algebra R V := f.toAlgebra
  haveI : IsScalarTower R V Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hintV : IsIntegral V (d • x⁻¹) := hint.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hintV
  have hyV : d • x⁻¹ ∈ V := by rw [← hy]; exact y.2

  have hfin : FiniteMultiplicity π d := FiniteMultiplicity.of_not_isUnit hπ.not_isUnit hd0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ π ^ n ∣ d := by
    obtain ⟨m, hm⟩ := hfin
    exact ⟨m + 1, hm⟩
  refine ⟨n, fun hmem => hn ?_⟩
  have hprod : d • x⁻¹ * (x / algebraMap K Ω (algebraMap R K π) ^ n) ∈ V := V.mul_mem _ _ hyV hmem
  have hπ0 : algebraMap R K π ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hπ.ne_zero
  have heq : d • x⁻¹ * (x / algebraMap K Ω (algebraMap R K π) ^ n) =
      algebraMap K Ω (algebraMap R K d / algebraMap R K π ^ n) := by
    rw [Algebra.smul_def, map_div₀, map_pow]
    change (algebraMap K Ω) (algebraMap R K d) * x⁻¹ * _ = _
    field_simp
  rw [heq] at hprod
  obtain ⟨r, hr⟩ := hKV _ hprod
  refine ⟨r, ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_pow, hr]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumKernelBallMeasureLeIntegralStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitSum_kernel_ballMeasure_le_integral : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) := by
  first | exact @GlobalTheory.BallSum.ballSum_le | exact GlobalTheory.BallSum.ballSum_le | (intros; apply GlobalTheory.BallSum.ballSum_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsSectionsInverseDetFlagBundleStatement
section
open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.FlagMod GlobalTheory.FlagPlucker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pluckerMinors_sections_inverseDetFlagBundle : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) (Mc : MChart Y) {T : Scheme.{0}} (g : T ⟶ Z) (hg : ⊤ ≤ (g ≫ π) ⁻¹ᵁ Mc.U) (σ : E →+* ℂ) (m : Fin (Dw.mult σ)) (q : Fin (plkNum Mc m + 1)), ∃ s : ((F.LL (ind σ m)).pull g).Sec, s.f = plkLoc F Mc g hg σ m q := by
  first | exact @GlobalTheory.FlagPlucker.plkLoc_sec | exact GlobalTheory.FlagPlucker.plkLoc_sec | (intros; apply GlobalTheory.FlagPlucker.plkLoc_sec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceEqRangeFockMapVariableSignatu
section
noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD.PolRangeD

open GlobalTheory.RealLift.PolRangePf

theorem tensD_top {ι : Type} [Fintype ι] [DecidableEq ι] {σ : ι → Type}
    (N : Submodule ℂ (⨂[ℂ] w : ι, MvPolynomial (σ w) ℂ))
    (h1 : PiTensorProduct.tprod ℂ (fun w => (1 : MvPolynomial (σ w) ℂ)) ∈ N)
    (hX : ∀ (w : ι) (l : σ w), ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial (σ w) ℂ)) T ∈ N) :
    N = ⊤ := by
  have key : ∀ s : Finset ι, ∀ f : ∀ w, MvPolynomial (σ w) ℂ, (∀ i ∉ s, f i = 1) → PiTensorProduct.tprod ℂ f ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      have : f = fun w => 1 := funext fun i => hf i (Finset.notMem_empty i)
      rw [this]; exact h1
    | insert w₀ s hw₀ ih =>
      intro f hf
      let S : Submodule ℂ (MvPolynomial (σ w₀) ℂ) :=
        N.comap ((PiTensorProduct.tprod ℂ : MultilinearMap ℂ (fun w : ι => MvPolynomial (σ w) ℂ)
          (⨂[ℂ] w : ι, MvPolynomial (σ w) ℂ)).toLinearMap f w₀)
      have hS1 : (1 : MvPolynomial (σ w₀) ℂ) ∈ S := by
        show PiTensorProduct.tprod ℂ (Function.update f w₀ 1) ∈ N
        apply ih
        intro i hi
        by_cases h : i = w₀
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hf i (by simp [h, hi])
      have hSX : ∀ (l : σ w₀), ∀ p ∈ S, MvPolynomial.X l * p ∈ S := by
        intro l p hp
        have hp' : PiTensorProduct.tprod ℂ (Function.update f w₀ p) ∈ N := hp
        show PiTensorProduct.tprod ℂ (Function.update f w₀ (MvPolynomial.X l * p)) ∈ N
        have := hX w₀ l _ hp'
        rw [GlobalTheory.RealLift.atPl_tprod] at this
        simpa using this
      have htop := GlobalTheory.RealLift.mvPolynomial_submodule_eq_top S hS1 hSX
      have hf0 : f w₀ ∈ S := by rw [htop]; trivial
      have : PiTensorProduct.tprod ℂ (Function.update f w₀ (f w₀)) ∈ N := hf0
      simpa using this
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact key Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)

theorem tensD_top_heis {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (N : Submodule ℂ (⨂[ℂ] w : ι, Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))
    (h1 : PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))) ∈ N)
    (hN : ∀ w c, ∀ T ∈ N, atPl w (heisOp (P := P w) (Q := Q w) (R := R w) (S := S w) c) T ∈ N) : N = ⊤ := by
  refine tensD_top N h1 fun w l T hT => ?_
  let K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))) :=
    { carrier := {L | ∀ T ∈ N, atPl w L T ∈ N}
      add_mem' := fun {a b} ha hb T hT => by
        rw [atPl_add', LinearMap.add_apply]; exact N.add_mem (ha T hT) (hb T hT)
      zero_mem' := fun T _ => by rw [atPl_zero']; exact N.zero_mem
      smul_mem' := fun c a ha T hT => by rw [atPl_smul', LinearMap.smul_apply]; exact N.smul_mem c (ha T hT) }
  have hK : Submodule.span ℂ (Set.range (heisOp (P := P w) (Q := Q w) (R := R w) (S := S w))) ≤ K :=
    Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hN w c)
  exact hK (mulX_mem_span l) T hT

theorem sumPlD_twist_one {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}
    (c : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    sumPl (fun w => heisOp (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))))
        (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))))
      = Complex.I • sumPl (fun w => heisOp (c w))
        (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w)))) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, GlobalTheory.RealLift.atPl_tprod, GlobalTheory.RealLift.heisOp_twist_one]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (PiTensorProduct.tprod ℂ).map_update_smul _ w Complex.I _

theorem polRangeD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (P Q R S : InfinitePlace F → ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : ∀ w : InfinitePlace F, Matrix (Fin n) (Ix (P w) (Q w)) ℂ) (C : ∀ w : InfinitePlace F, Matrix (Fin d) (Ix (R w) (S w)) ℂ)
    (Φ : TensD F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)), IsCMExt F E σ → IsStd ψ →
    FramedD τ (incM F X.J) (incM F W.J) 1 Complex.I A C → (∀ w, X.θ w * A w = A w * Jm (P w) (Q w)) →
    (∀ w, W.θ w * C w = C w * Jm (R w) (S w)) → IsFockMapD ψ τ M.co A C Φ → LinearMap.range Φ = M.Pol ψ τ := by
  intro F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ
  have hL := GlobalTheory.RealLift.actsLaws
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₁ := fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h
  have uniq : ∀ u (f f₁ f₂ : SInf F (Fin n × Fin d)), ActsD (evI F) (M.heisLine ψ u) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₂ → f₁ = f₂ := fun u f f₁ f₂ h1 h2 => (hL F _ f f₁ f₂).2.2.1 _ h1 h2
  choose A' hA' using fun w => (hfr.2.1 w).2
  choose C' hC' using fun w => (hfr.2.2 w).2
  have decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w,
      u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := by
    intro u w
    rw [show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ =
        (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc], hA', hC']
    simp
  have der : ∀ u, At (evI F) u → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T,
      ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T)) :=
    fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)
  have tw : ∀ w (c : Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (e : ℂ),
      A w * (e • (Jm (P w) (Q w) * c * Jm (R w) (S w))) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm (R w) (S w) * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']
    calc A w * (e • (Jm (P w) (Q w) * c * Jm (R w) (S w))) * (C w)ᵀ
          = e • ((A w * Jm (P w) (Q w)) * c * (Jm (R w) (S w) * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  have gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))))) := by
    refine ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
    have hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := decomp u
    have hc' : ∀ w, u'.map (piInf (τ w)) =
        A w * (Complex.I • (Jm (P w) (Q w) * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm (R w) (S w))) * (C w)ᵀ := by
      intro w; rw [hrel w, tw, ← hc w]; simp
    rw [uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPlD_twist_one, map_smul]
  have gauss_mem : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h => by
    unfold Model.Pol
    exact Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have pol_der : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := by
    intro u hu f hf f₁ h1
    unfold Model.Pol at hf ⊢
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h1
  apply le_antisymm
  · rintro _ ⟨T, rfl⟩
    have htop : (M.Pol ψ τ).comap Φ = ⊤ := by
      refine tensD_top_heis _ (gauss_mem _ gauss1) fun w c T hT => ?_
      obtain ⟨u, hu, hu'⟩ := exists_mat_at hcm τ
        (fun w' => A w' * Function.update (0 : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w c w' * (C w')ᵀ)
      have hs : sumPl (fun w' => heisOp (Function.update
          (0 : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w c w')) T = atPl w (heisOp c) T := by
        rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w]
        · simp
        · intro b _ hb; simp [Function.update_of_ne hb, heisOp_zero, atPl_zero']
        · simp
      have := pol_der u hu _ hT _ (der u hu _ hu' T)
      rwa [hs] at this
    have : T ∈ (M.Pol ψ τ).comap Φ := htop ▸ Submodule.mem_top
    exact this
  · unfold Model.Pol
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩
    · obtain ⟨ε, hε⟩ := hf₀
      obtain ⟨z, hz⟩ := GlobalTheory.T.fock_vacuum_line_placewise_signatures F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
        Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
          hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
      exact ⟨z • PiTensorProduct.tprod ℂ (fun w => (1 : Formalism.BasicNotions.TH.Pol (P w) (Q w) (R w) (S w))), by rw [map_smul, hz]⟩
    · obtain ⟨T, rfl⟩ := hf
      exact ⟨_, (uniq u _ _ _ (der u hu _ (decomp u) T) h1)⟩

end GlobalTheory.HoweD.PolRangeD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparationStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudo_coefficient_separation : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → (∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.CuspidalOperators V μ) → GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTerm → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → SpecTrace := by
  first | exact @GlobalTheory.SpecTraceProof.specTrace | exact GlobalTheory.SpecTraceProof.specTrace | (intros; apply GlobalTheory.SpecTraceProof.specTrace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineIsLineOfPlaceStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_line_is_line_of_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∃ (w : InfinitePlace F) (Z : Matrix (Fin n) (Fin n) ℂ), IsLineOf σ J (τ w) Z γ := by
  first | exact @GlobalTheory.LeviHC.isLineOf_of_isRealLine | exact GlobalTheory.LeviHC.isLineOf_of_isRealLine | (intros; apply GlobalTheory.LeviHC.isLineOf_of_isRealLine <;> assumption)
end

