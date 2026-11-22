import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0355
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0413
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0415
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorProductIrreducibleCountableDimen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0416
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0417
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0418

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalZetaSumsAbsolutelyConvergentUniform
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta.AbsConv

theorem invGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r N : ℕ) (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), KerGL w N z φ → ∀ g, ∀ k ∈ KGL w r, φ (g * k) = φ g := by
  intro E _ _ w r N z φ h g k hk
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV (E := E) w
  obtain ⟨d, -, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w r ϖ (mem_Ov_of_isUnifV hϖ) hϖ g
  have htd : (k₁⁻¹ * g * k₂⁻¹ : GL (Fin r) (w.adicCompletion E)).1 = Matrix.diagonal (fun i => ϖ ^ d i) := by
    rw [Units.val_mul, Units.val_mul, e]
    simp [Matrix.mul_assoc]
    rfl
  calc φ (g * k) = φ (k₁ * (k₁⁻¹ * g * k₂⁻¹) * (k₂ * k)) := by congr 1; group
    _ = φ (k₁ * (k₁⁻¹ * g * k₂⁻¹) * k₂) := by
      rw [h ϖ hϖ d _ htd k₁ hk₁ (k₂ * k) (mul_mem hk₂ hk), h ϖ hϖ d _ htd k₁ hk₁ k₂ hk₂]
    _ = φ g := by congr 1; group

theorem invU : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q r N : ℕ), IsUnramInv ϖ σ q → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), KerU ϖ q N z φ → ∀ g, ∀ k ∈ KU σ r, φ (g * k) = φ g := by
  intro E _ _ w ϖ σ q r N hU z φ h g k hk
  obtain ⟨d, t, -, htd, k₁, hk₁, k₂, hk₂, rfl⟩ := cartanU hU g
  rw [show k₁ * t * k₂ * k = k₁ * t * (k₂ * k) by group, h d t htd k₁ hk₁ _ (mul_mem hk₂ hk), h d t htd k₁ hk₁ k₂ hk₂]

theorem transport : ∀ (G H : Type) [Group G] [Group H] (e : G ≃* H) (K : Subgroup G) (K' : Subgroup H), (∀ g, g ∈ K ↔ e g ∈ K') → ∀ (f : H → ℝ), (∀ h, ∀ k ∈ K', f (h * k) = f h) → ∀ A : ℝ, HasSum (fun a : H ⧸ K' => f a.out) A → HasSum (fun a : G ⧸ K => f (e a.out)) A := by
  intro G H _ _ e K K' hK f hf A hA
  let Φ : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv (fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK]
    simp)
  have key : ∀ a : G ⧸ K, f (Φ a).out = f (e a.out) := by
    intro a
    have h1 : Φ a = (QuotientGroup.mk (e a.out) : H ⧸ K') := by
      conv_lhs => rw [← Quotient.out_eq a]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K' (e a.out)
    rw [h1, hk, hf _ _ k.2]
  have := (Φ.hasSum_iff (f := fun b : H ⧸ K' => f b.out)).2 hA
  simpa [Function.comp_def, key] using this

theorem glSum : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r + 5 ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∃ A : ℝ, HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => ‖φ a.out‖) A ∧ |A - 1| ≤ 27 ^ r * ((qV E w : ℝ) ^ 2)⁻¹ := by
  intro hP E _ _ w r t ht z φ hz hk
  obtain ⟨B, hc, hb, hs⟩ := GlobalTheory.T.hasSum_norm_sphericalZetaKernelGL_trivialRep hP E w r t (by omega) z φ hz hk
  refine ⟨_, by simpa using Complex.hasSum_re hs, ?_⟩
  have hq2 : 2 ≤ qV E w := one_lt_absNorm w
  have hX : ‖npow w (-((1 + (t : ℂ)) / 2))‖ = (qV E w : ℝ) ^ (-((1 + (t : ℝ)) / 2)) := by
    rw [norm_npow]
    congr 1
    simp
  refine le_trans ?_ (GlobalTheory.T.norm_GL_zetaSum_trivialParameter_sub_one_le (qV E w) hq2 r t ht B hc hb _ hX)
  have := Complex.abs_re_le_norm (eulerFac B (npow w (-((1 + (t : ℂ)) / 2))) *
    eulerFac (B.map fun β => β⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) *
      ∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹) - 1)
  simpa using this

theorem uSum : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r + 5 ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∃ A : ℝ, HasSum (fun a : GU σ r ⧸ KU σ r => ‖φ a.out‖) A ∧ |A - 1| ≤ 27 ^ r * ((q : ℝ) ^ 2)⁻¹ := by
  intro L _ _ _ ϖ σ q r t hU ht z φ hz hk
  obtain ⟨α, hb, hs⟩ := GlobalTheory.T.hasSum_norm_sphericalZetaKernel_unramifiedUnitary L ϖ σ q r t hU (by omega) z φ hz hk
  refine ⟨_, by simpa using Complex.hasSum_re hs, ?_⟩
  refine le_trans ?_ (GlobalTheory.T.norm_unitaryZetaSum_trivialBound_sub_one_le q r t hU.2.2.2.2.2.1 ht α hb)
  have := Complex.abs_re_le_norm (eulerFac (bcParam r α) (((q : ℂ) ^ (t + 1))⁻¹) *
    ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ (r + t))⁻¹) - 1)
  simpa using this

theorem local_place (hP : GlobalTheory.Published.UnramifiedDoublingGL) (D : D7) (V : HSp D) (hr : V.rank = D.R.r)
    (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ) (hz : ∀ w, ‖(z w : ℂ)‖ = 1) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Gv V v → ℂ) (hφ : IsLocKer V D.R.nV z v φ) :
    ∃ A : ℝ, HasSum (fun a : Gv V v ⧸ Kv V v => ‖φ a.out‖) A ∧
      |A - 1| ≤ 27 ^ D.R.r * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ := by
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hN : D.R.nV = V.rank + D.R.t := by rw [hr]; rfl
  have ht : V.rank + 5 ≤ D.R.t := by rw [hr]; exact D.R.rank_add_five_le
  rw [← hr]
  rcases GlobalTheory.LPositivity.split_or_inert D w with hs | hi
  · rw [hw] at hs
    obtain ⟨⟨e, he⟩, hq⟩ := GlobalTheory.NoExcl.chart V hw hs
    have hk := (hφ w hw).1 hs e he
    rw [hN] at hk
    obtain ⟨A, hA, hb⟩ := glSum hP D.host.E w V.rank D.R.t ht (z w) _ (hz w) hk
    refine ⟨A, ?_, ?_⟩
    · have := transport _ _ e (Kv V v) (KGL w V.rank) he.2 (fun g => ‖(φ ∘ e.symm) g‖)
        (fun g k hk' => congrArg norm (invGL _ w _ _ _ _ hk g k hk')) A hA
      simpa using this
    · have hq' : (qV D.host.E w : ℝ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
        rw [show qV D.host.E w = Ideal.absNorm w.asIdeal from rfl, hq]; rfl
      rwa [hq'] at hb
  · rw [hw] at hi
    obtain ⟨c, ϖ, e, hU, he, -, -⟩ := GlobalTheory.LPositivity.exists_inert_chart (isCMExt_host D) (GlobalTheory.NoExcl.isHermND_gram V)
      (SelfDual.isLattice_frameLat V) (SelfDual.isSelfDualAt_frameLat D V v) hw hi
    have hk := (hφ w hw).2 hi c ϖ e hU he
    rw [hN] at hk
    obtain ⟨A, hA, hb⟩ := uSum _ ϖ c (qV D.host.F v) V.rank D.R.t hU ht (z w) _ (hz w) hk
    refine ⟨A, ?_, hb⟩
    have := transport _ _ e (Kv V v) (KU c V.rank) he.2.2 (fun g => ‖(φ ∘ e.symm) g‖)
      (fun g k hk' => congrArg norm (invU _ w ϖ c _ _ _ hU _ _ hk g k hk')) A hA
    simpa using this

theorem absConv_localZeta : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (D : D7) (V : HSp D), V.rank = D.R.r → ∀ (z : HeightOneSpectrum (𝓞 D.host.E) → ℂˣ), (∀ w, ‖(z w : ℂ)‖ = 1) → ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (φ : ∀ v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb}, Gv V v.1 → ℂ), (∀ v, IsLocKer V D.R.nV z v.1 (φ v)) → ∃ A : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} → ℝ, Summable (fun v => A v - 1) ∧ ∀ v, HasSum (fun a : Gv V v.1 ⧸ Kv V v.1 => ‖φ v a.out‖) (A v) := by
  intro hP D V hr z hz Sb φ hφ
  choose A hA hB using fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => local_place hP D V hr z hz v.1 (φ v) (hφ v)
  refine ⟨A, ?_, hA⟩
  have hs := (summable_rpow (K := D.host.F) ((Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (σ := 2) (by norm_num)).mul_left (27 ^ D.R.r)
  refine Summable.of_norm_bounded hs fun v => ?_
  rw [Real.norm_eq_abs]
  refine (hB v).trans (le_of_eq ?_)
  congr 1
  rw [Real.rpow_neg (by positivity), Real.rpow_two]

end GlobalTheory.FinZeta.AbsConv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelThetaSeriesModerateGrowth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedSeriesGrowth

theorem mixed_series_growth : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ A : ℕ, ∀ f, IsThetaFunO ψ V W f → ∃ c : ℝ, ∀ (g : GA D V) (h : GA D W), (∀ y : Matrix (Fin W.rank) (Fin r) D.host.E, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω p f)) 0) ∧ ∑' y : Matrix (Fin W.rank) (Fin r) D.host.E, ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (g, h) f)) 0‖ₑ ≤ ENNReal.ofReal (c * (GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h) ^ A) := by
  intro D V V' W r C C' B hs h1 h2 h3 ψ χS χT ω hω μ 𝓨 hμ
  obtain ⟨⟨θ, hθ⟩, -, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨A₁, d, hF⟩ := GlobalTheory.T.mixedModelThetaTerms_summable_heightBound D V V' W r C C' B hs h1 h2 h3 ψ hω.std θ hθ μ 𝓨 hμ
  obtain ⟨A₂, hS⟩ := GlobalTheory.T.heisenbergWords_weilOperator_supNorm_polynomialGrowth D ψ V W χS χT ω hω θ hθ d
  refine ⟨A₁ + A₂, fun f hf => ?_⟩
  obtain ⟨U, hU, hl⟩ := hf.level
  obtain ⟨K, hK⟩ := hF U hU
  obtain ⟨c, hc⟩ := hS f hf
  refine ⟨max K 0 * max c 0, fun g h => ⟨fun y => GlobalTheory.T.continuous_restrictedHeisenbergWeilTranslate_at_zero D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ f hf _, ?_⟩⟩
  have hH : 0 ≤ GlobalTheory.Grow.height V g * GlobalTheory.Grow.height W h :=
    mul_nonneg (GlobalTheory.Grow.height_pos V g).le (GlobalTheory.Grow.height_pos W h).le
  refine (hK g h (ω (g, h) f) (hω.om_pres _ f hf) (fun u hu h0 => ?_)).trans ?_
  · rw [← hω.om_heis g h u f hf, hl u hu h0]
  · refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left K 0) (pow_nonneg hH _)))
      ((hc g h).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left c 0)
        (pow_nonneg hH _))))).trans_eq ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right K 0) (pow_nonneg hH _)), pow_add]
    congr 1; ring

end GlobalTheory.MixedSeriesGrowth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MoyalOrthogonalityHeisenbergThetaFunctions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.MoyalTheta

theorem orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) f f₀, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Integrable (fun w => thPair v.μ v.𝓕 f (heisO ψ S T w f₀)) v.μ ∧ ∀ x, ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ = thPair v.μ v.𝓕 f₀ f₀ * f x := by
  intro D ψ hψ S T v f f₀ hf hf₀
  have hv : IsCovolOne (ratL T S) v.μ v.𝓕 := v.covol
  obtain ⟨hμ, h𝓕, h1⟩ := hv
  obtain ⟨i1, i2, i3, i4, i5, -, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : IsTopologicalAddGroup (WO S T) := i1
  haveI : LocallyCompactSpace (WO S T) := i2
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : T2Space (WO S T) := i4
  haveI : DiscreteTopology (ratL T S) := i5
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hμ
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨-, -, -, -, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hcc := GlobalTheory.T.continuous_thetaMatrixCoeff_heisenbergTranslate D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀
  obtain ⟨C, hC⟩ := GlobalTheory.T.rationalTranslateSum_bounded_rapidDecay D ψ hψ θ hθ S T _ (GlobalTheory.T.thetaMatrixCoeff_eq_zero_unless_orthogonal_level D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀)
    (GlobalTheory.T.thetaMatrixCoeff_polynomialDecay_realDirections D ψ hψ θ hθ S T v.μ v.𝓕 v.covol f f₀ hf hf₀)
  have hint : Integrable (fun w => thPair v.μ v.𝓕 f (heisO ψ S T w f₀)) v.μ :=
    GlobalTheory.T.integrable_of_tsum_norm_translate_le (WO S T) (ratL T S) v.μ inferInstance v.𝓕 h𝓕 (by rw [h1]; exact ENNReal.one_lt_top) _ hcc C hC
  refine ⟨hint, fun x => ?_⟩
  have hψn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have hgc : Continuous fun w => heisO ψ S T w f₀ x := by
    unfold heisO
    exact (hψ.1.1.comp (hcont.comp (continuous_const.prodMk continuous_id))).mul
      (hf₀.cont.comp (continuous_const.add continuous_id))
  obtain ⟨-, ⟨B, hB⟩, -⟩ := GlobalTheory.ThetaSquare.squareIntegrable hψ f₀ hf₀
  have hgb : ∃ B : ℝ, ∀ w, ‖heisO ψ S T w f₀ x‖ ≤ B :=
    ⟨B, fun w => by rw [GlobalTheory.ThetaSquare.norm_heisO hψ]; exact hB _⟩
  rw [GlobalTheory.T.integral_eq_setIntegral_tsum_of_fundamentalDomain (WO S T) (ratL T S) v.μ inferInstance v.𝓕 h𝓕 _ _ hint hgc hgb]
  simp_rw [GlobalTheory.T.fourierInversion_thetaMatrixCoeff_rationalTranslates D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀ _ x (hC _).1]
  have e : ∀ w, f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x = f x * (f₀ (w + x) * star (f₀ (w + x))) := by
    intro w
    have hu : star (ψ (symplOH S T x w)) * ψ (symplOH S T x w) = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψn]; norm_num
    unfold heisO
    rw [star_mul, add_comm x w]
    linear_combination (f x * f₀ (w + x) * star (f₀ (w + x))) * hu
  simp_rw [e]
  rw [integral_const_mul]
  have hper : ∀ γ ∈ ratL T S, ∀ w : WO S T, f₀ (γ + w) * star (f₀ (γ + w)) = f₀ w * star (f₀ w) := by
    rintro _ ⟨γ, rfl⟩ w
    have hq := hf₀.quasi γ w
    have hu : ψ (-(symplOH S T (ratW T S γ) w)) * star (ψ (-(symplOH S T (ratW T S γ) w))) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψn]; norm_num
    change f₀ (ratW T S γ + w) * star (f₀ (ratW T S γ + w)) = _
    rw [hq, star_mul]
    linear_combination (f₀ w * star (f₀ w)) * hu
  rw [GlobalTheory.CompactQuotientFourier.setIntegral_translate (ratL T S) v.μ v.𝓕 h𝓕 (fun w => f₀ w * star (f₀ w)) hper x]
  unfold thPair
  ring

end GlobalTheory.MoyalTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates
section
open GlobalTheory.ArchUniq GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

namespace GlobalTheory.ArchUniq.SchrTransport

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coords (P : V → V → ℝ) (hP : IsPairing P) [FiniteDimensional ℝ V] (n : ℕ) (hn : Module.finrank ℝ V = n) :
    ∃ (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)),
      (∀ v, pPart (φ v) = C v.1) ∧ ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2 := by
  let C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (hn.trans (finrank_euclideanSpace_fin).symm)
  have hdim : Module.finrank ℝ (V × V) = Module.finrank ℝ (Fin n ⊕ Fin n → ℝ) := by
    simp [Module.finrank_prod, hn]
  let φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    LinearMap.linearEquivOfInjective (pairCoordsL C hP) (pairCoordsL_injective C hP) hdim
  have hφ : ∀ v, φ v = pairCoordsL C hP v := fun v => rfl
  refine ⟨C, φ, fun v => ?_, fun v y => ?_⟩
  · ext i; simp [hφ, pPart, pairCoordsL]
  · rw [pair_expand C hP y v.2]
    simp [hφ, qPart, pairCoordsL, PiLp.inner_apply, mul_comm]

theorem schr_coords {n : ℕ} (P : V → V → ℝ) (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (hp : ∀ v, pPart (φ v) = C v.1)
    (hq : ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2) (v : V × V) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    schrF P v (f ∘ C) = rhoFun (φ v) f ∘ C := by
  funext y
  have h2 : ⟪pPart (φ v), qPart (φ v)⟫ = -P v.1 v.2 := by rw [hp, real_inner_comm, hq]
  have h3 : ⟪C v.1, qPart (φ v)⟫ = -P v.1 v.2 := by rw [real_inner_comm, hq]
  simp only [schrF, rhoFun, phase, Function.comp_apply, map_add, hp, hq, h3]
  congr 2
  push_cast
  ring

theorem dRho_coords {n : ℕ} (P : V → V → ℝ) (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (φ : (V × V) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (hp : ∀ v, pPart (φ v) = C v.1)
    (hq : ∀ v y, ⟪qPart (φ v), C y⟫ = -P y v.2) (u : V × V) (g : 𝓢(V, ℂ)) (h : Sch (Fin n))
    (hg : ⇑g = ⇑h ∘ ⇑C) (y : V) :
    fderiv ℝ (⇑g) y u.1 - 2 * Real.pi * Complex.I * (P y u.2 : ℂ) * g y = dRho (φ u) h (C y) := by
  have hd : HasFDerivAt (⇑h ∘ ⇑C) ((fderiv ℝ (⇑h) (C y)).comp (C : V →L[ℝ] EuclideanSpace ℝ (Fin n))) y :=
    (h.hasFDerivAt (C y)).comp y C.hasFDerivAt
  rw [dRho_apply, hg, hd.fderiv, hp, hq]
  simp
  ring

theorem quad_eq_sum {l : Type} [Fintype l] [DecidableEq l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    quad X = ∑ p : (l ⊕ l) × (l ⊕ l), ((4 * Real.pi * Complex.I : ℂ)⁻¹ *
      ((((X * Matrix.J l ℝ) p.1 p.2 + (X * Matrix.J l ℝ) p.2 p.1) / 2 : ℝ) : ℂ)) •
        (dRho (Pi.single p.1 1) * dRho (Pi.single p.2 1)) := by
  rw [quad, Fintype.sum_prod_type, Finset.smul_sum]
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  rw [Finset.sum_comm (f := fun a b => (4 * Real.pi * Complex.I : ℂ)⁻¹ • (((X * Matrix.J l ℝ) a b / 2 : ℝ) : ℂ) •
    (dRho (Pi.single b 1) * dRho (Pi.single a 1))), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [smul_smul]
  rw [← add_smul]
  congr 1
  push_cast
  ring

theorem haar_coords {n : ℕ} [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (C : V ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ k : ℝ, 0 < k ∧ ∀ F : V → ℝ, ∫ y, F y ∂μ = k * ∫ x, F (C.symm x) := by
  let e : V ≃ᵐ EuclideanSpace ℝ (Fin n) := C.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = C y := fun y => rfl
  haveI : (μ.map e).IsAddHaarMeasure := C.isAddHaarMeasure_map μ
  have hk := Measure.isAddLeftInvariant_eq_smul (μ.map e) (volume : Measure (EuclideanSpace ℝ (Fin n)))
  refine ⟨(Measure.addHaarScalarFactor (μ.map e) volume : ℝ),
    NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), fun F => ?_⟩
  have h1 : ∫ y, F y ∂μ = ∫ x, F (C.symm x) ∂(μ.map e) := by
    rw [integral_map_equiv]
    simp [he]
  rw [h1, congrArg (fun m => ∫ x, F (C.symm x) ∂m) hk]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

theorem transport : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    (∀ (A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n)),
      (∀ w, Continuous fun t => A' t w) → (∀ s t f, T' (s + t) f = T' s (T' t f)) → (∀ f, T' 0 f = f) →
      (∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f)) →
      (∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T' t f y) →
      ∃ (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (c : ℂ),
        ∀ f y, HasDerivAt (fun t => T' t f y) (quad X f y + c * f y) 0) →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  intro V _ _ _ _ _ μ hμ P hP n hn H A T hAc hTadd hT0 hTi hTl2 hTc
  obtain ⟨C, φ, hp, hq⟩ := coords P hP n hn
  have hS := schr_coords P C φ hp hq
  let toE : 𝓢(V, ℂ) →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin n) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  let T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n) := fun t => toE.toLinearMap ∘ₗ T t ∘ₗ toV.toLinearMap
  let A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hT' : ∀ t h, T' t h = toE (T t (toV h)) := fun t h => rfl
  obtain ⟨k, hk, hint⟩ := haar_coords μ C
  have c1 : ∀ w, Continuous fun t => A' t w := by
    intro w
    exact (φ.toLinearMap.continuous_of_finiteDimensional).comp (hAc (φ.symm w))
  have c2 : ∀ s t f, T' (s + t) f = T' s (T' t f) := by
    intro s t h
    simp only [hT', hVE, hTadd]
  have c3 : ∀ f, T' 0 f = f := by
    intro h
    simp [hT', hT0, hEV]
  have c4 : ∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f) := by
    intro t w f f₁ hf
    have e1 : ⇑(toV f₁) = schrF P (φ.symm w) ⇑(toV f) := by
      funext x
      have := congrFun (hS (φ.symm w) ⇑f) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hf]
      exact this.symm
    have e2 := hTi t _ _ _ e1
    rw [hT' t f₁, hT' t f, htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin n) → ℂ, ⇑(T t (toV f)) = G ∘ ⇑C :=
      ⟨⇑(T t (toV f)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp [A']
  have c5 : ∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    intro t h
    have e := hTl2 t (toV h)
    rw [hint, hint] at e
    simp only [htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
    exact mul_left_cancel₀ hk.ne' e
  have c6 : ∀ f y, Continuous fun t => T' t f y := by
    intro h y
    exact hTc (toV h) (C.symm y)
  obtain ⟨X, c, hX⟩ := H A' T' c1 c2 c3 c4 c5 c6
  let eq := (Fintype.equivFin ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n))).symm
  let S := X * Matrix.J (Fin n) ℝ
  refine ⟨Fintype.card ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)), fun i => φ.symm (Pi.single (eq i).1 1),
    fun i => φ.symm (Pi.single (eq i).2 1),
    fun i => (4 * Real.pi * Complex.I : ℂ)⁻¹ * (((S (eq i).1 (eq i).2 + S (eq i).2 (eq i).1) / 2 : ℝ) : ℂ), c, ?_⟩
  intro f g₁ g₂ hg₁ hg₂ y
  have hf : ⇑f = ⇑(toE f) ∘ ⇑C := by ext x; simp [htoE]
  have h1 : ∀ i, ⇑(g₁ i) = ⇑(dRho (Pi.single (eq i).2 1) (toE f)) ∘ ⇑C := fun i => by
    ext x
    rw [hg₁, dRho_coords P C φ hp hq _ f (toE f) hf, LinearEquiv.apply_symm_apply]
    rfl
  have h2 : ∀ i, g₂ i y = dRho (Pi.single (eq i).1 1) (dRho (Pi.single (eq i).2 1) (toE f)) (C y) := fun i => by
    rw [hg₂, dRho_coords P C φ hp hq _ (g₁ i) _ (h1 i), LinearEquiv.apply_symm_apply]
  have hd := hX (toE f) (C y)
  have e1 : (fun t => T' t (toE f) (C y)) = fun t => T t f y := by
    funext t
    simp [hT', htoE, hVE]
  rw [e1] at hd
  convert hd using 1
  have e2 : toE f (C y) = f y := by simp [htoE]
  rw [e2, quad_eq_sum]
  congr 1
  simp only [h2, ContinuousLinearMap.coe_sum', Finset.sum_apply, SchwartzMap.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, SchwartzMap.smul_apply, ContinuousLinearMap.mul_apply, smul_eq_mul]
  exact Equiv.sum_comp eq (fun p => (4 * Real.pi * Complex.I : ℂ)⁻¹ * (((S p.1 p.2 + S p.2 p.1) / 2 : ℝ) : ℂ) *
    dRho (Pi.single p.1 1) (dRho (Pi.single p.2 1) (toE f)) (C y))

end GlobalTheory.ArchUniq.SchrTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorProductIrreducibleCountableDimenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedTensorProduct_irreducible_countable_dimension : ∀ {ι : Type} [DecidableEq ι] (N : ι → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (s : ∀ i, N i),
    {i | s i = 0}.Finite → (∀ i, Module.rank ℂ (N i) ≤ Cardinal.aleph0) → (∀ i, Nontrivial (N i)) →
    ∀ Sv : ∀ i, Set (Module.End ℂ (N i)),
    (∀ i, ∀ Q : Submodule ℂ (N i), (∀ a ∈ Sv i, ∀ x ∈ Q, a x ∈ Q) → Q = ⊥ ∨ Q = ⊤) →
    ∀ Op : ∀ i, Module.End ℂ (N i) → Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s),
    (∀ i, ∀ a ∈ Sv i, ∀ ξ, Formalism.MainNotions.KudlaSiegelWeil.Restr s ξ →
      Op i a (GlobalTheory.SmallThetaModules.pureT s ξ) = GlobalTheory.SmallThetaModules.pureT s (Function.update ξ i (a (ξ i)))) →
    ∀ Q : Submodule ℂ (GlobalTheory.SmallThetaModules.RTens s), (∀ i, ∀ a ∈ Sv i, ∀ x ∈ Q, Op i a x ∈ Q) → Q = ⊥ ∨ Q = ⊤ := by
  first | exact @GlobalTheory.rtens_irreducible | exact GlobalTheory.rtens_irreducible | (intros; apply GlobalTheory.rtens_irreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedThetaCoefficientEqIsotropicIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictedTheta_coefficient_eq_isotropic_integral : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ ν : Measure (Mx D W.rank r), ν.IsAddHaarMeasure ∧ ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ x : WO V' W, ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 F) w * star (res V V' W C B μ 𝓨 G w) ∂μ' = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) F w * star (G w) ∂μV) ∂ν := by
  first | exact @GlobalTheory.CoefUnfold.coef_unfold | exact GlobalTheory.CoefUnfold.coef_unfold | (intros; apply GlobalTheory.CoefUnfold.coef_unfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionWeilDataTwistCharacterTrivialSplitPlaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restriction_weilData_twistCharacter_trivial_splitPlaces : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e W g → c g = 1 := by
  first | exact @GlobalTheory.HalfAverage.charTwist_eq_one_at_split | exact GlobalTheory.HalfAverage.charTwist_eq_one_at_split | (intros; apply GlobalTheory.HalfAverage.charTwist_eq_one_at_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepVectorLocalPureTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStepVector_localPureTensor : ∀ D : D7, StepVecLocal D := by
  first | exact @GlobalTheory.StepVec.stepVecLocal | exact GlobalTheory.StepVec.stepVecLocal | (intros; apply GlobalTheory.StepVec.stepVecLocal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryQuotientHeight_comparable_wittDecomposition : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a := by
  first | exact @GlobalTheory.HtWitt.quotHeight_witt | exact GlobalTheory.HtWitt.quotHeight_witt | (intros; apply GlobalTheory.HtWitt.quotHeight_witt <;> assumption)
end

