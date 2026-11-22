import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1929
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralActionUnitCharacterEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierInversionUpToConstant
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.FourierLocInv

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem inversion_circle [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (μ : Measure (κ → k)) [μ.IsAddHaarMeasure] :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → k), ∀ a : κ → k,
      ∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ) ∂μ = d * φ (-a) := by
  classical
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ := (GlobalTheory.SplitWeil.selfDual_measure k ψ hc h1).1
  haveI := hν.1
  set m : Measure (κ → k) := Measure.pi fun _ => ν with hm
  have hμ : μ = μ.addHaarScalarFactor m • m := Measure.isAddLeftInvariant_eq_smul μ m
  set r := μ.addHaarScalarFactor m with hr_def
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact NeZero.ne μ hμ
  have hr' : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  refine ⟨((r : ℝ) : ℂ) ^ 2, pow_ne_zero 2 hr', fun φ hφ a => ?_⟩
  have hg : (fun x => φ (x + -a)) ∈ SB (κ → k) :=
    ⟨hφ.1.comp_continuous (Homeomorph.addRight (-a)).continuous, hφ.2.comp_homeomorph (Homeomorph.addRight (-a))⟩
  have key := (GlobalTheory.SplitWeil.FourierPi.fourier_pi k κ ψ hc h1 ν hν _ hg).2
  have hinner : ∀ y, ∫ x, φ (x + -a) * (ψ (x ⬝ᵥ y) : ℂ) ∂m
      = (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ) := by
    intro y
    rw [GlobalTheory.FourierLocBij.translate_fourier, neg_dotProduct, neg_neg, dotProduct_comm a y, mul_comm]
  have key' : ∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ) ∂m = φ (-a) := by
    refine Eq.trans ?_ (key.trans (congrArg φ (zero_add (-a))))
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact (hinner y).symm
  have hsm : ∀ G : (κ → k) → ℂ, ∫ y, G y ∂μ = ((r : ℝ) : ℂ) * ∫ y, G y ∂m := by
    intro G
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hfun : (fun y => (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ)) =
      fun y => ((r : ℝ) : ℂ) * ((∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ)) := by
    funext y
    rw [hsm, mul_assoc]
  rw [show (∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ) ∂μ) =
      ∫ y, ((r : ℝ) : ℂ) * ((∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ)) ∂μ from congrArg _ hfun,
    integral_const_mul, hsm, key']
  ring

end General

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourier_inversion : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (χ : AddChar (Fv F v) ℂ), Continuous χ → (∀ t, ‖χ t‖ = 1) →
    χ ≠ 1 → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure], ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → Fv F v), ∀ a : κ → Fv F v,
      ∫ y, (∫ x, φ x * χ (x ⬝ᵥ y) ∂μ) * χ (y ⬝ᵥ a) ∂μ = d * φ (-a) := by
  intro F _ _ v χ hc hn h1 κ _ inst _ μ _
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have e : inst = MeasurableSpace.pi := by
    rw [BorelSpace.measurable_eq (α := κ → Fv F v)]
    exact (BorelSpace.measurable_eq (α := κ → Fv F v) (self := Pi.borelSpace)).symm
  subst e
  have hcont : Continuous (GlobalTheory.FourierLocBij.toCircle χ hn) := Continuous.subtype_mk hc _
  have hne : GlobalTheory.FourierLocBij.toCircle χ hn ≠ 1 := by
    intro h
    apply h1
    ext t
    simpa [GlobalTheory.FourierLocBij.coe_toCircle] using
      congrArg (fun ψ : AddChar (Fv F v) Circle => ((ψ t : Circle) : ℂ)) h
  exact inversion_circle (GlobalTheory.FourierLocBij.toCircle χ hn) hcont hne κ μ

end GlobalTheory.FourierLocInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeHermitianSkew
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SplitTraceForm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ w) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem piW_inclR {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (e : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (inclR (F := F) (AF F) e) = τ e := by
  change evFin F v 1 * τ e = τ e
  simp

theorem sum_four_fintype_permute {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β] (f : α → β → α → β → R) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ b, ∑ a, f a b c e := by
  first
  | exact @_root_.GlobalTheory.FourTermSumReorder.sum_four_reorder
  | exact _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder
  | (apply _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder <;> assumption)
  | (intros; apply _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FourTermSumReorder.sum_four_reorder <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder ..)

theorem splitTrace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = J i j) → (∀ i j, σ (K j i) = -K i j) →
    ∀ (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x →
    GlobalTheory.AdelicU.evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) =
      ∑ i, ∑ j, (x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j * (-(J.map t * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j -
        ∑ i, ∑ j, (-(J.map t * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j * (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j := by
  intro F E _ _ _ _ _ σ hcm v t n d J K hJ hK x u hx
  have hzAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v)
      ((-1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) * GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) := by
    intro a ha
    have h0 : ∀ i j, a • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx a ha) i) j
      simpa using this
    simp only [GlobalTheory.WeilM.hTens, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    rw [show ∀ (p q r : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E), a • ((-1) * (x i j * p * q * r)) = -1 * ((a • x i j) * p * q * r) from
      fun p q r => by simp only [Algebra.smul_def]; ring, h0]
    simp
  show GlobalTheory.AdelicU.evFin F v (Algebra.trace (AF F) _ _) = _
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ hzAt, GlobalTheory.LatVac.evFin_liftV]
  simp only [GlobalTheory.WeilM.hTens, map_mul, map_neg, map_one, map_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, piW_cA, piW_inclR,
    GlobalTheory.AdelicU.comp_conj_conj hcm, AlgHom.comp_apply, hJ, hK]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, Finset.mul_sum, Finset.sum_mul]
  rw [sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [sum_four_fintype_permute]
    simp only [neg_mul, mul_neg, one_mul, Finset.sum_mul, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
end GlobalTheory.SplitTraceForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductCompatible
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

namespace GlobalTheory.EvOnto

open scoped Classical in

theorem ev_surjOn_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.SurjOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) →
    ∀ v, ∀ χ ∈ SB (κ → Fv F v), ∃ ψ ∈ SB (κ → Fv F v), ev v ψ = χ := by
  intro F _ _ κ _ e ei ev hSBev hfix he hsurj hne v χ hχ
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let Φ₁ : ∀ w : Pl F, (κ → Fv F w) → ℂ := fun w => ev w (stdInd F κ w)
  have hstdSB : ∀ w : Pl F, stdInd F κ w ∈ SB (κ → Fv F w) := fun w => GlobalTheory.StdVacuum.indicator_mem_SB w
  have hΦstd : ∀ᶠ w in cofinite, Φ₁ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := hfix
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v χ) ∈ schA F κ := by
    refine GlobalTheory.TensUniq.pure_mem_schA f₀ _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually Φ₁ v χ hΦstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hχ
    · rw [Function.update_of_ne hw]; exact hSBev w _ (hstdSB w)
  obtain ⟨Ψ, hΨ, heΨ⟩ := hsurj hmem
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ
  have hvac : ∀ i, ∀ᶠ w in cofinite, φ i w = stdInd F κ w := by
    intro i
    filter_upwards [T.eventually_cofinite_notMem] with w hT
    exact hstd i w hT
  have hvac' : ∀ i, ∀ᶠ w in cofinite, (fun w => ev w (φ i w)) w =
      Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hvac i, hfix] with w h1 h2
    rw [h1]; exact h2
  have hid : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v χ) =
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun w => ev w (φ i w) := by
    rw [← heΨ, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hSB i) (hvac i)
  obtain ⟨r₀, hr₀, hr₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f₀ Φ₁ hΦstd
  choose r hr hrt using fun i => GlobalTheory.PureFactor.exists_rest_factor v (ei (f i)) (fun w => ev w (φ i w)) (hvac' i)
  have hrt' : ∀ i, tens (evFin F v) (ev v (φ i v)) (r i) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun w => ev w (φ i w) := by
    intro i
    rw [hrt i]
    congr 1
    exact Function.update_eq_self v (fun w => ev w (φ i w))
  have hex : ∃ x₀, r₀ x₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v fun _ => 1) = 0 := by
      rw [← hr₀t]
      funext x
      simp [tens, hc]
    have hf : f₀ = 0 := by
      refine GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f₀ _ (fun w => ?_)
        (GlobalTheory.PureFactor.update_eventually Φ₁ v _ hΦstd) h0
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self]
        intro h
        exact one_ne_zero (congrFun h 0)
      · rw [Function.update_of_ne hw]; exact hne w
    exact hf₀ (by rw [hf]; rfl)
  obtain ⟨x₀, hx₀⟩ := hex
  refine ⟨∑ i, (r i x₀ / r₀ x₀) • φ i v, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hSB i v), ?_⟩
  funext y
  let z : κ → AF F := fun j => GlobalTheory.LatVac.liftV v (y j - evFin F v (x₀ j))
  have hz : At (evFin F v) z := by
    intro u hu
    funext j
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun j => evFin F v ((x₀ + z) j)) = y := by
    funext j
    rw [Pi.add_apply, map_add, GlobalTheory.LatVac.evFin_liftV]
    ring
  have key : χ y * r₀ x₀ = ∑ i, ev v (φ i v) y * r i x₀ := by
    have h := congrFun hid (x₀ + z)
    rw [← hr₀t, Finset.sum_apply] at h
    simp only [← hrt', tens, hev, hr₀ x₀ z hz] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [hr i x₀ z hz]
  rw [map_sum, Finset.sum_apply]
  apply mul_right_cancel₀ hx₀
  rw [key, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.EvOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductExtend
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.ArchBij

theorem bijective_arch : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) → Function.Bijective ei := by
  intro F _ _ κ _ e ei ev hSB hfix he hbij hne
  have hstdSB : ∀ v, stdInd F κ v ∈ SB (κ → Fv F v) := fun v => GlobalTheory.StdVacuum.indicator_mem_SB v
  have hstd0 : ∀ v, stdInd F κ v ≠ 0 := by
    intro v h0
    have h := congrFun h0 0
    have hm : (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem (v.adicCompletionIntegers F)
    simp only [stdInd, Set.indicator_of_mem hm, Pi.one_apply, Pi.zero_apply] at h
    exact one_ne_zero h
  constructor
  · refine (injective_iff_map_eq_zero ei).2 fun f hf => ?_
    have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ) ∈ schA F κ :=
      GlobalTheory.TensUniq.pure_mem_schA f (stdInd F κ) hstdSB (Filter.Eventually.of_forall fun _ => rfl)
    have h1 : e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ)) = e 0 := by
      rw [he f (stdInd F κ) hstdSB (Filter.Eventually.of_forall fun _ => rfl), hf, map_zero]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ) = 0 :=
      hbij.injOn hmem (schA F κ).zero_mem h1
    exact GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f (stdInd F κ) hstd0 (Filter.Eventually.of_forall fun _ => rfl) h2
  · intro h
    let Φ₁ : ∀ v : Pl F, (κ → Fv F v) → ℂ := fun w => ev w (stdInd F κ w)
    have hΦ₁SB : ∀ v, Φ₁ v ∈ SB (κ → Fv F v) := fun v => hSB v _ (hstdSB v)
    have hΦ₁std : ∀ᶠ v in Filter.cofinite,
        Φ₁ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := hfix
    have h₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h Φ₁ ∈ schA F κ := GlobalTheory.TensUniq.pure_mem_schA h Φ₁ hΦ₁SB hΦ₁std
    obtain ⟨Ψ, hΨ, heΨ⟩ := hbij.surjOn h₁
    obtain ⟨T, m, f, φ, hφSB, hφstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F κ Ψ hΨ
    have hvac : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = stdInd F κ v := fun i =>
      T.eventually_cofinite_notMem.mono fun v hT => hφstd i v hT
    have hid : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h Φ₁ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun v => ev v (φ i v) := by
      rw [← heΨ, hsum, map_sum]
      exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hφSB i) (hvac i)
    obtain ⟨y, hy⟩ := GlobalTheory.ArchSurj.exists_point_ne_zero Φ₁ hne hΦ₁std
    set c : ℂ := ∏ᶠ v, Φ₁ v (fun j => y j v) with hc
    have hc0 : c ≠ 0 := finprod_induction (fun a : ℂ => a ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hy
    set cs : Fin m → ℂ := fun i => ∏ᶠ v, ev v (φ i v) (fun j => y j v) with hcs
    refine ⟨∑ i, (cs i / c) • f i, ?_⟩
    refine DFunLike.ext _ _ fun x => ?_
    let a : κ → AF F := fun j => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x j), y j)
    have hI : (fun j => evI F (a j)) = x := by
      funext j
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x j)
    have hx : h x * c = ∑ i, ei (f i) x * cs i := by
      have := congrFun hid a
      rw [Finset.sum_apply] at this
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI] at this
      exact this
    rw [map_sum]
    have hs : (∑ i, ei ((cs i / c) • f i)) x = ∑ i, (cs i / c) * ei (f i) x := by
      rw [SchwartzMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]; rfl
    rw [hs]
    apply mul_right_cancel₀ hc0
    rw [hx, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp

end GlobalTheory.ArchBij
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundamentalDomainProdLtTop
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory

theorem isFundamentalDomain_stdDom_prod {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
    [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂]
    [IsTopologicalGroup G₂] [SecondCountableTopology G₂] [MeasurableSpace G₂] [BorelSpace G₂]
    (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂] (μ : Measure (G₁ × G₂)) :
    IsFundamentalDomain (Γ₁.prod Γ₂) (GlobalTheory.AutomorphicL2Unitary.stdDom Γ₁ ×ˢ GlobalTheory.AutomorphicL2Unitary.stdDom Γ₂) μ := by
  refine .mk' ((GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom Γ₁).prod (GlobalTheory.AutomorphicL2Unitary.measurableSet_stdDom Γ₂)).nullMeasurableSet ?_
  rintro ⟨a, b⟩
  obtain ⟨γ₁, h₁, u₁⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom Γ₁ a
  obtain ⟨γ₂, h₂, u₂⟩ := GlobalTheory.AutomorphicL2Unitary.existsUnique_stdDom Γ₂ b
  refine ⟨⟨((γ₁ : G₁), (γ₂ : G₂)), Subgroup.mem_prod.2 ⟨γ₁.2, γ₂.2⟩⟩, ⟨h₁, h₂⟩, ?_⟩
  rintro ⟨⟨c, d⟩, hcd⟩ ⟨hc, hd⟩
  have e₁ := u₁ ⟨c, (Subgroup.mem_prod.1 hcd).1⟩ hc
  have e₂ := u₂ ⟨d, (Subgroup.mem_prod.1 hcd).2⟩ hd
  ext <;> simp [← e₁, ← e₂]

theorem measure_fundamentalDomain_prod_lt_top : ∀ (G₁ G₂ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂] [MeasurableSpace G₂] [BorelSpace G₂] (Γ₁ : Subgroup G₁) (Γ₂ : Subgroup G₂) [DiscreteTopology Γ₁] [DiscreteTopology Γ₂], (∀ μ : Measure G₁, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₁ 𝓕 μ → μ 𝓕 ≠ ⊤) → (∀ μ : Measure G₂, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ₂ 𝓕 μ → μ 𝓕 ≠ ⊤) → ∀ μ : Measure (G₁ × G₂), μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain (Γ₁.prod Γ₂) 𝓕 μ → μ 𝓕 < ⊤ := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Γ₁ Γ₂ _ _ h₁ h₂ μ hμ 𝓕 h𝓕
  have hd := GlobalTheory.isFundamentalDomain_stdDom_prod Γ₁ Γ₂ μ
  haveI : Countable (Γ₁.prod Γ₂) := by
    have : Function.Injective (fun γ : Γ₁.prod Γ₂ => ((⟨(γ : G₁ × G₂).1, (Subgroup.mem_prod.1 γ.2).1⟩ : Γ₁),
      (⟨(γ : G₁ × G₂).2, (Subgroup.mem_prod.1 γ.2).2⟩ : Γ₂))) := by
      rintro ⟨⟨a, b⟩, _⟩ ⟨⟨c, d⟩, _⟩ h
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
      ext <;> simp [h.1, h.2]
    exact this.countable
  rw [h𝓕.measure_eq hd]
  have hp : (Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂) |>.IsHaarMeasure := inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ ((Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂)),
    Measure.smul_apply, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
  have a₁ := h₁ Measure.haar inferInstance _ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Γ₁ Measure.haar)
  have a₂ := h₂ Measure.haar inferInstance _ (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom Γ₂ Measure.haar)
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top a₁.lt_top a₂.lt_top)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCmCoordinateLatticeOfIntegralGramPairingStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cmCoordinateLattice_of_integral_gramPairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∀ barE : E →+* E, (∀ x : 𝓞 E, barE x = ((H.bar x : 𝓞 E) : E)) →
      ∀ d : Fin p → E, (∀ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ y : 𝓞 E, (y : E) = ∑ a, ∑ b, c a * (gP a b : E) * barE (d b)) →
        d ∈ GlobalTheory.FlatCM.HomLat.lat X := by
  first | exact @GlobalTheory.FlatCM.HomLat.mem_lat_of_dual | exact GlobalTheory.FlatCM.HomLat.mem_lat_of_dual | (intros; apply GlobalTheory.FlatCM.HomLat.mem_lat_of_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIdealIntegralTensorSwapIffMemIdealSubgroupStatement
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
theorem _root_.GlobalTheory.T.memIdealIntegral_tensorSwap_iff_mem_idealSubgroup : ∀ {D : D7} (𝔪 : Ideal (𝓞 D.host.E)) (y : Formalism.MainNotions.StandardLatticesGL3.AE D), InId 𝔪 (toE D y) ↔ y ∈ hatId D 𝔪 := by
  first | exact @GlobalTheory.StdRead.IdealDict.inId_toE_iff | exact GlobalTheory.StdRead.IdealDict.inId_toE_iff | (intros; apply GlobalTheory.StdRead.IdealDict.inId_toE_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedProjectionPreservesSchwartzAdmStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_projection_preserves_schwartz_adm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ), φ₀ ∈ SB (κ → Fv F v) → ∀ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ Φ ∈ schA F κ, GlobalTheory.MixedForm.proj v φ₀ l Φ ∈ schA F κ) ∧
      ∀ L ∈ (adeleClass F).adm κ, L ∘ₗ GlobalTheory.MixedForm.proj v φ₀ l ∈ (adeleClass F).adm κ := by
  first | exact @GlobalTheory.MixedForm.proj_schA_adm | exact GlobalTheory.MixedForm.proj_schA_adm | (intros; apply GlobalTheory.MixedForm.proj_schA_adm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicTemperedDistPoissonStatement
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_tempered_dist_poisson : ∀ (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ),
    (∀ k : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ, (∀ x, f' x = f (x + fun i => (k i : ℝ))) → T f' = T f) →
    (∀ m : Fin n → ℤ, ∀ f f' : SchwartzMap (Fin n → ℝ) ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * ((∑ i, (m i : ℝ) * x i : ℝ) : ℂ)) * f x) → T f' = T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = c * ∑' k : Fin n → ℤ, f (fun i => (k i : ℝ)) := by
  first | exact @GlobalTheory.IntComb.dirac_comb_unique | exact GlobalTheory.IntComb.dirac_comb_unique | (intros; apply GlobalTheory.IntComb.dirac_comb_unique <;> assumption)
end

