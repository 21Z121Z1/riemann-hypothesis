import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import ReciprocityTheory.ClassFieldTheory.GlobalClassField.Bundle0001
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0531
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0505
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbelianizationEqOfForallAbRestrictEq
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.GaloisAb

theorem abelianization_eq_of_forall_abRestrict_eq :
    ∀ (K : Type) [Field K] [NumberField K] (a b : Field.absoluteGaloisGroupAbelianization K),
      (∀ (L : IntermediateField K (AlgebraicClosure K)) (h : Neutral.B1.IsFiniteAbelian K L),
        Neutral.B1.abRestrict K L h a = Neutral.B1.abRestrict K L h b) → a = b := by
  intro K _ _ a b hab
  exact ReciprocityTheory.DiscreteGroups.GlobalClassField.abRestrict_ext hab

end GlobalTheory.CompanionTheory.GaloisAb
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsNormEqPrimesEquiv
section
open NumberField IsDedekindDomain GroundTheory.LocalField GroundTheory.Global
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.Rgads

theorem absNorm_eq_primesEquiv (p : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm p.asIdeal = (Rat.HeightOneSpectrum.primesEquiv p : ℕ) := by
  have e := Ideal.quotientEquiv p.asIdeal _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))
    (Rat.HeightOneSpectrum.span_natGenerator p)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_congr e.toEquiv]
  have := Ideal.absNorm_span_singleton ((Rat.HeightOneSpectrum.natGenerator p : ℕ) : ℤ)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
  rw [this]
  simp only [Algebra.norm_self, MonoidHom.id_apply, Int.natAbs_natCast]
  rfl

theorem e1b : faceMap_comp_succAbove_castSucc := by
  refine ⟨⟨Rat.HeightOneSpectrum.primesEquiv, fun v => (absNorm_eq_primesEquiv v).symm⟩,
    fun v μ h s => ?_⟩
  rw [localLFactor_of_isUnramified h, residueCard_adicCompletion]
  rfl

end GlobalTheory.CompanionTheory.Rgads
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicBoxCompactStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_box_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsCompact (boxF F 1) ∧ IsCompact (boxE F E 1) := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main | exact GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.BoxCpt.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicHaarSplitsAsArchTimesFiniteStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_splits_as_arch_times_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M n : ℕ) (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)), dx.IsAddHaarMeasure →
  ∃ (μ₁ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (μ₂ : Measure (Fin n → Fin M → Af F ⊗[F] E)) (c : ℝ≥0∞),
    μ₁.IsAddHaarMeasure ∧ μ₂.IsAddHaarMeasure ∧ SFinite μ₁ ∧ SFinite μ₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) ∧
    dx.map (fun X => (projInf X, projFin X)) = c • μ₁.prod μ₂ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple | exact GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.MapTup.map_tuple <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicNormRatVectorBound
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.MajHeight

theorem euclidNorm_le_sum {E : Type*} [NormedField E] (y : Fin 3 → E) :
    Reduction.euclidNorm y ≤ ∑ i, ‖y i‖ := by
  have h0 := norm_nonneg (y 0)
  have h1 := norm_nonneg (y 1)
  have h2 := norm_nonneg (y 2)
  rw [Reduction.euclidNorm, Fin.sum_univ_three, Fin.sum_univ_three]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h1 h2]

theorem infPart_le (y : Fin 3 → ℚ) :
    ∏ w : InfinitePlace ℚ, Reduction.euclidNorm (Reduction.infComp w (Reduction.ratVec y)) ^ w.mult
      ≤ ∑ i, |((y i : ℚ) : ℝ)| := by
  rw [Fintype.prod_unique,
    InfinitePlace.mult_isReal ⟨_, RationalIdeles.isReal_infinitePlace default⟩, pow_one]
  refine (euclidNorm_le_sum _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Reduction.infComp_ratVec]
  change ‖algebraMap ℚ (default : InfinitePlace ℚ).Completion (y i)‖ = _
  rw [eq_ratCast, InfinitePlace.Completion.Rat.norm_infinitePlace_completion]
  simp

theorem norm_intCast_le_one (v : HeightOneSpectrum (𝓞 ℚ)) (k : ℤ) :
    ‖Reduction.finComp v (Reduction.ratVec (fun _ : Fin 1 => (k : ℚ))) 0‖ ≤ 1 := by
  refine Reduction.norm_le_one_of_mem v ?_
  rw [Reduction.finComp_ratVec]
  refine (coe_mem_adicCompletionIntegers_iff v (k : ℚ)).2 ?_
  have h : (k : ℚ) = algebraMap (𝓞 ℚ) ℚ (k : 𝓞 ℚ) := by simp
  rw [h]
  exact HeightOneSpectrum.valuation_le_one v _

theorem finPart_le_one (y : Fin 3 → ℚ) (hy : ∀ i, ∃ k : ℤ, y i = k) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), ‖Reduction.finComp v (Reduction.ratVec y)‖ ≤ 1 := by
  have := finprod_induction (f := fun v : HeightOneSpectrum (𝓞 ℚ) =>
      ‖Reduction.finComp v (Reduction.ratVec y)‖) (fun x : ℝ => 0 ≤ x ∧ x ≤ 1)
    ⟨zero_le_one, le_rfl⟩
    (fun a b ha hb => ⟨mul_nonneg ha.1 hb.1, mul_le_one₀ ha.2 hb.1 hb.2⟩)
    (fun v => ⟨norm_nonneg _, (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      obtain ⟨k, hk⟩ := hy i
      have h := norm_intCast_le_one v k
      rw [Reduction.finComp_ratVec] at h
      rw [Reduction.finComp_ratVec, hk]
      exact h⟩)
  exact this.2

theorem adelicNorm_ratVec_le : ∀ M : ℕ, 0 < M → ∀ z : Fin 3 → ℚ,
    (∀ i, ∃ k : ℤ, (M : ℚ) * z i = k) →
    Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ]) ≤ M * ∑ i, |((z i : ℚ) : ℝ)| := by
  intro M hM z hz
  by_cases h0 : z = 0
  · subst h0
    have h := infPart_le (0 : Fin 3 → ℚ)
    have hnn : 0 ≤ ∏ w : InfinitePlace ℚ,
        Reduction.euclidNorm (Reduction.infComp w (Reduction.ratVec (0 : Fin 3 → ℚ))) ^ w.mult :=
      Finset.prod_nonneg fun _ _ => pow_nonneg (Reduction.euclidNorm_nonneg _) _
    have hz0 : ∏ w : InfinitePlace ℚ,
        Reduction.euclidNorm (Reduction.infComp w (Reduction.ratVec (0 : Fin 3 → ℚ))) ^ w.mult = 0 :=
      le_antisymm (by simpa using h) hnn
    rw [Reduction.adelicNorm, hz0, zero_mul]
    simp
  · have hc : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have hscale : Reduction.adelicNorm (Reduction.ratVec z : Fin 3 → 𝔸[ℚ]) =
        Reduction.adelicNorm (Reduction.ratVec ((M : ℚ) • z) : Fin 3 → 𝔸[ℚ]) := by
      rw [Reduction.ratVec_smul, Reduction.adelicNorm_smul_rat (Reduction.hasFiniteContent_ratVec h0) hc]
    rw [hscale, Reduction.adelicNorm]
    have hinf := infPart_le ((M : ℚ) • z)
    have hfin := finPart_le_one ((M : ℚ) • z) (fun i => by simpa using hz i)
    have hsum : ∑ i, |((((M : ℚ) • z) i : ℚ) : ℝ)| = M * ∑ i, |((z i : ℚ) : ℝ)| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [abs_mul]
    rw [← hsum]
    calc _ ≤ (∑ i, |((((M : ℚ) • z) i : ℚ) : ℝ)|) * 1 :=
          mul_le_mul hinf hfin (finprod_nonneg fun _ => norm_nonneg _)
            (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      _ = _ := mul_one _

end GlobalTheory.CompanionTheory.MajHeight
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicTensorRationalApproximationStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_tensor_rational_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ε : ℝ), 0 < ε → ∃ N : ℕ, 1 ≤ N ∧ ∀ b : AF F ⊗[F] E, ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧ ∃ c : E, (q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c ∈ boxE F E ε := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet | exact GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.Dirichlet.dirichlet <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicVectorIntegralProduct
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CutOff.Split

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def rowEquiv (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ) :
    (Fin k → InfiniteAdeleRing E) ≃ᵐ (Fin k → Cinf E) :=
  MeasurableEquiv.piCongrRight fun _ =>
    { toEquiv := (infEq E).symm.toEquiv
      measurable_toFun := (GlobalTheory.CuspRep.GASplit.continuous_infEq_symm E).measurable
      measurable_invFun := (continuous_infEq E).measurable }

theorem nuInf_eq (k : ℕ) :
    nuInf E k = (Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).map (rowEquiv E k) := rfl

theorem integral_split {k : ℕ} (A : (Fin k → Cinf E) → ℂ) (B : (Fin k → Af E) → ℂ) :
    ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) =
      (∫ x, A x ∂nuInf E k) * ∫ f, B f ∂nuFin E k := by
  have hmp := measurePreserving_arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)
    (fun _ => GroundTheory.Global.infiniteAdeleMeasure E) (fun _ => GroundTheory.Global.finiteAdeleMeasure E)
  haveI : SFinite (nuFin E k) := by unfold nuFin; infer_instance
  have e : (fun y : Fin k → Ad E => A (fun i => pInf E (y i)) * B (fun i => pFin E (y i))) =
      fun x => (A ∘ rowEquiv E k) ((MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)) x).1 *
        B ((MeasurableEquiv.arrowProdEquivProdArrow (InfiniteAdeleRing E) (Af E) (Fin k)) x).2 := by
    funext y
    rfl
  have h1 : ∫ y, A (fun i => pInf E (y i)) * B (fun i => pFin E (y i)) ∂vecMeasure E (Fin k) =
      ∫ z, (A ∘ rowEquiv E k) z.1 * B z.2 ∂((Measure.pi fun _ : Fin k => GroundTheory.Global.infiniteAdeleMeasure E).prod
        (nuFin E k)) := by
    rw [e]
    exact (hmp.integral_comp (MeasurableEquiv.measurableEmbedding _)
      (fun z => (A ∘ rowEquiv E k) z.1 * B z.2))
  rw [h1, integral_prod_mul, nuInf_eq, integral_map_equiv]
  rfl

end GlobalTheory.CompanionTheory.CutOff.Split
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCharacterInv
section
noncomputable section

open Ad3 Ad3.S
open GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)

namespace GlobalTheory.CompanionTheory.AdjointLift

theorem localChar_inv (c : HeckeCharacter ℚ) (v : Pl) :
    localChar c⁻¹ v = (localChar c v)⁻¹ := by
  ext a
  rfl

theorem admissible_character_inv {D : Dat} {c : HeckeCharacter ℚ} {δ : Bool} {S : Finset Pl} (h : admitted D c δ S) :
    admitted D c⁻¹ δ S where
  fin := h.fin.inv
  sgn w := by
    have e : (((c⁻¹).infiniteComponent w (-1) : Circle) : ℂ) =
        (((c.infiniteComponent w (-1))⁻¹ : Circle) : ℂ) := rfl
    rw [e, Circle.coe_inv, h.sgn w]
    split_ifs <;> simp
  bad := h.bad
  unr v hv := by
    rw [localChar_inv]
    exact isUnramifiedChar_inv_iff.2 (h.unr v hv)

theorem cont_zero {D : Dat} {c : HeckeCharacter ℚ} {S : Finset Pl} {Λ : ℂ → ℂ}
    (h : Cont D c S 1 Λ) (h1 : Λ 1 = 0) : Cont D c S 0 (dslope Λ 1) := by
  obtain ⟨hd, ho, he⟩ := h
  have hopen : IsOpen {s : ℂ | 1 / 4 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : {s : ℂ | 1 / 4 < s.re} ∈ nhds (1 : ℂ) := hopen.mem_nhds (by norm_num)
  have hd0 := (Complex.differentiableOn_dslope hmem).2 hd
  have hmul : ∀ s : ℂ, (s - 1) * dslope Λ 1 s = Λ s := fun s => by
    simpa [h1] using sub_smul_dslope Λ 1 s
  refine ⟨hd0, ?_, ?_⟩
  · intro b
    obtain ⟨C, hC⟩ := ho b
    have hsub : Metric.closedBall (1 : ℂ) (1 / 2) ⊆ {s : ℂ | 1 / 4 < s.re} := by
      intro s hs
      have h2 : ‖s - 1‖ ≤ 1 / 2 := by simpa [dist_eq_norm] using hs
      have h3 := (abs_le.1 ((Complex.abs_re_le_norm (s - 1)).trans h2)).1
      simp only [Complex.sub_re, Complex.one_re] at h3
      simp only [Set.mem_setOf_eq]
      linarith
    obtain ⟨K, hK⟩ := (isCompact_closedBall (1 : ℂ) (1 / 2)).exists_bound_of_continuousOn
      (hd0.continuousOn.mono hsub)
    refine ⟨2 * |C| + |K|, fun s hs1 hs2 => ?_⟩
    have hC0 : 0 ≤ |C| := abs_nonneg C
    have hK0 : 0 ≤ |K| := abs_nonneg K
    have hE : 1 ≤ Real.exp ((2 * |C| + |K|) * s.im ^ 2) :=
      Real.one_le_exp (by positivity)
    by_cases hs : ‖s - 1‖ ≤ 1 / 2
    · have hb : ‖dslope Λ 1 s‖ ≤ K := hK s (by simpa [dist_eq_norm] using hs)
      have hb2 : K ≤ 2 * |C| + |K| := (le_abs_self K).trans (by linarith)
      exact (hb.trans hb2).trans (le_mul_of_one_le_right (by positivity) hE)
    · push_neg at hs
      have hn : ‖s - 1‖ * ‖dslope Λ 1 s‖ = ‖Λ s‖ := by rw [← norm_mul, hmul]
      have hb := hC s hs1 hs2
      have hexp : Real.exp (C * s.im ^ 2) ≤ Real.exp ((2 * |C| + |K|) * s.im ^ 2) := by
        apply Real.exp_le_exp.2
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have := le_abs_self C
        linarith
      have hb2 : ‖Λ s‖ ≤ |C| * Real.exp ((2 * |C| + |K|) * s.im ^ 2) :=
        hb.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le).trans
          (mul_le_mul_of_nonneg_left hexp hC0))
      have hh : 1 / 2 * ‖dslope Λ 1 s‖ ≤ ‖Λ s‖ := by
        rw [← hn]
        exact mul_le_mul_of_nonneg_right hs.le (norm_nonneg _)
      have hpos := Real.exp_pos ((2 * |C| + |K|) * s.im ^ 2)
      have : |K| * Real.exp ((2 * |C| + |K|) * s.im ^ 2) ≥ 0 := by positivity
      nlinarith
  · intro s hs
    have hne : s - 1 ≠ 0 := by
      intro h0
      have : s = 1 := sub_eq_zero.1 h0
      rw [this] at hs
      simp at hs
    apply mul_left_cancel₀ hne
    rw [hmul, he s hs]
    ring

theorem anOf : AnOf := by
  intro a D hFE hEx
  by_cases hd : Dih a
  · exact Or.inl hd
  refine Or.inr fun c δ S hA => ?_
  have hA' := admissible_character_inv hA
  obtain ⟨Λ, hΛ⟩ := hEx c δ S hA
  obtain ⟨Λ', hΛ'⟩ := hEx c⁻¹ δ S hA'
  obtain ⟨hfe, h1⟩ := hFE c δ S hA Λ Λ' hΛ hΛ'
  obtain ⟨-, h1'⟩ := hFE c⁻¹ δ S hA' Λ' Λ hΛ' (by rwa [inv_inv])
  have h1 := h1.resolve_left hd
  have h1' := h1'.resolve_left hd
  refine ⟨dslope Λ 1, dslope Λ' 1, cont_zero hΛ h1, cont_zero hΛ' h1', fun s hs1 hs2 => ?_⟩
  have e := hfe s hs1 hs2
  have e1 : Λ s = (s - 1) * dslope Λ 1 s := by
    simpa [h1] using (sub_smul_dslope Λ 1 s).symm
  have e2 : Λ' (1 - s) = -s * dslope Λ' 1 (1 - s) := by
    simpa [h1'] using (sub_smul_dslope Λ' 1 (1 - s)).symm
  have hs0 : s ≠ 0 := by
    rintro rfl
    norm_num at hs1
  have hs1' : s - 1 ≠ 0 := by
    intro h0
    have : s = 1 := sub_eq_zero.1 h0
    rw [this] at hs2
    norm_num at hs2
  rw [e1, e2] at e
  apply mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.2 hs0) hs1')
  linear_combination e

end GlobalTheory.CompanionTheory.AdjointLift

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterInCoordinates
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem half_trace_eq (σ : E →ₐ[F] E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (h : IsCoord σ e τ Θ)
    (he : ∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) (z : Ainf F ⊗[F] E) (w : InfinitePlace F) :
    e (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w = (Θ z w).re := by
  have h4 := h.2.2.2 z w
  have h5 : e (Algebra.trace (Ainf F) (Ainf F ⊗[F] E) z) w = 2 * (Θ z w).re := by
    have := congrArg Complex.re h4
    simp only [Complex.ofReal_re, Complex.add_re, Complex.conj_re] at this
    rw [this]; ring
  rw [map_mul, Pi.mul_apply, he, h5, map_div₀, map_one, map_ofNat]
  ring

def evC (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (w : InfinitePlace F) : Ainf F ⊗[F] E →+* ℂ :=
  (Pi.evalRingHom (fun _ : InfinitePlace F => ℂ) w).comp (Θ : Ainf F ⊗[F] E →+* (InfinitePlace F → ℂ))

theorem evC_apply (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (w : InfinitePlace F) (z : Ainf F ⊗[F] E) :
    evC Θ w z = Θ z w := rfl

theorem coord_gramR (σ : E →ₐ[F] E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (τ : InfinitePlace F → (E →+* ℂ)) (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) (h : IsCoord σ e τ Θ)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) :
    matC Θ (gramR (Ainf F) σ J X) w = gramC (J.map (τ w)) (tupC Θ X w) := by
  ext a c
  change evC Θ w (Formalism.UG.hform (sigR (Ainf F) σ) (JR (Ainf F) J) (X a) (X c)) = _
  simp only [Formalism.UG.hform, map_sum, map_mul, gramC, tupC, evC_apply, h.2.1, JR, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show inclR (Ainf F) (J i j) = (1 : Ainf F) ⊗ₜ[F] (J i j) from rfl, h.2.2.1]

theorem coord_trace_mul (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)) {n : ℕ}
    (B G : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (w : InfinitePlace F) :
    Θ (Matrix.trace (B * G)) w = Matrix.trace (matC Θ B w * matC Θ G w) := by
  change evC Θ w _ = _
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]
  rfl

theorem gramC_smul {n M : ℕ} (c : ℂ) (J : Matrix (Fin M) (Fin M) ℂ) (X : Fin n → Fin M → ℂ) :
    gramC (c • J) X = c • gramC J X := by
  ext a b
  simp only [gramC, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem psiInf_phase : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) →
  ∀ (a : F) (ψ : AddChar (AF F) ℂ),
  (∀ x : Ainf F, ψ (pairA F x 0) = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, ρ w a * e x w : ℝ) : ℂ))) →
  ∀ (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))
    (X : Fin n → Fin M → Ainf F ⊗[F] E),
  psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
      (Matrix.trace (B * gramR (Ainf F) σ J X))) =
    Complex.exp (2 * Real.pi * Complex.I * ((phaseM (fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w))
      (fun w => matC Θ B w) (tupC Θ X) : ℝ) : ℂ)) := by
  intro F E _ _ _ _ _ σ ρ e τ Θ h he a ψ hψ M n J B X
  change ψ (pairA F _ 0) = _
  rw [hψ]
  congr 3
  rw [phaseM]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [half_trace_eq σ ρ e τ Θ h he, coord_trace_mul, coord_gramR σ e τ Θ h, gramC_smul,
    Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.PhaseCoord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCharacterRealPairing
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.JSPair

def dotL (E : Type) [Field E] [NumberField E] (k : ℕ) :
    (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] Cinf E :=
  ∑ i : Fin k, (ContinuousLinearMap.mul ℝ (Cinf E)).bilinearComp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => Cinf E) i)

theorem dotL_apply {E : Type} [Field E] [NumberField E] {k : ℕ} (x z : Fin k → Cinf E) :
    dotL E k x z = ∑ i, x i * z i := by
  simp [dotL, ContinuousLinearMap.sum_apply]

theorem exists_pairing : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} {ψ : AddChar (Ad E) ℂ}, S8 → StdPsi ψ → ∃ β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ, (∀ y, (∀ x, β x y = 0) → y = 0) ∧ ∀ x z : Fin k → Cinf E, ψ (sInf E (∑ i, x i * z i)) = Complex.exp (-((β x z : ℝ) : ℂ) * Complex.I) := by
  intro E _ _ _ k ψ h8 hψ
  obtain ⟨l, hl⟩ := h8 (InfinitePlace E) (GlobalTheory.CompanionTheory.JSInfStep.chiInf ψ)
    (hψ.cont.comp GlobalTheory.CompanionTheory.JSInfStep.continuous_sInf) (fun z => hψ.norm _)
  let β : (Fin k → Cinf E) →L[ℝ] (Fin k → Cinf E) →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ (Fin k → Cinf E) (Cinf E) ℝ (-l)) ∘L dotL E k
  have hβ : ∀ x z, β x z = -l (∑ i, x i * z i) := fun x z => by
    simp [β, dotL_apply]
  refine ⟨β, fun y hy => ?_, fun x z => ?_⟩
  · funext i
    refine GlobalTheory.CompanionTheory.JSInfStep.chiInf_nondeg hψ (y i) fun w => ?_
    have h0 := hy (Pi.single i w)
    rw [hβ] at h0
    have e : ∑ j, (Pi.single i w : Fin k → Cinf E) j * y j = y i * w := by
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, mul_comm]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, zero_mul]
      · simp
    rw [e] at h0
    have h1 : l (y i * w) = 0 := neg_eq_zero.1 h0
    rw [hl, h1]
    simp
  · have := hl (∑ i, x i * z i)
    rw [GlobalTheory.CompanionTheory.JSInfStep.chiInf_apply] at this
    rw [this, hβ]
    simp

end GlobalTheory.CompanionTheory.JSPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMultiplierTemperateStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_multiplier_temperate : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (α : D.host.F) (V : HSp D) (a : HermE D r), ∃ q : (D.what₂.Tau → Fin V.rank → Fin r → ℂ) → ℂ, q.HasTemperateGrowth ∧ ∀ y, ((multM θ α V a y : ℝ) : ℂ) = q (fun τ i j => compAt θ τ y i j) := by
  first | exact @GlobalTheory.CompanionTheory.WSum.multM_tempered | exact GlobalTheory.CompanionTheory.WSum.multM_tempered | (intros; apply GlobalTheory.CompanionTheory.WSum.multM_tempered <;> assumption)
end

