import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0768
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Formalism.PieriBlockIdeals.StatementE
import Formalism.PieriBlockIdeals.Bundle0007
import Formalism.PieriBlockIdeals.PieriColumnMinors.RecursionInclusionExceptional
import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlTieOfInertCore

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentsAdeleUnitCombination
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.PickUnit

variable {F : Type} [Field F] [NumberField F]

def compInf (w : InfinitePlace F) : AF F →+* w.Completion :=
  (Pi.evalRingHom (fun u : InfinitePlace F => u.Completion) w).comp (RingHom.fst _ _)

def compFin (v : HeightOneSpectrum (𝓞 F)) : AF F →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v).comp
    (RingHom.snd _ _)

theorem ext_comp {a b : AF F} (h1 : ∀ w, compInf w a = compInf w b) (h2 : ∀ v, compFin v a = compFin v b) :
    a = b :=
  Prod.ext (funext h1) (Subtype.ext (funext h2))

theorem isUnit_of_comp {a : AF F} (h1 : ∀ w, compInf w a ≠ 0) (h2 : ∀ v, compFin v a ≠ 0)
    (h3 : ∀ᶠ v in Filter.cofinite, Valued.v (compFin v a) = 1) : IsUnit a :=
  Prod.isUnit_iff.2 ⟨Pi.isUnit_iff.2 fun w => isUnit_iff_ne_zero.2 (h1 w), FiniteAdeleRing.isUnit_iff.2 ⟨h2, h3⟩⟩

variable {ι : Type} [DecidableEq ι]

def ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι) : AF F :=
  ((fun w => if a w = i then 1 else 0),
    ⟨fun v => if b v = i then 1 else 0, Filter.Eventually.of_forall fun v => by
      by_cases h : b v = i
      · simp only [h, if_true]; exact one_mem _
      · simp only [h, if_false]; exact zero_mem _⟩)

theorem compInf_ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι) (w : InfinitePlace F) :
    compInf w (ind a b i) = if a w = i then 1 else 0 := rfl

theorem compFin_ind (a : InfinitePlace F → ι) (b : HeightOneSpectrum (𝓞 F) → ι) (i : ι)
    (v : HeightOneSpectrum (𝓞 F)) : compFin v (ind a b i) = if b v = i then 1 else 0 := rfl

end GlobalTheory.QSA.PickUnit

open GlobalTheory.QSA.PickUnit in

theorem GlobalTheory.QSA.exists_idem_pick_unit : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (n u : ι → AF F), IsUnit (∑ i, u i * n i) → ∃ η : ι → AF F, (∀ i, η i * η i = η i) ∧
      (∀ i j, i ≠ j → η i * η j = 0) ∧ ∑ i, η i = 1 ∧ IsUnit (∑ i, η i * n i) := by
  intro F _ _ ι _ n u hs
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · rw [Finset.univ_eq_empty, Finset.sum_empty] at hs
    refine ⟨fun _ => 0, fun i => isEmptyElim i, fun i => isEmptyElim i, ?_, ?_⟩
    · rw [Finset.univ_eq_empty, Finset.sum_empty]; exact isUnit_zero_iff.1 hs
    · rw [Finset.univ_eq_empty, Finset.sum_empty]; exact hs
  have hinf : ∀ w, ∃ i, compInf w (n i) ≠ 0 := by
    intro w
    by_contra h
    push_neg at h
    apply (hs.map (compInf w)).ne_zero
    rw [map_sum]
    exact Finset.sum_eq_zero fun i _ => by rw [map_mul, h i, mul_zero]
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), ∃ i, ∀ j, Valued.v (compFin v (n j)) ≤ Valued.v (compFin v (n i)) := by
    intro v
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => Valued.v (compFin v (n j)))
      ⟨i₀, Finset.mem_univ _⟩
    exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩
  choose a ha using hinf
  choose b hb using hfin
  refine ⟨ind a b, ?_, ?_, ?_, ?_⟩
  · intro i
    apply ext_comp
    · intro w; rw [map_mul, compInf_ind]; split_ifs <;> simp
    · intro v; rw [map_mul, compFin_ind]; split_ifs <;> simp
  · intro i j hij
    apply ext_comp
    · intro w; rw [map_mul, map_zero, compInf_ind, compInf_ind]
      by_cases h1 : a w = i
      · rw [if_pos h1, if_neg (fun h2 => hij (h1.symm.trans h2)), mul_zero]
      · rw [if_neg h1, zero_mul]
    · intro v; rw [map_mul, map_zero, compFin_ind, compFin_ind]
      by_cases h1 : b v = i
      · rw [if_pos h1, if_neg (fun h2 => hij (h1.symm.trans h2)), mul_zero]
      · rw [if_neg h1, zero_mul]
  · apply ext_comp
    · intro w; rw [map_sum, map_one]; simp only [compInf_ind]; rw [Finset.sum_ite_eq]; simp
    · intro v; rw [map_sum, map_one]; simp only [compFin_ind]; rw [Finset.sum_ite_eq]; simp
  · have hcInf : ∀ w, compInf w (∑ i, ind a b i * n i) = compInf w (n (a w)) := by
      intro w
      rw [map_sum, Finset.sum_eq_single (a w)]
      · rw [map_mul, compInf_ind, if_pos rfl, one_mul]
      · intro j _ hj; rw [map_mul, compInf_ind, if_neg (Ne.symm hj), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hcFin : ∀ v, compFin v (∑ i, ind a b i * n i) = compFin v (n (b v)) := by
      intro v
      rw [map_sum, Finset.sum_eq_single (b v)]
      · rw [map_mul, compFin_ind, if_pos rfl, one_mul]
      · intro j _ hj; rw [map_mul, compFin_ind, if_neg (Ne.symm hj), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    apply isUnit_of_comp
    · intro w; rw [hcInf]; exact ha w
    · intro v h0
      rw [hcFin] at h0
      apply (hs.map (compFin v)).ne_zero
      rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      have h := hb v j
      rw [h0, map_zero] at h
      rw [map_mul, (Valuation.zero_iff _).1 (le_antisymm h zero_le'), mul_zero]
    · have hsu := (FiniteAdeleRing.isUnit_iff.1 (hs.map (RingHom.snd (InfiniteAdeleRing F) (Af F)))).2
      have hint : ∀ᶠ v in Filter.cofinite, ∀ j,
          Valued.v (compFin v (u j)) ≤ 1 ∧ Valued.v (compFin v (n j)) ≤ 1 := by
        refine Filter.eventually_all.2 fun j => ?_
        filter_upwards [(u j).2.2, (n j).2.2] with v h1 h2
        exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 h1,
          (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v).1 h2⟩
      filter_upwards [hsu, hint] with v hv1 hv2
      rw [hcFin]
      refine le_antisymm (hv2 _).2 ?_
      have hv1' : Valued.v (compFin v (∑ i, u i * n i)) = 1 := hv1
      rw [← hv1', map_sum]
      refine Valuation.map_sum_le _ fun j _ => ?_
      rw [map_mul, map_mul]
      exact (mul_le_of_le_one_left zero_le' (hv2 j).1).trans (hb v j)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsTranslationFamilyChartsThickenings
section
open CategoryTheory TopologicalSpace TensorProduct
open GlobalTheory.AnPer

namespace GlobalTheory.AnPer

set_option maxHeartbeats 1000000 in

theorem exists_points_on_DObj : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (et : Hol F₀.V →ₐ[ℂ] R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (ρ : ∀ k, Hol (K.W (ka k)) →+* R ⊗[ℂ] Hol (K₀.W k)), (∀ k f, ρ k (K.cst (ka k) f) = θ f ⊗ₜ[ℂ] 1) → (∀ k a h, ρ k (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ k h)) → (∀ l k' k (h : K₀.le l k' k), Close (M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k'))) ((ρ k').comp (Charts.sh (hka h))) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h)).toRingHom.comp (ρ k))) → ∀ (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)), (∀ k h, ρ k h - 1 ⊗ₜ[ℂ] res k h ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k))) → ∃ ρ' : ∀ S : K₀.DObj (et : Hol F₀.V →+* R) M, Hol (K.W (ka S.T.k)) →+* S.T.C, (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) ∧ (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) ∧ ∀ (S S' : K₀.DObj (et : Hol F₀.V →+* R) M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)) := by
  intro I _ g Λ _ F F₀ K K₀ R _ _ et M θ ka hka ρ hc hd hs res hr
  choose ψ hψ using GlobalTheory.T.exists_tensorLift_of_analyticThickening K₀ et M
  have h1 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (d : R), ψ S (d ⊗ₜ[ℂ] 1) = algebraMap R S.T.C d :=
    fun S d ↦ (hψ S d 1).trans (by rw [S.T.ρ.map_one, mul_one])
  have h2 : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M) (h : Hol (K₀.W S.T.k)), ψ S (1 ⊗ₜ[ℂ] h) = S.T.ρ h :=
    fun S h ↦ (hψ S 1 h).trans (by rw [(algebraMap R S.T.C).map_one, one_mul])
  have hJ : ∀ (S : K₀.DObj (et : Hol F₀.V →+* R) M),
      ∀ c ∈ M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)), ψ S c ∈ S.T.J := by
    intro S c hc
    have : M.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)) ≤ S.T.J.comap (ψ S) := by
      refine Ideal.map_le_iff_le_comap.2 fun d hd ↦ ?_
      change ψ S (d ⊗ₜ[ℂ] 1) ∈ S.T.J
      rw [h1]
      exact S.mem d hd
    exact this hc
  refine ⟨fun S ↦ (ψ S).comp (ρ S.T.k), fun S f ↦ ?_, fun S h ↦ ?_, fun S S' f ↦ ?_⟩
  · exact (congrArg (ψ S) (hc _ f)).trans (h1 S _)
  · have := hJ S _ (hr S.T.k h)
    rw [(ψ S).map_sub, h2] at this
    exact this
  · have c1 := (hs _ _ _ (Charts.Hom.le f.1)).map (ψ S') (hJ S')
    have c2 := GlobalTheory.T.close_comp_of_close_includeRight S'.T.J (ρ S.T.k) (hd S.T.k)
      ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1))).toRingHom)
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S))
      (fun d ↦ by
        have e : Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA (Charts.Hom.le f.1)) (d ⊗ₜ[ℂ] 1) = d ⊗ₜ[ℂ] 1 :=
          (Algebra.TensorProduct.map_tmul _ _ _ _).trans
            (congrArg (fun x ↦ d ⊗ₜ[ℂ] x) (Charts.shA (Charts.Hom.le f.1)).map_one)
        exact (congrArg (ψ S') e).trans ((h1 S' d).trans ((f.2 d).symm.trans (congrArg f.1.φ (h1 S d).symm))))
      (by
        have e1 : ((ψ S').comp (Algebra.TensorProduct.map (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1))).toRingHom).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            S'.T.ρ.comp (Charts.sh (Charts.Hom.le f.1)) :=
          RingHom.ext fun h ↦ (congrArg (ψ S') (Algebra.TensorProduct.map_tmul (AlgHom.id ℂ R)
            (Charts.shA (Charts.Hom.le f.1)) 1 h)).trans (h2 S' _)
        have e2 : ((f.1.φ : S.T.C →+* S'.T.C).comp (ψ S)).comp
            (Algebra.TensorProduct.includeRight : Hol (K₀.W S.T.k) →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W S.T.k)).toRingHom =
            (f.1.φ : S.T.C →+* S'.T.C).comp S.T.ρ :=
          RingHom.ext fun h ↦ congrArg f.1.φ (h2 S h)
        rw [e1, e2]
        exact f.1.close)
    exact Relation.ReflTransGen.trans c1 c2

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPureQuaternionSqOfAdelic
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.PureSq

theorem mul_self_of_re_eq_zero {R : Type*} [CommRing R] {a b : R} (p : ℍ[R, a, b]) (hp : p.re = 0) :
    p * p = algebraMap R ℍ[R, a, b] (a * p.imI ^ 2 + b * p.imJ ^ 2 - a * b * p.imK ^ 2) := by
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, hp] <;> ring

theorem exists_completion_hom_of_real {K : Type} [Field K] (σ : K →+* ℝ) :
    ∃ (w : InfinitePlace K) (f : w.Completion →+* ℝ), ∀ x : K, f (algebraMap K w.Completion x) = σ x := by
  have hφ : ComplexEmbedding.IsReal (Complex.ofRealHom.comp σ) := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp
  have hw : (InfinitePlace.mk (Complex.ofRealHom.comp σ)).IsReal := InfinitePlace.isReal_mk_iff.2 hφ
  refine ⟨_, InfinitePlace.Completion.extensionEmbeddingOfIsReal hw, fun x => ?_⟩
  have he := InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw
    ((WithAbs.equiv _).symm x)
  refine Eq.trans he ?_
  apply Complex.ofReal_injective
  rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_mk_eq_of_isReal hφ]
  simp

variable {F : Type} [Field F] [NumberField F]

theorem isotropic_of_ringHom {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c))
    {k : Type*} [Field k] (φ : AF F →+* k) (ψ : F →+* k)
    (hφ : ∀ x, φ (algebraMap F (AF F) x) = ψ x) :
    ∃ x : Fin 4 → k, x ≠ 0 ∧ ∑ i, ψ (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 := by
  rw [mul_self_of_re_eq_zero q hq0] at hqq
  have h1 := congrArg QuaternionAlgebra.re hqq
  simp only [QuaternionAlgebra.algebraMap_eq, QuaternionAlgebra.re_coe] at h1
  have h2 := congrArg φ h1
  simp only [map_add, map_sub, map_mul, map_pow, hφ] at h2
  refine ⟨![φ q.imI, φ q.imJ, φ q.imK, 1], fun h => by simpa using congrFun h 3, ?_⟩
  simp [Fin.sum_univ_four]
  linear_combination h2

end GlobalTheory.QSA.PureSq

namespace GlobalTheory.QSA.PureSq

variable {F : Type} [Field F] [NumberField F]

theorem isotropic_real {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c)) (σ : F →+* ℝ) :
    ∃ x : Fin 4 → ℝ, x ≠ 0 ∧ ∑ i, σ (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 := by
  obtain ⟨w, f, hf⟩ := exists_completion_hom_of_real σ
  refine isotropic_of_ringHom q hq0 hqq
    (f.comp ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)) σ
    (fun x => ?_)
  rw [← hf x]
  rfl

theorem isotropic_finite {a b c : F} (q : DA F a b) (hq0 : q.re = 0)
    (hqq : q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x : Fin 4 → v.adicCompletion F, x ≠ 0 ∧
      ∑ i, algebraMap F (v.adicCompletion F) (![a, b, -(a * b), -c] i) * x i ^ 2 = 0 :=
  isotropic_of_ringHom q hq0 hqq ((evalV F v).comp (sndA F)).toRingHom (algebraMap F _)
    (fun x => ((evalV F v).comp (sndA F)).commutes x)

theorem exists_ternary_eq {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) {u₁ u₂ u₃ : F}
    (hu : (u₁, u₂, u₃) ≠ (0, 0, 0)) (h : a * u₁ ^ 2 + b * u₂ ^ 2 - a * b * u₃ ^ 2 = 0) (c : F) :
    ∃ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c := by
  have key : ∀ v₁ v₂ v₃ : F, a * u₁ * v₁ + b * u₂ * v₂ - a * b * u₃ * v₃ ≠ 0 →
      ∃ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c := by
    intro v₁ v₂ v₃ hD
    set D := a * u₁ * v₁ + b * u₂ * v₂ - a * b * u₃ * v₃ with hDdef
    set t := (c - (a * v₁ ^ 2 + b * v₂ ^ 2 - a * b * v₃ ^ 2)) / (2 * D) with ht
    have h2 : (2 : F) * D ≠ 0 := mul_ne_zero two_ne_zero hD
    have ht' : t * (2 * D) = c - (a * v₁ ^ 2 + b * v₂ ^ 2 - a * b * v₃ ^ 2) := div_mul_cancel₀ _ h2
    refine ⟨t * u₁ + v₁, t * u₂ + v₂, t * u₃ + v₃, ?_⟩
    linear_combination t ^ 2 * h + ht'
  by_cases h1 : u₁ = 0
  · by_cases h2 : u₂ = 0
    · have h3 : u₃ ≠ 0 := fun h3 => hu (by simp [h1, h2, h3])
      exact key 0 0 1 (by simp [ha, hb, h3])
    · exact key 0 1 0 (by simp [hb, h2, h1])
  · exact key 1 0 0 (by simp [ha, h1])

theorem exists_rat_of_adelic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 →
    ∀ q : DA F a b, q.re = 0 → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) →
    ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
  intro F _ _ a b ha hb c hc q hq0 hqq
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.LocalQuad.isotropic_of_locally_isotropic GlobalTheory.QNorm.hasseNormSt F
    (ι := Fin 4) (by simp) ![a, b, -(a * b), -c]
    (fun i => by fin_cases i <;> simp [ha, hb, hc])
    (isotropic_real q hq0 hqq) (isotropic_finite q hq0 hqq)
  simp [Fin.sum_univ_four] at hx
  have pure : ∀ y₁ y₂ y₃ : F, a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2 = c →
      ∃ p : ℍ[F, a, b], p.re = 0 ∧ p * p = algebraMap F ℍ[F, a, b] c := by
    intro y₁ y₂ y₃ hy
    refine ⟨⟨0, y₁, y₂, y₃⟩, rfl, ?_⟩
    rw [mul_self_of_re_eq_zero _ rfl]
    change algebraMap F ℍ[F, a, b] (a * y₁ ^ 2 + b * y₂ ^ 2 - a * b * y₃ ^ 2) = _
    rw [hy]
  by_cases h3 : x 3 = 0
  · rw [h3] at hx
    obtain ⟨y₁, y₂, y₃, hy⟩ := exists_ternary_eq ha hb (u₁ := x 0) (u₂ := x 1) (u₃ := x 2)
      (fun h => hx0 (by
        simp only [Prod.mk.injEq] at h
        funext i; fin_cases i <;> simp [h.1, h.2.1, h.2.2, h3]))
      (by linear_combination hx) c
    exact pure y₁ y₂ y₃ hy
  · refine pure (x 0 / x 3) (x 1 / x 3) (x 2 / x 3) ?_
    field_simp
    linear_combination hx

end GlobalTheory.QSA.PureSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationClosedChartsSubordinateToCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translationClosed_charts_subordinate_to_cover : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ {N : Type} (𝒰 : N → X.Opens), ⨆ i, 𝒰 i = ⊤ → ∃ (K : Charts F) (r : Real K s σ) (j : K.K → N), K.Rich ∧ (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') ∧ r.IsFor u ∧ ∀ k, ⊤ ≤ r.x k ⁻¹ᵁ 𝒰 (j k) := by
  first | exact @GlobalTheory.AnPer.exists_charts_subordinate | exact GlobalTheory.AnPer.exists_charts_subordinate | (intros; apply GlobalTheory.AnPer.exists_charts_subordinate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringComplexOverPrimeStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_complex_restrict_eq_at_prime : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)), ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by
  first | exact @GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime | exact GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime | (intros; apply GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentOfRecordVsFormulas
section
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem exponent_of_record_vs_formulas :
    Formalism.CohomologicalDescent.E.ExCut → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
      ∀ l : ℕ, l.Prime → (¬ W.WRange P l → W.JA P l ≤ W.Jrec7 P l) ∧ (W.WRange P l → W.coarseWeightBound P l = W.Jrec7 P l) := by
  intro hC P hH hL ι _ _ W hW l hl
  refine ⟨fun hR => ?_, fun hR => ?_⟩
  · by_cases hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp
    · rw [seventh_recursion_eq_a_of_small_prime W P l hc]
    · have h1 : P.lJ < (l : ℝ) := not_le.mp fun h => hc (Or.inl h)
      have h2 : ¬ P.Excl l := fun h => hc (Or.inr (Or.inl h))
      have h3 : l ∉ W.Sp := fun h => hc (Or.inr (Or.inr h))
      have hh : P.h < (l : ℝ) := not_le.mp fun h => hR ⟨h1, h, h2, h3⟩
      have hb := Formalism.CohomologicalDescent.E.beyond_height_exceptional (Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut hC) hC P hH hL ι W hW l hl h1 hh
      rw [hb.2.1]
      exact Nat.zero_le _
  · obtain ⟨h1, _, h2, h3⟩ := hR
    have hc : ¬ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) := by
      rintro (h | h | h)
      · exact absurd h (not_le.mpr h1)
      · exact h2 h
      · exact h3 h
    rw [seventh_recursion_eq_w_of_large_prime W P l hc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePeriodEqFamilyPeriodValue
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem period_fibre_eq_value : PFix := by
  intro I _ g Λ _ F B _ 𝒜 _ h𝒜 σ e z hz y hy A _ hA φ m L u hE τ hτ P hP c per hper l
  let u' : Unif (⟨(fibFam u).V, (fibFam u).τ.comp τ, fun l ↦ (fibFam u).hol (τ l)⟩ : Fam Empty g Λ)
      (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V)) :=
    { E := (fibUnif u).E
      w := (fibUnif u).w
      per := fun l p hp ↦ (fibUnif u).per (τ l) p hp
      hol := (fibUnif u).hol }
  have h1 := GlobalTheory.T.period_comp_translationGroup_hom (fibUnif u) τ u' rfl _ _ (hP (m.pull c))
  have h2 := GlobalTheory.AnPer.isPeriod_pull1_eq_comap u' e (GlobalTheory.abelianScheme_left_isSeparated_of_affine A hA)
    (GlobalTheory.abelianScheme_left_isSeparated_of_affine 𝒜 h𝒜) (fun _ ↦ z) analyticOnNhd_const (fun _ _ ↦ hz)
    LinearMap.id (AddMonoidHom.id Λ) (fun l _ _ ↦ (hτ l).symm) y φ m.isMor
    (fun x ↦ Hol.ext_fn fun p hp ↦ by rw [Hol.fn_algebraMap _ hp, Hol.fn_comap _ _ _ _ hp, hy])
    (fun p _ ↦ (hE p.2).symm) c.1 per _ hper h1 l
  have hp : (0 : Empty → ℂ) ∈ (fibFam u).V := trivial
  have h3 := congrArg (fun f ↦ Hol.fn f 0) h2
  simp only [Hol.fn_comap _ _ _ _ hp] at h3
  exact (Hol.fn_algebraMap _ hp).symm.trans h3

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowerEmbedding
section
open NumberField IsDedekindDomain IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.DegreeFormula

set_option linter.style.haveILetI false

namespace GlobalTheory.FrobEmb

theorem exists_frob_all (E : Type) [Field E] [NumberField E] [IsGalois ℚ E]
    (hc : ∀ a b : E ≃ₐ[ℚ] E, a * b = b * a) (p : ℕ) (hp : p.Prime) :
    ∃ σ : E ≃ₐ[ℚ] E, ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ σ P := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 E)) := inferInstance
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(p : ℤ)}) (by simpa using hp.ne_zero) P
  haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (E ≃ₐ[ℚ] E) P
  refine ⟨σ, fun Q _ _ => ?_⟩
  obtain ⟨t, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)
  have := hσ.conj t
  rwa [hc t σ, mul_inv_cancel_right] at this

theorem frobenius_comp (E : Type) [Field E] [NumberField E] (p : ℕ) [hp : Fact p.Prime]
    (k : Type) [Field k] [CharP k p] [PerfectRing k p] (hu : ¬ p ∣ (discr E).natAbs) (σ : E ≃ₐ[ℚ] E)
    (hσ : ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ σ P)
    (τ : E →+* FractionRing (WittVector p k)) (x : E) :
    WittVector.FractionRing.frobenius p k (τ x) = τ (σ x) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp.out
  have hirr : Irreducible (p : WittVector p k) := WittVector.irreducible p
  have hm : ∀ y : WittVector p k, y ∈ maximalIdeal (WittVector p k) ↔ WittVector.constantCoeff y = 0 := fun y => by
    rw [hirr.maximalIdeal_eq, ← RingHom.mem_ker, WittVector.ker_constantCoeff]
  obtain ⟨g, hg⟩ := GO.PlWitt.exists_intHom (O := WittVector p k) τ
  have h : (p : 𝓞 E) ∈ (maximalIdeal (WittVector p k)).comap g := by
    rw [Ideal.mem_comap, map_natCast, hm, map_natCast, CharP.cast_eq_zero]
  let Q : HeightOneSpectrum (𝓞 E) := ⟨(maximalIdeal (WittVector p k)).comap g, inferInstance, fun e => by
    rw [e, Ideal.mem_bot] at h
    exact hp.out.ne_zero (Nat.cast_eq_zero.1 h)⟩
  have hQ : ∀ y, y ∈ Q.asIdeal ↔ WittVector.constantCoeff (g y) = 0 := fun y => hm _
  haveI hl : Q.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := ⟨by
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    refine this.eq_of_le (Ideal.comap_ne_top _ Q.isPrime.ne_top) ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact h⟩
  haveI : Algebra.IsUnramifiedAt ℤ Q.asIdeal :=
    (NumberField.not_dvd_discr_iff_forall_liesOver E (𝓞 E) hpZ).1
      (fun hd => hu (Int.natCast_dvd.1 hd)) Q.asIdeal Q.isMaximal hl
  have e : ∀ y : WittVector p k, WittVector.constantCoeff (WittVector.frobenius y) = WittVector.constantCoeff y ^ p :=
    fun y => WittVector.coeff_frobenius_charP p y 0
  let s : 𝓞 E →+* 𝓞 E := (MulSemiringAction.toAlgHom ℤ (𝓞 E) σ).toRingHom
  have key : WittVector.frobenius.comp g = g.comp s := GO.PlWitt.eq_of_cong Q _ _
    (fun y => by rw [hQ, hm, RingHom.comp_apply, e, pow_eq_zero_iff hp.out.ne_zero]) fun y => by
      have h1 := hσ Q.asIdeal y
      rw [← Ideal.LiesOver.over (P := Q.asIdeal) (p := Ideal.span {(p : ℤ)}), Int.card_ideal_quot, hQ, map_sub,
        map_sub, map_pow, map_pow, sub_eq_zero] at h1
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, hm, map_sub, RingHom.comp_apply, e, sub_eq_zero]
      exact h1.symm
  have h2 : (WittVector.FractionRing.frobenius p k : _ →+* _).comp τ = τ.comp (σ : E →+* E) :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun y => by
      have h3 := congrArg (algebraMap _ (FractionRing (WittVector p k))) (RingHom.congr_fun key y)
      rw [RingHom.comp_apply, RingHom.comp_apply, ← SqrtUnif.fractionRing_frobenius_algebraMap, hg, hg] at h3
      exact h3)
  exact RingHom.congr_fun h2 x

theorem isArithFrobAt_frobG (D : D7) (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] : IsArithFrobAt ℤ (D.host.sigmaOf (frobG D p)) P := by
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have h : ∃ g : D.R.GG, ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
      [P.LiesOver (Ideal.span {(p : ℤ)})], IsArithFrobAt ℤ (D.host.sigmaOf g) P := by
    obtain ⟨σ, hσ⟩ := exists_frob_all D.host.E (fun a b =>
      (D.host.gal).injective (by rw [map_mul, map_mul, mul_comm])) p hp
    obtain ⟨g, hg⟩ := (D.host.gal).symm.surjective σ
    have hg' : D.host.sigmaOf g = σ := hg
    exact ⟨g, hg' ▸ hσ⟩
  unfold frobG
  rw [dif_pos h]
  exact h.choose_spec P

theorem phiPow_one_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime], UnramE D p → ∀ τ : Emb D p,
    phiPow D 1 τ = τ.comp (D.host.sigmaOf (frobG D p) : D.host.E →+* D.host.E) := by
  intro D p hp hu τ
  refine RingHom.ext fun x => ?_
  unfold phiPow
  rw [pow_one]
  exact frobenius_comp D.host.E p _ hu _ (fun P _ _ => isArithFrobAt_frobG D p hp.out P) τ x

end GlobalTheory.FrobEmb
end

