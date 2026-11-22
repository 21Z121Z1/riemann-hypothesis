import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePlaceCharacterFactor
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaIntLeSetLIntegralOfCover
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AbsThetaQuot.absThetaInt_le_setLIntegral_of_cover : ∀ (D : D7) (V : HSp D) (n : ℕ) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank n → ℂ, Continuous φ → ∀ S : Set (GA D V), MeasurableSet S → (∀ g, ∃ γ ∈ GQ V, ∃ s ∈ S, g = γ * s) → GlobalTheory.SiegelFormula.absThetaInt V ν φ ≤ ∫⁻ g in S, GlobalTheory.SiegelFormula.absTheta V φ g ∂ν := by
  intro D V n ν hν φ hφ S hS hcov
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hScov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hleft := GlobalTheory.SiegelFormula.leftInv_absTheta V φ
  have e1 : GlobalTheory.SiegelFormula.absThetaInt V ν φ =
      ∫⁻ g in GlobalTheory.AutomorphicL2Unitary.stdDom (GQ V), GlobalTheory.SiegelFormula.absTheta V φ g ∂ν := by
    rw [GlobalTheory.SiegelFormula.absThetaInt, GlobalTheory.AutomorphicL2Unitary.autMeasure, GlobalTheory.AutomorphicL2Unitary.quotMeasure,
      lintegral_map (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hφ) GlobalTheory.AutomorphicL2Unitary.measurable_mk]
    exact lintegral_congr fun g => hleft.descend_mk g
  rw [e1]
  exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (GQ V) ν
    (GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (GQ V) ν) hS hScov
    (GlobalTheory.AbsThetaSemi.measurable_absTheta V hφ) (fun γ hγ g => hleft γ hγ g)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminormStatement
section
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absoluteThetaIntegral_le_continuousSeminorm : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E), ∃ ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)), IsContSeminorm ν ∧ ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) := by
  first | exact @GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm | exact GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm | (intros; apply GlobalTheory.AbsThetaSemi.absThetaInt_le_contSeminorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprime
section
open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors Matrix TensorProduct

noncomputable section
namespace GlobalTheory.SkewPlaneIdeal

theorem codiff_le_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P →
    ∀ c : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * c))) → w.valuation E c ≤ 1 :=
  GlobalTheory.T.valuation_le_one_of_integral_trace

theorem exists_unit_mul_integral : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
    (T : Set K) (d : 𝓞 K), d ≠ 0 → (∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) → (∀ t ∈ T, P.valuation K t ≤ 1) →
    ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) :=
  GlobalTheory.T.exists_unit_denominator_integral

theorem exists_valued_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : Fin n → E)
    (S : Set E), (0 : E) ∈ S → (∀ z ∈ L, z ⬝ᵥ c ∈ S) → ∀ u ∈ splitLat τ L,
    ∃ s ∈ S, Valued.v (u ⬝ᵥ fun i => τ (c i)) ≤ Valued.v (τ s) := by
  intro F E _ _ _ _ _ v τ n L c S h0 hS u hu
  obtain ⟨y, hy, rfl⟩ := hu
  refine latLoc_induction (p := fun y => ∃ s ∈ S, Valued.v (splitVec τ y ⬝ᵥ fun i => τ (c i)) ≤ Valued.v (τ s))
    ?_ ?_ ?_ ?_ hy
  · intro a ha z hz
    refine ⟨z ⬝ᵥ c, hS z hz, ?_⟩
    have e : (splitVec τ fun i => a ⊗ₜ[F] z i) ⬝ᵥ (fun i => τ (c i)) = a * τ (z ⬝ᵥ c) := by
      simp [splitVec, dotProduct, map_sum, Finset.mul_sum, mul_assoc]
    rw [e, map_mul]
    exact mul_le_of_le_one_left' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ha)
  · refine ⟨0, h0, ?_⟩
    have : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun i => map_zero _
    rw [this, zero_dotProduct, map_zero]
    exact zero_le
  · rintro y z ⟨s1, hs1, h1⟩ ⟨s2, hs2, h2⟩
    rw [splitVec_add, add_dotProduct]
    rcases le_total (Valued.v (τ s1)) (Valued.v (τ s2)) with h | h
    · exact ⟨s2, hs2, (Valuation.map_add _ _ _).trans (max_le (h1.trans h) h2)⟩
    · exact ⟨s1, hs1, (Valuation.map_add _ _ _).trans (max_le h1 (h2.trans h))⟩
  · rintro y ⟨s1, hs1, h1⟩
    refine ⟨s1, hs1, ?_⟩
    have : splitVec τ (-y) = -splitVec τ y := funext fun i => map_neg _ _
    rw [this, neg_dotProduct, Valuation.map_neg]
    exact h1

theorem exists_denom : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)),
    L.FG → ∀ c : Fin n → E, ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ z ∈ L, IsIntegral ℤ ((d : E) * (z ⬝ᵥ c)) := by
  intro E _ _ n L hL c
  let f : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => z ⬝ᵥ c
      map_add' := fun a b => add_dotProduct a b c
      map_smul' := fun o a => by simp [smul_dotProduct] }
  obtain ⟨a, ha, hint⟩ := FractionalIdeal.isFractional_of_fg (S := (𝓞 E)⁰) (P := E) (hL.map f)
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun z hz => ?_⟩
  obtain ⟨b, hb⟩ := hint _ (Submodule.mem_map_of_mem hz)
  rw [Algebra.smul_def] at hb
  have e : (a : E) * (z ⬝ᵥ c) = (b : E) := hb.symm
  rw [e]
  exact RingOfIntegers.isIntegral_coe b

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma form_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := add_dotProduct _ _ _

lemma form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (a c : Fin n → E) :
    form σ J (t • a) c = t * form σ J a c := smul_dotProduct _ _ _

lemma form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J a (b + c) = form σ J a b + form σ J a c := by
  have e : (fun i => σ ((b + c) i)) = (fun i => σ (b i)) + fun i => σ (c i) := funext fun i => map_add σ _ _
  simp only [form, e, Matrix.mulVec_add, dotProduct_add]

lemma form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (a b : Fin n → E) :
    form σ J a (t • b) = σ t * form σ J a b := by
  have e : (fun i => σ ((t • b) i)) = σ t • fun i => σ (b i) := funext fun i => by simp
  simp only [form, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma form_swap (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

lemma map_dotProduct {K : Type} [Field K] [Algebra F K] (τ : E →ₐ[F] K) {n : ℕ} (a c : Fin n → E) :
    (fun i => τ (a i)) ⬝ᵥ (fun i => τ (c i)) = τ (a ⬝ᵥ c) := by
  simp [dotProduct, map_sum, map_mul]

theorem count_eq_zero_of_valuation {K : Type} [Field K] [NumberField K] {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (w : HeightOneSpectrum (𝓞 K)) (h1 : ∀ s ∈ I, w.valuation K s ≤ 1) (h2 : ∃ s ∈ I, 1 ≤ w.valuation K s) :
    FractionalIdeal.count K w I = 0 := by
  obtain ⟨y, hy, hvy⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI w
  obtain ⟨s, hs, hvs⟩ := h2
  have a := h1 y hy
  have b := (GlobalTheory.Idele.mem_iff_valuation_le hI s).1 hs w
  rw [hvy, ← WithZero.exp_zero, WithZero.exp_le_exp] at a
  have c := hvs.trans b
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at c
  omega

lemma mem_splitLat_of_mem {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} {z : Fin n → E} (hz : z ∈ L) : (fun i => τ (z i)) ∈ splitLat τ L :=
  ⟨fun i => (1 : Fv F v) ⊗ₜ[F] z i, tmul_mem_latLoc (one_mem _) hz, funext fun i => by simp [splitVec]⟩

lemma col_prim {v : HeightOneSpectrum (𝓞 F)} {τ : E →ₐ[F] Fv F v} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) (j : Fin n) (z : Fin n → E) (hz : ∀ r, β.1 r j = τ (z r)) :
    (fun r => τ (z r)) ∈ splitLat τ L ∧ ∀ t : Fv F v, (fun r => t * τ (z r)) ∈ splitLat τ L → Valued.v t ≤ 1 := by
  classical
  have hcol : β.1 *ᵥ Pi.single j 1 = fun r => τ (z r) := by
    rw [Matrix.mulVec_single_one]; funext r; exact hz r
  refine ⟨hcol ▸ (hβ _).1 fun i => ?_, fun t ht => ?_⟩
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · have e : β.1 *ᵥ (t • Pi.single j 1) = fun r => t * τ (z r) := by
      rw [Matrix.mulVec_smul, hcol]; rfl
    have := (hβ _).2 (e ▸ ht) j
    simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using this

theorem skewPlaneIdeal_ne_zero_and_count_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsSkew σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < n → i₁ < n →
    H.𝔟 ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w H.𝔟 = 0 := by
  intro F E _ _ _ _ _ σ B n n₁ H Y Y₁ i₀ i₁ r s hB hY hH hi₀ hi₁
  have hσ : ∀ z, σ (σ z) = z := cm_conj_conj hB.cm
  have hyx : form σ Y.J H.y H.x = -1 := by rw [form_swap σ hσ Y.J hY.skew, hH.xy, map_one]
  have hxι : ∀ u, form σ Y.J H.x (H.ι *ᵥ u) = 0 := fun u => by
    rw [form_swap σ hσ Y.J hY.skew, (hH.orth u).1, map_zero, neg_zero]

  have hco : ∀ z ∈ Y.L, form σ Y.J z H.y • H.x ∈ Y.L ∧ (-form σ Y.J z H.x) • H.y ∈ Y.L ∧
      ∀ a : E, form σ Y.J (a • H.x) z = a * σ (-form σ Y.J z H.x) := by
    intro z hz
    obtain ⟨a, t, u, ha, ht, _, rfl⟩ := hH.split z hz
    have e1 : form σ Y.J (a • H.x + H.ι *ᵥ u + t • H.y) H.y = a := by
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xy, hH.yy, (hH.orth u).2]; ring
    have e2 : -form σ Y.J (a • H.x + H.ι *ᵥ u + t • H.y) H.x = t := by
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xx, hyx, (hH.orth u).1]; ring
    refine ⟨by rw [e1]; exact ha, by rw [e2]; exact ht, fun b => ?_⟩
    rw [e2, form_smul_left, form_add_right, form_add_right, form_smul_right, form_smul_right, hH.xx, hH.xy, hxι]
    ring

  have h0 : H.𝔟 ≠ 0 := by
    intro h0
    let f : (Fin n → E) →ₗ[E] E :=
      { toFun := fun z => form σ Y.J z H.y
        map_add' := fun a b => form_add_left σ Y.J a b H.y
        map_smul' := fun t a => form_smul_left σ Y.J t a H.y }
    have hle : Submodule.span E (Y.L : Set (Fin n → E)) ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      intro z hz
      have := (hH.ideal _).2 (hco z hz).1
      rw [h0] at this
      exact (FractionalIdeal.mem_zero_iff _).1 this
    haveI := hY.lat
    rw [Submodule.IsLattice.span_eq_top] at hle
    have : f H.x = 0 := hle Submodule.mem_top
    change form σ Y.J H.x H.y = 0 at this
    rw [hH.xy] at this
    exact one_ne_zero this
  refine ⟨h0, fun w hw => ?_⟩
  set v : B.P := ⟨w.under (𝓞 F), hw⟩ with hv
  set τ := B.τ v with hτ
  have hβ := hY.bas v
  obtain ⟨hxL, hxp⟩ := col_prim hβ ⟨i₀, hi₀⟩ H.x fun r => (hH.bas v ⟨i₀, hi₀⟩).1 rfl r
  obtain ⟨hyL, hyp⟩ := col_prim hβ ⟨i₁, hi₁⟩ H.y fun r => (hH.bas v ⟨i₁, hi₁⟩).2.1 rfl r
  have hτs : ∀ a : E, ∀ z : Fin n → E, (fun i => τ ((a • z) i)) = fun i => τ a * τ (z i) := fun a z =>
    funext fun i => by simp

  have hxw : ∀ a : E, a • H.x ∈ Y.L → Valued.v (τ a) ≤ 1 := fun a ha =>
    hxp _ (hτs a H.x ▸ mem_splitLat_of_mem τ ha)
  have hyw : ∀ a : E, a • H.y ∈ Y.L → Valued.v (τ a) ≤ 1 := fun a ha =>
    hyp _ (hτs a H.y ▸ mem_splitLat_of_mem τ ha)

  have hxu : ∃ a : E, a • H.x ∈ Y.L ∧ 1 ≤ Valued.v (τ a) := by
    obtain ⟨a, ha, hle⟩ := exists_valued_le F E v.1 τ n Y.L (Y.J *ᵥ fun i => σ (H.y i)) {a | a • H.x ∈ Y.L}
      (by simp) (fun z hz => (hco z hz).1) _ hxL
    refine ⟨a, ha, le_of_eq_of_le ?_ hle⟩
    rw [map_dotProduct τ]
    change 1 = Valued.v (τ (form σ Y.J H.x H.y))
    rw [hH.xy, map_one, map_one]
  have hyu : ∃ a : E, a • H.y ∈ Y.L ∧ 1 ≤ Valued.v (τ a) := by
    obtain ⟨a, ha, hle⟩ := exists_valued_le F E v.1 τ n Y.L (-(Y.J *ᵥ fun i => σ (H.x i))) {a | a • H.y ∈ Y.L}
      (by simp) (fun z hz => by show (z ⬝ᵥ -(Y.J *ᵥ _)) • H.y ∈ Y.L; rw [dotProduct_neg]; exact (hco z hz).2.1) _ hyL
    refine ⟨a, ha, le_of_eq_of_le ?_ hle⟩
    rw [map_dotProduct τ, dotProduct_neg]
    change 1 = Valued.v (τ (-form σ Y.J H.y H.x))
    rw [hyx, neg_neg, map_one, map_one]

  have hwP : w.asIdeal ∈ v.1.asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  rw [primesOver_eq_split hB.cm τ] at hwP
  rcases hwP with hw1 | hw1
  · have hw2 : w = splitPrime τ := HeightOneSpectrum.ext hw1
    have hval : ∀ a : E, w.valuation E a = Valued.v (τ a) := fun a =>
      (congrArg (fun u : HeightOneSpectrum (𝓞 E) => u.valuation E a) hw2).trans (valued_apply_eq_valuation τ a).symm
    refine count_eq_zero_of_valuation h0 _ (fun a ha => ?_) ?_
    · rw [hval]; exact hxw a ((hH.ideal a).1 ha)
    · obtain ⟨a, ha, h1⟩ := hxu
      exact ⟨a, (hH.ideal a).2 ha, by rw [hval]; exact h1⟩
  · have hw2 : w = splitPrime (τ.comp σ) := HeightOneSpectrum.ext (Set.mem_singleton_iff.1 hw1)
    have hval : ∀ a : E, w.valuation E a = Valued.v (τ (σ a)) := fun a =>
      (congrArg (fun u : HeightOneSpectrum (𝓞 E) => u.valuation E a) hw2).trans (valued_apply_eq_valuation _ a).symm
    have hwP' : w.under (𝓞 F) ∈ B.P := hw
    refine count_eq_zero_of_valuation h0 _ (fun a ha => ?_) ?_
    · obtain ⟨t, ht, h1⟩ := hyu
      have hd := (hY.dual (a • H.x)).1 ((hH.ideal a).1 ha) (t • H.y) ht
      have e : form σ Y.J (a • H.x) (t • H.y) = a * σ t := by
        rw [form_smul_left, form_smul_right, hH.xy]; ring
      rw [e] at hd
      have h2 := codiff_le_one F E σ B hB w hwP' _ hd
      rw [hval, map_mul, hσ, map_mul, map_mul] at h2
      rw [hval]
      calc Valued.v (τ (σ a)) = Valued.v (τ (σ a)) * 1 := (mul_one _).symm
        _ ≤ Valued.v (τ (σ a)) * Valued.v (τ t) := mul_le_mul' le_rfl h1
        _ ≤ 1 := h2
    · obtain ⟨d, hd0, hd⟩ := exists_denom E n Y.L hY.lat.fg (-(Y.J *ᵥ fun i => σ (H.x i)))
      have hdt : ∀ t : E, t • H.y ∈ Y.L → IsIntegral ℤ ((d : E) * t) := fun t ht => by
        have := hd _ ht
        rw [dotProduct_neg] at this
        change IsIntegral ℤ ((d : E) * -form σ Y.J (t • H.y) H.x) at this
        rwa [form_smul_left, hyx, mul_neg_one, neg_neg] at this
      let σZ : E →ₐ[ℤ] E := (σ : E →+* E).toIntAlgHom
      have hd1 : RingOfIntegers.mapRingHom (σ : E →+* E) d ≠ 0 := fun h => hd0 (by
        have h' := congrArg (fun x : 𝓞 E => (x : E)) h
        simp at h'
        exact h')
      obtain ⟨s', hs'1, hs'2⟩ := exists_unit_mul_integral E w {u | ∃ t, t • H.y ∈ Y.L ∧ u = σ t}
        (RingOfIntegers.mapRingHom (σ : E →+* E) d) hd1 (by
          rintro _ ⟨t, ht, rfl⟩
          show IsIntegral ℤ (σ (d : E) * σ t)
          rw [← map_mul]
          exact (hdt t ht).map σZ) (by
          rintro _ ⟨t, ht, rfl⟩
          rw [hval, hσ]
          exact hyw t ht)
      refine ⟨s', (hH.ideal _).2 ((hY.dual _).2 fun z hz o => ?_), by rw [hs'1]⟩
      rw [(hco z hz).2.2]
      exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (hs'2 _ ⟨_, (hco z hz).2.1, rfl⟩))

end GlobalTheory.SkewPlaneIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFixatorEqUnipotentRadicalMulCommonFixatorStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicFixator_eq_unipotentRadical_mul_commonFixator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g ∈ fixG σ J C, ∃ u ∈ unipRad σ J C, ∃ x ∈ (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), g = u * x ∧ (g ∈ ratPts σ J → x ∈ ratPts σ J) := by
  first | exact @GlobalTheory.SphEis.fixG_eq_unipRad_mul | exact GlobalTheory.SphEis.fixG_eq_unipRad_mul | (intros; apply GlobalTheory.SphEis.fixG_eq_unipRad_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzEqPureTensorOfFiniteSlicesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_eq_pureTensor_of_finite_slices : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : ∀ v : HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, vac v ≠ 0) →
    (∀ᶠ v in Filter.cofinite, vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ Φ ∈ schA F κ, (∀ (v : HeightOneSpectrum (𝓞 F)) (y : κ → AF F), (∀ k, evFin F v (y k) = 0) →
      ∃ a : ℂ, ∀ ξ : κ → Fv F v, Φ (y + fun k => GlobalTheory.LatVac.liftV v (ξ k)) = a * vac v ξ) →
    ∃ f : SInf F κ, Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f vac := by
  first | exact @GlobalTheory.PureGlue.eq_pure_of_slices | exact GlobalTheory.PureGlue.eq_pure_of_slices | (intros; apply GlobalTheory.PureGlue.eq_pure_of_slices <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
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

noncomputable section

namespace GlobalTheory.LatVac

theorem restrict_liftV_mem_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (fun t : κ → Fv F v => Φ (fun i => GlobalTheory.LatVac.liftV v (t i))) ∈ GlobalTheory.WeilM.SB (κ → Fv F v) := by
  intro F _ _ κ _ v Φ hΦ
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  induction hΦ using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    let s : (κ → Fv F v) → (κ → Af F) := fun t i => GlobalTheory.AdelicU.singleFin v (t i)
    have hs : Continuous s := continuous_pi fun i => (GlobalTheory.AdelicU.continuous_singleFin v).comp (continuous_apply i)
    have hinv : Function.LeftInverse (fun x : κ → Af F => fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (x i)) s :=
      fun t => funext fun i => GlobalTheory.AdelicU.evalV_singleFin_self v (t i)
    have hev : Continuous (fun x : κ → Af F => fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (x i)) :=
      continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
    have hce : Topology.IsClosedEmbedding s := hinv.isClosedEmbedding hev hs
    have hmem : g ∘ s ∈ GlobalTheory.WeilM.SB (κ → Fv F v) :=
      ⟨hg.1.comp_continuous hs, hg.2.comp_isClosedEmbedding hce⟩
    have e : (fun t : κ → Fv F v => GlobalTheory.WeilM.pureA F (⇑f) g (fun i => GlobalTheory.LatVac.liftV v (t i))) =
        f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F 0) • (g ∘ s) := by
      funext t
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ hmem
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ a hx

end GlobalTheory.LatVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
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

namespace GlobalTheory.SchwartzTranslation

theorem schA_add_const : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : κ → AF F),
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (fun y => Φ (y + c)) ∈ GlobalTheory.WeilM.schA F κ :=
  fun {F} _ _ {_} _ c Φ hΦ => GlobalTheory.SchwartzTranslate.schA_translate F c hΦ

end GlobalTheory.SchwartzTranslation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothBumpWithTrigonometricExpansionStatement
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
theorem _root_.GlobalTheory.T.archimedean_smooth_bump_with_trigonometric_expansion : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (U : Set (κ → Ainf F)) (y : κ → AF F), IsOpen U → (fun i => (y i).1) ∈ U →
    ∃ β : (κ → Ainf F) → ℝ, Continuous β ∧ (∀ u, 0 ≤ β u ∧ β u ≤ 1) ∧ β (fun i => (y i).1) = 1 ∧
      (∀ u, β u ≠ 0 → u ∈ U) ∧
      ∃ (s : ℕ → Finset (κ → AF F)) (c : ℕ → (κ → AF F) → ℂ) (C : ℝ),
        (∀ n, ∀ b ∈ s n, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
        (∀ n (x : κ → AF F), ‖∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)‖ ≤ C) ∧
        ∀ x : κ → AF F, Filter.Tendsto (fun n => ∑ b ∈ s n, c n b * ψ (x ⬝ᵥ b)) Filter.atTop
          (nhds ((β (fun i => (x i).1) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.ArchTrigBump.arch_bump_trig | exact GlobalTheory.ArchTrigBump.arch_bump_trig | (intros; apply GlobalTheory.ArchTrigBump.arch_bump_trig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelBoundOfQuotedTheoremsStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticHilbertSamuelBound : Quoted → GeoBound := by
  first | exact @GlobalTheory.HSShort.geoBound_of_quoted' | exact GlobalTheory.HSShort.geoBound_of_quoted' | (intros; apply GlobalTheory.HSShort.geoBound_of_quoted' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePlaceCharacterFactorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_place_character_factor : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ),
    ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 →
    ∃ (b : D.what₂.LL) (g g' : 𝓞 D.what₂.LL), GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      g ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      g' ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      ((chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v)) z) =
        D.what₂.embLL (b * ((g : D.what₂.LL) / (g' : D.what₂.LL))) * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) := by
  first | exact @GlobalTheory.SqStepArith.base_place_factor_zero | exact GlobalTheory.SqStepArith.base_place_factor_zero | (intros; apply GlobalTheory.SqStepArith.base_place_factor_zero <;> assumption)
end

