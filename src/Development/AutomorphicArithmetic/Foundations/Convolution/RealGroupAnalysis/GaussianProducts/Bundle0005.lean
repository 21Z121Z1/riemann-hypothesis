import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0003
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0004

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AdelicWeightFourNonneg
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G

variable {F : Type} [Field F] [NumberField F]

private theorem continuous_cD (s : (A F)ˣ) : Continuous (cD s : G1 F → G1 F) := by
  refine Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing.continuous_iff.2 ?_
  have he : ∀ i j, Continuous fun g : G1 F => g.1 i j := fun i j =>
    (Matrix.SpecialLinearGroup.isClosedEmbedding_val.continuous).matrix_elem i j
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact he 0 0
  · exact (he 0 1).mul continuous_const
  · exact continuous_const.mul (he 1 0)
  · exact he 1 1

private theorem cD_cD_inv (s : (A F)ˣ) (k : G1 F) : cD s (cD s⁻¹ k) = k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD, mul_assoc]

private theorem infOrth_cD {s : (A F)ˣ} (h1 : (s : A F).1 = 1) (h2 : ((s⁻¹ : (A F)ˣ) : A F).1 = 1)
    {k : G1 F} (hk : InfOrth k) : InfOrth (cD s k) := by
  have hm : ∀ a b : A F, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  have hent : ∀ i j, ((cD s k).1 i j).1 = (k.1 i j).1 := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · change (k.1 0 1 * ((s⁻¹ : (A F)ˣ) : A F)).1 = _
      rw [hm, h2, mul_one]
      rfl
    · change ((s : A F) * k.1 1 0).1 = _
      rw [hm, h1, one_mul]
      rfl
    · rfl
  intro i j
  have e : ∀ a b c d : A F, (a * b + c * d).1 = a.1 * b.1 + c.1 * d.1 := fun _ _ _ _ => rfl
  have h := hk i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, e, Matrix.transpose_apply, Matrix.transpose_apply] at h ⊢
  rw [hent, hent, hent, hent]
  exact h

private theorem adelicWeightFour_mono {L L' : (FractionalIdeal (𝓞 F)⁰ F)ˣ}
    (h : (L : FractionalIdeal (𝓞 F)⁰ F) ≤ L') (N : ℕ) (v : V4 F) : wt4 L N v ≤ wt4 L' N v :=
  Finset.prod_le_prod (fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _)
    fun i _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_mono h N (v i)

private theorem adelicWeightFour_nonneg (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (v : V4 F) : 0 ≤ wt4 L N v :=
  Finset.prod_nonneg fun _ _ => GlobalTheory.CompanionTheory.EpConvB.adeleWeight_nonneg _ _ _

private theorem common_majorant {n : ℕ} (Ψ : Fin n → V4 F → ℂ)
    (hΨ : ∀ i, Ψ i ∈ schwartzBruhatPi F (Fin 4)) (N : ℕ) :
    ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧ ∀ i v, ‖Ψ i v‖ ≤ B * wt4 L N v := by
  have one : ∀ i, ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧
      ∀ v, ‖Ψ i v‖ ≤ B * wt4 L N v := by
    intro i
    obtain ⟨M, L, hM, hb⟩ := GlobalTheory.CompanionTheory.EpConvB.exists_majorant (hΨ i)
      (isCompact_singleton (x := (1 : GL (Fin 4) (A F)))) N
    refine ⟨M, L, hM, fun v => ?_⟩
    have h := hb 1 rfl v
    simpa [wt4] using h
  choose B L hB hb using one
  have key : ∀ s : Finset (Fin n), ∃ (B' : ℝ) (L' : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B' ∧
      ∀ i ∈ s, ∀ v, ‖Ψ i v‖ ≤ B' * wt4 L' N v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, 1, le_rfl, by simp⟩
    | insert a s _ ih =>
      obtain ⟨B', L', h0, h⟩ := ih
      refine ⟨B a + B', fractionalIdealSupUnit (L a) L', add_nonneg (hB a) h0, fun i hi v => ?_⟩
      have hl : wt4 (L a) N v ≤ wt4 (fractionalIdealSupUnit (L a) L') N v :=
        adelicWeightFour_mono le_sup_left N v
      have hr : wt4 L' N v ≤ wt4 (fractionalIdealSupUnit (L a) L') N v :=
        adelicWeightFour_mono le_sup_right N v
      have hw := adelicWeightFour_nonneg (fractionalIdealSupUnit (L a) L') N v
      rcases Finset.mem_insert.1 hi with rfl | hi
      · calc ‖Ψ i v‖ ≤ B i * wt4 (L i) N v := hb i v
          _ ≤ B i * wt4 (fractionalIdealSupUnit (L i) L') N v :=
            mul_le_mul_of_nonneg_left hl (hB i)
          _ ≤ (B i + B') * wt4 (fractionalIdealSupUnit (L i) L') N v :=
            mul_le_mul_of_nonneg_right (by linarith) hw
      · calc ‖Ψ i v‖ ≤ B' * wt4 L' N v := h i hi v
          _ ≤ B' * wt4 (fractionalIdealSupUnit (L a) L') N v :=
            mul_le_mul_of_nonneg_left hr h0
          _ ≤ (B a + B') * wt4 (fractionalIdealSupUnit (L a) L') N v :=
            mul_le_mul_of_nonneg_right (by linarith [hB a]) hw
  obtain ⟨B', L', h0, h⟩ := key Finset.univ
  exact ⟨B', L', h0, fun i v => h i (Finset.mem_univ i) v⟩

end UpperTheory.ConvolutionTheory.R2.G

theorem UpperTheory.ConvolutionTheory.R2.G.majL :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D), ∀ φ ∈ Fock D.δ, ∀ h : GL (Fin 2) (A E), ((nu F h : (A F)ˣ) : A F).1 = 1 → ∀ N : ℕ,
    ∃ (B : ℝ) (L : (FractionalIdeal (𝓞 F)⁰ F)ˣ), 0 ≤ B ∧ ∀ k ∈ KK F, ∀ v, ‖hat (W.Om k (W.L h φ)).1 v‖ ≤ B * wt4 L N v := by
  intro F E _ _ _ _ _ _ _ D W φ hφ h ht N
  have hinv : (((nu F h)⁻¹ : (A F)ˣ) : A F).1 = 1 := by
    have h1 : (((nu F h : (A F)ˣ) : A F) * (((nu F h)⁻¹ : (A F)ˣ) : A F)).1 = (1 : A F).1 := by
      rw [Units.mul_inv]
    have h2 : (((nu F h : (A F)ˣ) : A F) * (((nu F h)⁻¹ : (A F)ˣ) : A F)).1 =
        ((nu F h : (A F)ˣ) : A F).1 * (((nu F h)⁻¹ : (A F)ˣ) : A F).1 := rfl
    rw [h2, ht, one_mul] at h1
    exact h1
  have hC : IsCompact (cD (nu F h)⁻¹ '' KK F) :=
    (UpperTheory.ConvolutionTheory.R2.M.kkCpt F).2.image (continuous_cD _)
  have hO : ∀ k ∈ cD (nu F h)⁻¹ '' KK F, InfOrth k := by
    rintro _ ⟨k, hk, rfl⟩
    exact infOrth_cD hinv (by rw [inv_inv]; exact ht) hk.1
  obtain ⟨U, -, hU, hm⟩ := (fockSt F E D W).om φ hφ _ hC hO
  obtain ⟨n, b, c, B, -, -, hb⟩ := coefBd F E D W φ _ U hC hU hm
  obtain ⟨H, hH⟩ := hatLin F
  obtain ⟨B', L, hB', hmaj⟩ := common_majorant (fun i => (H (W.L h (b i))).1)
    (fun i => (H (W.L h (b i))).2) N
  refine ⟨n * (|B| * B'), L, by positivity, fun k hk v => ?_⟩
  obtain ⟨hc, he⟩ := hb _ ⟨k, hk, rfl⟩
  have hcomm : W.Om k (W.L h φ) = W.L h (W.Om (cD (nu F h)⁻¹ k) φ) := by
    have h1 := LinearMap.congr_fun (W.comm h (cD (nu F h)⁻¹ k)) φ
    rw [cD_cD_inv] at h1
    exact h1.symm
  have hexp : hat (W.Om k (W.L h φ)).1 v =
      ∑ i, c i (cD (nu F h)⁻¹ k) * (H (W.L h (b i))).1 v := by
    rw [hcomm, he, ← hH, map_sum, map_sum]
    simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [hexp]
  have hw := adelicWeightFour_nonneg L N v
  calc ‖∑ i, c i (cD (nu F h)⁻¹ k) * (H (W.L h (b i))).1 v‖
      ≤ ∑ i, ‖c i (cD (nu F h)⁻¹ k) * (H (W.L h (b i))).1 v‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, |B| * (B' * wt4 L N v) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact mul_le_mul ((hc i).trans (le_abs_self B)) (hmaj i v) (norm_nonneg _) (abs_nonneg B)
    _ = n * (|B| * B') * wt4 L N v := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.CuspE
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

open GroundTheory.Automorphic.FourierWhittaker in

private noncomputable def latE {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) :
    vecLattice F (Fin 2) ≃ AdeleRing.principalSubgroup (𝓞 E) E where
  toFun g := ⟨D.coE.symm g.1, by
    obtain ⟨_, ξ, rfl⟩ := g
    refine ⟨algebraMap F E (ξ 0) + algebraMap F E (ξ 1) * D.θ, ?_⟩
    exact (D.mkE_rt (ξ 0) (ξ 1)).symm⟩
  invFun y := ⟨D.coE y.1, by
    obtain ⟨_, z, rfl⟩ := y
    exact mem_vecLattice.2 ⟨fun i => D.b.repr z i, funext fun i => (D.co_rt z i).symm⟩⟩
  left_inv g := Subtype.ext (D.coE.apply_symm_apply g.1)
  right_inv y := Subtype.ext (D.coE.symm_apply_apply y.1)

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.ConvolutionTheory.R2.G.cuspE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (Φ : GL (Fin 2) (A E) → ℂ), (∀ γ h, Φ (ratGL E 2 γ * h) = Φ h) →
    (∀ h, ∫ u in FS2 F, Φ (nE D u * h) ∂(adeleMeasurePi F) = 0) → GlobalTheory.CuspRep.IsCuspidal Φ := by
  intro F E _ _ _ _ _ D Φ hl h0
  refine cuspOf E Φ hl fun h => ?_
  let β : (Fin 2 → A F) ≃ₜ+ A E := D.coE.symm
  let m := β.toHomeomorph.toMeasurableEquiv
  haveI : (adeleMeasurePi F (ι := Fin 2)).IsAddHaarMeasure := inferInstanceAs (Measure.pi fun _ : Fin 2 => adeleMeasure F).IsAddHaarMeasure
  haveI : ((adeleMeasurePi F (ι := Fin 2)).map m).IsAddHaarMeasure := β.isAddHaarMeasure_map (adeleMeasurePi F)
  have hF : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 F) ((adeleMeasurePi F (ι := Fin 2)).map m) :=
    (isAddFundamentalDomain_vecDomain (K := F) (ι := Fin 2)).image_of_equiv m.toEquiv
      (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving (latE D).symm
      fun y x => by
        change β (D.coE y.1 + x) = y.1 + β x
        rw [map_add]
        congr 1
        exact D.coE.symm_apply_apply y.1
  have hF' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 E) E) (m '' FS2 F) (adeleMeasure E) :=
    hF.mono (Measure.absolutelyContinuous_isAddHaarMeasure _ _)
  have hper : ∀ (g : AdeleRing.principalSubgroup (𝓞 E) E) (x : A E),
      Φ (gl (nU (g +ᵥ x)) * h) = Φ (gl (nU x) * h) := by
    rintro ⟨_, k, rfl⟩ x
    obtain ⟨γ, hγ⟩ := Pp.rat_n k
    change Φ (gl (nU (rt k + x)) * h) = _
    rw [Pp.n_add, ← hγ, mul_assoc, hl]
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 E) E) := (latE D).symm.injective.countable
  have h1 := (isAddFundamentalDomain_fundamentalSet E).setIntegral_eq hF' (f := fun x => Φ (gl (nU x) * h)) hper
  rw [h1, Measure.isAddLeftInvariant_eq_smul (adeleMeasure E) ((adeleMeasurePi F (ι := Fin 2)).map m), Measure.restrict_smul,
    integral_smul_nnreal_measure, m.measurableEmbedding.setIntegral_map, m.injective.preimage_image]
  have h3 : ∫ u in FS2 F, Φ (gl (nU (m u)) * h) ∂(adeleMeasurePi F) = 0 := h0 h
  rw [h3, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HermAdel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private noncomputable def hJ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    (InfinitePlace F → ℝ) ≃ₜ InfiniteAdeleRing F where
  toEquiv := (TR.infEq F).toEquiv
  continuous_toFun := TR.continuous_infEq F
  continuous_invFun := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private lemma map_hJ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ c : NNReal, (infiniteAdeleMeasure F).map (hJ F).symm =
      c • (volume : Measure (InfinitePlace F → ℝ)) := by
  have hH : ((infiniteAdeleMeasure F).map (hJ F).symm).IsAddHaarMeasure :=
    (TR.infEq F).symm.toAddEquiv.isAddHaarMeasure_map (infiniteAdeleMeasure F)
      (hJ F).symm.continuous (hJ F).continuous
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul ((infiniteAdeleMeasure F).map (hJ F).symm)
    (volume : Measure (InfinitePlace F → ℝ))⟩

private lemma split_int {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {c : NNReal}
    (hc : (infiniteAdeleMeasure F).map (hJ F).symm = c • (volume : Measure (InfinitePlace F → ℝ)))
    (f : InfinitePlace F → ℝ → ℂ) (hf : ∀ w, Integrable (f w))
    (G : FiniteAdeleRing (𝓞 F) F → ℂ) :
    (Integrable G (finiteAdeleMeasure F) →
      Integrable (fun s : A F => (∏ w, f w (TR.pInf F s w)) * G s.2) (adeleMeasure F)) ∧
    ∫ s : A F, (∏ w, f w (TR.pInf F s w)) * G s.2 ∂(adeleMeasure F) =
      (c : ℂ) * (∏ w, ∫ t, f w t) * ∫ a, G a ∂(finiteAdeleMeasure F) := by
  have emb := (hJ F).symm.measurableEmbedding
  have hv : Integrable (fun y : InfinitePlace F → ℝ => ∏ w, f w (y w)) volume :=
    Integrable.fintype_prod hf
  have hv' : Integrable (fun y : InfinitePlace F → ℝ => ∏ w, f w (y w))
      ((infiniteAdeleMeasure F).map (hJ F).symm) := by
    rw [hc]
    exact hv.smul_measure ENNReal.coe_ne_top
  have hi : Integrable (fun z : InfiniteAdeleRing F => ∏ w, f w ((hJ F).symm z w))
      (infiniteAdeleMeasure F) := (emb.integrable_map_iff.1 hv')
  have hint : ∫ z : InfiniteAdeleRing F, ∏ w, f w ((hJ F).symm z w) ∂(infiniteAdeleMeasure F) =
      (c : ℂ) * ∏ w, ∫ t, f w t := by
    have h1 := emb.integral_map (μ := infiniteAdeleMeasure F)
      (fun y : InfinitePlace F → ℝ => ∏ w, f w (y w))
    rw [← h1, hc, integral_smul_nnreal_measure, volume_pi, integral_fintype_prod_eq_prod]
    rw [NNReal.smul_def, Complex.real_smul]
  refine ⟨fun hG => hi.mul_prod hG, ?_⟩
  have h2 := integral_prod_mul (μ := infiniteAdeleMeasure F) (ν := finiteAdeleMeasure F)
    (fun z : InfiniteAdeleRing F => ∏ w, f w ((hJ F).symm z w)) G
  rw [hint] at h2
  exact h2

private lemma gauss_prod {ι : Type} [Fintype ι] (y : ι → ℝ) :
    Complex.exp (-(Real.pi : ℂ) * ((∑ w, y w ^ 2 : ℝ) : ℂ)) =
      ∏ w, Complex.exp (-(Real.pi : ℂ) * (y w : ℂ) ^ 2) := by
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

private lemma eval_mem {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (Q : Polynomial ℂ)
    (w : InfinitePlace F) :
    (fun v : V4 F => Q.eval ((TR.pInf F (v 1) w : ℝ) : ℂ)) ∈ polyFn (F := F) := by
  have h0 : (fun v : V4 F => ((TR.pInf F (v 1) w : ℝ) : ℂ)) ∈ polyFn (F := F) :=
    Algebra.subset_adjoin ⟨1, w, rfl⟩
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    have := (polyFn (F := F)).add_mem hp hq
    convert this using 1
    ext v
    simp [Polynomial.eval_add]
  | monomial n a =>
    have := (polyFn (F := F)).mul_mem ((polyFn (F := F)).algebraMap_mem a)
      ((polyFn (F := F)).pow_mem h0 n)
    convert this using 1
    ext v
    simp [Polynomial.eval_monomial]

theorem UpperTheory.ConvolutionTheory.R2.G.hermAdel :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (e : InfinitePlace F → ℕ), ∃ P : A F → ℂ, (fun v : V4 F => P (v 1)) ∈ polyFn (F := F) ∧
    ∀ g : FiniteAdeleRing (𝓞 F) F → ℂ, Integrable g (finiteAdeleMeasure F) →
    Integrable (fun s : A F => (∏ w, ((TR.pInf F s w : ℝ) : ℂ) ^ e w) * Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F s w ^ 2 : ℝ) : ℂ)) * g s.2) (adeleMeasure F) ∧
    ∀ x : A F, ∫ s : A F, (∏ w, ((TR.pInf F s w : ℝ) : ℂ) ^ e w) * Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F s w ^ 2 : ℝ) : ℂ)) * g s.2 * ψ (-(s * x)) ∂(adeleMeasure F) =
    P x * Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F x w ^ 2 : ℝ) : ℂ)) *
    ∫ s, g s * ((finiteAdelicChar F (-(s * x.2)) : Circle) : ℂ) ∂(finiteAdeleMeasure F) := by
  intro F _ _ _ e
  obtain ⟨c, hc⟩ := map_hJ F
  have hP := fun n => (hermite1 n).2
  choose Q hQ using hP
  have hH : ∀ y : InfinitePlace F → ℝ, (∏ w, ((y w : ℝ) : ℂ) ^ e w) *
      Complex.exp (-(Real.pi : ℂ) * ((∑ w, y w ^ 2 : ℝ) : ℂ)) =
      ∏ w, ((y w : ℂ) ^ e w * Complex.exp (-(Real.pi : ℂ) * (y w : ℂ) ^ 2)) := by
    intro y
    rw [gauss_prod, Finset.prod_mul_distrib]
  refine ⟨fun x => (c : ℂ) * ∏ w, (Q (e w)).eval ((TR.pInf F x w : ℝ) : ℂ), ?_, fun g hg => ⟨?_, fun x => ?_⟩⟩
  · have h1 : (fun v : V4 F => (∏ w, (Q (e w)).eval ((TR.pInf F (v 1) w : ℝ) : ℂ))) ∈ polyFn (F := F) := by
      have := (polyFn (F := F)).prod_mem (t := Finset.univ)
        (f := fun w => fun v : V4 F => (Q (e w)).eval ((TR.pInf F (v 1) w : ℝ) : ℂ))
        (fun w _ => eval_mem _ w)
      convert this using 1
      ext v
      simp [Finset.prod_apply]
    have := (polyFn (F := F)).mul_mem ((polyFn (F := F)).algebraMap_mem (c : ℂ)) h1
    convert this using 1
    ext v
    simp
  · have h := (split_int hc (fun w t => (t : ℂ) ^ e w * Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2))
      (fun w => (hermite1 (e w)).1) g).1 hg
    refine h.congr (Filter.Eventually.of_forall fun s => ?_)
    simp only [hH]
  · have hS := (UpperTheory.ConvolutionTheory.R2.C.splitA F).2
    have hint : ∀ w : InfinitePlace F, Integrable (fun t : ℝ => (t : ℂ) ^ e w * Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (t * (TR.pInf F x w : ℝ)))) := by
      intro w
      refine (hermite1 (e w)).1.mono (Continuous.aestronglyMeasurable (by fun_prop))
        (Filter.Eventually.of_forall fun s => ?_)
      rw [norm_mul]
      have : ‖Complex.exp (2 * Real.pi * Complex.I * (s * (TR.pInf F x w : ℝ)))‖ = 1 := by
        have e1 : (2 * Real.pi * Complex.I * (s * (TR.pInf F x w : ℝ)) : ℂ) =
            ((2 * Real.pi * (s * TR.pInf F x w) : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [e1, Complex.norm_exp_ofReal_mul_I]
      rw [this, mul_one]
    have h := (split_int hc (fun w t => (t : ℂ) ^ e w * Complex.exp (-(Real.pi : ℂ) * (t : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (t * (TR.pInf F x w : ℝ)))) hint
      (fun a => g a * ((finiteAdelicChar F (-(a * x.2)) : Circle) : ℂ))).2
    have hcongr : ∀ s : A F, (∏ w, ((TR.pInf F s w : ℝ) : ℂ) ^ e w) * Complex.exp (-(Real.pi : ℂ) * ((∑ w, TR.pInf F s w ^ 2 : ℝ) : ℂ)) * g s.2 * ψ (-(s * x)) =
        (∏ w, (((TR.pInf F s w : ℝ) : ℂ) ^ e w * Complex.exp (-(Real.pi : ℂ) * ((TR.pInf F s w : ℝ) : ℂ) ^ 2) *
          Complex.exp (2 * Real.pi * Complex.I * (((TR.pInf F s w : ℝ) : ℂ) * (TR.pInf F x w : ℝ))))) *
        (g s.2 * ((finiteAdelicChar F (-(s.2 * x.2)) : Circle) : ℂ)) := by
      intro s
      have e1 : (-(s * x)).2 = -(s.2 * x.2) := rfl
      have e2 : ∀ w, TR.pInf F (-(s * x)) w = -(TR.pInf F s w * TR.pInf F x w) := by
        intro w
        rw [map_neg, map_mul]
        rfl
      rw [hS (-(s * x)), e1, hH, Finset.prod_mul_distrib (f := fun w => _ * _)]
      have e3 : ∀ w, Complex.exp (-(2 * Real.pi * Complex.I) * ((TR.pInf F (-(s * x)) w : ℝ) : ℂ)) =
          Complex.exp (2 * Real.pi * Complex.I * (((TR.pInf F s w : ℝ) : ℂ) * (TR.pInf F x w : ℝ))) := by
        intro w
        rw [e2]
        congr 1
        push_cast
        ring
      simp only [e3]
      ring
    simp only [hcongr]
    rw [h]
    simp only [hQ]
    rw [Finset.prod_mul_distrib, gauss_prod]
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomAdel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private theorem td_adic {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

private theorem td_fin (F : Type) [Field F] [NumberField F] :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), TotallyDisconnectedSpace (v.adicCompletion F) :=
    fun v => td_adic v
  refine ⟨isTotallyDisconnected_of_image (f := fun (x : FiniteAdeleRing (𝓞 F) F) v => x v)
    (continuous_pi fun v => RestrictedProduct.continuous_eval v).continuousOn
    (fun x y h => Subtype.ext (funext fun v => congrFun h v))
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

private theorem basis_fin (F : Type) [Field F] [NumberField F] :
    TopologicalSpace.IsTopologicalBasis
      {T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F) | IsCompact T ∧ IsOpen T} := by
  haveI := td_fin F
  have hb : TopologicalSpace.IsTopologicalBasis
      {s : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F) | IsClopen s} :=
    loc_compact_Haus_tot_disc_of_zero_dim
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun T hT => hT.2) ?_
  intro x U hx hU
  obtain ⟨K, hKc, hxK, hKU⟩ := exists_compact_subset hU hx
  obtain ⟨C, hC, hxC, hCU⟩ := hb.exists_subset_of_mem_open hxK isOpen_interior
  exact ⟨C, ⟨hKc.of_isClosed_subset hC.isClosed (hCU.trans interior_subset), hC.isOpen⟩, hxC,
    hCU.trans (interior_subset.trans hKU)⟩

section
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

private theorem cont_symm : Continuous (TR.infEq F).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem cont_pInf : Continuous (TR.pInf F) := (cont_symm F).comp continuous_fst

private noncomputable def xc (v : Fin 2 → A F) : Fin 2 × InfinitePlace F → ℝ := fun p => TR.pInf F (v p.1) p.2

private noncomputable def ec (y : (Fin 2 × InfinitePlace F → ℝ) × (Fin 2 → FiniteAdeleRing (𝓞 F) F)) :
    Fin 2 → A F :=
  fun i => ((TR.infEq F (fun w => y.1 (i, w)), y.2 i) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

private theorem cont_xc : Continuous (xc F) :=
  continuous_pi fun p => (continuous_apply p.2).comp ((cont_pInf F).comp (continuous_apply p.1))

private theorem cont_fin : Continuous (finPartPi : (Fin 2 → A F) → Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

private theorem cont_ec : Continuous (ec F) := by
  refine continuous_pi fun i => ?_
  exact ((TR.continuous_infEq F).comp (continuous_pi fun w =>
    (continuous_apply (i, w)).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

private theorem ec_xc (v : Fin 2 → A F) : ec F (xc F v, finPartPi v) = v := by
  funext i
  refine TR.ad_ext ?_ rfl
  exact (TR.infEq F).symm_apply_apply _

private theorem poly_mem (t : Fin 2 × InfinitePlace F → ℝ) (n : ℕ) :
    (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ) ^ n) ∈ polyOn F (Fin 2) := by
  have h : (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ))
      = ∑ p, (t p : ℂ) • (fun v : Fin 2 → A F => ((TR.pInf F (v p.1) p.2 : ℝ) : ℂ)) := by
    funext v
    simp [Finset.sum_apply, xc]
  have h1 : (fun v : Fin 2 → A F => ((∑ p, t p * xc F v p : ℝ) : ℂ)) ∈ polyOn F (Fin 2) := by
    rw [h]
    refine Subalgebra.sum_mem _ fun p _ => Subalgebra.smul_mem _ ?_ _
    exact Algebra.subset_adjoin (show _ ∈ {g : (Fin 2 → A F) → ℂ | ∃ i w, g = fun v => ((TR.pInf F (v i) w : ℝ) : ℂ)} from ⟨p.1, p.2, rfl⟩)
  exact Subalgebra.pow_mem _ h1 n

private theorem sum_xc (v : Fin 2 → A F) : ∑ p, |xc F v p| = sz v := by
  rw [Fintype.sum_prod_type]; rfl

end

theorem UpperTheory.ConvolutionTheory.R2.G.momAdel :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : Ω → Fin 2 → A F) (ρ : Ω → ℂ), Measurable r →
    (∀ R : ℝ, Integrable (fun ω => ((Real.exp (R * sz (r ω)) : ℝ) : ℂ) * ρ ω) ν) →
    (∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T → ∫ ω, p (r ω) * T.indicator 1 (finPartPi (r ω)) * ρ ω ∂ν = 0) →
    ∀ q : (Fin 2 → A F) → ℂ, Measurable q → (∀ x, ‖q x‖ ≤ 1) → ∫ ω, q (r ω) * ρ ω ∂ν = 0 := by
  intro F _ _ _ Ω _ ν r ρ hr hint hmom q hq hq1
  have hρ : Integrable ρ ν := by simpa using hint 0
  have hX : Measurable fun ω => xc F (r ω) := (cont_xc F).measurable.comp hr
  have hs : Measurable fun ω => (finPartPi (r ω) : Fin 2 → FiniteAdeleRing (𝓞 F) F) :=
    (cont_fin F).measurable.comp hr
  have hT : ∀ (T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F)) (S : Set (Fin 2 × InfinitePlace F → ℝ)),
      MeasurableSet S → IsCompact T → IsOpen T →
      ∫ ω, S.indicator 1 (xc F (r ω)) * (T.indicator 1 (finPartPi (r ω)) * ρ ω) ∂ν = 0 := by
    intro T S hS hTc hTo
    have hi : Measurable fun ω => T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) :=
      (measurable_one.indicator hTo.measurableSet).comp hs
    have hib : ∀ ω, ‖T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω))‖ ≤ 1 := by
      intro ω
      by_cases h : finPartPi (r ω) ∈ T <;> simp [h]
    have hI : ∀ g : Ω → ℂ, Integrable g ν →
        Integrable (fun ω => T.indicator (1 : (Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ) (finPartPi (r ω)) * g ω) ν :=
      fun g hg => hg.bdd_mul hi.aestronglyMeasurable (Eventually.of_forall hib)
    refine charZero Ω _ ν _ _ hX (hI ρ hρ) ?_ S hS
    refine momChar Ω _ ν _ _ hX (fun R => ?_) (fun n t => ?_)
    · simp only [sum_xc]
      refine (hI _ (hint R)).congr (Eventually.of_forall fun ω => ?_)
      simp only
      ring
    · have := hmom _ (poly_mem F t n) T hTc hTo
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only
      ring
  have hQ : Measurable fun y => q (ec F y) := hq.comp (cont_ec F).measurable
  have := prodExt Ω _ _ ν (fun ω => xc F (r ω)) (fun ω => finPartPi (r ω)) ρ (basis_fin F) hX hs hρ
    (fun S T hS hTc hTo => hT T S hS hTc hTo) _ hQ (fun y => hq1 _)
  simpa only [ec_xc] using this
end

