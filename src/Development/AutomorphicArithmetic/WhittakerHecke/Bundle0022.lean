import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.UnipotentThetaMemCongruenceOfIntegral
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.unipotentTheta_mem_congruence_of_integral :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (M d : ℕ), (∀ w : H.P E, Valued.v (H.cp w (rt ((d : E) * D.θ))) ≤ 1) → ∀ c ∈ Oh ℚ, CongE M (nu D ((M : A ℚ) * (d : A ℚ) * c)) := by
  intro E _ _ D M d hd c hc
  have hk : ∀ u t : A ℚ, D.mkE u t = AdeleBaseChange.adeleMap ℚ E u + AdeleBaseChange.adeleMap ℚ E t * rt D.θ := fun _ _ => rfl
  have h0 : (0 : A E) ∈ Oh E := ⟨rfl, fun w => by
    change Valued.v (0 : H.Kv w) ≤ 1
    simp⟩
  have hneg : ∀ s : A E, s ∈ Oh E → -s ∈ Oh E := fun s hs => ⟨by
    change -s.1 = 0
    rw [hs.1, neg_zero], fun w => by
    have e : (-s).2 w = -(s.2 w) := rfl
    rw [e, Valuation.map_neg]
    exact hs.2 w⟩
  have hfst : (AdeleBaseChange.adeleMap ℚ E c).1 = 0 := by
    obtain ⟨c1, c2⟩ := c
    obtain rfl : c1 = 0 := hc.1
    exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E))
  have hb : AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ) ∈ Oh E := by
    refine ⟨?_, fun w => ?_⟩
    · change (AdeleBaseChange.adeleMap ℚ E c).1 * _ = 0
      rw [hfst, zero_mul]
    · have h1 : Valued.v ((AdeleBaseChange.adeleMap ℚ E c).2 w) ≤ 1 :=
        GroundTheory.Global.AdeleBaseChange.mapsTo_completionMap _ w (hc.2 _)
      have e : (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)).2 w =
          (AdeleBaseChange.adeleMap ℚ E c).2 w * H.cp w (rt ((d : E) * D.θ)) := rfl
      rw [e, map_mul]
      exact mul_le_one' h1 (hd w)
  have hx : D.mkE 0 ((M : A ℚ) * (d : A ℚ) * c) = (M : A E) * (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)) := by
    have hr : rt ((d : E) * D.θ) = (d : A E) * rt D.θ := by
      change algebraMap E (A E) ((d : E) * D.θ) = _
      rw [map_mul, map_natCast]
    rw [hk, map_zero, zero_add, map_mul, map_mul, map_natCast, map_natCast, hr]
    ring
  have key : ∀ s : A E, s ∈ Oh E → ∀ i j, ∃ c ∈ Oh E,
      (!![1, (M : A E) * s; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j - (1 : Matrix (Fin 2) (Fin 2) (A E)) i j = (M : A E) * c := by
    intro s hs i j
    fin_cases i <;> fin_cases j
    · exact ⟨0, h0, by simp⟩
    · exact ⟨s, hs, by simp⟩
    · exact ⟨0, h0, by simp⟩
    · exact ⟨0, h0, by simp⟩
  have hinv : ∀ q : A E, (gl (nU q))⁻¹ = gl (nU (-q)) := by
    intro q
    refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
    change (!![1, q; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) * !![1, -q; 0, 1] = 1
    simp [Matrix.mul_fin_two, Matrix.one_fin_two]
  have hn : nu D ((M : A ℚ) * (d : A ℚ) * c) = gl (nU ((M : A E) * (AdeleBaseChange.adeleMap ℚ E c * rt ((d : E) * D.θ)))) := by
    change gl (nU (D.mkE 0 ((M : A ℚ) * (d : A ℚ) * c))) = _
    rw [hx]
  intro i j
  rw [hn, hinv, ← mul_neg]
  exact ⟨key _ hb i j, key _ (hneg _ hb) i j⟩
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerPeriodAddSmulAndNormLe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

private theorem volume_fundamental_domain_two : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 :=
  GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain

private theorem cont_nE {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
  UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))

private theorem int_Wo {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) {f : GL (Fin 2) (A E) → ℂ}
    (hf : Continuous f) (h : GL (Fin 2) (A E)) :
    IntegrableOn (fun u : Fin 2 → A ℚ => f (nE D u * h) * ψ (u 1)) (FS2 ℚ) (adeleMeasurePi ℚ) := by
  have hg : Continuous fun u : Fin 2 → A ℚ => f (nE D u * h) * ψ (u 1) :=
    (hf.comp ((cont_nE D).mul continuous_const)).mul
      (UpperTheory.ConvolutionTheory.R2.Pp.cont_ψ.comp (continuous_apply 1))
  obtain ⟨C, hC, hs⟩ := UpperTheory.ConvolutionTheory.R2.Pp.exists_cpt (F := ℚ)
  have hK : IsCompact (Set.univ.pi fun _ : Fin 2 => C) := isCompact_univ_pi fun _ => hC
  have hsub : FS2 ℚ ⊆ Set.univ.pi fun _ : Fin 2 => C := Set.pi_mono fun _ _ => hs
  unfold adeleMeasurePi
  exact (hg.continuousOn.integrableOn_compact hK).mono_set hsub

theorem UpperTheory.whittakerPeriod_add_smul_and_norm_le :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E),
        (∀ f f' : GL (Fin 2) (A E) → ℂ, Continuous f → Continuous f' → ∀ h, Wo D (f + f') h = Wo D f h + Wo D f' h) ∧
        (∀ (c : ℂ) (f : GL (Fin 2) (A E) → ℂ) h, Wo D (c • f) h = c * Wo D f h) ∧
        ∀ (f : GL (Fin 2) (A E) → ℂ) (B : ℝ) h, (∀ g, ‖f g‖ ≤ B) → ‖Wo D f h‖ ≤ B := by
  intro E _ _ D
  refine ⟨fun f f' hf hf' h => ?_, fun c f h => ?_, fun f B h hB => ?_⟩
  · unfold Wo
    rw [← integral_add (int_Wo D hf h) (int_Wo D hf' h)]
    simp only [Pi.add_apply, add_mul]
  · unfold Wo
    rw [← integral_const_mul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  · have := norm_setIntegral_le_of_norm_le_const (μ := adeleMeasurePi (ι := Fin 2) ℚ) (s := FS2 ℚ)
      (f := fun u => f (nE D u * h) * ψ (u 1)) (C := B) (by rw [volume_fundamental_domain_two]; exact ENNReal.one_lt_top)
      fun u _ => by rw [norm_mul, UpperTheory.ConvolutionTheory.R2.Pp.norm_ψ, mul_one]; exact hB _
    rwa [measureReal_def, volume_fundamental_domain_two, ENNReal.toReal_one, mul_one] at this
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerScalarMulEqCentralCharSqMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

theorem UpperTheory.whittaker_scalar_mul_eq_centralChar_sq_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ (x : IdeleGroup ℚ) (g : GL (Fin 2) (A E)),
        Wo D φ (em E (Matrix.GeneralLinearGroup.scalar (Fin 2) x) * g) = ((ω.1 x : ℂˣ) : ℂ) ^ 2 * Wo D φ g := by
  intro E _ _ D ω φ hφ x g
  have h1 : em E (Matrix.GeneralLinearGroup.scalar (Fin 2) x) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (ideleEmbedding ℚ E x) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change AdeleBaseChange.adeleMap ℚ E (Matrix.scalar (Fin 2) (x : A ℚ) i j) =
      Matrix.scalar (Fin 2) (AdeleBaseChange.adeleMap ℚ E (x : A ℚ)) i j
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have h2 : ∀ (z : (A E)ˣ) (n : GL (Fin 2) (A E)),
      n * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = Matrix.GeneralLinearGroup.scalar (Fin 2) z * (n * g) := by
    intro z n
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact Units.ext (Matrix.scalar_commute (z : A E) (fun _ => Commute.all _ _) n.val).symm.eq
  have h3 : ideleNorm ℚ E (ideleEmbedding ℚ E x) = x ^ 2 := by
    rw [ideleNorm_ideleEmbedding, Module.finrank_eq_card_basis D.b, Fintype.card_fin]
  unfold Wo
  rw [h1, ← integral_const_mul]
  congr 1
  funext u
  rw [h2, hφ.cen, h3, map_pow, Units.val_pow_eq_pow_val, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerSumMulEqSumMulWhittaker
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.whittaker_sum_mul_eq_sum_mul_whittaker :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ι : Type) (s : Finset ι) (c : ι → ℂ) (φ : ι → GL (Fin 2) (A E) → ℂ), (∀ i, Continuous (φ i)) → (∀ i, ∃ B : ℝ, ∀ g, ‖φ i g‖ ≤ B) → ∀ h : GL (Fin 2) (A E), Wo D (fun g => ∑ i ∈ s, c i * φ i g) h = ∑ i ∈ s, c i * Wo D (φ i) h := by
  intro E _ _ D ι s c φ hc hb h
  haveI : IsFiniteMeasure ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) := ⟨by
    rw [Measure.restrict_apply_univ]
    have h1 : adeleMeasurePi (ι := Fin 2) ℚ (FS2 ℚ) = 1 :=
      GroundTheory.Automorphic.FourierWhittaker.vecMeasure_vecDomain
    rw [h1]
    exact ENNReal.one_lt_top⟩
  have hψ : Continuous (ψ (F := ℚ)) := continuous_subtype_val.comp continuous_adelicChar
  have hn : Continuous (nE D : (Fin 2 → A ℚ) → GL (Fin 2) (A E)) :=
    UpperTheory.ConvolutionTheory.R2.Pp.cont_n.comp (D.continuous_mkE' (continuous_apply 0) (continuous_apply 1))
  have hi : ∀ i, Integrable (fun u : Fin 2 → A ℚ => φ i (nE D u * h) * ψ (u 1))
      ((adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ)) := by
    intro i
    obtain ⟨B, hB⟩ := hb i
    refine Integrable.of_bound (C := B)
      (((hc i).comp (hn.mul continuous_const)).mul
        (hψ.comp (continuous_apply 1))).aestronglyMeasurable ?_
    refine ae_of_all _ fun u => ?_
    rw [norm_mul, show ‖ψ (u 1)‖ = 1 from Circle.norm_coe _, mul_one]
    exact hB _
  have e : ∀ u : Fin 2 → A ℚ, (∑ i ∈ s, c i * φ i (nE D u * h)) * ψ (u 1) =
      ∑ i ∈ s, c i * (φ i (nE D u * h) * ψ (u 1)) := fun u => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
  simp only [Wo, e]
  rw [integral_finset_sum _ fun i _ => (hi i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentMulEqAdditiveCharMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ), Pp.Lf f → ∀ (v : Fin 2 → A ℚ) (h : GL (Fin 2) (A E)),
        Wo D f (nE D v * h) = ψ (-(v 1)) * Wo D f h := by
  intro E _ _ D f hf v h
  have hadd : ∀ u w : Fin 2 → A ℚ, nE D (u + w) = nE D u * nE D w := fun u w => by
    simp only [nE, Pi.add_apply, D.mkE_add, Pp.n_add]
  let G : (Fin 2 → A ℚ) → ℂ := fun u => f (nE D u * h) * ψ (u 1)
  have hper : ∀ ξ ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x := by
    intro ξ hξ x
    obtain ⟨η, rfl⟩ := GroundTheory.Automorphic.FourierWhittaker.mem_vecLattice.1 hξ
    have e1 : D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1) =
        rt (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ) + D.mkE (x 0) (x 1) := by
      rw [D.mkE_add, D.mkE_rt]
    change f (gl (nU (D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1))) * h) * ψ (rt (η 1) + x 1) =
      f (gl (nU (D.mkE (x 0) (x 1))) * h) * ψ (x 1)
    rw [e1, hf.per, Pp.ψ_add, Pp.ψ_rt, one_mul]
  have key : ∫ u in FS2 ℚ, G (u + v) ∂(adeleMeasurePi ℚ) = ∫ u in FS2 ℚ, G u ∂(adeleMeasurePi ℚ) :=
    GroundTheory.Automorphic.FourierWhittaker.setIntegral_comp_add v hper
  have pt : ∀ u : Fin 2 → A ℚ, f (nE D u * (nE D v * h)) * ψ (u 1) = ψ (-(v 1)) * G (u + v) := by
    intro u
    have e2 : ψ (u 1) = ψ (-(v 1)) * ψ ((u + v) 1) := by
      rw [← Pp.ψ_add]
      congr 1
      simp only [Pi.add_apply]
      ring
    change _ = ψ (-(v 1)) * (f (nE D (u + v) * h) * ψ ((u + v) 1))
    rw [hadd, mul_assoc, e2]
    ring
  simp only [Wo, pt]
  rw [integral_const_mul]
  exact congrArg _ key
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentTranslateOfInfiniteComponentZe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.whittaker_unipotent_translate_of_infinite_component_zero :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ), Continuous φ → (∀ γ g, φ (ratGL E 2 γ * g) = φ g) → ∀ x : A ℚ, x.1 = 0 → ∀ (y : (A ℚ)ˣ) (X : GL (Fin 2) (Cinf E)), Wo D (fun g => φ (g * nu D x)) (em E (aE y) * infGL E 2 X) = ψ (-((y : A ℚ) * x)) * Wo D φ (em E (aE y) * infGL E 2 X) := by
  intro E _ _ _ D φ _ hL x hx y X
  have hfst : (AdeleBaseChange.adeleMap ℚ E x).1 = 0 := by
    obtain ⟨c1, c2⟩ := x
    obtain rfl : c1 = 0 := hx
    exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E))
  have h0 : pInf E (D.mkE 0 x) = 0 := by
    have h1 : (D.mkE 0 x).1 = 0 := by
      have e : D.mkE 0 x = AdeleBaseChange.adeleMap ℚ E x * rt D.θ := by
        simp only [Dat.mkE, map_zero, zero_add]
      rw [e]
      change (AdeleBaseChange.adeleMap ℚ E x).1 * _ = 0
      rw [hfst, zero_mul]
    change (infEq E).symm (D.mkE 0 x).1 = 0
    rw [h1]
    exact map_zero _
  have hk : GeneralLinearGroup.map (pInf E) (Xg.nu D x) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change pInf E ((!![1, D.mkE 0 x; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j
    fin_cases i <;> fin_cases j <;> simp [h0]
  have hc : infGL E 2 X * Xg.nu D x = Xg.nu D x * infGL E 2 X := by
    have e := infGL_mul_finGL (Xg.nu D x)
    rw [hk, map_one, one_mul] at e
    rw [← e]
    exact infGL_comm X _
  rw [Nz.Wo_right, mul_assoc, hc, ← mul_assoc, Xg.nu, Nz.em_conj, mul_assoc, Nz.Wo_shift D hL]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ZetaIntegralEqZeroOfMemMaximalCompactNotMemLevel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem loc_dv {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {c d z n : K}
    (hc : w c ≤ 1) (hd : w d ≤ 1) (hn : w n ≤ 1) (h0 : w (z * c) ≤ w n) (h1 : w (z * d - 1) ≤ w n) : w c ≤ w n := by
  rcases lt_or_eq_of_le hn with hlt | heq
  · have h2 : w (z * d - 1) < w 1 := by rw [map_one]; exact h1.trans_lt hlt
    have h3 : w (z * d) = 1 := by
      have e : z * d = (z * d - 1) + 1 := by ring
      rw [e, Valuation.map_add_eq_of_lt_right w h2, map_one]
    have h4 : 1 ≤ w z := by
      rw [map_mul] at h3
      calc (1 : Γ) = w z * w d := h3.symm
        _ ≤ w z * 1 := mul_le_mul' le_rfl hd
        _ = w z := mul_one _
    calc w c = 1 * w c := (one_mul _).symm
      _ ≤ w z * w c := mul_le_mul' h4 le_rfl
      _ = w (z * c) := (map_mul _ _ _).symm
      _ ≤ w n := h0
  · rw [heq]
    exact hc

private theorem nat_le_one (v : H.P ℚ) (N : ℕ) : Valued.v (N : H.Kv v) ≤ 1 := by
  have h : (N : H.Kv v) ∈ v.adicCompletionIntegers ℚ := natCast_mem _ N
  exact h

theorem UpperTheory.zeta_integral_eq_zero_of_mem_maximal_compact_not_mem_level :
    ∀ (N : ℕ), 0 < N → ∀ (p : MvPolynomial (Fin 2) ℂ) (s : ℂ), ∀ k ∈ KK ℚ, k ∉ SS N → Zr N p s k = 0 := by
  intro N _ p s k hk hkS
  have hz : ∀ z : IdeleGroup ℚ, (PhiN N p fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) = 0 := by
    intro z
    unfold PhiN
    rw [if_neg]
    intro h
    apply hkS
    intro v
    obtain ⟨h0, h1⟩ := h v
    have hint : ∀ i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun i j => hk.2 v i j
    have e0 : H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 0) = H.cp v ((z : (A ℚ)ˣ) : A ℚ) * H.cp v (k 1 0) := map_mul _ _ _
    have e1 : H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 1 - 1) = H.cp v ((z : (A ℚ)ˣ) : A ℚ) * H.cp v (k 1 1) - 1 := by
      rw [map_sub, map_one]
      exact congrArg (· - 1) (map_mul _ _ _)
    have h0' : Valued.v (H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 0)) ≤ Valued.v (N : H.Kv v) := h0
    have h1' : Valued.v (H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 1 - 1)) ≤ Valued.v (N : H.Kv v) := h1
    rw [e0] at h0'
    rw [e1] at h1'
    exact loc_dv Valued.v (hint 1 0) (hint 1 1) (nat_le_one v N) h0' h1'
  simp only [Zr, hz, zero_mul, MeasureTheory.integral_zero]
end

