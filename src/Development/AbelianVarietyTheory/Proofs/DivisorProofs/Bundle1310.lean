import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0288
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFlagSmoothArithmeticStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_flag_smooth_arithmetic : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)), SmoothOfRelativeDimension (Nat.card (CellVar a l)) (str a l) ∧ topologicalKrullDim (Part a l) = (Nat.card (CellVar a l) + 1 : ℕ) ∧ GlobalTheory.IsArithVar (str a l) (Nat.card (CellVar a l)) := by
  first | exact @GlobalTheory.FlagZ.smooth_dim_isArithVar_part | exact GlobalTheory.FlagZ.smooth_dim_isArithVar_part | (intros; apply GlobalTheory.FlagZ.smooth_dim_isArithVar_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydi
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_poinVol {n : ℕ} (S : Finset (Fin n)) (K : Set (V n)) (hK : IsCompact K)
    (hS : ∀ v ∈ K, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) :
    IntegrableOn (fun v => ∏ a, (poinWt S v a)⁻¹ ^ 2) K := by
  classical
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let g : Fin n → ℂ → ℝ := fun a =>
    if a ∈ S then (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2)
    else (Metric.closedBall (0 : ℂ) R).indicator (fun _ => 1)
  have hg : ∀ a, Integrable (g a) := by
    intro a
    by_cases h : a ∈ S
    · simp only [g, h, if_true]
      exact (integrable_indicator_iff measurableSet_closedBall).2 GlobalTheory.T.integrableOn_poincareAreaDensity_punctured_disc
    · simp only [g, h, if_false]
      exact (integrable_indicator_iff measurableSet_closedBall).2
        (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _))
  have h1 : Integrable (fun x : Fin n → ℂ => ∏ a, g a (x a)) := Integrable.fintype_prod hg
  have h2 := (GlobalTheory.volume_preserving_ofLp_complex (Fin n)).integrable_comp_of_integrable h1
  refine (h2.integrableOn (s := K)).congr_fun ?_ hK.measurableSet
  intro v hv
  simp only [Function.comp]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases h : a ∈ S
  · have : v.ofLp a ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      simpa using hS v hv a h
    simp only [g, h, if_true, poinWt]
    exact Set.indicator_of_mem this _
  · have : v.ofLp a ∈ Metric.closedBall (0 : ℂ) R := by
      simpa using (PiLp.norm_apply_le v a).trans (hR v hv)
    simp only [g, h, if_false, poinWt, inv_one, one_pow]
    exact Set.indicator_of_mem this _

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionFormulaAndChernDegreeOfHeightProjectio
section
namespace GlobalTheory.Published

theorem arDegree_of_heightProjection : HeightProjection → ChernDegreeComplex → ArDegree :=
  fun H H' => ⟨arBirational_of_arProj (GlobalTheory.T.arithInterProjectionFormula_of_heightProjectionFormula H), GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case H'⟩

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeEqIffSameIntegralGLCosetStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLattice_eq_iff_same_integralGL_coset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → ∀ g g' : GLw n w, pullLat w B ψ g = pullLat w B ψ g' → g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w n := by
  first | exact @GlobalTheory.KapOrb.PullInj.main | exact GlobalTheory.KapOrb.PullInj.main | (intros; apply GlobalTheory.KapOrb.PullInj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeMulEqMulLeftImageStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLattice_mul_eq_mulLeftImage : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (h g : GLw n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = h.val *ᵥ ψ y) → pullLat w B ψ (h * g) = GlobalTheory.UnitLemma.mulLat K.O (a : B.A) (pullLat w B ψ g) := by
  first | exact @GlobalTheory.KapOrb.pullLat_mul_eq_mulLat | exact GlobalTheory.KapOrb.pullLat_mul_eq_mulLat | (intros; apply GlobalTheory.KapOrb.pullLat_mul_eq_mulLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeSelfDualOfUnitaryStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLattice_selfDual_of_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → (∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)) → ∀ g ∈ UL n w, GlobalTheory.UnitLemma.IsLat K.O K.E (pullLat w B ψ g) ∧ ∀ y, y ∈ pullLat w B ψ g ↔ ∀ z ∈ pullLat w B ψ g, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  first | exact @GlobalTheory.KapOrb.SDual.pullLat_selfDual | exact GlobalTheory.KapOrb.SDual.pullLat_selfDual | (intros; apply GlobalTheory.KapOrb.SDual.pullLat_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackLatticeStableIffPrincipalCongruenceStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackLattice_stable_iff_principalCongruence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (k : ℕ) (t : K.O), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → u = 1 + algebraMap K.O B.A t * B.g → γ ∈ UL n w → ∀ g ∈ UL n w, ((∀ y ∈ pullLat w B ψ g, B.g * y ∈ pullLat w B ψ g) ↔ g⁻¹ * γ * g ∈ congSet w n k) := by
  first | exact @GlobalTheory.KapCong.pullLat_stable_iff_cong | exact GlobalTheory.KapCong.pullLat_stable_iff_cong | (intros; apply GlobalTheory.KapCong.pullLat_stable_iff_cong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackOfTranslatedStandardLatticeMulIntegralGLStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackOfTranslatedStandardLattice_mul_integralGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (g k : GLw n w), k ∈ GlobalTheory.LFun.KGL w n → pullLat w B ψ (g * k) = pullLat w B ψ g := by
  first | exact @GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL | exact GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL | (intros; apply GlobalTheory.KapOrb.pullLat_mul_of_mem_KGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTri
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EtaInfSign

open GlobalTheory.QuadSymbol

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem mem_normGroup_of_pos (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ)
    (hy : 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion)) :
    y ∈ normGroup (maximalRealSubfield E) E v.Completion := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq (maximalRealSubfield E) E
  rw [mem_normGroup_iff_form b h0 h1]
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hy' : 0 < e y := hy
  refine ⟨e.symm (Real.sqrt (e y)), 0, e.injective ?_⟩
  simp only [map_sub, map_pow, map_mul, map_zero, RingEquiv.apply_symm_apply]
  rw [zero_pow two_ne_zero, mul_zero, sub_zero, Real.sq_sqrt hy'.le]

theorem not_mem_normGroup_of_neg (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ)
    (hy : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion) < 0) :
    y ∉ normGroup (maximalRealSubfield E) E v.Completion := by
  intro hmem
  have hneg : (-y) ∈ normGroup (maximalRealSubfield E) E v.Completion := by
    refine mem_normGroup_of_pos E v (-y) ?_
    rw [Units.val_neg, map_neg]
    exact neg_pos.2 hy
  have h1 : (-1 : (v.Completion)ˣ) ∈ normGroup (maximalRealSubfield E) E v.Completion := by
    have : (-1 : (v.Completion)ˣ) = y * (-y)⁻¹ := by
      rw [inv_neg, mul_neg, mul_inv_cancel]
    rw [this]
    exact mul_mem hmem (inv_mem hneg)
  exact eta_eq_neg_one_iff.1 (GlobalTheory.GalOfCusp.eta_neg_one E v) h1

theorem eta_real (v : InfinitePlace (maximalRealSubfield E)) (y : (v.Completion)ˣ) :
    eta (maximalRealSubfield E) E v.Completion y =
      if 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion)
      then 1 else -1 := by
  split_ifs with h
  · exact eta_eq_one_iff.2 (mem_normGroup_of_pos E v y h)
  · have h0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) (y : v.Completion) ≠ 0 :=
      fun h' => y.ne_zero ((InfinitePlace.Completion.extensionEmbeddingOfIsReal _).injective (h'.trans (map_zero _).symm))
    exact eta_eq_neg_one_iff.2 (not_mem_normGroup_of_neg E v y (lt_of_le_of_ne (not_lt.1 h) h0))

theorem embedding_comp_algebraMap (w : InfinitePlace E) :
    (w.comap (algebraMap (maximalRealSubfield E) E)).embedding =
      w.embedding.comp (algebraMap (maximalRealSubfield E) E) := by
  have hw : w.comap (algebraMap (maximalRealSubfield E) E) =
      InfinitePlace.mk (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) := by
    conv_lhs => rw [← InfinitePlace.mk_embedding w]
    rw [InfinitePlace.comap_mk]
  rw [hw]
  rcases InfinitePlace.embedding_mk_eq (w.embedding.comp (algebraMap (maximalRealSubfield E) E)) with h | h
  · exact h
  · rw [h]
    exact ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal _)

theorem extensionEmbedding_completionMap (w : InfinitePlace E)
    (x : (w.comap (algebraMap (maximalRealSubfield E) E)).Completion) :
    InfinitePlace.Completion.extensionEmbedding w
      (NumberField.LiesOver.completionMap (v := w.comap (algebraMap (maximalRealSubfield E) E)) (w := w) x) =
    ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal _) x : ℝ) : ℂ) := by
  induction x using InfinitePlace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
        NumberField.LiesOver.continuous_completionMap)
      (Complex.continuous_ofReal.comp (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous)
  | ih a =>
    rw [NumberField.LiesOver.completionMap_coe, InfinitePlace.Completion.extensionEmbedding_coe,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe, InfinitePlace.embedding_of_isReal_apply,
      embedding_comp_algebraMap]
    simp [WithAbs.algebraMap_left_apply, WithAbs.algebraMap_right_apply]

theorem unitDir_ofReal (r : ℝ) (hr : r ≠ 0) (u : ℂˣ) (hu : (u : ℂ) = r) :
    GlobalTheory.ConsEta.unitDir u = Units.map (Int.castRingHom ℂ).toMonoidHom (if 0 < r then 1 else -1) := by
  ext
  change (u : ℂ) / (‖(u : ℂ)‖ : ℂ) = _
  rw [hu, Complex.norm_real, Real.norm_eq_abs]
  split_ifs with h
  · rw [abs_of_pos h, div_self (Complex.ofReal_ne_zero.2 hr)]
    simp
  · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) hr), Complex.ofReal_neg, div_neg, div_self (Complex.ofReal_ne_zero.2 hr)]
    simp

end GlobalTheory.EtaInfSign

open GlobalTheory.QuadSymbol in

theorem GlobalTheory.EtaInfSign.quadChar_eq_infSign : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    (∀ v, (b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1) →
    (GlobalTheory.GalOfCusp.quadChar E).1 b = GlobalTheory.ConsEta.infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  intro E _ _ _ b hb
  have hfin : GlobalTheory.IdeleNormChar.finComp b = 1 := funext fun v => Units.ext (hb v)
  have hL : (GlobalTheory.GalOfCusp.quadChar E).1 b = Units.map (Int.castRingHom ℂ).toMonoidHom
      (∏ v : InfinitePlace (maximalRealSubfield E),
        eta (maximalRealSubfield E) E v.Completion (GlobalTheory.IdeleNormChar.infComp b v)) := by
    change Units.map _ (etaProd _ E (GlobalTheory.IdeleNormChar.finComp b) (GlobalTheory.IdeleNormChar.infComp b)) = _
    unfold etaProd
    rw [hfin]
    have h1 : (fun v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) =>
        eta (maximalRealSubfield E) E (v.adicCompletion _) ((1 : FinFam (maximalRealSubfield E)) v)) = fun _ => 1 :=
      funext fun v => eta_eq_one_iff.2 (one_mem _)
    rw [h1, finprod_one, one_mul]
  rw [hL, map_prod, GlobalTheory.ConsEta.infSign, MonoidHom.finset_prod_apply]
  symm
  refine Fintype.prod_equiv (IsCMField.equivInfinitePlace E) _ _ fun w => ?_
  rw [IsCMField.equivInfinitePlace_apply, GlobalTheory.EtaInfSign.eta_real]
  have hv := IsTotallyReal.isReal (w.comap (algebraMap (maximalRealSubfield E) E))
  refine GlobalTheory.EtaInfSign.unitDir_ofReal _ ?_ _ ?_
  · intro h'
    exact (GlobalTheory.IdeleNormChar.infComp b _).ne_zero
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hv).injective (by rw [map_zero]; exact h'))
  · exact GlobalTheory.EtaInfSign.extensionEmbedding_completionMap E w _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientBundleCurvatureFormulaStatement
section
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_bundle_curvature_formula : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V), curv (gramQ H) z ξ η = blockQQ (H z) (curv H z ξ η) + wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η := by
  first | exact @GlobalTheory.GaussQuot.curv_gramQ | exact GlobalTheory.GaussQuot.curv_gramQ | (intros; apply GlobalTheory.GaussQuot.curv_gramQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationWeightedLogNormSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramification_weighted_log_norm_sum : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k'), ∃ (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ), (∀ 𝔓 (z : k), 𝔓.valuation k' (i z) = (π 𝔓).valuation k z ^ ε 𝔓) ∧ ∀ 𝔭, ∃ s : Finset (HeightOneSpectrum (𝓞 k')), (∀ 𝔓, 𝔓 ∈ s ↔ π 𝔓 = 𝔭) ∧ s.Nonempty ∧ (Module.finrank ℚ k : ℝ) * ∑ 𝔓 ∈ s, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) = (Module.finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) := by
  first | exact @GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm | exact GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm | (intros; apply GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFnFamilySmallPullbackBirationalModelStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratFnFamilySmall_pullback_birationalModel : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  first | exact @GlobalTheory.HSNef.smallFam_pull | exact GlobalTheory.HSNef.smallFam_pull | (intros; apply GlobalTheory.HSNef.smallFam_pull <;> assumption)
end

