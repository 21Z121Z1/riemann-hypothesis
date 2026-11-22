import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.Intersections.JacMinorC
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.StatementsGluing
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogIdealChain
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinRestrictionPoints
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreMoment
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagFibreMoment

theorem coeff_momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) (m : Fin 3 →₀ ℕ) :
    coeff m (momentPoly μ w Q) = ∫ p, w p * coeff m Q p ∂μ := by
  rw [momentPoly, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h]
    simp

theorem momentPoly_sum {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ) (s : Finset ι)
    (Q : ι → MvPolynomial (Fin 3) (Ω → ℝ)) (hQ : ∀ i ∈ s, ∀ m, Integrable (fun p => w p * coeff m (Q i) p) μ) :
    momentPoly μ w (∑ i ∈ s, Q i) = ∑ i ∈ s, momentPoly μ w (Q i) := by
  ext m
  rw [coeff_momentPoly, coeff_sum, coeff_sum]
  simp only [coeff_momentPoly, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => hQ i hi m

theorem continuous_coeff_aeval (Q : MvPolynomial (Fin 2) ℝ) (m : Fin 3 →₀ ℕ) :
    Continuous (coeff m (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] Q)) := by
  set φ : C(S2 × S2, ℝ) →ₐ[ℝ] (S2 × S2 → ℝ) := ContinuousMap.coeFnAlgHom (α := S2 × S2) (A := ℝ) ℝ
  set v : Fin 2 → MvPolynomial (Fin 3) C(S2 × S2, ℝ) :=
    ![∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.fst),
      ∑ i, X i * C ((FibreLocal.coordS i).comp ContinuousMap.snd)]
  have hv : ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd] = fun r => mapAlgHom φ (v r) := by
    funext r
    fin_cases r
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, v, dotPoly, mapAlgHom_apply, map_sum, map_mul, map_X, map_C]
      rfl
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, v, dotPoly, mapAlgHom_apply, map_sum,
        map_mul, map_X, map_C]
      rfl
  rw [hv, ← comp_aeval, AlgHom.comp_apply, mapAlgHom_apply, coeff_map]
  exact (coeff m (aeval v Q)).continuous

theorem sum_words (k : ℕ) :
    ∑ i ∈ Finset.range k, ((X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) : MvPolynomial (Fin 2) ℝ) =
      gPoly k := by
  rw [FibreLocal.gPoly_eq, FlagBundles.gKernel]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  rw [show 2 * k - 2 * i = (2 * k - 1 - 2 * i) + 1 by omega, pow_succ, pow_succ]
  ring

theorem sum_diagWordMomentPoly (k : ℕ) :
    ∑ i ∈ Finset.range k, diagWordMomentPoly k i = fibreMomentPoly k := by
  simp only [diagWordMomentPoly]
  rw [← momentPoly_sum _ _ _ _ fun i _ m =>
    FibreLocal.integrable_mul _ (continuous_coeff_aeval _ m)]
  rw [← map_sum, ← map_sum, ← map_sum, sum_words]
  rfl

theorem fibreMomentPoly_eq (k : ℕ) :
    fibreMomentPoly k = C (-kappa k) * (∑ i, X i ^ 2) ^ (k - 1) := by
  have h := FibreLocal.proof.2.1 k (MvPolynomial (Fin 3) ℝ) X
  rwa [aeval_X_left_apply, MvPolynomial.algebraMap_eq] at h

theorem proof (h : DiagFibreFubini.Statement) : DiagFibreMoment.Statement := by
  intro D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  obtain ⟨Λ, hw, hp⟩ := h D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  rw [Finset.sum_congr rfl fun i hi => hw i (Finset.mem_range.1 hi), ← Finset.mul_sum, ← map_sum,
    sum_diagWordMomentPoly, fibreMomentPoly_eq, hp, FibreLocal.pushMomentPoly_eq k hk, C_mul', map_smul,
    map_neg, smul_eq_mul]
  ring

end DiagFibreMoment

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial
open scoped Matrix

theorem frame_matrix_det_ne_zero {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (Matrix.of fun j l : Fin n => b j l).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  apply hv
  have hsum : ∑ j, v j • b j = 0 := by
    ext l
    have := congrFun hvM l
    simpa [Matrix.vecMul, dotProduct, mul_comm] using this
  have hli := Fintype.linearIndependent_iff.mp b.toBasis.linearIndependent v (by simpa using hsum)
  funext j
  exact hli j

theorem FrameJacobianGeneric.proof (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : FrameJacobianGeneric.Statement := by
  classical
  intro n d J hJ hd b
  have := hJ
  set K := FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)
  let π : MvPolynomial (Fin n) ℂ →+* K :=
    (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) K).comp (Ideal.Quotient.mk J)
  have hπ : ∀ f, π f = 0 ↔ f ∈ J := by
    intro f
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact_mod_cast h1
  obtain ⟨t, G, hG⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  set r := Fintype.card (Fin n) - d with hr
  obtain ⟨a, c, hac⟩ := IndefiniteRowSideFullHecke.Inter.exists_jacobian_minor_not_mem_charZero J G hG d hd
  have hrn : r = n - d := by rw [hr, Fintype.card_fin]
  have hGJ : ∀ i, G i ∈ J := fun i => hG ▸ Ideal.subset_span ⟨i, rfl⟩
  let V : Matrix (Fin r) (Fin n) K := Matrix.of fun i l => π (pderiv l (G (a i)))
  let N : Matrix (Fin n) (Fin n) K := Matrix.of fun l j => π (C (b j l))
  let W : Matrix (Fin r) (Fin n) K := Matrix.of fun i j => π (frameDeriv b j (G (a i)))
  have hW : W = V * N := by
    ext i j
    simp [W, V, N, frameDeriv, Matrix.mul_apply, map_sum, mul_comm]
  have hVc : (V.submatrix id c).det ≠ 0 := by
    have : V.submatrix id c = π.mapMatrix (Matrix.of fun i j => pderiv (c j) (G (a i))) := by
      ext i j
      rfl
    rw [this, ← RingHom.map_det]
    exact fun h => hac ((hπ _).mp h)
  have hN : N.det ≠ 0 := by
    have : N = π.mapMatrix ((C : ℂ →+* MvPolynomial (Fin n) ℂ).mapMatrix
        (Matrix.of fun j l : Fin n => b j l)ᵀ) := by
      ext l j
      rfl
    rw [this, ← RingHom.map_det, ← RingHom.map_det, Matrix.det_transpose]
    intro h
    rw [hπ] at h
    have hu : IsUnit (C (Matrix.of fun j l : Fin n => b j l).det : MvPolynomial (Fin n) ℂ) :=
      (isUnit_iff_ne_zero.mpr (frame_matrix_det_ne_zero b)).map C
    exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  have hVinj : ∀ x : Fin r → K, x ᵥ* V = 0 → x = 0 := by
    intro x hx
    apply Matrix.eq_zero_of_vecMul_eq_zero hVc
    ext j
    simpa [Matrix.vecMul, dotProduct] using congrFun hx (c j)
  have hWinj : ∀ x : Fin r → K, Wᵀ *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.mulVec_transpose, hW, ← Matrix.vecMul_vecMul] at hx
    exact hVinj x (Matrix.eq_zero_of_vecMul_eq_zero hN hx)
  obtain ⟨col, hcol⟩ := ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero Wᵀ hWinj
  have hcol' : (W.submatrix id col).det ≠ 0 := by
    rwa [← Matrix.det_transpose, Matrix.transpose_submatrix]
  have hinj : Function.Injective col := by
    intro i i' h
    by_contra hne
    apply hcol
    apply Matrix.det_zero_of_row_eq hne
    funext k
    simp [h]
  let I₀ : Finset (Fin n) := (Finset.univ.image col)ᶜ
  have hmem : ∀ j, j ∈ Set.range col ↔ j ∉ I₀ := by
    intro j
    simp [I₀]
  let e : Fin r ≃ {j // j ∉ I₀} :=
    (Equiv.ofInjective col hinj).trans (Equiv.subtypeEquivRight hmem)
  have he : ∀ i, (e i : Fin n) = col i := fun i => rfl
  let f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ := fun k => G (a (e.symm k))
  have hli : LinearIndependent K (fun i => genericGradient J (G (a i))) := by
    rw [Fintype.linearIndependent_iff]
    intro x hx
    have : x ᵥ* V = 0 := by
      rw [Matrix.vecMul_eq_sum]
      exact hx
    simpa using congrFun (hVinj x this)
  have hspan : Submodule.span K (Set.range (genericGradient J ∘ f)) =
      Submodule.span K (genericGradient J '' (J : Set _)) := by
    have hrange : Set.range (genericGradient J ∘ f) =
        Set.range (fun i => genericGradient J (G (a i))) := by
      ext v
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨e.symm k, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp [f]⟩
    rw [hrange]
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨G (a i), hGJ _, rfl⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
      exact (hR n d J hd).trans (by simp)
  obtain ⟨s, hsJ, hs⟩ := hC n J {j // j ∉ I₀} f (fun k => hGJ _) hspan
  refine ⟨I₀, f, s, ?_, fun k => hGJ _, hsJ, ?_, hs⟩
  · rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fin]
    omega
  · intro hdet
    rw [← hπ, frameJacobianDet, RingHom.map_det, ← Matrix.det_submatrix_equiv_self e] at hdet
    apply hcol'
    convert hdet using 2
    ext i i'
    simp [f, W, he]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuFrameExists
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

theorem MuFrameExists.proof (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) :
    MuFrameExists.Statement D H := by
  intro z hz
  choose c hc using hz.1
  have hx : segreCoord D.y c ≠ 0 := HermMetricEq.segreCoord_ne_zero hz hc
  obtain ⟨m, f, cc, hf, hcc, hsum, hdat⟩ := H.locally c hx
  choose vf hvf using fun l =>
    IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc (hf l)
  choose vc hvc using fun l =>
    IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hc (hcc l)
  have hS : IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt D.y (∑ l, cc l * f l) z (∑ l, vc l * vf l) :=
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.sum _ fun l _ => (hvc l).mul (hvf l)
  rw [hsum] at hS
  have h1 : (∑ l, vc l * vf l) = 1 :=
    IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hz hS IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one
  have hex : ∃ l, vf l ≠ 0 := by
    by_contra hne
    simp only [not_exists, not_not] at hne
    simp [hne] at h1
  obtain ⟨l, hl⟩ := hex
  obtain ⟨b, hb, u, hu, heq⟩ := hdat l
  exact ⟨⟨c, f l, ⟨hc, vf l, HermMetricEq.isValueAt_iff.2 (hvf l), hl⟩, b, hb, u, hu, heq⟩⟩

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PNefAddBlock
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

namespace NefAddBlock

section Reduction

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]

omit [∀ k, Fintype (ι k)] in

theorem red_component (f : NumbersDVR.MRing ι ℤ) (b : K → ℕ) :
    Bridge.GeoNum.red p (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b (Bridge.GeoNum.red p f) := by
  ext d
  simp only [Bridge.GeoNum.red, coeff_map, coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

theorem isMultiProjPrime_comap_red {Q : Ideal (NumbersDVR.MRing ι (ZMod p))}
    (hQ : NumbersDVR.IsMultiProjPrime Q) :
    Geo.IsMultiProjPrime (Q.comap (Bridge.GeoNum.red p)) := by
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ _, ?_, (Bridge.GeoNum.isRelevant_comap_iff p Q).mpr hQ.relevant⟩
  rw [← Bridge.isMultiHomogIdeal_iff]
  intro f hf b
  rw [Ideal.mem_comap, red_component]
  exact hQ.multiHomog _ hf b

theorem map_red {W : Ideal (Geo.MRing ι)} (hW : Geo.IsMultiProjPrime W)
    (hpW : (C (p : ℤ) : Geo.MRing ι) ∈ W) (n : ℕ)
    (hdim : ringKrullDim (Geo.MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    NumbersDVR.IsMultiProjPrime (W.map (Bridge.GeoNum.red p)) ∧
      FieldNumbers.relDim (W.map (Bridge.GeoNum.red p)) = ((n : ℕ) : WithBot (WithTop ℤ)) := by
  have hker : RingHom.ker (Bridge.GeoNum.red (ι := ι) p) ≤ W := by
    rw [Bridge.GeoNum.ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpW
  have hcm : (W.map (Bridge.GeoNum.red p)).comap (Bridge.GeoNum.red p) = W :=
    Bridge.GeoNum.comap_map_eq p hker
  have : W.IsPrime := hW.1
  refine ⟨⟨Ideal.map_isPrime_of_surjective (Bridge.GeoNum.red_surjective p) hker, ?_, ?_⟩, ?_⟩
  · rw [Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, hWS⟩ := hW.2.1
    refine ⟨Bridge.GeoNum.red p '' S, ?_, by rw [hWS, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨b, hb⟩ := hS f hf
    exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [← Bridge.GeoNum.isRelevant_comap_iff p, hcm]
    exact hW.2.2
  · rw [FieldNumbers.CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p (W.map (Bridge.GeoNum.red p)))
    rw [hcm] at this
    exact this.symm

end Reduction

theorem rename_mem_mCoordIdeal {K K' : Type} [Fintype K] [Fintype K'] (j : K ↪ K')
    {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω']
    (y : (Σ k, ι' (j k)) → Ω) (Y : (Σ k', ι' k') → Ω')
    (hY : ∀ k i, Y ⟨j k, i⟩ = algebraMap Ω Ω' (y ⟨k, i⟩))
    {f : Geo.MRing (fun k => ι' (j k))} (hf : f ∈ Geo.mCoordIdeal y) :
    rename (FieldNumbers.blockIncl j ι') f ∈ Geo.mCoordIdeal Y := by
  let φ : MvPolynomial K Ω →ₐ[ℤ] MvPolynomial K' Ω' :=
    ((rename j).toRingHom.comp (MvPolynomial.map (algebraMap Ω Ω'))).toIntAlgHom
  have e : (Geo.mConeMap Y).comp (rename (FieldNumbers.blockIncl j ι')) =
      φ.comp (Geo.mConeMap y) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨k, i⟩
    simp [φ, Geo.mConeMap, FieldNumbers.blockIncl, hY]
    change _ = (rename j) (MvPolynomial.map (algebraMap Ω Ω')
      ((aeval fun p => C (y p) * X p.fst) (X ⟨k, i⟩)))
    simp
  have h := DFunLike.congr_fun e f
  simp only [AlgHom.comp_apply] at h
  rw [Geo.mCoordIdeal, RingHom.mem_ker] at hf ⊢
  rw [h, hf, map_zero]

theorem proof (hPF : FieldNumbers.ProjectionFormulaDegree.Statement.{0}) : NefAddBlock.Statement := by
  classical
  intro K _ ι _ κ _ Ω Ω' _ _ _ y z a hnef W' hW' hyz hchar hdim
  have hhor : ¬ Geo.IsHorizontal W' := fun h => hchar (by
    unfold Geo.charOf
    rw [(Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mp h]
    rfl)
  set p := Geo.charOf W' with hp_def
  have hp : p.Prime := Geo.charOf_prime hW'.1 hhor
  have : Fact p.Prime := ⟨hp⟩
  have hpW' : (C (p : ℤ) : Geo.MRing (addBlockIdx ι κ)) ∈ W' := Inter.C_charOf_mem W'
  rw [← Bridge.intNum_map_eq_geoNum p 1 W' hW' hpW' hdim (fun _ => addBlockDeg a)]
  obtain ⟨hQ', hQ'd⟩ := map_red p hW' hpW' 1 hdim
  set Q' := W'.map (Bridge.GeoNum.red p) with hQ'_def
  let j : K ↪ Option K := Function.Embedding.some
  have hpull : (fun _ : Fin 1 => FieldNumbers.pullDeg j a) = fun _ => addBlockDeg a := by
    funext _ o
    cases o with
    | none =>
      exact Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ => Option.some_ne_none k hk)
    | some k =>
      exact Option.some_injective _ |>.extend_apply a 0 k
  set Q := FieldNumbers.contractPrime j Q' with hQ_def
  have hQ : NumbersDVR.IsMultiProjPrime Q :=
    FieldNumbers.isMultiProjPrime_contractPrime j (addBlockIdx ι κ) hQ'
  have hle := FieldNumbers.ContractRelDimLe.proof (ZMod p) K (Option K) j (addBlockIdx ι κ) Q' hQ'
  rw [hQ'd] at hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · have h0 := FieldNumbers.ProjectionFormulaContracted.full (ZMod p) K (Option K) j
      (addBlockIdx ι κ) Q' hQ' 1 hQ'd hlt (fun _ => a)
    rw [← hpull, h0]
  · obtain ⟨-, h1⟩ := hPF (ZMod p) K (Option K) j (addBlockIdx ι κ) Q' hQ' 1 hQ'd heq (fun _ => a)
    rw [← hpull, h1]
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    rw [Bridge.GeoNum.intNum_eq_geoNum_comap p 1 Q hQ heq (fun _ => a)]
    let y' : (Σ k, addBlockIdx ι κ (j k)) → Ω := y
    have hnef' : Geo.NefOnFibres (Geo.mCoordIdeal y') a := hnef
    refine hnef' (Q.comap (Bridge.GeoNum.red p)) (isMultiProjPrime_comap_red p hQ) ?_ ?_ ?_
    · intro f hf
      rw [Ideal.mem_comap, hQ_def, FieldNumbers.contractPrime, Ideal.mem_comap, Bridge.GeoNum.red,
        ← map_rename]
      exact Ideal.mem_map_of_mem _ (hyz (rename_mem_mCoordIdeal j y' (addBlockPt y z)
        (fun _ _ => rfl) hf))
    · refine ArakelovGeometry.charOf_ne_zero_of_mem hp.ne_zero ?_
      rw [Ideal.mem_comap, map_natCast, CharP.cast_eq_zero]
      exact Q.zero_mem
    · rw [ringKrullDim_eq_of_ringEquiv (Bridge.GeoNum.quotEquiv p Q)]
      exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff Q 1).mp heq

end NefAddBlock

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictionPointsAllX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts modVec resImage residue ResField)

theorem RestrictionPointsAll.proof : RestrictionPointsAll.Statement := by
  intro S _ K ι Ω _ _ y c p _ hc
  ext z'
  constructor
  · rintro ⟨c₁, hv, P, hP, rfl⟩
    obtain ⟨hz, heq⟩ := RestrictionPoints.main y c p hc c₁ hv P
    exact ⟨_, ⟨c₁, fun k => RestrictionPoints.ne_zero_of_modVec_ne_zero y c p (hv k), _,
      Ideal.comap_isPrime _ _, rfl⟩, hz, heq.symm⟩
  · rintro ⟨_, ⟨c₁, hc₁, q, hq, rfl⟩, hz, rfl⟩
    have hA : ∀ x ∈ chartRingOver S y c₁, x ∈ locIn (chartRingOver S y c) p :=
      fun x hx => hz (RestrictionPoints.mem_locIn_of_mem _ q hx)
    have hv : ∀ k, modVec S y c p ⟨k, c₁ k⟩ ≠ 0 := by
      intro k
      have h1 := RestrictionPoints.mem_locIn_of_mem (chartRingOver S y c) p
        (RestrictionPoints.ratio_mem y c ⟨k, c₁ k⟩)
      rw [← RestrictionPoints.resMap_ratio y c p ⟨k, c₁ k⟩ h1]
      refine RestrictionPoints.resMap_ne_zero_of_inv y c p h1 (div_ne_zero (hc₁ k) (hc k)) ?_
      rw [inv_div]
      exact hA _ (RestrictionPoints.ratio_mem y c₁ ⟨k, c k⟩)
    have hker : RingHom.ker (RestrictionPoints.chartRes y c p hc c₁ hv) ≤ q := by
      intro b hb
      by_contra hbq
      have hb0 : (b : Ω) ≠ 0 := coe_ne_zero_of_notMem y c₁ q hbq
      have hbi : (b : Ω)⁻¹ ∈ locIn (chartRingOver S y c₁) q :=
        (mem_locIn_chart_iff y c₁ q).mpr ⟨1, b, hbq, by simp⟩
      apply RestrictionPoints.resMap_ne_zero_of_inv y c p (hA b b.2) hb0 (hz hbi)
      exact congrArg Subtype.val (RingHom.mem_ker.mp hb)
    have hsurj := RestrictionPoints.chartRes_surjective y c p hc c₁ hv
    have hP : (q.map (RestrictionPoints.chartRes y c p hc c₁ hv)).IsPrime :=
      Ideal.map_isPrime_of_surjective hsurj hker
    have hcq : (q.map (RestrictionPoints.chartRes y c p hc c₁ hv)).comap
        (RestrictionPoints.chartRes y c p hc c₁ hv) = q := by
      rw [Ideal.comap_map_of_surjective _ hsurj]
      exact sup_eq_left.mpr hker
    obtain ⟨-, heq⟩ := RestrictionPoints.main y c p hc c₁ hv
      (q.map (RestrictionPoints.chartRes y c p hc c₁ hv))
    rw [hcq] at heq
    exact ⟨c₁, hv, _, hP, heq⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotDevissageX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

theorem SnapperFinite.closed : SnapperFinite.Statement.{u, v, w} :=
  SnapperFinite.proof Extension.proof Extension.proof TwistTilde.proof TwistTilde.proof TildeShift.proof
    (TildeFiniteE.proof SerreFinite.full)

theorem SnapperSubquotFinite.closed : SnapperSubquotFinite.Statement.{u, v, w} :=
  SnapperSubquotFinite.proof SnapperFinite.closed

theorem SnapperQuotAdd.closed : SnapperQuotAdd.Statement.{u, v, w} :=
  SnapperQuotAdd.proof SnapperSubquotFinite.closed

theorem SnapperQuotDevissage.closed : SnapperQuotDevissage.Statement.{u, v, w} :=
  SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof SnapperQuotAdd.closed SubFamilyTwist.proof

end

end GroundTheory.Heights₂.Heights.Kleiman
end

