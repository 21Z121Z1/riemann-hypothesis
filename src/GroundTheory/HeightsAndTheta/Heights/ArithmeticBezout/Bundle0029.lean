import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0077
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LengthLocalizedModuleQuotient
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

namespace VerticalPartMultiplicity

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk Xc)

theorem length_localizedModule_quotient {A : Type*} [CommRing A] (K W : Ideal A) [W.IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ K)) =
      Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) := by
  let g := Submodule.toLocalizedQuotient' (Localization.AtPrime W) W.primeCompl
    (Algebra.linearMap A (Localization.AtPrime W)) K
  let e := (IsLocalizedModule.linearEquiv W.primeCompl g
    (LocalizedModule.mkLinearMap W.primeCompl (A ⧸ K))).restrictScalars (Localization.AtPrime W)
  have hK : Submodule.localized' (Localization.AtPrime W) W.primeCompl
      (Algebra.linearMap A (Localization.AtPrime W)) K = K.map (algebraMap A (Localization.AtPrime W)) := by
    rw [Submodule.localized'_eq_span]
    rfl
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ hK).length_eq

theorem length_self_eq_of_ringEquiv {Q Q' : Type*} [CommRing Q] [CommRing Q'] (τ : Q ≃+* Q') :
    Module.length Q Q = Module.length Q' Q' := by
  letI := RingHomInvPair.of_ringEquiv τ
  letI := RingHomInvPair.symm (↑τ : Q →+* Q') (τ.symm : Q' →+* Q)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap τ.toSemilinearEquiv)]

theorem localMult_map_equiv {A B : Type*} [CommRing A] [CommRing B] (Ψ : A ≃+* B) (K W : Ideal A) :
    localMult (K.map (Ψ : A →+* B)) (W.map (Ψ : A →+* B)) = localMult K W := by
  classical
  have hWc : (W.map (Ψ : A →+* B)).comap (Ψ : A →+* B) = W := by
    rw [Ideal.map_comap_of_equiv]
    ext x
    simp [Ideal.mem_comap]
  by_cases hW : W.IsPrime
  · haveI := hW
    haveI hW' : (W.map (Ψ : A →+* B)).IsPrime := Ideal.map_isPrime_of_equiv _
    have H : W.primeCompl.map Ψ.toMonoidHom = (W.map (Ψ : A →+* B)).primeCompl := by
      ext x
      rw [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.map_comap_of_equiv, Ideal.mem_comap]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Ideal.mem_primeCompl_iff] at hy
        simpa using hy
      · intro hx
        exact ⟨Ψ.symm x, (Ideal.mem_primeCompl_iff).mpr hx, by simp⟩
    let σ : Localization.AtPrime W ≃+* Localization.AtPrime (W.map (Ψ : A →+* B)) :=
      IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime W)
        (Localization.AtPrime (W.map (Ψ : A →+* B))) Ψ H
    have hIJ : (K.map (Ψ : A →+* B)).map (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B)))) =
        (K.map (algebraMap A (Localization.AtPrime W))).map (σ : _ →+* _) := by
      rw [Ideal.map_map, Ideal.map_map]
      congr 1
      ext x
      exact (IsLocalization.ringEquivOfRingEquiv_eq H x).symm
    let τ := Ideal.quotientEquiv _ _ σ hIJ
    have e1 : Module.length (Localization.AtPrime W)
        (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) =
        Module.length (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W)))
          (Localization.AtPrime W ⧸ K.map (algebraMap A (Localization.AtPrime W))) :=
      Module.length_eq_of_surjective (by exact Ideal.Quotient.mk_surjective)
    have e2 : Module.length (Localization.AtPrime (W.map (Ψ : A →+* B)))
        (Localization.AtPrime (W.map (Ψ : A →+* B)) ⧸ (K.map (Ψ : A →+* B)).map
          (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B))))) =
        Module.length (Localization.AtPrime (W.map (Ψ : A →+* B)) ⧸ (K.map (Ψ : A →+* B)).map
            (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B)))))
          (Localization.AtPrime (W.map (Ψ : A →+* B)) ⧸ (K.map (Ψ : A →+* B)).map
            (algebraMap B (Localization.AtPrime (W.map (Ψ : A →+* B))))) :=
      Module.length_eq_of_surjective (by exact Ideal.Quotient.mk_surjective)
    unfold localMult
    rw [dif_pos hW', dif_pos hW, e1, e2, length_self_eq_of_ringEquiv τ]
  · have hW' : ¬ (W.map (Ψ : A →+* B)).IsPrime := fun h => hW (hWc ▸ Ideal.comap_isPrime _ _)
    unfold localMult
    rw [dif_neg hW', dif_neg hW]

variable {n : ℕ}

def eb (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟩, i⟩
    rfl

abbrev ι : ℤ ≃+* 𝓞 ℚ := Rat.ringOfIntegersEquiv.symm

def Ψ (n : ℕ) : MRing (PBlk n) ≃+* MvPolynomial (Fin n) (𝓞 ℚ) :=
  (renameEquiv ℤ (eb n)).symm.toRingEquiv.trans (mapEquiv (Fin n) ι)

theorem Ψ_apply (f : MRing (PBlk n)) :
    Ψ n f = MvPolynomial.map (ι : ℤ →+* 𝓞 ℚ) (rename (eb n).symm f) := rfl

theorem Ψ_C (a : ℤ) : Ψ n (C a) = C (ι a) := by
  rw [Ψ_apply, rename_C, map_C]
  rfl

theorem Ψ_X (i : Fin n) : Ψ n (X ⟨(), i⟩) = X i := by
  rw [Ψ_apply, rename_X, map_X]
  rfl

theorem Ψ_symm_C (a : 𝓞 ℚ) : (Ψ n).symm (C a) = C (ι.symm a) := by
  rw [RingEquiv.symm_apply_eq, Ψ_C, RingEquiv.apply_symm_apply]

theorem Ψ_symm_X (i : Fin n) : (Ψ n).symm (X i) = X ⟨(), i⟩ := by
  rw [RingEquiv.symm_apply_eq, Ψ_X]

theorem ι_apply (a : ℤ) : ι a = (a : 𝓞 ℚ) := map_intCast ι a

theorem Ψ_linForm (u : Fin n → ℤ) :
    Ψ n (IndefiniteRowSideFullHecke.ArithBezout.linForm u) = linForm (fun j => ((u j : ℤ) : 𝓞 ℚ)) := by
  simp [IndefiniteRowSideFullHecke.ArithBezout.linForm, linForm, map_sum, Ψ_C, Ψ_X, ι_apply, Xc]

theorem finIdeal_eq_map (W : Ideal (MRing (PBlk n))) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal W =
      W.map ((renameEquiv ℤ (eb n)).symm.toRingEquiv : MRing (PBlk n) →+* MvPolynomial (Fin n) ℤ) := by
  rw [Ideal.map_comap_of_equiv]
  rfl

theorem minimalPrimes_map_equiv {A B : Type*} [CommRing A] [CommRing B] (Φ : A ≃+* B) (K : Ideal A) :
    (K.map (Φ : A →+* B)).minimalPrimes = Ideal.map (Φ : A →+* B) '' K.minimalPrimes := by
  have hk : RingHom.ker (Φ : A →+* B) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp Φ.injective
  rw [Ideal.minimalPrimes_map_of_surjective Φ.surjective, hk, sup_bot_eq]

theorem comap_C_map (W : Ideal (MRing (PBlk n))) :
    (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
        (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) =
      (W.comap (C : ℤ →+* MRing (PBlk n))).map (ι : ℤ →+* 𝓞 ℚ) := by
  ext a
  rw [Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap, Ideal.map_comap_of_equiv,
    Ideal.mem_comap, Ideal.mem_comap]
  exact Iff.of_eq (congrArg (· ∈ W) (Ψ_symm_C a))

theorem isHorizontal_iff (W : Ideal (MRing (PBlk n))) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W ↔
      (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))).comap
        (C : 𝓞 ℚ →+* MvPolynomial (Fin n) (𝓞 ℚ)) = ⊥ := by
  rw [comap_C_map, ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal]
  constructor
  · intro h
    rw [h, Ideal.map_bot]
  · intro h
    exact (Ideal.map_eq_bot_iff_of_injective ι.injective).mp h

theorem isRelevant_map_iff (W : Ideal (MRing (PBlk n))) :
    IsRelevant (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) ↔
      ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by
  simp only [IsRelevant, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, Ideal.map_comap_of_equiv, Ideal.mem_comap,
    RingEquiv.coe_toRingHom, Ψ_symm_X]
  exact ⟨fun ⟨j, hj⟩ k => ⟨j, by cases k; exact hj⟩, fun h => h ()⟩

theorem localMult_map_eq_multAt (K W : Ideal (MRing (PBlk n))) :
    localMult (K.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)))
        (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) =
      ReciprocityTheory.ChartRestriction.G.Geo.multAt K W := by
  rw [localMult_map_equiv]
  unfold localMult ReciprocityTheory.ChartRestriction.G.Geo.multAt
  by_cases hW : W.IsPrime
  · rw [dif_pos hW, dif_pos hW]
    haveI := hW
    rw [length_localizedModule_quotient]
  · rw [dif_neg hW, dif_neg hW]

theorem finIdeal_comap_C (P : Ideal (MRing (PBlk n))) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).comap (C : ℤ →+* MvPolynomial (Fin n) ℤ) =
      P.comap (C : ℤ →+* MRing (PBlk n)) := by
  ext a
  simp [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, rename_C]

theorem integralModel_genericIdeal (P : Ideal (MRing (PBlk n))) [hP : P.IsPrime]
    (hh : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal P) :
    integralModel (genericIdeal P) = P.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ)) := by
  set J := IndefiniteRowSideFullHecke.ArithBezout.finIdeal P with hJdef
  haveI hJ : J.IsPrime := Ideal.comap_isPrime _ _
  have hJC : J.comap (C : ℤ →+* MvPolynomial (Fin n) ℤ) = ⊥ := by
    rw [hJdef, finIdeal_comap_C]
    exact hh
  have key : (J.map (MvPolynomial.map (Int.castRingHom ℚ))).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) = J := by
    letI : Algebra (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) :=
      MvPolynomial.algebraMvPolynomial
    haveI : IsLocalization ((nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ))
        (MvPolynomial (Fin n) ℚ) := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors ℤ) ℚ
    have hdisj : Disjoint (((nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ) :
        Submonoid (MvPolynomial (Fin n) ℤ)) : Set (MvPolynomial (Fin n) ℤ)) J := by
      refine Set.disjoint_left.mpr fun x hx hxJ => ?_
      obtain ⟨a, ha, rfl⟩ := hx
      have : a ∈ J.comap (C : ℤ →+* MvPolynomial (Fin n) ℤ) := hxJ
      rw [hJC, Ideal.mem_bot] at this
      exact nonZeroDivisors.ne_zero ha this
    have := IsLocalization.under_map_of_isPrime_disjoint
      ((nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ)) (MvPolynomial (Fin n) ℚ) hJ hdisj
    exact this
  have hm : ∀ f : MvPolynomial (Fin n) (𝓞 ℚ),
      MvPolynomial.map (algebraMap (𝓞 ℚ) ℚ) f =
        MvPolynomial.map (Int.castRingHom ℚ) (MvPolynomial.map (ι.symm : 𝓞 ℚ →+* ℤ) f) := by
    intro f
    have e : algebraMap (𝓞 ℚ) ℚ = (Int.castRingHom ℚ).comp (ι.symm : 𝓞 ℚ →+* ℤ) := by
      ext z
      simp [Rat.ringOfIntegersEquiv_apply_coe]
    rw [MvPolynomial.map_map, ← e]
  ext f
  rw [integralModel, Ideal.mem_comap, hm, ← Ideal.mem_comap, genericIdeal, ← hJdef, key, hJdef,
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rfl

theorem reduceMod_map (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (W : Ideal (MRing (PBlk n))) :
    reduceMod v (W.map (Ψ n : MRing (PBlk n) →+* MvPolynomial (Fin n) (𝓞 ℚ))) =
      (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W).map
        (MvPolynomial.map (Int.castRingHom v.asIdeal.ResidueField)) := by
  rw [reduceMod, finIdeal_eq_map, Ideal.map_map, Ideal.map_map]
  congr 1
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
  · simp [Ψ_C, ι_apply]
  · obtain ⟨⟨⟩, i⟩ := p
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
    rw [Ψ_X]
    simp [eb]

theorem absNorm_map_comap_C (W : Ideal (MRing (PBlk n))) :
    Ideal.absNorm ((W.comap (C : ℤ →+* MRing (PBlk n))).map (ι : ℤ →+* 𝓞 ℚ)) =
      ReciprocityTheory.ChartRestriction.G.Geo.charOf W := by
  set g := Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing (PBlk n))) with hg
  have hspan : W.comap (C : ℤ →+* MRing (PBlk n)) = Ideal.span {g} :=
    (Ideal.span_singleton_generator _).symm
  rw [hspan, Ideal.map_span, Set.image_singleton, Ideal.absNorm_span_singleton]
  have h1 : (ι : ℤ →+* 𝓞 ℚ) g = algebraMap ℤ (𝓞 ℚ) g :=
    (eq_intCast _ g).trans (eq_intCast _ g).symm
  rw [h1, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  rfl

end VerticalPartMultiplicity

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaFormulaLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set

open scoped ENNReal

noncomputable section

namespace AreaFormulaLocal

theorem normDet_comp_of_norm {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (Q : F →ₗ[ℝ] G) (hQ : ∀ v, ‖Q v‖ = ‖v‖) (M : E →ₗ[ℝ] F) :
    (Q ∘ₗ M).normDet = M.normDet := by
  rw [LinearMap.normDet_comp,
    show (Q.domRestrict (LinearMap.range M)).normDet = 1 from
      LinearIsometry.normDet_eq_one ⟨Q.domRestrict _, fun v => hQ v⟩, one_mul]

theorem exists_frame {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (W : Submodule ℝ F) {k : ℕ} (hW : finrank ℝ W = k) :
    ∃ (m : ℕ) (c : F →L[ℝ] EuclideanSpace ℝ (Fin k)) (c' : F →L[ℝ] EuclideanSpace ℝ (Fin m)),
      (∀ z, ‖AreaGraphPiece.pairPt (c z) (c' z)‖ = ‖z‖) ∧ ∀ w ∈ W, c' w = 0 := by
  have h1 := (Wᗮ).finrank_add_finrank_orthogonal
  have h2 := W.finrank_add_finrank_orthogonal
  have hK : finrank ℝ (Wᗮᗮ : Submodule ℝ F) = k := by omega
  let b : OrthonormalBasis (Fin k) ℝ (Wᗮᗮ : Submodule ℝ F) :=
    (stdOrthonormalBasis ℝ (Wᗮᗮ : Submodule ℝ F)).reindex (finCongr hK)
  let b' := stdOrthonormalBasis ℝ (Wᗮ : Submodule ℝ F)
  refine ⟨finrank ℝ (Wᗮ : Submodule ℝ F),
    (b.repr.toContinuousLinearEquiv : (Wᗮᗮ : Submodule ℝ F) →L[ℝ] _).comp (Wᗮᗮ).orthogonalProjectionOnto,
    (b'.repr.toContinuousLinearEquiv : (Wᗮ : Submodule ℝ F) →L[ℝ] _).comp (Wᗮ).orthogonalProjectionOnto,
    fun z => ?_, fun w hw => ?_⟩
  · refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [AreaGraphPiece.norm_pairPt_sq, Submodule.norm_sq_eq_add_norm_sq_projection z (Wᗮ), add_comm]
    simp
  · have h0 : (Wᗮ).orthogonalProjectionOnto w = 0 :=
      Submodule.orthogonalProjectionOnto_eq_zero_iff.2 (W.le_orthogonal_orthogonal hw)
    simp [h0]

theorem setLIntegral_image {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (hk : finrank ℝ E = k)
    {B : Set E} (hB : MeasurableSet B) {a : E → EuclideanSpace ℝ (Fin k)}
    {a' : E → E →L[ℝ] EuclideanSpace ℝ (Fin k)} (ha' : ∀ x ∈ B, HasFDerivWithinAt a (a' x) B x)
    (hinj : InjOn a B) (g : EuclideanSpace ℝ (Fin k) → ℝ≥0∞) :
    ∫⁻ y in a '' B, g y ∂(μH[(k : ℝ)]) =
      ∫⁻ x in B, g (a x) *
        ENNReal.ofReal (a' x : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).normDet ∂(μH[(k : ℝ)]) := by
  let R : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) := ((stdOrthonormalBasis ℝ E).reindex (finCongr hk)).repr
  let Rs : EuclideanSpace ℝ (Fin k) →L[ℝ] E := (R.symm.toContinuousLinearEquiv : _ →L[ℝ] E)
  have : (μH[(k : ℝ)] : Measure E).IsAddHaarMeasure := by
    have := isAddHaarMeasure_hausdorffMeasure (E := E)
    rwa [hk] at this
  have himg : a '' B = R '' ((fun x => R.symm (a x)) '' B) := by
    rw [image_image]
    simp
  have hpres : MeasurePreserving R (μH[(k : ℝ)]) (μH[(k : ℝ)]) :=
    R.toIsometryEquiv.measurePreserving_hausdorffMeasure (k : ℝ)
  have hemb : MeasurableEmbedding R := R.toHomeomorph.measurableEmbedding
  rw [himg, ← hpres.setLIntegral_comp_emb hemb,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul (μH[(k : ℝ)]) hB
      (f := fun x => R.symm (a x)) (f' := fun x => Rs.comp (a' x))
      (fun x hx => Rs.hasFDerivAt.comp_hasFDerivWithinAt x (ha' x hx))
      (fun x hx y hy hxy => hinj hx hy (R.symm.injective hxy))]
  refine setLIntegral_congr_fun hB fun x _ => ?_
  have hN : |(Rs.comp (a' x)).det| = (a' x : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).normDet := by
    rw [ContinuousLinearMap.det, ← LinearMap.normDet_eq_abs_det]
    exact normDet_comp_of_norm (Rs : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] E) (fun v => by simp [Rs])
      (a' x : E →ₗ[ℝ] EuclideanSpace ℝ (Fin k))
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [hN, mul_comm]

end AreaFormulaLocal

open AreaFormulaLocal AreaGraphPiece in

theorem AreaFormulaLocal.proof : AreaFormulaLocal.Statement := by
  intro E F _ _ _ _ _ _ _ _ _ _ k hk U f x₀ hU hf hx₀ hinj
  classical
  have hAG : AreaGraph.Statement := AreaGraph.proof
    (AreaGraphBound.proof AreaGraphPiece.proof AreaGraphPartition.proof GraphJacContinuous.proof)
  have hfc : ∀ x ∈ U, ContDiffAt ℝ 1 f x := fun x hx => hf.contDiffAt (hU.mem_nhds hx)
  have hfd : ∀ x ∈ U, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hfc x hx).differentiableAt one_ne_zero).hasFDerivAt

  set D := fderiv ℝ f x₀ with hD
  have hWk : finrank ℝ (LinearMap.range (D : E →ₗ[ℝ] F)) = k := by
    rw [LinearMap.finrank_range_of_inj hinj, hk]
  obtain ⟨m, c, c', hcc, hc'⟩ := exists_frame (LinearMap.range (D : E →ₗ[ℝ] F)) hWk
  let Q : F →ₗ[ℝ] EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
    { toFun := fun z => pairPt (c z) (c' z)
      map_add' := fun z w => by rw [map_add, map_add, pairPt_add]
      map_smul' := fun r z => by rw [map_smul, map_smul, pairPt_smul]; rfl }
  have hQ : ∀ z, ‖Q z‖ = ‖z‖ := hcc

  let a : E → EuclideanSpace ℝ (Fin k) := fun x => c (f x)
  have had : ∀ x ∈ U, HasFDerivAt a (c.comp (fderiv ℝ f x)) x := fun x hx =>
    c.hasFDerivAt.comp x (hfd x hx)
  have hinj0 : Function.Injective ((c.comp D : E →L[ℝ] EuclideanSpace ℝ (Fin k)) :
      E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by
    intro v w hvw
    apply hinj
    have hv : D (v - w) ∈ LinearMap.range (D : E →ₗ[ℝ] F) := ⟨v - w, rfl⟩
    have h0 : c (D (v - w)) = 0 := by
      rw [map_sub, map_sub]
      exact sub_eq_zero.2 hvw
    have hz : D (v - w) = 0 := by
      rw [← norm_eq_zero, ← hcc (D (v - w)), h0, hc' _ hv]
      have hp : pairPt (0 : EuclideanSpace ℝ (Fin k)) (0 : EuclideanSpace ℝ (Fin m)) = 0 := by
        ext i
        rcases i with i | i <;> simp [pairPt]
      rw [hp, norm_zero]
    rwa [map_sub, sub_eq_zero] at hz
  have hdim : finrank ℝ E = finrank ℝ (EuclideanSpace ℝ (Fin k)) := by simp [hk]
  let e0 : E ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (LinearMap.linearEquivOfInjective _ hinj0 hdim).toContinuousLinearEquiv
  have he0 : HasFDerivAt a (e0 : E →L[ℝ] EuclideanSpace ℝ (Fin k)) x₀ := by
    convert had x₀ hx₀ using 1
    exact ContinuousLinearMap.ext fun v => rfl
  have hac : ContDiffAt ℝ 1 a x₀ := c.contDiff.contDiffAt.comp x₀ (hfc x₀ hx₀)

  let φ := hac.toOpenPartialHomeomorph a he0 one_ne_zero
  have hφa : (φ : E → EuclideanSpace ℝ (Fin k)) = a := rfl
  have hx₀φ : x₀ ∈ φ.source := hac.mem_toOpenPartialHomeomorph_source he0 one_ne_zero

  let O : Set (E →L[ℝ] EuclideanSpace ℝ (Fin k)) :=
    range ((↑) : (E ≃L[ℝ] EuclideanSpace ℝ (Fin k)) → E →L[ℝ] EuclideanSpace ℝ (Fin k))
  have hcont : ContinuousOn (fun x => c.comp (fderiv ℝ f x)) U :=
    ((ContinuousLinearMap.compL ℝ E F (EuclideanSpace ℝ (Fin k))) c).continuous.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hU le_rfl)
  have hS : IsOpen (U ∩ (fun x => c.comp (fderiv ℝ f x)) ⁻¹' O) :=
    hcont.isOpen_inter_preimage hU ContinuousLinearEquiv.isOpen
  let V : Set E := φ.source ∩ (U ∩ (fun x => c.comp (fderiv ℝ f x)) ⁻¹' O)
  have hVo : IsOpen V := φ.open_source.inter hS
  have hVU : V ⊆ U := fun x hx => hx.2.1
  have hx₀V : x₀ ∈ V := ⟨hx₀φ, hx₀, e0, rfl⟩
  refine ⟨V, hVo, hx₀V, hVU, fun B hBV hB => ?_⟩

  let T : Set (EuclideanSpace ℝ (Fin k)) := a '' V
  have hTo : IsOpen T := φ.isOpen_image_of_subset_source hVo inter_subset_left
  let h : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) := fun y => c' (f (φ.symm y))
  have hleft : ∀ x ∈ V, φ.symm (a x) = x := fun x hx => φ.left_inv hx.1
  have hhc : ContDiffOn ℝ 1 h T := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨ex, hex⟩ := hx.2.2
    have htgt : a x ∈ φ.target := φ.map_source hx.1
    have hder : HasFDerivAt φ (ex : E →L[ℝ] EuclideanSpace ℝ (Fin k)) (φ.symm (a x)) := by
      rw [hleft x hx, hex]
      exact had x (hVU hx)
    have hcd : ContDiffAt ℝ 1 φ (φ.symm (a x)) := by
      rw [hleft x hx]
      exact c.contDiff.contDiffAt.comp x (hfc x (hVU hx))
    have hψ := φ.contDiffAt_symm htgt hder hcd
    have hf' : ContDiffAt ℝ 1 f (φ.symm (a x)) := by
      rw [hleft x hx]
      exact hfc x (hVU hx)
    exact (c'.contDiff.contDiffAt.comp _ (hf'.comp _ hψ)).contDiffWithinAt
  have hQf : ∀ x ∈ V, Q (f x) = realGraphPt h (a x) := by
    intro x hx
    show pairPt (c (f x)) (c' (f x)) = pairPt (a x) (c' (f (φ.symm (a x))))
    rw [hleft x hx]

  have hJ : ∀ x ∈ V, areaJacobian (fderiv ℝ f x : E →ₗ[ℝ] F) =
      graphJac (fderiv ℝ h (a x) : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) *
        ((c.comp (fderiv ℝ f x) : E →L[ℝ] EuclideanSpace ℝ (Fin k)) :
          E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).normDet := by
    intro x hx
    have hhd : HasFDerivAt h (fderiv ℝ h (a x)) (a x) :=
      ((hhc.contDiffAt (hTo.mem_nhds ⟨x, hx, rfl⟩)).differentiableAt one_ne_zero).hasFDerivAt
    have h1 : HasFDerivAt (fun z => c' (f z)) (c'.comp (fderiv ℝ f x)) x :=
      c'.hasFDerivAt.comp x (hfd x (hVU hx))
    have h2 : HasFDerivAt (fun z => h (a z)) ((fderiv ℝ h (a x)).comp (c.comp (fderiv ℝ f x))) x :=
      hhd.comp x (had x (hVU hx))
    have heq : c'.comp (fderiv ℝ f x) = (fderiv ℝ h (a x)).comp (c.comp (fderiv ℝ f x)) :=
      h1.unique (h2.congr_of_eventuallyEq (Filter.eventually_of_mem (hVo.mem_nhds hx)
        fun z hz => by simp only [h, hleft z hz]))
    have hlin : Q ∘ₗ (fderiv ℝ f x : E →ₗ[ℝ] F) =
        graphLin (fderiv ℝ h (a x)) ∘ₗ ((c.comp (fderiv ℝ f x) : E →L[ℝ] EuclideanSpace ℝ (Fin k)) :
          E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by
      refine LinearMap.ext fun v => ?_
      have hv := congrArg (fun M : E →L[ℝ] EuclideanSpace ℝ (Fin m) => M v) heq
      simp only [ContinuousLinearMap.comp_apply] at hv
      show pairPt (c (fderiv ℝ f x v)) (c' (fderiv ℝ f x v)) =
        pairPt (c (fderiv ℝ f x v)) (fderiv ℝ h (a x) (c (fderiv ℝ f x v)))
      rw [hv]
    rw [SheetImageAreaSet.areaJacobian_eq_normDet, ← normDet_comp_of_norm Q hQ, hlin,
      LinearMap.normDet_comp_of_finrank_eq _ _ hdim, normDet_graphLin]

  have hBV' : B ⊆ φ.source := fun x hx => (hBV hx).1
  have hinjB : InjOn a B := φ.injOn.mono hBV'
  have haB : MeasurableSet (a '' B) :=
    hB.image_of_continuousOn_injOn
      (fun x hx => (had x (hVU (hBV hx))).continuousAt.continuousWithinAt) hinjB
  have hBT : a '' B ⊆ T := image_mono hBV
  have hQi : Isometry Q := AddMonoidHomClass.isometry_of_norm Q hQ
  calc μH[(k : ℝ)] (f '' B) = μH[(k : ℝ)] (Q '' (f '' B)) :=
        (hQi.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg k)) _).symm
    _ = μH[(k : ℝ)] (realGraphPt h '' (a '' B)) := by
        rw [image_image, image_image]
        exact congrArg _ (image_congr fun x hx => hQf x (hBV hx))
    _ = ∫⁻ y in a '' B, ENNReal.ofReal (graphJac (fderiv ℝ h y :
          EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)]) :=
        hAG k m T h hTo hhc (a '' B) hBT haB
    _ = ∫⁻ x in B, ENNReal.ofReal (graphJac (fderiv ℝ h (a x) :
          EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
          ENNReal.ofReal ((c.comp (fderiv ℝ f x) : E →L[ℝ] EuclideanSpace ℝ (Fin k)) :
            E →ₗ[ℝ] EuclideanSpace ℝ (Fin k)).normDet ∂(μH[(k : ℝ)]) :=
        setLIntegral_image hk hB (fun x hx => (had x (hVU (hBV hx))).hasFDerivWithinAt) hinjB _
    _ = _ := by
        refine setLIntegral_congr_fun hB fun x hx => ?_
        rw [hJ x (hBV hx), ENNReal.ofReal_mul (by unfold graphJac; exact Real.sqrt_nonneg _)]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeChartIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

def ConeChartIntegrable.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (P : Ideal (MRing (PBlk n))) (u : Fin n → ℂ),
    IsArithVar P (e + 1) → (∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm u ∉ W) →
      IntegrableOn (fun y => fsLog h u (h.pointOf y))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ q ∈ complexFibreIdeal P, eval (h.pointOf y) q = 0}
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))

end GroundTheory.Heights₂.Heights
end
end

