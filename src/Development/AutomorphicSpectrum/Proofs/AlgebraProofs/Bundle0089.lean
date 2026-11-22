import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0056
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0042
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinDivCycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PJoinIntNum
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0064
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0086
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0088
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0074
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0078
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0076
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0080
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0081
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0041

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPair
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial

open GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial

theorem rootPolyNum : RootPolynomialNumber.Statement := by
  intro O _ _ _ K _ _ ι _ P d N x c G hG hc q L Q hQ a
  have hH : (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q :
      MvPolynomial (Fin (N + q)) ℤ).IsHomogeneous d := by
    have h3 := (hG.rename_isHomogeneous (f := Fin.castAdd q)).mul
      (hQ.rename_isHomogeneous (f := Fin.natAdd N))
    rwa [show c + (d - c) = d by omega] at h3
  have hZ : ⇑(Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
      (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (C a))) = divCycle P (C a) := by
    funext W
    simp [FlagTypings.divCycle_eq]
  have hfin : (Function.support (divCycle P (C a))).Finite := by
    rw [← hZ]
    exact Finsupp.finite_support _
  have hcast : Fin.append x L ∘ Fin.castAdd q = x := by
    funext i
    simp [Fin.append_left]
  have hnat : Fin.append x L ∘ Fin.natAdd N = L := by
    funext j
    simp [Fin.append_right]
  have key : ∀ W : Ideal (MRing ι O), IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
      (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) (specialIdeal W) d (Fin.append x L)
      (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q) =
      ∑ μ ∈ Q.support, Q.coeff μ * classNum x G (classList L μ) W := by
    intro W
    rw [BundleExamples.polyNum_eq_classNum (Fin.append x L) (Equiv.refl _) (Fin.append x L) rfl hH W]
    simp only [Equiv.coe_refl, rename_id_apply]
    rw [plainPolynomialPairNumber.classNum_mul_tail _ L _ hnat]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [plainPairNumber.classNum_rename _ (Fin.castAdd_injective _ _), hcast]
  rw [BundleExamples.vEval_eq, hZ]
  simp only [key, cycEval_eq_sum hfin, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun W _ => ?_
  ring

theorem main : ChernClassOnFlagPair.Statement :=
  ChernClassOnFlagPair.proof
    (JoinPointFlagModel.proof FlagPairCharacterisation.proof JoinPointModel.proof
      JoinPointVerticalDivisor.proof)
    (JoinPointNumbers.proof JoinPointIdeal.proof JoinDivCycle.proof JoinVariety.proof
      JoinIntNum.proof PairNumberJoinLeft.verticalComponentFibre)
    GlobalTheory.T.flag_model_value_independent GlobalTheory.T.flag_model_root_independent plainPolynomialPairNumber.proof rootPolyNum
    (PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute) dividedDifferenceExpansion.proof

end GlobalTheory.CompanionTheory.ChernFlagPairRootPolynomial
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsOrthogonalLocalBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_local_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p q : ℕ) (ℓ : Nat.Primes) (x' : Fin p → D.La), p + q = D.p + D.q → (gramE D x').det ≠ 0 → (∀ j : E →+* ℂ_[ℓ], Real.log ‖j (gramE D x').det‖ = -(p : ℝ) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → ∃ x : Fin p ⊕ Fin q → D.La, x ∘ Sum.inl = x' ∧ IsLocBasis (𝓞 E) ℓ x ∧ ∀ a b, sesq D (x (.inl a)) (x (.inr b)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis | exact GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_orthogonal_local_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMinusConeIntegralIndep
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem log_norm_sub_fsSum_eq {n e : ℕ} (h : HermNorm n) (u : Fin n → ℂ)
    (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) (c z : ℂ)
    (hfin : (fibrePts S π).Finite) (hc : c ≠ 0)
    (hz : z = c * ∏ᶠ y ∈ fibrePts S π, ∑ j, u j * h.pointOf y j) (hz0 : z ≠ 0) :
    Real.log ‖z‖ - fsSum h u S π = Real.log ‖c‖ + ∑ y ∈ hfin.toFinset, Real.log ‖y‖ := by
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin] at hz
  have hprod : ∏ y ∈ hfin.toFinset, ∑ j, u j * h.pointOf y j ≠ 0 :=
    fun h0 => hz0 (by rw [hz, h0, mul_zero])
  have hne := Finset.prod_ne_zero_iff.mp hprod
  have key : ∀ y ∈ hfin.toFinset, fsLog h u (h.pointOf y) =
      Real.log ‖∑ j, u j * h.pointOf y j‖ - Real.log ‖y‖ := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hne _ hy
      show ∑ j, u j * (h.matᵀ *ᵥ (0 : Fin n → ℂ)) j = 0
      simp
    rw [fsLog, ConeFsLog.dualNorm_pointOf,
      Real.log_div (norm_ne_zero_iff.2 (hne y hy)) (norm_ne_zero_iff.2 hy0)]
  rw [fsSum, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_congr rfl key,
    Finset.sum_sub_distrib, hz, norm_mul, norm_prod,
    Real.log_mul (norm_ne_zero_iff.2 hc)
      (Finset.prod_ne_zero_iff.mpr fun y hy => norm_ne_zero_iff.2 (hne y hy)),
    Real.log_prod (fun y hy => norm_ne_zero_iff.2 (hne y hy))]
  ring

theorem defect_eq_of_linForm_notMem : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u u' : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g → linForm u ∉ W → linForm u' ∉ W →
      mahler h e (specFirst g u) - coneIntegral h W e (fsLog h u) =
        mahler h e (specFirst g u') - coneIntegral h W e (fsLog h u') := by
  intro n e δ h W g u u' hW hg hδ hu hu'
  have hq := SpecFirstNe.full ℂ n e W g u hW hg hu
  have hq' := SpecFirstNe.full ℂ n e W g u' hW hg hu'
  have hh := SpecFirstHomog.proof n e δ g u hδ
  have hh' := SpecFirstHomog.proof n e δ g u' hδ
  obtain ⟨hΓ0, hΓ⟩ := GlobalTheory.T.gaussian_matrix_measure_pos_finite (e + 1) n
  have hΓr : (gaussM (e + 1) n Set.univ).toReal ≠ 0 := (ENNReal.toReal_pos hΓ0.ne' hΓ.ne).ne'
  have hae : ∀ᵐ π : Fin (e + 1) → Fin n → ℂ,
      Real.log ‖eval (nrmGroups h e (coefRows h π)) (specFirst g u)‖ - fsSum h u (coneSet h W) π =
        Real.log ‖eval (nrmGroups h e (coefRows h π)) (specFirst g u')‖ -
          fsSum h u' (coneSet h W) π := by
    filter_upwards [GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W g hW hg hδ, GlobalTheory.T.ae_polynomial_nonvanishing_rows n e δ h _ hq hh,
      GlobalTheory.T.ae_polynomial_nonvanishing_rows n e δ h _ hq' hh'] with π hcount h1 h2
    rw [EvalSpecFirst.proof] at h1 h2 ⊢
    rw [EvalSpecFirst.proof]
    obtain ⟨c, hc, hfac⟩ := GlobalTheory.T.chow_form_fibre_specialization n e δ h W g π u hW hg hδ hcount h1
    have hfin : (fibrePts (coneSet h W) π).Finite := Set.finite_of_encard_eq_coe hcount
    rw [log_norm_sub_fsSum_eq h u _ π c _ hfin hc (hfac u) h1,
      log_norm_sub_fsSum_eq h u' _ π c _ hfin hc (hfac u') h2]
  have haeG := (withDensity_absolutelyContinuous (volume : Measure (Fin (e + 1) → Fin n → ℂ))
    matGauss).ae_le hae
  obtain ⟨i1, e1⟩ := GlobalTheory.T.sphere_mean_normalized_groups n e h (fun w => Real.log ‖eval w (specFirst g u)‖)
    (MahlerIntegrand.proof n e δ h _ hq hh)
  obtain ⟨i1', e1'⟩ := GlobalTheory.T.sphere_mean_normalized_groups n e h (fun w => Real.log ‖eval w (specFirst g u')‖)
    (MahlerIntegrand.proof n e δ h _ hq' hh')
  obtain ⟨i2, e2⟩ := GlobalTheory.T.integral_fubini_study_sum_cone n e δ h W g u hW hg hδ hu
  obtain ⟨i2', e2'⟩ := GlobalTheory.T.integral_fubini_study_sum_cone n e δ h W g u' hW hg hδ hu'
  have hint := integral_congr_ae (μ := gaussM (e + 1) n) haeG
  rw [integral_sub i1 i2, integral_sub i1' i2', e1, e2, e1', e2'] at hint
  apply mul_left_cancel₀ hΓr
  rw [mul_sub, mul_sub]
  exact hint

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericFlagDifference
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ck_rootNum_eq_pairNum_on_flagPair : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V), SameGeneric O x E E' → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O (joinCoord x z)) d → fnField O (joinCoord x z) = fnField O x → ∀ EB E'B : ChartBundle O (mseg (joinCoord x z)) N V, IsPull O x z E EB → IsPull O x z E' E'B → ∀ (w w' : Module.Basis (Fin N) Ω V) (b b' : Fin N → K ⊕ K' → ℤ) (f g : Fin N → MRing (Sum.elim ι ι') O), IsFlagPair ϖ (joinCoord x z) EB E'B w w' b b' f g → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O (joinCoord x z)) b b' f g (psumExpansion N k) (classList (fun j => pullDeg (K' := K') (L j)) μ)) ∧ (∀ (c : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsSymmetric → G.IsHomogeneous c → c ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - c) → ∀ a : O, a ≠ 0 → rootNum O x d N E G L Q a = ∑ μ ∈ Q.support, Q.coeff μ * cycEval (fun W => classNum b G (classList (fun j => pullDeg (K' := K') (L j)) μ) W) (divCycle (pointIdeal O (joinCoord x z)) (C a))) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hW N V _ _ E E' hEE' K' _ _ ι' _ z hm hb EB E'B hp hp'
    w w' b b' f g hfp
  have hprime : (mcIdeal O x).IsPrime := hW.2.1.1
  obtain ⟨-, hB⟩ := (BundleExamples.isModelOver_iff O _ d).mp hm
  have hB' : IsModelOver (pointIdeal O (joinCoord x z)) d := hB
  haveI hprimeB : (pointIdeal O (joinCoord x z)).IsPrime := hm.2.1.1
  have hI := IntNumIsFieldIntersection.full (IsLocalRing.ResidueField O) (K ⊕ K') (Sum.elim ι ι')
  refine ⟨fun k hk1 hk2 q L Q hQ => ?_, fun c G hsym hG hc q L Q hQ a ha => ?_⟩
  · obtain ⟨φ, -, -, hd, hd', hf, hg⟩ :=
      ((FlagPairCharacterisation.proof O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) N V EB E'B ϖ hϖ
        hB'.multiProj).1 w w' b b' f g).mp hfp
    let F₀ : FlagModel O x d N E E' :=
      { K' := K', ι' := ι', z := z, model := hm, birat := hb, EB := EB, E'B := E'B,
        pull := hp, pull' := hp', flag := φ }
    have hne : Nonempty (FlagModel O x d N E E') := ⟨F₀⟩
    have hv : F₀.value O (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
        (psum (Fin N) ℤ k) L L (fun _ => 1) (fun _ => 1) Q =
        GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O
          (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs)
          (pointIdeal O (joinCoord x z)) d
          (Fin.append b fun l => pullDeg (K' := K') (L l))
          (Fin.append b' fun l => pullDeg (K' := K') (L l))
          (Fin.append f fun _ => 1) (Fin.append g fun _ => 1)
          (rename (Fin.castAdd q) (psum (Fin N) ℤ k) * rename (Fin.natAdd N) Q) := by
      show GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O _ _ d (Fin.append φ.deg _)
        (Fin.append φ.deg' _) (Fin.append φ.f fun _ => rename (liftVar ι') (1 : MRing ι O))
        (Fin.append φ.g fun _ => rename (liftVar ι') (1 : MRing ι O)) _ = _
      rw [hd, hd', hf, hg, map_one]
      rfl
    unfold ck
    rw [dif_pos hne]
    refine (GlobalTheory.T.flag_model_value_independent O Ω K ι x d N V E E' hW hEE'
      (Classical.choice hne) F₀ _ _ (ChernClassOnFlagPair.fieldNum_spec _ _) hI (psum (Fin N) ℤ k)
      (psum_isSymmetric _ _ k) q L L (fun _ => 1) (fun _ => 1)
      (fun l => ChernClassOnFlagPair.isVertDiv_one hprime _ (sub_self _)) k Q hk2
      (isHomogeneous_psum N k) hQ).trans ?_
    refine hv.trans ((plainPolynomialPairNumber.proof O (K ⊕ K') (Sum.elim ι ι')
      (pointIdeal O (joinCoord x z)) d N b b' f g k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) hk2 q _ Q hQ).trans ?_)
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hlen : (classList (fun j => pullDeg (K' := K') (L j)) μ).length + k = d + 1 := by
      have h := hQ (mem_support_iff.mp hμ)
      rw [ChernClassOnFlagPair.length_classList, Finsupp.degree_eq_weight_one]
      have : Finsupp.weight (fun _ => 1) μ = Finsupp.weight 1 μ := rfl
      omega
    rw [PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute O ϖ hϖ (K ⊕ K') (Sum.elim ι ι')
      (pointIdeal O (joinCoord x z)) d hB' N b b' f g hfp.vertical k (psum (Fin N) ℤ k)
      (isHomogeneous_psum N k) _ (psumExpansion N k)
      (dividedDifferenceExpansion.proof N k _ (isHomogeneous_psum N k)) (isPairExpansion_psum N k)
      _ hlen]
  · have hsame : SameGeneric O x E E := fun s _ =>
      ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
        fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
    obtain ⟨φ, -, -, hd, -, -, -⟩ :=
      ((FlagPairCharacterisation.proof O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) N V EB EB ϖ hϖ
        hB'.multiProj).1 w w b b _ _).mp (ChernClassOnFlagPair.isFlagPair_self hfp.flag)
    let F₀ : FlagModel O x d N E E :=
      { K' := K', ι' := ι', z := z, model := hm, birat := hb, EB := EB, E'B := EB,
        pull := hp, pull' := hp, flag := φ }
    have hne : Nonempty (FlagModel O x d N E E) := ⟨F₀⟩
    unfold rootNum
    rw [dif_pos hne]
    refine (GlobalTheory.T.flag_model_root_independent O Ω K ι x d N V E E hW hsame
      (Classical.choice hne) F₀ _ _ (ChernClassOnFlagPair.fieldNum_spec _ _) hI c G hsym hG hc q L Q hQ a
      ha).trans ?_
    have h6 := RootPolynomialNumber.proof O (K ⊕ K') (Sum.elim ι ι') (pointIdeal O (joinCoord x z)) d N b
      c G hG hc q (fun j => pullDeg (K' := K') (L j)) Q hQ a
    rw [← hd] at h6 ⊢
    exact h6

end GlobalTheory.CompanionTheory.Ar.Num
end

