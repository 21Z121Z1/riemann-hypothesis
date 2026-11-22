import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersLatticeInvariantsNeZero
section
open GlobalTheory.Published Formalism.L2.Th1.F
open scoped IntermediateField

namespace GlobalTheory.CMModel

theorem isIntegral_sqrtNegNat (p : ℕ) : IsIntegral ℤ (sqrtNegNat p) :=
  IsIntegral.of_pow two_pos (by rw [sqrtNegNat_sq]; exact (isIntegral_natCast p).neg)

theorem exists_rat_of_mem_adjoin_sqrtNegNat {p : ℕ} {z : ℂ} (hz : z ∈ ℚ⟮sqrtNegNat p⟯) :
    ∃ a b : ℚ, z = a + b * sqrtNegNat p := by
  have hint : IsIntegral ℚ (sqrtNegNat p) := (isIntegral_sqrtNegNat p).tower_top
  have hz' : z ∈ Algebra.adjoin ℚ {sqrtNegNat p} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by simpa using hx⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a + c, b + d, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    exact ⟨a * c - p * (b * d), a * d + b * c, by
      push_cast; linear_combination (b * d : ℂ) * sqrtNegNat_sq p⟩

theorem dvd_of_sqrtNegNat_mem {p q : ℕ} (hp : p.Prime) (h : sqrtNegNat q ∈ ℚ⟮sqrtNegNat p⟯) :
    p ∣ q := by
  obtain ⟨a, b, e⟩ := exists_rat_of_mem_adjoin_sqrtNegNat h
  have ha : a = 0 := by
    have := congrArg Complex.re e
    simpa [sqrtNegNat] using this.symm
  have e2 : (q : ℂ) = b ^ 2 * p := by
    have := sqrtNegNat_sq q
    rw [e, ha] at this
    push_cast at this
    linear_combination this - (b : ℂ) ^ 2 * sqrtNegNat_sq p
  have e3 : (q : ℚ) = b ^ 2 * p := by exact_mod_cast e2
  have hs : IsSquare ((q * p : ℕ) : ℚ) := ⟨b * p, by push_cast; rw [e3]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_natCast_iff.1 hs
  have hpn : p ∣ n := by
    have : p ∣ n * n := hn ▸ dvd_mul_left p q
    exact (hp.dvd_mul.1 this).elim id id
  have : p * p ∣ q * p := hn ▸ mul_dvd_mul hpn hpn
  exact Nat.dvd_of_mul_dvd_mul_right hp.pos this

theorem mem_adjoin_of_invariant {p : ℕ} {L : PeriodPair} (hL : IsIntegersLattice p L) (m : ℂ) (hm0 : m ≠ 0)
    (e2 : (m ^ 4)⁻¹ * L.g₂ = L.g₂) (e3 : (m ^ 6)⁻¹ * L.g₃ = L.g₃) : m ∈ ℚ⟮sqrtNegNat p⟯ := by
  have H₀ := isHomothetic_scalePeriods L m hm0
  have e := lattice_eq_of_g₂_eq_of_g₃_eq (H₀.g₂_eq.trans e2) (H₀.g₃_eq.trans e3)
  have := (H₀ 1).2 ((hL 1).2 ⟨one_mem _, isIntegral_one⟩)
  rw [e, mul_one] at this
  exact ((hL m).1 this).1

theorem integersLattice_invariants_ne_zero :
    ∀ (p : ℕ) (L : PeriodPair), p.Prime → 3 < p → IsIntegersLattice p L →
      L.g₂ ≠ 0 ∧ L.g₃ ≠ 0 ∧ MulStable L (sqrtNegNat p) := by
  intro p L hp h3 hL
  refine ⟨fun h => ?_, fun h => ?_, fun ω hω => ?_⟩
  · have hs := sqrtNegNat_sq 3
    push_cast at hs
    have h6 : ((1 + sqrtNegNat 3) / 2) ^ 3 = -1 := by
      linear_combination (3 / 8 + sqrtNegNat 3 / 8) * hs
    have hm := mem_adjoin_of_invariant hL ((1 + sqrtNegNat 3) / 2)
      (fun e => by rw [e] at h6; norm_num at h6) (by simp [h])
      (by rw [show 6 = 3 * 2 by norm_num, pow_mul, h6]; simp)
    have hm' : sqrtNegNat 3 ∈ ℚ⟮sqrtNegNat p⟯ := by
      have := sub_mem (add_mem hm hm) (one_mem _)
      convert this using 1
      ring
    exact absurd (Nat.le_of_dvd three_pos (dvd_of_sqrtNegNat_mem hp hm')) (not_le.2 h3)
  · have hm := mem_adjoin_of_invariant hL Complex.I Complex.I_ne_zero (by simp) (by simp [h])
    have hm' : sqrtNegNat 1 ∈ ℚ⟮sqrtNegNat p⟯ := by simpa [sqrtNegNat] using hm
    have := Nat.le_of_dvd one_pos (dvd_of_sqrtNegNat_mem hp hm')
    omega
  · exact (hL _).2 ⟨mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ((hL ω).1 hω).1,
      (isIntegral_sqrtNegNat p).mul ((hL ω).1 hω).2⟩

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRules
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem map_inj_of_inj {σ O E : Type} [CommRing O] [CommRing E] (ι : O →+* E)
    (hι : Function.Injective ι) : Function.Injective (map ι : MvPowerSeries σ O → MvPowerSeries σ E) := by
  intro a b h
  ext α
  apply hι
  rw [← coeff_map, ← coeff_map, h]

theorem integral_cob_defect_rules : ∀ (O E : Type) [CommRing O] [CommRing E] [Algebra O E] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → Function.Injective (algebraMap O E) → ∀ (f : MvPowerSeries (Fin d) E) (κ : MvPowerSeries (Fin d ⊕ Fin d) O), map (algebraMap O E) κ = cob1 (up E μ) f → IsCoc μ κ ∧ (constantCoeff f = 0 → constantCoeff κ = 0) ∧ ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect μ n f → cob1 μ s = (n : O) • κ - pull2 (nmul μ n) κ ∧ ∀ (m : ℕ) (t u : MvPowerSeries (Fin d) O), map (algebraMap O E) t = defect μ m f → map (algebraMap O E) u = defect μ (m * n) f → u = (m : O) • s + subst (nmul μ n) t := by
  intro O E _ _ _ d μ hμ hι f κ hκ
  set ι := algebraMap O E with hιdef
  have inj2 := map_inj_of_inj (σ := Fin d ⊕ Fin d) ι hι
  have inj3 := map_inj_of_inj (σ := Fin d ⊕ (Fin d ⊕ Fin d)) ι hι
  have inj1 := map_inj_of_inj (σ := Fin d) ι hι
  obtain ⟨hlawE, hnm⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d μ hμ E ι
  obtain ⟨hcob1, hcob2, hswap, -, hpull⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d μ hμ.const E ι
  have hupμ : up E μ = fun i => map ι (μ i) := rfl
  have hconstE : ∀ i, constantCoeff (up E μ i) = 0 := hlawE.const
  have hcocE := (GlobalTheory.Katz.formalGroupLawCoboundaryTwo_coboundaryOne_alt E d (up E μ) hconstE f).2.2.2.2.2 hlawE
  have hsmul : ∀ {σ : Type} (k : ℕ) (g : MvPowerSeries σ O), map ι ((k : O) • g) = (k : E) • map ι g := by
    intro σ k g
    ext α
    simp [coeff_map, map_natCast]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · apply inj3
    rw [hcob2, ← hupμ, hκ, hcocE.1, map_zero]
  · apply inj2
    rw [hswap, hκ, hcocE.2]
  · intro hf
    apply hι
    have h1 : ι (constantCoeff κ) = constantCoeff (map ι κ) := by
      rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    rw [h1, hκ, map_zero]
    unfold cob1 inL inR
    rw [map_sub, map_sub, GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero hconstE,
      GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero (fun i => constantCoeff_X _),
      GlobalTheory.Katz.SubstCalc.constantCoeff_subst_of_zero (fun i => constantCoeff_X _), hf]
    simp
  · intro n s hs
    have hnc : ∀ i, constantCoeff (nmul μ n i) = 0 := fun i => (hnm n i).1
    have hupn : up E (nmul μ n) = fun i => map ι (nmul μ n i) := rfl
    obtain ⟨hpl, hsb⟩ := hpull (nmul μ n) hnc
    obtain ⟨hd1, -⟩ := GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul O E d μ hμ f 0 n
    refine ⟨?_, ?_⟩
    · apply inj2
      rw [hcob1, ← hupμ, hs, hd1, map_sub, hsmul, hpl, hκ, ← hupn]
    · intro m t u ht hu
      obtain ⟨-, hd2⟩ := GlobalTheory.T.formalGroupLawCoboundary_multiplicationDefect_mul O E d μ hμ f m n
      apply inj1
      rw [hu, hd2, map_add, hsmul, hsb, ← hupn, hs, ht]

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrationOverCyclesLiftsLieLatticeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrationOverCycles_lifts_lieLattice : PLie := by
  first | exact @GlobalTheory.AnPer.pLie_holds | exact GlobalTheory.AnPer.pLie_holds | (intros; apply GlobalTheory.AnPer.pLie_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbBaseChange

theorem isAbelianScheme_and_relDim_of_isGrpPullback : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left) (g : ℕ), IsGrpPullback A' A (spMap f) φ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme A' ∧ SmoothOfRelativeDimension g A'.hom := by
  intro R R' _ _ f A _ A' _ φ g h hA hg
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  exact ⟨GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h,
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg⟩

end GlobalTheory.AbBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
section
noncomputable section
open NumberField Topology MeasureTheory Filter Metric
open scoped Pointwise

namespace GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem countable_ratN (r : ℕ) : Countable (ratN E a r) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  refine Function.Surjective.countable (f := fun q : BlockIx a r → E =>
    (⟨fun p => algebraMap E (Ad E) (q p), q, rfl⟩ : ratN E a r)) ?_
  rintro ⟨x, q, rfl⟩
  exact ⟨q, rfl⟩

theorem covol_lt_top {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) [μ.IsAddHaarMeasure] (𝓕 : Set (BlockIx a r → Ad E))
    (h : IsAddFundamentalDomain (ratN E a r) 𝓕 μ) : μ 𝓕 < ⊤ := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have := countable_ratN (E := E) (a := a) r
  let Cm : Set (BlockIx a r → Ad E) := Set.univ.pi fun _ => K
  have hCm : IsCompact Cm := isCompact_univ_pi fun _ => hK
  have hcovm : ∀ x : BlockIx a r → Ad E, ∃ γ : ratN E a r, x ∈ γ +ᵥ Cm := by
    intro x
    choose q hq using fun p => hcov (x p)
    refine ⟨⟨fun p => algebraMap E (Ad E) (q p), q, rfl⟩, fun p => x p - algebraMap E (Ad E) (q p),
      fun p _ => hq p, ?_⟩
    funext p
    show algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p)) = x p
    abel
  have h1 : μ 𝓕 ≤ ∑' γ : ratN E a r, μ ((γ +ᵥ Cm) ∩ 𝓕) := by
    calc μ 𝓕 ≤ μ (⋃ γ : ratN E a r, ((γ +ᵥ Cm) ∩ 𝓕)) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨γ, hγ⟩ := hcovm x
          exact Set.mem_iUnion.mpr ⟨γ, hγ, hx⟩
      _ ≤ ∑' γ : ratN E a r, μ ((γ +ᵥ Cm) ∩ 𝓕) := measure_iUnion_le _
  have : MeasurableConstVAdd (ratN E a r) (BlockIx a r → Ad E) :=
    ⟨fun γ => (continuous_const.add continuous_id :
      Continuous fun x : BlockIx a r → Ad E => (γ : BlockIx a r → Ad E) + x).measurable⟩
  have : VAddInvariantMeasure (ratN E a r) (BlockIx a r → Ad E) μ :=
    ⟨fun γ s _ => measure_preimage_add μ (γ : BlockIx a r → Ad E) s⟩
  rw [← h.measure_eq_tsum Cm] at h1
  exact h1.trans_lt hCm.measure_lt_top

theorem chart_unip_periodic {r : ℕ} {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) (q : BlockIx a r → E)
    (x : BlockIx a r → Ad E) :
    chart φ.1 (unip ((fun p => algebraMap E (Ad E) (q p)) + x) * g) = chart φ.1 (unip x * g) := by
  rw [unip_add, unip_algebraMap, mul_assoc]
  funext y
  unfold chart
  split_ifs
  · rw [mul_assoc, hφ.left]
  · rfl

theorem chart_cont_bound {r : ℕ} {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) (X : Lie E a) :
    (∀ y ∈ invSet E a, Continuous fun x : BlockIx a r → Ad E => chart φ.1 (unip x * g) y) ∧
    (∀ y ∈ invSet E a, Continuous fun x : BlockIx a r → Ad E => fderiv ℝ (chart φ.1 (unip x * g)) y X) ∧
    ∀ S : Set (Lie E a), IsCompact S → S ⊆ invSet E a → ∃ C, ∀ x : BlockIx a r → Ad E, ∀ y ∈ S,
      ‖chart φ.1 (unip x * g) y‖ ≤ C ∧ ‖fderiv ℝ (chart φ.1 (unip x * g)) y X‖ ≤ C := by
  have h1 := (GlobalTheory.T.chart_unipotent_fderiv_continuousOn E a r φ hφ g X).1
  have h2 := (GlobalTheory.T.chart_unipotent_fderiv_continuousOn E a r φ hφ g X).2
  have hm : ∀ y ∈ invSet E a, ∀ x : BlockIx a r → Ad E,
      ((x, y) : (BlockIx a r → Ad E) × Lie E a) ∈ Set.univ ×ˢ invSet E a :=
    fun y hy x => Set.mem_prod.2 ⟨Set.mem_univ _, hy⟩
  refine ⟨fun y hy => ?_, fun y hy => ?_, fun S hS hSi => ?_⟩
  · have := h1.comp_continuous (continuous_id.prodMk continuous_const) (hm y hy)
    exact this
  · have := h2.comp_continuous (continuous_id.prodMk continuous_const) (hm y hy)
    exact this
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hKc : IsCompact ((Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S) := (isCompact_univ_pi fun _ => hK).prod hS
  have hsub : (Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S ⊆ Set.univ ×ˢ invSet E a :=
    Set.prod_mono (Set.subset_univ _) hSi
  obtain ⟨C1, hC1⟩ := hKc.exists_bound_of_continuousOn (h1.mono hsub)
  obtain ⟨C2, hC2⟩ := hKc.exists_bound_of_continuousOn (h2.mono hsub)
  refine ⟨max C1 C2, fun x y hy => ?_⟩
  choose q hq using fun p => hcov (x p)
  have hx : x = (fun p => algebraMap E (Ad E) (q p)) + fun p => x p - algebraMap E (Ad E) (q p) := by
    funext p
    show x p = algebraMap E (Ad E) (q p) + (x p - algebraMap E (Ad E) (q p))
    exact (add_sub_cancel _ _).symm
  have hx' : ((fun p => x p - algebraMap E (Ad E) (q p)), y) ∈ (Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S :=
    ⟨fun p _ => hq p, hy⟩
  rw [hx, chart_unip_periodic hφ]
  exact ⟨(hC1 _ hx').trans (le_max_left _ _), (hC2 _ hx').trans (le_max_right _ _)⟩

theorem isCuspidal_lie (X : Lie E a) (φ : Sm E a) (hφ : IsCuspForm φ) : IsCuspidal (lie E a X φ).1 := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  haveI := hμ
  obtain ⟨hc1, hc2, hb⟩ := chart_cont_bound (r := r) hφ.1 g X
  let ℓ : ℝ → Lie E a := fun t => oneL E a + t • X
  have hℓc : Continuous ℓ := continuous_const.add (continuous_id.smul continuous_const)
  have hT : IsOpen (ℓ ⁻¹' invSet E a) := isOpen_invSet.preimage hℓc
  have h0T : (0:ℝ) ∈ ℓ ⁻¹' invSet E a := by
    show oneL E a + (0:ℝ) • X ∈ invSet E a
    rw [zero_smul, add_zero]; exact isUnit_one
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hT 0 h0T
  have hε : 0 < δ / 2 := by positivity
  have hS : IsCompact (ℓ '' closedBall 0 (δ / 2)) := (isCompact_closedBall 0 (δ / 2)).image hℓc
  have hSinv : ℓ '' closedBall 0 (δ / 2) ⊆ invSet E a := by
    rintro _ ⟨t, ht, rfl⟩; exact hball (closedBall_subset_ball (by linarith) ht)
  obtain ⟨C, hC⟩ := hb _ hS hSinv
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hballT : ∀ t ∈ ball (0:ℝ) (δ / 2), ℓ t ∈ invSet E a := fun t ht => hball (ball_subset_ball (by linarith) ht)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕)
    (F := fun t x => chart φ.1 (unip x * g) (ℓ t))
    (F' := fun t x => fderiv ℝ (chart φ.1 (unip x * g)) (ℓ t) X) (x₀ := 0)
    (bound := fun _ => C) (s := ball 0 (δ / 2)) (ball_mem_nhds 0 hε) ?meas ?int ?meas' ?bd (integrable_const C) ?diff
  case meas =>
    filter_upwards [ball_mem_nhds (0:ℝ) hε] with t ht
    exact (hc1 _ (hballT t ht)).aestronglyMeasurable
  case int =>
    refine Integrable.of_bound (hc1 _ (hballT 0 (mem_ball_self hε))).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun x => (hC x _ ⟨0, mem_closedBall_self hε.le, rfl⟩).1
  case meas' => exact (hc2 _ (hballT 0 (mem_ball_self hε))).aestronglyMeasurable
  case bd =>
    exact Filter.Eventually.of_forall fun x t ht => (hC x _ ⟨t, ball_subset_closedBall ht, rfl⟩).2
  case diff =>
    refine Filter.Eventually.of_forall fun x t ht => ?_
    have hd := ((contDiffAt_chart φ.2 (unip x * g) (hballT t ht)).differentiableAt (by simp)).hasFDerivAt
    have hl : HasDerivAt ℓ X t := by
      have := ((hasDerivAt_id t).smul_const X).const_add (oneL E a)
      rw [one_smul] at this
      exact this
    exact hd.comp_hasDerivAt t hl
  have heq : (fun t => ∫ x in 𝓕, chart φ.1 (unip x * g) (ℓ t) ∂μ) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [ball_mem_nhds (0:ℝ) hε] with t ht
    have hu : IsUnit (Matrix.of (ℓ t)) := hballT t ht
    have e : ∀ x : BlockIx a r → Ad E, chart φ.1 (unip x * g) (ℓ t) = φ.1 (unip x * (g * infGL E a hu.unit)) := fun x => by
      rw [chart, dif_pos hu, mul_assoc]
    simp only [e]
    exact hφ.2 r h0 h1 μ 𝓕 hμ hF _
  have h2 := key.2.unique ((hasDerivAt_const (0:ℝ) (0:ℂ)).congr_of_eventuallyEq heq)
  have e0 : ℓ 0 = oneL E a := by simp [ℓ]
  simp only [e0] at h2
  exact h2

theorem isCuspidal_lie_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (X : Lie E a) (φ : Sm E a), IsCuspForm φ → IsCuspidal (lie E a X φ).1 :=
  fun _ _ _ _ _ X φ h => isCuspidal_lie X φ h

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplier
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LatticeJInt

theorem main : ∀ (L : PeriodPair) (β : ℂ), MulStable L β → β.im ≠ 0 →
    _root_.IsIntegral ℤ (latticeCurve L).j := by
  intro L β hβ him
  obtain ⟨c, τ, hτ⟩ := ReciprocityTheory.ChartRestriction.L1.latTau L
  have hj := GlobalTheory.JInt.main L c τ β hτ hβ him
  rw [← ReciprocityTheory.ChartRestriction.L1.jInv_eq_jT hτ] at hj
  rw [latticeCurve_j_eq]
  exact hj

end GlobalTheory.CMModel.LatticeJInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMinimalOfDiscrEqUnitMulNegCube
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem isMinimal_of_discr_eq_unit_mul_neg_cube : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (W : WeierstrassCurve F) (u : (w.valuationSubringAtPrime F)ˣ), (p : 𝓞 F) ∉ w.asIdeal ^ 3 → W.IsIntegral (w.valuationSubringAtPrime F) → W.Δ = ((u : w.valuationSubringAtPrime F) : F) * -(p : F) ^ 3 → W.IsMinimal (w.valuationSubringAtPrime F) := by
  intro p F _ _ w W u hp hI hΔ
  have hmem : ∀ y : F, y ∈ w.valuationSubringAtPrime F ↔ w.valuation F y ≤ 1 := by
    intro y
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    rfl
  refine GlobalTheory.isMinimal_of_forall_div_pow_twelve _ F W hI ?_
  intro x hx0 hx
  by_contra hnu
  have hxF : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hx1 : w.valuation F (x : F) < 1 := by
    refine lt_of_le_of_ne ((hmem _).1 x.2) (fun h => hnu ?_)
    have hi : (x : F)⁻¹ ∈ w.valuationSubringAtPrime F := by
      rw [hmem, map_inv₀, h, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hxF))
  have hu : w.valuation F ((u : w.valuationSubringAtPrime F) : F) = 1 := by
    have h1 := (hmem _).1 (u : w.valuationSubringAtPrime F).2
    have h2 := (hmem _).1 ((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F).2
    have h3 : w.valuation F ((u : w.valuationSubringAtPrime F) : F) *
        w.valuation F (((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F) : F) = 1 := by
      rw [← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]; simp
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ _ * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  obtain ⟨y, hy⟩ := hx
  have hy1 := (hmem _).1 y.2
  have hyx : (y : F) * (x : F) ^ 12 = W.Δ := by
    have : (y : F) = W.Δ / (x : F) ^ 12 := hy
    rw [this]; field_simp
  have hv := congrArg (w.valuation F) (hyx.trans hΔ)
  rw [map_mul, map_mul, hu, Valuation.map_neg, map_pow, map_pow, one_mul] at hv
  have hpv : w.valuation F (p : F) = w.intValuation (p : 𝓞 F) := by
    rw [← w.valuation_of_algebraMap (K := F)]; simp
  have hp' : WithZero.exp (-(3 : ℤ)) < w.valuation F (p : F) := by
    rw [hpv]
    by_contra h
    exact hp ((w.intValuation_le_pow_iff_mem _ 3).1 (by simpa using h))
  have hle : w.valuation F (p : F) ^ 3 ≤ w.valuation F (x : F) ^ 12 := by
    rw [← hv]
    calc _ ≤ 1 * _ := mul_le_mul_left hy1 _
      _ = _ := one_mul _
  have hvx0 : w.valuation F (x : F) ≠ 0 := by simpa using hxF
  have hvp0 : w.valuation F (p : F) ≠ 0 := (lt_of_le_of_lt zero_le' hp').ne'
  rw [← WithZero.exp_log hvx0] at hle hx1
  rw [← WithZero.exp_log hvp0] at hle hp'
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_le_exp] at hle
  rw [WithZero.exp_lt_exp] at hp'
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx1
  simp only [nsmul_eq_mul] at hle
  push_cast at hle
  omega

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeSpanOfSqEqNegPrimeStatement
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrime_span_of_sq_eq_neg_prime_quadratic : ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 → y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  first | exact @GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime | exact GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime | (intros; apply GlobalTheory.CMModel.isPrime_span_of_sq_eq_neg_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionHolomorphicMulFrameExtendByZero
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ) (F0 : U → ℂ), Etale A U z → A.IsFrameOn la U β → Holo n (fun y : U => z y) F0 → A.IsSecOn la U (fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 U F0 y) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) := by
  intro n Y _ _ _ _ _ ι La _ A la U z β F0 hE hβ hF
  have hfun : (fun y : U => GlobalTheory.OTY.TwEst.ext0 U F0 y) = F0 :=
    funext fun y => GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U F0 y
  have hd := (GlobalTheory.T.holo_iff_differentiableOn_charts_of_etale n Y ι La A U z hE (GlobalTheory.OTY.TwEst.ext0 U F0)).1 (by rw [hfun]; exact hF)
  refine ⟨⟨fun i => (hβ.1.1 i).mul (hd i), fun i j y hy hi hj => ?_⟩, ?_⟩
  · show β i y * _ = _ * (β j y * _)
    rw [hβ.1.2 i j y hy hi hj, mul_assoc]
  · have hc : ContinuousOn (GlobalTheory.OTY.TwEst.ext0 U F0) U := by
      intro y hy
      have hs := A.mem_pick y
      set e := A.chart (A.pick y) with he
      have hop : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hE.isOpen
      have hm : e y ∈ e.target ∩ e.symm ⁻¹' U :=
        ⟨e.map_source hs, by simpa [e.left_inv hs] using hy⟩
      have h1 : ContinuousAt (GlobalTheory.OTY.TwEst.ext0 U F0 ∘ e.symm) (e y) :=
        (hd (A.pick y)).continuousOn.continuousAt (hop.mem_nhds hm)
      have h2 : ContinuousAt ((GlobalTheory.OTY.TwEst.ext0 U F0 ∘ e.symm) ∘ e) y :=
        h1.comp (e.continuousAt hs)
      refine (h2.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hs] with x hx
      simp [e.left_inv hx]
    classical
    have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : ℂ)) (s := Uᶜ))
      hE.isOpen.measurableSet
    convert hm using 1
    funext y
    by_cases hy : y ∈ U
    · simp [hy]
    · simp [hy, GlobalTheory.OTY.TwEst.ext0]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KatzQuasiIntegralCriterionStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.katz_quasi_integral_criterion : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ f : MvPowerSeries (Fin d) (Fr p k), (∀ i, ∃ w : WittVector p k, lin f i = algebraMap (WittVector p k) (Fr p k) w) → cob1 (fun i => Katz.lift p (μ i)) f ∈ intBy p k _ 1 → f ∈ quasiInt p k (Fin d) := by
  first | exact @GlobalTheory.Katz.quasiInt_of_cob1_int_of_lin_int | exact GlobalTheory.Katz.quasiInt_of_cob1_int_of_lin_int | (intros; apply GlobalTheory.Katz.quasiInt_of_cob1_int_of_lin_int <;> assumption)
end

