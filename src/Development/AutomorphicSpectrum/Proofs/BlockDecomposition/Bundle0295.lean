import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0052
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0051
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0287
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0290
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBundleRootFromRelations
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0270
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0278
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0286
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSup
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.PbKer

theorem isPullback_of_ker_eq_sup {X A B Z : Scheme.{0}} (a : A ⟶ X) (b : B ⟶ X) (f : Z ⟶ A)
    (g : Z ⟶ B) [IsClosedImmersion a] [IsClosedImmersion b] [IsClosedImmersion (f ≫ a)]
    (h : f ≫ a = g ≫ b)
    (hk : Scheme.Hom.ker (f ≫ a) = Scheme.Hom.ker a ⊔ Scheme.Hom.ker b) :
    IsPullback f g a b := by
  have hle : ∀ {W : Scheme.{0}} (u : W ⟶ A) (v : W ⟶ B), u ≫ a = v ≫ b →
      Scheme.Hom.ker (f ≫ a) ≤ Scheme.Hom.ker (u ≫ a) := by
    intro W u v huv
    rw [hk]
    refine sup_le (Scheme.Hom.le_ker_comp u a) ?_
    rw [huv]
    exact Scheme.Hom.le_ker_comp v b
  refine IsPullback.of_isLimit' ⟨h⟩ ?_
  refine PullbackCone.IsLimit.mk h
    (fun s => IsClosedImmersion.lift (f ≫ a) (s.fst ≫ a) (hle s.fst s.snd s.condition)) ?_ ?_ ?_
  · intro s
    rw [← cancel_mono a, Category.assoc]
    exact IsClosedImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono b, Category.assoc, ← h, ← s.condition]
    exact IsClosedImmersion.lift_fac _ _ _
  · intro s m hm1 _
    rw [← cancel_mono (f ≫ a), IsClosedImmersion.lift_fac, ← Category.assoc, hm1]

end GlobalTheory.CompanionTheory.GE.PbKer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobsonIdealFaithfulModule
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE.Krull

theorem fPow_torsion_of_chartIn : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (I : Ideal Γ(X, V)) {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R] {M : Type} [AddCommGroup M] [Module R M] [Module Γ(X, V) M] [IsScalarTower Γ(X, V) R M] [Module.Finite R M], I.map (algebraMap Γ(X, V) R) ≤ Ideal.jacobson ⊥ → (∀ a ∈ J.ideal ⟨V, hV⟩, ∀ m : M, a • m = 0) → ∀ f : Γ(X, V), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ y : M, (∀ n, ChartIn (ψ ≫ J.subschemeι) V (I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) y) → ∃ k : ℕ, f ^ k • y = 0 := by
  intro X J Z ψ hψ V hV _ I R _ _ _ M _ _ _ _ _ hIR hJM f hiso y hy
  by_contra hne
  push_neg at hne
  let A : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M y)
  have hA : ∀ a : R, a ∈ A ↔ a • y = 0 := fun a => by
    simp [A, LinearMap.toSpanSingleton_apply]
  have hdisj : Disjoint (A : Set R) (Submonoid.powers (algebraMap Γ(X, V) R f) : Set R) := by
    refine Set.disjoint_left.2 fun x hxA hxS => ?_
    obtain ⟨k, rfl⟩ := hxS
    apply hne k
    have h1 := (hA _).1 hxA
    simp only at h1
    rwa [← map_pow, algebraMap_smul] at h1
  obtain ⟨p, hp, hAp, hpS⟩ := Ideal.exists_le_prime_disjoint A _ hdisj
  have hfp : algebraMap Γ(X, V) R f ∉ p := fun h =>
    Set.disjoint_left.1 hpS h (Submonoid.mem_powers _)
  have hJp : (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => hAp ((hA _).2 ?_)
    rw [algebraMap_smul]
    exact hJM a ha y
  obtain ⟨U, hU, h, Q₀, Q₁, hQ₀, hQ₁, hle, hQ₀p, hQ₁m⟩ := GlobalTheory.T.proper_birational_prime_exists J ψ hψ V hV f hiso p hp hJp hfp
  letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra
  haveI : IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := GlobalTheory.T.tensor_noetherian_affine_open J ψ hψ V hV U hU h R
  have hy' : ∀ n : ℕ, y ⊗ₜ[Γ(X, V)] (1 : Γ(Z, U)) ∈ LinearMap.range
      ((I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M).subtype.rTensor Γ(Z, U)) := fun n => hy n U hU h
  have hIQ : I.map (algebraMap Γ(X, V) R) ≤
      Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) :=
    hIR.trans (sInf_le ⟨bot_le, hQ₁m⟩)
  obtain ⟨w, hw, hwy⟩ := GlobalTheory.T.tensor_prime_over_ideal_completion I y hy' Q₁ hQ₁ hIQ
  have hw0 : w ∉ Q₀ := fun h' => hw (hle h')
  have hfq : f ∉ (Q₀.comap (Algebra.TensorProduct.includeRight : Γ(Z, U) →ₐ[Γ(X, V)] R ⊗[Γ(X, V)] Γ(Z, U))).comap
      (algebraMap Γ(X, V) Γ(Z, U)) := by
    intro hf
    apply hfp
    rw [← hQ₀p]
    simp only [Ideal.mem_comap] at hf ⊢
    rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply] at hf
    simpa [Algebra.TensorProduct.includeLeftRingHom_apply] using hf
  obtain ⟨hloc1, hloc2⟩ := GlobalTheory.T.proper_birational_prime_criterion J ψ V hV f hiso U hU h _ (Ideal.comap_isPrime _ _) hfq
  obtain ⟨u, hu, huy⟩ := GlobalTheory.T.tensor_prime_localization_criterion (J.ideal ⟨V, hV⟩) hJM Q₀ hQ₀ hloc1 hloc2 y w hw0 hwy
  rw [hQ₀p] at hu
  exact hu (hAp ((hA u).2 huy))

end GlobalTheory.CompanionTheory.GE.Krull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBundleRootFromRelationsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_root_from_relations : ∀ (X : Scheme.{0}) (Q : LB X), Q.IsLB → ∀ (k : ℕ), 1 ≤ k → ∀ (τ : Type) (u : (Fin k → τ) → LB.Sec Q), (∀ w₁ w₂ w₃ w₄ : Fin k → τ, (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (u w₁).f c * (u w₂).f c = (u w₃).f c * (u w₄).f c) → (⨆ i : τ, nonzeroLocus (u (fun _ => i)) = ⊤) → ∃ (A : LB X) (ω : LB.Iso (pw A (k : ℤ)) Q), A.IsLB ∧ ω.IsGen ∧ ∀ (Y : Scheme.{0}) (b : Y ⟶ X) (L : LB Y) (d D : ℤ) (hD : d * k = D) (a : τ → LB.Sec (pw L d)) (θ : LB.Iso (Q.pull b) (pw L D)), L.IsLB → θ.IsGen → (∀ w, SecMaps θ (secPull (u w) b) (secMono hD a w)) → LBIso (A.pull b) (pw L d) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese | exact GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.exists_root_of_veronese <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralEnormSqLe
section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Dblock

theorem lintegral_enorm_sq_le {α : Type} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ≥0∞)
    (hg : AEMeasurable g μ) :
    (∫⁻ x, g x ∂μ) ^ 2 ≤ μ Set.univ * ∫⁻ x, g x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have h1 : (∫⁻ a, ((g * fun _ => (1 : ℝ≥0∞)) : α → ℝ≥0∞) a ∂μ) = ∫⁻ x, g x ∂μ := by simp
  have h2 : (∫⁻ _a, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂μ) = μ Set.univ := by simp
  have h3 : (∫⁻ a, g a ^ (2 : ℝ) ∂μ) = ∫⁻ x, g x ^ 2 ∂μ := by
    refine lintegral_congr fun x => ?_
    exact ENNReal.rpow_two _
  rw [h1, h2, h3] at h
  calc (∫⁻ x, g x ∂μ) ^ 2
      ≤ ((∫⁻ x, g x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (μ Set.univ) ^ (1 / (2 : ℝ))) ^ 2 := by
        gcongr
    _ = μ Set.univ * ∫⁻ x, g x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
        rw [mul_comm]

theorem enorm_mean_sq_mul_le {α : Type} [MeasurableSpace α] (ν : Measure α) (s : Set α)
    (f : α → ℂ) :
    ‖((ν.real s : ℝ) : ℂ)⁻¹ * ∫ x in s, f x ∂ν‖ₑ ^ 2 * ν s ≤ ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν := by
  by_cases h0 : ν s = 0
  · simp [h0]
  by_cases htop : ν s = ⊤
  · simp [Measure.real, htop]
  by_cases hf : IntegrableOn f s ν
  · have hcs := lintegral_enorm_sq_le (ν.restrict s) (fun x => ‖f x‖ₑ) hf.1.enorm
    rw [Measure.restrict_apply_univ] at hcs
    have hz : ‖∫ x in s, f x ∂ν‖ₑ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    have hc : ‖((ν.real s : ℝ) : ℂ)⁻¹‖ₑ = (ν s)⁻¹ := by
      have hne : ((ν.real s : ℝ) : ℂ) ≠ 0 := by
        simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, htop]
      rw [enorm_inv hne]
      congr 1
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg,
        Measure.real, ENNReal.ofReal_toReal htop]
    rw [enorm_mul, hc]
    calc ((ν s)⁻¹ * ‖∫ x in s, f x ∂ν‖ₑ) ^ 2 * ν s
        ≤ ((ν s)⁻¹ * ∫⁻ x in s, ‖f x‖ₑ ∂ν) ^ 2 * ν s := by gcongr
      _ = ((ν s)⁻¹) ^ 2 * (∫⁻ x in s, ‖f x‖ₑ ∂ν) ^ 2 * ν s := by rw [mul_pow]
      _ ≤ ((ν s)⁻¹) ^ 2 * (ν s * ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν) * ν s := by gcongr
      _ = ((ν s)⁻¹ * ν s) ^ 2 * ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν := by ring
      _ = ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν := by
        rw [ENNReal.inv_mul_cancel h0 htop]; simp
  · rw [integral_undef hf]
    simp

end GlobalTheory.CompanionTheory.Dblock
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBrauerRootsUnityEquiv
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInv

theorem nonempty_H2_muLoc_equiv_zmod : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Nonempty (H2 (muLoc F l r A) ≃ₗ[ZMod (l ^ r)] ZMod (l ^ r)) := by
  intro F Ω _ _ _ _ _ l _ r hr A v hA
  exact (GlobalTheory.CompanionTheory.Hypotheses₂.localTateDuality F Ω l r (ZMod (l ^ r)) A (muLoc F l r A) v hr hA
    (GlobalTheory.TameQuot.contAction_muDec A l r)).1

end GlobalTheory.CompanionTheory.LocalInv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTatePeriodNotFiltered
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem exact_degrees_of_product : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ),
    (∀ (g : GQ l) (hg : g ∈ GK K), (∀ u ∈ GroundTheory.PAdicHodge.unramifiedClosure l, g u = u) →
      Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) =
        (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot g) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) →
    ∀ t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l, (∀ μ, PrePer K χ μ (t μ)) →
      ∀ μ, (μ = K.1.val → t μ ∉ FB l 2) ∧ (μ ≠ K.1.val → t μ ∉ FB l 1) := by
  intro l _ K χ hN t ht
  haveI hfK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  obtain ⟨L, hLdef⟩ : ∃ L : IntermediateField ℚ_[l] (Om l),
      L = IntermediateField.normalClosure ℚ_[l] ↥K.1 (Om l) := ⟨_, rfl⟩
  haveI : FiniteDimensional ℚ_[l] ↥L := by
    subst hLdef
    infer_instance
  have hμL : ∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), μ x ∈ L := fun μ x => by
    subst hLdef
    exact μ.fieldRange_le_normalClosure ⟨x, rfl⟩
  have hKL : ∀ x ∈ K.1, x ∈ L := fun x hx => hμL K.1.val ⟨x, hx⟩
  let res : Gal(Om l/↥L) → GQ l := fun σ => σ.restrictScalars ℚ_[l]
  have hresv : ∀ (σ : Gal(Om l/↥L)) (y : ↥L), res σ y = y := fun σ y => σ.commutes y
  have hres : ∀ σ, res σ ∈ GK K := fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hresv σ ⟨x, hKL x hx⟩
  obtain ⟨s, hs⟩ : ∃ s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l), ∀ μ, μ ∈ s :=
    ⟨(Set.toFinite (Set.univ : Set (↥K.1 →ₐ[ℚ_[l]] Om l))).toFinset, fun μ => by simp⟩
  have hT0 : (∏ μ ∈ s, t μ) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => (ht μ).1
  have htirr : Irreducible (GroundTheory.PAdicHodge.tBdR l) :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer _ |>.2
      (GroundTheory.PAdicHodge.maximalIdeal_eq_span_fontaineT GroundTheory.PAdicHodge.untilt_epsilon
        GroundTheory.PAdicHodge.untilt_frobeniusEquiv_symm_epsilon_ne_one)
  obtain ⟨n, u, hTu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hT0 htirr
  have hTu' : ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l) := by
    rw [hTu, mul_comm]
  have hcyc : ∀ σ : Gal(Om l/↥L),
      (((GroundTheory.PAdicHodge.cycloChar ⊥ (Formalism.Per6.toBot (res σ)) : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) =
        (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) := fun σ => by
    have h1 := GroundTheory.PAdicHodge.gal_smul_fontaineT σ (GroundTheory.PAdicHodge.untilt_epsilon (p := l))
    have h2 := GroundTheory.PAdicHodge.gal_smul_fontaineT (Formalism.Per6.toBot (res σ))
      (GroundTheory.PAdicHodge.untilt_epsilon (p := l))
    have h3 := h2.symm.trans h1
    exact (algebraMap ℚ_[l] (Formalism.Per6.BdRp l)).injective (mul_right_cancel₀ htirr.ne_zero h3)
  have hn : n = 1 := GlobalTheory.T.hodge_tate_character_weight L (GlobalTheory.T.sen_period_finite_extension GlobalTheory.T.sen_unramified_character_period L) u n
    (fun σ => Algebra.norm ℚ_[l] ((χ ⟨res σ, hres σ⟩ : (↥K.1)ˣ) : ↥K.1))
    (fun σ => by
      rw [← hTu']
      exact GlobalTheory.T.galois_action_period_product K χ t s hs ht (res σ) (hres σ) fun μ x => hresv σ ⟨μ x, hμL μ x⟩)
    (fun σ hσ => (hN (res σ) (hres σ) hσ).trans (hcyc σ))
  subst hn
  intro μ
  exact GlobalTheory.T.period_product_filtration_levels s t K.1.val (hs _) u (by rw [hTu', pow_one]) ((ht _).2.2 rfl) μ (hs μ)

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateSeriesDeRhamPeriodStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lubin_tate_series_de_rham_period : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (π : ↥(OL K)) (S : Subring (Formalism.Per6.BdRp l)),
    (∀ a, wB l a ∈ S) → (∀ c, oB K μ c ∈ S) → PerEnv S (FB l) (oB K μ π) → π ∣ (l : ↥(OL K)) →
    ∀ (r : ↥(OL K) →+* Tl l), (∀ c, ∃ c', tch l (r c) = oB K μ (c + π * c')) →
    ∀ (x y : Tl l), ‖thB l (tch l x)‖ < 1 → ∀ (φ : PowerSeries ↥(OL K)),
      (∀ D, x ^ D ∣ y - ∑ i ∈ Finset.range D, r (PowerSeries.coeff i φ) * x ^ i) →
      EvalMod S (FB l) (oB K μ π) (oB K μ) φ (tch l x) (tch l y) 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.Glue.evalMod_teichmuller | exact GlobalTheory.CompanionTheory.LTPer.Glue.evalMod_teichmuller | (intros; apply GlobalTheory.CompanionTheory.LTPer.Glue.evalMod_teichmuller <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHClsEq
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.CrisOne

universe w w' v u v' u'

theorem mapH_cls_eq {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'}
    (φ : Cx.Hom K L σ) (n : ℕ) (a : K.X n) (ha : K.d n a = 0) (b : L.X n) (hb : L.d n b = 0) (e : φ.f n a = b) :
    φ.mapH n (K.cls a ha) = L.cls b hb := by
  subst e
  exact CrystallineSemistableComparison.P.mapH_cls φ n a ha hb

theorem pull_oneH {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {A : C ⥤ CommAlgCat.{w} R} {B : C' ⥤ CommAlgCat.{w'} R}
    (m : CH.Mor (CH.modF A) (CH.modF B) (RingHom.id R))
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : B.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH B :=
  mapH_cls_eq m.hom 0 _ _ _ _ (funext fun _ => h _)

theorem β_one {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) :
    β F κ k n 0 (CH.oneH (OcA F κ k n)) = CH.oneH (AcrEl (F.pt κ) n) :=
  pull_oneH (βMor F κ k n) fun _ => rfl

end GlobalTheory.CompanionTheory.CrisOne
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsForm
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.MemVan

variable {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N)

def KilledIn (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) : Prop :=
  ∃ hf : f.IsHomogeneous n, KillsForm φ n f hf

theorem killedIn_zero (n : ℕ) : KilledIn φ n 0 := by
  unfold KilledIn KillsForm
  refine ⟨isHomogeneous_zero _ _ _, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_zero, map_zero]

variable {φ}

theorem KilledIn.add {n : ℕ} {f g : MvPolynomial (Fin (N + 1)) R} (hf : KilledIn φ n f)
    (hg : KilledIn φ n g) : KilledIn φ n (f + g) := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  unfold KillsForm at hf2 hg2
  unfold KilledIn KillsForm
  refine ⟨hf1.add hg1, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_add hf1 hg1, map_add, hf2 k, hg2 k, add_zero]

theorem KilledIn.mul {d m : ℕ} {a f : MvPolynomial (Fin (N + 1)) R} (ha : a.IsHomogeneous d)
    (hf : KilledIn φ m f) : KilledIn φ (d + m) (a * f) := by
  obtain ⟨hf1, hf2⟩ := hf
  unfold KillsForm at hf2
  unfold KilledIn KillsForm
  refine ⟨ha.mul hf1, fun k => ?_⟩
  rw [GlobalTheory.ProjSpace.formOn_mul ha hf1, map_mul, hf2 k, mul_zero]

theorem KilledIn.sum {ι : Type*} (s : Finset ι) {n : ℕ} (g : ι → MvPolynomial (Fin (N + 1)) R)
    (hg : ∀ i ∈ s, KilledIn φ n (g i)) : KilledIn φ n (∑ i ∈ s, g i) := by
  exact Finset.sum_induction g (KilledIn φ n) (fun a b ha hb => ha.add hb) (killedIn_zero φ n) hg

theorem killedIn_component_mul_of_homog {d : ℕ} {a h : MvPolynomial (Fin (N + 1)) R}
    (ha : a.IsHomogeneous d) (hh : ∀ n, KilledIn φ n (homogeneousComponent n h)) (n : ℕ) :
    KilledIn φ n (homogeneousComponent n (a * h)) := by
  have hsum : a * h = ∑ m ∈ Finset.range (h.totalDegree + 1), a * homogeneousComponent m h := by
    rw [← Finset.mul_sum, sum_homogeneousComponent]
  rw [hsum, map_sum]
  refine KilledIn.sum _ _ fun m _ => ?_
  rw [homogeneousComponent_of_mem
    ((mem_homogeneousSubmodule _ _).2 (ha.mul (homogeneousComponent_isHomogeneous m h)))]
  split_ifs with hnm
  · subst hnm
    exact KilledIn.mul ha (hh m)
  · exact killedIn_zero φ n

theorem killedIn_component_mul (a : MvPolynomial (Fin (N + 1)) R)
    {h : MvPolynomial (Fin (N + 1)) R} (hh : ∀ n, KilledIn φ n (homogeneousComponent n h)) (n : ℕ) :
    KilledIn φ n (homogeneousComponent n (a * h)) := by
  have hsum : a * h = ∑ k ∈ Finset.range (a.totalDegree + 1), homogeneousComponent k a * h := by
    rw [← Finset.sum_mul, sum_homogeneousComponent]
  rw [hsum, map_sum]
  exact KilledIn.sum _ _ fun k _ =>
    killedIn_component_mul_of_homog (homogeneousComponent_isHomogeneous k a) hh n

theorem killedIn_component_of_mem {h : MvPolynomial (Fin (N + 1)) R} (hh : h ∈ vanIdeal φ) :
    ∀ n, KilledIn φ n (homogeneousComponent n h) := by
  unfold vanIdeal Ideal.span at hh
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, hk⟩ := hx
    intro n
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hm)]
    split_ifs with hnm
    · subst hnm
      exact ⟨hm, hk⟩
    · exact killedIn_zero φ n
  | zero =>
    intro n
    rw [map_zero]
    exact killedIn_zero φ n
  | add x y _ _ ihx ihy =>
    intro n
    rw [map_add]
    exact (ihx n).add (ihy n)
  | smul a x _ ih =>
    intro n
    rw [smul_eq_mul]
    exact killedIn_component_mul a ih n

end GlobalTheory.CompanionTheory.GE.MemVan

namespace GlobalTheory.CompanionTheory.GE

theorem mem_vanIdeal_iff_killsForm {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}}
    (φ : Y ⟶ PSpace R N) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) :
    f ∈ vanIdeal φ ↔ KillsForm φ n f hf := by
  constructor
  · intro hmem
    have h1 := MemVan.killedIn_component_of_mem hmem n
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hf), if_pos rfl] at h1
    obtain ⟨_, hk⟩ := h1
    exact hk
  · intro hk
    refine Ideal.subset_span ?_
    exact ⟨n, hf, hk⟩

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuBNat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.MuNat

theorem muB_nat : ∀ {K B₁ B₂ : Type} [CommRing K] [CommRing B₁] [CommRing B₂] [Algebra K B₁] [Algebra K B₂] {I₁ : Ideal B₁} {I₂ : Ideal B₂}
    {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂} {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of K)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of K)} {σ : B₁ →+* B₂} (nm : NMor γ₁ q₁ (κA K I₁) γ₂ q₂ (κA K I₂) σ) (hu : nm.u ≫ q₁ = q₂) (l s : ℕ),
    (∀ k, σ (algebraMap K B₁ k) = algebraMap K B₂ k) → ∀ (j : ℕ) (x : HdR q₁ j),
    nmHO nm l s j (muB γ₁ q₁ l s {⊤} j x) = muB γ₂ q₂ l s {⊤} j (pullR j nm.u hu x) := by
  intro K B₁ B₂ _ _ _ _ _ I₁ I₂ γ₁ γ₂ X₁ X₂ q₁ q₂ σ nm hu l s hσ j x
  letI t1 : RingHomCompTriple (algebraMap K B₁) σ (algebraMap K B₂) := ⟨RingHom.ext hσ⟩
  let r₁ := CH.Mor.restrict (O (smFun X₁ q₁)) (TO q₁ l s {⊤}).ι
  let r₂ := CH.Mor.restrict (O (smFun X₂ q₂)) (TO q₂ l s {⊤}).ι
  let a₁ := (smO γ₁ q₁ l s {⊤}).o
  let a₂ := (smO γ₂ q₂ l s {⊤}).o
  let n := (nmS nm l s).o
  let MS : CH.Mor (O (smFun X₁ q₁)) (O (smFun X₂ q₂)) (RingHom.id K) := CH.Mor.ofBlk
    { G := (smMor nm.u hu).functor
      τ := fun _ => { toFun := fun z => z, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      nat := fun _ _ => rfl }
  let L1 : CH.Mor _ _ (algebraMap K B₁) := r₁.comp a₁
  let ML : CH.Mor _ _ (algebraMap K B₂) := L1.comp n
  let R1 : CH.Mor _ _ (RingHom.id K) := MS.comp r₂
  let MR : CH.Mor _ _ (algebraMap K B₂) := R1.comp a₂
  have hL1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap K B₁) r₁ a₁ j x).1
  have hL2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap K B₂) L1 n j x).1
  have hR1 := (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id K) MS r₂ j x).1
  have hR2 := (CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap K B₂) R1 a₂ j x).1
  let η : ML.G ⟶ MR.G :=
    { app := fun T => mkH (γ := dividedPowersBot K) (p := 0) (q := q₁) (κ := Ideal.Quotient.mk ⊥)
        (T := ML.G.obj T) (T' := MR.G.obj T) (RingHom.id T.obj.B)
        (fun r => congrArg T.obj.i (hσ r)) ⟨le_of_eq (Ideal.map_id _), fun x hx => rfl⟩ (fun x hx => hx) (by
          refine Subtype.ext (Prod.ext ?_ ?_)
          · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
            have hw1 := (ML.G.obj T).w r
            have hw2 := (MR.G.obj T).w r
            have h3 : Ideal.Quotient.mk T.obj.J ((ML.G.obj T).i r) = Ideal.Quotient.mk T.obj.J ((MR.G.obj T).i r) :=
              congrArg (Ideal.Quotient.mk T.obj.J) (congrArg T.obj.i (hσ r))
            exact (congrArg (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx)) hw1).trans (h3.trans hw2.symm)
          · have e : CommRingCat.ofHom (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx)) =
                𝟙 (CommRingCat.of (T.obj.B ⧸ T.obj.J)) :=
              CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
            have e2 : Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx))) =
                𝟙 (Spec (CommRingCat.of (T.obj.B ⧸ T.obj.J))) := (congrArg Spec.map e).trans (Spec.map_id _)
            change Spec.map (CommRingCat.ofHom (Ideal.quotientMap T.obj.J (RingHom.id T.obj.B) (fun x hx => hx))) ≫
                ((T.obj.y.1.2 ≫ nm.u) ≫ 𝟙 X₁) = (T.obj.y.1.2 ≫ 𝟙 X₂) ≫ nm.u
            rw [e2, Category.id_comp, Category.comp_id, Category.comp_id])
      naturality := fun T T' f => hom_ext (γ := dividedPowersBot K) (p := 0) (q := q₁) (κ := Ideal.Quotient.mk ⊥)
        (RingHom.ext fun _ => rfl) }
  have h4 := CrystallineSemistableComparison.P.prism ML MR η (fun T y => rfl) j x
  exact (congrArg (n.pull j) hL1.symm).trans (hL2.symm.trans (h4.trans (hR2.trans (congrArg (a₂.pull j) hR1))))

end GlobalTheory.CompanionTheory.MuNat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_ring_base_change_from_universal : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ π : A.A →+* A.Acr n ⧸ A.PFil n, (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧ π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi})) ∧ (∀ r, A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n)) ∧ (∀ k, JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n)) ∧ (∀ r, fil (A.pdFil n) r = A.Fil n r) ∧ (∀ k r, fil (DD k A n) r = (fil (DD k (base l) n) r).map (mapAcr A.fromBase n)) ∧ (∀ x ∈ A.PFil n, IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)}) ∧ ∀ k, n ≠ 0 → Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  first | exact @GlobalTheory.CompanionTheory.AcrMod.acr_modp | exact GlobalTheory.CompanionTheory.AcrMod.acr_modp | (intros; apply GlobalTheory.CompanionTheory.AcrMod.acr_modp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCup
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CupBeta
open CrystallineSemistableComparison.CH
universe w u v u' v'

theorem pull_cup {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    (A : C ⥤ CommAlgCat.{w} R) (A' : C' ⥤ CommAlgCat.{w} R) (m : Mor (modF A) (modF A') (RingHom.id R))
    (hm : ∀ T (x y : A.obj (m.G.obj T)), m.τ T ((mulP A).μ _ x y) = (mulP A').μ T (m.τ T x) (m.τ T y))
    {p q n : ℕ} (h : p + q = n) (x : H (modF A) p) (y : H (modF A) q) :
    m.pull n ((mulP A).cup h x y) = (mulP A').cup h (m.pull p x) (m.pull q y) :=
  CrystallineSemistableComparison.P.cup_pull (mulP A) (mulP A') m.G m.τ m.τ m.τ m.nat m.nat m.nat hm h x y

theorem beta_cup {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (k : Bool) (n : ℕ) {i j m : ℕ}
    (h : i + j = m) (x : Hc F κ k n i) (y : Hc F κ k n j) :
    β F κ k n m ((CH.mulP (OcA F κ k n)).cup h x y) =
      (CH.mulP (AcrEl (F.pt κ) n)).cup h (β F κ k n i x) (β F κ k n j y) :=
  pull_cup (OcA F κ k n) (AcrEl (F.pt κ) n) (βMor F κ k n) (fun _ _ _ => rfl) h x y

end GlobalTheory.CompanionTheory.CupBeta
end

