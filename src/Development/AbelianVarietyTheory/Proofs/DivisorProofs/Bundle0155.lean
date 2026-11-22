import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleBaseChangeEvalHomStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyEtale_baseChange_eval_hom : ∀ {k R B : Type} [CommRing k] [CommRing R] [CommRing B] [Algebra k R] [Algebra k B] {r : ℕ} (τ : Fin r → B),
  (MvPolynomial.eval₂Hom (algebraMap k B) τ).FormallyEtale →
  (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[k] B)
      (fun i => (1 : R) ⊗ₜ[k] τ i)).FormallyEtale := by
  first | exact @GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor | exact GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor | (intros; apply GlobalTheory.formallyEtale_mvPolynomial_eval₂_tensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealCoprimeElementExistsStatement
section
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractional_ideal_coprime_element_exists : ∀ {F : Type} [Field F] [NumberField F] (Y N : FractionalIdeal (𝓞 F)⁰ F), Y ≠ 0 → N ≠ 0 → N ≤ 1 →
    ∃ β ∈ Y, FractionalIdeal.spanSingleton (𝓞 F)⁰ β * Y⁻¹ + N = 1 := by
  first | exact @GlobalTheory.exists_mem_spanSingleton_mul_inv_add_eq_one | exact GlobalTheory.exists_mem_spanSingleton_mul_inv_add_eq_one | (intros; apply GlobalTheory.exists_mem_spanSingleton_mul_inv_add_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeAwayMulOfFiniteType
section
open TensorProduct

namespace GlobalTheory

theorem free_away_mul_of_finiteType : ∀ {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A] [Algebra A B] [Algebra.FiniteType A B] [Algebra.IsAlgebraic A B], ∃ a : A, a ≠ 0 ∧ ∀ (c : A) (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'], IsLocalization.Away (a * c) A' → IsLocalization.Away (algebraMap A B (a * c)) B' → Module.Free A' B' := by
  intro A B _ _ _ _ _ _ _
  obtain ⟨a, ha0, hfree⟩ := (generic_freeness A).2.1 B B
  refine ⟨a, ha0, fun c A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  haveI := hA
  have hu : IsUnit (algebraMap A A' a) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := A') (a * c)
    rw [map_mul] at this
    exact isUnit_of_mul_isUnit_left this
  letI : Algebra (Localization.Away a) A' :=
    (IsLocalization.Away.lift a (S := Localization.Away a) hu).toAlgebra
  haveI : IsScalarTower A (Localization.Away a) A' :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (IsLocalization.Away.lift_eq (S := Localization.Away a) a hu x).symm
  haveI : Module.Free (Localization.Away a) ((Localization.Away a) ⊗[A] B) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers a) B)
  haveI : Module.Free A' (A' ⊗[A] B) :=
    Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A
      (Localization.Away a) A' A' B)
  haveI hloc : IsLocalizedModule (Submonoid.powers (a * c))
      (IsScalarTower.toAlgHom A B B').toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization, Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hB
  have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers (a * c)) A'
    (IsScalarTower.toAlgHom A B B').toLinearMap
  exact Module.Free.of_equiv hbc.equiv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeModuleComplementSupportCompact
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_module_complement_support_compact : ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (r : ℕ), (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) → ∀ s : Fin r → M, IsCompact (Module.support R (M ⧸ Submodule.span R (Set.range s)))ᶜ := by
  first | (exact @GlobalTheory.isCompact_compl_support_quotient_span) | (exact GlobalTheory.isCompact_compl_support_quotient_span) | (intros; apply GlobalTheory.isCompact_compl_support_quotient_span  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfPrincipalMaximalIdealOfKerSmulLeStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_of_principal_maximalIdeal_of_ker_smul_le' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (x : R), IsLocalRing.maximalIdeal R = Ideal.span {x} → ∀ (N : Type 1) [AddCommGroup N] [Module R N], Module.Finite R N → (∀ n : N, x • n = 0 → n ∈ Ideal.span {a : R | x * a = 0} • (⊤ : Submodule R N)) → Module.Free R N := by
  first | exact @GlobalTheory.free_of_principal_maximalIdeal_of_ker_smul_le | exact GlobalTheory.free_of_principal_maximalIdeal_of_ker_smul_le | (intros; apply GlobalTheory.free_of_principal_maximalIdeal_of_ker_smul_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSemilinearMatrixIterateEqZeroOfNilpotenStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusSemilinearMatrix_iterate_eq_zero_of_nilpotent : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι S) (N : ℕ), (∀ j i, IsNilpotent ((fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[N] (Pi.single j 1) i)) → ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => Q.mulVec fun k => frobenius S p (w k))^[K] z = 0 := by
  first | exact @GlobalTheory.frobSemilinear_iterate_eq_zero | exact GlobalTheory.frobSemilinear_iterate_eq_zero | (intros; apply GlobalTheory.frobSemilinear_iterate_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusStrictLowerComparisonNearIdentityStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_strictLower_comparison_near_identity : ∀ (r : ℕ) (g n b B W H : Matrix (Fin r) (Fin r) ℂ) (δ : ℝ), 0 ≤ δ → (r : ℝ) * δ ≤ 1 / 100 → (∀ a c : Fin r, a < c → n a c = 0) → (∀ a : Fin r, n a a = 1) → (∀ a c : Fin r, c < a → ‖n a c‖ ≤ δ) → (∀ a c : Fin r, c < a → b a c = 0) → (∀ a : Fin r, |‖b a a‖ ^ 2 - 1| ≤ 6 * δ) → (∀ a c : Fin r, a < c → ‖b a c‖ ≤ 6 * δ) → (∀ a c : Fin r, c < a → B a c = 0) → (∀ a c : Fin r, a ≤ c → W a c = 0) → (∀ a c : Fin r, a ≤ c → H a c = 0) → g * n = b → g * W = H * b + B → ∑ a, ∑ c, ‖W a c‖ ^ 2 ≤ 2 * ∑ a, ∑ c, ‖H a c‖ ^ 2 := by
  first | exact @GlobalTheory.frobenius_lower_comparison | exact GlobalTheory.frobenius_lower_comparison | (intros; apply GlobalTheory.frobenius_lower_comparison <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubalgebraCounitalComulStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusSubalgebra_counital_comul : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ B : Subalgebra k A, (∀ a, a ∈ B ↔ ∃ c : A, c ^ p = a) ∧ ∃ Δ' : B →ₐ[k] B ⊗[k] B, ((∀ a : B, TensorProduct.lid k B (LinearMap.rTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a) ∧ (∀ a : B, TensorProduct.rid k B (LinearMap.lTensor B (ε.comp B.val).toLinearMap (Δ' a)) = a)) := by
  first | exact @GlobalTheory.frobSubalgebra_counit | exact GlobalTheory.frobSubalgebra_counit | (intros; apply GlobalTheory.frobSubalgebra_counit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromSpecComapEqBotEqGenericPointStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromSpec_comap_eq_bot_eq_genericPoint : ∀ (X Y : Scheme.{0}) [IsIntegral X] (π : Y ⟶ X) (V : X.Opens), IsAffineOpen V → ∀ (hW : IsAffineOpen (π ⁻¹ᵁ V)) (P : Ideal Γ(Y, π ⁻¹ᵁ V)) (hP : P.IsPrime), P.comap (π.app V).hom = ⊥ → π (hW.fromSpec ⟨P, hP⟩) = genericPoint X := by
  first | exact @GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | exact GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint | (intros; apply GlobalTheory.fromSpec_prime_comap_bot_lies_over_genericPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainL2Bound
section
open MeasureTheory Set
open scoped ENNReal

namespace GlobalTheory.QuotLocInt

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G}

open MeasureTheory Set in
open scoped ENNReal in
private theorem lintegral_compact_le_mul_lintegral_fundamentalDomain (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (C : Set G) (hC : IsCompact C) (n : ℝ)
    (hn : ∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n)
    (g : G → ℝ≥0∞) (hg : Measurable g) (hinv : ∀ (γ : Γ) x, g (γ • x) = g x) :
    ∫⁻ x in C, g x ∂μ ≤ ENNReal.ofReal n * ∫⁻ x in 𝓕, g x ∂μ := by
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hcount : ∀ x : G, ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x) ≤ ENNReal.ofReal n := by
    intro x
    have hS : ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x) =
        ∑' γ : Γ, {γ : Γ | (γ : G) * x ∈ C}.indicator 1 γ := rfl
    rw [hS, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    obtain ⟨hfin, hle⟩ := hn x
    have hE : ({γ : Γ | (γ : G) * x ∈ C}).encard ≤
        (({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℕ∞) := by
      rw [hfin.cast_ncard_eq, ← Subtype.val_injective.encard_image]
      apply Set.encard_le_encard
      rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ.2, hγ⟩
    calc ((({γ : Γ | (γ : G) * x ∈ C}).encard : ℕ∞) : ℝ≥0∞)
        ≤ (((({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := ENat.toENNReal_le.mpr hE
      _ = (({γ : G | γ ∈ Γ ∧ γ * x ∈ C}.ncard : ℕ) : ℝ≥0∞) := by simp
      _ ≤ ENNReal.ofReal n := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hle
  calc ∫⁻ x in C, g x ∂μ = ∫⁻ x, C.indicator g x ∂μ := (lintegral_indicator hCm _).symm
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, C.indicator g (γ⁻¹ • x) ∂μ := h𝓕.lintegral_eq_tsum' _
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, C.indicator (1 : G → ℝ≥0∞) (γ⁻¹ • x) * g x ∂μ := by
        congr 1; funext γ; congr 1; funext x
        by_cases hx : γ⁻¹ • x ∈ C <;> simp [hx, hinv]
    _ = ∫⁻ x in 𝓕, ∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ⁻¹ • x) * g x ∂μ := by
        rw [lintegral_tsum]
        intro γ
        exact (((measurable_one.indicator hCm).comp (measurable_const_smul _)).mul hg).aemeasurable
    _ = ∫⁻ x in 𝓕, (∑' γ : Γ, C.indicator (1 : G → ℝ≥0∞) (γ • x)) * g x ∂μ := by
        congr 1; funext x
        rw [ENNReal.tsum_mul_right]
        congr 1
        exact (Equiv.inv Γ).tsum_eq (fun γ => C.indicator (1 : G → ℝ≥0∞) (γ • x))
    _ ≤ ∫⁻ x in 𝓕, ENNReal.ofReal n * g x ∂μ :=
        lintegral_mono fun x => by gcongr ?_ * _; exact hcount x
    _ = _ := lintegral_const_mul _ hg

open MeasureTheory Set in
open scoped ENNReal in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] {Γ : Subgroup G} [Countable Γ] {𝓕 : Set G} in

theorem _root_.GlobalTheory.QuotLocInt.integrableOn_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ]
    (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ C : Set G, IsCompact C → ∀ n : ℝ,
    (∀ y : G, {γ : G | γ ∈ Γ ∧ γ * y ∈ C}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ γ * y ∈ C}.ncard : ℕ) : ℝ) ≤ n) →
    ∃ M : ℝ, ∀ F : Lp ℂ 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))),
      IntegrableOn (fun x => F (Quotient.mk _ x)) C μ ∧
        ∫ x in C, ‖F (Quotient.mk _ x)‖ ∂μ ≤ M * ‖F‖ := by
  intro G _ _ _ _ _ _ μ _ Γ _ 𝓕 h𝓕 C hC n hn
  refine ⟨(ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ)).toReal, fun F => ?_⟩
  have hπ : Measurable (Quotient.mk (QuotientGroup.rightRel Γ)) := fun _ hs => hs
  have hF := Lp.stronglyMeasurable F
  have hf : StronglyMeasurable fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x) :=
    hF.comp_measurable hπ
  have hL2 : eLpNorm (fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x)) 2 (μ.restrict C) ≤
      ENNReal.ofReal n ^ (1/2 : ℝ) *
        eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    calc ∫⁻ x in C, ‖F (Quotient.mk (QuotientGroup.rightRel Γ) x)‖ₑ ^ (2 : ℝ) ∂μ
        ≤ ENNReal.ofReal n * ∫⁻ x in 𝓕, ‖F (Quotient.mk (QuotientGroup.rightRel Γ) x)‖ₑ ^ (2 : ℝ) ∂μ :=
          lintegral_compact_le_mul_lintegral_fundamentalDomain G μ Γ 𝓕 h𝓕 C hC n hn _
            ((hF.measurable.enorm.pow_const _).comp hπ) fun γ x => by
              rw [show Quotient.mk (QuotientGroup.rightRel Γ) (γ • x) = Quotient.mk _ x from
                Quotient.sound (QuotientGroup.rightRel_apply.2 (by simp [Subgroup.smul_def, mul_inv_rev]))]
      _ = _ := by rw [lintegral_map (hF.measurable.enorm.pow_const _) hπ]
  have hL1 : eLpNorm (fun x => F (Quotient.mk (QuotientGroup.rightRel Γ) x)) 1 (μ.restrict C) ≤
      ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ) *
        eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hf.aestronglyMeasurable).trans ?_
    rw [Measure.restrict_apply_univ]
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
    rw [show (1 / 1 - 1 / 2 : ℝ) = 1 / 2 by norm_num]
    calc _ ≤ ENNReal.ofReal n ^ (1/2 : ℝ) *
          eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) *
            μ C ^ (1/2 : ℝ) := by gcongr
      _ = _ := by ring
  have hfin : ENNReal.ofReal n ^ (1/2 : ℝ) * μ C ^ (1/2 : ℝ) *
      eLpNorm F 2 ((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))) < ⊤ := by
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) (Lp.eLpNorm_lt_top F)
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.measure_lt_top.ne
  refine ⟨memLp_one_iff_integrable.1 ⟨hf.aestronglyMeasurable, hL1.trans_lt hfin⟩, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable, ← eLpNorm_one_eq_lintegral_enorm,
    Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hfin.ne hL1

end GlobalTheory.QuotLocInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalMapGalElt
section
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.GoodEtale

variable {R C O G : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O] [Group G]

def galMap (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) : O ⊗[R] C →ₐ[O] (G → O) :=
  Pi.algHom O (fun _ => O) fun g =>
    Algebra.TensorProduct.lift (AlgHom.id O O) (σ.comp (act g).toAlgHom) (fun _ _ => Commute.all _ _)

@[simp] theorem galMap_tmul (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) (o : O) (c : C) (g : G) :
    galMap act σ (o ⊗ₜ c) g = o * σ (act g c) := by
  simp [galMap]

def galElt (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) {n : ℕ} (x y : Fin n → C) (h : G) : O ⊗[R] C :=
  ∑ i, σ (x i) ⊗ₜ act h⁻¹ (y i)

theorem galMap_galElt [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (σ : C →ₐ[R] O) {n : ℕ} (x y : Fin n → C)
    (b : R) (hxy : ∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C b else 0) (h : G) :
    galMap act σ (galElt act σ x y h) = Pi.single h (algebraMap R O b) := by
  funext g
  simp only [galElt, map_sum, Finset.sum_apply, galMap_tmul]
  have : ∀ i, σ (x i) * σ (act g (act h⁻¹ (y i))) = σ (x i * act (g * h⁻¹) (y i)) := by
    intro i; simp [map_mul]
  simp_rw [this, ← map_sum, hxy]
  by_cases hg : g = h
  · subst hg; simp
  · have : g * h⁻¹ ≠ 1 := fun e => hg (mul_inv_eq_one.mp e)
    simp [this, hg]

end GlobalTheory.GoodEtale

example (R : Type) [CommRing R] (o r : R) :
    GlobalTheory.GoodEtale.galMap (G := Unit) 1 (AlgHom.id R R) (o ⊗ₜ r) () = o * r := by
  simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfFiniteGeneratingAutomorphismsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGalois_of_finite_fixed_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by
  first | exact @GlobalTheory.galois_of_finite_generating_automorphisms | exact GlobalTheory.galois_of_finite_generating_automorphisms | (intros; apply GlobalTheory.galois_of_finite_generating_automorphisms <;> assumption)
end

