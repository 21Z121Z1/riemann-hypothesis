import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0107
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.BlockVal

theorem normV_eq_absNorm {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

open NumberField IsDedekindDomain Polynomial in
private theorem block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv {E : Type} [Field E] [NumberField E]
    (μ η : _root_.Formalism.L2.Host.HChar E) (r : ℕ) (v : HeightOneSpectrum (𝓞 E)) :
    (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) * (Real.sqrt (_root_.Formalism.ConjugateSelfDual.normV v) : ℂ) ^ (-(r : ℤ)) =
      (((μ * η⁻¹).val v : ℂˣ) : ℂ) := by
  have hval : (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) =
      (((μ * η⁻¹).val v : ℂˣ) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) :=
    _root_.GlobalTheory.GalChar.block_val μ η r v
  have hN : (_root_.Formalism.ConjugateSelfDual.normV v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := by
    unfold _root_.Formalism.ConjugateSelfDual.normV
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
    have := _root_.GlobalTheory.GalChar.absNorm_ne_zero v
    exact_mod_cast this
  have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hne)
  set N : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hNdef
  have hpow : (N : ℂ) ^ ((((r : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N ^ r : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow hpos.le, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hpos.le]
    congr 2
    ring
  have hs : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  rw [hval, hN]
  have hcast : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = (N : ℂ) := by simp [hNdef]
  rw [hcast, hpow, zpow_neg, zpow_natCast, Complex.ofReal_pow, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hs)), mul_one]

open NumberField IsDedekindDomain Polynomial in

theorem _root_.GlobalTheory.BlockVal.block_val_ae : ∀ {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ)
    (μ η : _root_.Formalism.L2.Host.HChar E),
    _root_.GlobalTheory.GalChar.AlmostIn ε μ → η.ValuesIn (1 / 2) ε → ∀ {r : ℕ}, Odd r →
    ∀ (μH ηH : _root_.Formalism.L2.NC.HC E),
    μH.χ = (μ : _root_.Neutral.B1.Ideles E →* ℂˣ) → ηH.χ = (η : _root_.Neutral.B1.Ideles E →* ℂˣ) → ∀ᶠ v in Filter.cofinite,
    (μH * ηH⁻¹).At v ((((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ) *
      (Real.sqrt (_root_.Formalism.ConjugateSelfDual.normV v) : ℂ) ^ (-(r : ℤ))) ∧
    ∃ y : K, ε y = (((_root_.GlobalTheory.GalChar.block μ η r).val v : ℂˣ) : ℂ)⁻¹ := by
  intro E _ _ K _ ε μ η hμ hη r hr μH ηH hμH hηH
  have hχ : (μH * ηH⁻¹).χ = ((μ * η⁻¹ : _root_.Formalism.L2.Host.HChar E) : _root_.Neutral.B1.Ideles E →* ℂˣ) := by
    rw [_root_.Formalism.L2.NC.HC.mul_χ, _root_.Formalism.L2.NC.HC.inv_χ, hμH, hηH]
    simp
  have hblock := _root_.GlobalTheory.GalChar.AlmostIn.block hμ hη hr
  unfold _root_.GlobalTheory.GalChar.AlmostIn at hblock
  filter_upwards [hblock, _root_.GlobalTheory.GalChar.unr_ae (μ * η⁻¹)] with v hv hunr
  refine ⟨?_, ?_⟩
  · rw [block_val_mul_sqrt_normV_zpow_neg_eq_mul_inv]
    exact (_root_.GlobalTheory.HeckeUnifVal.at_val_and_unr_iff (μ * η⁻¹) (μH * ηH⁻¹) hχ v).1 hunr
  · obtain ⟨y, hy⟩ := hv
    exact ⟨y⁻¹, by rw [map_inv₀, hy]⟩

end GlobalTheory.BlockVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardFilterLeLogClassNumber
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

theorem prod_orderOf_le_card_of_indep {G ι : Type} [CommGroup G] [Fintype G] [Fintype ι] (x : ι → G)
    (hx : ∀ a : ι → ℤ, ∏ i, x i ^ a i = 1 → ∀ i, x i ^ a i = 1) : ∏ i, orderOf (x i) ≤ Fintype.card G := by
  classical
  have hinj : Function.Injective (fun a : (∀ i, Fin (orderOf (x i))) => ∏ i, x i ^ (a i : ℕ)) := by
    intro a a' h
    have h1 := hx (fun i => ((a i : ℕ) : ℤ) - ((a' i : ℕ) : ℤ)) (by
      simp only [zpow_sub, zpow_natCast, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      exact mul_inv_eq_one.2 h)
    funext i
    have h2 := h1 i
    rw [zpow_sub, zpow_natCast, zpow_natCast, mul_inv_eq_one] at h2
    exact Fin.ext (pow_injOn_Iio_orderOf (a i).2 (a' i).2 h2)
  simpa using Fintype.card_le_of_injective _ hinj

theorem card_filter_le_log_classNumber {E : Type} [Field E] [NumberField E] (b : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis E) :
    (Finset.univ.filter fun i => b.h i ≠ 1).card ≤ Nat.log 2 (classNumber E) := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  have h1 : ∏ i, b.h i ≤ classNumber E := prod_orderOf_le_card_of_indep _ b.indep
  refine le_trans ?_ h1
  rw [← Finset.prod_filter_ne_one]
  refine Finset.pow_card_le_prod _ _ _ fun i hi => ?_
  have h2 := (Finset.mem_filter.1 hi).2
  have h3 := b.h_pos i
  omega

theorem exists_kPsiField_generators (R : Ranks) (H : Host R) (b : GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis.ClassBasis H.E) (p q : ℕ) :
    ∃ S : Finset ℂ, S.card ≤ Nat.log 2 (classNumber H.E) ∧
      (∀ y ∈ S, ∃ n : ℕ, 0 < n ∧ n ∣ classNumber H.E ∧ y ^ n ∈ imField H.φ₀) ∧
      kPsiField H b p q = imField H.φ₀ ⊔ cycField (classNumber H.E) ⊔ IntermediateField.adjoin ℚ (S : Set ℂ) := by
  classical
  choose ψ hψ using fun i : Fin b.k =>
    IsAlgClosed.exists_pow_nat_eq (H.φ₀ (typeNorm H p q (b.γ i : H.E))) (b.h_pos i)
  refine ⟨(Finset.univ.filter fun i => b.h i ≠ 1).image ψ,
    Finset.card_image_le.trans (card_filter_le_log_classNumber b), fun y hy => ?_, ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨b.h i, b.h_pos i, orderOf_dvd_card, _, (hψ i).symm⟩
  · rw [kPsiField_eq H b p q ψ hψ]
    refine le_antisymm (sup_le le_sup_left ?_) (sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      by_cases h : b.h i = 1
      · have h1 : ψ i ∈ imField H.φ₀ := ⟨_, by have := hψ i; rw [h, pow_one] at this; exact this.symm⟩
        exact (le_sup_left.trans le_sup_left : imField H.φ₀ ≤ _) h1
      · exact (le_sup_right : IntermediateField.adjoin ℚ _ ≤ _) (IntermediateField.subset_adjoin ℚ _
          (Finset.mem_coe.2 (Finset.mem_image_of_mem ψ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))))
    · intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact ⟨i, rfl⟩

end GlobalTheory.Mem.Fld
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharEqOfApplyRootEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
namespace GlobalTheory.TameTau

theorem char_eq_of_apply_root_eq : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (ϖ : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ π : Ω, π ^ m = algebraMap E Ω (ϖ : E) → ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, σ π = σ' π → χ σ = χ σ' := by
  intro E Ω _ _ _ _ _ A P hP O _ _ _ _ _ hO χ hχ m hm hmP hχm ϖ hϖP hϖ2 π hπ σ hσ σ' hσ' heq
  have hm0 : m ≠ 0 := hm.ne'
  have hvm : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    rw [← hP]
    simpa using h
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    exact hϖ2 (Ideal.zero_mem _)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0, eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective] at hπ
    exact hϖ0 (by exact_mod_cast hπ)
  obtain ⟨γ, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt_of_valuationSubring (E := E) A
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Ω, IsPrimitiveRoot ζ m := by
    have : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.2 hm0⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  obtain ⟨σ₀, hσ₀, hσ₀π⟩ := GlobalTheory.T.inertia_acts_on_tame_root A P hP m hm hmP ϖ hϖP hϖ2 π hπ ζ hζ.pow_eq_one
  have J := fun τ hτ => GlobalTheory.T.character_tameQuotient_jointPowers_tameGenerator A γ hγ hO χ hχ m hm hvm hχm (ϖ : E) π hπ0 hπ τ hτ
  obtain ⟨k, -, hk⟩ := J σ₀ hσ₀
  obtain ⟨n, hn1, hn2⟩ := J σ hσ
  obtain ⟨n', hn1', hn2'⟩ := J σ' hσ'
  set θ := γ π / π with hθ
  rw [hσ₀π, mul_div_cancel_right₀ _ hπ0] at hk
  have hθn : θ ^ n = θ ^ n' := by rw [← hn2, ← hn2', heq]
  have hζn : ζ ^ n = ζ ^ n' := by rw [hk, ← pow_mul, ← pow_mul, mul_comm k n, mul_comm k n', pow_mul, pow_mul, hθn]
  have hmod : n ≡ n' [MOD m] := by
    have hζ0 : ζ ≠ 0 := hζ.ne_zero hm0
    have hu : (Units.mk0 ζ hζ0) ^ n = (Units.mk0 ζ hζ0) ^ n' := Units.ext (by simpa using hζn)
    rw [pow_eq_pow_iff_modEq, ← orderOf_units, Units.val_mk0, ← hζ.eq_orderOf] at hu
    exact hu
  have hγI : γ ∈ Ine (F := E) A := hγ.1
  have hord : orderOf (χ γ) ∣ m := orderOf_dvd_of_pow_eq_one (hχm γ hγI)
  rw [hn1, hn1', pow_eq_pow_iff_modEq]
  exact Nat.ModEq.of_dvd hord hmod

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeNormGeneratorOfKummerFieldLe
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.KPsiGen

open GlobalTheory.Mem.FieldsEx GlobalTheory.Mem.BaseExt GlobalTheory.IndefiniteRowSideFullHecke.RootValueClassBasis

variable {E : Type} [Field E] [NumberField E]

theorem typeNorm_of_root [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ)
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (𝔞 : Ideal (𝓞 E)) {h : ℕ} (hpos : 0 < h) (γ : 𝓞 E) (h0 : γ ≠ 0)
    (hγ : 𝔞 ^ h = Ideal.span {γ}) (β : K) (hb : (β : ℂ) ^ h = ∏ τ : E →+* ℂ, τ (γ : E) ^ r τ) : β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} =
        ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  classical
  have : NumberField K := NumberField.mk
  have hβ : β ^ h = ∏ τ : E →+* ℂ, τ.codRestrict K (hK τ) (γ : E) ^ r τ := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb]
    rfl
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow hpos.ne'] at hβ
    refine Finset.prod_ne_zero_iff.2 (fun τ _ => pow_ne_zero _ ?_) hβ.symm
    rw [map_ne_zero]; exact_mod_cast h0
  refine ⟨hβ0, ?_, fun σ => ?_⟩
  · simp only [fun τ => span_eq_extend K τ (hK τ)]
    refine (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β _ hpos hβ0
      (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_).symm
    rw [hβ, ← span_singleton_prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hγ, extendIdealHom_span]
  · have h1 := norm_typeNorm_sq_eq E r n hr K hK (γ : E) σ
    have h2 : ‖σ (β ^ h)‖ ^ 2 = (Ideal.absNorm (Ideal.span {γ}) : ℝ) ^ n := by
      rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, hβ]
      rw [← Algebra.coe_norm_int, Rat.cast_intCast] at h1
      exact h1
    rw [← hγ, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at h2
    exact (pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 h2

theorem exists_gen_basis (b : ClassBasis E) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ (γ : 𝓞 E) (α : Eˣ) (a : Fin b.k → ℤ) (k : Fin b.k → ℕ), γ ≠ 0 ∧ (∀ i, classNumber E = b.h i * k i) ∧
      𝔞 ^ classNumber E = Ideal.span {γ} ∧
      (γ : E) = ((α ^ classNumber E * ∏ i, (b.γ i ^ k i) ^ a i : Eˣ) : E) := by
  let 𝔠 : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  obtain ⟨a, ha⟩ := b.span (ClassGroup.mk E (FractionalIdeal.mk0 E 𝔠))
  have hk : ∀ i, ∃ k, classNumber E = b.h i * k := fun i => (orderOf_dvd_card : b.h i ∣ classNumber E)
  choose k hk using hk
  have h1 : ClassGroup.mk E (FractionalIdeal.mk0 E 𝔠 * (∏ i, b.c i ^ a i)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_prod, ha]
    simp only [map_zpow, mul_inv_cancel]
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h1)
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hx
    exact Units.ne_zero _ hx
  have h2 : FractionalIdeal.mk0 E 𝔠 = toPrincipalIdeal (𝓞 E) E (Units.mk0 x hx0) * ∏ i, b.c i ^ a i := by
    rw [← mul_inv_eq_iff_eq_mul]
    exact Units.ext (by rw [hx, coe_toPrincipalIdeal]; rfl)
  set y : Eˣ := Units.mk0 x hx0 ^ classNumber E * ∏ i, (b.γ i ^ k i) ^ a i with hy
  have h3 : FractionalIdeal.mk0 E 𝔠 ^ classNumber E = toPrincipalIdeal (𝓞 E) E y := by
    rw [h2, hy, mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow, map_pow, ← b.pow_eq i, ← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm, hk i]
    rfl
  have h4 : ((𝔞 ^ classNumber E : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (y : E) := by
    rw [← coe_toPrincipalIdeal, ← h3, FractionalIdeal.coeIdeal_pow, Units.val_pow_eq_pow_val]
    rfl
  have h5 : (y : E) ∈ ((𝔞 ^ classNumber E : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [h4]; exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨γ, -, hγ⟩ := (FractionalIdeal.mem_coeIdeal _).1 h5
  refine ⟨γ, Units.mk0 x hx0, a, k, ?_, hk, ?_, hγ⟩
  · rintro rfl
    exact y.ne_zero (by rw [← hγ, map_zero])
  · apply FractionalIdeal.coeIdeal_injective (K := E)
    simp only
    rw [h4, FractionalIdeal.coeIdeal_span_singleton, hγ]

theorem typeNorm_of_basis [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ)
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (b : ClassBasis E)
    (hb : ∀ i (z : ℂ), z ^ b.h i = ∏ τ : E →+* ℂ, τ (b.γ i : E) ^ r τ → z ∈ K)
    (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : ∃ β : K, β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} =
        ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  obtain ⟨γ, α, a, k, h0, hk, hγ, hy⟩ := exists_gen_basis b 𝔞 h𝔞
  let Ψ : Eˣ →* ℂ :=
    { toFun := fun x => ∏ τ : E →+* ℂ, τ (x : E) ^ r τ
      map_one' := by simp
      map_mul' := fun x y => by simp only [Units.val_mul, map_mul, mul_pow, Finset.prod_mul_distrib] }
  choose ψ hψ using fun i => IsAlgClosed.exists_pow_nat_eq (Ψ (b.γ i)) (b.h_pos i)
  have hm : Ψ α * ∏ i, ψ i ^ a i ∈ K :=
    mul_mem (prod_mem fun τ _ => pow_mem (hK τ _) _) (prod_mem fun i _ => zpow_mem (hb i _ (hψ i)) _)
  refine ⟨⟨_, hm⟩, typeNorm_of_root r n hr K hK 𝔞 (classNumber_pos E) γ h0 hγ _ ?_⟩
  rw [hy]
  change (Ψ α * ∏ i, ψ i ^ a i) ^ _ = Ψ _
  rw [mul_pow, map_mul, map_pow, map_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, map_pow, ← hψ i, ← pow_mul, ← hk i, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm]

theorem typeNorm_gen_of_kPsi_le : ∀ (P : Pre) (δ : FieldDat P) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (j : ℕ), δ.KPsi j ≤ F → ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧ Submodule.span (𝓞 F) {β} = ∏ g : Tau P.R, (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (a : P.host.E))} ^ (P.R.sigW j).1 * Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (P.host.conj (a : P.host.E)))} ^ (P.R.sigW j).2) ∧ ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2) := by
  intro P δ F _ j hF 𝔞 h𝔞
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  have hgal : IsGalois ℚ P.host.E := P.host.hostE_isGalois
  simp only [FieldDat.KPsi, kPsiField, sup_le_iff, imField_le_iff, IntermediateField.adjoin_le_iff] at hF
  obtain ⟨⟨hE, -⟩, hψ⟩ := hF
  have hK : ∀ (τ : P.host.E →+* ℂ) x, τ x ∈ F := fun τ x => by
    obtain ⟨σ, hσ⟩ := exists_aut P.host.φ₀ τ
    rw [hσ]; exact hE _
  obtain ⟨β, hβ, hsp, hn⟩ := typeNorm_of_basis (typeExp P.host (P.R.sigW j).1 (P.R.sigW j).2) _
    (typeExp_add P.host _ _) F hK δ.basis (fun i z hz => hψ ⟨i, by
      rw [hz, prod_typeExp, typeNorm, map_prod]
      refine Finset.prod_congr rfl fun g _ => ?_
      rw [map_mul, map_pow, map_pow, conjugate_emb_apply]
      rfl⟩) 𝔞 h𝔞
  refine ⟨β, hβ, ?_, hn⟩
  rw [hsp, prod_typeExp]
  refine Finset.prod_congr rfl fun g _ => ?_
  simp only [conjugate_emb_apply]
  rfl

end GlobalTheory.Mem.KPsiGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionNormalOfUnramifiedStatement
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_normal_of_unramified : ∀ (D T : Type) [CommRing D] [IsDomain D] [IsLocalRing D] [IsIntegrallyClosed D] [CharZero D] [Algebra.EssFiniteType ℤ D] [CommRing T] [IsLocalRing T] (h : D →+* T), IsNoetherianRing T → IsLocalHom h → h.Flat → (maximalIdeal D).map h = maximalIdeal T → ((residue T).comp h).Finite → ((residue T).comp h).FormallyUnramified → IsDomain (AdicCompletion (maximalIdeal T) T) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) := by
  first | exact @GlobalTheory.EtaleCompletionCharZero.completion_isDomain_and_isIntegrallyClosed | exact GlobalTheory.EtaleCompletionCharZero.completion_isDomain_and_isIntegrallyClosed | (intros; apply GlobalTheory.EtaleCompletionCharZero.completion_isDomain_and_isIntegrallyClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdLatGmap
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

noncomputable section

namespace GlobalTheory.Mem.Col2.ChiFacLaw

open GlobalTheory.PeriodTransport GlobalTheory.IdealTransport

theorem detId_image (D : D7) {n : ℕ} (L₀ L L' : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (G G' : Matrix (Fin n) (Fin n) D.host.E) (hu : G * G' = 1)
    (h : ∀ x ∈ L, G.mulVec x ∈ L') (h' : ∀ x ∈ L', G'.mulVec x ∈ L) :
    TaylorLogMetric.detId D L₀ L' = Submodule.span (𝓞 D.host.E) {G.det} * TaylorLogMetric.detId D L₀ L := by
  unfold TaylorLogMetric.detId
  rw [Submodule.span_mul_span, Set.singleton_mul]
  congr 1
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨(G' * A).det, ⟨_, fun v hv => ?_, rfl⟩, ?_⟩
    · rw [← Matrix.mulVec_mulVec]
      exact h' _ (hA v hv)
    · show G.det * (G' * A).det = A.det
      rw [← Matrix.det_mul, ← Matrix.mul_assoc, hu, Matrix.one_mul]
  · rintro ⟨_, ⟨A, hA, rfl⟩, rfl⟩
    refine ⟨G * A, fun v hv => ?_, (Matrix.det_mul _ _).symm⟩
    rw [← Matrix.mulVec_mulVec]
    exact h _ (hA v hv)

theorem norm_one_span (D : D7) (z : D.host.E) (hz : z * D.host.conj z = 1) :
    TaylorLogMetric.N1 D (Submodule.span (𝓞 D.host.E) {z}) := by
  letI := D.host.cmStar
  have hst : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rw [← hst] at hz
  have key : ∀ w x : D.host.E, x ∈ Submodule.span (𝓞 D.host.E) {w} → star x ∈ Submodule.span (𝓞 D.host.E) {star w} := by
    intro w x hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
    refine Submodule.mem_span_singleton.2 ⟨⟨star (r : D.host.E), r.2.map (starRingEnd D.host.E).toIntAlgHom⟩, ?_⟩
    exact (star_mul' (r : D.host.E) w).symm
  refine ⟨Submodule.span (𝓞 D.host.E) {star z}, fun x => ?_, ?_⟩
  · rw [← hst]
    exact ⟨fun h => by simpa using key _ _ h, fun h => by simpa using key _ _ h⟩
  · rw [Submodule.span_mul_span, Set.singleton_mul_singleton, hz, Submodule.one_eq_span]

theorem star_det_mul {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    star ((LinearEquiv.det γ.1 : Eˣ) : E) * ((LinearEquiv.det γ.1 : Eˣ) : E) = 1 := by
  set M : Matrix (Fin n) (Fin n) E := LinearMap.toMatrix' (γ.1 : Sp E n →ₗ[E] Sp E n) with hM
  have hd : ((LinearEquiv.det γ.1 : Eˣ) : E) = M.det := by
    rw [LinearEquiv.coe_det, hM, LinearMap.det_toMatrix']
  have hu : M.conjTranspose * M = 1 := by
    ext i j
    have h := γ.2 (Pi.single i 1) (Pi.single j 1)
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, hM, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    refine h.trans ?_
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [Pi.single_apply]
    · simp [Pi.single_apply, hij, Ne.symm hij]
  rw [hd, ← Matrix.det_conjTranspose, ← Matrix.det_mul, hu, Matrix.det_one]

theorem matT_eq {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (e : E ≃+* E') {n : ℕ}
    (x : HomE E n n) : matT e n n x = (e : E →+* E').mapMatrix (LinearMap.toMatrix' x) := rfl

variable {D : D7} {X : Fields} (s : Seam D X)

theorem detId_lat_gmap {n : ℕ} (L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n)
    (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D L₀ (s.lat (gmap g N)) =
      Submodule.span (𝓞 D.host.E) {s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)} * TaylorLogMetric.detId D L₀ (s.lat N) := by
  have hd : s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) = (matT s.iE n n g.toLinearMap).det := by
    rw [matT_eq, ← RingHom.map_det, LinearMap.det_toMatrix', LinearEquiv.coe_det]
    rfl
  rw [hd]
  refine detId_image D L₀ _ _ _ (matT s.iE n n g.symm.toLinearMap) ?_
    ((matT_carries s.iE N (gmap g N) _).2 fun y hy => ⟨y, hy, rfl⟩) ((matT_carries s.iE (gmap g N) N _).2 ?_)
  · rw [matT_eq, matT_eq, ← map_mul, ← LinearMap.toMatrix'_comp]
    simp
  · rintro _ ⟨y, hy, rfl⟩
    simpa using hy

theorem chi_lat_gmap (hs : s.Ok) {χ : TaylorLogMetric.IdE D → ℂ} (hχ : TaylorLogMetric.IsChi D χ) {n : ℕ} (γ : UF X.E n)
    {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat (gmap γ.1 N))) =
      (∏ τ, X.embC s.σ₀ τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E))⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  letI := D.host.cmStar
  have hst : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  have h1 : star (s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E)) * s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) = 1 := by
    rw [hst, ← hs.2, ← map_mul, star_det_mul, map_one]
  let z : unitary D.host.E := ⟨s.iE ((LinearEquiv.det γ.1 : X.Eˣ) : X.E), h1, by rw [mul_comm]; exact h1⟩
  have hL := sd_lat s hs hN
  rw [detId_lat_gmap, hχ.1 _ _ (norm_one_span D z.1 (by rw [← hst, mul_comm]; exact h1))
    (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (GlobalTheory.ThetaMove.Moved.sd_stdL D n) hL hL).1, hχ.2 z,
    Finset.prod_inv_distrib, ← s.iT.prod_comp]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (hs.1 τ _).symm

theorem chiLaw_ambOf : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), s.Ok → TaylorLogMetric.IsChi D χ → (ambOf s B χ cD).ChiLaw a b := by
  intro D X s cc δ B χ cD a b hs hχ γ γ' N N' hN hN'
  change Base.chiFac χ a b (s.lat (gmap γ.1 N)) (s.lat (gmap γ'.1 N')) =
    (∏ τ, X.embC s.σ₀ τ _) ^ _ * (∏ τ, X.embC s.σ₀ τ _) ^ _ * Base.chiFac χ a b (s.lat N) (s.lat N')
  unfold Base.chiFac
  rw [chi_lat_gmap s hs hχ γ hN, chi_lat_gmap s hs hχ γ' hN', mul_zpow, mul_zpow, inv_zpow', inv_zpow', neg_neg]
  ring

end GlobalTheory.Mem.Col2.ChiFacLaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetSpanConjMulIntegralOfIntegralPairing
section
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory

theorem detSpan_conj_mul_mem_range (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (M M' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ v ∈ M, ∀ w ∈ M', ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range) :
    ∀ x ∈ GlobalTheory.BetaEx.detSpan M, ∀ y ∈ GlobalTheory.BetaEx.detSpan M',
      IsCMField.complexConj E x * y ∈ (algebraMap (𝓞 E) E).range := by
  have hc : ∀ a : 𝓞 E, IsCMField.complexConj E (a : E) ∈ (algebraMap (𝓞 E) E).range := fun a =>
    ⟨IsCMField.ringOfIntegersComplexConj E a, IsCMField.coe_ringOfIntegersComplexConj E a⟩
  intro x hx y hy
  unfold GlobalTheory.BetaEx.detSpan at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M x).1 hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M' y).1 hy
      choose A hA using fun i k => h (v i) (hv i) (w k) (hw k)
      refine ⟨(Matrix.of A).det, ?_⟩
      have e1 : IsCMField.complexConj E v.det
          = ((IsCMField.complexConj E : E →+* E).mapMatrix v).det := by
        rw [← RingHom.map_det]; rfl
      rw [RingHom.map_det, e1, ← Matrix.det_transpose w, ← Matrix.det_mul]
      congr 1
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
        Matrix.transpose_apply, hA]
      rfl
    | zero => simpa using Subring.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Subring.add_mem _ ha hb
    | smul a b _ hb =>
      rw [Algebra.smul_def, mul_left_comm]
      exact Subring.mul_mem _ ⟨a, rfl⟩ hb
  | zero => simpa using Subring.zero_mem _
  | add a b _ _ ha hb => rw [map_add, add_mul]; exact Subring.add_mem _ ha hb
  | smul a b _ hb =>
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact Subring.mul_mem _ (hc a) hb

end GlobalTheory
end

