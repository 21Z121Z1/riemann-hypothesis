import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
import Formalism.LocalToGlobal.HermitianForms.Bundle0003
import Formalism.LocalToGlobal.Columns.RecLevelLocT
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualWeylEqSpanColProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeNormOfKummer
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.FieldsEx

variable {E : Type} [Field E] [NumberField E] {h : ℕ}

theorem one_mem_pow : (1 : E) ∈ powIdealElts E h :=
  ⟨one_ne_zero, 1, by rw [one_pow, FractionalIdeal.spanSingleton_one]⟩

theorem mul_mem_pow {x y : E} (hx : x ∈ powIdealElts E h) (hy : y ∈ powIdealElts E h) :
    x * y ∈ powIdealElts E h := by
  obtain ⟨hx0, a, ha⟩ := hx
  obtain ⟨hy0, b, hb⟩ := hy
  exact ⟨mul_ne_zero hx0 hy0, a * b, by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ha, hb, mul_pow]⟩

theorem inv_mem_pow {x : E} (hx : x ∈ powIdealElts E h) : x⁻¹ ∈ powIdealElts E h := by
  obtain ⟨hx0, a, ha⟩ := hx
  exact ⟨inv_ne_zero hx0, a⁻¹, by rw [← FractionalIdeal.spanSingleton_inv, ha, inv_pow]⟩

theorem npow_mem_pow {x : E} (hx : x ∈ powIdealElts E h) (n : ℕ) : x ^ n ∈ powIdealElts E h := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem_pow
  | succ n ih => rw [pow_succ]; exact mul_mem_pow ih hx

theorem zpow_mem_pow {x : E} (hx : x ∈ powIdealElts E h) (n : ℤ) : x ^ n ∈ powIdealElts E h := by
  cases n with
  | ofNat n => simpa using npow_mem_pow hx n
  | negSucc n => rw [zpow_negSucc]; exact inv_mem_pow (npow_mem_pow hx _)

theorem prod_mem_pow {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, f i ∈ powIdealElts E h) :
    ∏ i ∈ s, f i ∈ powIdealElts E h :=
  Finset.prod_induction f (· ∈ powIdealElts E h) (fun _ _ => mul_mem_pow) one_mem_pow hf

theorem map_mem_pow {E' : Type} [Field E'] [NumberField E'] (σ : E →+* E') {x : E} (hx : x ∈ powIdealElts E h) :
    σ x ∈ powIdealElts E' h := by
  obtain ⟨hx0, a, ha⟩ := hx
  have hle : (𝓞 E)⁰ ≤ Submonoid.comap (RingOfIntegers.mapRingHom σ) (𝓞 E')⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ fun a b hab =>
      RingOfIntegers.ext (σ.injective (congrArg (fun y : 𝓞 E' => (y : E')) hab))
  have hm : IsLocalization.map E' (RingOfIntegers.mapRingHom σ) hle = σ :=
    IsLocalization.ringHom_ext (𝓞 E)⁰ (by rw [IsLocalization.map_comp]; rfl)
  refine ⟨(map_ne_zero σ).2 hx0, FractionalIdeal.extendedHom' E' hle a, ?_⟩
  rw [← map_pow, ← ha]
  change _ = FractionalIdeal.extended E' _ _
  rw [FractionalIdeal.extended_spanSingleton, hm]

theorem mem_pow_of_span {𝔞 : Ideal (𝓞 E)} {γ : 𝓞 E} (h0 : γ ≠ 0) (hγ : 𝔞 ^ h = Ideal.span {γ}) :
    (γ : E) ∈ powIdealElts E h :=
  ⟨by exact_mod_cast h0, 𝔞, by
    rw [← FractionalIdeal.coeIdeal_pow, hγ, FractionalIdeal.coeIdeal_span_singleton]⟩

theorem exists_aut [IsGalois ℚ E] (φ τ : E →+* ℂ) : ∃ σ : E ≃ₐ[ℚ] E, ∀ x, τ x = φ (σ x) := by
  letI := φ.toAlgebra
  let t : E →ₐ[ℚ] ℂ := τ.toRatAlgHom
  exact ⟨t.restrictNormal' E, fun x => (t.restrictNormal_commutes E x).symm⟩

theorem exists_gen (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ γ : 𝓞 E, γ ≠ 0 ∧ 𝔞 ^ classNumber E = Ideal.span {γ} := by
  let 𝔠 : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  have h1 : ClassGroup.mk0 (𝔠 ^ classNumber E) = 1 := by
    rw [map_pow, classNumber, pow_card_eq_one]
  obtain ⟨γ, hγ⟩ := (ClassGroup.mk0_eq_one_iff (𝔠 ^ classNumber E).2).1 h1
  have hγ' : 𝔞 ^ classNumber E = Ideal.span {γ} := hγ
  refine ⟨γ, ?_, hγ'⟩
  rintro rfl
  rw [Ideal.span_singleton_zero] at hγ'
  exact pow_ne_zero _ h𝔞 hγ'

theorem span_eq_extend (K : IntermediateField ℚ ℂ) [NumberField K] (τ : E →+* ℂ) (hK : ∀ x, τ x ∈ K)
    (𝔞 : Ideal (𝓞 E)) : Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} =
      extendIdealHom (τ.codRestrict K hK) 𝔞 := by
  refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (τ.codRestrict K hK) 𝔞)
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
  rfl

theorem capit_of_kummer (φ : E →+* ℂ) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hV : kummerField φ (classNumber E) ≤ K) (𝔞 : Ideal (𝓞 E)) : ∃ β : K,
      Submodule.span (𝓞 K) {β} = Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = φ (a : E)} := by
  have : NumberField K := NumberField.mk
  obtain ⟨hK, -, hV⟩ := (kummerField_le_iff φ).1 hV
  rw [span_eq_extend K φ hK]
  rcases eq_or_ne 𝔞 ⊥ with rfl | h𝔞
  · refine ⟨0, ?_⟩
    rw [← Ideal.span_singleton_zero, extendIdealHom_span]
    simp
  obtain ⟨γ, h0, hγ⟩ := exists_gen 𝔞 h𝔞
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (φ (γ : E)) (classNumber_pos E)
  let β : K := ⟨b, hV _ (mem_pow_of_span h0 hγ) b hb⟩
  have hβ : β ^ classNumber E = φ.codRestrict K hK (γ : E) := Subtype.ext hb
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow (classNumber_ne_zero E), eq_comm, map_eq_zero] at hβ
    exact h0 (by exact_mod_cast hβ)
  refine ⟨β, (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β _ (classNumber_pos E) hβ0
    (extendIdealHom_fg _ _) ?_).symm⟩
  rw [← map_pow, hγ, extendIdealHom_span, hβ]

theorem typeNorm_of_kummer [IsCMField E] [IsGalois ℚ E] (φ : E →+* ℂ) (r : (E →+* ℂ) → ℕ) (n : ℕ)
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hV : kummerField φ (classNumber E) ≤ K) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : ∃ β : K, β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} =
        ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  classical
  have : NumberField K := NumberField.mk
  obtain ⟨hK0, -, hV⟩ := (kummerField_le_iff φ).1 hV
  choose s hs using exists_aut φ
  have hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K := fun τ x => by rw [hs]; exact hK0 _
  have hpos := classNumber_pos E
  obtain ⟨γ, h0, hγ⟩ := exists_gen 𝔞 h𝔞
  have hy : ∏ τ, s τ (γ : E) ^ r τ ∈ powIdealElts E (classNumber E) :=
    prod_mem_pow _ _ fun τ _ => npow_mem_pow (map_mem_pow (s τ : E →+* E) (mem_pow_of_span h0 hγ)) _
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (φ (∏ τ, s τ (γ : E) ^ r τ)) hpos
  let β : K := ⟨b, hV _ hy b hb⟩
  have hβ : β ^ classNumber E = ∏ τ : E →+* ℂ, τ.codRestrict K (hK τ) (γ : E) ^ r τ := by
    apply Subtype.ext
    simp only [β, SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb, map_prod, map_pow, ← hs]
    rfl
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow hpos.ne'] at hβ
    refine Finset.prod_ne_zero_iff.2 (fun τ _ => pow_ne_zero _ ?_) hβ.symm
    rw [map_ne_zero]; exact_mod_cast h0
  refine ⟨β, hβ0, ?_, fun σ => ?_⟩
  · simp only [fun τ => span_eq_extend K τ (hK τ)]
    refine (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β _ hpos hβ0
      (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_).symm
    rw [hβ, ← span_singleton_prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hγ, extendIdealHom_span]
  · have h1 := norm_typeNorm_sq_eq E r n hr K hK (γ : E) σ
    have h2 : ‖σ (β ^ classNumber E)‖ ^ 2 = (Ideal.absNorm (Ideal.span {γ}) : ℝ) ^ n := by
      rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, hβ]
      rw [← Algebra.coe_norm_int, Rat.cast_intCast] at h1
      exact h1
    rw [← hγ, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at h2
    exact (pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 h2

end GlobalTheory.Mem.FieldsEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryScalarEqOneModOfFixesSimpleModule
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory.UnitaryScalarModT

theorem eq_one_add_of_fixes : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : Module.finrank F E = 2) (_ : ∀ x, σ (σ x) = x) (_ : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (_ : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (_ : T.Prime)
    (_ : ∀ a : v.adicCompletionIntegers F, Valued.v (a : v.adicCompletion F) < 1 → ∃ b : v.adicCompletionIntegers F, a = (T : v.adicCompletionIntegers F) * b)
    (M : Type) [AddCommGroup M] [Module (intV E v) M] (_ : Nat.card M = T) (m : M) (_ : m ≠ 0) (d c : intV E v) (_ : (d - 1) • m = 0)
    (_ : sigR σ (v.adicCompletion F) (d : E ⊗[F] v.adicCompletion F) * (d : E ⊗[F] v.adicCompletion F) =
        1 + (T : E ⊗[F] v.adicCompletion F) * (c : E ⊗[F] v.adicCompletion F)),
    ∃ e : intV E v, (d : E ⊗[F] v.adicCompletion F) = 1 + (T : E ⊗[F] v.adicCompletion F) * (e : E ⊗[F] v.adicCompletion F) := by
  intro F E _ _ _ _ _ σ hdeg hσ hfix hun v T hT hunif M _ _ hM m hm d c hd hc
  obtain ⟨χ, hχ⟩ := GlobalTheory.PrimeOrderModule.exists_character (intV E v) M T hT hM
  obtain ⟨s, hs, hsχ⟩ := GlobalTheory.OverSplit.exists_splitting_of_character F E σ hdeg hσ hfix hun v T hT χ
  obtain ⟨⟨ε, hε⟩, -, -⟩ := GlobalTheory.OverResidue.residue_of_prime_card F E σ v s hs M T hT hM
    (fun a m ha => hχ a m (hsχ a ha))
  have hεm : ε m ≠ 0 := fun h => hm (ε.injective (h.trans (map_zero ε).symm))
  have key : ∀ (a : intV E v) (a' : v.adicCompletionIntegers F),
      (a' : v.adicCompletion F) = (s a).1 → a • m = 0 →
      a' ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    intro a a' h h0
    have h1 := hε a a' h m
    rw [h0, map_zero] at h1
    have h2 : IsLocalRing.residue _ a' * ε m = 0 := h1.symm
    exact (IsLocalRing.residue_eq_zero_iff _).1 ((mul_eq_zero.1 h2).resolve_right hεm)
  obtain ⟨hd1, hd2⟩ := (hs.2.2 d).1 d.2
  obtain ⟨hc1, -⟩ := (hs.2.2 c).1 c.2
  set d₁ : v.adicCompletionIntegers F := ⟨_, hd1⟩ with hd₁
  set d₂ : v.adicCompletionIntegers F := ⟨_, hd2⟩ with hd₂
  set c₁ : v.adicCompletionIntegers F := ⟨_, hc1⟩ with hc₁
  have m1 : d₁ - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
    key (d - 1) _ (by simp [hd₁]) hd
  have mT : (T : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
    key (T : intV E v) _ (by simp) (by rw [Nat.cast_smul_eq_nsmul, ← hM, card_nsmul_eq_zero'])
  have hrel : d₂ * d₁ = 1 + (T : v.adicCompletionIntegers F) * c₁ := by
    have h := congrArg (fun x => (s x).1) hc
    simp only [map_mul, map_add, map_one, map_natCast, hs.2.1] at h
    exact Subtype.ext (by simpa [hd₁, hd₂, hc₁, swapR] using h)
  have m2 : d₂ - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    have : d₂ - 1 = (T : v.adicCompletionIntegers F) * c₁ - d₂ * (d₁ - 1) := by
      linear_combination hrel
    rw [this]
    exact sub_mem (Ideal.mul_mem_right _ _ mT) (Ideal.mul_mem_left _ _ m1)
  obtain ⟨b₁, hb₁⟩ := hunif _ ((Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := d₁ - 1)).1 m1)
  obtain ⟨b₂, hb₂⟩ := hunif _ ((Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := d₂ - 1)).1 m2)
  refine ⟨⟨s.symm ((b₁ : v.adicCompletion F), (b₂ : v.adicCompletion F)), (hs.2.2 _).2 ?_⟩, s.injective ?_⟩
  · rw [s.apply_symm_apply]
    exact ⟨b₁.2, b₂.2⟩
  · have e1 : (s d).1 - 1 = (T : v.adicCompletion F) * b₁ := by
      have h := congrArg Subtype.val hb₁
      push_cast at h
      exact h
    have e2 : (s d).2 - 1 = (T : v.adicCompletion F) * b₂ := by
      have h := congrArg Subtype.val hb₂
      push_cast at h
      exact h
    rw [map_add, map_one, map_mul, map_natCast, s.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · simpa using sub_eq_iff_eq_add'.1 e1
    · simpa using sub_eq_iff_eq_add'.1 e2

end GlobalTheory.UnitaryScalarModT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeIntegralColumnMinorExpansion
section
open MvPolynomial

namespace GlobalTheory.WeylIntExpansion

theorem weyl_int_expansion : ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N), (∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r : Fin N => Y.rowLen r),
      ∑ J : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N),
        Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) f • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J =
      Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
        (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r)) • f) →
    ∀ f : MvPolynomial (Fin N × Fin N) ℤ, f ∈ Formalism.GradedWeylDivisibility.weyl ℤ N N (le_refl N) (fun r : Fin N => Y.rowLen r) →
    ∃ z : (∀ c : Fin (Y.rowLen 0), Fin (Y.colLen c) ↪o Fin N) → ℤ,
      (∀ J, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) =
        (z J : ℚ) * Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))
          (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) (fun r : Fin N => Y.rowLen r))) ∧
      ∑ J, z J • GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J = f := by
  intro N Y hY hrep f hf
  set μ : Fin N → ℕ := fun r => Y.rowLen r with hμ
  set N0 := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ) with hN0
  have hN0ne : N0 ≠ 0 :=
    ((Formalism.GradedWeylDivisibility.fockQPos _ _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl N) μ)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ N N le_rfl _)).ne'
  have hanti : Antitone μ := fun a b hab => Y.rowLen_anti _ _ hab
  have hfQ : Formalism.GradedWeylDivisibility.intQ N N f ∈ Formalism.GradedWeylDivisibility.bDual N N le_rfl μ ((Formalism.GradedWeylDivisibility.dualWeyl ℤ N N μ).map (Formalism.GradedWeylDivisibility.intQ N N)) := by
    rw [← GlobalTheory.StdDual.weylEqDualNabla N N le_rfl μ hanti]
    exact ⟨f, hf, rfl⟩
  have hmem : ∀ J, GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ N N μ := by
    intro J
    rw [hμ, GlobalTheory.WeylMinorDual.dualWeyl_eq_span_colProd ℤ N Y hY]
    exact Submodule.subset_span ⟨J, rfl⟩
  have hz : ∀ J, ∃ z : ℤ, Formalism.GradedWeylDivisibility.fockQ (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J)) = z * N0 :=
    fun J => hfQ.2 _ ⟨_, hmem J, rfl⟩
  choose z hz using hz
  refine ⟨z, hz, ?_⟩
  have hmap : ∀ J, map (Int.castRingHom ℚ) (GlobalTheory.WeylMinorDual.colProd ℤ N Y hY J) =
      GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J := fun J => by
    unfold GlobalTheory.WeylMinorDual.colProd
    exact Formalism.L2.DIV.fk_map_bidet _ _ _ _
  have h := hrep (map (Int.castRingHom ℚ) f) hfQ.1
  have hc : ∀ J, Formalism.GradedWeylDivisibility.fockQ (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) (map (Int.castRingHom ℚ) f) = z J * N0 :=
    fun J => by rw [(Formalism.GradedWeylDivisibility.fockQPos _ _ _).1, ← hmap, hz]
  simp only [hc] at h
  apply MvPolynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  apply smul_right_injective _ hN0ne
  simp only
  rw [← h, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [map_zsmul, hmap, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, mul_comm]

end GlobalTheory.WeylIntExpansion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsAtFiniteNonempty
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

open Formalism.HermitianLatticesTheory (localization₂)

namespace GlobalTheory.Mem.CosetFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

omit [StarRing E] in

theorem exists_reps (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (m : ℕ) (hm : m ≠ 0) :
    ∃ T : Set (Sp E n), T.Finite ∧ ∀ x ∈ N, ∃ t ∈ T, ∃ z ∈ N, x - t = (m : 𝓞 E) • z := by
  haveI : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  haveI : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  let M : Submodule ℤ N := LinearMap.range (LinearMap.lsmul ℤ N (m : ℤ))
  haveI : Finite (N ⧸ M) := by
    refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm)⟩, ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective M x
    show (m : ℤ) • (Submodule.Quotient.mk y : N ⧸ M) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, rfl⟩
  refine ⟨Set.range fun q : N ⧸ M => ((Quotient.out q : N) : Sp E n), Set.finite_range _, fun x hx => ?_⟩
  refine ⟨_, ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩, ?_⟩
  have h : (⟨x, hx⟩ : N) - Quotient.out (Submodule.Quotient.mk (p := M) ⟨x, hx⟩) ∈ M :=
    (Submodule.Quotient.eq M).1 (Quotient.out_eq _).symm
  obtain ⟨z, hz⟩ := h
  refine ⟨z, z.2, ?_⟩
  have h2 := congrArg Subtype.val hz
  simp only [LinearMap.lsmul_apply, AddSubgroupClass.coe_sub, natCast_zsmul] at h2
  rw [← h2, Nat.cast_smul_eq_nsmul]
  rfl

theorem exists_reps_loc (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (m : ℕ) (hm : m ≠ 0) :
    ∃ T : Set (Sp E n), T.Finite ∧
      ∀ x ∈ localization₂ P.asIdeal N, ∃ t ∈ T, ((m : E)⁻¹) • (x - t) ∈ localization₂ P.asIdeal N := by
  obtain ⟨T, hT, h⟩ := exists_reps N hN m hm
  refine ⟨T, hT, fun x hx => ?_⟩
  obtain ⟨s, hs, hsx⟩ := (mem_locP P N x).1 hx
  have hk : ∀ k : ℕ, s ^ (k + 1) • x ∈ N := fun k => by
    rw [pow_succ, mul_smul]; exact N.smul_mem _ hsx
  choose t ht z hz he using fun k => h _ (hk k)
  haveI := hT.to_subtype
  obtain ⟨i, j, hij, hEq⟩ : ∃ i j : ℕ, i < j ∧ t i = t j := by
    obtain ⟨a, b, hab, h1⟩ := Finite.exists_ne_map_eq_of_infinite (fun k => (⟨t k, ht k⟩ : T))
    have h1' : t a = t b := congrArg Subtype.val h1
    rcases lt_or_gt_of_ne hab with h2 | h2
    · exact ⟨a, b, h2, h1'⟩
    · exact ⟨b, a, h2, h1'.symm⟩
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨t p, ht p, (mem_locP P N _).2 ⟨s ^ (i + 1), fun hh => hs (P.isPrime.mem_of_pow_mem _ hh), ?_⟩⟩
  have hm' : (m : E) ≠ 0 := by exact_mod_cast hm
  have e1 : s ^ (i + 1) • (x - t p) = (m : 𝓞 E) • (z i - z (i + p + 1) + s ^ (i + 1) • z p) := by
    rw [smul_add, smul_sub (m : 𝓞 E), ← he i, ← he (i + p + 1), smul_comm (m : 𝓞 E), ← he p, hEq, smul_sub, smul_sub,
      ← mul_smul, ← pow_add, show i + 1 + (p + 1) = i + p + 1 + 1 by ring]
    abel
  rw [smul_comm, e1, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hm']
  exact N.add_mem (N.sub_mem (hz _) (hz _)) (N.smul_mem _ (hz _))

theorem exists_reps_pow (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (a b : ℤ) :
    ∃ T : Set (Sp E n), T.Finite ∧ ∀ x : Sp E n, ((qOf P : E) ^ a)⁻¹ • x ∈ localization₂ P.asIdeal N →
      ∃ t ∈ T, ((qOf P : E) ^ b)⁻¹ • (x - t) ∈ localization₂ P.asIdeal N := by
  have hq : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hq' : (qOf P : E) ≠ 0 := by exact_mod_cast hq
  obtain ⟨T, hT, h⟩ := exists_reps_loc P N hN (qOf P ^ (b - a).toNat) (pow_ne_zero _ hq)
  refine ⟨(fun t => (qOf P : E) ^ a • t) '' T, hT.image _, fun x hx => ?_⟩
  obtain ⟨t, ht, h1⟩ := h _ hx
  refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
  have h2 := (localization₂ P.asIdeal N).smul_mem ((qOf P ^ (a - b).toNat : ℕ) : 𝓞 E) h1
  rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h2
  have e : ((qOf P ^ (a - b).toNat : ℕ) : E) * ((qOf P ^ (b - a).toNat : ℕ) : E)⁻¹ = ((qOf P : E) ^ b)⁻¹ * (qOf P : E) ^ a := by
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_neg, ← zpow_add₀ hq', ← zpow_add₀ hq']
    congr 1
    omega
  rw [smul_smul, e, mul_smul, smul_sub, smul_inv_smul₀ (zpow_ne_zero _ hq')] at h2
  exact h2

theorem finite_cosets (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (a b : SB → ℤ) :
    {Y : Set (Sp E n) | ∃ y ∈ locLat SB N a, Y = {z | z - y ∈ locLat SB N b}}.Finite := by
  choose T hT h using fun P : SB => exists_reps_pow P.1 N hN (a P) (b P)
  refine ((Set.Finite.pi' hT).image fun t : SB → Sp E n =>
    {z | ∀ P : SB, ((qOf P.1 : E) ^ b P)⁻¹ • (z - t P) ∈ localization₂ P.1.asIdeal N}).subset ?_
  rintro Y ⟨y, hy, rfl⟩
  choose t ht h1 using fun P => h P y ((mem_locLat SB N a y).1 hy P)
  refine ⟨t, ht, ?_⟩
  ext z
  simp only [Set.mem_setOf_eq, mem_locLat]
  refine forall_congr' fun P => ?_
  have e : z - t P = (z - y) + (y - t P) := by abel
  rw [e, smul_add]
  exact (localization₂ P.1.asIdeal N).add_mem_iff_left (h1 P)

theorem ysAt_finite_nonempty : ∀ {X : Fields} {Pr : Primes X} (R : Ranks)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))), Submodule.IsLattice X.E N →
      ((ysAt R sel mu cst j).ys N).Finite ∧ ((ysAt R sel mu cst j).ys N).Nonempty := by
  intro X Pr R sel S mu cst j N hN
  unfold ysAt
  split_ifs
  · exact ⟨finite_cosets _ N hN.fg _ _, _, 0, zero_mem _, rfl⟩
  · exact ⟨Set.finite_singleton _, Set.singleton_nonempty _⟩

end GlobalTheory.Mem.CosetFin
end

