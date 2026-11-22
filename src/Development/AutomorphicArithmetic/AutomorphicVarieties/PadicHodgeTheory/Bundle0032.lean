import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0029
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0040
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantVectorOfFiniteImageAveraging
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.fixed_vector_descends_finite_image {Γ L D W : Type} [Group Γ] [Field L] [AddCommGroup D] [Module L D]
    [AddCommGroup W] [Module ℂ W] (a : Γ →* Module.End L D) (b : Γ →* Module.End ℂ W) (mk : D →+ W)
    (hs : Submodule.span ℂ (Set.range mk) = ⊤) (hc : ∀ g x, b g (mk x) = mk (a g x))
    [Finite (Γ ⧸ a.ker)] (y : W) (hy : y ≠ 0) (hi : ∀ g, b g y = y) :
    ∃ x : D, x ≠ 0 ∧ ∀ g, a g x = x := by
  classical
  by_contra hn
  push Not at hn
  let := Fintype.ofFinite (Γ ⧸ a.ker)
  let a' : Γ ⧸ a.ker →* Module.End L D := QuotientGroup.lift a.ker a le_rfl
  have ha : ∀ q : Γ ⧸ a.ker, a q.out = a' q := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have h0 : ∀ x : D, ∑ q : Γ ⧸ a.ker, a' q x = 0 := fun x => by
    by_contra hx
    obtain ⟨g, hg⟩ := hn _ hx
    refine hg ?_
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (g : Γ ⧸ a.ker)) _ _ fun q => ?_
    rw [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
    rfl
  have h1 : (∑ q : Γ ⧸ a.ker, b q.out) = 0 := by
    refine LinearMap.ext_on_range hs fun x => ?_
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    simp only [hc, ha]
    rw [← map_sum, h0, map_zero]
  have h2 := LinearMap.congr_fun h1 y
  rw [LinearMap.sum_apply, LinearMap.zero_apply] at h2
  simp only [hi, Finset.sum_const, Finset.card_univ] at h2
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h2
  exact hy ((smul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

theorem UpperTheory.exists_invariant_vector_of_finite_image_averaging :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ y : WDSpace P ι ρ, y ≠ 0 ∧ ∀ s, wdRho P ι Bw h hj ρ (ineIncl h s) y = y) → (∀ y : WDSpace P ι ρ, (∀ s, wdRho P ι Bw h hj ρ (ineIncl h s) y = y) → ∀ σ, wdRho P ι Bw h hj ρ σ y = y) → (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ s, weilD Bw h P ρ (ineIncl h s) x = x) ∧ ∀ x : ↥(Dpst P ρ), (∀ s, weilD Bw h P ρ (ineIncl h s) x = x) → ∀ σ, weilD Bw h P ρ σ x = x := by
  intro F Ω _ _ _ _ _ l _ ι A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ h1 h2
  refine ⟨?_, fun x hx σ => ?_⟩
  · obtain ⟨y, hy, hi⟩ := h1
    have := compactSpace_Ine (E := F) A
    have : Finite (Ine (F := F) A ⧸ (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h)).ker) :=
      Subgroup.quotient_finite_of_isOpen _ (isSmooth_weilD Bw h P ρ hj)
    exact UpperTheory.fixed_vector_descends_finite_image (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h))
      (MonoidHom.comp (wdRho P ι Bw h hj ρ) (ineIncl h))
      (AddMonoidHom.mk' (wdMk P ι ρ) (wdMk_add P ι ρ)) (span_wdMk P ι ρ)
      (fun g x => wdRho_mk P ι Bw h hj ρ _ x) y hy hi
  · have hc : ∀ (n : ℕ) τ, Commute (phiD P ρ ^ n) (weilD Bw h P ρ τ) := fun n τ => by
      refine Commute.pow_left ?_ n
      rw [weilD_apply]
      refine Commute.mul_right (phiD_actD P ρ _) ?_
      exact Commute.units_zpow_right (u := phiU P ρ) (Commute.refl _) _
    have hc' : ∀ (n : ℕ) τ, weilD Bw h P ρ τ ((phiD P ρ ^ n) x) = (phiD P ρ ^ n) (weilD Bw h P ρ τ x) :=
      fun n τ => (LinearMap.congr_fun (hc n τ).eq x).symm
    refine sub_eq_zero.mp
      (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L V ρ _ fun n => ?_)
    have h3 := h2 (wdMk P ι ρ ((phiD P ρ ^ n) x)) (fun s => by rw [wdRho_mk, hc', hx]) σ
    rw [wdRho_mk, hc'] at h3
    have h4 := wdMk_add P ι ρ ((phiD P ρ ^ n) (weilD Bw h P ρ σ x - x)) ((phiD P ρ ^ n) x)
    rw [← map_add, sub_add_cancel, h3] at h4
    exact left_eq_add.mp (h4.trans (add_comm _ _))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTotallyImaginaryPadicSqrt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K :=
  _root_.UpperTheory.Reformulated.B.Qh9.isCM_of_conj K h

private theorem exists_root_lift {Ω M : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field M] [CharZero M]
    (j : Ω →+* M) (g : Polynomial ℚ) (hg : g ≠ 0) (β : M) (hβ : Polynomial.aeval β g = 0) :
    ∃ b : Ω, j b = β ∧ Polynomial.aeval b g = 0 := by
  have hs : (g.map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
  have hne : g.map (algebraMap ℚ Ω) ≠ 0 := Polynomial.map_ne_zero hg
  have hroot : ((g.map (algebraMap ℚ Ω)).map j).IsRoot β := by
    rw [Polynomial.map_map, Subsingleton.elim (j.comp (algebraMap ℚ Ω)) (algebraMap ℚ M)]
    simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] using hβ
  obtain ⟨b, hb⟩ := hs.mem_range_of_isRoot hne hroot
  refine ⟨b, hb, j.injective ?_⟩
  have := Polynomial.aeval_algHom_apply j.toRatAlgHom b g
  rw [map_zero]
  change Polynomial.aeval (j b) g = j _ at this
  rw [← this, hb, hβ]

private theorem exists_sqrt_padic (l : ℕ) [Fact l.Prime] : ∃ d : ℚ_[l], d ^ 2 = 1 - 4 * l := by
  let P : Polynomial ℤ_[l] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (l : ℤ_[l])
  have h : ‖Polynomial.aeval (0 : ℤ_[l]) P‖ < ‖Polynomial.aeval (0 : ℤ_[l]) (Polynomial.derivative P)‖ ^ 2 := by
    have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp [P]
    exact inv_lt_one_of_one_lt₀ hl
  obtain ⟨z, hz, -⟩ := hensels_lemma h
  have hz' : z ^ 2 - z + l = 0 := by simpa [P] using hz
  have hz2 : (z : ℚ_[l]) ^ 2 - z + l = 0 := by exact_mod_cast congrArg (fun t : ℤ_[l] => (t : ℚ_[l])) hz'
  exact ⟨2 * z - 1, by linear_combination 4 * hz2⟩

theorem UpperTheory.exists_totally_imaginary_padic_sqrt :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (j : Ω →+* Om l) (K : FinExt l), ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (_ : Algebra E Ω) (_ : IsAlgClosure E Ω), IntermediateField.adjoin ℚ_[l] (Set.range fun x : E => j (algebraMap E Ω x)) = K.1 ∧ ∃ δ : E, δ ≠ 0 ∧ (∀ φ : E →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ) ∧ j (algebraMap E Ω δ) ∈ Set.range (algebraMap ℚ_[l] (Om l)) := by
  intro F Ω _ _ _ _ _ l _ j K
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero (Om l) := charZero_of_injective_algebraMap (algebraMap ℚ_[l] (Om l)).injective
  have halg : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  obtain ⟨β, g, hg, hβ, hreal, hK⟩ := UpperTheory.exists_totally_real_primitive_element_padic_finite_ext l K
  obtain ⟨b, hb, hbg⟩ := exists_root_lift j g hg.ne_zero β hβ
  obtain ⟨d, hd⟩ := exists_sqrt_padic l
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq (1 - 4 * l : Ω) (n := 2) two_pos
  obtain ⟨δ, hδ, hjδ⟩ : ∃ δ : Ω, δ ^ 2 = 1 - 4 * l ∧ j δ = algebraMap ℚ_[l] (Om l) d := by
    have h1 : j e ^ 2 = (algebraMap ℚ_[l] (Om l) d) ^ 2 := by
      rw [← map_pow, ← map_pow, he, hd]; simp [map_ofNat]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact ⟨e, he, h⟩
    · exact ⟨-e, by rw [neg_sq, he], by rw [map_neg, h, neg_neg]⟩
  let E : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ {b, δ}
  have hfin : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (halg.isAlgebraic x).isIntegral)
  have hNF : NumberField E := ⟨⟩
  let b' : E := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let δ' : E := ⟨δ, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hδ' : δ' ^ 2 = 1 - 4 * l := (algebraMap E Ω).injective (by
    rw [map_pow, map_sub, map_mul, map_one, map_ofNat, map_natCast]; exact hδ)
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hre : ∀ φ : E →+* ℂ, (φ δ').re = 0 ∧ (φ δ').im ≠ 0 := fun φ => by
    have h : φ δ' ^ 2 = 1 - 4 * l := by rw [← map_pow, hδ']; simp [map_ofNat]
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp [pow_two] at h1 h2
    have h3 : (φ δ').im ≠ 0 := by
      intro h0
      rw [h0] at h1
      nlinarith [mul_self_nonneg (φ δ').re]
    refine ⟨?_, h3⟩
    have : (φ δ').re * (φ δ').im = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right h3
  have hconj : ∀ φ : E →+* ℂ, starRingEnd ℂ (φ δ') = -φ δ' := fun φ => by
    apply Complex.ext <;> simp [(hre φ).1]
  have hbb : ∀ φ : E →+* ℂ, (φ b').im = 0 := fun φ => by
    apply hreal
    have h0 : Polynomial.aeval b' g = 0 := by
      apply (algebraMap E Ω).injective
      rw [← Polynomial.aeval_algebraMap_apply, map_zero]
      exact hbg
    have := Polynomial.aeval_algHom_apply φ.toRatAlgHom b' g
    rw [h0, map_zero] at this
    exact this
  have htc : IsTotallyComplex E := ⟨fun w => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro h
    have h1 : starRingEnd ℂ (w.embedding δ') = w.embedding δ' := congrArg (fun f : E →+* ℂ => f δ') h
    exact (hre w.embedding).2 (Complex.conj_eq_iff_im.mp h1)⟩
  have hCM : IsCMField E := by
    refine isCM_of_conj _ ?_
    rintro ⟨x, hx⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨b', fun φ => (Complex.conj_eq_iff_im.mpr (hbb φ)).symm⟩
      · exact ⟨-δ', fun φ => by rw [map_neg]; exact (hconj φ).symm⟩
    | algebraMap a =>
      refine ⟨(a : E), fun φ => ?_⟩
      change φ (a : E) = starRingEnd ℂ (φ (a : E))
      simp
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a + b, fun φ => ?_⟩
      rw [map_add, ha, hb, ← map_add, ← map_add]
      rfl
    | inv x hx ihx =>
      obtain ⟨a, ha⟩ := ihx
      refine ⟨a⁻¹, fun φ => ?_⟩
      rw [map_inv₀, ha, ← map_inv₀, ← map_inv₀]
      rfl
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a * b, fun φ => ?_⟩
      rw [map_mul, ha, hb, ← map_mul, ← map_mul]
      rfl
  have hAC : IsAlgClosure E Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) E⟩
  refine ⟨E, inferInstance, hNF, hCM, inferInstance, hAC, ?_, δ', ?_, hconj, ⟨d, hjδ.symm⟩⟩
  · apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      change j x ∈ K.1
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
        rcases hx with rfl | rfl
        · rw [hb, ← hK]; exact IntermediateField.mem_adjoin_simple_self _ _
        · rw [hjδ]; exact IntermediateField.algebraMap_mem _ _
      | algebraMap a => simp
      | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
      | inv x hx ihx => rw [map_inv₀]; exact inv_mem ihx
      | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy
    · rw [← hK]
      apply IntermediateField.adjoin.mono
      rintro _ rfl
      exact ⟨b', hb⟩
  · intro h
    have φ : E →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    exact (hre φ).2 (by rw [h]; simp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsWeilInvariantInDpstOfWeilDeligneInvariant
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.fixed_vector_descends_weil_group {Γ I K D W : Type} [Group Γ] [Group I] [Field K] [CharZero K]
    [AddCommGroup D] [Module K D] [FiniteDimensional K D]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (j : I →* Γ) (φ : Γ) (hn : ∀ s, ∃ t, j s * φ = φ * j t) (hg : ∀ σ, ∃ (n : ℤ) (t : I), σ = φ ^ n * j t)
    (a : Γ →* Module.End K D) (b : Γ →* Module.End ℂ W) (mk : D →+ W)
    (hs : Submodule.span ℂ (Set.range mk) = ⊤) (hc : ∀ g x, b g (mk x) = mk (a g x))
    [Finite (I ⧸ (a.comp j).ker)] (y : W) (hy : y ≠ 0) (hi : ∀ g, b g y = y) :
    ∃ x : D, x ≠ 0 ∧ ∀ g, a g x = x := by
  classical
  by_contra hno
  let := Fintype.ofFinite (I ⧸ (a.comp j).ker)
  let a' : I ⧸ (a.comp j).ker →* Module.End K D := QuotientGroup.lift _ (a.comp j) le_rfl
  have ha : ∀ q : I ⧸ (a.comp j).ker, a (j q.out) = a' q := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  let n : ℕ := Fintype.card (I ⧸ (a.comp j).ker)
  have hn0 : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let E : Module.End K D := ∑ q : I ⧸ (a.comp j).ker, a (j q.out)
  let E' : Module.End ℂ W := ∑ q : I ⧸ (a.comp j).ker, b (j q.out)
  have hE : ∀ x s, a (j s) (E x) = E x := fun x s => by
    simp only [E, LinearMap.sum_apply, map_sum, ha]
    refine Fintype.sum_equiv (Equiv.mulLeft (s : I ⧸ (a.comp j).ker)) _ _ fun q => ?_
    rw [Equiv.coe_mulLeft, map_mul, Module.End.mul_apply]
    rfl
  have hE1 : ∀ z, (∀ s, a (j s) z = z) → E z = n • z := fun z hz => by
    simp only [E, LinearMap.sum_apply, hz, Finset.sum_const, Finset.card_univ, n]
  have hE2 : E' y = n • y := by
    simp only [E', LinearMap.sum_apply, hi, Finset.sum_const, Finset.card_univ, n]
  have hEE : ∀ x, E' (mk x) = mk (E x) := fun x => by
    simp only [E, E', LinearMap.sum_apply, hc, map_sum]
  have hcan : ∀ z : D, n • z = 0 → z = 0 := fun z hz => by
    rw [← Nat.cast_smul_eq_nsmul K] at hz
    exact (smul_eq_zero.mp hz).resolve_left hn0
  let S : Module.End K D := a φ * E - E + n • 1 - E
  let S' : Module.End ℂ W := b φ * E' - E' + n • 1 - E'
  have hS : ∀ x, S x = a φ (E x) - E x + n • x - E x := fun x => rfl
  have hS' : ∀ x, S' x = b φ (E' x) - E' x + n • x - E' x := fun x => rfl
  have hinj : Function.Injective S := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : ∀ s, a (j s) (a φ (E x)) = a φ (E x) := fun s => by
      obtain ⟨t, ht⟩ := hn s
      rw [← Module.End.mul_apply, ← map_mul, ht, map_mul, Module.End.mul_apply, hE]
    have h2 := congrArg E hx
    rw [hS, map_sub, map_add, map_sub, map_nsmul, hE1 _ h1, hE1 _ (hE x), map_zero, add_sub_cancel_right,
      ← smul_sub] at h2
    have h3 : a φ (E x) = E x := sub_eq_zero.mp (hcan _ h2)
    have h4 : E x = 0 := by
      by_contra h0
      refine hno ⟨_, h0, fun g => ?_⟩
      obtain ⟨m, t, rfl⟩ := hg g
      rw [map_mul, Module.End.mul_apply, hE]
      exact (GlobalTheory.PstLaws.vecStab a (E x)).zpow_mem h3 m
    rw [hS, h4, map_zero, sub_zero, sub_zero, zero_add] at hx
    exact hcan _ hx
  have hsur := LinearMap.injective_iff_surjective.mp hinj
  have hsur' : Function.Surjective S' := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hsur x
    refine ⟨mk z, ?_⟩
    rw [hS, hS', hEE, hc, map_sub, map_add, map_sub, map_nsmul]
  refine hy (LinearMap.injective_iff_surjective.mpr hsur' ?_)
  rw [hS', hE2, map_nsmul, hi, map_zero, sub_self, zero_add, sub_self]

theorem UpperTheory.exists_weil_invariant_in_Dpst_of_weilDeligne_invariant :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ y : WDSpace P ι ρ, y ≠ 0 ∧ ∀ σ, wdRho P ι Bw h hj ρ σ y = y) → ∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ σ, weilD Bw h P ρ σ x = x := by
  intro F Ω _ _ _ _ _ l _ ι A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ h1
  obtain ⟨y, hy, hi⟩ := h1
  let a : ↥(Weil h) →* Module.End ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) :=
    { toFun := fun σ => urEnd P ρ (weilD Bw h P ρ σ) (weilD_mulD Bw h P ρ hj σ)
      map_one' := LinearMap.ext fun x => LinearMap.congr_fun (map_one (weilD Bw h P ρ)) ((toUr P ρ).symm x)
      map_mul' := fun σ τ => LinearMap.ext fun x =>
        LinearMap.congr_fun (map_mul (weilD Bw h P ρ) σ τ) ((toUr P ρ).symm x) }
  have := compactSpace_Ine (E := F) A
  have hle : (MonoidHom.comp (weilD Bw h P ρ) (ineIncl h)).ker ≤ (a.comp (ineIncl h)).ker := fun s hs =>
    LinearMap.ext fun x => LinearMap.congr_fun (MonoidHom.mem_ker.mp hs) ((toUr P ρ).symm x)
  have : Finite (Ine (F := F) A ⧸ (a.comp (ineIncl h)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ (Subgroup.isOpen_mono hle (isSmooth_weilD Bw h P ρ hj))
  have hn : ∀ s, ∃ t, ineIncl h s * frob h = frob h * ineIncl h t := fun s => by
    obtain ⟨t, ht⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (ineIncl h s * frob h)
    refine ⟨t, ?_⟩
    rw [deg_mul, deg_ineIncl, deg_frob, zero_add, zpow_one] at ht
    exact ht
  obtain ⟨x, hx, hf⟩ := UpperTheory.fixed_vector_descends_weil_group (ineIncl h) (frob h) hn
    (fun σ => ⟨deg σ, exists_eq_zpow_mul (deg_frob (h := h)) σ⟩) a (wdRho P ι Bw h hj ρ)
    ((AddMonoidHom.mk' (wdMk P ι ρ) (wdMk_add P ι ρ)).comp (toUr P ρ).symm.toAddMonoidHom) (span_wdMk P ι ρ)
    (fun g x => wdRho_mk P ι Bw h hj ρ g ((toUr P ρ).symm x)) y hy hi
  exact ⟨(toUr P ρ).symm x, hx, hf⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HasLocalLanglandsIffOfPlaceIso
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section SlopeTestRemainingChoices
open Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N Polynomial GlobalTheory.Pst UpperTheory.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem wdAt_of_model {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
    {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces B) {a : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (L₂ : FinExt l) (r₂ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₂.1)
    (hm₂ : IsModel B r L₂ r₂) (hV₂ : IsPst P (B.repE L₂ r₂)) :
    wdAt P ι B h hj r = wdPst P ι B h hj (B.repE L₂ r₂) := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj (r := r) ⟨L₂, r₂, hm₂, hV₂⟩
  have h₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have h₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have e : mapRep (IntermediateField.inclusion h₁).toRingHom r₁ =
      mapRep (IntermediateField.inclusion h₂).toRingHom r₂ := by
    ext g i j
    exact congrArg (fun f : ↥(Dec (F := E) A) →* GL (Fin a) (Om l) => (f g : Matrix (Fin a) (Fin a) (Om l)) i j)
      (hm₁.2.trans hm₂.2.symm)
  rw [e₁, BridgeParam.wdPst_enlarge P ι B h hj h₁ r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj h₂ r₂ hV₂, e]

private theorem wdRel_of_frobSS {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'} (φ : Ω ≃+* Ω')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {ρ' : Weil h' → Module.End ℂ V} {N : Module.End ℂ V}
    {a : WDRep h V} {b : WDRep h' V} (ha : IsFrobSS ρ N a) (hb : IsFrobSS ρ' N b)
    (hρ : ∀ σ σ', WeilRel φ σ σ' → ρ σ = ρ' σ') : WDRel φ (WD.mk a) (WD.mk b) := by
  let e := (Module.finBasis ℂ V).equivFun
  refine ⟨_, a.transport e, b.transport e, WD.sound (a.iso_transport e).symm, WD.sound (b.iso_transport e).symm,
    ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ a.N = e.conjAlgEquiv ℂ b.N
    rw [ha.1, hb.1]
  · show e.conjAlgEquiv ℂ (a.ρ σ) = e.conjAlgEquiv ℂ (b.ρ σ')
    have h1 := hρ σ σ' hσ
    have h2 := hb.2 σ'
    rw [← h1] at h2
    rw [(Module.End.isNilpotent_isSemisimple_unique (ha.2 σ).2 (a.semisimple σ) h2.2 (b.semisimple σ')
      ((ha.2 σ).1.symm.sub_left (Commute.refl _)) (h2.1.symm.sub_left (Commute.refl _))
      (by simp)).2]

private theorem eig_of_wdRel {E Ω E' Ω' : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'} {φ : Ω ≃+* Ω'}
    {y : WD h} {y' : WD h'} (H : WDRel φ y y') {σ : Weil h} {σ' : Weil h'} (hσ : WeilRel φ σ σ') :
    y.eig σ = y'.eig σ' := by
  obtain ⟨n, b, b', rfl, rfl, -, H⟩ := H
  rw [WD.eig_mk, WD.eig_mk, H σ σ' hσ]

set_option maxHeartbeats 1000000 in
private theorem exists_transfer {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F Ω] [Algebra K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O)
    (hj : Induces Bw) (hj' : Induces Bw') (hK : Bw'.Kw = Bw.Kw) (hJ : Bw'.j = Bw.j) (hL : Bw'.LL = Bw.LL)
    (hdeg : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ σ' → deg σ' = deg σ)
    (hq : normV w = normV v) (ι : Qbar l ≃+* ℂ) :
    ∃ t : ↥(Dec (F := K) A) →* ↥(Dec (F := F) A), Continuous t ∧
      (∀ (g : ↥(Dec (F := K) A)) (x : Ω), ((t g : ↥(Dec (F := F) A)) : G F Ω) x = (g : G K Ω) x) ∧
      ∀ (n : ℕ) (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)), IsPstAt (Loc.PP l) Bw r →
        IsPstAt (Loc.PP l) Bw' (r.comp t) ∧
          WDRel (RingEquiv.refl Ω) (wdAt (Loc.PP l) ι Bw h hj r) (wdAt (Loc.PP l) ι Bw' h' hj' (r.comp t)) := by
  obtain ⟨Kw, j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩ := Bw'
  dsimp only at hK hJ hL
  subst hK hJ hL
  set Bw' : LocBridge l K Ω (Dec (F := K) A) O :=
    ⟨Bw.Kw, Bw.j, j_E, j_dense, e, e_cont, e_symm_cont, e_comm, Bw.LL, LL_split, eO, eO_alg, eO_cont, eO_symm_cont⟩
    with hB
  have key : ∀ (g : ↥(Dec (F := K) A)) (x : Ω), ((Bw.e.symm (e g) : ↥(Dec (F := F) A)) : G F Ω) x = (g : G K Ω) x :=
    fun g x => Bw.j.injective (by rw [← Bw.e_comm, MulEquiv.apply_symm_apply, e_comm])
  refine ⟨(e.trans Bw.e.symm).toMonoidHom, Bw.e_symm_cont.comp e_cont, key, fun n r hr => ?_⟩
  obtain ⟨L, r', hm, hV⟩ := hr
  let r'' : ↥(Dec (F := K) A) →* GL (Fin n) ↥L.1 := r'.comp (e.trans Bw.e.symm).toMonoidHom
  have hm' : IsModel Bw' (r.comp (e.trans Bw.e.symm).toMonoidHom) L r'' :=
    ⟨hm.1, MonoidHom.ext fun g => DFunLike.congr_fun hm.2 (Bw.e.symm (e g))⟩
  have hrep : Bw'.repE L r'' = Bw.repE L r' := by
    refine MonoidHom.ext fun g => ?_
    have h1 : r'' (e.symm g) = r' (Bw.e.symm g) := by simp [r'']
    exact congrArg (fun m : GL (Fin n) ↥L.1 => Matrix.toLin' (m : Matrix (Fin n) (Fin n) ↥L.1)) h1
  have hV' : IsPst (Loc.PP l) (Bw'.repE L r'') := by rw [hrep]; exact hV
  refine ⟨⟨L, r'', hm', hV'⟩, ?_⟩
  rw [wdAt_of_model _ ι Bw h hj _ L r' hm hV, wdAt_of_model _ ι Bw' h' hj' _ L r'' hm' hV', hrep]
  generalize Bw.repE L r' = ρ at hV ⊢
  haveI := hV.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV]
  refine wdRel_of_frobSS _ (BridgeParam.isFrobSS_wdRep (Loc.PP l) ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep (Loc.PP l) ι Bw' h' hj' ρ) fun σ σ' hσ => ?_
  have h1 : weilToGK Bw h σ = weilToGK Bw' h' σ' := by
    have h2 : Subgroup.inclusion (Weil_le_Dec h) σ = Bw.e.symm (e (Subgroup.inclusion (Weil_le_Dec h') σ')) :=
      Subtype.ext (AlgEquiv.ext fun x => (hσ x).trans (key (Subgroup.inclusion (Weil_le_Dec h') σ') x).symm)
    exact (congrArg Bw.e h2).trans (Bw.e.apply_symm_apply _)
  have h3 : alpha l σ = alpha l σ' := by
    rw [alpha, alpha, hdeg σ σ' hσ, resDeg, resDeg, hq]
  have h4 : weilD Bw h (Loc.PP l) ρ σ = weilD Bw' h' (Loc.PP l) ρ σ' :=
    (weilD_apply Bw h (Loc.PP l) ρ σ).trans ((congrArg₂ (fun (g : ↥(GK Bw.Kw)) (m : ℤ) => actD (Loc.PP l) ρ g *
      ((phiU (Loc.PP l) ρ ^ (-m) : (Module.End ↥L.1 ↥(Dpst (Loc.PP l) ρ))ˣ) : Module.End ↥L.1 ↥(Dpst (Loc.PP l) ρ)))
      h1 h3).trans (weilD_apply Bw' h' (Loc.PP l) ρ σ').symm)
  refine wd_ext _ ι ρ fun x => ?_
  exact (wdRho_mk (Loc.PP l) ι Bw h hj ρ σ x).trans
    ((congrArg (wdMk (Loc.PP l) ι ρ) (LinearMap.congr_fun h4 x)).trans (wdRho_mk (Loc.PP l) ι Bw' h' hj' ρ σ' x).symm)

private theorem hasLT_transfer {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F Ω] [Algebra K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}
    {v : Plc F} {w : Plc K} (h : IsPlaceOver A v) (h' : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O)
    (hj : Induces Bw) (hj' : Induces Bw') (hK : Bw'.Kw = Bw.Kw) (hJ : Bw'.j = Bw.j) (hL : Bw'.LL = Bw.LL)
    (hdeg : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ σ' → deg σ' = deg σ)
    (hq : normV w = normV v) (ι : Qbar l ≃+* ℂ) (c : Weil h' →* Weil h)
    (hc : ∀ σ', WeilRel (RingEquiv.refl Ω) (c σ') σ')
    (hs : ∀ f : Weil h →* ℂˣ, IsSmooth f → IsSmooth (f.comp c))
    (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ) (a : Weil h →* (v.adicCompletion F)ˣ) (a' : Weil h' →* (w.adicCompletion K)ˣ)
    (hp : ∀ σ σ', WeilRel (RingEquiv.refl Ω) σ σ' →
      ∏ᶠ τ : Emb l v, τ.1 (a σ : v.adicCompletion F) ^ wt τ = ∏ᶠ τ : Emb l w, τ.1 (a' σ' : w.adicCompletion K) ^ wt' τ)
    (H : Loc.HasLT h Bw hj ι wt a) : Loc.HasLT h' Bw' hj' ι wt' a' := by
  obtain ⟨μ, ξ, hμ, hξ, hP, h1, h2⟩ := H
  obtain ⟨t, ht, key, hr⟩ := exists_transfer h h' Bw Bw' hj hj' hK hJ hL hdeg hq ι
  obtain ⟨h3, h4⟩ := hr 1 _ hP
  refine ⟨μ.comp t, ξ.comp c, hμ.comp ht, hs ξ hξ, h3, fun σ' => ?_, fun σ' => ?_⟩
  · have e : t (Subgroup.inclusion (Weil_le_Dec h') σ') = Subgroup.inclusion (Weil_le_Dec h) (c σ') :=
      Subtype.ext (AlgEquiv.ext fun x => (key _ x).trans (hc σ' x).symm)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, h1, hp _ _ (hc σ')]
  · have e := h2 (c σ')
    rw [eig_of_wdRel h4 (hc σ')] at e
    exact e

private theorem cont_symm {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 K)} (i : v.adicCompletion F ≃+* w.adicCompletion K)
    (hi : Continuous i) : Continuous i.symm := by
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : CharZero (w.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
  exact (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i hi).1

end SlopeTestRemainingChoices

theorem UpperTheory.hasLocalLanglands_iff_of_placeIso :
    ∀ {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : Plc F} {w : Plc K} (h : IsPlaceOver A v) (h' : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O) (hj : GlobalTheory.Pst.Induces Bw) (hj' : GlobalTheory.Pst.Induces Bw'), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → Bw'.LL = Bw.LL → ∀ (jF : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) jF i → ∀ (ι : Qbar l ≃+* ℂ) (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ), (∀ (τ : Emb l v) (τ' : Emb l w), τ.1 = τ'.1.comp i.toRingHom → wt τ = wt' τ') → ∀ (a : Weil h →* (v.adicCompletion F)ˣ) (a' : Weil h' →* (w.adicCompletion K)ˣ), (∀ σ σ', WeilRel (RingEquiv.refl Ω) σ σ' → a' σ' = Units.map i.toRingHom.toMonoidHom (a σ)) → (UpperTheory.V.Loc.HasLT h Bw hj ι wt a ↔ UpperTheory.V.Loc.HasLT h' Bw' hj' ι wt' a') := by
  intro F K Ω _ _ _ _ _ _ _ _ _ l _ A v w h h' O _ _ _ Bw Bw' hj hj' hK hJ hL jF i hP ι wt wt' hwt a a' ha
  obtain ⟨c, hc, hdeg, hq, hs⟩ := GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' _ _ i hP
  have hi' : Continuous i.symm := cont_symm i hP.cont
  let E : Emb l w ≃ Emb l v :=
    { toFun := fun τ => ⟨τ.1.comp i.toRingHom, τ.2.comp hP.cont⟩
      invFun := fun τ => ⟨τ.1.comp i.symm.toRingHom, τ.2.comp hi'⟩
      left_inv := fun τ => Subtype.ext (RingHom.ext fun x => congrArg τ.1 (i.apply_symm_apply x))
      right_inv := fun τ => Subtype.ext (RingHom.ext fun x => congrArg τ.1 (i.symm_apply_apply x)) }
  have hp : ∀ σ σ', WeilRel (RingEquiv.refl Ω) σ σ' →
      ∏ᶠ τ : Emb l v, τ.1 (a σ : v.adicCompletion F) ^ wt τ =
        ∏ᶠ τ : Emb l w, τ.1 (a' σ' : w.adicCompletion K) ^ wt' τ := by
    intro σ σ' hσ
    rw [← finprod_comp_equiv E]
    refine finprod_congr fun τ => ?_
    rw [hwt (E τ) τ rfl, ha σ σ' hσ]
    rfl
  have sy : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ' σ → WeilRel (RingEquiv.refl Ω) σ σ' :=
    fun σ σ' H z => (H z).symm
  have hd : ∀ (σ : Weil h) (σ' : Weil h'), WeilRel (RingEquiv.refl Ω) σ σ' → deg σ' = deg σ :=
    fun σ σ' H => by rw [← (hc σ σ').1 H, hdeg]
  refine ⟨hasLT_transfer h h' Bw Bw' hj hj' hK hJ hL hd hq ι c.symm.toMonoidHom
      (fun σ' => (hc _ _).2 (c.apply_symm_apply σ')) (fun f hf => (hs _ _).2 ?_) wt wt' a a' hp,
    hasLT_transfer h' h Bw' Bw hj' hj hK.symm hJ.symm hL.symm (fun σ' σ H => (hd σ σ' (sy _ _ H)).symm) hq.symm ι
      c.toMonoidHom (fun σ z => ((hc σ _).2 rfl z).symm) (fun f hf => (hs _ f).1 hf) wt' wt a' a
      fun σ' σ H => (hp σ σ' (sy _ _ H)).symm⟩
  have e : (f.comp c.symm.toMonoidHom).comp c.toMonoidHom = f :=
    MonoidHom.ext fun σ => congrArg f (c.symm_apply_apply σ)
  rw [e]
  exact hf
end

