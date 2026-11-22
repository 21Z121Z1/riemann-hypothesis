import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0054
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0024

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasis
section
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.UnramDict

section
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem t2Space_isNonarchimedeanLocalField_singleBlock : T2Space K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

theorem exists_pow_lt_value {a γ : ValueGroupWithZero K} (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ m < γ := by
  have e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have : MulArchimedean (ValueGroupWithZero K) := .comap e.toMonoidHom e.strictMono
  exact exists_pow_lt₀ ha (Units.mk0 γ hγ)

variable {K}

theorem exists_value_eq_zpow {π : K} (h0 : valuation K π ≠ 0) (h1 : valuation K π < 1)
    (hmax : ∀ x : K, valuation K x < 1 → valuation K x ≤ valuation K π) {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, valuation K x = valuation K π ^ m := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hb0 : e (valuation K π) ≠ 0 := by
    intro h
    exact h0 (e.injective (h.trans (map_zero e).symm))
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hey : e (valuation K y) = WithZero.exp (-1 : ℤ) := by rw [hy]; simp
  have hy1 : valuation K y < 1 := by
    rw [← e.strictMono.lt_iff_lt, hey, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hle : e (valuation K y) ≤ e (valuation K π) := e.strictMono.monotone (hmax y hy1)
  have hlt : e (valuation K π) < 1 := by simpa using e.strictMono h1
  have hb : e (valuation K π) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨b, hbe⟩ : ∃ b : ℤ, e (valuation K π) = WithZero.exp b := ⟨_, (WithZero.exp_log hb0).symm⟩
    rw [hbe] at hle hlt ⊢
    rw [hey, WithZero.exp_le_exp] at hle
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    congr 1
    omega
  have hx0 : e (valuation K x) ≠ 0 := by
    intro h
    exact (Valuation.ne_zero_iff _).2 hx (e.injective (h.trans (map_zero e).symm))
  refine ⟨-WithZero.log (e (valuation K x)), e.injective ?_⟩
  have hz : (WithZero.exp (-1 : ℤ)) ^ (-WithZero.log (e (valuation K x))) =
      e (valuation K x) := by
    rw [← WithZero.exp_zsmul]
    simpa using WithZero.exp_log hx0
  show e (valuation K x) = e (valuation K π ^ (-WithZero.log (e (valuation K x))))
  rw [map_zpow₀ e, hb, hz]

end

section Matrices

theorem mem_unitGL_iff {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} (g : GL (Fin n) F) :
    g ∈ unitGL (n := Fin n) F ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ intO F) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ((h : Matrix (Fin n) (Fin n) (intO F)) i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact (((h⁻¹ : GL (Fin n) (intO F)) : Matrix (Fin n) (Fin n) (intO F)) i j).2
  · rintro ⟨hA, hB⟩
    let f : intO F →+* F := (intO F).subtype
    let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, hA i j⟩
    let B : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, hB i j⟩
    have hinj : Function.Injective (f.mapMatrix (m := Fin n)) :=
      Matrix.map_injective Subtype.val_injective
    have hAf : f.mapMatrix A = (g : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hBf : f.mapMatrix B = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      ext i j; rfl
    have hAB : A * B = 1 := hinj (by rw [map_mul, hAf, hBf, map_one]; exact Units.mul_inv g)
    have hBA : B * A = 1 := hinj (by rw [map_mul, hAf, hBf, map_one]; exact Units.inv_mul g)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hAf⟩

end Matrices

section Extension

variable {k E : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra k E]

theorem value_algebraMap_le_iff [ValuativeExtension k E] (a b : k) :
    valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) ↔
      valuation k a ≤ valuation k b := by
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le,
    ValuativeExtension.vle_iff_vle]

theorem tendsto_pow_zero {x : E} (hx : valuation E x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt_value E hx hγ
  filter_upwards [eventually_ge_atTop m] with n hn
  show valuation E (x ^ n) < γ
  rw [map_pow]
  exact (pow_le_pow_right_of_le_one' hx.le hn).trans_lt hm

theorem continuous_algebraMap_of_lt_one [ValuativeExtension k E] {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1) :
    Continuous (algebraMap k E) := by
  refine continuous_of_continuousAt_zero (algebraMap k E) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt_value E h1 hγ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at h0
  have hmem : {a : k | valuation k a < valuation k (π ^ m)} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem (by simpa using pow_ne_zero m hπ0)
  filter_upwards [hmem] with a ha
  have h2 : valuation E (algebraMap k E a) < valuation E (algebraMap k E (π ^ m)) := by
    rw [← not_le, value_algebraMap_le_iff, not_le]
    exact ha
  show valuation E (algebraMap k E a) < γ
  refine h2.trans_le ?_
  rw [map_pow, map_pow]
  exact hm.le

theorem continuous_linearMap [FiniteDimensional k E] [ContinuousSMul k E] (f : E →ₗ[k] E) :
    Continuous f := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  haveI := t2Space_isNonarchimedeanLocalField_singleBlock E
  exact f.continuous_of_finiteDimensional

theorem value_lt_one_of_continuous (τ : E ≃ₐ[k] E) (hτ : Continuous τ) {x : E}
    (hx : valuation E x < 1) : valuation E (τ x) < 1 := by
  have ht : Tendsto (fun n : ℕ => τ (x ^ n)) atTop (𝓝 0) := by
    have h := (hτ.tendsto 0).comp (tendsto_pow_zero hx)
    rw [map_zero] at h
    exact h
  have hmem : {y : E | valuation E y < 1} ∈ 𝓝 (0 : E) :=
    (IsValuativeTopology.hasBasis_nhds_zero' E).mem_of_mem one_ne_zero
  obtain ⟨n, hn, hn0⟩ := ((ht.eventually hmem).and (eventually_gt_atTop 0)).exists
  by_contra hc
  have h1 : 1 ≤ valuation E (τ x) ^ n := one_le_pow₀ (not_lt.1 hc)
  have h2 : valuation E (τ (x ^ n)) < 1 := hn
  rw [map_pow, map_pow] at h2
  exact absurd h2 (not_lt.2 h1)

theorem value_le_one_of_continuous (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) (τ : E ≃ₐ[k] E) {x : E}
    (hx : valuation E x ≤ 1) : valuation E (τ x) ≤ 1 := by
  by_contra h
  have h1 : 1 < valuation E (τ x) := not_le.1 h
  have hy0 : valuation E (τ x) ≠ 0 := (zero_lt_one.trans h1).ne'
  have h2 : valuation E (τ x)⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1
  have h3 := value_lt_one_of_continuous τ.symm (hc _) h2
  rw [map_inv₀, AlgEquiv.symm_apply_apply, map_inv₀] at h3
  have hx0 : valuation E x ≠ 0 := by
    intro h0
    have : x = 0 := (Valuation.zero_iff _).1 h0
    simp [this] at hy0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 hx0)).1 h3) (not_lt.2 hx)

theorem value_eq_one_of_continuous (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) (τ : E ≃ₐ[k] E) {x : E}
    (hx : valuation E x = 1) : valuation E (τ x) = 1 := by
  refine le_antisymm (value_le_one_of_continuous hc τ hx.le) ?_
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 : valuation E x⁻¹ ≤ 1 := by rw [map_inv₀, hx, inv_one]
  have h2 := value_le_one_of_continuous hc τ h1
  rw [map_inv₀, map_inv₀] at h2
  have hy0 : valuation E (τ x) ≠ 0 := by simpa using hx0
  exact (inv_le_one₀ (zero_lt_iff.2 hy0)).1 h2

theorem value_map_eq (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1)
    (hmax : ∀ x : E, valuation E x < 1 → valuation E x ≤ valuation E (algebraMap k E π))
    (τ : E ≃ₐ[k] E) (x : E) : valuation E (τ x) = valuation E x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, hm⟩ := exists_value_eq_zpow h0 h1 hmax hx
  set p := algebraMap k E π with hp
  have hy : valuation E (x * p ^ (-m)) = 1 := by
    rw [map_mul, map_zpow₀, hm, ← zpow_add₀ h0]
    simp
  have h2 := value_eq_one_of_continuous hc τ hy
  rw [map_mul, map_zpow₀ τ, hp, τ.commutes, ← hp, map_mul, map_zpow₀, zpow_neg,
    mul_inv_eq_one₀ (zpow_ne_zero _ h0)] at h2
  rw [h2, hm]

end Extension

theorem unramifiedDictionary_a : PositivityTheory.Rg.Tf.Loc.D0a := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ _
  obtain ⟨π, h1, hmax⟩ := hun
  have h0 : valuation E (algebraMap k E π) ≠ 0 := by
    obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation E)
    intro h
    have := hmax r hr1
    rw [h] at this
    exact hr0 ((Valuation.zero_iff _).1 (le_antisymm this zero_le'))
  have hcont := continuous_algebraMap_of_lt_one h0 h1
  haveI : ContinuousSMul k E := continuousSMul_of_algebraMap k E hcont
  have hc : ∀ τ : E ≃ₐ[k] E, Continuous τ := fun τ => continuous_linearMap τ.toLinearMap
  have hval := value_map_eq hc h0 h1 hmax
  have hint : ∀ a : k, algebraMap k E a ∈ intO E ↔ a ∈ intO k := by
    intro a
    have := value_algebraMap_le_iff (E := E) a 1
    simpa [Valuation.mem_integer_iff] using this
  refine ⟨hval, hint, ?_, ?_, hcont, ?_⟩
  · intro n g
    rw [mem_unitGL_iff, mem_unitGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => hint _) (forall₂_congr fun i j => hint _)
  · intro τ n g
    have hτ : ∀ x : E, τ x ∈ intO E ↔ x ∈ intO E := by
      intro x
      simp only [Valuation.mem_integer_iff, hval]
    rw [mem_unitGL_iff, mem_unitGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => hτ _) (forall₂_congr fun i j => hτ _)
  · intro n
    exact Continuous.units_map _ (continuous_id.matrix_map hcont)

end GlobalTheory.CompanionTheory.UnramDict
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationOfLocalDichotomy
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.Idem

theorem val_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S),
    (∀ m : Ideal S, m.IsMaximal → Dich (Ideal.Quotient.mk (compI m) ϖ)) → Val ϖ := by
  intro S _ ϖ hD f g hfg
  obtain ⟨N, hN⟩ := hfg
  let Q : S → Prop := fun e => ∃ d, IsIdempotentElem d ∧ d * e = d ∧ d * f ∈ Ideal.span {g} ∧
    (e - d) * g ∈ Ideal.span {f}
  have hQ1 : Q 1 := by
    apply GlobalTheory.CompanionTheory.Idem.glue_idempotent_property Q
    · exact ⟨0, IsIdempotentElem.zero, by simp, by simp, by simp⟩
    · rintro e e' he he' ⟨d, hd, hde, hdf, hdg⟩
      refine ⟨d * e', hd.mul he', ?_, ?_, ?_⟩
      · calc d * e' * (e * e') = (d * e) * (e' * e') := by ring
          _ = d * e' := by rw [hde, he'.eq]
      · rw [mul_comm d e', mul_assoc]
        exact Ideal.mul_mem_left _ _ hdf
      · have h3 : (e * e' - d * e') * g = e' * ((e - d) * g) := by ring
        rw [h3]
        exact Ideal.mul_mem_left _ _ hdg
    · rintro e e' he he' hee ⟨d, hd, hde, hdf, hdg⟩ ⟨d', hd', hde', hdf', hdg'⟩
      have hdd : d * d' = 0 := by
        calc d * d' = (d * e) * (d' * e') := by rw [hde, hde']
          _ = (d * d') * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      have h1 : d * e' = 0 := by
        calc d * e' = (d * e) * e' := by rw [hde]
          _ = d * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      have h2 : d' * e = 0 := by
        calc d' * e = (d' * e') * e := by rw [hde']
          _ = d' * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      refine ⟨d + d', ?_, ?_, ?_, ?_⟩
      · show (d + d') * (d + d') = d + d'
        calc (d + d') * (d + d') = d * d + d' * d' + 2 * (d * d') := by ring
          _ = d + d' := by rw [hd.eq, hd'.eq, hdd, mul_zero, add_zero]
      · calc (d + d') * (e + e') = d * e + d * e' + (d' * e + d' * e') := by ring
          _ = d + d' := by rw [hde, hde', h1, h2]; ring
      · rw [add_mul]
        exact Ideal.add_mem _ hdf hdf'
      · have h3 : (e + e' - (d + d')) * g = (e - d) * g + (e' - d') * g := by ring
        rw [h3]
        exact Ideal.add_mem _ hdg hdg'
    · intro m hm
      have hprime := hm.isPrime
      have hspan : (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) ϖ) ^ N ∈
          Ideal.span {Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) f, Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) g} := by
        rw [← map_pow]
        have h4 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m)) hN
        rwa [Ideal.map_span, Set.image_pair] at h4
      rcases hD m hm _ _ ⟨N, hspan⟩ with hgf | hfg'
      · obtain ⟨c, hc⟩ := hgf
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hmem : f - g * a ∈ CrystallineSemistableComparison.R.compI m := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
        obtain ⟨e, he, hem, hex⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem
        have hef : e * f = e * (g * a) := by
          rw [mul_sub] at hex
          exact sub_eq_zero.1 hex
        refine ⟨e, he, hem, e, he, he.eq, ?_, by simp⟩
        rw [hef]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))
      · obtain ⟨c, hc⟩ := hfg'
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hmem : g - f * a ∈ CrystallineSemistableComparison.R.compI m := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
        obtain ⟨e, he, hem, hex⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem
        have heg : e * g = e * (f * a) := by
          rw [mul_sub] at hex
          exact sub_eq_zero.1 hex
        refine ⟨e, he, hem, 0, IsIdempotentElem.zero, by simp, by simp, ?_⟩
        rw [sub_zero, heg]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
  obtain ⟨d, hd, -, hdf, hdg⟩ := hQ1
  exact ⟨d, hd, hdf, hdg⟩

end GlobalTheory.CompanionTheory.Idem
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecCloseOfKerBasicColSq
section
open PositivityTheory.Rg.BcB.E1

noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem ker_sub_of_kerBasic (hK : KerBasic) (X : Ctx) {φ φ' : X.G → ℂ} (h : Tst φ) (h' : Tst φ')
    (x y : X.G) :
    ker X.Γ (fun z => φ z - φ' z) x y = ker X.Γ φ x y - ker X.Γ φ' x y := by
  unfold ker
  exact finsum_sub_distrib ((hK X φ h).1 x y) ((hK X φ' h').1 x y)

theorem enorm_sq_Lp_two {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : Lp ℂ 2 ν) :
    ‖f‖ₑ ^ 2 = ∫⁻ z, ‖(f : α → ℂ) z‖ₑ ^ 2 ∂ν := by
  rw [Lp.enorm_def]
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := (f : α → ℂ)) (μ := ν) (p := 2) (by norm_num)
  simpa using h

theorem enorm_sq_piLp_two {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (f : PiLp 2 E) :
    ‖f‖ₑ ^ 2 = ∑ l, ‖f l‖ₑ ^ 2 := by
  have h : ‖f‖₊ ^ 2 = ∑ l, ‖f l‖₊ ^ 2 := by
    apply NNReal.coe_injective
    push_cast
    simpa using PiLp.norm_sq_eq_of_L2 E f
  simp only [enorm_eq_nnnorm]
  exact_mod_cast congrArg (fun t : NNReal => (t : ℝ≥0∞)) h

theorem vecClose_of_kerBasic_colSq : KerBasic → ColSq → VecClose := by
  intro hK hC X ι _ Φ Φ' Ω ε y j k k' hΩ hΦ hk hk'
  set R : ℝ≥0∞ := ENNReal.ofReal ε ^ 2 * X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y with hR
  have key : ∀ l, ‖(k - k') l‖ₑ ^ 2 ≤ R := by
    intro l
    obtain ⟨t, t', s, s', hd⟩ := hΦ l
    have hT : Tst (fun z => Φ l j z - Φ' l j z) :=
      ⟨t.1.sub t'.1, t.2.sub t'.2⟩
    have hS : Function.support (fun z => Φ l j z - Φ' l j z) ⊆ Ω := by
      intro z hz
      by_contra hn
      have h1 : Φ l j z = 0 := by
        by_contra h0
        exact hn (s h0)
      have h2 : Φ' l j z = 0 := by
        by_contra h0
        exact hn (s' h0)
      exact hz (by simp [h1, h2])
    have hcol := hC X (fun z => Φ l j z - Φ' l j z) ε Ω hT hd hΩ hS y
    have hae : ((k l - k' l : Lp ℂ 2 X.ν) : X.G → ℂ) =ᵐ[X.ν]
        fun z => ker X.Γ (fun w => Φ l j w - Φ' l j w) z y := by
      filter_upwards [Lp.coeFn_sub (k l) (k' l), hk l, hk' l] with z h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, ker_sub_of_kerBasic hK X t t']
    have hsub : (k - k') l = k l - k' l := rfl
    rw [hsub, enorm_sq_Lp_two]
    calc ∫⁻ z, ‖((k l - k' l : Lp ℂ 2 X.ν) : X.G → ℂ) z‖ₑ ^ 2 ∂X.ν
        = ∫⁻ z, ‖ker X.Γ (fun w => Φ l j w - Φ' l j w) z y‖ₑ ^ 2 ∂X.ν :=
          lintegral_congr_ae (hae.mono fun z hz => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) hz)
      _ ≤ R := hcol
  rw [enorm_sq_piLp_two]
  calc ∑ l, ‖(k - k') l‖ₑ ^ 2 ≤ ∑ _l : ι, R := Finset.sum_le_sum fun l _ => key l
    _ = Fintype.card ι * R := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.KernelColumns

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecLimOf
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelColumns

theorem exists_delta (c : ℝ≥0∞) (hc : c ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ^ 2 * c ≤ ENNReal.ofReal ε ^ 2 := by
  have hpos : 0 < Real.sqrt (c.toReal + 1) := Real.sqrt_pos.2 (by positivity)
  refine ⟨ε / Real.sqrt (c.toReal + 1), div_pos hε hpos, ?_⟩
  have hδ : 0 ≤ ε / Real.sqrt (c.toReal + 1) := (div_pos hε hpos).le
  rw [← ENNReal.ofReal_pow hδ, ← ENNReal.ofReal_pow hε.le]
  have hct : c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hc).symm
  calc ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * c
      = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2) * ENNReal.ofReal c.toReal := by
        rw [← hct]
    _ = ENNReal.ofReal ((ε / Real.sqrt (c.toReal + 1)) ^ 2 * c.toReal) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (ε ^ 2) := ?_
  apply ENNReal.ofReal_le_ofReal
  have hsq : Real.sqrt (c.toReal + 1) ^ 2 = c.toReal + 1 := Real.sq_sqrt (by positivity)
  rw [div_pow, hsq, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : 0 ≤ ε ^ 2 := by positivity
  nlinarith

theorem vecLim_of (hCnt : CntBasic) (hCv : CvTest) (hCol : ColOp) (hA : ApproxU) (hVC : VecClose) :
    VecLim := by
  intro X ι _ Φ T y j k ε hΦ hT hk hε
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  set Ω₀ : Set X.G := ⋃ l, tsupport (Φ l j) with hΩ₀
  have hΩ₀c : IsCompact Ω₀ := isCompact_iUnion fun l => (hΦ l j).2.isCompact
  set Ω : Set X.G := Ω₀ * N with hΩ
  have hΩc : IsCompact Ω := hΩ₀c.mul hNc
  set c : ℝ≥0∞ := (Fintype.card ι : ℝ≥0∞) * (X.μ Ω⁻¹ * cnt X.Γ (Ω⁻¹ * Ω) y) with hc
  have hctop : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top ?_ ?_)
    · exact hΩc.inv.measure_lt_top.ne
    · exact (hCnt X).1 _ (hΩc.inv.mul hΩc) y
  obtain ⟨δ, hδ, hδc⟩ := exists_delta c hctop ε hε
  choose Wl hWl hWlP using fun l => hA X (Φ l j) δ (hΦ l j) hδ
  refine ⟨N ∩ ⋂ l, Wl l, Filter.inter_mem hN1 (Filter.iInter_mem.2 hWl), ?_⟩
  intro ψ hψ hsupp u hu
  have hsN : tsupport ψ ⊆ N := hsupp.trans Set.inter_subset_left
  have hsl : ∀ l, tsupport ψ ⊆ Wl l := fun l =>
    hsupp.trans (Set.inter_subset_right.trans (Set.iInter_subset _ l))
  have hvec : X.IsVec (fun l j => cv X.μ (Φ l j) ψ) y j (T u) := fun l =>
    (((hCol X ι ψ hψ.1).2 Φ T hΦ hT y j u hu).1 l)
  have hfin := hVC X ι (fun l j => cv X.μ (Φ l j) ψ) Φ Ω δ y j (T u) k hΩc (fun l => by
    have hcv := hCv X (Φ l j) ψ (hΦ l j) hψ.1
    refine ⟨hcv.1, hΦ l j, ?_, ?_, fun z => ((hWlP l ψ hψ (hsl l) z).1)⟩
    · exact hcv.2.1.trans (Set.mul_subset_mul (Set.subset_iUnion (fun l => tsupport (Φ l j)) l) hsN)
    · intro z hz
      exact ⟨z, Set.subset_iUnion (fun l => tsupport (Φ l j)) l (subset_tsupport _ hz), 1, h1N, mul_one z⟩)
    hvec hk
  have hle : ‖T u - k‖ₑ ^ 2 ≤ ENNReal.ofReal ε ^ 2 := by
    refine hfin.trans (le_trans (le_of_eq ?_) hδc)
    rw [hc]; ring
  have hle' : ‖T u - k‖ₑ ≤ ENNReal.ofReal ε := (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hle
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hε.le] at hle'
  exact hle'

end GlobalTheory.CompanionTheory.KernelColumns

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeSubspaceBoundStatement
section
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wedge_subspace_bound : WedgeSub := by
  first | exact @GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub | exact GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub | (intros; apply GlobalTheory.CompanionTheory.WedgeNorm.wedgeSub <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylDenominatorProductStatement
section
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weyl_denominator_product : ∀ {n : ℕ} (z : Fin n → ℂ), (∀ a, z a ≠ 0) → (∏ a, ∏ b, (1 + z a / z b)) * (∏ a, z a) ^ (n - 1) = 2 ^ n * (∏ p ∈ prs n, (z p.1 + z p.2)) ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | exact GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow | (intros; apply GlobalTheory.CompanionTheory.CoefId.prod_one_add_div_mul_prod_pow <;> assumption)
end

