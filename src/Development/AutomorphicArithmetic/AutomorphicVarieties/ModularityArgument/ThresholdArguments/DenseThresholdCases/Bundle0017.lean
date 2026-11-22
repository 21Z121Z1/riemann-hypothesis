import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0006

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TRegElt
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem regElt_place {Ω : Type} [Field Ω] [CharZero Ω] (p : ℕ) (hp : p.Prime) :
    ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 := by
  have hI : Ideal.span {((p : ℕ) : (Int.castRingHom Ω).range)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_exists_inv]
    rintro ⟨⟨_, c, rfl⟩, hc⟩
    have h1 : ((p : ℕ) : Ω) * ((c : ℤ) : Ω) = 1 := congrArg Subtype.val hc
    have h2 : ((p : ℕ) : ℤ) * c = 1 := by exact_mod_cast h1
    have h3 : ((p : ℕ) : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (by positivity) h2
    exact hp.one_lt.ne' (by exact_mod_cast h3)
  obtain ⟨A, -, hA⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI
  exact ⟨A, A.mem_nonunits_iff.1 (hA ⟨((p : ℕ) : (Int.castRingHom Ω).range), Ideal.mem_span_singleton_self _, by simp⟩)⟩
private theorem regElt_zpow_ne {G : Type} [Group G] (e : G) (he : ¬ IsOfFinOrder e) (n : ℤ) (hn : 0 < n) : e ^ n ≠ 1 := by
  intro h
  refine he (isOfFinOrder_iff_pow_eq_one.2 ⟨n.toNat, by omega, ?_⟩)
  rw [← zpow_natCast, Int.toNat_of_nonneg hn.le, h]
private theorem regElt_key {K : Type} [Field K] (e x : Kˣ) (m k : ℕ) (hm : 2 ≤ m) (hk : 0 < k)
    (hx : x ^ k = (e ^ (m : ℤ)) ^ k) (he : ¬ IsOfFinOrder e) :
    ¬ IsOfFinOrder x ∧ ∀ i : ℤ, |i| ≤ 2 →
      ((x : K) + ((x⁻¹ : Kˣ) : K)) ^ 2 - 2 ≠ (e : K) ^ i + (e : K) ^ (-i) := by
  have hsq : ∀ j : ℤ, |j| ≤ 2 → x ^ 2 ≠ e ^ j := by
    intro j hj h
    have hj' := (abs_le.1 hj).2
    have hpos : 0 < (2 * (m : ℤ) - j) * (k : ℤ) := by
      have : (0 : ℤ) < k := by exact_mod_cast hk
      have : (2 : ℤ) ≤ m := by exact_mod_cast hm
      apply mul_pos <;> omega
    refine regElt_zpow_ne e he _ hpos ?_
    have h1 : (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k = (e ^ j) ^ k := by
      rw [← hx, ← h, ← pow_add, ← pow_mul, two_mul]
    have h2 : e ^ ((2 * (m : ℤ) - j) * (k : ℤ)) = (e ^ (m : ℤ)) ^ k * (e ^ (m : ℤ)) ^ k * ((e ^ j) ^ k)⁻¹ := by
      simp only [← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    rw [h2, h1, mul_inv_cancel]
  refine ⟨fun hf => ?_, fun i hi h => ?_⟩
  · obtain ⟨n, hn, h⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    have hpos : 0 < (m : ℤ) * k * n := by
      have a : (0 : ℤ) < m := by exact_mod_cast (by omega : 0 < m)
      have b : (0 : ℤ) < k := by exact_mod_cast hk
      have c : (0 : ℤ) < n := by exact_mod_cast hn
      positivity
    refine regElt_zpow_ne e he _ hpos ?_
    rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← hx, ← pow_mul, mul_comm, pow_mul, h, one_pow]
  · have hx0 : (x : K) ≠ 0 := x.ne_zero
    have hE0 : ((e : K) ^ i) ≠ 0 := zpow_ne_zero _ e.ne_zero
    have hz : ((x : K) ^ 2 - (e : K) ^ i) * ((x : K) ^ 2 - ((e : K) ^ i)⁻¹) = 0 := by
      rw [Units.val_inv_eq_inv_val, zpow_neg] at h
      field_simp at h ⊢
      linear_combination (exp := 1) h
    rcases mul_eq_zero.1 hz with h0 | h0
    · refine hsq i hi (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val]
      exact sub_eq_zero.1 h0
    · refine hsq (-i) (by rwa [abs_neg]) (Units.ext ?_)
      rw [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, zpow_neg]
      exact sub_eq_zero.1 h0
theorem UpperTheory.V.Z.Sym.Ga.exists_regular_elt_in_open_subgroup_infinite_order :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)), _root_.UpperTheory.V.Z.Sym.AdInAlt ι M m r → ∀ H : Subgroup (G L Ω), IsOpen (H : Set (G L Ω)) → ∃ s ∈ H, s ∉ Ga.Bad r ∧ ∃ a b : (Qbar l)ˣ, ¬ IsOfFinOrder (a / b) ∧ (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C (a : Qbar l)) * (X - C (b : Qbar l)) := by
  intro L Ω _ _ _ _ _ _ l _ ι M m r hr H hH
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  obtain ⟨A, hA⟩ := regElt_place (Ω := Ω) l (Fact.out)
  obtain ⟨b0, k, κ, hk, ⟨g, hg⟩, hκ⟩ := hr.above A hA
  obtain ⟨s, hsH, hsI, hinf⟩ := UpperTheory.V.Z.Sym.Ga.ineInf L Ω l A hA H hH
  let t : ↥(Dec (F := L) A) := ⟨s, Ine_le_Dec A hsI⟩
  obtain ⟨h0, h1⟩ := hκ t hsI
  have hcp : (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly = (X - C ((κ 0 t : (Qbar l)ˣ) : Qbar l)) * (X - C ((κ 1 t : (Qbar l)ˣ) : Qbar l)) := by
    have e : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly =
        (r s : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly := by
      rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
      exact Matrix.charpoly_units_conj g _
    rw [← e, Matrix.charpoly_of_isUpperTriangular _ (fun i j hij => (hg t).1 i j hij), Fin.prod_univ_two]
    have e0 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((κ 0 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 0
    have e1 : ((g * r s * g⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = ((κ 1 t : (Qbar l)ˣ) : Qbar l) := (hg t).2 1
    rw [e0, e1]
  have hx : (κ 0 t / κ 1 t) ^ k = (cycBar L Ω l s ^ (m : ℤ)) ^ k := by
    rw [div_pow, h0, h1, zpow_add, mul_pow]
    exact mul_div_cancel_left _ _
  have key := regElt_key (cycBar L Ω l s) (κ 0 t / κ 1 t) m k hr.gap hk hx hinf
  refine ⟨s, hsH, ?_, κ 0 t, κ 1 t, key.1, hcp⟩
  rintro ⟨i, hi, hb⟩
  have huf := (UpperTheory.V.Z.Sym.Ga.ufFacts _ (r s)).1 _ _ hcp
  rw [huf] at hb
  exact key.2 i hi hb
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TToCsd
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
open scoped Matrix
private theorem eig_dual {K : Type} [Field K] (φ : K →+* ℂ) {n : ℕ} (M M' P : GL (Fin n) K) (t : K)
    (hP : (M : Matrix (Fin n) (Fin n) K)ᵀ * (P : Matrix (Fin n) (Fin n) K) * (M' : Matrix (Fin n) (Fin n) K) =
      t • (P : Matrix (Fin n) (Fin n) K)) (S S' : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S.map fun b => X - C b).prod)
    (h' : (M' : Matrix (Fin n) (Fin n) K).charpoly.map φ = (S'.map fun b => X - C b).prod) :
    S = S'.map fun a => φ t * a⁻¹ := by
  have h0 : (M : Matrix (Fin n) (Fin n) K)ᵀ = (P : Matrix (Fin n) (Fin n) K) *
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul, ← hP, Units.mul_inv_cancel_right, Units.mul_inv_cancel_right]
  have h1 : (M : Matrix (Fin n) (Fin n) K).charpoly =
      (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).charpoly := by
    rw [← Matrix.charpoly_transpose, h0, Matrix.coe_units_inv P, Matrix.charpoly_units_conj]
  rw [← Matrix.charpoly_map] at h'
  have h3 := GlobalTheory.charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map φ M') (φ t) _ h'
  have h4 : (t • ((M'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).map φ =
      φ t • (((Matrix.GeneralLinearGroup.map φ M')⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← map_inv]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    rfl
  rw [h1, ← Matrix.charpoly_map, h4, h3] at h
  have h5 := congrArg roots h
  rw [roots_multiset_prod_X_sub_C] at h5
  rw [← roots_multiset_prod_X_sub_C (S'.map fun a => φ t * a⁻¹), Multiset.map_map]
  exact h5.symm
private theorem cPl_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    cPl w = preplace (IsCMField.complexConj E).toRingEquiv w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))
private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm
private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))
private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : G (maximalRealSubfield F) Ω} (hc : IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)
private theorem frob_dual {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {r : G F Ω →* GL (Fin n) (Qbar l)} {θ : G F Ω →* (Qbar l)ˣ}
    {c : G (maximalRealSubfield F) Ω} {P : GL (Fin n) (Qbar l)} (hc : IsConjEl c)
    (hP : IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ)) * θ) P) {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {B B' : Multiset ℂˣ} {z : ℂˣ} (hB : FrobEig ι r w (algSat n (normV w) B))
    (hB' : FrobEig ι r (cPl w) (algSat n (normV (cPl w)) B')) (hz : CharEig ι θ w z) :
    B'.map (·⁻¹) = B.map (· * z⁻¹) := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have hL := isLift_conj hc
  have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
  rw [cPl_eq] at hB'
  have e := (hB' _ (isPlaceOver_preplace hL hAA hA)).2 (conjGal hL σ)
    (by rw [normV_preplace]; exact isFrob_conjGal hL hAA hσ)
  rw [normV_preplace] at e
  have h1 := eig_dual ι.toRingHom (r σ⁻¹) (r (conjGal hL σ)⁻¹) P _
    (hP σ⁻¹ (conjGal hL σ)⁻¹ (by rw [← map_inv]; exact AlgEquiv.ext fun _ => rfl)) _ _ ((hB A hA).2 σ hσ) e
  have h2 : ((cycBar F Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [cycZ_of_isFrob hw hA hσ, map_natCast, map_natCast]
  have hq0 : normV w ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at h2
    exact Units.ne_zero _ h2
  have hqR : (0 : ℝ) < normV w := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have h3 := (hz A hA).2 σ hσ
  set d : ℂ := ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact_mod_cast (Real.rpow_pos_of_pos hqR _).ne'
  have hdd : d * d = (normV w : ℂ) ^ ((n : ℤ) - 1) := by
    rw [hd, ← Complex.ofReal_mul, ← Real.rpow_add hqR, add_halves,
      show ((n : ℝ) - 1) = (((n : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring, Real.rpow_intCast]
    push_cast
    rfl
  have h4 : ι.toRingHom (((cycBar F Ω l ^ (1 - (n : ℤ)) * θ) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = d * d * z := by
    change ι _ = _
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, Units.val_mul, map_mul, map_inv (cycBar F Ω l),
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀, map_inv₀, map_natCast, h3, hdd, inv_zpow',
      neg_sub]
  have hS : ∀ B : Multiset ℂˣ, algSat n (normV w) B = B.map fun α : ℂˣ => d * (α : ℂ) := fun B => by
    simp only [algSat, ← hd, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map,
      Function.comp_def]
  rw [h4, hS, hS] at h1
  have h5 := congrArg (Multiset.map fun a : ℂ => d⁻¹ * a * (z : ℂ)⁻¹) h1
  simp only [Multiset.map_map, Function.comp_def] at h5
  apply Multiset.map_injective (f := (Units.val : ℂˣ → ℂ)) Units.val_injective
  simp only [Multiset.map_map, Function.comp_def]
  have := z.ne_zero
  refine (Multiset.map_congr rfl fun a _ => ?_).trans (h5.symm.trans (Multiset.map_congr rfl fun a _ => ?_))
  · rw [Units.val_inv_eq_inv_val]
    have := a.ne_zero
    field_simp
  · rw [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
theorem selfDual_of_automorphic_inputs :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.SelfDualC := by
  intro H F Ω _ _ _ _ _ _ l _ ι n hn r π hπ χ μ hμ c P hc hP
  refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse H.litN.aut.js.1 H.litN.aut.gk F n hn π _ ?_
  have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ((l : ℕ) : 𝓞 F) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have h2 := (conjSrc_injective (IsCMField.complexConj F).toRingEquiv).tendsto_cofinite.eventually hπ.2
  filter_upwards [Bc.normGal F Ω l ι χ μ hμ, hπ.2, h2, hl] with w ⟨hu, he⟩ ⟨B, hB, hF⟩ ⟨B', hB', hF'⟩ hw
  exact ⟨hu, B, B', hB, hB', frob_dual hc hP hw hF hF' he⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwist
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base
namespace UpperTheory.V.Sd.Tw
section
variable {Ω : Type} [Field Ω]
private theorem not_lt_of_coprime (A : ValuationSubring Ω) {q n : ℕ} (hq : A.valuation (q : Ω) < 1) (h : q.Coprime n) :
    ¬ A.valuation (n : Ω) < 1 := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (1 : Ω) = (a : Ω) * q + (b : Ω) * n := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab.symm
  have h1 : ∀ (a : ℤ) (x : Ω), A.valuation x < 1 → A.valuation ((a : Ω) * x) < 1 := fun a x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hx
  have := Valuation.map_add_lt A.valuation (h1 a _ hq) (h1 b _ hn)
  rw [← e, map_one] at this
  exact lt_irrefl _ this
variable [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem cls_frob {A : ValuationSubring Ω} {q N : ℕ} [NeZero N] (hq : A.valuation (q : Ω) < 1) (h : q.Coprime N)
    {t : G ℚ Ω} (ht : IsFrob (F := ℚ) A q t) : Chr.cls ℚ Ω N t = ZMod.unitOfCoprime q h := by
  refine (Chr.clsFacts ℚ Ω N).2.2.1 t _ fun ζ hζ => ?_
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod q hζ]
  refine eq_of_pow_eq_one A (not_lt_of_coprime A hq h) ?_ ?_
    (ht.2 ζ (valuation_eq_one_of_pow_eq_one A (NeZero.ne N) hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
private theorem cyc_frob {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {q : ℕ} (hp : q.Prime) (hq : A.valuation (q : Ω) < 1)
    (h : q.Coprime l) {t : G ℚ Ω} (ht : IsFrob (F := ℚ) A q t) : ((cycBar ℚ Ω l t : (Qbar l)ˣ) : Qbar l) = q := by
  haveI : Fact q.Prime := ⟨hp⟩
  obtain ⟨v, hv⟩ := (places ℚ Ω q A).1 fun hA => ((places ℚ Ω q A).2.1 hA).2 hq
  have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun hm =>
    not_lt_of_coprime A hq h (((places ℚ Ω l A).2.2.1 v hv).2 hm)
  have e : ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]) = (q : ℤ_[l]) :=
    PadicInt.ext_of_toZModPow.mp fun n => cycZ_toZModPow_eq hl hv ht.2 n
  change ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]) = _
  rw [e, map_natCast]
private theorem continuous_cyc (l : ℕ) [Fact l.Prime] :
    Continuous fun t : G ℚ Ω => ((cycBar ℚ Ω l t : (Qbar l)ˣ) : Qbar l) :=
  ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val).comp
    ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l))
variable (K : Type) [Field K] [NumberField K] [Algebra K Ω]
omit [IsAlgClosure ℚ Ω] in
private theorem cc_notMem [IsTotallyComplex K] {c : G ℚ Ω} (hc : Sd.IsCC c) : c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := hc
  intro h
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hj (algebraMap K Ω x)
  rw [h x] at this
  exact this.symm
omit [IsAlgClosure ℚ Ω] in
private theorem cc_sq {c : G ℚ Ω} (hc : Sd.IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  ext x
  apply j.injective
  rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply]
private theorem exists_chi [IsAlgClosure K Ω] (hK : Module.finrank ℚ K = 2) (N : ℕ) [NeZero N] (hN : N = (discr K).natAbs) :
    (Chr.cls ℚ Ω N).ker ≤ galOf ℚ K Ω ∧ ∃ χ : (ZMod N)ˣ →* ℂˣ, χ ^ 2 = 1 ∧
      ∀ t : G ℚ Ω, t ∉ galOf ℚ K Ω → χ (Chr.cls ℚ Ω N t) = -1 := by
  classical
  have hker : (Chr.cls ℚ Ω N).ker ≤ galOf ℚ K Ω := fun s hs => quadMu K Ω hK s fun ζ hζ => by
    rw [← hN] at hζ
    rw [Chr.cls_spec N s ζ hζ, MonoidHom.mem_ker.1 hs, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  have hi : (galOf ℚ K Ω).index = 2 := (galEmbTop ℚ K Ω).2.2.trans hK
  let δ : G ℚ Ω →* ℂˣ := MonoidHom.mk' (fun s => if s ∈ galOf ℚ K Ω then 1 else -1) fun a b => by
    by_cases ha : a ∈ galOf ℚ K Ω <;> by_cases hb : b ∈ galOf ℚ K Ω <;>
      simp [Subgroup.mul_mem_iff_of_index_two hi, ha, hb]
  have hδ : (Chr.cls ℚ Ω N).ker ≤ δ.ker := fun s hs => if_pos (hker hs)
  have hs := (Chr.clsOnto Ω N).1
  have e : ∀ t, (Chr.cls ℚ Ω N).liftOfSurjective hs ⟨δ, hδ⟩ (Chr.cls ℚ Ω N t) = δ t := fun t =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t
  refine ⟨hker, (Chr.cls ℚ Ω N).liftOfSurjective hs ⟨δ, hδ⟩, MonoidHom.ext fun u => ?_, fun t ht => (e t).trans (if_neg ht)⟩
  obtain ⟨t, rfl⟩ := hs u
  rw [MonoidHom.pow_apply, e]
  change (if t ∈ galOf ℚ K Ω then (1 : ℂˣ) else -1) ^ 2 = 1
  split_ifs <;> simp
private theorem ver_of_frob [IsAlgClosure K Ω] (hK : Module.finrank ℚ K = 2) {l : ℕ} [Fact l.Prime] (κ : G K Ω →* (Qbar l)ˣ)
    (hκ : Continuous κ) (T : ℕ) (hT : T ≠ 0)
    (H : ∀ (q : ℕ) (A : ValuationSubring Ω) (t : G ℚ Ω) (s : G K Ω), q.Prime → ¬ q ∣ T → A.valuation (q : Ω) < 1 →
      IsFrob (F := ℚ) A q t → t ∉ galOf ℚ K Ω → galEmb ℚ K Ω s = t * t →
      (κ s : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1)
    (s : G K Ω) (t : G ℚ Ω) (ht : t ∉ galOf ℚ K Ω) (hs : galEmb ℚ K Ω s = t * t) : κ s = -(cycBar ℚ Ω l t)⁻¹ := by
  obtain ⟨hemb, hopen, hi⟩ := galEmbTop ℚ K Ω
  have hsq : ∀ t : G ℚ Ω, ∃ s, galEmb ℚ K Ω s = t * t := fun t => by
    have := Subgroup.mul_self_mem_of_index_two (hi.trans hK) t
    rw [← range_galEmb] at this
    exact this
  choose g hg using hsq
  have hgc : Continuous g := hemb.continuous_iff.2 ((continuous_id.mul continuous_id).congr fun t => (hg t).symm)
  have hcl : IsClosed {t : G ℚ Ω | (κ (g t) : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1} :=
    isClosed_eq ((Units.continuous_val.comp (hκ.comp hgc)).mul (continuous_cyc l)) continuous_const
  have key : (κ (g t) : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1 := by
    by_contra hne
    obtain ⟨q, A, φ, hq, hqT, hA, hφ, h1, h2⟩ := ML.chebQ Ω _
      (hcl.isOpen_compl.inter ((galOf ℚ K Ω).isClosed_of_isOpen hopen).isOpen_compl) ⟨t, hne, ht⟩ T hT
    exact h1 (H q A φ (g φ) hq hqT hA hφ h2 (hg φ))
  rw [hemb.injective ((hg t).trans hs.symm)] at key
  rw [← mul_left_inj (cycBar ℚ Ω l t), neg_mul, inv_mul_cancel]
  exact Units.ext key
end
end UpperTheory.V.Sd.Tw
open UpperTheory.V.Sd.Tw in
theorem UpperTheory.V.Sd.twist_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Twist := by
  intro hP K Ω _ _ _ _ _ _ _ hK l hl hl2 hld ι c hc
  haveI : IsAlgClosure K Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  set N := (discr K).natAbs with hN
  have hN3 : 3 ≤ N := by
    have := abs_discr_gt_two (K := K) (by omega)
    rw [Int.abs_eq_natAbs] at this
    omega
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hker, χ, hχ2, hχ⟩ := exists_chi (Ω := Ω) K hK N hN
  have hχ1 : χ (-1) = -1 := by
    rw [← (Chr.clsFacts ℚ Ω N).2.2.2.1 c hc]
    exact hχ c (cc_notMem K hc)
  obtain ⟨Y, a, τ, hYa, ha1, ha0, hYu, ⟨m, hm0, hml, hm⟩, hYv⟩ := hecke K hK l hl.out hl2 hld N hN3 χ hχ2 hχ1
  obtain ⟨art, hart⟩ : ∃ art : Ideles K →* Gab K Ω, IsGlobalArtin art := hP.litN.aut.art K Ω
  obtain ⟨κ, hκ, hL⟩ := hart.exists_isLAdicOf ι (isAlgPos_of_isAlg hYa)
  have hNd : ∀ v : HeightOneSpectrum (𝓞 K), ((discr K : ℤ) : 𝓞 K) ∉ v.asIdeal → (N : 𝓞 K) ∉ v.asIdeal := fun v hv h => by
    apply hv
    rcases Int.natAbs_eq (discr K) with e | e
    · rw [e, Int.cast_natCast]
      exact h
    · rw [e, Int.cast_neg, Int.cast_natCast]
      exact neg_mem h
  have hnat : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → ∀ n : ℤ,
      ¬ A.valuation (n : Ω) < 1 → (n : 𝓞 K) ∉ w.asIdeal := fun A w hw n hn h => by
    have := (hw (n : 𝓞 K)).2 h
    exact hn (by simpa using this)
  have hnat' : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → ∀ n : ℕ,
      ¬ A.valuation (n : Ω) < 1 → (n : 𝓞 K) ∉ w.asIdeal := fun A w hw n hn => by
    simpa using hnat A w hw n (by simpa using hn)
  have hver := ver_of_frob K hK κ hκ (l * N) (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) fun q A t s hq hqT hA ht htK hs => by
    have hc' := (Nat.Prime.coprime_iff_not_dvd hq).2 hqT
    have hql := hc'.coprime_mul_right_right
    have hqN := hc'.coprime_mul_left_right
    have hAN := not_lt_of_coprime A hA hqN
    obtain ⟨w, hw, hwq, hfr⟩ := inert K Ω hK q hq A hA (((Chr.clsFacts ℚ Ω N).2.2.2.2 A hAN).trans hker) t ht htK
    rw [hL.frob_unr hart (Or.inl (hnat' A w hw l (not_lt_of_coprime A hA hql))) (hYu w (hnat' A w hw N hAN)) hw (hfr s hs),
      hYv q hqN w hwq, ← cls_frob hA hqN ht, hχ t htK, cyc_frob hq hA hql ht]
    have hq0 : (q : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    simp [hq0]
  refine ⟨κ, hκ, ⟨art, Y, a, τ, hart, isAlgPos_of_isAlg hYa, hL, ha1, ha0, fun v hv => hYu v (hNd v hv)⟩,
    fun s s' h => ?_, hver, fun A hAl hAd s hs => ?_, m, hm0, hml, fun A hAl s hs => ?_⟩
  · have hi : (galOf ℚ K Ω).index = 2 := (galEmbTop ℚ K Ω).2.2.trans hK
    have h1 : galEmb ℚ K Ω s * c ∉ galOf ℚ K Ω := fun h' =>
      cc_notMem K hc (((galOf ℚ K Ω).mul_mem_cancel_left (galEmb_mem ℚ K Ω s)).1 h')
    have h2 : c⁻¹ = c := inv_eq_of_mul_eq_one_right (cc_sq hc)
    have h3 : cycBar ℚ Ω l c = -1 := by
      have h4 : cycZ ℚ Ω l c = -1 := IsConjOm.cyc (E := ℚ) (show IsConjOm c.toRingEquiv from hc)
      change Units.map _ (cycZ ℚ Ω l c) = -1
      rw [h4]
      exact Units.ext (by simp)
    rw [← map_mul, hver (s * s') _ h1 (by rw [map_mul, h, h2]; simp only [mul_assoc]), map_mul, h3, mul_neg_one, inv_neg, neg_neg]
    rfl
  · by_cases hA : A = ⊤
    · rw [((places K Ω l A).2.1 hA).1, Subgroup.mem_bot] at hs
      rw [hs, map_one]
    · obtain ⟨w, hw⟩ := (places K Ω l A).1 hA
      exact (hL.unr_iff hart (Or.inl (hnat' A w hw l hAl)) hw).2 (hYu w (hNd w (hnat A w hw _ hAd))) s hs
  · by_cases hA : A = ⊤
    · rw [((places K Ω l A).2.1 hA).1, Subgroup.mem_bot] at hs
      rw [hs, map_one, one_pow]
    · obtain ⟨w, hw⟩ := (places K Ω l A).1 hA
      obtain ⟨x, hx, e⟩ := (hL.ine_image hart (Or.inl (hnat' A w hw l hAl)) hw _).1 ⟨s, hs, rfl⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← e, ← map_pow, ← Units.val_pow_eq_pow_val, hm w x hx]
      simp
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWDAway
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
private theorem UpperTheory.V.Af.isOpen_fixMu {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {M : ℕ}
    (hM : 1 ≤ M) : IsOpen {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine (Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet.subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M from hM)] using hζ
  have e : {s : G F Ω | ∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ} =
      ⋂ ζ ∈ {ζ : Ω | ζ ^ M = 1}, (MulAction.stabilizer (Ω ≃ₐ[F] Ω) ζ : Set (Ω ≃ₐ[F] Ω)) := by
    ext s
    simp [MulAction.mem_stabilizer_iff]
  rw [e]
  exact hfin.isOpen_biInter fun ζ _ => stabilizer_isOpen_of_isIntegral ζ
theorem UpperTheory.V.Af.weil_deligne_away_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WDAway := by
  intro _ F Ω _ _ _ _ _ l _ ι n M hM r _ w hl A h χ hχ hd x hx
  obtain ⟨g, hg⟩ := hd
  let r' : G F Ω →* GL (Fin n) (Qbar l) := (MulAut.conj g).toMonoidHom.comp r
  have hr' : ∀ s, r' s = g * r s * g⁻¹ := fun s => rfl
  have hx' : IsWDOf ι r' x := hx.of_conj hl g fun s => by rw [hr', inv_mul_cancel_right]
  obtain ⟨t, ht, φ, hφ, N, a, hN, ha, rfl⟩ := hx'
  have hs : IsSmooth (r'.comp (Weil h).subtype) := by
    refine .of_open ((UpperTheory.V.Af.isOpen_fixMu (F := F) (Ω := Ω) hM).preimage continuous_subtype_val)
      (fun ζ _ => rfl) fun σ hσ => Units.ext ?_
    change (r' σ : Matrix (Fin n) (Fin n) (Qbar l)) = 1
    rw [hr', hg σ σ.2]
    simp [fun i => hχ i σ hσ]
  obtain rfl : N = 0 := hN.unique ht ((isMonodromy_zero_iff (h := h)).mpr hs)
  refine ⟨fun i => (Units.map ι.toRingHom.toMonoidHom).comp (χ i), a, fun i s hs => ?_, rfl, ?_, fun s => ?_⟩
  · simp [hχ i s hs]
  · rw [ha.1, map_zero]
  · rw [IsFrobSS.ρ_ineIncl (ρ := hN.rep hl ht hφ ι) ha (hN.isSmooth_rep hl ht _ ι), hN.rep_apply, wdMat_zero, coe_ineIncl, hr',
      hg s s.2, toEndC_apply, Matrix.diagonal_map (map_zero ι)]
    rfl
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWeylC
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh
theorem UpperTheory.V.Af.weyl_complex_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Af.WeylC := by
  intro _ E _ _ _ n
  refine ⟨((n + 1) ^ 2) ^ (n * n * Fintype.card (E →+* ℂ)), n * n * Fintype.card (E →+* ℂ), fun m hm H hH => ?_⟩
  have hb := fun i => abs_le.1 (hH i)
  let ν : Fin n → ℕ := fun k => ((k : ℕ) + 1 + H - m k.rev : ℤ).toNat
  have hν : ∀ k, (ν k : ℤ) = (k : ℕ) + 1 + H - m k.rev := fun k => Int.toNat_of_nonneg (by have := hb k.rev; omega)
  have hanti : Antitone ν := by
    cases n with
    | zero => exact fun i => i.elim0
    | succ n =>
      refine Fin.antitone_iff_succ_le.2 fun i => ?_
      have h1 := hν i.succ
      have h2 := hν i.castSucc
      have h3 : m i.castSucc.rev < m i.succ.rev := hm (Fin.rev_lt_rev.2 Fin.castSucc_lt_succ)
      simp only [Fin.val_succ, Fin.val_castSucc] at h1 h2
      omega
  have hle : ∀ k, ν k ≤ n + 2 * H := fun k => by
    have h1 := hν k
    have h2 := hb k.rev
    have h3 := k.2
    omega
  obtain ⟨P, hP, hd, hw⟩ := UpperTheory.V.Weyl.existsScalar n ν hanti _ hle
  obtain ⟨Ξ, h1, h2⟩ := UpperTheory.V.WeylC.exists_tens (E := E) P hP _ hw (n + H)
  refine ⟨Ξ, fun τ => (UpperTheory.V.WeylC.algInfChar_iff _ _ _).2 ⟨by simp [UpperTheory.V.Af.infOf], fun u => ?_⟩, ?_⟩
  · rw [h2, UpperTheory.V.Af.infOf, Multiset.map_map, Multiset.map_map]
    congr 1
    refine (Fintype.prod_equiv Fin.revPerm _ _ fun k => ?_)
    have h3 : ((ν k : ℕ) : ℂ) = (k : ℕ) + 1 + H - m k.rev := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) (hν k)
    simp only [Function.comp_apply, Fin.revPerm_apply, h3]
    push_cast
    ring
  · refine h1.trans ((Nat.pow_le_pow_left hd _).trans ?_)
    rw [← pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith [Nat.zero_le (n * n * H), Nat.zero_le H, Nat.zero_le n]) _
end
end

