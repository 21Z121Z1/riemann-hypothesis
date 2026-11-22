import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemGlobalNormOfMemLocalNorms
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerRankVanishing
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0189
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitSemisimpleCuspForms
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOddOrderAtEvenElsewhere
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma mem_locSq_iff' (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (x : Fˣ) :
    x ∈ _root_.GlobalTheory.QNorm.locSq F S ↔
      (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) (x : F))) ∧
        ∀ σ : F →+* ℝ, IsSquare (σ (x : F)) := by
  unfold _root_.GlobalTheory.QNorm.locSq _root_.GlobalTheory.QNorm.finSq
  simp [_root_.GlobalTheory.QNorm.mem_sqSub]

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma pos_of_isSquare_real_embedding_unit {F : Type} [Field F] (σ : F →+* ℝ) (x : Fˣ)
    (h : IsSquare (σ (x : F))) : 0 < σ (x : F) := by
  obtain ⟨r, hr⟩ := h
  have hne : σ (x : F) ≠ 0 := (map_ne_zero σ).mpr x.ne_zero
  exact lt_of_le_of_ne (by rw [hr]; exact mul_self_nonneg r) (Ne.symm hne)

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exists_valuation_eq_exp_two_mul_of_isSquare_completion (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : F) (hx : x ≠ 0)
    (h : IsSquare (algebraMap F (v.adicCompletion F) x)) :
    ∃ n : ℤ, v.valuation F x = WithZero.exp (2 * n) := by
  obtain ⟨y, hy⟩ := h
  have hv : Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have hy0 : Valued.v y ≠ 0 := by
    intro h0
    rw [hy, map_mul, h0, zero_mul] at hv
    exact ((Valuation.ne_zero_iff _).mpr hx) hv.symm
  refine ⟨WithZero.log (Valued.v y), ?_⟩
  rw [← hv, hy, map_mul, two_mul, WithZero.exp_add, WithZero.exp_log hy0]

open NumberField IsDedekindDomain in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.exists_odd_order_at_even_elsewhere : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ)
    (σ₀ : F →+* ℝ), ¬ IsSquare (δ : F) →
    (∀ t : F, t ≠ 0 → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) ∨
        ∃ n : ℤ, v.valuation F t = WithZero.exp (2 * n)) →
      (∀ σ : F →+* ℝ, σ ≠ σ₀ → 0 < σ t) → 0 < σ₀ t) →
    ∀ v₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ t : F, t ≠ 0 ∧
      (∃ n : ℤ, v₀.valuation F t = WithZero.exp (2 * n + 1)) ∧
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v ≠ v₀ →
        IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) ∨
          ∃ n : ℤ, v.valuation F t = WithZero.exp (2 * n) := by
  intro F _ _ δ σ₀ hδ H v₀
  classical
  obtain ⟨S₀, hS₀, hδS₀, -⟩ := _root_.GlobalTheory.QNorm.exists_adm_mem_sUnits_local_norm_mem_sUnits_sup_normSub F δ hδ
  set S := insert v₀ S₀ with hSdef
  have hv₀S : v₀ ∈ S := Finset.mem_insert_self _ _
  have hS : _root_.GlobalTheory.QNorm.admitted F S :=
    hS₀.mono (Finset.subset_insert _ _)
  have hδS : δ ∈ _root_.GlobalTheory.QNorm.sUnits F S := by
    rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hδS₀ ⊢
    intro v hv
    exact hδS₀ v fun h => hv (Finset.mem_insert_of_mem h)
  obtain ⟨T, hST, hcard, hTsq, hpat⟩ :=
    _root_.GlobalTheory.QNorm.exists_auxiliary_places F δ S hS hδS hδ
  have htop := _root_.GlobalTheory.QNorm.sUnits_union_sup_finSq_eq_top F S T hS hST hpat
  set U := _root_.GlobalTheory.QNorm.sUnits F (S ∪ T) with hU
  set M := _root_.GlobalTheory.QNorm.locSq F S with hM
  have hgoodU : ∀ u ∈ U, ∀ v, v ∉ S → IsSquare (algebraMap F (v.adicCompletion F) (δ : F)) ∨
      ∃ n : ℤ, v.valuation F (u : F) = WithZero.exp (2 * n) := by
    intro u hu v hv
    by_cases hvT : v ∈ T
    · exact Or.inl (hTsq v hvT)
    · right
      refine ⟨0, ?_⟩
      rw [hU, _root_.GlobalTheory.QNorm.mem_sUnits] at hu
      rw [hu v (by simp [hv, hvT])]
      simp
  have hinf : M ⊓ U = _root_.GlobalTheory.QNorm.sqs U ⊓ U := by
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hyM, hyU⟩
      exact ⟨_root_.GlobalTheory.QNorm.mem_sqs_sUnits_of_isSquare F (S ∪ T) y hyU
        (_root_.GlobalTheory.QNorm.isSquare_of_mem_locSq F S T hS htop y hyU hyM), hyU⟩
    · rintro ⟨hysq, hyU⟩
      exact ⟨_root_.GlobalTheory.QNorm.sqs_le_locSq F U S hysq, hyU⟩
  have hrel : M.relIndex U = 2 ^ ((S ∪ T).card + Fintype.card (InfinitePlace F)) := by
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right,
      _root_.GlobalTheory.QNorm.relIndex_sqs_sUnits]
  obtain ⟨hM0, hMle⟩ := _root_.GlobalTheory.QNorm.index_locSq_le F S
  have hidx := _root_.GlobalTheory.QNorm.index_eq_relIndex_mul_index_sup U M
  have hunion : (S ∪ T).card = S.card + T.card := Finset.card_union_of_disjoint hST
  rw [hrel, hunion] at hidx
  have hsup0 : (U ⊔ M).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hidx
    exact hM0 hidx
  have hle2 : (U ⊔ M).index ≤ 2 := by
    have h4 : (4 : ℕ) ^ (S.card + Fintype.card (InfinitePlace F)) =
        2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_succ]
      congr 1
      omega
    have h : 2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * (U ⊔ M).index ≤
        2 ^ (S.card + T.card + Fintype.card (InfinitePlace F)) * 2 := by
      rw [← hidx, ← h4]
      exact hMle
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  obtain ⟨xs, hxs0, hxsS, hxsσ⟩ := _root_.GlobalTheory.QNorm.exists_approx_mod_squares F S (fun _ => 1)
    (fun σ => if σ = σ₀ then -1 else 1) (fun _ => one_ne_zero)
    (fun σ => by split_ifs <;> norm_num)
  simp only [mul_one] at hxsS
  have hxsσ₀ : σ₀ xs < 0 := by
    have h := hxsσ σ₀
    rw [if_pos rfl] at h
    linarith
  have hxsσ' : ∀ σ, σ ≠ σ₀ → 0 < σ xs := fun σ hσ => by
    have h := hxsσ σ
    rwa [if_neg hσ, mul_one] at h
  set X : Fˣ := Units.mk0 xs hxs0 with hX
  have hXnot : X ∉ U ⊔ M := by
    intro hXmem
    obtain ⟨y, hyU, z, hzM, hyz⟩ := Subgroup.mem_sup.mp hXmem
    rw [hM, mem_locSq_iff'] at hzM
    have hy : (y : F) = xs / z := by
      rw [eq_div_iff z.ne_zero, ← Units.val_mul, hyz, hX, Units.val_mk0]
    have hzpos : ∀ σ : F →+* ℝ, 0 < σ (z : F) := fun σ => pos_of_isSquare_real_embedding_unit σ z (hzM.2 σ)
    have hpos := H y y.ne_zero (fun v => by
      by_cases hv : v ∈ S
      · right
        apply exists_valuation_eq_exp_two_mul_of_isSquare_completion F v _ y.ne_zero
        rw [hy, map_div₀]
        exact (hxsS v hv).div (hzM.1 v hv)
      · exact hgoodU y hyU v hv) (fun σ hσ => by
        rw [hy, map_div₀]
        exact div_pos (hxsσ' σ hσ) (hzpos σ))
    rw [hy, map_div₀] at hpos
    have := (div_pos_iff_of_pos_right (hzpos σ₀)).mp hpos
    linarith
  have hidx2 : (U ⊔ M).index = 2 := by
    have hne1 : (U ⊔ M).index ≠ 1 := by
      intro h1
      exact hXnot (Subgroup.index_eq_one.mp h1 ▸ Subgroup.mem_top X)
    omega
  obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuation_exists_uniformizer F v₀
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  obtain ⟨xa, hxa0, hxaS, -⟩ := _root_.GlobalTheory.QNorm.exists_approx_mod_squares F S
    (fun v => if v = v₀ then algebraMap F (v.adicCompletion F) ϖ else 1) (fun _ => 1)
    (fun v => by
      split_ifs
      · exact (map_ne_zero _).mpr hϖ0
      · exact one_ne_zero)
    (fun _ => one_ne_zero)
  have hav₀ : ∃ n : ℤ, v₀.valuation F xa = WithZero.exp (2 * n + 1) := by
    have h := hxaS v₀ hv₀S
    rw [if_pos rfl, ← map_mul] at h
    obtain ⟨n, hn⟩ :=
      exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ (xa * ϖ) (mul_ne_zero hxa0 hϖ0) h
    have hva : v₀.valuation F xa ≠ 0 := (Valuation.ne_zero_iff _).mpr hxa0
    rw [map_mul, hϖ, ← WithZero.exp_log hva, ← WithZero.exp_add] at hn
    have h' := WithZero.exp_injective hn
    refine ⟨n, ?_⟩
    rw [← WithZero.exp_log hva]
    congr 1
    omega
  have haS : ∀ v ∈ S, v ≠ v₀ → IsSquare (algebraMap F (v.adicCompletion F) xa) := fun v hv hne => by
    have h := hxaS v hv
    rwa [if_neg hne, mul_one] at h
  set A : Fˣ := Units.mk0 xa hxa0 with hA
  obtain ⟨B, hBmem, hBv₀, hBS⟩ : ∃ B : Fˣ, B ∈ U ⊔ M ∧
      (∃ n : ℤ, v₀.valuation F (B : F) = WithZero.exp (2 * n + 1)) ∧
      ∀ v ∈ S, v ≠ v₀ → IsSquare (algebraMap F (v.adicCompletion F) (B : F)) := by
    by_cases hAmem : A ∈ U ⊔ M
    · exact ⟨A, hAmem, hav₀, haS⟩
    · refine ⟨A * X, (Subgroup.mul_mem_iff_of_index_two hidx2).mpr (iff_of_false hAmem hXnot),
        ?_, ?_⟩
      · obtain ⟨m, hm⟩ := exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ xs hxs0 (hxsS v₀ hv₀S)
        obtain ⟨n, hn⟩ := hav₀
        refine ⟨n + m, ?_⟩
        rw [Units.val_mul, hA, hX, Units.val_mk0, Units.val_mk0, map_mul, hn, hm,
          ← WithZero.exp_add]
        congr 1
        ring
      · intro v hv hne
        rw [Units.val_mul, hA, hX, Units.val_mk0, Units.val_mk0, map_mul]
        exact (haS v hv hne).mul (hxsS v hv)
  obtain ⟨u, huU, m, hmM, hum⟩ := Subgroup.mem_sup.mp hBmem
  rw [hM, mem_locSq_iff'] at hmM
  have hum' : (u : F) * m = B := by rw [← Units.val_mul, hum]
  have hu : (u : F) = B / m := by rw [eq_div_iff m.ne_zero, hum']
  refine ⟨u, u.ne_zero, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hBv₀
    obtain ⟨k, hk⟩ := exists_valuation_eq_exp_two_mul_of_isSquare_completion F v₀ m m.ne_zero (hmM.1 v₀ hv₀S)
    have hvu : v₀.valuation F (u : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
    have h := congrArg (v₀.valuation F) hum'
    rw [map_mul, hn, hk, ← WithZero.exp_log hvu, ← WithZero.exp_add] at h
    have h' := WithZero.exp_injective h
    refine ⟨n - k, ?_⟩
    rw [← WithZero.exp_log hvu]
    congr 1
    omega
  · intro v hne
    by_cases hv : v ∈ S
    · right
      apply exists_valuation_eq_exp_two_mul_of_isSquare_completion F v _ u.ne_zero
      rw [hu, map_div₀]
      exact (hBS v hv hne).div (hmM.1 v hv)
    · exact hgoodU u huU v hv

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceEmb
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

namespace GlobalTheory.EmbThroughCompletion

section Norm

theorem norm_le_one_of_isIntegral {R C : Type} [CommRing R] [NormedField C] [IsUltrametricDist C]
    [Algebra R C] (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {x : C} (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  let f : R →+* (NormedField.valuation (K := C)).integer :=
    (algebraMap R C).codRestrict _ (fun r => by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
      exact hR r)
  have h1 : IsIntegral (NormedField.valuation (K := C)).integer x :=
    hx.map_of_comp_eq f (RingHom.id C) (by ext r; rfl)
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h1
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe] at h2
  exact h2

variable {E C : Type} [Field E] [NumberField E] [NormedField C] [IsUltrametricDist C]

theorem norm_int_le_one (a : E →+* C) (x : 𝓞 E) : ‖a (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (R := ℤ) (fun r => by simpa using IsUltrametricDist.norm_intCast_le_one C r)
    (map_isIntegral_int a x.isIntegral_coe)

theorem norm_lt_one_iff (v : HeightOneSpectrum (𝓞 E)) (a b : E →+* C)
    (ha : ∀ x : 𝓞 E, ‖a (x : E)‖ < 1 ↔ x ∈ v.asIdeal) (hb : ∀ x : 𝓞 E, ‖b (x : E)‖ < 1 ↔ x ∈ v.asIdeal)
    (x : E) : ‖a x‖ < 1 ↔ ‖b x‖ < 1 := by
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  have hd : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ‖c ((d : 𝓞 E) : E)‖ = 1 :=
    fun c hc => le_antisymm (norm_int_le_one c _) (not_lt.1 fun h' => d.2 ((hc _).1 h'))
  rcases h with h | h
  · have key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) →
        (‖c x‖ < 1 ↔ n ∈ v.asIdeal) := by
      intro c hc
      have h1 := congrArg (fun y => ‖c y‖) h
      simp only [map_mul, norm_mul] at h1
      rw [← hc n]
      change ‖c x‖ * ‖c ((d : 𝓞 E) : E)‖ = ‖c (n : E)‖ at h1
      rw [hd c hc, mul_one] at h1
      rw [h1]
    rw [key a ha, key b hb]
  · have key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ¬ ‖c x‖ < 1 := by
      intro c hc hlt
      have h1 := congrArg (fun y => ‖c y‖) h
      simp only [map_mul, norm_mul] at h1
      change ‖c x‖ * ‖c (n : E)‖ = ‖c ((d : 𝓞 E) : E)‖ at h1
      rw [hd c hc] at h1
      have h2 := norm_int_le_one c n
      have h3 := norm_nonneg (c x)
      have h4 := norm_nonneg (c (n : E))
      nlinarith
    exact iff_of_false (key a ha) (key b hb)

end Norm

section Padic

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

theorem mem_OL_iff (K : Loc.FinExt l) (x : K.1) : x ∈ Loc.OL K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  refine (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).symm.trans
    ⟨fun h => norm_le_one_of_isIntegral (fun r => ?_) h, fun h => isIntegral_of_norm_le_one _ h⟩
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  exact r.2

theorem not_isUnit_iff (K : Loc.FinExt l) (x : Loc.OL K) :
    ¬ IsUnit x ↔ ‖((x : K.1) : PadicAlgCl l)‖ < 1 := by
  have hx := (mem_OL_iff K _).1 x.2
  constructor
  · intro h
    refine lt_of_le_of_ne hx fun h1 => h ?_
    have h0 : (x : K.1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : K.1)⁻¹, (mem_OL_iff K _).2 ?_⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    rw [IntermediateField.coe_inv, norm_inv, h1, inv_one]
  · intro h hu
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hu
    have hy' := (mem_OL_iff K _).1 y.2
    have h1 := congrArg (fun z : Loc.OL K => ‖((z : K.1) : PadicAlgCl l)‖) hy
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h1
    have h3 := norm_nonneg ((x : K.1) : PadicAlgCl l)
    have h4 := norm_nonneg ((y : K.1) : PadicAlgCl l)
    nlinarith

variable {E : Type} [Field E] [NumberField E]

theorem sum_eq_zero (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) {n : ℕ}
    (y : Fin n → E) (c : Fin n → ℚ_[l]) (hc : ∑ k, c k • a (y k) = 0) : ∑ k, c k • b (y k) = 0 := by
  have hd : DenseRange (Pi.map fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ f : E →+* PadicAlgCl l, IsClopen {c : Fin n → ℚ_[l] | ‖∑ k, c k • f (y k)‖ < 1} := by
    intro f
    have := (IsUltrametricDist.isClopen_ball (0 : PadicAlgCl l) 1).preimage
      (f := fun c : Fin n → ℚ_[l] => ∑ k, c k • f (y k)) (by fun_prop)
    convert this using 1
    ext c
    simp
  have key : ∀ c : Fin n → ℚ_[l], ‖∑ k, c k • a (y k)‖ < 1 → ‖∑ k, c k • b (y k)‖ < 1 := by
    intro c
    refine hd.induction_on c ?_ fun q => ?_
    · have := (hcl a).compl.isClosed.union (hcl b).isClosed
      convert this using 1
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      exact imp_iff_not_or
    · have e : ∀ f : E →+* PadicAlgCl l,
          ∑ k, (Pi.map (fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) q) k • f (y k) =
            f (∑ k, (q k : E) * y k) := by
        intro f
        simp [Algebra.smul_def]
      rw [e a, e b]
      exact (h _).1
  by_contra hne
  have hpos : 0 < ‖∑ k, c k • b (y k)‖ := norm_pos_iff.2 hne
  obtain ⟨r, hr⟩ := NormedField.exists_lt_norm ℚ_[l] ‖∑ k, c k • b (y k)‖⁻¹
  have h1 := key (r • c) (by
    simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, hc, smul_zero, norm_zero, zero_lt_one])
  simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, norm_smul] at h1
  rw [inv_lt_iff_one_lt_mul₀ hpos] at hr
  linarith

theorem exists_conj (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) :
    ∃ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, g (a x) = b x := by
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ E
  have hroot : Polynomial.aeval (b pb.gen) (minpoly ℚ_[l] (a pb.gen)) = 0 := by
    have h0 := minpoly.aeval ℚ_[l] (a pb.gen)
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range] at h0 ⊢
    simp only [← map_pow] at h0 ⊢
    exact sum_eq_zero a b h _ _ h0
  obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) hroot
  refine ⟨g, fun x => ?_⟩
  have : ((g : PadicAlgCl l →+* PadicAlgCl l).comp a).toRatAlgHom = b.toRatAlgHom :=
    pb.algHom_ext hg
  exact DFunLike.congr_fun this x

variable {Ω : Type} [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem exists_factor (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (hA : IsPlaceOver A v)
    (hj : ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) (b : E →+* Bw.LL.1)
    (hb : ∀ x : 𝓞 E, ‖((b (x : E) : Bw.LL.1) : PadicAlgCl l)‖ < 1 ↔ x ∈ v.asIdeal) :
    ∃ τ : Bw.Kw.1 →ₐ[ℚ_[l]] Bw.LL.1, ∀ x : E, τ ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ = b x := by
  obtain ⟨g, hg⟩ := exists_conj (Bw.j.comp (algebraMap E Ω)) (Bw.LL.1.val.toRingHom.comp b)
    (norm_lt_one_iff v _ _ (fun x => by
      rw [← hA x, ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, hj,
        RingHom.comp_apply, map_inv₀, norm_inv]
      generalize algebraMap E Ω (x : E) = y
      by_cases hy : y = 0
      · simp [hy]
      · have : 0 < ‖Bw.j y‖ := norm_pos_iff.2 ((map_ne_zero _).2 hy)
        simp only [hy, false_or, not_le]
        rw [one_lt_inv₀ this]) hb)
  let σ : Bw.Kw.1 →ₐ[ℚ_[l]] PadicAlgCl l := (g : PadicAlgCl l →ₐ[ℚ_[l]] PadicAlgCl l).comp Bw.Kw.1.val
  exact ⟨σ.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split σ), fun x => Subtype.ext (hg x)⟩

end Padic

end GlobalTheory.EmbThroughCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockQWordRowActAdj
section
open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.FockAdj

theorem fockQ_applyWord : Formalism.GradedWeylDivisibility.FockQWordAdj := by
  intro r n w
  induction w with
  | nil => intro F G; rfl
  | cons x w ih =>
    intro F G
    have h1 : applyWord ℚ (x :: w) F = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w F) := rfl
    have h2 : applyWord ℚ (transposeWord (x :: w)) G =
        applyWord ℚ (transposeWord w) (rowDiv ℚ x.2.1 x.1 x.2.2 G) := by
      simp [applyWord, transposeWord, List.foldr_append]
    rw [h1, h2, fockQRowDivAdj, ih]

theorem map_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℚ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    map (Rat.castHom ℂ) (rowAct ℚ g f) =
      rowAct ℂ (g.map (Rat.castHom ℂ)) (map (Rat.castHom ℂ) f) := by
  have : (map (Rat.castHom ℂ)).comp (rowAct ℚ (n := n) g).toRingHom =
      (rowAct ℂ (n := n) (g.map (Rat.castHom ℂ))).toRingHom.comp (map (Rat.castHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowAct]
    · intro v
      simp [rowAct]
  exact congrArg (fun φ => φ f) this

theorem fockQ_rowAct : Formalism.GradedWeylDivisibility.FockQRowAct := by
  intro r n g P Q
  have ht : (g.map (Rat.castHom ℂ)).conjTranspose = g.transpose.map (Rat.castHom ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h : ((fockQ (rowAct ℚ g P) Q : ℚ) : ℂ) = ((fockQ P (rowAct ℚ g.transpose Q) : ℚ) : ℂ) := by
    rw [lfockq_cast, lfockq_cast, map_rowAct, map_rowAct, fockRowAdj, ht]
  exact_mod_cast h

theorem fockQ_word_rowAct_adj : Formalism.GradedWeylDivisibility.FockQWordAdj ∧ Formalism.GradedWeylDivisibility.FockQRowAct :=
  ⟨fockQ_applyWord, fockQ_rowAct⟩

end GlobalTheory.FockAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisEmbeddingCount
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

namespace GlobalTheory.Proof.GaloisEmbeddingCount

theorem card_ringHom_of_isGalois (E F : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field F]
    (φ : E →+* F) : Nat.card (E →+* F) = Module.finrank ℚ E := by
  haveI : CharZero F := (RingHom.charZero_iff φ.injective).1 inferInstance
  letI : Algebra E F := φ.toAlgebra
  haveI : IsScalarTower ℚ E F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  rw [Nat.card_congr (RingHom.equivRatAlgHom E F), Nat.card_congr (Normal.algHomEquivAut ℚ F E),
    IsGalois.card_aut_eq_finrank]

end GlobalTheory.Proof.GaloisEmbeddingCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisUniformizerRingStableStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_uniformizer_ring_stable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (σ : Ainf l →+* Ainf l), (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.wittFixedFrobeniusPow K, σ w = w) → (∃ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ (GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s) = GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s * u) → ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s ∧ ∃ b ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ a - a = GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s * b := by
  first | exact @GlobalTheory.RingAsStable.ringAs_stable | exact GlobalTheory.RingAsStable.ringAs_stable | (intros; apply GlobalTheory.RingAsStable.ringAs_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitSemisimpleCuspFormsStatement
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTOperatorExplicit_semisimple_cuspForms : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (c : ℂ) (n : ℕ), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, (fun h => GlobalTheory.Hk.heckeT k q σ h - c • h)^[n] ⇑f = 0 → GlobalTheory.Hk.heckeT k q σ ⇑f = c • ⇑f := by
  first | exact @GlobalTheory.Hk.Semisimple.heckeT_semisimple | exact GlobalTheory.Hk.Semisimple.heckeT_semisimple | (intros; apply GlobalTheory.Hk.Semisimple.heckeT_semisimple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerCongruenceModularFunctionTowerLevelStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_congruence_modularFunctionTower_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s → ∀ W : ValuationSubring X.K, Dom X V W → ∀ (k : ℕ) (f : X.K), f ≠ 0 → Lev X (M₀ * l ^ k) f → (∃ c : Ω, W.valuation (algebraMap Ω X.K c * Nq X (M₀ * l ^ k) q f / X.gal s f - 1) < 1) ∧ ∃ c : Ω, W.valuation (algebraMap Ω X.K c * X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f / (X.gal s.symm f) ^ q - 1) < 1 := by
  first | exact @GlobalTheory.KZ.ES.kron_cong_level | exact GlobalTheory.KZ.ES.kron_cong_level | (intros; apply GlobalTheory.KZ.ES.kron_cong_level <;> assumption)
end

