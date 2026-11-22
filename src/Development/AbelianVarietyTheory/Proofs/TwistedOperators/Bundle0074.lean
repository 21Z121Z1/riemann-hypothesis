import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSquareMulInfinite
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlmostNormEtaProdEqNegOne
section
open NumberField IsDedekindDomain

namespace GlobalTheory.QuadSymbol

open NumberField IsDedekindDomain in
private theorem linearIndependent_one_of_notMem_range {K L : Type} [Field K] [Field L] [Algebra K L]
    {θ : L} (hθ : θ ∉ Set.range (algebraMap K L)) : LinearIndependent K ![(1 : L), θ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
  by_cases ht : t = 0
  · subst ht
    simp only [map_zero, zero_mul, add_zero, map_eq_zero] at hst
    exact ⟨hst, rfl⟩
  · exfalso
    apply hθ
    refine ⟨-s / t, ?_⟩
    have ht' : algebraMap K L t ≠ 0 := (map_ne_zero _).mpr ht
    rw [map_div₀, map_neg, div_eq_iff ht']
    linear_combination -hst

open NumberField IsDedekindDomain in
private theorem exists_basis_one_sqrt_nonsquare_of_finrank_two (K L : Type) [Field K] [CharZero K] [Field L]
    [Algebra K L] (h2 : Module.finrank K L = 2) :
    ∃ (e : Module.Basis (Fin 2) K L) (δ : K), e 0 = 1 ∧ e 1 * e 1 = algebraMap K L δ ∧
      ¬ IsSquare δ := by
  obtain ⟨θ, hθ⟩ : ∃ θ : L, θ ∉ Set.range (algebraMap K L) := by
    by_contra hcon
    push_neg at hcon
    have hbot : (⊥ : Subalgebra K L) = ⊤ :=
      eq_top_iff.mpr fun x _ => Algebra.mem_bot.mpr (hcon x)
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot
    omega
  let B := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_notMem_range hθ)
    (by simp [h2])
  have hB : ∀ i, B i = ![(1 : L), θ] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hθθ : θ * θ = algebraMap K L (B.repr (θ * θ) 0) +
      algebraMap K L (B.repr (θ * θ) 1) * θ := by
    conv_lhs => rw [← B.sum_repr (θ * θ)]
    rw [Fin.sum_univ_two, hB, hB, Algebra.smul_def, Algebra.smul_def]
    simp
  set q := B.repr (θ * θ) 0
  set p := B.repr (θ * θ) 1
  clear_value p q
  have hθ' : θ - algebraMap K L (p / 2) ∉ Set.range (algebraMap K L) := by
    rintro ⟨c, hc⟩
    exact hθ ⟨c + p / 2, by rw [map_add, hc]; ring⟩
  have hp2 : algebraMap K L (p / 2) * 2 = algebraMap K L p := by
    rw [← map_ofNat (algebraMap K L) 2, ← map_mul, div_mul_cancel₀ p two_ne_zero]
  have hδeq : algebraMap K L (q + p ^ 2 / 4) = algebraMap K L q + algebraMap K L (p / 2) ^ 2 := by
    rw [show q + p ^ 2 / 4 = q + (p / 2) ^ 2 by ring, map_add, map_pow]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_notMem_range hθ')
    (by simp [h2]), q + p ^ 2 / 4, ?_, ?_, ?_⟩
  · simp [coe_basisOfLinearIndependentOfCardEqFinrank]
  · simp only [coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.cons_val_one,
      Matrix.cons_val_zero]
    rw [hδeq]
    linear_combination hθθ - θ * hp2
  · rintro ⟨c, hc⟩
    have hsq : (θ - algebraMap K L (p / 2) - algebraMap K L c) *
        (θ - algebraMap K L (p / 2) + algebraMap K L c) = 0 := by
      have hc' := congrArg (algebraMap K L) hc
      rw [hδeq, map_mul] at hc'
      linear_combination hθθ - θ * hp2 + hc'
    rcases mul_eq_zero.mp hsq with h | h
    · exact hθ' ⟨c, by linear_combination -h⟩
    · exact hθ' ⟨-c, by rw [map_neg]; linear_combination -h⟩

open NumberField IsDedekindDomain in
private theorem exists_sq_sub_mul_sq_of_isSquare {K : Type} [Field K] [CharZero K] {d : K}
    (hd : d ≠ 0) (hsq : IsSquare d) (x : K) : ∃ a b : K, x = a ^ 2 - d * b ^ 2 := by
  obtain ⟨c, rfl⟩ := hsq
  have hc : c ≠ 0 := by rintro rfl; simp at hd
  refine ⟨(x + 1) / 2, (x - 1) / (2 * c), ?_⟩
  field_simp
  ring

open NumberField IsDedekindDomain in
private theorem exists_place_notMem_not_isSquare (F : Type) [Field F] [NumberField F] (δ : F)
    (hδ0 : δ ≠ 0) (hδ : ¬ IsSquare δ) (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ v, v ∉ S₀ ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) δ) := by
  classical
  by_contra hcon
  push_neg at hcon
  set d : Fˣ := Units.mk0 δ hδ0 with hd
  have hidx := (_root_.GlobalTheory.QNorm.two_pow_le_index_locNorm F δ S₀ hδ0).1
  haveI : (_root_.GlobalTheory.QNorm.locNorm F δ S₀).FiniteIndex := ⟨hidx⟩
  haveI := Fintype.ofFinite (Fˣ ⧸ _root_.GlobalTheory.QNorm.locNorm F δ S₀)
  let X : Finset Fˣ := insert d
    (Finset.univ.image fun q : Fˣ ⧸ _root_.GlobalTheory.QNorm.locNorm F δ S₀ => q.out)
  obtain ⟨S₁, -, hS₁⟩ := _root_.GlobalTheory.QNorm.exists_superset_mem_sUnits F X S₀
  obtain ⟨S, hS₁S, hadm⟩ := _root_.GlobalTheory.QNorm.exists_admissible_superset_finite_places F (S₁ ∪ S₀)
  have hmem : ∀ x ∈ X, x ∈ _root_.GlobalTheory.QNorm.sUnits F S :=
    hS₁ S (Finset.union_subset_left hS₁S)
  have hdδ : (d : F) = δ := rfl
  refine _root_.GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top F d S hadm (hmem d (Finset.mem_insert_self _ _))
    (by rwa [hdδ]) ?_
  have hle : _root_.GlobalTheory.QNorm.locNorm F δ S₀ ≤ _root_.GlobalTheory.QNorm.locNorm F (d : F) S := by
    intro x hx
    rw [hdδ]
    unfold _root_.GlobalTheory.QNorm.locNorm at hx ⊢
    simp only [Subgroup.mem_inf, Subgroup.mem_iInf] at hx ⊢
    refine ⟨fun v hv => ?_, hx.2⟩
    by_cases hv0 : v ∈ S₀
    · exact hx.1 v hv0
    · rw [_root_.GlobalTheory.QNorm.mem_normSub]
      haveI : CharZero (v.adicCompletion F) :=
        charZero_of_injective_algebraMap (algebraMap F _).injective
      exact exists_sq_sub_mul_sq_of_isSquare ((map_ne_zero _).mpr hδ0) (hcon v hv0) _
  rw [eq_top_iff]
  intro t _
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (_root_.GlobalTheory.QNorm.locNorm F δ S₀) t
  have ht : t = (QuotientGroup.mk t : Fˣ ⧸ _root_.GlobalTheory.QNorm.locNorm F δ S₀).out * (h : Fˣ)⁻¹ := by
    rw [hh]; group
  rw [ht]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hmem _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ _)))))
    (Subgroup.mem_sup_right (hle (Subgroup.inv_mem _ h.2)))

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.QuadSymbol.exists_almostNorm_etaProd_eq_neg_one :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [Algebra.IsQuadraticExtension K L],
      ∃ (x : _root_.GlobalTheory.QuadSymbol.FinFam K) (y : _root_.GlobalTheory.QuadSymbol.InfFam K),
        _root_.GlobalTheory.QuadSymbol.AlmostNorm K L x ∧ _root_.GlobalTheory.QuadSymbol.etaProd K L x y = -1 := by
  intro K L _ _ _ _ _ _
  classical
  obtain ⟨e, δ, he0, he1, hδ⟩ := exists_basis_one_sqrt_nonsquare_of_finrank_two K L
    (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact hδ ⟨0, by simp⟩
  obtain ⟨v, -, hv⟩ := exists_place_notMem_not_isSquare K δ hδ0 hδ ∅
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.QNorm.exists_local_nonnorm K v _
    ((map_ne_zero _).mpr hδ0) hv
  have hnot : Units.mk0 x hx0 ∉ _root_.GlobalTheory.QuadSymbol.normGroup K L (v.adicCompletion K) := by
    rw [_root_.GlobalTheory.QuadSymbol.mem_normGroup_iff_form e he0 he1]
    exact hx
  refine ⟨Pi.mulSingle v (Units.mk0 x hx0), 1, ?_, ?_⟩
  · unfold _root_.GlobalTheory.QuadSymbol.AlmostNorm
    refine (Set.finite_singleton v).subset fun v' hv' => ?_
    by_contra hne
    apply hv'
    rw [Pi.mulSingle_eq_of_ne (Set.mem_singleton_iff.not.mp hne)]
    exact Subgroup.one_mem _
  · unfold _root_.GlobalTheory.QuadSymbol.etaProd
    rw [finprod_eq_single _ v]
    · rw [Pi.mulSingle_eq_same, _root_.GlobalTheory.QuadSymbol.eta_eq_neg_one_iff.mpr hnot,
        Finset.prod_eq_one, mul_one]
      intro w _
      exact _root_.GlobalTheory.QuadSymbol.eta_eq_one_iff.mpr (Subgroup.one_mem _)
    · intro v' hv'
      rw [Pi.mulSingle_eq_of_ne hv']
      exact _root_.GlobalTheory.QuadSymbol.eta_eq_one_iff.mpr (Subgroup.one_mem _)

end GlobalTheory.QuadSymbol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSubgroupIndexTwo
section
open NumberField IsDedekindDomain GlobalTheory.CNorm GlobalTheory.QuadSymbol.NormIndex

namespace GlobalTheory.QuadraticValuationIndexTwo

theorem exists_mul_conj_iff {B E : Type} [Field B] [CharZero B] [Field E] [Algebra B E] {d : B}
    {θ : E} {σ : E ≃ₐ[B] E} (h : IsKum 2 (-1 : B) d θ σ) (x : B) :
    (∃ y : E, y * σ y = algebraMap B E x) ↔ Nm d x := by
  have kb := GlobalTheory.CNorm.kummer_basic 2 B E (-1) d θ σ h
  have hinv : ∀ z, σ (σ z) = z := fun z => kb.2.2.1 z
  have hfix := kb.2.2.2.1
  have hpow : θ ^ 2 = algebraMap B E d := h.pow
  have hconj : σ θ = -θ := by rw [h.conj, map_neg, map_one, neg_one_mul]
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap B E).injective
  have hθ : θ ≠ 0 := by
    intro h0
    apply h.nonpow 0
    apply (algebraMap B E).injective
    rw [← hpow, h0]
    simp
  constructor
  · rintro ⟨y, hy⟩

    obtain ⟨a, ha⟩ := hfix ((y + σ y) / 2) (by
      rw [map_div₀, map_add, hinv, map_ofNat, add_comm])
    obtain ⟨b, hb⟩ := hfix ((y - σ y) / (2 * θ)) (by
      rw [map_div₀, map_sub, hinv, map_mul, hconj, map_ofNat, mul_neg, div_neg, ← neg_div, neg_sub])
    have hy' : y = algebraMap B E a + algebraMap B E b * θ := by
      rw [← ha, ← hb]
      field_simp
      ring
    have hσy : σ y = algebraMap B E a - algebraMap B E b * θ := by
      rw [hy', map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hconj]
      ring
    refine ⟨a, b, (algebraMap B E).injective ?_⟩
    rw [← hy, hσy, hy']
    simp only [map_sub, map_mul, map_pow]
    rw [← hpow]
    ring
  · rintro ⟨a, b, rfl⟩
    refine ⟨algebraMap B E a + algebraMap B E b * θ, ?_⟩
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hconj]
    simp only [map_sub, map_mul, map_pow]
    rw [← hpow]
    ring

theorem exists_valuation_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ e : ℕ, v.valuation F ((2 : ℕ) : F) = WithZero.exp (-(e : ℤ)) := by
  have h0 : v.valuation F ((2 : ℕ) : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr (by norm_num)
  have hle : v.valuation F ((2 : ℕ) : F) ≤ 1 := by
    have := GlobalTheory.QuadSymbol.NormIndex.map_two_le (v.valuation F)
    simpa using this
  have hlog : WithZero.log (v.valuation F ((2 : ℕ) : F)) ≤ 0 := by
    rw [WithZero.log_le_iff_le_exp h0]
    simpa using hle
  refine ⟨(-WithZero.log (v.valuation F ((2 : ℕ) : F))).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]

theorem exists_subgroup_index_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] (d : B) (hd : ¬ IsSquare d) :
    ∃ N : Subgroup Bˣ, N.index = 2 ∧ ∀ x : Bˣ, x ∈ N ↔ Nm d (x : B) := by
  set K := v.adicCompletion F
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have : CharZero B := charZero_of_injective_algebraMap (algebraMap K B).injective
  have hnp : ∀ r : B, r ^ 2 ≠ d := fun r hr => hd ⟨r, by rw [← hr, sq]⟩

  obtain ⟨E, _, _, θ, σ, hK⟩ :=
    GlobalTheory.CNorm.exists_isKum 2 B (-1) d Nat.prime_two (IsPrimitiveRoot.neg_one 0 (by norm_num)) hnp
  have kb := GlobalTheory.CNorm.kummer_basic 2 B E (-1) d θ σ hK
  have : FiniteDimensional B E := kb.1
  let : Algebra K E := ((algebraMap B E).comp (algebraMap K B)).toAlgebra
  have : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FiniteDimensional K E := Module.Finite.trans B E
  obtain ⟨e, he⟩ := exists_valuation_two F v
  have hB := GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion 2 F v e B (by norm_num) he
  have hE := GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion 2 F v e E (by norm_num) he
  let σ' : Eˣ →* Eˣ := Units.map (σ : E →+* E).toMonoidHom
  let j : Bˣ →* Eˣ := Units.map (algebraMap B E).toMonoidHom
  have hσ' : ∀ y : Eˣ, ((σ' y : Eˣ) : E) = σ (y : E) := fun y => rfl
  have hj' : ∀ x : Bˣ, ((j x : Eˣ) : E) = algebraMap B E (x : B) := fun x => rfl
  have hj : Function.Injective j := fun a b hab =>
    Units.ext ((algebraMap B E).injective (by rw [← hj', ← hj', hab]))
  have hσ'2 : ∀ a, σ'^[2] a = a := fun a => Units.ext (kb.2.2.1 (a : E))

  have hfix : GlobalTheory.CNorm.fix σ' = j.range := by
    ext x
    rw [GlobalTheory.CNorm.mem_fix, MonoidHom.mem_range]
    constructor
    · intro hx
      have hx' : σ (x : E) = x := by rw [← hσ', hx]
      obtain ⟨a, ha⟩ := kb.2.2.2.1 (x : E) hx'
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact x.ne_zero (by rw [ha, map_zero])
      exact ⟨Units.mk0 a ha0, Units.ext (by rw [hj', Units.val_mk0, ha])⟩
    · rintro ⟨b, rfl⟩
      exact Units.ext (by rw [hσ', hj', AlgEquiv.commutes])
  have hnrm : ∀ y : Eˣ, ((GlobalTheory.CNorm.nrm σ' 2 y : Eˣ) : E) = (y : E) * σ y := by
    intro y
    rw [GlobalTheory.CNorm.nrm_apply, Finset.prod_range_succ, Finset.prod_range_one]
    rfl

  have hker : (GlobalTheory.CNorm.nrm σ' 2).ker ≤ (GlobalTheory.CNorm.dif σ').range := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : ∏ i ∈ Finset.range 2, σ^[i] (y : E) = 1 := by
      rw [Finset.prod_range_succ, Finset.prod_range_one]
      have := congrArg Units.val hy
      rw [hnrm] at this
      exact this
    obtain ⟨z, hz0, hz⟩ := kb.2.2.2.2.1 (y : E) h1
    refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
    rw [GlobalTheory.CNorm.dif_apply, Units.val_div_eq_div_val, hσ', Units.val_mk0, hz]
  have hR2 : (GlobalTheory.CNorm.dif σ').range.relIndex (GlobalTheory.CNorm.nrm σ' 2).ker = 1 :=
    Subgroup.relIndex_eq_one.mpr hker
  have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hIE : GlobalTheory.CNorm.pIdx 2 (⊤ : Subgroup Eˣ) ≠ 0 := by
    rw [hE.2]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (pow_ne_zero _ hq))) hE.1

  obtain ⟨-, -, -, -, heq⟩ := GlobalTheory.CNorm.herbrand_prime_order 2 Eˣ σ' Nat.prime_two hσ'2 hIE hE.1
  rw [hfix, hR2, GlobalTheory.CNorm.pIdx_range_of_injective 2 j hj, GlobalTheory.CNorm.pTor_range_of_injective 2 j hj,
    hE.2, hB.2] at heq
  have hrank : Module.finrank K E = Module.finrank K B * 2 := by
    rw [← Module.finrank_mul_finrank K B E, kb.2.1]
  rw [hrank, pow_mul] at heq
  set Q := (Ideal.absNorm v.asIdeal ^ e) ^ Module.finrank K B
  set TE := GlobalTheory.CNorm.pTor 2 (⊤ : Subgroup Eˣ)
  set TB := GlobalTheory.CNorm.pTor 2 (⊤ : Subgroup Bˣ)
  set R := (GlobalTheory.CNorm.nrm σ' 2).range.relIndex j.range
  have hX : Q ^ 2 * TE * TB ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (pow_ne_zero _ hq))) hE.1)
      (pow_ne_zero _ hB.1)
  have hR : R = 2 := by
    have h4 : (R * 2) * (Q ^ 2 * TE * TB ^ 2) = 4 * (Q ^ 2 * TE * TB ^ 2) := by
      have e21 : (2 : ℕ) - 1 = 1 := rfl
      rw [e21, pow_one, one_pow, one_mul] at heq
      calc (R * 2) * (Q ^ 2 * TE * TB ^ 2) = R * (2 * Q ^ 2 * TE) * TB ^ 2 := by ring
        _ = TE * (2 * Q * TB) ^ 2 := heq
        _ = 4 * (Q ^ 2 * TE * TB ^ 2) := by ring
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hX) h4
    omega
  refine ⟨(GlobalTheory.CNorm.nrm σ' 2).range.comap j, ?_, ?_⟩
  · rw [Subgroup.index_comap]
    exact hR
  · intro x
    rw [Subgroup.mem_comap, MonoidHom.mem_range, ← exists_mul_conj_iff hK (x : B)]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨(y : E), ?_⟩
      rw [← hnrm, hy, hj']
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hy
        exact x.ne_zero ((algebraMap B E).injective (by rw [← hy, map_zero]))
      refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
      rw [hnrm, hj', Units.val_mk0]
      exact hy

theorem norm_index_two (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (B : Type) [Field B] [Algebra (v.adicCompletion F) B]
    [FiniteDimensional (v.adicCompletion F) B] (d : B) (hd : ¬ IsSquare d) :
    (∃ c : B, c ≠ 0 ∧ ¬ Nm d c) ∧
      ∀ x y : B, x ≠ 0 → y ≠ 0 → ¬ Nm d x → ¬ Nm d y → Nm d (x * y) := by
  obtain ⟨N, hN, hmem⟩ := exists_subgroup_index_two F v B d hd
  refine ⟨?_, ?_⟩
  ·
    have hne : N ≠ ⊤ := by
      rintro rfl
      rw [Subgroup.index_top] at hN
      exact absurd hN (by norm_num)
    obtain ⟨c, hc⟩ : ∃ c : Bˣ, c ∉ N := by
      by_contra hall
      apply hne
      rw [eq_top_iff]
      intro c _
      by_contra hc
      exact hall ⟨c, hc⟩
    exact ⟨c, c.ne_zero, fun h => hc ((hmem c).mpr h)⟩
  · intro x y hx hy hnx hny
    have hx' : Units.mk0 x hx ∉ N := fun h => hnx ((hmem _).mp h)
    have hy' : Units.mk0 y hy ∉ N := fun h => hny ((hmem _).mp h)
    have : Units.mk0 x hx * Units.mk0 y hy ∈ N :=
      (Subgroup.mul_mem_iff_of_index_two hN).mpr (iff_of_false hx' hy')
    exact (hmem _).mp this

end GlobalTheory.QuadraticValuationIndexTwo
end

