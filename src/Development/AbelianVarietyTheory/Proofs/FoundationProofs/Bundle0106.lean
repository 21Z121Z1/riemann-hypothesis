import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0085
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedIntertwinerCompOfAdjacentLattices
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem idx_congr_of_inf_eq {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    {A B C : Submodule R X} (h : A ⊓ C = B ⊓ C) : idx A C = idx B C := by
  unfold idx
  rw [← AddSubgroup.inf_relIndex_right A.toAddSubgroup, ← AddSubgroup.inf_relIndex_right B.toAddSubgroup]
  have : A.toAddSubgroup ⊓ C.toAddSubgroup = B.toAddSubgroup ⊓ C.toAddSubgroup := by
    ext x
    have := SetLike.ext_iff.1 h x
    simpa using this
  rw [this]

theorem normOp_comp_of_adj : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hl A B C hA hB hC hadj hAC v hv
  obtain ⟨x, hx, P, hP, hfin, hann, hle⟩ := id hadj
  obtain ⟨hAB, hBA, -, hsB, hsA⟩ := GlobalTheory.T.adjacent_selfDual_lattices_index_simple h A B hA hB x hx P hP hfin hann hle
  have hn : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB0 : idx A B ≠ 0 := hAB ▸ hn
  have hBA0 : idx B A ≠ 0 := hBA ▸ hn
  have hBC0 : idx B C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hBA0 hAC
  have hsq : lam (idx A B) ^ 2 = (idx A B : ℂ) := by
    rw [hAB]; exact (hl.2 P hP hfin).1
  have lAB := hl.1 _ hAB0
  have lBC := hl.1 _ hBC0
  have lAC := hl.1 _ hAC
  have homBC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h B C hC).2.1 hBC0).2.2
  have homAC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A C hC).2.1 hAC).2.2
  have fixB := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A B hB).2.1 hAB0).2.1 v hv
  unfold normOp
  rw [homBC, smul_smul]
  by_cases h1 : B ⊓ C ≤ A
  · by_cases h2 : A ⊓ C ≤ B
    · have he : A ⊓ C = B ⊓ C :=
        le_antisymm (le_inf h2 inf_le_right) (le_inf h1 inf_le_right)
      rw [GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq h lam hl A B C hA hB hC hadj hAC he v hv, smul_smul, ← idx_congr_of_inf_eq he]
      congr 1
      field_simp
    · have hT : A ⊓ B ⊔ A ⊓ C = A := by
        rcases hsA (A ⊓ B ⊔ A ⊓ C) le_sup_left (sup_le inf_le_left inf_le_left) with h3 | h3
        · exact absurd (le_sup_right.trans h3) h2
        · exact h3
      obtain ⟨hi, hs⟩ := GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h B A C hB hA hC hBA0 hAC hT.ge
      rw [← hs _ fixB, (GlobalTheory.T.heisenberg_intertwining_sums_comp_eq_index h A B hA hB hAB0).2 v hv, homAC, smul_smul, hi,
        hBA.trans hAB.symm, map_mul, ← hsq]
      congr 1
      field_simp
  · have hT : A ⊓ B ⊔ B ⊓ C = B := by
      rcases hsB (A ⊓ B ⊔ B ⊓ C) le_sup_left (sup_le inf_le_right inf_le_left) with h3 | h3
      · exact absurd (le_sup_right.trans h3) h1
      · exact h3
    obtain ⟨hi, hs⟩ := GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h A B C hA hB hC hAB0 hBC0 (by rw [inf_comm B A]; exact hT.ge)
    rw [hs v hv, hi, map_mul]
    congr 1
    field_simp

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NqSubGalSmall
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

noncomputable section

namespace GlobalTheory.KZ.ES

open GlobalTheory.KroneckerCongruence in

theorem nq_sub_gal_small : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (M q : ℕ), 0 < M → q.Prime → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), FrobV V q s →
    ∀ a : X.K, Lev X M a → IntC X V a → SmallC X V (Nq X M q a - X.gal s a) := by
  intro Ω _ _ _ ε X M q hM hq V s hFr f hf hfV
  obtain ⟨hqV, hs⟩ := hFr
  have hε : Function.Injective ε := ε.injective
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set ρ := IsLocalRing.residue V with hρ_def
  have hρ0 : ∀ x : V, ρ x = 0 ↔ V.valuation (x : Ω) < 1 := fun x => by
    rw [hρ_def, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  haveI : CharP (IsLocalRing.ResidueField V) q := (CharP.charP_iff_prime_eq_zero hq).2 (by
    have : ρ (q : V) = 0 := (hρ0 _).2 (by simpa [ValuationSubring.mem_nonunits_iff] using hqV)
    simpa using this)
  have hfrob : ∀ x : V, ρ ⟨s x, (hs x x.2).1⟩ = ρ x ^ q := by
    intro x
    rw [← sub_eq_zero, ← map_pow, ← map_sub, hρ0]
    simpa using (hs x x.2).2.2
  set c := X.exp f with hc
  have hdet : ∀ j : ℕ, 0 < (!![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    intro j; simp [Matrix.det_fin_two]; exact_mod_cast hq.pos
  have hFj : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t =
      eOm ε (t * j * M) * c.coeff (t * q) := by
    intro j t
    have h := X.exp_upper (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) (by rw [ent_toGQ _ (hdet j)]; simp) f (t * q)
    rw [ent_toGQ _ (hdet j), ent_toGQ _ (hdet j), ent_toGQ _ (hdet j)] at h
    simp at h
    convert h using 2 <;> first | field_simp | (congr 1; field_simp)
  have hw : ∀ (j : ℕ) (t : ℚ), c.coeff (t * q) ≠ 0 → ∃ h : eOm ε (t * j * M) ∈ V, ρ ⟨_, h⟩ = 1 := by
    intro j t ht
    have h1 : eOm ε (t * j * M) ^ q = 1 := by
      rw [← eOm_mul_nat hε, show (q : ℚ) * (t * j * M) = j * (t * q * M) by ring, eOm_mul_nat hε,
        eOm_level X M f hf _ ht, one_pow]
    have hmem : eOm ε (t * j * M) ∈ V := mem_of_pow_eq_one V hq.ne_zero h1
    refine ⟨hmem, ?_⟩
    have h2 : (⟨_, hmem⟩ : V) ^ q = 1 := Subtype.ext (by simpa using h1)
    have h3 : (ρ ⟨_, hmem⟩ - 1) ^ q = 0 := by rw [sub_pow_char, ← map_pow, h2, map_one, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff hq.ne_zero |>.1 h3)
  have memF : ∀ (j : ℕ) (t : ℚ), (X.exp (X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f)).coeff t ∈ V := by
    intro j t
    rw [hFj]
    by_cases h0 : c.coeff (t * q) = 0
    · rw [h0, mul_zero]; exact zero_mem V
    · exact mul_mem (hw j t h0).1 (hfV _)
  have redF : ∀ (j : ℕ) (t : ℚ), ρ ⟨_, memF j t⟩ = ρ ⟨_, hfV (t * q)⟩ := by
    intro j t
    by_cases h0 : c.coeff (t * q) = 0
    · exact congrArg ρ (Subtype.ext (by simp only; rw [hFj, h0, mul_zero]))
    · obtain ⟨hm, h1⟩ := hw j t h0
      have e : (⟨_, memF j t⟩ : V) = ⟨_, hm⟩ * ⟨_, hfV (t * q)⟩ :=
        Subtype.ext (by simp only [MulMemClass.mk_mul_mk]; rw [hFj])
      rw [e, map_mul, h1, one_mul]
  have memC : ∀ t : ℚ, (X.exp (X.gal s f)).coeff t ∈ V := by
    intro t; rw [X.gal_exp]; exact (hs _ (hfV t)).1
  set LF : ℕ → HahnSeries ℚ V := fun j => liftV V _ (memF j) with hLF
  set LC := liftV V _ memC with hLC
  have h1 : ∀ j, hahnSeriesCoeffRingHomMap ρ (LF j) = hahnSeriesCoeffRingHomMap ρ (LF 0) := by
    intro j; ext t; rw [hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]; exact (redF j t).trans (redF 0 t).symm
  have h2 : hahnSeriesCoeffRingHomMap ρ (LF 0) ^ q = hahnSeriesCoeffRingHomMap ρ LC := by
    ext t
    rw [coeff_pow_char q, hahnSeriesCoeffRingHomMap_coeff, hahnSeriesCoeffRingHomMap_coeff]
    show ρ ⟨_, memF 0 (t / q)⟩ ^ q = ρ ⟨_, memC t⟩
    rw [redF 0 (t / q), ← hfrob]
    exact congrArg ρ (Subtype.ext (by simp only; rw [X.gal_exp, div_mul_cancel₀ t hq0]))
  have hexp : X.exp ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, ((j : ℤ) * M : ℤ); 0, (q : ℤ)]) f) - X.gal s f) =
      hahnSeriesCoeffRingHomMap V.subtype ((∏ j ∈ Finset.range q, LF j) - LC) := by
    simp only [map_sub, map_prod, hLF, hLC, map_liftV]
  have hW : hahnSeriesCoeffRingHomMap ρ ((∏ j ∈ Finset.range q, LF j) - LC) = 0 := by
    rw [map_sub, map_prod, Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const, Finset.card_range, h2, sub_self]
  intro r
  unfold Nq
  rw [hexp, hahnSeriesCoeffRingHomMap_coeff, ValuationSubring.mem_nonunits_iff]
  refine (hρ0 (((∏ j ∈ Finset.range q, LF j) - LC).coeff r)).1 ?_
  rw [← hahnSeriesCoeffRingHomMap_coeff, hW]
  rfl

end GlobalTheory.KZ.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneSubPrimeDivZetaSubOneMulIsUnit
section
open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.K5

theorem one_sub_p_div_zeta_mul_isUnit : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (j : ℕ), 1 ≤ j → ∀ y : Ω, IsInt p y →
  1 - (p : Ω) / (T.ζ j - 1) * y ≠ 0 ∧ IsInt p (1 - (p : Ω) / (T.ζ j - 1) * y)⁻¹ := by
  intro p hp hp2 Ω _ _ _ T j hj y hy
  classical
  set A := integralClosure (O0 p) Ω
  have hpj : 1 < p ^ j := Nat.one_lt_pow (by omega) hp.out.one_lt
  have hζ1 : T.ζ j ≠ 1 := (T.prim j).ne_one hpj
  have hτ0 : T.ζ j - 1 ≠ 0 := sub_ne_zero.2 hζ1
  have hζint : IsIntegral (O0 p) (T.ζ j) := by
    refine IsIntegral.of_pow (n := p ^ j) (by omega) ?_
    rw [(T.prim j).pow_eq_one]; exact isIntegral_one
  have htot : 2 ≤ Nat.totient (p ^ j) := by
    rw [Nat.totient_prime_pow hp.out (by omega)]
    have : 3 ≤ p := by have := hp.out.two_le; omega
    have h1 : 1 ≤ p ^ (j - 1) := Nat.one_le_pow _ _ hp.out.pos
    calc 2 = 1 * 2 := by ring
      _ ≤ p ^ (j - 1) * (p - 1) := Nat.mul_le_mul h1 (by omega)
  have hw : IsIntegral (O0 p) ((p : Ω) / (T.ζ j - 1) ^ 2 * y) :=
    (GlobalTheory.T.isInt_prime_div_rootOfUnity_sub_one_pow p Ω T j 2 hj htot).mul hy
  let ζ' : A := ⟨T.ζ j, hζint⟩
  let τ : A := ζ' - 1
  let w : A := ⟨_, hw⟩
  let u : A := 1 - τ * w
  have hu : (u : Ω) = 1 - (p : Ω) / (T.ζ j - 1) * y := by
    simp only [u, τ, w, ζ', Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_one]
    field_simp
  obtain ⟨hdom, hdvr, hirr⟩ := completed_laurent_isDVR p
  have hmax : IsLocalRing.maximalIdeal (O0 p) = Ideal.span {(p : O0 p)} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr

  have hτM : ∀ M : Ideal A, M.IsMaximal → τ ∈ M := by
    intro M hM
    have hc : (M.comap (algebraMap (O0 p) A)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have hpM : (p : A) ∈ M := by
      have h1 : M.comap (algebraMap (O0 p) A) = IsLocalRing.maximalIdeal (O0 p) :=
        IsLocalRing.eq_maximalIdeal hc
      have h2 : (p : O0 p) ∈ M.comap (algebraMap (O0 p) A) := by
        rw [h1, hmax]; exact Ideal.mem_span_singleton_self _
      simpa using h2
    haveI : M.IsPrime := hM.isPrime
    haveI : Nontrivial (A ⧸ M) := Ideal.Quotient.nontrivial_iff.2 hM.ne_top
    haveI : CharP (A ⧸ M) p := by
      rw [CharP.charP_iff_prime_eq_zero hp.out]
      rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]; exact hpM
    have hζp : ζ' ^ (p ^ j) = 1 := Subtype.ext (by simp [ζ', (T.prim j).pow_eq_one])
    have h3 : (Ideal.Quotient.mk M τ) ^ (p ^ j) = 0 := by
      simp only [τ, map_sub, map_one]
      rw [sub_pow_char_pow, ← map_pow, hζp, map_one, one_pow, sub_self]
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact pow_eq_zero_iff (by omega) |>.1 h3
  have hunit : IsUnit u := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {u})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have h1 : u ∈ M := hle (Ideal.mem_span_singleton_self _)
    have h2 : τ * w ∈ M := M.mul_mem_right _ (hτM M hM)
    have : (1 : A) ∈ M := by
      have := M.add_mem h1 h2; simpa [u] using this
    exact hM.ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨v, hv⟩ := hunit
  have hval : (u : Ω) * (((v⁻¹ : Aˣ) : A) : Ω) = 1 := by
    rw [← hv, ← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
  rw [← hu]
  refine ⟨left_ne_zero_of_mul_eq_one hval, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right hval]
  exact ((v⁻¹ : Aˣ) : A).2

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PAdicCompletionLaurentEqSumPthPowersModPStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicCompletionLaurent_eq_sum_pthPowers_mod_p : ∀ (p : ℕ) [Fact p.Prime] (x : O0 p), ∃ (g : Fin p → O0 p) (h : O0 p), x = ∑ j : Fin p, qO p ^ (j : ℕ) * g j ^ p + (p : O0 p) * h := by
  first | exact @GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul | exact GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul | (intros; apply GlobalTheory.K5.exists_eq_sum_qO_pow_mul_pow_add_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeriodMapEquivariant
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.HeckeEqv

theorem toGL_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    toGL (A * B) = toGL A * toGL B := by
  have hAB : (A * B).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero hA hB
  ext i j
  simp [toGL, hA, hB, hAB, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply, Fin.sum_univ_two]

theorem toGL_mat (γ : SL(2, ℤ)) : toGL (mat γ) = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  have h : (mat γ).det ≠ 0 := by simp [mat]
  ext i j
  simp [toGL, h, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.SpecialLinearGroup.mapGL]

theorem toGL_smul_mat (γ : SL(2, ℤ)) (τ : ℍ) : toGL (mat γ) • τ = γ • τ := by
  rw [toGL_mat]; rfl

theorem mem_of_natDegree_le {w : ℕ} {p : ℂ[X]} (h : p.natDegree ≤ w) : p ∈ degreeLT ℂ (w + 1) := by
  rw [mem_degreeLT]
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le h)

theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  refine Submodule.sum_mem _ fun j hj => mem_of_natDegree_le ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))

theorem polySlash_mem (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : slP w g p ∈ degreeLT ℂ (w + 1) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]
  refine Submodule.sum_mem _ fun i hi => ?_
  refine Submodule.smul_mem _ _ (mem_of_natDegree_le ?_)
  have hi' : i ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  refine natDegree_mul_le.trans ?_
  have h1 := (natDegree_pow_le (p := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) (n := i)).trans
    (Nat.mul_le_mul_left i (natDegree_linear_le))
  have h2 := (natDegree_pow_le (p := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) (n := w - i)).trans
    (Nat.mul_le_mul_left (w - i) (natDegree_linear_le))
  omega

theorem hecke_eqv (Γ : Subgroup SL(2, ℤ)) (k : ℕ) (hk2 : 2 ≤ k) (f : ModularForm Γ (k : ℤ))
    {ι : Type} [Fintype ι] (δ : ι → Matrix (Fin 2) (Fin 2) ℤ) (hδ : ∀ i, 0 < (δ i).det)
    (hπ : ∀ γ : Γ, ∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i)) :
    per Γ (k - 2) (hkF (k : ℤ) δ ⇑f) - hk Γ (k - 2) δ (per Γ (k - 2) ⇑f) ∈ B1 Γ (k - 2) := by
  have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ⇑f := f.holo'
  have hdet : ∀ i, (δ i).det ≠ 0 := fun i => (hδ i).ne'
  have hpc := (GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk2 f).2
  set w := k - 2 with hw
  set F := eichler w ⇑f with hF
  set c : ι → ℂ[X] := fun i => slP w (δ i) (F (toGL (δ i) • UpperHalfPlane.I)) with hc
  set C := ∑ i, c i with hCdef
  have hC : -C ∈ degreeLT ℂ (w + 1) :=
    Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => polySlash_mem _ _ _)
  refine ⟨⟨-C, hC⟩, ?_⟩
  funext γ
  have hγdet : (mat (γ : SL(2, ℤ))).det ≠ 0 := by simp [mat]
  obtain ⟨hex⟩ : Nonempty (∃ π : Equiv.Perm ι, ∀ i, ∃ γ' : Γ, δ i * mat γ = mat γ' * δ (π i)) := ⟨hπ γ⟩
  have e2 : hk Γ w δ (per Γ w ⇑f) γ =
      ∑ i, slP w (δ (hex.choose i)) (per Γ w ⇑f (hex.choose_spec i).choose) := by
    simp only [hk, LinearMap.pi_apply, dif_pos hex, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply]
  have e1 : per Γ w (hkF (k : ℤ) δ ⇑f) γ =
      ∑ i, (slP w (δ i * mat γ) (F (toGL (δ i * mat γ) • UpperHalfPlane.I)) - slP w (mat γ) (c i)) := by
    simp only [per, hkF]
    rw [GlobalTheory.T.eichlerIntegralFromI_finset_sum w _ (fun i => hfd.slash _ _), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := GlobalTheory.T.eichlerIntegral_changeOfVariables_intMatrix_slash k hk2 ⇑f hfd (δ i) (hδ i) ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
    rw [eq_sub_of_add_eq h.symm, map_sub, GlobalTheory.T.polyDegreeSlashAction_matrix_mul w (δ i) (mat γ) _ (eichler_mem _ _ _),
      toGL_mul _ _ (hdet i) hγdet, mul_smul, toGL_smul_mat]
  have e3 : ∀ i, slP w (δ i * mat γ) (F (toGL (δ i * mat γ) • UpperHalfPlane.I)) =
      slP w (δ (hex.choose i)) (per Γ w ⇑f (hex.choose_spec i).choose) + c (hex.choose i) := by
    intro i
    set γ' := (hex.choose_spec i).choose
    have hγ' : δ i * mat γ = mat γ' * δ (hex.choose i) := (hex.choose_spec i).choose_spec
    have hγ'det : (mat (γ' : SL(2, ℤ))).det ≠ 0 := by simp [mat]
    rw [hγ', toGL_mul _ _ hγ'det (hdet _), mul_smul, toGL_smul_mat,
      GlobalTheory.T.polyDegreeSlashAction_matrix_mul w (mat γ') (δ (hex.choose i)) _ (eichler_mem _ _ _),
      hpc γ' (toGL (δ (hex.choose i)) • UpperHalfPlane.I), map_sub]
    simp only [hc]
    abel
  have hsum : ∑ i, c (hex.choose i) = C := Equiv.sum_comp hex.choose c
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.pi_apply, LinearMap.sub_apply,
    LinearMap.id_apply, Pi.sub_apply]
  rw [e1, e2]
  simp only [e3, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, ← map_sum, map_neg]
  abel

theorem tqFam_det (q : ℕ) (hq : q.Prime) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : 0 < (tqFam q σ i).det := by
  have hq0 : (0 : ℤ) < q := by exact_mod_cast hq.pos
  unfold tqFam
  split_ifs
  · simpa [Matrix.det_fin_two_of] using hq0
  · simpa [Matrix.det_mul, mat, dg, Matrix.det_fin_two_of] using hq0

theorem ulFam_det (l : ℕ) (hl : l.Prime) (i : Fin l) : 0 < (ulFam l i).det := by
  have hl0 : (0 : ℤ) < l := by exact_mod_cast hl.pos
  simpa [ulFam, Matrix.det_fin_two_of] using hl0

theorem period_map_equivariant : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ f : ModularForm (Lev N l) (k : ℤ),
  (∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
    per (Lev N l) (k - 2) (TqF (k : ℤ) q σ ⇑f) - TqZ (Lev N l) (k - 2) q σ (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) ∧
  per (Lev N l) (k - 2) (UlF (k : ℤ) l ⇑f) - UlZ (Lev N l) (k - 2) l (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2) ∧
  (∀ (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
    per (Lev N l) (k - 2) (DdF (k : ℤ) σ ⇑f) - DdZ (Lev N l) (k - 2) σ (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) := by
  intro N l k hN hl hlN hk f
  refine ⟨fun q σ hq hqN hσ => ?_, ?_, fun d σ hσ => ?_⟩
  · exact hecke_eqv _ k (by omega) f (tqFam q σ) (tqFam_det q hq σ)
      (GlobalTheory.T.heckeTqRepresentatives_right_mul_permutes_cosets N l q hN hl hlN hq hqN σ hσ)
  · exact hecke_eqv _ k (by omega) f (ulFam l) (ulFam_det l hl) (GlobalTheory.T.heckeUlRepresentatives_right_mul_perm N l hN hl hlN)
  · exact hecke_eqv _ k (by omega) f (fun _ : Unit => mat σ) (fun _ => by simp [mat])
      (fun γ => ⟨Equiv.refl _, fun _ => GlobalTheory.T.diamondMatrix_normalizes_gammaOneGammaZeroLevel N l d σ hσ γ⟩)

end GlobalTheory.HeckeFamilyMatrices.HeckeEqv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PermutedModularFamilyMonicPolyCoeffInvariant
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Polynomial

namespace GlobalTheory.QFam

theorem vieta_root {ι : Type} [Fintype ι] (y : ι → ℂ) (i : ι) :
    y i ^ Fintype.card ι + ∑ j : Fin (Fintype.card ι),
      ((-1) ^ (Fintype.card ι - (j : ℕ)) *
        ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, y l) *
        y i ^ (j : ℕ) = 0 := by
  classical
  set n := Fintype.card ι with hn
  set P : ℂ[X] := ∏ l, (X + C (-y l)) with hP
  have hmon : P.Monic := monic_prod_of_monic _ _ fun l _ => monic_X_add_C _
  have hdeg : P.natDegree = n := by
    rw [hP, natDegree_prod_of_monic _ _ fun l _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hn]
  have hroot : P.eval (y i) = 0 := by
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hcoeff : ∀ j ≤ n, P.coeff j =
      (-1) ^ (n - j) * ∑ t ∈ Finset.powersetCard (n - j) Finset.univ, ∏ l ∈ t, y l := by
    intro j hj
    rw [hP, Finset.prod_X_add_C_coeff _ _ (by simpa [hn] using hj), Finset.card_univ, ← hn,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_neg, (Finset.mem_powersetCard.mp ht).2]
  have h1 : P.coeff n = 1 := hdeg ▸ hmon.coeff_natDegree
  rw [eval_eq_sum_range, hdeg, Finset.sum_range_succ, h1, one_mul] at hroot
  rw [← hroot, add_comm]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun m => P.coeff m * y i ^ m)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoeff j j.2.le]

end GlobalTheory.QFam

theorem GlobalTheory.QFam.minpoly_coeff_invariant : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (k N : ℕ) (F : ι → ℍ → ℂ) (R : Subring ℂ), 0 < N → ActBij act → IsFam act k F → (∀ i, QAll (· ∈ R) N (F i)) → ∃ s : Fin (Fintype.card ι) → ℍ → ℂ, (∀ j : Fin (Fintype.card ι), (∀ γ : SL(2, ℤ), s j ∣[((k * (Fintype.card ι - j) : ℕ) : ℤ)] γ = s j) ∧ QAll (· ∈ R) N (s j)) ∧ ∀ i τ, F i τ ^ Fintype.card ι + ∑ j, s j τ * F i τ ^ (j : ℕ) = 0 := by
  intro ι _ act k N F R _ hb hF hQ
  refine ⟨fun j τ => (-1) ^ (Fintype.card ι - (j : ℕ)) *
      ∑ t ∈ Finset.powersetCard (Fintype.card ι - (j : ℕ)) Finset.univ, ∏ l ∈ t, F l τ,
    fun j => ⟨fun γ => ?_, ?_⟩, fun i τ => vieta_root (fun l => F l τ) i⟩
  · have hE := IsFam.esymm_slash hb hF γ (Fintype.card ι - (j : ℕ))
    have hw : (((k * (Fintype.card ι - (j : ℕ)) : ℕ) : ℤ)) =
        (((Fintype.card ι - (j : ℕ) : ℕ) : ℤ) * (k : ℤ)) := by
      rw [Nat.cast_mul, mul_comm]
    funext τ
    have hEτ := congrFun hE τ
    rw [ModularForm.SL_slash_apply] at hEτ
    rw [hw, ModularForm.SL_slash_apply, mul_assoc, hEτ]
  · exact QAllSubring.mul (QAllSubring.const (R.pow_mem (R.neg_mem R.one_mem) _))
      (QAllSubring.sum _ fun t _ => QAllSubring.prod _ fun l _ => hQ l)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolynomialRelationPassesToQExpansions
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

theorem HasQ.mul_powerSeries {N : ℕ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}
    (hf : HasQ N f (fun n => PowerSeries.coeff n φ)) (hg : HasQ N g (fun n => PowerSeries.coeff n ψ)) :
    HasQ N (fun τ => f τ * g τ) (fun n => PowerSeries.coeff n (φ * ψ)) := by
  have h := hf.mul_conv hg
  have e : conv (fun n => PowerSeries.coeff n φ) (fun n => PowerSeries.coeff n ψ) =
      fun n => PowerSeries.coeff n (φ * ψ) := by
    funext n; rw [conv, PowerSeries.coeff_mul]
  rwa [e] at h

theorem HasQ.pow_powerSeries {N : ℕ} {f : ℍ → ℂ} {b : ℕ → ℂ} (hf : HasQ N f b) (i : ℕ) :
    HasQ N (fun τ => f τ ^ i) (fun n => PowerSeries.coeff n (PowerSeries.mk b ^ i)) := by
  induction i with
  | zero =>
    have h := HasQ.const N (1 : ℂ)
    convert h using 2 <;> simp [PowerSeries.coeff_one]
  | succ i ih =>
    have hb : HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk b)) := by
      simpa only [PowerSeries.coeff_mk] using hf
    have h := ih.mul_powerSeries hb
    simpa only [pow_succ] using h

theorem polyRel_qSeries : ∀ (N n : ℕ) (f : ℍ → ℂ) (b : ℕ → ℂ) (p : ℕ → ℍ → ℂ) (c : ℕ → ℕ → ℂ), 0 < N → HasQ N f b → (∀ i, HasQ N (p i) (c i)) → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i = 0) → (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i))).eval (PowerSeries.mk b) = 0 := by
  intro N n f b p c hN hf hp hrel
  have hterm : ∀ i ∈ Finset.range (n + 1), HasQ N (fun τ => p i τ * f τ ^ i)
      (fun m => PowerSeries.coeff m (PowerSeries.mk (c i) * PowerSeries.mk b ^ i)) := by
    intro i _
    have hpi : HasQ N (p i) (fun m => PowerSeries.coeff m (PowerSeries.mk (c i))) := by
      simpa only [PowerSeries.coeff_mk] using hp i
    exact hpi.mul_powerSeries (hf.pow_powerSeries i)
  have hsum := HasQ.sum (Finset.range (n + 1)) hterm
  have hzero : HasQ N (fun τ => ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i) (fun _ => 0) := by
    have h0 := HasQ.const N (0 : ℂ)
    have e : (fun τ => ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i) = fun _ => (0 : ℂ) :=
      funext hrel
    rw [e]
    simpa using h0
  have hc := HasQ.coeff_unique hN hsum hzero
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_monomial]
  ext m
  have := congrFun hc m
  simpa [map_sum] using this

end GlobalTheory.QFam
end

