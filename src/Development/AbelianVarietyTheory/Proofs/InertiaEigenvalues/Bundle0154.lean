import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0146
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0142
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0102
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0108
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0097
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.GaloisCohomology.Statement

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField

variable {l : ℕ} [Fact l.Prime]

theorem aeval_ne_zero_of_norm_eq (K : FinExt l) (N : ℕ) (π : Om l)
    (hπ : ‖π‖ = (l : ℝ) ^ (-(1 : ℝ) / (N : ℝ))) (p : (↥(K0 K))[X]) (hp : p ≠ 0)
    (hd : p.natDegree < N) : aeval π p ≠ 0 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le _).trans_lt hd
  have hπ0 : π ≠ 0 := by
    rw [← norm_pos_iff, hπ]; positivity
  have key : ∀ i ∈ p.support, ∃ n : ℤ,
      ‖p.coeff i • π ^ i‖ = (l : ℝ) ^ ((n : ℝ) - (i : ℝ) / N) := by
    intro i hi
    have h0 : ((p.coeff i : ↥(K0 K)) : Om l) ≠ 0 := by
      have := mem_support_iff.1 hi
      exact fun h => this (Subtype.ext h)
    obtain ⟨n, hn⟩ := GlobalTheory.T.norm_eq_zpow_of_mem_maxUnramifiedSubfield l K _ (p.coeff i).2 h0
    refine ⟨n, ?_⟩
    change ‖((p.coeff i : ↥(K0 K)) : Om l) * π ^ i‖ = _
    rw [norm_mul, norm_pow, hn, hπ, ← Real.rpow_natCast, ← Real.rpow_mul hl0.le,
      ← Real.rpow_intCast, ← Real.rpow_add hl0]
    congr 1
    ring
  have hpw : Set.Pairwise (p.support : Set ℕ)
      (fun i k => ‖p.coeff i • π ^ i‖₊ ≠ ‖p.coeff k • π ^ k‖₊) := by
    intro i hi k hk hik h
    obtain ⟨n, hn⟩ := key i hi
    obtain ⟨m, hm⟩ := key k hk
    have h' : ‖p.coeff i • π ^ i‖ = ‖p.coeff k • π ^ k‖ := congrArg NNReal.toReal h
    rw [hn, hm] at h'
    have h2 := (Real.rpow_right_inj hl0 hl1.ne').1 h'
    have h3 : ((n - m) * N : ℝ) = i - k := by
      field_simp at h2
      linarith
    have h4 : ((n - m) * N : ℤ) = i - k := by exact_mod_cast h3
    have hi' : i < N := (le_natDegree_of_mem_supp i hi).trans_lt hd
    have hk' : k < N := (le_natDegree_of_mem_supp k hk).trans_lt hd
    have h5 : (i : ℤ) - k = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd (m := N) ⟨n - m, by rw [← h4]; ring⟩
      rw [abs_lt]; constructor <;> omega
    omega
  intro h
  rw [aeval_eq_sum_range' (Nat.lt_succ_self _)] at h
  have hs : ∑ i ∈ p.support, p.coeff i • π ^ i = 0 := by
    rw [← h]
    apply Finset.sum_subset supp_subset_range_natDegree_succ
    intro i _ hi
    rw [notMem_support_iff.1 hi, zero_smul]
  have h6 := IsUltrametricDist.nnnorm_sum_eq_sup_of_pairwise_ne hpw
  rw [hs, nnnorm_zero] at h6
  have hm : p.natDegree ∈ p.support := natDegree_mem_support_of_nonzero hp
  have h7 := Finset.le_sup (f := fun i => ‖p.coeff i • π ^ i‖₊) hm
  rw [← h6] at h7
  obtain ⟨n, hn⟩ := key _ hm
  have h8 : ‖p.coeff p.natDegree • π ^ p.natDegree‖ ≤ 0 := h7
  rw [hn] at h8
  exact absurd h8 (not_le.2 (by positivity))

theorem minpoly_unramifiedSubfield_eq_cyclotomic (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) : minpoly ↥(K0 K) ζ = cyclotomic (l ^ j) ↥(K0 K) := by
  have hlp : l.Prime := Fact.out
  have hpos : 0 < l ^ j := pow_pos hlp.pos j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  have hroot : aeval ζ (cyclotomic (l ^ j) ↥(K0 K)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hpos
  have hnorm : ‖ζ - 1‖ = (l : ℝ) ^ (-(1 : ℝ) / ((Nat.totient (l ^ j) : ℕ) : ℝ)) := by
    have h1 := GlobalTheory.T.norm_primitiveRoot_primePow_sub_one_padicComplex l j hj (ζ : PadicComplex l)
      (hζ.map_of_injective (f := algebraMap (Om l) (PadicComplex l)) (RingHom.injective _))
    rw [Nat.totient_prime_pow hlp hj]
    push_cast [Nat.cast_sub hlp.one_le]
    rw [← h1, ← PadicComplex.norm_extends]
    congr 1
    exact (map_sub (algebraMap (Om l) (PadicComplex l)) ζ 1).trans (by rw [map_one]; rfl)
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic _ _)
    (minpoly.dvd _ _ hroot)
  rw [natDegree_cyclotomic]
  by_contra hlt
  push_neg at hlt
  refine aeval_ne_zero_of_norm_eq K _ (ζ - 1) hnorm (taylor 1 (minpoly ↥(K0 K) ζ)) ?_ ?_ ?_
  · intro h
    exact minpoly.ne_zero hint (taylor_injective 1 (by rw [h, map_zero]))
  · rwa [natDegree_taylor]
  · rw [taylor_apply, aeval_comp]
    simp

theorem exists_primitiveRoot_Om (j : ℕ) : ∃ ζ : Om l, IsPrimitiveRoot ζ (l ^ j) := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ j) := ⟨(pow_pos hlp.pos j).ne'⟩
  haveI : CharZero (Om l) := algebraRat.charZero _
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ j)

theorem Ks_eq_restrictScalars (K : FinExt l) (j : ℕ) (ζ : Om l)
    (hζ : IsPrimitiveRoot ζ (l ^ j)) :
    Ks K j = ((↥(K0 K))⟮ζ⟯).restrictScalars ℚ_[l] := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ j) := ⟨(pow_pos hlp.pos j).ne'⟩
  rw [IntermediateField.restrictScalars_adjoin_eq_sup, Ks]
  congr 1
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (IntermediateField.mem_adjoin_simple_self _ ζ) i
  · exact IntermediateField.adjoin.mono _ _ _ (Set.singleton_subset_iff.2 hζ.pow_eq_one)

theorem finrank_Ks (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) :
    Module.finrank ℚ_[l] ↥(Ks K j) =
      Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1)) := by
  have hlp : l.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  have hint : IsIntegral ↥(K0 K) ζ := Algebra.IsIntegral.isIntegral ζ
  rw [Ks_eq_restrictScalars K j ζ hζ]
  have h1 : Module.finrank ↥(K0 K) ↥((↥(K0 K))⟮ζ⟯) = (l - 1) * l ^ (j - 1) := by
    rw [IntermediateField.adjoin.finrank hint, minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ,
      natDegree_cyclotomic, Nat.totient_prime_pow hlp hj, mul_comm]
  rw [← h1]
  exact (Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥((↥(K0 K))⟮ζ⟯)).symm

theorem exists_chi_approx (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) (j : ℕ) (hj : 1 ≤ j) :
    ∃ g ∈ (K0 K).fixingSubgroup, ‖(χ g : ℚ_[l]) - u‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hpos : 0 < l ^ j := pow_pos hlp.pos j
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  let z : ℤ_[l] := ⟨u, hu.le⟩
  set a := z.appr j with ha
  have hza : ‖u - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    have := (PadicInt.norm_le_pow_iff_mem_span_pow _ j).2 (PadicInt.appr_spec j z)
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this
    exact this
  have hlt : (l : ℝ) ^ (-(j : ℤ)) < 1 := zpow_lt_one_of_neg₀ hl1 (by omega)
  have hna : ‖(a : ℚ_[l])‖ = 1 := by
    have h1 : (a : ℚ_[l]) = u + -(u - a) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, hu, norm_neg,
      max_eq_left (hza.trans hlt.le)]
    rw [hu, norm_neg]
    exact (hza.trans_lt hlt).ne'
  have hcop : a.Coprime (l ^ j) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hlp.coprime_iff_not_dvd]
    intro hd
    have : ‖((a : ℤ) : ℚ_[l])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 (by exact_mod_cast hd)
    rw [Int.cast_natCast, hna] at this
    exact lt_irrefl _ this
  have hζa := hζ.pow_of_coprime a hcop
  have hconj : IsConjRoot ↥(K0 K) (ζ ^ a) ζ := by
    unfold IsConjRoot
    rw [minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, minpoly_unramifiedSubfield_eq_cyclotomic K j hj _ hζa]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  refine ⟨σ.restrictScalars ℚ_[l], fun x => σ.commutes x, ?_⟩
  obtain ⟨b, hb, hb'⟩ := hχ (σ.restrictScalars ℚ_[l]) j ζ hζ.pow_eq_one
  have hab : ζ ^ a = ζ ^ b := hσ.symm.trans hb'
  have hmod : a ≡ b [MOD l ^ j] := by
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder hpos.ne').pow_eq_pow_iff_modEq.1 hab
  have hba : ‖(b : ℚ_[l]) - a‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    have := (Padic.norm_int_le_pow_iff_dvd ((b : ℤ) - a) j (p := l)).2
      (by exact_mod_cast hmod.dvd)
    simpa using this
  have h1 : (χ (σ.restrictScalars ℚ_[l]) : ℚ_[l]) - u =
      ((χ (σ.restrictScalars ℚ_[l]) : ℚ_[l]) - b) + (((b : ℚ_[l]) - a) + -(u - a)) := by ring
  rw [h1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ?_)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hba ?_)
  rwa [norm_neg]

theorem exists_chi_eq (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) : ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u := by
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hcont := (cyc_basic l χ hχ).2.1
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  have hcl : IsClosed ((K0 K).fixingSubgroup : Set (GQ l)) :=
    IntermediateField.fixingSubgroup_isClosed _
  have hc := (hcl.isCompact.image hcont).isClosed
  have hmem : u ∈ (fun g => (χ g : ℚ_[l])) '' ((K0 K).fixingSubgroup : Set (GQ l)) := by
    rw [← hc.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl1)
    obtain ⟨g, hg, hg'⟩ := exists_chi_approx K χ hχ u hu (n + 1) (by omega)
    refine ⟨_, ⟨g, hg, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm]
    refine hg'.trans_lt (lt_of_le_of_lt ?_ hn)
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hl1.le (by push_cast; omega)
  exact hmem

theorem finrank_Ks_and_chi_surjective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l),
    (∀ j : ℕ, 1 ≤ j → Module.finrank ℚ_[l] ↥(Ks K j) =
      Module.finrank ℚ_[l] ↥(K0 K) * ((l - 1) * l ^ (j - 1))) ∧
    ∀ χ : GQ l →* ℚ_[l]ˣ, IsCyc χ → ∀ u : ℚ_[l], ‖u‖ = 1 →
      ∃ g ∈ (K0 K).fixingSubgroup, (χ g : ℚ_[l]) = u :=
  fun _ _ K => ⟨finrank_Ks K, exists_chi_eq K⟩

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPolydiscWindowsSurjectiveBoundsZero
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset Matrix

theorem coefB_norm {F : Type} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] [PerfectRing F p] {h : ℕ}
    (ϖ : F) (lam π : Fin h → F) (L U : ℕ)
    (hb : ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖)) :
    (∀ m r j, ‖coefB p ϖ lam π L U m r j‖ ≤ 1) ∧ (∀ m, L < m → ∀ r j, ‖coefB p ϖ lam π L U m r j‖ < 1) := by
  have key : ∀ m r j, ‖coefB p ϖ lam π L U m r j‖ ≤ 1 ∧ (L < m → ‖coefB p ϖ lam π L U m r j‖ < 1) := by
    intro m r j
    simp only [coefB, Matrix.of_apply]
    split_ifs with hm
    · rw [norm_pow, norm_div]
      obtain ⟨h1, h2⟩ := hb r j ((m : ℤ) - L)
      have hpos : p ^ (h - (r : ℕ)) ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
      rcases eq_or_lt_of_le (norm_nonneg (lam r * π r ^ p ^ (r : ℕ))) with hc | hc
      · rw [← hc, div_zero, zero_pow hpos]
        exact ⟨zero_le_one, fun _ => zero_lt_one⟩
      · refine ⟨pow_le_one₀ (div_nonneg (norm_nonneg _) hc.le) ((div_le_one hc).2 h1), fun hLm => ?_⟩
        exact pow_lt_one₀ (div_nonneg (norm_nonneg _) hc.le) ((div_lt_one hc).2 (h2 (by omega))) hpos
    · simp
  exact ⟨fun m r j => (key m r j).1, fun m hm r j => (key m r j).2 hm⟩

theorem gsum_mul_left {F : Type} [NormedField F] {m : Type} [Fintype m] (q D : ℕ) (A : Matrix m m F)
    (B : ℕ → Matrix m m F) (z : m → F) :
    gsum q D (fun n => A * B n) z = A *ᵥ gsum q D B z := by
  simp only [gsum, Matrix.mulVec_sum, Matrix.mulVec_mulVec]

theorem normalize {F : Type} [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] [CharP F p]
    [PerfectRing F p] {h : ℕ} (ϖ : F) (hϖ : ϖ ≠ 0) (lam π : Fin h → F) (hlam : ∀ j, lam j ≠ 0)
    (hπ : ∀ j, π j ≠ 0) (hanti : Antitone (fun j => ‖lam j‖)) (horth : Orth p lam) (L U : ℕ) (hL : 1 ≤ L)
    (hb : ∀ (r j : Fin h) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖)) :
    ∃ M : ℕ → Matrix (Fin h) (Fin h) F, Normal L M ∧ (M 0).det ≠ 0 ∧
      ∃ Φ : (Fin h → F) → (Fin h → F), (∀ b, (∀ r, ‖b r‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖) → Integral (Φ b)) ∧
        Φ 0 = 0 ∧ ∀ z b, gsum (p ^ h) (L + U) M z = Φ b ↔ ∀ r, rowS p ϖ lam L U (winPt p π L z) r = b r := by
  set B := coefB p ϖ lam π L U with hBdef
  obtain ⟨hB1, hB2⟩ := coefB_norm p ϖ lam π L U hb
  obtain ⟨hdet, hdet0⟩ := GlobalTheory.T.normalizedRowCoefficientMatrices_det_norm F p h ϖ hϖ lam π hlam hπ hanti horth L U
  obtain ⟨hN, hinv⟩ := GlobalTheory.T.normal_inv_mul_and_norm_inv_le_one F (Fin h) L B hB1 hB2 hdet
  have hdne : (B L).det ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hdet
    exact zero_ne_one hdet
  have hdu : IsUnit (B L).det := isUnit_iff_ne_zero.2 hdne
  have hc : ∀ r, lam r * π r ^ p ^ (r : ℕ) ≠ 0 := fun r => mul_ne_zero (hlam r) (pow_ne_zero _ (hπ r))
  let nb : (Fin h → F) → (Fin h → F) := fun b r => (b r / (lam r * π r ^ p ^ (r : ℕ))) ^ p ^ (h - (r : ℕ))
  refine ⟨fun n => (B L)⁻¹ * B n, hN, ?_, fun b => (B L)⁻¹ *ᵥ nb b, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det (B L) hdu).ne_zero hdet0
  · intro b hbb i
    simp only [Matrix.mulVec, dotProduct]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro j _
    rw [norm_mul]
    have h1 : ‖nb b j‖ ≤ 1 := by
      simp only [nb]
      rw [norm_pow, norm_div]
      exact pow_le_one₀ (div_nonneg (norm_nonneg _) (norm_nonneg _))
        ((div_le_one (norm_pos_iff.2 (hc j))).2 (hbb j))
    exact mul_le_one₀ (hinv i j) (norm_nonneg _) h1
  · have : nb 0 = 0 := by
      funext r
      simp only [nb, Pi.zero_apply, zero_div]
      exact zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    simp only [this, Matrix.mulVec_zero]
  · intro z b
    rw [gsum_mul_left]
    constructor
    · intro H r
      have H2 : gsum (p ^ h) (L + U) B z = nb b := by
        have := congrArg (fun v => B L *ᵥ v) H
        simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdu, Matrix.one_mulVec] using this
      have H3 := congrFun H2 r
      rw [← GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum F p h ϖ lam π L U hL z r] at H3
      have H4 := (iterateFrobenius_inj F p (h - (r : ℕ))).eq_iff.1 (by simpa [iterateFrobenius_def] using H3)
      exact (div_left_inj' (hc r)).1 H4
    · intro H
      have H2 : gsum (p ^ h) (L + U) B z = nb b := by
        funext r
        rw [← GlobalTheory.T.windowSummedRow_pow_eq_additiveSystemPowerSum F p h ϖ lam π L U hL z r, H r]
      rw [H2]

theorem winThm : WinThm := by
  intro F _ _ _ _ p _ _ _ h ϖ hh hϖ lam hlam hanti horth hlt
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  obtain ⟨π, hπ, hrel1, hrel2⟩ := exists_window_radii F p k ϖ hϖ lam hlam hanti hlt
  have hp := (Fact.out : p.Prime)
  have hϖ0 : ϖ ≠ 0 := by
    have : (0 : ℝ) < ‖ϖ‖ := by
      rw [hϖ]
      exact inv_pos.2 (by exact_mod_cast hp.pos)
    exact norm_pos_iff.1 this
  have hbd := GlobalTheory.T.frobeniusWindowSeriesTerm_norm_le_rowBound F p k ϖ hϖ lam π hlam hanti hlt hπ hrel1 hrel2
  have hb : ∀ (r j : Fin (k + 1)) (n : ℤ), ‖term p ϖ lam π r j n‖ ≤ ‖lam r * π r ^ p ^ (r : ℕ)‖ ∧
      (0 < n → ‖term p ϖ lam π r j n‖ < ‖lam r * π r ^ p ^ (r : ℕ)‖) :=
    fun r j n => ⟨(hbd r j n).1, (hbd r j n).2.1⟩
  have hπ0 : ∀ j, π j ≠ 0 := fun j => (hπ j).1
  have hGL := GlobalTheory.T.additiveSystem_generalLemma_all_orders
  refine ⟨fun j => ‖π j‖, fun r => ‖lam r * π r ^ p ^ (r : ℕ)‖, 2,
    fun j => ⟨norm_pos_iff.2 (hπ j).1, (hπ j).2⟩,
    fun r => norm_pos_iff.2 (mul_ne_zero (hlam r) (pow_ne_zero _ (hπ r).1)), ?_, ?_, ?_⟩
  · intro x hx r j n
    have hm := GlobalTheory.T.norm_frobeniusWindowSeriesTerm_mono F p (k + 1) ϖ lam π x hx r j n
    exact ⟨hm.trans (hbd r j n).1, fun hn => hm.trans ((hbd r j n).2.2 (by exact_mod_cast hn))⟩
  · intro b hbnd
    obtain ⟨M, hM, _, Φ, hΦ, _, hiff⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth 2 2 (by norm_num) hb
    obtain ⟨z, hz, hzb⟩ := (hGL 2).1 F p (Fin (k + 1)) (k + 1) (2 + 2) (by omega) (by omega) M hM (Φ b)
      (hΦ b hbnd)
    refine ⟨winPt p π 2 z, ?_, fun r => ?_⟩
    · intro j
      simp only [winPt]
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hz j))
    · rw [rowT_eq_rowS]
      exact (hiff z b).1 hzb r
  · obtain ⟨M, hM, hM0, Φ, _, hΦ0, hiff⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth 2 2 (by norm_num) hb
    obtain ⟨M', hM', hM0', Φ', _, hΦ0', hiff'⟩ :=
      normalize p ϖ hϖ0 lam π hlam hπ0 hanti horth (2 - 1) (2 + 1) (by norm_num) hb
    have c1 := (hGL 2).2 F p (Fin (k + 1)) (k + 1) (2 + 2) (by omega) (by omega) M hM hM0
    have c2 := (hGL (2 - 1)).2 F p (Fin (k + 1)) (k + 1) ((2 - 1) + (2 + 1)) (by omega) (by omega) M' hM' hM0'
    have d1 := GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem F p (k + 1) ϖ lam π hπ0 2 2 M (fun z => by simpa [hΦ0] using hiff z 0)
    have d2 := GlobalTheory.T.card_windowZeros_eq_integral_additiveSystem F p (k + 1) ϖ lam π hπ0 (2 - 1) (2 + 1) M' (fun z => by simpa [hΦ0'] using hiff' z 0)
    have e1 := GlobalTheory.T.card_windowZeros_inner_eq_shifted_outer F p (k + 1) 2 ϖ hϖ0 (by norm_num) lam π
    have hq1 : 1 < p ^ (k + 1) := Nat.one_lt_pow (by omega) hp.one_lt
    have cS : Nat.card {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0} =
        (p ^ (k + 1)) ^ ((k + 1) * 2) := by
      rw [d1, c1, Fintype.card_fin]
    have cI : Nat.card {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
        ∀ r, rowT p ϖ lam 2 x r = 0} = (p ^ (k + 1)) ^ ((k + 1) * (2 - 1)) := by
      rw [e1, d2, c2, Fintype.card_fin]
    by_contra hcon
    have hsub : ∀ x : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0},
        ∀ j, ‖x.1 j‖ ≤ ‖π j‖ ^ p ^ (k + 1) := by
      intro x
      by_contra hx
      push_neg at hx
      exact hcon ⟨x.1, x.2.1, hx, x.2.2⟩
    haveI : Finite {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
        ∀ r, rowT p ϖ lam 2 x r = 0} := Nat.finite_of_card_ne_zero (by rw [cI]; positivity)
    have hle := Nat.card_le_card_of_injective
      (fun x : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖) ∧ ∀ r, rowS p ϖ lam 2 2 x r = 0} =>
        (⟨x.1, hsub x, x.2.2⟩ : {x : Fin (k + 1) → F // (∀ j, ‖x j‖ ≤ ‖π j‖ ^ p ^ (k + 1)) ∧
          ∀ r, rowT p ϖ lam 2 x r = 0}))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    rw [cS, cI] at hle
    exact absurd hle (not_le.2 (Nat.pow_lt_pow_right hq1 (by omega)))

end GlobalTheory.PMonE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedOneSubIndexMemDegreeOneCharacterDiff
section
open GlobalTheory.BI GlobalTheory.BrauerZero

namespace GlobalTheory.BrauerZero

theorem ind_one_sub_index_mem_D0 {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hK : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) :
    ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  classical
  haveI := Fintype.ofFinite G
  haveI hN : K.Normal := ⟨fun n hn g => by
    have h1 := hK g n
    have : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [this]; exact K.mul_mem h1 hn⟩
  letI : CommGroup (G ⧸ K) :=
    { (inferInstance : Group (G ⧸ K)) with
      mul_comm := by
        intro x y
        induction x using QuotientGroup.induction_on with
        | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have := hK b⁻¹ a⁻¹
          have e : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ := by group
          rw [e]; exact this }
  haveI : Fintype (G ⧸ K) := Fintype.ofFinite _
  let Q := Additive (G ⧸ K)

  let F : AddChar Q ℂ → G → ℂ := fun ψ g => ψ (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))
  have hFmul : ∀ ψ : AddChar Q ℂ, ∀ a b : G, F ψ (a * b) = F ψ a * F ψ b := by
    intro ψ a b
    simp only [F, QuotientGroup.mk_mul, ofMul_mul, AddChar.map_add_eq_mul]
  have hFone : ∀ ψ : AddChar Q ℂ, F ψ 1 = 1 := by
    intro ψ
    simp only [F, QuotientGroup.mk_one, ofMul_one, AddChar.map_zero_eq_one]

  have hgen : ∀ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) ∈ D0 G := by
    intro ψ
    let f : G →* ℂ := { toFun := F ψ, map_one' := hFone ψ, map_mul' := hFmul ψ }
    let χ : (⊤ : Subgroup G) →* ℂˣ := (MonoidHom.toHomUnits f).comp (⊤ : Subgroup G).subtype
    have hcl : ∀ g x : G, F ψ (x⁻¹ * g * x) = F ψ g := by
      intro g x
      rw [hFmul, hFmul, mul_comm (F ψ x⁻¹), mul_assoc, ← hFmul, inv_mul_cancel, hFone, mul_one]
    have h1 : ind (⊤ : Subgroup G) (fun h => (χ h : ℂ)) = F ψ := by
      exact (ind_top (F ψ) hcl : _)
    have h2 : ind (⊤ : Subgroup G) (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ) :=
      ind_top (fun _ => (1 : ℂ)) (fun _ _ => rfl)
    apply AddSubgroup.subset_closure
    exact ⟨⊤, χ, by rw [h1, h2]⟩

  have hind : ∀ g : G, ind K (fun _ => (1 : ℂ)) g = if g ∈ K then (K.index : ℂ) else 0 := by
    intro g
    have hconj : ∀ x : G, (x⁻¹ * g * x ∈ K ↔ g ∈ K) := by
      intro x
      constructor
      · intro h
        have := hN.conj_mem _ h x
        have e : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
        rwa [e] at this
      · intro h
        have := hN.conj_mem _ h x⁻¹
        have e : x⁻¹ * g * x⁻¹⁻¹ = x⁻¹ * g * x := by group
        rwa [e] at this
    simp only [ind, finsum_eq_sum_of_fintype, ext0]
    have hs : ∀ x : G, (if h : x⁻¹ * g * x ∈ K then (1 : ℂ) else 0) = if g ∈ K then 1 else 0 := by
      intro x
      by_cases hg : g ∈ K
      · rw [dif_pos ((hconj x).2 hg), if_pos hg]
      · rw [dif_neg (fun h => hg ((hconj x).1 h)), if_neg hg]
    rw [Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, ← K.card_mul_index]
    have : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := K)).ne'
    split_ifs
    · push_cast; field_simp
    · simp

  have hsum : ∀ g : G, (∑ ψ : AddChar Q ℂ, F ψ g) = if g ∈ K then (K.index : ℂ) else 0 := by
    intro g
    have := AddChar.sum_apply_eq_ite (α := Q) (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))
    simp only [F]
    rw [this]
    have hc : (Fintype.card Q : ℂ) = (K.index : ℂ) := by
      rw [Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
    have he : (Additive.ofMul (QuotientGroup.mk g : G ⧸ K) = 0) ↔ g ∈ K := by
      rw [ofMul_eq_zero, QuotientGroup.eq_one_iff]
    by_cases hg : g ∈ K
    · rw [if_pos (he.2 hg), if_pos hg, hc]
    · rw [if_neg (fun h => hg (he.1 h)), if_neg hg]
  have hcard : (Fintype.card (AddChar Q ℂ) : ℂ) = (K.index : ℂ) := by
    rw [AddChar.card_eq, Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
  have heq : ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ))
      = ∑ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) := by
    funext g
    rw [Finset.sum_apply]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [hind g, hsum g, hcard]
  rw [heq]
  exact AddSubgroup.sum_mem _ (fun ψ _ => hgen ψ)

end GlobalTheory.BrauerZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvCupPairingOfInvCupCharactersStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_cup_pairing_of_inv_cup_characters_alt : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (μ : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g m, μ g m = m) → ∀ (e : H2 μ →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) (I : Γ → Prop) (u : ZMod (l ^ 1)) (γ φ : Γ), (∀ z y : Γ → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = u * (z γ * y φ)) → ∀ (M M' : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M'], (∀ m : M, l • m = 0) → ∀ (β : M →+ M' →+ ZMod (l ^ 1)) (x : Γ → M) (y : Γ → M'), Continuous x → Continuous y → (∀ g h, x (g * h) = x g + x h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = β (x g) (y h)) → e (Submodule.Quotient.mk w) = u * β (x γ) (y φ) := by
  first | exact @GlobalTheory.inv_cup_pairing_of_inv_cup_characters | exact GlobalTheory.inv_cup_pairing_of_inv_cup_characters | (intros; apply GlobalTheory.inv_cup_pairing_of_inv_cup_characters <;> assumption)
end

