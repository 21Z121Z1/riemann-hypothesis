import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0206
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeFullDescends
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeKurOfNorm
section
namespace GlobalTheory.UnramValue

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct IsLocalRing Polynomial

theorem exists_pow_card_eq {S : Type*} [CommRing S] [IsLocalRing S]
    [IsAdicComplete (maximalIdeal S) S] [Fintype (ResidueField S)] (x : S) :
    ∃ t : S, t ^ Fintype.card (ResidueField S) = t ∧ t - x ∈ maximalIdeal S := by
  have h1 : 1 < Fintype.card (ResidueField S) := Fintype.one_lt_card
  have hm : (X ^ Fintype.card (ResidueField S) - X : S[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  obtain ⟨t, ht, htx⟩ := (IsAdicComplete.henselianRing S (maximalIdeal S)).is_henselian _ hm x
    (by
      rw [← residue_eq_zero_iff]
      simp [FiniteField.pow_card])
    (by
      change IsUnit (residue S _)
      rw [derivative_sub, derivative_X_pow]
      simp)
  refine ⟨t, ?_, htx⟩
  simpa [sub_eq_zero] using ht

variable {l : ℕ} [Fact l.Prime]

theorem norm_natCast_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]

theorem integral_mem (L : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] L]
    (h : ∀ x ∈ L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k) (x : integralClosure ℤ_[l] L) :
    ((x : L) : Om l) ∈ MaximalUnramifiedExtension l := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : L) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hmax : ∀ y : integralClosure ℤ_[l] L,
      y ∈ maximalIdeal (integralClosure ℤ_[l] L) ↔ ‖((y : L) : Om l)‖ < 1 := fun y => by
    rw [GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm, GlobalTheory.DiscEval.intEmb_apply,
      GlobalTheory.DiscEval.fieldEmb_apply, PadicComplex.norm_extends]
  have hint : ∀ y : L, y ∈ integralClosure ℤ_[l] L ↔ ‖(y : Om l)‖ ≤ 1 := fun y => by
    rw [GlobalTheory.DiscEval.mem_integralClosure_iff_norm, GlobalTheory.DiscEval.fieldEmb_apply,
      PadicComplex.norm_extends]
  let N : Submodule ℤ_[l] (integralClosure ℤ_[l] L) :=
    { carrier := {y | ((y : L) : Om l) ∈ MaximalUnramifiedExtension l}
      add_mem' := fun ha hb => (MaximalUnramifiedExtension l).add_mem ha hb
      zero_mem' := (MaximalUnramifiedExtension l).zero_mem
      smul_mem' := fun c y hy => (MaximalUnramifiedExtension l).smul_mem (x := (c : ℚ_[l])) hy }
  have := GlobalTheory.DiscEval.isAdicComplete_integralClosure L
  have := GlobalTheory.DiscEval.finite_residueField_integralClosure L
  let _ := Fintype.ofFinite (ResidueField (integralClosure ℤ_[l] L))
  have hle : (⊤ : Submodule ℤ_[l] (integralClosure ℤ_[l] L)) ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal ℤ_[l])
      Module.Finite.fg_top (maximalIdeal_le_jacobson _) fun y _ => ?_
    obtain ⟨t, ht, hty⟩ := exists_pow_card_eq y
    have htN : t ∈ N := by
      change ((t : L) : Om l) ∈ MaximalUnramifiedExtension l
      by_cases h0 : ((t : L) : Om l) = 0
      · rw [h0]; exact zero_mem _
      have h1 : 1 < Fintype.card (ResidueField (integralClosure ℤ_[l] L)) := Fintype.one_lt_card
      refine IntermediateField.subset_adjoin _ _
        ⟨Fintype.card (ResidueField (integralClosure ℤ_[l] L)) - 1, by omega, ?_, ?_⟩
      · rintro ⟨c, hc⟩
        have h2 : (l : ResidueField (integralClosure ℤ_[l] L)) = 0 := by
          rw [← map_natCast (residue _), residue_eq_zero_iff, hmax]
          push_cast
          rw [norm_natCast_l]
          exact inv_lt_one_of_one_lt₀ hl1
        have h3 := congrArg (Nat.cast : ℕ → ResidueField (integralClosure ℤ_[l] L)) hc
        rw [Nat.cast_sub h1.le] at h3
        simp [h2] at h3
      · have h2 := congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : Om l)) ht
        push_cast at h2
        apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel h1.le, h2, one_mul]
    have hd : ((t - y : integralClosure ℤ_[l] L) : L) / l ∈ integralClosure ℤ_[l] L := by
      rw [hint]
      rw [hmax] at hty
      generalize ((t - y : integralClosure ℤ_[l] L) : L) = z at hty
      push_cast
      by_cases h0 : (z : Om l) = 0
      · simp [h0]
      obtain ⟨k, hk⟩ := h _ z.2 h0
      rw [hk, zpow_lt_one_iff_right₀ hl1] at hty
      rw [norm_div, hk, norm_natCast_l, div_inv_eq_mul, ← zpow_add_one₀ (by positivity)]
      exact zpow_le_one_of_nonpos₀ hl1.le (by omega)
    have he : y = t - (l : ℤ_[l]) • (⟨_, hd⟩ : integralClosure ℤ_[l] L) := by
      apply Subtype.ext
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
      push_cast
      field_simp
      ring
    rw [he]
    refine sub_mem (Submodule.mem_sup_left htN) (Submodule.mem_sup_right
      (Submodule.smul_mem_smul ?_ Submodule.mem_top))
    exact PadicInt.irreducible_p.not_isUnit
  exact hle Submodule.mem_top

theorem le_Kur_of_norm : ∀ (l : ℕ) [Fact l.Prime] (M : FinExt l),
    (∀ x ∈ M.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k) → M.1 ≤ MaximalUnramifiedExtension l := by
  intro l _ M h x hx
  obtain ⟨L, hL⟩ := M
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := integralClosure ℤ_[l] L) (⟨x, hx⟩ : L)
  have h1 : x = ((a : L) : Om l) / ((b : L) : Om l) := (congrArg Subtype.val hab).symm
  rw [h1]
  exact div_mem (integral_mem L h a) (integral_mem L h b)

end GlobalTheory.UnramValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedOfFrobeniusIterateFixedFil
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.CrisPerFix

variable {l : ℕ} [Fact l.Prime]

def maxUnramifiedFrobenius (P : LocPrime l) (K : FinExt l) : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥(K0 K) :=
  AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij

theorem frobK0_apply (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) :
    maxUnramifiedFrobenius P K x = (P.PD K).σ x := rfl

theorem nontrivial_B (P : LocPrime l) (K : FinExt l) : Nontrivial P.R.B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact (P.PD K).not_mem_filtration_two (by rw [Subsingleton.elim ((P.PD K).t) 0, map_zero]; exact Submodule.zero_mem _)

theorem ιB_algebraMap (P : LocPrime l) (K : FinExt l) (a : ↥(K0 K)) :
    P.ιB (algebraMap ↥(K0 K) P.R.B a) = algebraMap ↥(K0 K) P.R.BdR a := by
  rw [← P.PD_ι K]
  exact (P.PD K).ι.commutes a

theorem orderOf_frobK0 (P : LocPrime l) (K : FinExt l) :
    orderOf (maxUnramifiedFrobenius P K) = finrank ℚ_[l] ↥(K0 K) := by
  haveI := (P.PD K).finK₀
  haveI := nontrivial_B P K
  have hfix : IntermediateField.fixedField (Subgroup.zpowers (maxUnramifiedFrobenius P K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hσ : (P.PD K).σ x = x := hx _ (Subgroup.mem_zpowers _)
    obtain ⟨q, hq⟩ := (P.PD K).fund (algebraMap ↥(K0 K) P.R.B x)
      (by rw [(P.PD K).φ_K₀, hσ])
      (by
        rw [(P.PD K).ι.commutes, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_of_tower_mem _ x (P.PD K).one_mem)
    rw [IntermediateField.mem_bot]
    refine ⟨q, (algebraMap ↥(K0 K) P.R.B).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact hq
  have h := IntermediateField.finrank_fixedField_eq_card (Subgroup.zpowers (maxUnramifiedFrobenius P K))
  rw [hfix, IntermediateField.finrank_bot', Nat.card_zpowers] at h
  exact h.symm

theorem iterate_φB_mul (P : LocPrime l) (K : FinExt l) (j : ℕ) (b : ↥(K0 K)) (x : P.R.B) :
    (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * x) =
      algebraMap ↥(K0 K) P.R.B ((maxUnramifiedFrobenius P K ^ j) b) * (⇑P.φB)^[j] x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, ← P.PD_φ K (algebraMap _ _ _), (P.PD K).φ_K₀,
      Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, frobK0_apply]

theorem det_ne_zero (P : LocPrime l) (K : FinExt l)
    (bas : Module.Basis (Fin (finrank ℚ_[l] ↥(K0 K))) ℚ_[l] ↥(K0 K)) :
    (Matrix.of fun i j : Fin (finrank ℚ_[l] ↥(K0 K)) => (maxUnramifiedFrobenius P K ^ (j : ℕ)) (bas i)).det ≠ 0 := by
  set τ := maxUnramifiedFrobenius P K
  intro h
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  let L : ↥(K0 K) →ₗ[ℚ_[l]] ↥(K0 K) :=
    { toFun := fun x => ∑ j : Fin (finrank ℚ_[l] ↥(K0 K)), u j * (τ ^ (j : ℕ)) x
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_smul_comm]
        congr 1
        exact (τ ^ (j : ℕ)).toLinearEquiv.map_smul r x }
  have hL : L = 0 := by
    refine bas.ext fun i => ?_
    have := congrFun hu i
    simpa [L, Matrix.mulVec, dotProduct, mul_comm] using this
  let f : Fin (finrank ℚ_[l] ↥(K0 K)) → (↥(K0 K) →* ↥(K0 K)) := fun j => ((τ ^ (j : ℕ)).toRingEquiv : _ ≃+* _).toMonoidHom
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : τ ^ (i : ℕ) = τ ^ (j : ℕ) := AlgEquiv.ext fun x => DFunLike.congr_fun hij x
    have hi : (i : ℕ) ∈ Set.Iio (orderOf τ) := by rw [orderOf_frobK0]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf τ) := by rw [orderOf_frobK0]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h1)
  have li := (linearIndependent_monoidHom ↥(K0 K) ↥(K0 K)).comp f hf
  rw [Fintype.linearIndependent_iff] at li
  apply hu0
  funext j
  refine li u ?_ j
  funext x
  have := LinearMap.congr_fun hL x
  simpa [L, f, Finset.sum_apply, smul_eq_mul] using this

theorem mem_unramified_of_frobenius_iterate_fixed_fil_alt :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K : FinExt l) (c : P.R.B), (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] c = c →
    (∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0) →
    ∃ a : ↥(K0 K), c = algebraMap ↥(K0 K) P.R.B a := by
  intro l _ P _ _ K c hn hF
  set n := finrank ℚ_[l] ↥(K0 K) with hn_def
  haveI := (P.PD K).finK₀
  set τ := maxUnramifiedFrobenius P K
  have hord : orderOf τ = n := orderOf_frobK0 P K
  have hn0 : 0 < n := Module.finrank_pos
  let bas := Module.finBasisOfFinrankEq ℚ_[l] ↥(K0 K) hn_def.symm
  let A : Matrix (Fin n) (Fin n) ↥(K0 K) := Matrix.of fun i j => (τ ^ (j : ℕ)) (bas i)
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.2 (det_ne_zero P K bas)
  have hs : ∀ b : ↥(K0 K), ∃ q : ℚ_[l], algebraMap ℚ_[l] P.R.B q =
      ∑ j ∈ Finset.range n, (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c) := by
    intro b
    apply (P.PD K).fund
    · rw [P.PD_φ, map_sum]
      have e1 : ∀ j, P.φB ((⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c)) =
          (⇑P.φB)^[j + 1] (algebraMap ↥(K0 K) P.R.B b * c) :=
        fun j => (Function.iterate_succ_apply' _ _ _).symm
      simp_rw [e1]
      have hfn : (⇑P.φB)^[n] (algebraMap ↥(K0 K) P.R.B b * c) =
          (⇑P.φB)^[0] (algebraMap ↥(K0 K) P.R.B b * c) := by
        rw [iterate_φB_mul, hn, ← hord, pow_orderOf_eq_one, AlgEquiv.one_apply, Function.iterate_zero, id]
      have h := Finset.sum_range_succ' (fun j => (⇑P.φB)^[j] (algebraMap ↥(K0 K) P.R.B b * c)) n
      rw [Finset.sum_range_succ, hfn] at h
      exact (add_right_cancel h).symm
    · rw [P.PD_ι, map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [iterate_φB_mul, map_mul, ιB_algebraMap, ← Algebra.smul_def]
      exact Submodule.smul_of_tower_mem _ _ (hF j)
  choose q hq using fun i => hs (bas i)
  let v : Fin n → P.R.B := fun j => (⇑P.φB)^[(j : ℕ)] c
  have hAv : Matrix.mulVec (A.map (algebraMap ↥(K0 K) P.R.B)) v =
      fun i => algebraMap ↥(K0 K) P.R.B (algebraMap ℚ_[l] ↥(K0 K) (q i)) := by
    funext i
    rw [← IsScalarTower.algebraMap_apply, hq i, Finset.sum_range]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, A, v, Matrix.of_apply, iterate_φB_mul]
    rfl
  have hinv : (A⁻¹.map (algebraMap ↥(K0 K) P.R.B)) * (A.map (algebraMap ↥(K0 K) P.R.B)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hv : v = Matrix.mulVec (A⁻¹.map (algebraMap ↥(K0 K) P.R.B))
      (fun i => algebraMap ↥(K0 K) P.R.B (algebraMap ℚ_[l] ↥(K0 K) (q i))) := by
    rw [← hAv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  refine ⟨∑ i, A⁻¹ ⟨0, hn0⟩ i * algebraMap ℚ_[l] ↥(K0 K) (q i), ?_⟩
  have h0 := congrFun hv ⟨0, hn0⟩
  simp only [v, Function.iterate_zero, id] at h0
  rw [h0]
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

end GlobalTheory.CrisPerFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
section
noncomputable section

open Filter Topology

namespace GlobalTheory.PadicLogUnits

variable {l : ℕ} [hl : Fact l.Prime]

def term (y : ℚ_[l]) (k : ℕ) : ℚ_[l] := (-1 : ℚ_[l]) ^ k * y ^ (k + 1) / ((k : ℚ_[l]) + 1)

def lg (x : ℚ_[l]) : ℚ_[l] := ∑' k : ℕ, term (x - 1) k

lemma inv_norm_succ_le (k : ℕ) : ‖((k : ℚ_[l]) + 1)‖⁻¹ ≤ 2 ^ k := by
  have h0 : ((k + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h1 : ((k : ℚ_[l]) + 1) = ((k + 1 : ℕ) : ℚ_[l]) := by push_cast; rfl
  rw [h1, Padic.norm_eq_zpow_neg_valuation h0, Padic.valuation_natCast, zpow_neg, inv_inv,
    zpow_natCast]
  have h2 : l ^ padicValNat l (k + 1) ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) pow_padicValNat_dvd
  have h3 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  exact_mod_cast h2.trans h3

lemma norm_pow_div_le {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) (k : ℕ) :
    ‖y ^ (k + 1) / ((k : ℚ_[l]) + 1)‖ ≤ ‖y‖ * (2 / 3) ^ k := by
  rw [norm_div, norm_pow, div_eq_mul_inv, pow_succ']
  have h1 : ‖y‖ ^ k ≤ (1 / 3) ^ k := pow_le_pow_left₀ (norm_nonneg _) hy k
  calc ‖y‖ * ‖y‖ ^ k * ‖((k : ℚ_[l]) + 1)‖⁻¹ ≤ ‖y‖ * (1 / 3) ^ k * 2 ^ k := by
        gcongr
        exact inv_norm_succ_le k
    _ = ‖y‖ * (2 / 3) ^ k := by rw [mul_assoc, ← mul_pow]; norm_num

lemma norm_term_le {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) (k : ℕ) :
    ‖term y k‖ ≤ ‖y‖ * (2 / 3) ^ k := by
  rw [term, mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_pow_div_le hy k

lemma summable_geo (c : ℝ) : Summable fun k : ℕ => c * (2 / 3 : ℝ) ^ k :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left c

lemma summable_term {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) : Summable (term y) :=
  Summable.of_norm_bounded (summable_geo ‖y‖) (norm_term_le hy)

lemma norm_lg {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) : ‖lg x‖ = ‖x - 1‖ := by
  rcases eq_or_ne (x - 1) 0 with h | h
  · simp [lg, h, term]
  have hpos : 0 < ‖x - 1‖ := norm_pos_iff.mpr h
  rw [lg, (summable_term hx).tsum_eq_zero_add]
  have h0 : term (x - 1) 0 = x - 1 := by simp [term]
  have h1 : ‖∑' k : ℕ, term (x - 1) (k + 1)‖ ≤ ‖x - 1‖ * (2 / 3) := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
    refine (norm_term_le hx (k + 1)).trans ?_
    gcongr
    exact pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero k)
  have h2 : ‖∑' k : ℕ, term (x - 1) (k + 1)‖ < ‖x - 1‖ := by linarith
  rw [h0, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne', max_eq_left h2.le]

lemma desc_eval_neg_one (k : ℕ) :
    (descPochhammer ℚ_[l] k).eval (-1) = (-1) ^ k * (k.factorial : ℚ_[l]) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_eval, ih, Nat.factorial_succ]
    push_cast
    ring

lemma tendsto_pow_zero : Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one

lemma tendsto_choose (k : ℕ) :
    Tendsto (fun n : ℕ => (((l ^ n - 1).choose k : ℕ) : ℚ_[l])) atTop (𝓝 ((-1) ^ k)) := by
  have hk : (k.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h1 : Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n - 1) atTop (𝓝 (-1)) := by
    simpa using (tendsto_pow_zero (l := l)).sub_const 1
  have h2 := (((descPochhammer ℚ_[l] k).continuous.tendsto (-1)).comp h1).div_const
    (k.factorial : ℚ_[l])
  rw [desc_eval_neg_one, mul_div_cancel_right₀ _ hk] at h2
  refine h2.congr fun n => ?_
  rw [Nat.cast_choose_eq_descPochhammer_div, Nat.cast_sub (Nat.one_le_pow _ _ hl.out.pos)]
  simp

lemma pow_sub_one_div (y : ℚ_[l]) (M : ℕ) :
    ((1 + y) ^ (M + 1) - 1) / ((M + 1 : ℕ) : ℚ_[l]) =
      ∑' k : ℕ, ((M.choose k : ℕ) : ℚ_[l]) * (y ^ (k + 1) / ((k : ℚ_[l]) + 1)) := by
  have h0 : ((M + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
  rw [tsum_eq_sum (s := Finset.range (M + 1))
    (fun k hk => by rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]; simp)]
  rw [add_comm 1 y, add_pow, Finset.sum_range_succ', div_eq_iff h0, Finset.sum_mul]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ((k : ℚ_[l]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h := congrArg (Nat.cast : ℕ → ℚ_[l]) (Nat.add_one_mul_choose_eq M k)
  push_cast at h ⊢
  field_simp
  linear_combination (-(y ^ (k + 1))) * h

lemma tendsto_lg {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) :
    Tendsto (fun n : ℕ => (x ^ (l ^ n) - 1) / (l : ℚ_[l]) ^ n) atTop (𝓝 (lg x)) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (n k : ℕ) => (((l ^ n - 1).choose k : ℕ) : ℚ_[l]) *
      ((x - 1) ^ (k + 1) / ((k : ℚ_[l]) + 1))) (g := term (x - 1))
    (summable_geo ‖x - 1‖) (fun k => by
      rw [term, mul_div_assoc]; exact (tendsto_choose k).mul_const _)
    (Eventually.of_forall fun n k => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans
        (norm_pow_div_le hx k))
  refine h.congr fun n => ?_
  rw [← pow_sub_one_div, Nat.sub_add_cancel (Nat.one_le_pow _ _ hl.out.pos)]
  simp

lemma norm_mul_sub_one {x w : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (hw : ‖w - 1‖ ≤ 1 / 3) :
    ‖x * w - 1‖ ≤ 1 / 3 := by
  have : x * w - 1 = (x - 1) * (w - 1) + (x - 1) + (w - 1) := by ring
  rw [this]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hw)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)
  rw [norm_mul]
  nlinarith [norm_nonneg (x - 1), norm_nonneg (w - 1)]

lemma lg_mul {x w : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (hw : ‖w - 1‖ ≤ 1 / 3) :
    lg (x * w) = lg x + lg w := by
  have h := ((tendsto_lg hx).add (tendsto_lg hw)).add
    (tendsto_pow_zero.mul ((tendsto_lg hx).mul (tendsto_lg hw)))
  rw [zero_mul, add_zero] at h
  refine tendsto_nhds_unique (tendsto_lg (norm_mul_sub_one hx hw)) (h.congr fun n => ?_)
  have h0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  rw [mul_pow]
  field_simp
  ring

lemma lg_pow {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (m : ℕ) :
    ‖x ^ m - 1‖ ≤ 1 / 3 ∧ lg (x ^ m) = m * lg x := by
  induction m with
  | zero => simp [lg, term]
  | succ m ih =>
    rw [pow_succ]
    refine ⟨norm_mul_sub_one ih.1 hx, ?_⟩
    rw [lg_mul ih.1 hx, ih.2]
    push_cast
    ring

lemma continuousOn_lg : ContinuousOn (lg (l := l)) {x | ‖x - 1‖ ≤ 1 / 3} := by
  refine continuousOn_tsum (fun k => ?_) (summable_geo (1 / 3)) (fun k x hx => ?_)
  · unfold term
    fun_prop
  · refine (norm_term_le hx k).trans ?_
    gcongr
    exact hx

lemma norm_unit_pow_sub_one {u : ℚ_[l]} (hu : ‖u‖ = 1) :
    ‖u ^ (l * (l - 1)) - 1‖ ≤ (l : ℝ) ^ (-(2 : ℕ) : ℤ) := by
  let z : ℤ_[l] := ⟨u, hu.le⟩
  have hz : IsUnit z := PadicInt.isUnit_iff.mpr hu
  obtain ⟨v, hv⟩ := hz.map (PadicInt.toZModPow (p := l) 2)
  have h1 := ZMod.pow_totient v
  rw [Nat.totient_prime_pow hl.out (by norm_num)] at h1
  have h2 : z ^ (l * (l - 1)) - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := l) 2) := by
    rw [RingHom.mem_ker, map_sub, map_pow, map_one, ← hv, ← Units.val_pow_eq_pow_val]
    simp only [Nat.add_one_sub_one, pow_one] at h1
    rw [h1]
    simp
  rw [PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow] at h2
  exact h2

lemma zpow_le_third {j : ℕ} (h1 : 1 ≤ j) (h2 : l = 2 → 2 ≤ j) :
    (l : ℝ) ^ (-(j : ℤ)) ≤ 1 / 3 := by
  have h3 : 3 ≤ l ^ j := by
    by_cases h : l = 2
    · subst h
      exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (h2 rfl))
    · have := hl.out.two_le
      calc 3 ≤ l ^ 1 := by rw [pow_one]; omega
        _ ≤ l ^ j := Nat.pow_le_pow_right hl.out.pos h1
  rw [zpow_neg, zpow_natCast, one_div]
  exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)

lemma norm_unit_pow_sub_one' {u : ℚ_[l]} (hu : ‖u‖ = 1) : ‖u ^ (l * (l - 1)) - 1‖ ≤ 1 / 3 :=
  (norm_unit_pow_sub_one hu).trans (zpow_le_third (by norm_num) fun _ => le_rfl)

lemma logZl_eq (u : ℚ_[l]) :
    Formalism.MainNotions.LocalSituation.logZl l u = lg (u ^ (l * (l - 1))) / ((l : ℚ_[l]) * ((l : ℚ_[l]) - 1)) := rfl

lemma norm_sub_one : ‖(l : ℚ_[l]) - 1‖ = 1 := by
  have h : ‖(l : ℚ_[l])‖ < ‖(-1 : ℚ_[l])‖ := by
    simpa using Padic.norm_p_lt_one (p := l)
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne, max_eq_right h.le]
  simp

theorem logZl_hom : ∀ (l : ℕ) [Fact l.Prime],
    (∀ u w : ℚ_[l], ‖u‖ = 1 → ‖w‖ = 1 →
      Formalism.MainNotions.LocalSituation.logZl l (u * w) = Formalism.MainNotions.LocalSituation.logZl l u + Formalism.MainNotions.LocalSituation.logZl l w) ∧
    ContinuousOn (Formalism.MainNotions.LocalSituation.logZl l) {u | ‖u‖ = 1} ∧
    (∀ u : ℚ_[l], ‖u‖ = 1 → ‖Formalism.MainNotions.LocalSituation.logZl l u‖ ≤ 1) ∧
    ∀ j : ℕ, 1 ≤ j → (l = 2 → 2 ≤ j) → ∀ u : ℚ_[l], ‖u - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ)) →
      ‖Formalism.MainNotions.LocalSituation.logZl l u‖ = ‖u - 1‖ := by
  intro l hl
  refine ⟨fun u w hu hw => ?_, ?_, fun u hu => ?_, fun j h1 h2 u hu => ?_⟩
  · rw [logZl_eq, logZl_eq, logZl_eq, mul_pow,
      lg_mul (norm_unit_pow_sub_one' hu) (norm_unit_pow_sub_one' hw), add_div]
  · exact (continuousOn_lg.comp (continuous_pow (l * (l - 1))).continuousOn
      fun u hu => norm_unit_pow_sub_one' hu).div_const _
  · have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_le
    rw [logZl_eq, norm_div, norm_lg (norm_unit_pow_sub_one' hu), norm_mul, norm_sub_one,
      mul_one, Padic.norm_p, div_le_one (by positivity)]
    refine (norm_unit_pow_sub_one hu).trans ?_
    rw [← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1 (by norm_num)
  · have hu' := hu.trans (zpow_le_third h1 h2)
    have h0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
    have h3 : (l : ℚ_[l]) - 1 ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_sub_one]; exact one_ne_zero
    rw [logZl_eq, (lg_pow hu' _).2, Nat.cast_mul, Nat.cast_sub hl.out.one_le, Nat.cast_one,
      mul_div_cancel_left₀ _ (mul_ne_zero h0 h3), norm_lg hu']

end GlobalTheory.PadicLogUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicitySubquotientLatticeLeStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senMultiplicity_subquotient_lattice_le : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (B A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (w w' : ZMod n → ℤ) (N : Lats k n B.m), F.Obj B → IsHom A₁ B j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → ABC (F.D B) w w' N → ∀ i x, sen ((F.D A).γ i) (F.push A₁ A p (F.pre A₁ B j N) i) x ≤ sen ((F.D B).γ i) (N i) x := by
  first | exact @GlobalTheory.Models.sen_push_pre_le | exact GlobalTheory.Models.sen_push_pre_le | (intros; apply GlobalTheory.Models.sen_push_pre_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeFullDescendsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachExpansionLattice_full_descends : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → Full (Di (HW l) h T i) (Lat C h T i ζ) → Full (Di (HW l) h T (i - 1)) (Lat C h T (i - 1) (ζ ^ l)) := by
  first | exact @GlobalTheory.NL.FullDown.full_down | exact GlobalTheory.NL.FullDown.full_down | (intros; apply GlobalTheory.NL.FullDown.full_down <;> assumption)
end

