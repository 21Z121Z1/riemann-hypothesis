import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.StrongApproximationUnitaryCongruence
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0119
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMulIntegralAtSplitPrime
section
open NumberField IsDedekindDomain Matrix
open scoped BigOperators

namespace GlobalTheory.UnIntApprox

open Filter Topology

theorem exists_near {K : Type} [Field K] [CharZero K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]
    (w : AbsoluteValue K ℝ) {q : K} (hq0 : q ≠ 0) (hq : star q = q⁻¹) (hw : w q < 1)
    (g : Matrix n n K) (hg : IsUnit g.det) :
    ∃ u : Matrix n n K, uᴴ * u = 1 ∧ (∀ i j, w ((g⁻¹ * u - 1) i j) ≤ 1) ∧
      ∀ i j, w ((u⁻¹ * g - 1) i j) ≤ 1 := by
  let ι := Fintype.equivFin n
  obtain ⟨u, hu, hlim⟩ := GlobalTheory.UnApprox.exists_seq (G := (1 : Matrix (Fin (Fintype.card n)) _ K))
    conjTranspose_one (by simp) (reindex ι ι g) (fun k => (1 + q ^ k)⁻¹)
  let _ : NormedField K := w.toNormedField
  have hq1 : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw
  have he : Tendsto (fun k : ℕ => (1 + q ^ k)⁻¹) atTop (𝓝 1) := by
    simpa using (hq1.const_add 1).inv₀ (by simp)
  have he' : Tendsto (fun k : ℕ => star (1 + q ^ k)⁻¹) atTop (𝓝 0) := by
    have h := hq1.mul he
    rw [zero_mul] at h
    refine h.congr fun k => ?_
    have hk : q ^ k ≠ 0 := pow_ne_zero _ hq0
    rw [star_inv₀, star_add, star_one, star_pow, hq, inv_pow]
    have : 1 + (q ^ k)⁻¹ = (q ^ k)⁻¹ * (1 + q ^ k) := by field_simp; ring
    rw [this, mul_inv, inv_inv]
  have h1 := hlim w (tendsto_iff_norm_sub_tendsto_zero.1 he) (tendsto_zero_iff_norm_tendsto_zero.1 he')
  let U : ℕ → Matrix n n K := fun k => (u k).submatrix ι ι
  have hU : Tendsto U atTop (𝓝 g) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    have h3 := h1 (ι i) (ι j)
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] at h3
    exact h3
  have hinv : ContinuousAt Inv.inv g :=
    continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hg.ne_zero)
  have ha : Tendsto (fun k => g⁻¹ * U k - 1) atTop (𝓝 0) := by
    have := (hU.const_mul g⁻¹).sub_const 1
    rwa [nonsing_inv_mul _ hg, sub_self] at this
  have hb : Tendsto (fun k => (U k)⁻¹ * g - 1) atTop (𝓝 0) := by
    have := ((hinv.tendsto.comp hU).mul_const g).sub_const 1
    rwa [nonsing_inv_mul _ hg, sub_self] at this
  have key : ∀ f : ℕ → Matrix n n K, Tendsto f atTop (𝓝 0) → ∀ᶠ k in atTop, ∀ i j, w (f k i j) ≤ 1 := by
    intro f hf
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have := tendsto_zero_iff_norm_tendsto_zero.1 (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hf i) j)
    exact this.eventually_le_const one_pos
  obtain ⟨k, hk1, hk2⟩ := ((key _ ha).and (key _ hb)).exists
  refine ⟨U k, ?_, hk1, hk2⟩
  have h2 : (u k)ᴴ * u k = 1 := by
    have := hu k
    rw [Matrix.mul_one] at this
    exact mul_eq_one_comm.1 this
  show ((u k).submatrix ι ι)ᴴ * (u k).submatrix ι ι = 1
  rw [conjTranspose_submatrix, submatrix_mul_equiv, h2, submatrix_one_equiv]

theorem exists_unitary_mul_integral :
    ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* K) (n : Type) [Fintype n] [DecidableEq n] (𝔭 : HeightOneSpectrum (𝓞 K)) (α β : 𝓞 K), (∀ x, σ (σ x) = x) → α ∈ 𝔭.asIdeal → β ∉ 𝔭.asIdeal → (β : K) = σ α → ∀ g : Matrix n n K, IsUnit g.det → ∃ u : Matrix n n K, (u.map σ)ᵀ * u = 1 ∧ ∃ t : 𝓞 K, t ∉ 𝔭.asIdeal ∧ (∀ i j, (t : K) * (g⁻¹ * u) i j ∈ (algebraMap (𝓞 K) K).range) ∧ ∀ i j, (t : K) * (u⁻¹ * g) i j ∈ (algebraMap (𝓞 K) K).range := by
  intro K _ _ σ n _ _ 𝔭 α β hσ hα hβ hαβ g hg
  let _ : StarRing K :=
    { star := σ
      star_involutive := hσ
      star_mul := fun x y => by rw [map_mul, mul_comm]
      star_add := fun x y => map_add σ x y }
  have hβ0 : (β : K) ≠ 0 := by
    intro h
    apply hβ
    have : β = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have hα0 : (α : K) ≠ 0 := by
    intro h
    apply hβ0
    rw [hαβ, h, map_zero]
  have hq : star ((α : K) / β) = ((α : K) / β)⁻¹ := by
    show σ _ = _
    rw [map_div₀, ← hαβ, hαβ, hσ, inv_div]
  have hw : NumberField.HeightOneSpectrum.adicAbv K 𝔭 ((α : K) / β) < 1 := by
    rw [map_div₀, ← FinitePlace.norm_embedding, ← FinitePlace.norm_embedding]
    have h1 := (FinitePlace.norm_lt_one_iff_mem K 𝔭 α).2 hα
    have h2 := (FinitePlace.norm_eq_one_iff_notMem K 𝔭 β).2 hβ
    erw [h2]
    rw [div_one]
    exact h1
  obtain ⟨u, hu, h1, h2⟩ := exists_near _ (div_ne_zero hα0 hβ0) hq hw g hg
  obtain ⟨s, hs, hsb⟩ := GlobalTheory.UnApprox.exists_denom (J := (n × n) ⊕ (n × n)) 𝔭.ne_bot
    (Sum.elim (fun p => (g⁻¹ * u - 1) p.1 p.2) (fun p => (u⁻¹ * g - 1) p.1 p.2)) (by
      intro v hv
      have : v = 𝔭 := by
        ext1
        exact (𝔭.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.1 hv)).symm
      subst this
      rintro (p | p)
      · exact h1 _ _
      · exact h2 _ _)
  have key : ∀ (M : Matrix n n K) (i j : n), (∃ b : 𝓞 K, (s : K) * (M - 1) i j = b) →
      (s : K) * M i j ∈ (algebraMap (𝓞 K) K).range := by
    rintro M i j ⟨b, hb⟩
    refine ⟨b + if i = j then s else 0, ?_⟩
    rw [Matrix.sub_apply, one_apply, mul_sub] at hb
    rw [map_add]
    split_ifs at hb ⊢
    · show (b : K) + s = _
      linear_combination -hb
    · rw [map_zero]
      show (b : K) + 0 = _
      linear_combination -hb
  refine ⟨u, hu, s, fun h => 𝔭.isPrime.ne_top ?_, fun i j => key _ _ _ (hsb (Sum.inl (i, j))),
    fun i j => key _ _ _ (hsb (Sum.inr (i, j)))⟩
  have := Ideal.isCoprime_iff_sup_eq.1 hs
  rwa [sup_eq_right.2 ((Ideal.span_singleton_le_iff_mem _).2 h)] at this

end GlobalTheory.UnIntApprox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisInvariantsBcrisEqMaxUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc Polynomial
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.InvCris

section Abstract
variable {k Ω B D : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing B] [CommRing D]
  {U : IntermediateField k Ω} {ι : B →+* D} {O : Ω →+* D} {u : U →+* B} {φ : B →+* B} {σ : U →ₐ[k] U}

theorem aeval_step [Nontrivial D] (hι : Function.Injective ι) (hu : ∀ c : U, ι (u c) = O c)
    (hφ : ∀ c : U, φ (u c) = u (σ c)) {b : B} {y y' : Ω} (hy : ι b = O y) (hy' : ι (φ b) = O y')
    (q : k[X]) (hq : aeval y q = 0) : aeval y' q = 0 := by
  set v : k →+* B := u.comp (algebraMap k U) with hv
  have e1 : ι.comp v = O.comp (algebraMap k Ω) := by
    ext c
    simp [hv, hu]
  have e2 : φ.comp v = v := by
    ext c
    simp [hv, hφ]
  have key : ∀ (x : B) (z : Ω), ι x = O z → ι (q.eval₂ v x) = O (aeval z q) := by
    intro x z h
    rw [aeval_def, hom_eval₂, hom_eval₂, e1, h]
  have h0 : q.eval₂ v b = 0 := hι (by rw [key b y hy, hq, map_zero, map_zero])
  have h1 : q.eval₂ v (φ b) = 0 := by
    have := congrArg φ h0
    rwa [hom_eval₂, e2, map_zero] at this
  apply O.injective
  rw [← key _ _ hy', h1, map_zero, map_zero]

theorem periodic [Nontrivial D] [Algebra.IsAlgebraic k Ω] (hι : Function.Injective ι)
    (hu : ∀ c : U, ι (u c) = O c) (hφ : ∀ c : U, φ (u c) = u (σ c)) (S : AddSubgroup B)
    (hS : ∀ b ∈ S, φ b ∈ S) (hO : ∀ b ∈ S, ∃ y, ι b = O y) {b : B} (hb : b ∈ S) :
    ∃ N, 0 < N ∧ φ^[N] b = b := by
  have hint : ∀ y : Ω, IsIntegral k y := fun y => (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hit : ∀ (i : ℕ) (x : B), x ∈ S → φ^[i] x ∈ S := by
    intro i x hx
    induction i with
    | zero => exact hx
    | succ i ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  have hinj0 : ∀ x ∈ S, φ x = 0 → x = 0 := by
    intro x hx h
    obtain ⟨y, hy⟩ := hO x hx
    have := aeval_step hι hu hφ hy (y' := 0) (by rw [h, map_zero, map_zero]) _ (minpoly.aeval k y)
    rw [← coeff_zero_eq_aeval_zero', map_eq_zero, minpoly.coeff_zero_eq_zero (hint y)] at this
    exact hι (by rw [hy, this, map_zero, map_zero])
  have hinj : ∀ (i : ℕ) (x : B), x ∈ S → φ^[i] x = φ^[i] b → x = b := by
    intro i
    induction i with
    | zero => exact fun x _ h => h
    | succ i ih =>
      intro x hx h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
      refine ih x hx (sub_eq_zero.1 (hinj0 _ (S.sub_mem (hit i x hx) (hit i b hb)) ?_))
      rw [map_sub, h, sub_self]
  choose y hy using fun i : ℕ => hO _ (hit i b hb)
  have hroot : ∀ i, aeval (y i) (minpoly k (y 0)) = 0 := by
    intro i
    induction i with
    | zero => exact minpoly.aeval k _
    | succ i ih =>
      exact aeval_step hι hu hφ (hy i) (by rw [← hy (i + 1), Function.iterate_succ_apply']) _ ih
  obtain ⟨i, j, hij, h⟩ := (Polynomial.rootSet_finite (minpoly k (y 0)) Ω).exists_lt_map_eq_of_forall_mem
    (f := y) (fun i => (Polynomial.mem_rootSet_of_ne (minpoly.ne_zero (hint _))).2 (hroot i))
  refine ⟨j - i, Nat.sub_pos_of_lt hij, hinj i _ (hit _ _ hb) ?_⟩
  rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hij.le]
  exact hι (by rw [hy, hy, h])

theorem mem_range (hu : ∀ c : U, ι (u c) = O c) (hφ : ∀ c : U, φ (u c) = u (σ c))
    (fund : ∀ (b : B) (y : Ω), φ b = b → ι b = O y → ∃ c : k, u (algebraMap k U c) = b)
    {b : B} {N : ℕ} (hN : 0 < N) (hb : φ^[N] b = b) (hO : ∀ i, ∃ y, ι (φ^[i] b) = O y)
    {ζ : U} (hζ : σ^[N] ζ = ζ) (hζ' : ∀ i, 0 < i → i < N → σ^[i] ζ ≠ ζ) : ∃ c, u c = b := by
  choose y hy using hO
  have tr : ∀ n : ℕ, ∑ i ∈ Finset.range N, u ((σ^[i] ζ) ^ n) * φ^[i] b ∈ u.range := by
    intro n
    obtain ⟨c, hc⟩ := fund (∑ i ∈ Finset.range N, u ((σ^[i] ζ) ^ n) * φ^[i] b)
      (∑ i ∈ Finset.range N, (((σ^[i] ζ) ^ n : U) : Ω) * y i) (by
        rw [map_sum]
        have e : ∀ i, φ (u ((σ^[i] ζ) ^ n) * φ^[i] b) = u ((σ^[i + 1] ζ) ^ n) * φ^[i + 1] b := by
          intro i
          rw [map_mul, hφ, map_pow σ, Function.iterate_succ_apply', Function.iterate_succ_apply']
        simp only [e]
        have h1 := Finset.sum_range_succ (fun i => u ((σ^[i] ζ) ^ n) * φ^[i] b) N
        have h2 := Finset.sum_range_succ' (fun i => u ((σ^[i] ζ) ^ n) * φ^[i] b) N
        rw [h1, hζ, hb] at h2
        exact (add_right_cancel h2).symm) (by
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul, hu, hy])
    exact ⟨_, hc⟩
  have pol : ∀ p : U[X], ∑ i ∈ Finset.range N, u (p.eval (σ^[i] ζ)) * φ^[i] b ∈ u.range := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [eval_add, map_add, add_mul, Finset.sum_add_distrib]
      exact add_mem hp hq
    | monomial n a =>
      simp only [eval_monomial, map_mul, mul_assoc, ← Finset.mul_sum]
      exact mul_mem ⟨a, rfl⟩ (tr n)
  obtain ⟨c, hc⟩ := pol (∏ j ∈ (Finset.range N).erase 0, (X - C (σ^[j] ζ)))
  rw [Finset.sum_eq_single 0] at hc
  · have hne : (∏ j ∈ (Finset.range N).erase 0, (X - C (σ^[j] ζ))).eval (σ^[0] ζ) ≠ 0 := by
      rw [eval_prod]
      refine Finset.prod_ne_zero_iff.2 fun j hj => ?_
      rw [Finset.mem_erase, Finset.mem_range] at hj
      simpa [sub_eq_zero] using (hζ' j (Nat.pos_of_ne_zero hj.1) hj.2).symm
    refine ⟨((∏ j ∈ (Finset.range N).erase 0, (X - C (σ^[j] ζ))).eval (σ^[0] ζ))⁻¹ * c, ?_⟩
    rw [map_mul, hc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
    rfl
  · intro i hi hi0
    rw [eval_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hi0, hi⟩) (by simp), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 hN) h

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem exists_period (σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l))
    (hσ : ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l) {N : ℕ} (hN : 0 < N) :
    ∃ ζ : ↥(MaximalUnramifiedExtension l), σ^[N] ζ = ζ ∧ ∀ i, 0 < i → i < N → σ^[i] ζ ≠ ζ := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have h1 : 1 < l ^ N := Nat.one_lt_pow hN.ne' hl
  have hm : 0 < l ^ N - 1 := by omega
  have hd : ¬ l ∣ l ^ N - 1 := by
    intro h
    have h2 : l ∣ l ^ N := dvd_pow_self l hN.ne'
    have := (Nat.dvd_sub h2 h)
    rw [Nat.sub_sub_self h1.le, Nat.dvd_one] at this
    omega
  haveI : NeZero ((l ^ N - 1 : ℕ) : Om l) := ⟨by exact_mod_cast hm.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ N - 1)
  have hzm : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, hm, hd, hz.pow_eq_one⟩
  set ζ : ↥(MaximalUnramifiedExtension l) := ⟨z, hzm⟩ with hζ
  have hp : IsPrimitiveRoot ζ (l ^ N - 1) :=
    IsPrimitiveRoot.of_map_of_injective (f := (MaximalUnramifiedExtension l).val) hz Subtype.val_injective
  have hit : ∀ i, σ^[i] ζ = ζ ^ l ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply', ih, map_pow, hσ ζ _ hm hd hp.pow_eq_one, ← pow_mul, pow_succ']
  have hz0 : ζ ≠ 0 := hp.ne_zero hm.ne'
  have hpw : ∀ i, ζ ^ l ^ i = ζ ^ (l ^ i - 1) * ζ := by
    intro i
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]
  refine ⟨ζ, by rw [hit, hpw, hp.pow_eq_one, one_mul], fun i hi hiN h => ?_⟩
  rw [hit, hpw, mul_eq_right₀ hz0] at h
  have h3 : 1 < l ^ i := Nat.one_lt_pow hi.ne' hl
  have h4 : l ^ i < l ^ N := Nat.pow_lt_pow_right hl hiN
  exact hp.pow_ne_one_of_pos_of_lt (by omega) (by omega) h

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem invariants_Bcris : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (K : FinExt l) (b : Per.Bcris l),
    (∀ g ∈ GK K, Per.σB g b = b) → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ C.u c = b := by
  intro l _ C K b hb
  obtain ⟨hφ, -, -, hι, hσ, -⟩ := GlobalTheory.T.localPeriodRingsData_unramified_laws l C
  have hcomm := (GlobalTheory.T.periodRings_galoisAction_laws_frobenius_comm l).2.2.2.2.1
  have hfil := (GlobalTheory.T.bdR_filtration_laws l).2.2.2.2.2.2 0
  rcases subsingleton_or_nontrivial (Per.BdR l) with hs | hs
  · exact ⟨0, zero_mem _, hι (Subsingleton.elim _ _)⟩
  let O : Om l →+* Per.BdR l := (algebraMap (Per.BdRp l) (Per.BdR l)).comp C.o
  have hu : ∀ c : ↥(MaximalUnramifiedExtension l), C.ι (C.u c) = O c := C.ι_u
  let S : AddSubgroup (Per.Bcris l) :=
    { carrier := {x | ∀ g ∈ GK K, Per.σB g x = x}
      zero_mem' := fun g _ => map_zero _
      add_mem' := fun {x y} hx hy g hg => by rw [map_add, hx g hg, hy g hg]
      neg_mem' := fun {x} hx g hg => by rw [map_neg, hx g hg] }
  have hS : ∀ x ∈ S, Per.φB l x ∈ S := fun x hx g hg => by rw [← hcomm, hx g hg]
  have hO' : ∀ x ∈ S, ∃ y ∈ K.1, C.ι x = O y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := GlobalTheory.T.bdR_galois_invariants_eq_finExt l C K (C.ι x) (fun g hg => by rw [← hσ, hx g hg])
    exact ⟨y, hy, e.symm⟩
  have hO : ∀ x ∈ S, ∃ y, C.ι x = O y := fun x hx => (hO' x hx).imp fun _ h => h.2
  have fund : ∀ (x : Per.Bcris l) (y : Om l), Per.φB l x = x → C.ι x = O y →
      ∃ c : ℚ_[l], C.u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) c) = x := by
    intro x y h1 h2
    refine GlobalTheory.T.bcris_frobenius_fixed_fil_zero_eq_qp l C x h1 ?_
    rw [h2]
    refine (hfil (C.o y)).2 ?_
    have hone : (1 : Per.BdRp l) ∈ Per.FilP l 0 :=
      (hfil 1).1 (by rw [map_one]; exact (GlobalTheory.T.bdR_filtration_laws l).2.1)
    simpa using Ideal.mul_mem_left _ (C.o y) hone
  have hbS : b ∈ S := hb
  obtain ⟨N, hN, hper⟩ := periodic hι hu hφ S hS hO hbS
  obtain ⟨ζ, h1, h2⟩ := exists_period C.σ C.σ_root hN
  have hit : ∀ i, (Per.φB l)^[i] b ∈ S := by
    intro i
    induction i with
    | zero => rw [Function.iterate_zero_apply]; exact hbS
    | succ i ih => rw [Function.iterate_succ_apply']; exact hS _ ih
  obtain ⟨c, hc⟩ := mem_range hu hφ fund hN hper (fun i => hO _ (hit i)) h1 h2
  obtain ⟨y, hy, e⟩ := hO' b hbS
  refine ⟨c, ?_, hc⟩
  have : (c : Om l) = y := O.injective (by rw [← hu, hc, e])
  rwa [this]

end GlobalTheory.MemLoc.InvCris
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep
open Polynomial

namespace GlobalTheory.CuspRep

theorem exists_multiset_qdet {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (F : Fin n → Fin n → Module.End ℂ M)
    (s : ℂ) (φ : M) (f : M →ₗ[ℂ] ℂ) (hf : f φ = 1) :
    ∃ m : Multiset ℂ, Multiset.card m = n ∧ ∀ u, f (Formalism.REAL.qdet F (u + s) φ) = (m.map (u + ·)).prod := by
  classical
  let Q : Finset (Fin n) → ℂ[X] := fun S => ∏ k ∈ Sᶜ, (X - C ((k : ℂ) - s))
  have hQm : ∀ S, (Q S).Monic := fun S => monic_prod_of_monic _ _ fun k _ => monic_X_sub_C _
  have hQd : ∀ S, (Q S).natDegree = Sᶜ.card := fun S => by
    simp only [Q]
    rw [natDegree_prod_of_monic _ _ fun k _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  let R : ℂ[X] := ∑ S ∈ Finset.univ.erase (∅ : Finset (Fin n)), C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S
  have h0 : (Q ∅).degree = n := by
    rw [degree_eq_natDegree (hQm _).ne_zero, hQd]; simp
  have hR : R.degree < (Q ∅).degree := by
    rw [h0]
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun S hS => ?_)
    refine degree_le_natDegree.trans_lt ?_
    have h1 : (C (f (GlobalTheory.CapelliTop.subdet F S φ)) * Q S).natDegree < n := by
      refine (natDegree_C_mul_le _ _).trans_lt ?_
      rw [hQd, Finset.card_compl, Fintype.card_fin]
      have h2 := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 (Finset.ne_of_mem_erase hS))
      have h3 : S.card ≤ n := by simpa using Finset.card_le_univ S
      omega
    exact_mod_cast h1
  have hm : (Q ∅ + R).Monic := (hQm _).add_of_left hR
  have hd : (Q ∅ + R).natDegree = n := by
    rw [natDegree_eq_of_degree_eq_some ((degree_add_eq_left_of_degree_lt hR).trans h0)]
  have hc : Multiset.card (Q ∅ + R).roots = (Q ∅ + R).natDegree := IsAlgClosed.card_roots_eq_natDegree
  refine ⟨(Q ∅ + R).roots.map Neg.neg, by rw [Multiset.card_map, hc, hd], fun u => ?_⟩
  have e := congrArg (eval u) (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc)
  have e2 : ((Q ∅ + R).roots.map Neg.neg |>.map (u + ·)).prod = eval u (Q ∅ + R) := by
    rw [← e]
    simp [eval_multiset_prod, Multiset.map_map, sub_eq_add_neg]
  have hQe : ∀ S, eval u (Q S) = ∏ k ∈ Sᶜ, (u + s - (k : ℂ)) := fun S => by
    simp only [Q, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_congr rfl fun k _ => by ring
  rw [e2, GlobalTheory.CapelliTop.qdet_expand, ← Finset.add_sum_erase _ _ (Finset.mem_univ (∅ : Finset (Fin n))),
    GlobalTheory.CapelliTop.subdet_empty]
  simp only [R, eval_add, eval_finset_sum, eval_mul, eval_C, hQe, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, map_add, map_sum, map_smul, Module.End.one_apply, hf, smul_eq_mul, mul_one]
  congr 1
  exact Finset.sum_congr rfl fun S _ => mul_comm _ _

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem CuspSub.exists_scalar (π : CuspSub E a) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a)
    (hc : ∀ o : Op E a, Commute z (act o)) : ∃ c : ℂ, ∀ φ ∈ π.V, z φ = c • φ := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set U := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hU
  have hfin : FiniteDimensional ℂ U := (π.cusp φ hφ).1.zfin
  have hle : U ≤ π.V := Submodule.span_le.2 (by
    rintro _ ⟨y, hy, rfl⟩
    exact Zalg_stable (fun X => π.stable (.lie X)) hy φ hφ)
  have hst : ∀ x ∈ U, z x ∈ U := fun x hx => by
    have : U ≤ U.comap z := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact Submodule.subset_span ⟨z * y, mul_mem hz hy, rfl⟩)
    exact this hx
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, one_mem _, rfl⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (z.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1 = c • v.1 := congrArg Subtype.val hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1 ∈ π.V ⊓ z.eigenspace c := ⟨hle v.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext ((Submodule.mem_bot ℂ).1 this)) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

theorem hasInfChar_infChar_of_commute : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o)) → ∀ (π : CG E a) (τ : E →+* ℂ), π.HasInfChar τ (π.infChar τ) := by
  intro E _ _ _ a hc π τ
  suffices h : ∃ m, π.HasInfChar τ m by
    obtain ⟨m, h⟩ := h
    rwa [h.infChar_eq]
  induction π using Quotient.inductionOn with
  | h π =>
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ h0
  obtain ⟨m, hm, h⟩ := exists_multiset_qdet (Eop (a := a) τ) (((a : ℂ) - 1) / 2) φ f hf
  refine ⟨m, hm, fun u ψ hψ => ?_⟩
  obtain ⟨c, h1⟩ := π.exists_scalar (z := cap τ u) (Algebra.subset_adjoin ⟨τ, u, rfl⟩) (hc τ u)
  have h2 : f (cap τ u φ) = _ := h u
  rw [h1 φ hφ, map_smul, hf, smul_eq_mul, mul_one] at h2
  rw [h1 ψ hψ, h2]

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImportsRest
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.SignatureFactor

theorem Jpq_mul_self (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem exists_factor : ∀ (M p q : ℕ) (G : Matrix (Fin M) (Fin M) ℂ), Formalism.UG.HasSignature G p q → p + q = M ∧ (∃ A : Matrix (Fin p ⊕ Fin q) (Fin M) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G) ∧ ∀ A : Matrix (Fin p ⊕ Fin q) (Fin M) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G → ∃ B : Matrix (Fin M) (Fin p ⊕ Fin q) ℂ, A * B = 1 ∧ B * A = 1 := by
  intro M p q G h
  obtain ⟨e, P, hP⟩ := h
  have hP' : P.valᴴ * (reindex e e G) * P.val = Formalism.UG.Jpq p q := hP
  set Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Units.val (P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) with hQ
  have hPQ : P.val * Q = 1 := by
    rw [hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hG' : Qᴴ * Formalism.UG.Jpq p q * Q = reindex e e G := by
    rw [← hP']
    calc Qᴴ * (P.valᴴ * (reindex e e G) * P.val) * Q
        = (P.val * Q)ᴴ * (reindex e e G) * (P.val * Q) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hPQ]; simp
  have hdet : G.det ≠ 0 := by
    intro h0
    have h1 : (Formalism.UG.Jpq p q).det = 0 := by
      rw [← hP', Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, h0]; simp
    have h2 := congrArg Matrix.det (Jpq_mul_self p q)
    rw [Matrix.det_mul, h1] at h2
    simp at h2
  refine ⟨?_, ⟨Q.submatrix id e, ?_⟩, ?_⟩
  · simpa using (Fintype.card_congr e).symm
  · ext i j
    have := congrFun (congrFun hG' (e i)) (e j)
    simpa [Matrix.mul_apply] using this
  · intro A hA
    have hBA : (G⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by
      rw [Matrix.mul_assoc, hA]
      exact Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hdet)
    exact ⟨_, (Matrix.mul_eq_one_comm_of_equiv e).mp hBA, hBA⟩

end GlobalTheory.Mem.SignatureFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatCFullLattice
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem latC_full_lattice : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), ∃ L : Submodule (𝓞 E) (Fin W.rank → E), (L : Set (Fin W.rank → E)) = latC W ∧ L.FG ∧ Submodule.span E (L : Set (Fin W.rank → E)) = ⊤ := by
  intro E _ _ _ W
  refine ⟨W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)), ?_, W.standardTuple_isLattice.fg.map _, ?_⟩
  · ext x
    simp only [latC, SetLike.mem_coe, Submodule.mem_map, Set.mem_ofPred_eq]
    rw [← W.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨_, h, W.frame.equivFun.apply_symm_apply x⟩
  · have h := W.standardTuple_isLattice.span_eq_top
    have : ((W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin W.rank → E)) :
        Set (Fin W.rank → E)) = W.frame.equivFun.toLinearMap '' (W.L0 : Set W.V) := rfl
    rw [this, ← Submodule.map_span, h, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.Mem.Vol
end

