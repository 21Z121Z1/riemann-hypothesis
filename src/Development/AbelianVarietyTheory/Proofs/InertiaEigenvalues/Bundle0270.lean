import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.WachFree

theorem mem_X_smul_of_projective {D M : Type} [CommRing D] [IsDomain D] [AddCommGroup M]
    [Module D⟦X⟧ M] [Module.Projective D⟦X⟧ M] (c : D) (hc : c ≠ 0) (x y : M)
    (h : (C c : D⟦X⟧) • x = (X : D⟦X⟧) • y) : ∃ z : M, x = (X : D⟦X⟧) • z := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective D⟦X⟧ M›
  have hs' : ∀ m, Finsupp.linearCombination D⟦X⟧ id (s m) = m := fun m => LinearMap.congr_fun hs m
  have hd : ∀ m, (X : D⟦X⟧) ∣ s x m := by
    intro m
    have h1 := congrArg (fun w => constantCoeff (s w m)) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, constantCoeff_C,
      constantCoeff_X, zero_mul] at h1
    exact X_dvd_iff.mpr ((mul_eq_zero.mp h1).resolve_left hc)
  have : x ∈ LinearMap.range ((X : D⟦X⟧) • (LinearMap.id : M →ₗ[D⟦X⟧] M)) := by
    rw [← hs' x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    obtain ⟨d, hd⟩ := hd m
    exact ⟨d • m, by rw [hd, mul_smul]; rfl⟩
  obtain ⟨z, hz⟩ := this
  exact ⟨z, by simpa using hz.symm⟩

theorem free_of_regular {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M] (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular M (X : O⟦X⟧))
    (h : ∀ x y : M, (C c : O⟦X⟧) • x = (X : O⟦X⟧) • y → ∃ z : M, x = (X : O⟦X⟧) • z) :
    Module.Free O⟦X⟧ M := by
  haveI : Module.FinitePresentation O⟦X⟧ M := Module.finitePresentation_of_finite _ _
  have hker : Ideal.span {(X : O⟦X⟧)} = RingHom.ker (constantCoeff (R := O)) := by
    ext f
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, X_dvd_iff]
  let e : (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) ≃+* O :=
    (Ideal.quotEquivOfEq hker).trans
      (RingHom.quotientKerEquivOfSurjective (f := constantCoeff (R := O))
        fun a => ⟨C a, by simp⟩)
  haveI : IsDomain (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) := e.toMulEquiv.isDomain
  haveI : IsPrincipalIdealRing (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective
  have hpow : ∀ (k : ℕ) (x y : M), (C (c ^ k) : O⟦X⟧) • x = (X : O⟦X⟧) • y →
      ∃ z : M, x = (X : O⟦X⟧) • z := by
    intro k
    induction k with
    | zero => intro x y hxy; exact ⟨y, by simpa using hxy⟩
    | succ k ih =>
      intro x y hxy
      rw [pow_succ, map_mul, mul_smul] at hxy
      obtain ⟨z, hz⟩ := ih _ _ hxy
      exact h _ _ hz
  have hdvd : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ c ^ k := by
    intro a ha
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    obtain ⟨j, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    have hj : j ≠ 0 := by
      rintro rfl
      exact hc' (by simp)
    refine ⟨k, ?_⟩
    rw [Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd (Dvd.dvd.mul_left (dvd_pow_self _ hj) _) _
  haveI := Module.Finite.of_restrictScalars_finite O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)})
    (QuotSMulTop (X : O⟦X⟧) M)
  haveI : Module.IsTorsionFree (O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}) (QuotSMulTop (X : O⟦X⟧) M) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    by_cases hr : constantCoeff r = 0
    · left
      rw [Ideal.Quotient.eq_zero_iff_mem, hker]
      exact hr
    right
    have h1 : (Submodule.Quotient.mk (r • m) : QuotSMulTop (X : O⟦X⟧) M) = 0 := hrm
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at h1 ⊢
    obtain ⟨y, -, hy⟩ := h1
    obtain ⟨k, b, hb⟩ := hdvd _ hr
    obtain ⟨d, hd⟩ : (X : O⟦X⟧) ∣ C (c ^ k) - C b * r := by
      rw [X_dvd_iff]
      simp [hb, mul_comm]
    obtain ⟨z, hz⟩ := hpow k m (d • m + (C b : O⟦X⟧) • y) (by
      rw [smul_add, smul_comm (X : O⟦X⟧) (C b : O⟦X⟧) y, hy, smul_smul, smul_smul, ← hd, ← add_smul,
        sub_add_cancel])
    exact ⟨z, trivial, hz.symm⟩
  refine (Module.free_quotSMulTop_iff_free O⟦X⟧ M ?_ hX).mp inferInstance
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, isUnit_iff_constantCoeff]
  simp

theorem finrank_fibre {ι R N : Type} [DecidableEq ι] [CommRing R] [IsLocalRing R] [AddCommGroup N]
    [Module (ι → R) N] [Module.Finite (ι → R) N] [Module.Flat (ι → R) N] (i : ι) :
    ∃ r : ℕ, ∀ (S : Type) [CommRing S] [Nontrivial S] [Algebra (ι → R) S],
      algebraMap (ι → R) S (Pi.single i 1) = 1 → Module.finrank S (S ⊗[ι → R] N) = r := by
  letI : Algebra (ι → R) R := (Pi.evalRingHom (fun _ : ι => R) i).toAlgebra
  haveI : Module.Free R (R ⊗[ι → R] N) := Module.free_of_flat_of_isLocalRing
  refine ⟨Module.finrank R (R ⊗[ι → R] N), fun S _ _ _ hS => ?_⟩
  letI : Algebra R S := ((algebraMap (ι → R) S).comp (Pi.constRingHom ι R)).toAlgebra
  haveI : IsScalarTower (ι → R) R S := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap (ι → R) S a = algebraMap (ι → R) S (fun _ => a i)
    have : a * Pi.single i 1 = (fun _ => a i) * Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    have h2 := congrArg (algebraMap (ι → R) S) this
    rwa [map_mul, map_mul, hS, mul_one, mul_one] at h2
  rw [← (AlgebraTensorModule.cancelBaseChange (ι → R) R S S N).finrank_eq,
    Module.finrank_baseChange]

theorem basis_of_baseChange {ι R N E D : Type} [Finite ι] [CommRing R] [IsLocalRing R]
    [AddCommGroup N] [Module (ι → R) N] [Module.Finite (ι → R) N] [Module R N]
    [IsScalarTower R (ι → R) N] [Module.Flat R N] [CommRing E] [Algebra (ι → R) E]
    (hE : Function.Injective (algebraMap (ι → R) E)) [AddCommGroup D] [Module E D]
    [Module (ι → R) D] [IsScalarTower (ι → R) E D] [Module.Free E D] (f : N →ₗ[ι → R] D)
    (hf : IsBaseChange E f) : Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → R) N) := by
  classical
  haveI := Fintype.ofFinite ι
  haveI : Module.Flat (ι → R) N := Algebra.FormallyUnramified.flat_of_restrictScalars R (ι → R) N
  haveI : Finite (MaximalSpectrum (ι → R)) := by
    haveI := (Algebra.QuasiFinite.finite_primesOver (S := ι → R)
      (IsLocalRing.maximalIdeal R)).to_subtype
    refine Finite.of_injective (fun n : MaximalSpectrum (ι → R) =>
      (⟨n.asIdeal, n.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
        (@Ideal.isMaximal_comap_of_isIntegral_of_isMaximal R _ _ _ _ _ n.asIdeal n.isMaximal)).symm⟩⟩ :
        (IsLocalRing.maximalIdeal R).primesOver (ι → R))) fun a b hab => ?_
    exact MaximalSpectrum.ext (congrArg Subtype.val hab)
  refine Module.nonempty_basis_of_flat_of_finrank_eq _ _ _ fun P => ?_
  haveI := P.isMaximal
  have hee : ∀ i : ι, (Pi.single i 1 : ι → R) * (Pi.single i 1 - 1) = 0 := by
    intro i
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  obtain ⟨i, hi⟩ : ∃ i : ι, (Pi.single i 1 : ι → R) ∉ P.asIdeal := by
    by_contra hcon
    push Not at hcon
    apply P.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one, ← Finset.univ_sum_single (1 : ι → R)]
    exact Ideal.sum_mem _ fun j _ => hcon j
  have hi' : (Pi.single i 1 - 1 : ι → R) ∈ P.asIdeal :=
    (P.isMaximal.isPrime.mem_or_mem (by rw [hee i]; exact Ideal.zero_mem _)).resolve_left hi
  obtain ⟨r, hr⟩ := finrank_fibre (R := R) (N := N) i
  rw [hr ((ι → R) ⧸ P.asIdeal) (by
    rw [Ideal.Quotient.algebraMap_eq, ← map_one (Ideal.Quotient.mk P.asIdeal), Ideal.Quotient.eq]
    exact hi')]
  let I : Ideal E := Ideal.span {algebraMap (ι → R) E (Pi.single i 1 - 1)}
  haveI : Nontrivial (E ⧸ I) := by
    rw [Ideal.Quotient.nontrivial_iff]
    intro hI
    rw [Ideal.span_singleton_eq_top] at hI
    apply hi
    have : algebraMap (ι → R) E (Pi.single i 1) = 0 := by
      rw [← hI.mul_left_eq_zero, ← map_mul, hee, map_zero]
    rw [hE (this.trans (map_zero _).symm)]
    exact Ideal.zero_mem _
  haveI : Nontrivial E := (algebraMap E (E ⧸ I)).domain_nontrivial
  rw [← hr (E ⧸ I) (by
    rw [IsScalarTower.algebraMap_apply (ι → R) E (E ⧸ I), Ideal.Quotient.algebraMap_eq,
      ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact Ideal.subset_span (by simp)),
    ← (AlgebraTensorModule.cancelBaseChange (ι → R) E (E ⧸ I) (E ⧸ I) N).finrank_eq,
    (AlgebraTensorModule.congr (LinearEquiv.refl (E ⧸ I) (E ⧸ I)) hf.equiv).finrank_eq,
    Module.finrank_baseChange]

theorem basis_of_regular {ι O N E D : Type} [Finite ι] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [AddCommGroup N] [Module (ι → O⟦X⟧) N] [Module.Finite (ι → O⟦X⟧) N]
    [CommRing E] [Algebra (ι → O⟦X⟧) E]
    (hE : Function.Injective (algebraMap (ι → O⟦X⟧) E)) [AddCommGroup D] [Module E D]
    [Module (ι → O⟦X⟧) D] [IsScalarTower (ι → O⟦X⟧) E D] [Module.Free E D]
    (f : N →ₗ[ι → O⟦X⟧] D) (hf : IsBaseChange E f) (c : O) (hc : c ≠ 0) (hc' : ¬ IsUnit c)
    (hX : IsSMulRegular N (fun _ => X : ι → O⟦X⟧))
    (h : ∀ x y : N, (fun _ => C c : ι → O⟦X⟧) • x = (fun _ => X : ι → O⟦X⟧) • y →
      ∃ z : N, x = (fun _ => X : ι → O⟦X⟧) • z) :
    Nonempty (Module.Basis (Fin (Module.finrank E D)) (ι → O⟦X⟧) N) := by
  letI : Module O⟦X⟧ N := Module.compHom _ (algebraMap O⟦X⟧ (ι → O⟦X⟧))
  haveI : IsScalarTower O⟦X⟧ (ι → O⟦X⟧) N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite O⟦X⟧ N := Module.Finite.trans (ι → O⟦X⟧) _
  haveI : Module.Free O⟦X⟧ N := free_of_regular c hc hc' hX h
  exact basis_of_baseChange hE f hf

set_option maxHeartbeats 1600000 in

theorem wach_free {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys (P.PD K) T.ρ) :
    Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T))
      (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K s LL h).N T)) := by
  obtain ⟨_, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hproj := H.W_proj K s LL h T
  generalize H.W K s LL h = W at hproj ⊢
  obtain ⟨hfree, hrk⟩ := W.DD_free T
  rw [← hrk]
  haveI : Module.Finite (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(W.N T) :=
    Module.Finite.iff_fg.mpr (W.N_fg T)
  have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
    simp [(Fact.out : l.Prime).ne_zero] at this
  refine basis_of_regular (ι := ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (O := ↥(OL LL))
    (N := ↥(W.N T)) (E := W.EE) (D := W.DD T) W.EE_inj (W.N T).subtype (W.N_base T hT)
    ((l : ℕ) : ↥(OL LL)) hl0 hl ?_ ?_
  · intro x y hxy
    have h1 : (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (x : W.DD T) =
        (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (y : W.DD T) :=
      congrArg Subtype.val hxy
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE letπ (y : W.DD T)] at h1
    exact Subtype.ext (W.EE_π.smul_left_cancel.mp h1)
  · intro x y hxy
    have e1 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) =
        fun _ => C ((l : ℕ) : ↥(OL LL)) := by
      funext i
      simp
    have e2 : zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X = fun _ => X := by
      funext i
      simp [zlA]
    obtain ⟨z, hz⟩ := @mem_X_smul_of_projective ℤ_[l] ↥(W.N T) _ _ _
      (Module.compHom _ (zlA LL (Module.finrank ℚ_[l] ↥(K0 K)))) hproj ((l : ℕ) : ℤ_[l])
      (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) x y (by
        change zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) (C ((l : ℕ) : ℤ_[l])) • x =
          zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • y
        rw [e1, e2]
        exact hxy)
    refine ⟨z, ?_⟩
    change x = zlA LL (Module.finrank ℚ_[l] ↥(K0 K)) X • z at hz
    rw [e2] at hz
    exact hz

end GlobalTheory.WachFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatLogFloorExpLe
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

open NumberField IsDedekindDomain Module in
private lemma natLog_mul_log_two_le_log_of_le {l m : ℕ} {C : ℝ} (hl : 2 ≤ l) (hC : 1 ≤ C)
    (hm : (m : ℝ) ≤ C) : (Nat.log l m : ℝ) * Real.log 2 ≤ Real.log C := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · simpa using Real.log_nonneg hC
  have h1 : Nat.log l m ≤ Nat.log 2 m := Nat.log_anti_left (by norm_num) hl
  have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 hpos.ne'
  have h3 : (2 : ℝ) ^ Nat.log l m ≤ C :=
    calc (2 : ℝ) ^ Nat.log l m ≤ 2 ^ Nat.log 2 m := pow_le_pow_right₀ (by norm_num) h1
      _ ≤ m := by exact_mod_cast h2
      _ ≤ C := hm
  have h4 := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at h4

open NumberField IsDedekindDomain Module in
private lemma natLog_le_add_two_mul_of_le_two_pow_mul_exp {l m k : ℕ} {L : ℝ} (hl : 2 ≤ l) (hL : 0 ≤ L)
    (hm : (m : ℝ) ≤ 2 ^ k * Real.exp L) : (Nat.log l m : ℝ) ≤ k + 2 * L := by
  have hC : (1 : ℝ) ≤ 2 ^ k * Real.exp L :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_exp hL)
  have h := natLog_mul_log_two_le_log_of_le hl hC hm
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  have hlog : (1 : ℝ) / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_contra hcon
  push_neg at hcon
  have : ((Nat.log l m : ℝ) - k) * Real.log 2 ≤ L := by linarith
  nlinarith

open NumberField IsDedekindDomain Module in

theorem _root_.GlobalTheory.HubLoc.cBnum_le_thirty : ∀ (l t N : ℕ) (L : ℝ), 2 ≤ l → 1 ≤ t → 1 ≤ N →
    1 ≤ L → (_root_.GlobalTheory.HubLoc.cBnum l ⌊2 * Real.exp L⌋₊ t N : ℝ) ≤ 30 * t * N * L := by
  intro l t N L hl ht hN hL
  have hfl : ((⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 * Real.exp L :=
    Nat.floor_le (by positivity)
  have hm : ((2 * ⌊2 * Real.exp L⌋₊ : ℕ) : ℝ) ≤ 2 ^ 2 * Real.exp L := by
    push_cast
    nlinarith
  have hK := natLog_le_add_two_mul_of_le_two_pow_mul_exp hl (by linarith) hm
  unfold _root_.GlobalTheory.HubLoc.cBnum
  push_cast at hK ⊢
  set K : ℝ := (Nat.log l (2 * ⌊2 * Real.exp L⌋₊) : ℝ)
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have htN : (1 : ℝ) ≤ t * N := one_le_mul_of_one_le_of_one_le ht' hN'
  have htNL : (1 : ℝ) ≤ t * N * L := one_le_mul_of_one_le_of_one_le htN hL
  have hL1 : L ≤ t * N * L := by nlinarith
  have ht1 : (t : ℝ) ≤ t * N * L := by nlinarith
  have hA : (t : ℝ) * N * K ≤ t * N * (2 + 2 * L) := by
    apply mul_le_mul_of_nonneg_left hK; positivity
  nlinarith

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtRho1OfMemIdealPowerStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_lt_rho1_of_mem_ideal_power : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (j n f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (ζ : OC l), 1 ≤ j → IsPrimitiveRoot (ζ : PadicComplex l) (l ^ j) → φ letπ = (ζ - 1) ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ∀ a ∈ Ideal.span {((l : ℕ) : LetA ↥(OL LL) n) ^ 2} ⊔ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) n), letπ}) ^ (l ^ j), ∀ k, ‖kap o (φ a) k‖ < rho1 l := by
  first | exact @GlobalTheory.Cyc.Decomp.norm_kap_lt_rho1_of_mem_sq_sup_pow | exact GlobalTheory.Cyc.Decomp.norm_kap_lt_rho1_of_mem_sq_sup_pow | (intros; apply GlobalTheory.Cyc.Decomp.norm_kap_lt_rho1_of_mem_sq_sup_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicativeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ocTensorCoeffActionMatrix_multiplicative : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), IsMat K LL T M A → (∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a) ∧ A 1 = 1 ∧ (∀ a b, A (a * b) = A a * A b) ∧ ∀ x y : OCO LL, lam o A (x * y) = lam o A x * lam o A y := by
  first | exact @GlobalTheory.Cyc.Decomp.lam_mul_of_isMat | exact GlobalTheory.Cyc.Decomp.lam_mul_of_isMat | (intros; apply GlobalTheory.Cyc.Decomp.lam_mul_of_isMat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffBasisCoordsMemCyclotomicLevelOfPoweStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ocTensorCoeffBasisCoords_mem_cyclotomicLevel_of_powerSeries : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (m n f : ℕ) [NeZero n] (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (c : OC l), (∀ a : ↥(OL LL), φ (algebraMap ↥(OL LL) (LetA ↥(OL LL) n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a) → φ letπ = c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL)) → ‖(c : PadicComplex l)‖ < 1 → (c : PadicComplex l) ∈ inC (Ks K m) → (∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m)) → ∀ a k, kap o (φ a) k ∈ intC (Ks K m) := by
  first | exact @GlobalTheory.Cyc.Decomp.Coord.coord | exact GlobalTheory.Cyc.Decomp.Coord.coord | (intros; apply GlobalTheory.Cyc.Decomp.Coord.coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc.PhiFree

open PowerSeries

theorem bijective_of_congr {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (a : R) [IsPrecomplete (Ideal.span {a}) M] [IsHausdorff (Ideal.span {a}) M]
    [IsHausdorff (Ideal.span {a}) N] (ha : ∀ y : N, a • y = 0 → y = 0) (S T : M →ₗ[R] N)
    (hS : Function.Bijective S) (h : ∀ z, T z - S z ∈ (Ideal.span {a} • ⊤ : Submodule R N)) :
    Function.Bijective T := by
  constructor
  · rw [injective_iff_map_eq_zero]
    have step : ∀ z, T z = 0 → ∃ z', T z' = 0 ∧ z = a • z' := fun z hz => by
      have h1 := h z
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
      obtain ⟨u, -, hu⟩ := h1
      obtain ⟨v, rfl⟩ := hS.2 u
      have h2 : z = a • (-v) := hS.1 (by rw [map_smul, map_neg, smul_neg, hu, hz]; simp)
      exact ⟨-v, ha _ (by rw [← map_smul, ← h2, hz]), h2⟩
    have all : ∀ (n : ℕ) z, T z = 0 → ∃ z', z = a ^ n • z' := fun n => by
      induction n with
      | zero => exact fun z _ => ⟨z, by simp⟩
      | succ n ih =>
        intro z hz
        obtain ⟨z', h1, rfl⟩ := step z hz
        obtain ⟨w, rfl⟩ := ih z' h1
        exact ⟨w, by rw [smul_smul, pow_succ']⟩
    intro z hz
    refine IsHausdorff.haus' (I := Ideal.span {a}) z fun n => ?_
    obtain ⟨w, rfl⟩ := all n z hz
    rw [SModEq.zero]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self a) n) trivial
  · refine surjective_of_mkQ_comp_surjective (I := Ideal.span {a}) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    obtain ⟨z, rfl⟩ := hS.2 G
    exact ⟨z, (Submodule.Quotient.eq _).2 (h z)⟩

theorem bijective_one_add {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : B) (n : ℕ)
    (h : Function.Bijective fun z : Fin n → A => ∑ j : Fin n, x ^ (j : ℕ) * f (z j)) :
    Function.Bijective fun z : Fin n → A => ∑ j : Fin n, (1 + x) ^ (j : ℕ) * f (z j) := by
  have key : ∀ (t : B) (p : Polynomial.degreeLT A n),
      ∑ j : Fin n, t ^ (j : ℕ) * f (Polynomial.degreeLTEquiv A n p j) = p.1.eval₂ f t := fun t p => by
    rw [Polynomial.eval₂_eq_sum, ← Polynomial.sum_fin _ (by simp) (Polynomial.mem_degreeLT.1 p.2)]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let e : (Fin n → A) ≃ₗ[A] (Fin n → A) := (Polynomial.degreeLTEquiv A n).symm.trans
    ((Polynomial.taylorLinearEquiv 1 n).trans (Polynomial.degreeLTEquiv A n))
  convert h.comp e.bijective using 1
  funext z
  obtain ⟨p, rfl⟩ := (Polynomial.degreeLTEquiv A n).surjective z
  simp only [e, Function.comp, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, key]
  change _ = (Polynomial.taylor 1 p.1).eval₂ f x
  rw [Polynomial.taylor_apply, Polynomial.eval₂_comp]
  simp [add_comm]

theorem coeff_sum_expand {R : Type} [CommRing R] (n : ℕ) (hn : n ≠ 0) (z : Fin n → R⟦X⟧) (i : Fin n)
    (m : ℕ) : coeff (n * m + i) (∑ j : Fin n, X ^ (j : ℕ) * expand n hn (z j)) = coeff m (z i) := by
  rw [map_sum, Finset.sum_eq_single i]
  · rw [coeff_X_pow_mul, coeff_expand_mul]
  · intro j _ hj
    rw [coeff_X_pow_mul']
    split_ifs with h
    · refine coeff_expand_of_not_dvd _ _ _ fun hd => hj (Fin.ext ?_)
      have h1 : (j : ℕ) ≡ n * m + i [MOD n] := (Nat.modEq_iff_dvd' h).2 hd
      have h2 : n * m + i ≡ i [MOD n] := by simp [Nat.ModEq]
      exact (h1.trans h2).eq_of_lt_of_lt j.2 i.2
    · rfl
  · simp

theorem bijective_expand {R : Type} [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective fun z : Fin n → R⟦X⟧ => ∑ j : Fin n, X ^ (j : ℕ) * expand n hn (z j) := by
  constructor
  · intro z z' h
    funext i
    ext m
    rw [← coeff_sum_expand n hn z, ← coeff_sum_expand n hn z']
    exact congrArg _ h
  · intro y
    refine ⟨fun i => PowerSeries.mk fun m => coeff (n * m + i) y, ?_⟩
    ext k
    have h := coeff_sum_expand n hn (fun i => PowerSeries.mk fun m => coeff (n * m + i) y)
      ⟨k % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩ (k / n)
    simpa [Nat.div_add_mod] using h

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem coeff_phi_sub_expand_mem (J : Ideal O) (hl : (l : O) ∈ J) (z : O⟦X⟧) (k : ℕ) :
    coeff k (phi l O z - expand l (Fact.out : l.Prime).ne_zero z) ∈ J := by
  have h : (PowerSeries.map (Ideal.Quotient.mk J)).comp (phi l O : O⟦X⟧ →+* O⟦X⟧) =
      (PowerSeries.map (Ideal.Quotient.mk J)).comp
        (expand l (Fact.out : l.Prime).ne_zero : O⟦X⟧ →ₐ[O] O⟦X⟧) := by
    have hX : PowerSeries.map (Ideal.Quotient.mk J) (phi l O X) = X ^ l := by
      obtain ⟨r, hr⟩ := Series.phi_X_mod l O
      have h0 : ((l : ℕ) : (O ⧸ J)⟦X⟧) = 0 := by
        rw [← map_natCast (C (R := O ⧸ J)), ← map_natCast (Ideal.Quotient.mk J),
          Ideal.Quotient.eq_zero_iff_mem.2 hl, map_zero]
      rw [hr]
      simp [h0]
    refine Fon.ps_hom_ext (fun r => ?_) ?_ ?_
    · exact congrArg (PowerSeries.map (Ideal.Quotient.mk J))
        (((phi l O).commutes r).trans ((expand l (Fact.out : l.Prime).ne_zero).commutes r).symm)
    · exact hX.trans (by simp)
    · refine Fon.eq_zero_of_pow_dvd ?_
      change constantCoeff (PowerSeries.map (Ideal.Quotient.mk J) (phi l O X)) = 0
      rw [hX]
      simp [(Fact.out : l.Prime).ne_zero]
  have h1 := congrArg (coeff k) (RingHom.congr_fun h z)
  rw [map_sub, ← Ideal.Quotient.eq]
  simpa only [RingHom.comp_apply, coeff_map, RingHom.coe_coe] using h1

end GlobalTheory.Cyc.PhiFree

namespace GlobalTheory.Cyc

open PhiFree CompleteBaseChange

theorem phi_free : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ y : PowerSeries O, ∃! z : Fin l → PowerSeries O, y = ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * phi l O (z j) := by
  intro l _ O _ _ _ _ _ _ hl y
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := ha.maximalIdeal_eq
  have hla : (l : O) ∈ Ideal.span {a} := hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hl
  have : IsAdicComplete (Ideal.span {a}) O := hm ▸ ‹_›
  have hJ : (Ideal.span {a}).FG := Submodule.fg_span_singleton a
  have : IsPrecomplete (Ideal.span {a}) (PowerSeries O) := isPrecomplete_pi (Unit →₀ ℕ) hJ
  have : IsHausdorff (Ideal.span {a}) (PowerSeries O) := isHausdorff_pi (Unit →₀ ℕ) hJ
  have : IsPrecomplete (Ideal.span {a}) (Fin l → PowerSeries O) := isPrecomplete_pi _ hJ
  have : IsHausdorff (Ideal.span {a}) (Fin l → PowerSeries O) := isHausdorff_pi _ hJ
  let F : (PowerSeries O →ₐ[O] PowerSeries O) → (Fin l → PowerSeries O) →ₗ[O] PowerSeries O := fun f =>
    { toFun := fun z => ∑ j : Fin l, PowerSeries.X ^ (j : ℕ) * f (z j)
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum] }
  have hT : Function.Bijective (F (phi l O)) := by
    refine bijective_of_congr a (fun y hy => ?_) (F (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)) _
      (bijective_expand l _) fun z => ?_
    · ext k
      have h1 := congrArg (PowerSeries.coeff k) hy
      rw [map_smul, map_zero, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left ha.ne_zero
    · change (∑ j : Fin l, _) - (∑ j : Fin l, _) ∈ _
      rw [← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h1 : phi l O (z j) - PowerSeries.expand l (Fact.out : l.Prime).ne_zero (z j) ∈
          (Ideal.span {a} • ⊤ : Submodule O (PowerSeries O)) :=
        (mem_smul_top_pi (ι := Unit →₀ ℕ) hJ _).2 fun d => by
          have h2 := coeff_phi_sub_expand_mem l O _ hla (z j) (d ())
          rw [PowerSeries.coeff, Finsupp.unique_single d |>.symm] at h2
          rw [smul_eq_mul, Ideal.mul_top]
          exact h2
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1 ⊢
      obtain ⟨u, -, hu⟩ := h1
      exact ⟨PowerSeries.X ^ (j : ℕ) * u, trivial, by rw [← mul_sub, ← hu, mul_smul_comm]⟩
  have h := (bijective_one_add (phi l O : PowerSeries O →+* PowerSeries O) PowerSeries.X l hT).existsUnique y
  simpa only [eq_comm (a := y), RingHom.coe_coe] using h

end GlobalTheory.Cyc
end
end

