import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBanachModelTensorAcris
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusFrameOfPeriodMatrix
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0352
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfProperties
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfEPow

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evE_ne_zero : bk.ev bk.E ≠ 0 := fun h =>
  bk.E_ne_zero (bk.ev_injective (by rw [h, map_zero]))

theorem theta_eq_zero_iff (x : Ainf l) : Per.θ l x = 0 ↔ bk.ev bk.E ∣ x := by
  rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]

theorem theta_of_natPow_mul (n : ℕ) (c : Ainf l) (h : Per.θ l ((l : Ainf l) ^ n * c) = 0) :
    Per.θ l c = 0 := by
  rw [map_mul, map_pow, map_natCast] at h
  have hne : ((l : Per.OC l)) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.out.ne_zero)
  exact (mul_eq_zero.mp h).resolve_left hne

theorem dvd_of_dvd_natPow_mul (n : ℕ) (c : Ainf l) (h : bk.ev bk.E ∣ (l : Ainf l) ^ n * c) :
    bk.ev bk.E ∣ c := by
  rw [← theta_eq_zero_iff] at h ⊢
  exact theta_of_natPow_mul n c h

theorem pow_dvd_of_pow_dvd_l_mul (m : ℕ) : ∀ a : Ainf l,
    bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have h1 : bk.ev bk.E ∣ (l : Ainf l) ^ 1 * a := by
      rw [pow_one]; exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    obtain ⟨a', rfl⟩ := dvd_of_dvd_natPow_mul bk 1 a h1
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem pow_dvd_of_pow_dvd_lpow_mul (m k : ℕ) (a : Ainf l)
    (h : bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * a) : bk.ev bk.E ^ m ∣ a := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply pow_dvd_of_pow_dvd_l_mul bk m
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem pow_dvd_of_ev_pow_dvd (m : ℕ) : ∀ s : bk.S,
    bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s := by
  induction m with
  | zero => intro s _; simp
  | succ m ih =>
    intro s h
    have h1 : bk.ev bk.E ∣ bk.ev s := dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    have hE : bk.E ∣ s := by
      set r := bk.str.symm (Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s) with hr
      have hmk : Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s = bk.str r := by
        rw [hr, RingEquiv.apply_symm_apply]
      have hθ := bk.θ_ev r s hmk
      rw [(theta_eq_zero_iff bk _).mpr h1] at hθ
      have hr0 : r = 0 := intToOC_injective K (by rw [← hθ, map_zero])
      rw [hr0, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmk
      exact hmk
    obtain ⟨s', rfl⟩ := hE
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', map_mul] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem theta_eq_zero_of_forall (y : Per.OC l) (h : ∀ n : ℕ, ∃ z : Per.OC l, y = (l : Per.OC l) ^ n * z) :
    y = 0 := by
  apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(l : Per.OC l)})) y
  intro n
  obtain ⟨z, hz⟩ := h n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨z, hz⟩

theorem pow_dvd_of_forall_approx (m : ℕ) : ∀ a : Ainf l,
    (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) →
      bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have hθ : Per.θ l a = 0 := by
      apply theta_eq_zero_of_forall
      intro n
      obtain ⟨b, c, hbc⟩ := h n
      refine ⟨Per.θ l c, ?_⟩
      have hE : Per.θ l (bk.ev bk.E) = 0 := (theta_eq_zero_iff bk _).mpr dvd_rfl
      rw [hbc, map_add, map_mul, map_mul, map_pow, map_pow, hE, map_natCast]
      simp
    obtain ⟨a', rfl⟩ := (theta_eq_zero_iff bk a).mp hθ
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    intro n
    obtain ⟨b, c, hbc⟩ := h n
    have hc : bk.ev bk.E ∣ (l : Ainf l) ^ n * c :=
      ⟨a' - bk.ev bk.E ^ m * b, by rw [mul_sub, ← mul_assoc, ← pow_succ', hbc]; ring⟩
    obtain ⟨c', rfl⟩ := dvd_of_dvd_natPow_mul bk n c hc
    refine ⟨b, c', ?_⟩
    apply mul_left_cancel₀ (evE_ne_zero bk)
    rw [hbc]; ring

theorem ker_localizedTheta_eq_span_eisenstein (bk : BK K) : Per.kerP l = Ideal.span {(algebraMap (Per.Ainf l) (Per.AinfP l)) (bk.ev bk.E)} :=
  GlobalTheory.MemLoc.ker_localizedTheta_eq_span_of_dvd l _ (fun a => theta_eq_zero_iff bk a)

theorem mem_filtration_iff_eisenstein_pow_dvd (m : ℕ) (a : Ainf l) :
    aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a := by
  have key : aDp l a ∈ Per.FilP l m ↔
      (algebraMap (Per.Ainf l) (Per.AinfP l)) a ∈ Per.kerP l ^ m := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    unfold aDp
    rw [RingHom.comp_apply, GlobalTheory.RingIface.ev_alg]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [key, ker_localizedTheta_eq_span_eisenstein bk, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
  constructor
  · rintro ⟨y, hy⟩
    haveI : IsLocalization (Submonoid.powers (l : Per.Ainf l)) (Per.AinfP l) :=
      inferInstance
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) y
    obtain ⟨k, hk⟩ := s.2
    simp only at hs hk
    rw [← hk] at hs
    have hl0 : (l : Per.Ainf l) ≠ 0 := fun h => by
      have h' := congrArg (Per.θ l) h
      rw [map_natCast, map_zero] at h'
      exact (Nat.cast_ne_zero.mpr hl.out.ne_zero) h'
    have hinj : Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) :=
      IsLocalization.injective (Per.AinfP l) (powers_le_nonZeroDivisors_of_noZeroDivisors hl0)
    have heq : (l : Ainf l) ^ k * a = bk.ev bk.E ^ m * b := by
      apply hinj
      rw [map_mul, map_mul, ← hs, hy]
      ring
    exact pow_dvd_of_pow_dvd_lpow_mul bk m k a ⟨b, heq⟩
  · exact fun h => map_dvd _ h

theorem ePow_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), (∀ a : Ainf l, bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a) ∧ (∀ s : bk.S, bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s) ∧ (∀ a : Ainf l, aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a) ∧ ∀ a : Ainf l, (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) → bk.ev bk.E ^ m ∣ a := by
  intro l _ K bk m
  exact ⟨pow_dvd_of_pow_dvd_l_mul bk m, pow_dvd_of_ev_pow_dvd bk m, mem_filtration_iff_eisenstein_pow_dvd bk m,
    pow_dvd_of_forall_approx bk m⟩

end GlobalTheory.AinfEPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMinpolyUniformizerWittTotallyRamified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.TotRam

open IsLocalRing

variable {R O : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R O]

theorem isUnit_of_not_dvd_uniformiser {S : Type} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    {ϖ c : S} (hϖ : Irreducible ϖ) (h : ¬ ϖ ∣ c) : IsUnit c := by
  by_contra hc
  have hm : c ∈ maximalIdeal S := (mem_maximalIdeal c).2 (mem_nonunits_iff.2 hc)
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  exact h hm

theorem not_isUnit_algebraMap [Module.Finite R O] {ϖ : R} (hϖ : Irreducible ϖ) :
    ¬ IsUnit (algebraMap R O ϖ) := by
  intro hu
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hmem : ϖ ∈ maximalIdeal R := by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
  have hle : (⊤ : Submodule R O) ≤ maximalIdeal R • ⊤ := by
    intro x _
    have hx : x = ϖ • (v * x) := by rw [Algebra.smul_def, ← mul_assoc, hv, one_mul]
    rw [hx]
    exact Submodule.smul_mem_smul hmem trivial
  exact top_ne_bot (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
    (Module.finite_def.mp ‹_›) hle (maximalIdeal_le_jacobson _))

theorem dvd_coeff_of_dvd_sum {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ) {e : ℕ}
    (he : π ^ e ∣ algebraMap R O ϖ) (c : ℕ → R) {m j : ℕ} (hj : j < e) (hjm : j < m)
    (hlow : ∀ i < j, ϖ ∣ c i) (hs : π ^ (j + 1) ∣ ∑ i ∈ Finset.range m, c i • π ^ i) : ϖ ∣ c j := by
  by_contra hc
  have hu : IsUnit (algebraMap R O (c j)) := (isUnit_of_not_dvd_uniformiser hϖ hc).map _
  have hrest : π ^ (j + 1) ∣ ∑ i ∈ (Finset.range m).erase j, c i • π ^ i := by
    refine Finset.dvd_sum fun i hi => ?_
    rw [Algebra.smul_def]
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hi) with h | h
    · obtain ⟨d, hd⟩ := hlow i h
      refine Dvd.dvd.mul_right ((pow_dvd_pow π (by omega : j + 1 ≤ e)).trans (he.trans ?_)) _
      rw [hd, map_mul]; exact dvd_mul_right _ _
    · exact Dvd.dvd.mul_left (pow_dvd_pow π (by omega : j + 1 ≤ i)) _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hjm)] at hs
  have h1 : π ^ j * π ∣ π ^ j * algebraMap R O (c j) := by
    rw [← pow_succ, mul_comm, ← Algebra.smul_def]; exact (dvd_add_left hrest).1 hs
  have h2 := (mul_dvd_mul_iff_left (pow_ne_zero j hπ.ne_zero)).1 h1
  exact hπ.not_isUnit (isUnit_of_dvd_unit h2 hu)

theorem dvd_coeff_all {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ) {e : ℕ}
    (he : π ^ e ∣ algebraMap R O ϖ) (c : ℕ → R) {m : ℕ}
    (hs : π ^ e ∣ ∑ i ∈ Finset.range m, c i • π ^ i) : ∀ j < e, j < m → ϖ ∣ c j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hjm
    exact dvd_coeff_of_dvd_sum hπ hϖ he c hj hjm (fun i hi => ih i hi (by omega) (by omega))
      ((pow_dvd_pow π (by omega)).trans hs)

theorem coeff_eq_zero_of_sum {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (hinj : Function.Injective (algebraMap R O)) {e : ℕ} (he : π ^ e ∣ algebraMap R O ϖ) :
    ∀ c : ℕ → R, ∑ i ∈ Finset.range e, c i • π ^ i = 0 → ∀ i < e, c i = 0 := by
  have hϖ0 : algebraMap R O ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have key : ∀ n : ℕ, ∀ c : ℕ → R, ∑ i ∈ Finset.range e, c i • π ^ i = 0 → ∀ i < e, ϖ ^ n ∣ c i := by
    intro n
    induction n with
    | zero => intro c _ i _; simp
    | succ n ih =>
      intro c hc i hi
      have hd := dvd_coeff_all hπ hϖ he c (m := e) (by rw [hc]; exact dvd_zero _)
      choose! d hd' using fun k (h : k < e) => hd k h h
      have h0 : algebraMap R O ϖ * ∑ k ∈ Finset.range e, d k • π ^ k = 0 := by
        rw [Finset.mul_sum, ← hc]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [hd' k (Finset.mem_range.1 hk), Algebra.smul_def, Algebra.smul_def, map_mul]; ring
      have h1 := (mul_eq_zero.1 h0).resolve_left hϖ0
      rw [hd' i hi, pow_succ']
      exact mul_dvd_mul_left ϖ (ih d h1 i hi)
  intro c hc i hi
  by_contra h0
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ
  have h1 : ϖ ^ n * ϖ ∣ ϖ ^ n * 1 := by
    rw [← pow_succ, mul_one, ← hu]; exact (key (n + 1) c hc i hi).mul_right _
  exact hϖ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero n hϖ.ne_zero)).1 h1))

theorem exists_degreeLT [Module.Finite R O] {ϖ : R} {π : O} (hπ : Irreducible π) (hϖ : Irreducible ϖ) {e : ℕ}
    (he : Associated (algebraMap R O ϖ) (π ^ e))
    (hres : ∀ x : O, ∃ c : R, ¬ IsUnit (x - algebraMap R O c)) :
    ∀ x : O, ∃ f ∈ Polynomial.degreeLT R e, Polynomial.aeval π f = x := by
  have step : ∀ k (x : O), ∃ f ∈ Polynomial.degreeLT R k, π ^ k ∣ x - Polynomial.aeval π f := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, Submodule.zero_mem _, by rw [pow_zero]; exact one_dvd _⟩
    | succ k ih =>
      intro x
      obtain ⟨f, hf, z, hz⟩ := ih x
      obtain ⟨c, hc⟩ := hres z
      have hm : z - algebraMap R O c ∈ maximalIdeal O := (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hc)
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      obtain ⟨t, ht⟩ := hm
      refine ⟨f + Polynomial.C c * Polynomial.X ^ k, ?_, t, ?_⟩
      · rw [Polynomial.mem_degreeLT] at hf ⊢
        have hk : ((k : ℕ) : WithBot ℕ) < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast k.lt_succ_self
        exact (Polynomial.degree_add_le _ _).trans_lt
          (max_lt (hf.trans hk) ((Polynomial.degree_C_mul_X_pow_le _ _).trans_lt hk))
      · simp only [map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
        rw [pow_succ, mul_assoc, ← ht]
        linear_combination hz
  have hmem : ϖ ∈ maximalIdeal R := by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
  obtain ⟨v, hv⟩ := he.dvd
  let N : Submodule R O := (Polynomial.degreeLT R e).map (Polynomial.aeval π).toLinearMap
  have hle : (⊤ : Submodule R O) ≤ N ⊔ maximalIdeal R • ⊤ := by
    intro x _
    obtain ⟨f, hf, y, hy⟩ := step e x
    refine Submodule.mem_sup.2 ⟨Polynomial.aeval π f, Submodule.mem_map.2 ⟨f, hf, rfl⟩, ϖ • (v * y),
      Submodule.smul_mem_smul hmem trivial, ?_⟩
    rw [Algebra.smul_def]
    linear_combination -hy - y * hv
  have hN := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›)
    (maximalIdeal_le_jacobson _) hle
  intro x
  obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.1 (hN (Submodule.mem_top : x ∈ ⊤))
  exact ⟨f, hf, hfx⟩

theorem eisenstein_of_totallyRamified {ϖ : R} (hϖ : Irreducible ϖ) [Module.Finite R O]
    (hinj : Function.Injective (algebraMap R O))
    (hres : ∀ x : O, ∃ c : R, ¬ IsUnit (x - algebraMap R O c)) {π : O} (hπ : Irreducible π) :
    ∃ Ep : Polynomial R, Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, ϖ ∣ Ep.coeff i) ∧
      (∃ w : Rˣ, Ep.coeff 0 = ϖ * w) ∧ Polynomial.aeval π Ep = 0 ∧
      (∀ x : O, ∃ f : Polynomial R, Polynomial.aeval π f = x) ∧
      ∀ f : Polynomial R, Polynomial.aeval π f = 0 → Ep ∣ f := by
  have hϖ0 : algebraMap R O ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hϖ0 hπ
  have he0 : e ≠ 0 := by
    rintro rfl
    exact not_isUnit_algebraMap hϖ (he.isUnit_iff.2 (by simp))
  have hed : π ^ e ∣ algebraMap R O ϖ := he.symm.dvd
  have hspan := exists_degreeLT hπ hϖ he hres
  obtain ⟨g, hg, hgπ⟩ := hspan (π ^ e)
  have hgdeg : g.degree < e := Polynomial.mem_degreeLT.1 hg
  have hdeg : (Polynomial.X ^ e - g).degree = (e : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]; exact hgdeg
  have hmon : (Polynomial.X ^ e - g).Monic := Polynomial.monic_X_pow_sub hgdeg
  have hnat : (Polynomial.X ^ e - g).natDegree = e := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have hroot : Polynomial.aeval π (Polynomial.X ^ e - g) = 0 := by simp [hgπ]
  have hsum : ∑ i ∈ Finset.range (e + 1), (Polynomial.X ^ e - g).coeff i • π ^ i = 0 := by
    have h := Polynomial.aeval_eq_sum_range (p := Polynomial.X ^ e - g) π
    rw [hnat] at h; rw [← h]; exact hroot
  have hdvd : ∀ i < e, ϖ ∣ (Polynomial.X ^ e - g).coeff i := fun i hi =>
    dvd_coeff_all hπ hϖ hed _ (by rw [hsum]; exact dvd_zero _) i hi (by omega)
  have hcoeffe : (Polynomial.X ^ e - g).coeff e = 1 := by
    have := hmon.coeff_natDegree; rwa [hnat] at this
  have hc0 : ∃ w : Rˣ, (Polynomial.X ^ e - g).coeff 0 = ϖ * w := by
    obtain ⟨w, hw⟩ := hdvd 0 (Nat.pos_of_ne_zero he0)
    by_cases hwu : ϖ ∣ w
    · exfalso
      obtain ⟨t, ht⟩ := hwu
      have hrest : π ^ (e + 1) ∣
          ∑ i ∈ (Finset.range (e + 1)).erase e, (Polynomial.X ^ e - g).coeff i • π ^ i := by
        refine Finset.dvd_sum fun i hi => ?_
        have hie : i < e := by
          have := Finset.mem_range.1 (Finset.mem_of_mem_erase hi); have := Finset.ne_of_mem_erase hi; omega
        rw [Algebra.smul_def]
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [pow_zero, mul_one, hw, ht, map_mul, map_mul]
          refine (pow_dvd_pow π (by omega : e + 1 ≤ e + e)).trans ?_
          rw [pow_add]; exact mul_dvd_mul hed (hed.mul_right _)
        · obtain ⟨d, hd⟩ := hdvd i hie
          rw [hd, map_mul, pow_succ]
          exact mul_dvd_mul (hed.mul_right _) (dvd_pow_self π hi0.ne')
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (Nat.lt_succ_self e)), hcoeffe, one_smul] at hsum
      have h1 : π ^ e * π ∣ π ^ e * 1 := by
        rw [← pow_succ, mul_one]; exact (dvd_add_left hrest).1 (by rw [hsum]; exact dvd_zero _)
      exact hπ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left (pow_ne_zero e hπ.ne_zero)).1 h1))
    · exact ⟨(isUnit_of_not_dvd_uniformiser hϖ hwu).unit, hw⟩
  have hmod : ∀ f : Polynomial R, Polynomial.aeval π f = 0 → (Polynomial.X ^ e - g) ∣ f := by
    intro f hf
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hmon]
    have hr : Polynomial.aeval π (f %ₘ (Polynomial.X ^ e - g)) = 0 := by
      have h := congrArg (Polynomial.aeval π) (Polynomial.modByMonic_add_div f (Polynomial.X ^ e - g))
      rwa [map_add, map_mul, hroot, zero_mul, add_zero, hf] at h
    have hrdeg : (f %ₘ (Polynomial.X ^ e - g)).natDegree < e := by
      by_cases h0 : f %ₘ (Polynomial.X ^ e - g) = 0
      · rw [h0, Polynomial.natDegree_zero]; omega
      · rw [Polynomial.natDegree_lt_iff_degree_lt h0, ← hdeg]
        exact Polynomial.degree_modByMonic_lt f hmon
    have hs := Polynomial.aeval_eq_sum_range' hrdeg π
    rw [hr] at hs
    have hc := coeff_eq_zero_of_sum hπ hϖ hinj hed _ hs.symm
    ext i
    rw [Polynomial.coeff_zero]
    by_cases hi : i < e
    · exact hc i hi
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  exact ⟨Polynomial.X ^ e - g, hmon, by rw [hnat]; omega, fun i hi => hdvd i (by rw [hnat] at hi; exact hi), hc0,
    hroot, fun x => (hspan x).imp fun f hf => hf.2, hmod⟩

theorem eisenstein_minpoly_Wq : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (Wq l a) O] [Module.Finite (Wq l a) O], Function.Injective (algebraMap (Wq l a) O) → (∀ x : O, ∃ c : Wq l a, ¬ IsUnit (x - algebraMap (Wq l a) O c)) → ∀ π : O, Irreducible π → ∃ Ep : Polynomial (Wq l a), Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w) ∧ Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f := by
  intro l _ a _ O _ _ _ _ _ hinj hres π hπ
  exact eisenstein_of_totallyRamified (WittVector.irreducible l) hinj hres hπ

end GlobalTheory.TotRam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBanachModelTensorAcrisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_banachModel_tensor_Acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (N : Type) (_ : NormedCommRing N) (_ : CompleteSpace N) (c : ↥LL.1 →+* N) (b : RA LL →+* N) (κ : N →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : N →+* N) (γ : GQ l → (N →+* N)) (t : N), ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∃ C : ℝ, ∀ x : ↥LL.1, ‖c x‖ ≤ C * ‖x‖) ∧ (∀ y, ‖b y‖ ≤ 1) ∧ (∀ o : ↥(OL LL), b (o ⊗ₜ[ℤ_[l]] (1 : Ainf l)) = c (o : ↥LL.1)) ∧ (∀ x, κ (c x) = x ⊗ₜ[ℚ_[l]] (1 : P.R.B)) ∧ (Continuous φ ∧ ∀ x, φ (c x) = c x) ∧ (∀ g, Continuous (γ g) ∧ ∀ x, γ g (c x) = c x) ∧ (∀ s : ℕ, ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ k‖ ≤ C * r ^ k) ∧ Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, c (PowerSeries.coeff k (logS LL)) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ k) Filter.atTop (nhds t) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), IsClosed {x : N | Algebra.TensorProduct.productMap ι P.ιB (κ x) ∈ GlobalTheory.ExpImage.FilB P (m : ℤ)} := by
  first | exact @GlobalTheory.HWL.BanachModel.exists_banach_model | exact GlobalTheory.HWL.BanachModel.exists_banach_model | (intros; apply GlobalTheory.HWL.BanachModel.exists_banach_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusFrameOfPeriodMatrixStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bdRPlus_frame_of_period_matrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (A : ↥(GK K) → Matrix n n P.R.BdR) (Q : GL n P.R.BdR), (∀ g i j, A g i j ∈ Fil P 0) → (∀ g : ↥(GK K), A g * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → ∃ (U : GL n P.R.BdR) (w : n → ℤ), UnitM P U ∧ ∀ g : ↥(GK K), A g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j => algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ w j : ℚ_[l]ˣ) : ℚ_[l]) := by
  first | exact @GlobalTheory.PMon.FrameOne.frame_of_period_matrix | exact GlobalTheory.PMon.FrameOne.frame_of_period_matrix | (intros; apply GlobalTheory.PMon.FrameOne.frame_of_period_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinEvalTeichmullerTilt
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKReal.Roots

variable (l : ℕ) [hl : Fact l.Prime]

theorem exists_roots (π : OC l) : ∃ s : ℕ → OC l, s 0 = π ∧ ∀ n, s (n + 1) ^ l = s n := by
  choose r hr using fun x : ℂ_[l] => IsAlgClosed.exists_pow_nat_eq x hl.out.pos
  have hn : ∀ x : ℂ_[l], ‖x‖ ≤ 1 → ‖r x‖ ≤ 1 := fun x hx => by
    have h := congrArg norm (hr x)
    rw [norm_pow] at h
    by_contra h1
    exact absurd (h ▸ one_lt_pow₀ (not_le.1 h1) hl.out.ne_zero) (not_lt.2 hx)
  let t : OC l → OC l := fun x => ⟨r x, (GlobalTheory.RingBasics.mem_OC _).2 (hn _ ((GlobalTheory.RingBasics.mem_OC _).1 x.2))⟩
  exact ⟨fun n => t^[n] π, rfl, fun n => by
    show (t^[n + 1] π) ^ l = t^[n] π
    rw [Function.iterate_succ_apply']
    exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hr _)⟩

variable {l} in

def flatOf (s : ℕ → OC l) (hs : ∀ n, s (n + 1) ^ l = s n) : OCb l :=
  (⟨fun n => Ideal.Quotient.mk _ (s n), fun n => by rw [← map_pow, hs]⟩ :
    Perfection (ModP (OC l) l) l)

variable {l} in

theorem untilt_flatOf (s : ℕ → OC l) (hs : ∀ n, s (n + 1) ^ l = s n) : (flatOf s hs).untilt = s 0 := by
  have hp : ∀ n, s n ^ l ^ n = s 0 := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, hs, ih]
  refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : OC l)}) fun n => ⟨s n, rfl, ?_⟩
  rw [hp]

end GlobalTheory.BKReal.Roots

namespace GlobalTheory.BKReal

theorem exists_ev_of_root : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (π : OC l), ¬ IsUnit π →
    ∃ (fl : OCb l) (ev : (Wq l a)⟦X⟧ →+* Ainf l), Per.θ l (WittVector.teichmuller l fl) = π ∧
      ev X = WittVector.teichmuller l fl ∧ (∀ w, ev (C w) = wA l a w) ∧
      ∀ x, ev (frobS l a x) = WittVector.frobenius (ev x) := by
  intro l hl a _ π hπ
  obtain ⟨s, hs0, hs⟩ := Roots.exists_roots l π
  set fl := Roots.flatOf s hs
  set t : Ainf l := WittVector.teichmuller l fl
  have ht : Per.θ l t = π := (WittVector.fontaineTheta_teichmuller _).trans
    ((Roots.untilt_flatOf s hs).trans hs0)
  have htu : ¬ IsUnit t := fun h => hπ (ht ▸ h.map (Per.θ l))
  have hc : IsAdicComplete (Ideal.span {t}) (Ainf l) := (GlobalTheory.Per.AinfComplete.main l _ htu).2
  have hsep : ∀ x : Ainf l, (∀ n, t ^ n ∣ x) → x = 0 := fun x h =>
    GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (h n)
  letI : Algebra (Wq l a) (Ainf l) := (wA l a).toRingHom.toAlgebra
  obtain ⟨f, hfX⟩ := GlobalTheory.Cyc.IoMap.algHom_exists (R := Wq l a) t
    (GlobalTheory.Per.AinfComplete.summ_of_precomplete _) hsep
  have hfC : ∀ w, f.toRingHom (C w) = wA l a w := f.commutes
  have h1 : WittVector.frobenius t = t ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  refine ⟨fl, f.toRingHom, ht, hfX, hfC, fun x => ?_⟩
  refine RingHom.congr_fun (ringHom_ext_of_sep (f.toRingHom.comp (frobS l a))
    (WittVector.frobenius.comp f.toRingHom) (fun w => ?_) ?_ fun y hy => hsep y fun n => ?_) x
  · simp only [RingHom.comp_apply, frobS_C, hfC, wA_sigma]
  · simp only [RingHom.comp_apply, frobS_X, map_pow]
    rw [show f.toRingHom X = t from hfX, h1]
  · refine Dvd.dvd.trans ?_ (hy n)
    simp only [RingHom.comp_apply, frobS_X, map_pow]
    rw [show f.toRingHom X = t from hfX]
    exact pow_dvd_pow_of_dvd (dvd_pow_self _ hl.out.ne_zero) n

end GlobalTheory.BKReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvdStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd : ∀ (l : ℕ) [Fact l.Prime], ∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap f F := by
  first | exact @GlobalTheory.BSP.exists_discMap_of_pow_dvd | exact GlobalTheory.BSP.exists_discMap_of_pow_dvd | (intros; apply GlobalTheory.BSP.exists_discMap_of_pow_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexReadingLocalEmbeddingStatement
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_reading_local_embedding : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv), ∃ τc : D.host.E →+* ℂ, ReadEmb bkP i ι v hv τ τc ∧ ∀ (v' : HeightOneSpectrum (𝓞 D.host.E)) (hv' : v' ∈ placesOver D.host.E (D.ntw.l i)) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' → ReadEmb bkP i ι v' hv' τ' (τc.comp (cj D)) := by
  first | exact @GlobalTheory.ReadEmbEx.exists_readEmb | exact GlobalTheory.ReadEmbEx.exists_readEmb | (intros; apply GlobalTheory.ReadEmbEx.exists_readEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGroupDataSeriesIdempotentsLabelSumsStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteGroupData_seriesIdempotentsLabelSums : ∀ D : D7, ∃ lz : ∀ k : Fin 2, PairedCharacterCondition.LzData (D.host.g k), SerEq D lz := by
  first | exact @GlobalTheory.LzExist.exists_lz_serEq | exact GlobalTheory.LzExist.exists_lz_serEq | (intros; apply GlobalTheory.LzExist.exists_lz_serEq <;> assumption)
end

