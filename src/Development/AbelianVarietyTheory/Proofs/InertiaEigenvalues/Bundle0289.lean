import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0271

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Decompl

theorem sep_complete_of_coord {R A B I : Type} [AddCommGroup R] [CommRing A] [CommRing B]
    (φ : I → R →+ B) (j : A →+* B) (hj : Function.Injective j) (t : A)
    (hs : ∀ c : I → A, ∃ x : R, ∀ i, φ i x = j (c i))
    (h1 : ∀ x : A, (∀ m : ℕ, t ^ m ∣ x) → x = 0)
    (h2 : ∀ a : ℕ → A, ∃ x : A, ∀ m : ℕ, t ^ m ∣ x - ∑ i ∈ Finset.range m, t ^ i * a i) :
    (∀ x : R, (∀ (m : ℕ) i, ∃ c, φ i x = j (t ^ m * c)) → ∀ i, φ i x = 0) ∧
    ∀ (k : ℕ) (f : ℕ → R), (∀ n i, ∃ c, φ i (f n) = j (t ^ (n + k) * c)) →
      ∃ x, ∀ (m : ℕ) i, ∃ c, φ i (x - ∑ n ∈ Finset.range m, f n) = j (t ^ (m + k) * c) := by
  refine ⟨fun x hx i => ?_, fun k f hf => ?_⟩
  · obtain ⟨y, hy⟩ := hx 0 i
    rw [pow_zero, one_mul] at hy
    have hdiv : ∀ m : ℕ, t ^ m ∣ y := by
      intro m
      obtain ⟨c, hc⟩ := hx m i
      exact ⟨c, hj (hy.symm.trans hc)⟩
    rw [hy, h1 y hdiv, map_zero]
  · choose c hc using hf
    choose y hy using fun i => h2 (fun n => c n i)
    obtain ⟨x, hx⟩ := hs (fun i => t ^ k * y i)
    refine ⟨x, fun m i => ?_⟩
    obtain ⟨d, hd⟩ := hy i m
    refine ⟨d, ?_⟩
    rw [map_sub, map_sum, hx i, Finset.sum_congr rfl (fun n _ => hc n i), ← map_sum j, ← map_sub j]
    congr 1
    have e : t ^ k * y i - ∑ n ∈ Finset.range m, t ^ (n + k) * c n i =
        t ^ k * (y i - ∑ n ∈ Finset.range m, t ^ n * c n i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e, hd]
    ring

def crdZero {l : ℕ} [Fact l.Prime] (LL : FinExt l) (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) :
    RW LL →+ Cb l :=
  (WittVector.constantCoeff : WCb l →+* Cb l).toAddMonoidHom.comp
    (crd (W := WCb l) (basisO LL) i).toAddMonoidHom

theorem crdZero_apply {l : ℕ} [Fact l.Prime] (LL : FinExt l) (i) (x : RW LL) :
    crdZero LL i x = (crd (basisO LL) i x).coeff 0 := rfl

private theorem crd_tmul_lemma {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (o : ↥(OL LL)) (w : WCb l) :
    crd (W := WCb l) (basisO LL) i (o ⊗ₜ[ℤ_[l]] w) = (basisO LL).coord i o • w := by
  unfold crd
  rfl

set_option maxHeartbeats 1000000 in
private theorem crd_mul_lemma_2 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (q : WCb l) (y : RW LL) :
    crd (W := WCb l) (basisO LL) i (((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] q) * y) =
      q * crd (W := WCb l) (basisO LL) i y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, crd_tmul_lemma, crd_tmul_lemma, mul_smul_comm]
  | add y z hy hz =>
    rw [mul_add, LinearMap.map_add, LinearMap.map_add, hy, hz]
    exact (mul_add q _ _).symm

private theorem expand_lemma_3 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (y : RW LL) :
    ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] crd (W := WCb l) (basisO LL) k y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o w =>
    simp_rw [crd_tmul_lemma, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul]
    simp_rw [Module.Basis.coord_apply]
    rw [Module.Basis.sum_repr]
  | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hy, hz]

private theorem crd_sum_lemma_4 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (w : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → WCb l) :
    crd (W := WCb l) (basisO LL) i (∑ k, basisO LL k ⊗ₜ[ℤ_[l]] w k) = w i := by
  simp [map_sum, crd_tmul_lemma, Finsupp.single_apply]

private theorem wdiv_lemma_5 {l : ℕ} [Fact l.Prime] (w : WCb l) (hw : w.coeff 0 = 0) :
    ∃ v : WCb l, w = (l : WCb l) * v := by
  have e : w = WittVector.verschiebung^[1] (w.shift 1) :=
    WittVector.eq_iterate_verschiebung (fun i hi => by
      obtain rfl : i = 0 := by omega
      exact hw)
  obtain ⟨z, hz⟩ := (WittVector.frobenius_bijective (p := l) (R := Cb l)).2 (w.shift 1)
  refine ⟨z, ?_⟩
  rw [e, Function.iterate_one, ← hz, WittVector.verschiebung_frobenius, mul_comm]

private theorem rwdiv_lemma_6 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (z : RW LL)
    (hz : ∀ i, (crd (W := WCb l) (basisO LL) i z).coeff 0 = 0) : ∃ r : RW LL, z = (l : RW LL) * r := by
  choose v hv using fun i => wdiv_lemma_5 _ (hz i)
  refine ⟨∑ k, basisO LL k ⊗ₜ[ℤ_[l]] v k, ?_⟩
  rw [← expand_lemma_3 LL z, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hv k, ← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.tmul_smul]

private theorem cc_inclW_lemma_7 {l : ℕ} [Fact l.Prime] (w : Ainf l) :
    (inclW l w).coeff 0 = algebraMap (OCb l) (Cb l) (w.coeff 0) := by
  unfold inclW
  exact WittVector.map_coeff _ _ 0

private theorem cc_pi_lemma_8 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ) :
    (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 =
      algebraMap (OCb l) (Cb l) (AI.εroot s - 1) := by
  rw [cc_inclW_lemma_7]
  congr 1
  change WittVector.constantCoeff (WittVector.teichmuller l (AI.εroot s) - 1) = _
  rw [map_sub, map_one]
  rfl

private theorem inclR_piR_lemma_9 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ) :
    piR AI LL s =
      (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (AI.εroot s) - 1) := rfl

private theorem inclR_tmul_lemma_10 {l : ℕ} [Fact l.Prime] (LL : FinExt l) (o : ↥(OL LL)) (w : Ainf l) :
    (inclR LL) (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] inclW l w := rfl

private theorem cc_inclR_lemma_11 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) (a : ↥(OL LL) ⊗[ℤ_[l]] Ainf l) :
    ∃ c : OCb l, (crd (W := WCb l) (basisO LL) i (inclR LL a)).coeff 0 = algebraMap (OCb l) (Cb l) c := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul o w =>
    refine ⟨((basisO LL).coord i o • w).coeff 0, ?_⟩
    rw [inclR_tmul_lemma_10, crd_tmul_lemma, ← cc_inclW_lemma_7]
    congr 1
    exact (map_smul (inclWA l) _ _).symm
  | add a b ha hb =>
    obtain ⟨c1, h1⟩ := ha
    obtain ⟨c2, h2⟩ := hb
    refine ⟨c1 + c2, ?_⟩
    have e : (inclR LL) (a + b) = (inclR LL) a + (inclR LL) b := (inclR LL).toRingHom.map_add a b
    rw [e, LinearMap.map_add, (algebraMap (OCb l) (Cb l)).map_add, ← h1, ← h2]
    exact WittVector.add_coeff_zero _ _

private theorem coord_of_near_lemma_12 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s n : ℕ) (y : RW LL) (h : NearPi AI LL s n y)
    (i : Fin (Module.finrank ℤ_[l] ↥(OL LL))) :
    ∃ c, crdZero LL i y = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ n * c) := by
  unfold NearPi Near at h
  obtain ⟨a, r, rfl⟩ := h
  obtain ⟨c, hc⟩ := cc_inclR_lemma_11 LL i a
  refine ⟨c, ?_⟩
  rw [map_add, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, crdZero_apply, inclR_piR_lemma_9,
    Algebra.TensorProduct.tmul_pow, one_pow, crd_mul_lemma_2]
  change WittVector.constantCoeff (p := l) (R := Cb l) (_ * _) + _ = _
  rw [map_mul, map_pow]
  change (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 ^ n *
    (crd (W := WCb l) (basisO LL) i (inclR LL a)).coeff 0 + _ = _
  rw [cc_pi_lemma_8, hc, map_mul, map_pow]
  simp

set_option maxHeartbeats 2000000 in
private theorem near_of_coord_lemma_13 {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s n : ℕ) (y : RW LL)
    (h : ∀ i, ∃ c, crdZero LL i y = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ n * c)) :
    NearPi AI LL s n y := by
  choose c hc using h
  let a : ↥(OL LL) ⊗[ℤ_[l]] Ainf l := ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (c k)
  obtain ⟨r, hr⟩ := rwdiv_lemma_6 LL (y - piR AI LL s ^ n * (inclR LL) a) (fun i => by
    have ha : (inclR LL) a = ∑ k, basisO LL k ⊗ₜ[ℤ_[l]] inclW l (WittVector.teichmuller l (c k)) := by
      change (inclR LL : RA LL →+* RW LL) (∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (c k)) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => rfl
    rw [LinearMap.map_sub, inclR_piR_lemma_9, Algebra.TensorProduct.tmul_pow, one_pow, crd_mul_lemma_2, ha,
      crd_sum_lemma_4]
    change WittVector.constantCoeff (p := l) (R := Cb l) (_ - _) = 0
    rw [map_sub, map_mul, map_pow]
    change (crd (W := WCb l) (basisO LL) i y).coeff 0 -
      (inclW l (WittVector.teichmuller l (AI.εroot s) - 1)).coeff 0 ^ n *
        (inclW l (WittVector.teichmuller l (c i))).coeff 0 = 0
    rw [← crdZero_apply, hc, cc_pi_lemma_8, cc_inclW_lemma_7, WittVector.teichmuller_coeff_zero, map_mul,
      map_pow, sub_self])
  unfold NearPi Near
  exact ⟨a, r, sub_eq_iff_eq_add'.mp hr⟩

private theorem surj_lemma_14 {l : ℕ} [Fact l.Prime] (LL : FinExt l)
    (c : Fin (Module.finrank ℤ_[l] ↥(OL LL)) → OCb l) :
    ∃ x : RW LL, ∀ i, crdZero LL i x = algebraMap (OCb l) (Cb l) (c i) := by
  refine ⟨∑ k, basisO LL k ⊗ₜ[ℤ_[l]] WittVector.teichmuller l (algebraMap (OCb l) (Cb l) (c k)),
    fun i => ?_⟩
  rw [crdZero_apply, crd_sum_lemma_4, WittVector.teichmuller_coeff_zero]

theorem nearPi_sep_complete (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ) :
    (∀ x : RW LL, (∀ m, NearPi AI LL s m x) → ∃ r, x = (l : RW LL) * r) ∧
    ∀ (k : ℕ) (f : ℕ → RW LL), (∀ i, NearPi AI LL s (i + k) (f i)) →
      ∃ x, ∀ m, NearPi AI LL s (m + k) (x - ∑ i ∈ Finset.range m, f i) := by
  have key := sep_complete_of_coord (fun i => crdZero LL i) (algebraMap (OCb l) (Cb l))
    (IsFractionRing.injective (OCb l) (Cb l)) (AI.εroot s - 1) (surj_lemma_14 LL)
    (GlobalTheory.T.tilt_separated_complete_epsilonRoot_sub_one l P AI s).1 (GlobalTheory.T.tilt_separated_complete_epsilonRoot_sub_one l P AI s).2
  refine ⟨fun x hx => ?_, fun k f hf => ?_⟩
  · refine rwdiv_lemma_6 LL x fun i => ?_
    rw [← crdZero_apply]
    exact key.1 x (fun m i => coord_of_near_lemma_12 P AI LL s m x (hx m) i) i
  · obtain ⟨x, hx⟩ := key.2 k f (fun n i => coord_of_near_lemma_12 P AI LL s (n + k) (f n) (hf n) i)
    exact ⟨x, fun m => near_of_coord_lemma_13 P AI LL s (m + k) _ (hx m)⟩

end GlobalTheory.Decompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem geom_sum_add_one_eq_sum_choose {R : Type*} [Ring R] (D : R) (n : ℕ) :
    ∑ i ∈ Finset.range n, (D + 1) ^ i = ∑ j ∈ Finset.range n, n.choose (j + 1) • D ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h := (Commute.one_right D).add_pow n
    simp only [one_pow, mul_one] at h
    rw [h]
    simp_rw [Nat.choose_succ_succ', add_smul]
    rw [Finset.sum_add_distrib, Finset.sum_range_succ (fun j => n.choose (j + 1) • D ^ j) n,
      Nat.choose_succ_self, zero_smul, add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [nsmul_eq_mul, Nat.cast_comm]

theorem norm_geom_sum_galois_le (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hS : ∀ x ∈ S, σ x ∈ S) (hσ : ∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) :
    ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧
      ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  intro x hx
  set M := max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ with hM

  have hpowS : ∀ (i : ℕ), ∀ y ∈ S, (σ ^ i) y ∈ S := by
    intro i
    induction i with
    | zero => intro y hy; simpa using hy
    | succ i ih => intro y hy; rw [pow_succ', AlgEquiv.mul_apply]; exact hS _ (ih y hy)

  let T : AddMonoid.End (Om l) := AddMonoidHom.mk' (fun y => σ y) (fun a b => map_add σ a b)
  have hT : ∀ (i : ℕ) (y : Om l), (T ^ i) y = (σ ^ i) y := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih => intro y; rw [pow_succ', pow_succ', AlgEquiv.mul_apply, ← ih]; rfl
  have hD : ∀ (j : ℕ), ∀ y ∈ S, ((T - 1) ^ j) y ∈ S ∧ ‖((T - 1) ^ j) y‖ ≤ s ^ j * ‖y‖ := by
    intro j
    induction j with
    | zero => intro y hy; rw [pow_zero]; exact ⟨hy, by rw [pow_zero, one_mul]; exact le_rfl⟩
    | succ j ih =>
      intro y hy
      obtain ⟨h1, h2⟩ := ih y hy
      rw [pow_succ']
      change σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y ∈ S ∧
        ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s ^ (j + 1) * ‖y‖
      refine ⟨S.sub_mem (hS _ h1) h1, ?_⟩
      calc ‖σ (((T - 1) ^ j) y) - ((T - 1) ^ j) y‖ ≤ s * ‖((T - 1) ^ j) y‖ := hσ _ h1
        _ ≤ s * (s ^ j * ‖y‖) := mul_le_mul_of_nonneg_left h2 hs0
        _ = s ^ (j + 1) * ‖y‖ := by ring

  have hnat : ∀ n : ℕ, ‖((n : ℕ) : Om l)‖ ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih norm_one.le)

  have key := geom_sum_add_one_eq_sum_choose (T - 1) l
  rw [sub_add_cancel] at key
  have hsum : ∑ i ∈ Finset.range l, (σ ^ i) x =
      ∑ j ∈ Finset.range l, l.choose (j + 1) • ((T - 1) ^ j) x := by
    let ev : AddMonoid.End (Om l) →+ Om l :=
      { toFun := fun f => f x, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have h := congrArg ev key
    simp only [map_sum, map_nsmul] at h
    calc ∑ i ∈ Finset.range l, (σ ^ i) x = ∑ i ∈ Finset.range l, (T ^ i) x :=
          Finset.sum_congr rfl fun i _ => (hT i x).symm
      _ = _ := h
  have hbound : ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ M * ‖x‖ := by
    rw [hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg (le_max_of_le_right (norm_nonneg _)) (norm_nonneg _)) fun j hj => ?_
    obtain ⟨-, hle⟩ := hD j x hx
    have hsj : s ^ j ≤ 1 := pow_le_one₀ hs0 hs1
    rw [nsmul_eq_mul, norm_mul]
    rcases Nat.lt_or_ge (j + 1) l with hlt | hge
    ·
      obtain ⟨m, hm⟩ := (Fact.out : l.Prime).dvd_choose_self (Nat.succ_ne_zero j) hlt
      rw [hm, Nat.cast_mul, norm_mul]
      have h3 : ‖((T - 1) ^ j) x‖ ≤ 1 * ‖x‖ :=
        hle.trans (mul_le_mul_of_nonneg_right hsj (norm_nonneg _))
      calc _ ≤ ‖((l : ℕ) : Om l)‖ * 1 * (1 * ‖x‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hnat m) (norm_nonneg _)) h3 (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) zero_le_one)
        _ ≤ M * ‖x‖ := by
            rw [mul_one, one_mul]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    ·
      have hjl : j = l - 1 := by have := Finset.mem_range.mp hj; omega
      have hc : l.choose (j + 1) = 1 := by
        rw [show j + 1 = l by have := Finset.mem_range.mp hj; omega, Nat.choose_self]
      rw [hc, Nat.cast_one, norm_one, one_mul]
      calc _ ≤ s ^ j * ‖x‖ := hle
        _ ≤ M * ‖x‖ := by
            rw [hjl]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

  set y := ∑ i ∈ Finset.range l, (σ ^ i) x with hy
  have hyS : y ∈ S := S.sum_mem fun i _ => hpowS i x hx
  have htel : (σ ^ l) x - x = σ y - y := by
    rw [hy, map_sum, ← Finset.sum_sub_distrib]
    have h := Finset.sum_range_sub (fun i => (σ ^ i) x) l
    simp only [pow_zero, AlgEquiv.one_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pow_succ', AlgEquiv.mul_apply]
  refine ⟨hbound, ?_⟩
  rw [htel]
  calc ‖σ y - y‖ ≤ s * ‖y‖ := hσ y hyS
    _ ≤ s * (M * ‖x‖) := mul_le_mul_of_nonneg_left hbound hs0
    _ = M * s * ‖x‖ := by ring

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowIndexLeOfFixed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem norm_pow_index_le_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup (GQ l)), H.index ≠ 0 → ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖x‖ < 1 → ‖x‖ ^ H.index ≤ ‖((l : ℕ) : Om l)‖ := by
  intro l _ H hidx x hx hx1
  have hfin : Fintype (GQ l ⧸ H) := Subgroup.fintypeOfIndexNeZero hidx
  have fout : ∀ g : GQ l, (g : GQ l ⧸ H).out x = g x := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, AlgEquiv.mul_apply, hx h h.2]
  have hfix : ∀ g : GQ l, g (∏ q : GQ l ⧸ H, q.out x) = ∏ q : GQ l ⧸ H, q.out x := fun g => by
    rw [map_prod, ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ H => q.out x]
    refine Finset.prod_congr rfl fun q _ => ?_
    have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ H) := by
      rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    rw [e, fout, AlgEquiv.mul_apply]
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  have hn : ‖c‖ = ‖x‖ ^ H.index := by
    rw [← norm_algebraMap' (Om l) c, hc, norm_prod]
    refine (Finset.prod_congr rfl fun q _ => GlobalTheory.RingBasics.norm_gal (Quotient.out q) x).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
    rfl
  have hc1 : ‖c‖ < 1 := hn ▸ pow_lt_one₀ (norm_nonneg x) hx1 hidx
  have h2 : ‖c‖ ≤ (l : ℝ) ^ (-1 : ℤ) := by
    rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simpa using hc1
  rw [← hn, ← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]
  simpa using h2

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRing
section
namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc Filter Topology

theorem exists_padicInt_lim {l : ℕ} [Fact l.Prime] (z : ℕ → ℤ_[l])
    (h : ∀ n m, n ≤ m → ‖z n - z m‖ ≤ (l : ℝ) ^ (-(n : ℤ))) :
    ∃ y : ℤ_[l], ∀ n : ℕ, ∃ w : ℤ_[l], y - z n = (l : ℤ_[l]) ^ n * w := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : Tendsto (fun n : ℕ => (l : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    simpa using this
  have hc : CauchySeq z :=
    cauchySeq_of_le_tendsto_0' _ (fun n m hnm => by rw [dist_eq_norm]; exact h n m hnm) h0
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨y, fun n => ?_⟩
  have h1 : ‖z n - y‖ ≤ (l : ℝ) ^ (-(n : ℤ)) :=
    le_of_tendsto ((tendsto_const_nhds.sub hy).norm)
      (eventually_atTop.2 ⟨n, fun m hm => h n m hm⟩)
  rw [norm_sub_rev, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at h1
  exact h1

theorem nearZ_of_forall_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M : ℕ) (hM : 1 ≤ M) (v : P.R.BdR)
    (hv : ∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) : NearZ P M v := by
  choose z hz using hv
  obtain ⟨y, hy⟩ := exists_padicInt_lim z (fun n m hnm => by
    have h1 := sub_mem (hz n) (Lat_anti AI hnm (hz m))
    rw [sub_sub_sub_cancel_right, ← map_sub] at h1
    exact GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM _ h1)
  refine ⟨y, GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI T M _ fun n => ?_⟩
  obtain ⟨w, hw⟩ := hy n
  have h2 := io_mem_Lat AI M n (algebraMap ℤ_[l] (Ainf l) w)
  rw [← map_natCast (algebraMap ℤ_[l] (Ainf l)), ← map_pow, ← map_mul, ← hw, io_zl AI T,
    PadicInt.coe_sub, map_sub] at h2
  have := add_mem h2 (hz n)
  rwa [sub_add_sub_cancel] at this

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntExistsPowSubNormLeOfExactLevel
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory

theorem padicInt_exists_pow_sub_norm_le_of_exact_level (l : ℕ) [Fact l.Prime] (u v : ℤ_[l]) (m : ℕ)
    (hm : 1 ≤ m) (hu : ‖u - 1‖ = ‖((l : ℕ) : ℤ_[l])‖ ^ m)
    (hv : ‖v - 1‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ m) :
    ∃ i : ℕ, ‖u ^ i - v‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ (m + 1) := by
  have key : ∀ (x : ℤ_[l]) (n : ℕ), ‖x‖ ≤ ‖((l : ℕ) : ℤ_[l])‖ ^ n ↔ ((l : ℕ) : ℤ_[l]) ^ n ∣ x := by
    intro x n
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_p,
      zpow_neg, zpow_natCast, inv_pow]
  have hl0 : ‖((l : ℕ) : ℤ_[l])‖ ^ m ≠ 0 := by
    apply pow_ne_zero
    rw [norm_ne_zero_iff]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  obtain ⟨a, ha⟩ := (key _ _).1 hu.le
  obtain ⟨b, hb⟩ := (key _ _).1 hv
  have ha1 : ‖a‖ = 1 := by
    rw [ha, norm_mul, norm_pow] at hu
    exact mul_left_cancel₀ hl0 (by rw [hu, mul_one])
  obtain ⟨a', ha'⟩ := (PadicInt.isUnit_iff.2 ha1).exists_right_inv
  refine ⟨(a' * b).appr 1, (key _ _).2 ?_⟩
  set i := (a' * b).appr 1 with hi
  have hc := PadicInt.appr_spec 1 (a' * b)
  rw [Ideal.mem_span_singleton, pow_one, ← hi] at hc
  obtain ⟨c, hc⟩ := hc
  have hu' : u = 1 + ((l : ℕ) : ℤ_[l]) ^ m * a := by rw [← ha]; ring
  have hv' : v = 1 + ((l : ℕ) : ℤ_[l]) ^ m * b := by rw [← hb]; ring
  have hpow : ∀ (x : ℤ_[l]) (n : ℕ), ∃ d, (1 + x) ^ n = 1 + n * x + x ^ 2 * d := by
    intro x n
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨d, hd⟩ := ih
      exact ⟨d + n + x * d, by rw [pow_succ, hd]; push_cast; ring⟩
  obtain ⟨d, hd⟩ := hpow (((l : ℕ) : ℤ_[l]) ^ m * a) i
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  refine ⟨-(a * c) + ((l : ℕ) : ℤ_[l]) ^ k * a ^ 2 * d, ?_⟩
  have hi' : (i : ℤ_[l]) = a' * b - ((l : ℕ) : ℤ_[l]) * c := by rw [← hc]; ring
  rw [hu', hd, hv', hi']
  linear_combination (((l : ℕ) : ℤ_[l]) ^ (1 + k) * b) * ha'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntegersFiniteExtGoodCoefficientRing
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LitGood

theorem litGoodO : LitGoodO :=
  fun l _ LL => GlobalTheory.Pass.goodO_ringOfIntegers l LL

end GlobalTheory.LitGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowMulInvPowMemAinfFilLatticeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_mul_inv_pow_mem_ainfFilLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (s : ℕ), Lev l s → ∀ u ∈ FilB P 0, io AI AI.π₁ * u = 1 → ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ a : Ainf l, (l : P.R.BdR) ^ (s * k) * io AI a * u ^ (k + 1) ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat | exact GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat | (intros; apply GlobalTheory.ExpImage.pow_mul_inv_pow_mem_Lat <;> assumption)
end

