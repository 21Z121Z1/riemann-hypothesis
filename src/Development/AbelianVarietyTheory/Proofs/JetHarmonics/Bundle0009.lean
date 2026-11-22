import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueMaximalAbovePlace
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.OnePrime

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

theorem nontrivial_Ow (w : Place p R) : Nontrivial w.Ow := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  rw [Ideal.span_singleton_eq_top] at h
  have h1 : (1 - w.e) * (1 - w.e) = (1 - w.e) * 1 := by
    rw [mul_one]; exact w.idem.one_sub
  exact w.ne_zero (sub_eq_self.mp (h.mul_left_cancel h1))

theorem idem_Ow (w : Place p R) {d : w.Ow} (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  have hx : x * x - x ∈ Ideal.span {1 - w.e} :=
    Ideal.Quotient.eq.mp (by rw [map_mul]; exact hd)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hx
  have hee : w.e * w.e = w.e := w.idem
  have he1 : Ideal.Quotient.mk (Ideal.span {1 - w.e}) w.e = 1 := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩
  have hf : IsIdempotentElem (w.e * x) := by
    show w.e * x * (w.e * x) = w.e * x
    linear_combination (x * x - c) * hee - w.e * hc
  have hfe : w.e * x * w.e = w.e * x := by linear_combination x * hee
  have hmk : Ideal.Quotient.mk (Ideal.span {1 - w.e}) (w.e * x) =
      Ideal.Quotient.mk (Ideal.span {1 - w.e}) x := by
    rw [map_mul, he1, one_mul]
  rcases w.primitive _ hf hfe with h0 | h1
  · left
    rw [← hmk, h0, map_zero]
  · right
    rw [← hmk, h1, he1]

theorem maximal_unique [Module.Finite ℤ R] (w : Place p R) (M N : Ideal w.Ow) (hM : M.IsMaximal)
    (hN : N.IsMaximal) : N = M := by
  have : HenselianLocalRing ℤ_[p] := GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[p]
  have := hM
  obtain ⟨d, hd, hmem⟩ := GlobalTheory.exists_idempotent_notMem_iff_of_henselian ℤ_[p] (S := w.Ow) M
  rcases idem_Ow w hd with rfl | rfl
  · exact absurd M.zero_mem ((hmem M hM).mpr rfl)
  · exact (hmem N hN).mp (fun h => hN.ne_top ((Ideal.eq_top_iff_one _).mpr h))

private theorem exists_eq_one_tmul_add_mul (x : Op p R) :
    ∃ (r : R) (t : Op p R), x = (1 : ℤ_[p]) ⊗ₜ r + (p : Op p R) * t := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z r =>
    obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := z)
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨(n : R) * r, t ⊗ₜ r, ?_⟩
    have hz : z = (n : ℤ_[p]) + t * p := by rw [ht]; ring
    have h1 : (n : ℤ_[p]) ⊗ₜ[ℤ] r = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by
      calc (n : ℤ_[p]) ⊗ₜ[ℤ] r = ((n : ℤ_[p]) ⊗ₜ[ℤ] (1 : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        _ = (n : Op p R) * ((1 : ℤ_[p]) ⊗ₜ r) := by rw [Algebra.TensorProduct.natCast_def]
        _ = ((1 : ℤ_[p]) ⊗ₜ[ℤ] (n : R)) * ((1 : ℤ_[p]) ⊗ₜ r) := by
            rw [Algebra.TensorProduct.natCast_def']
        _ = (1 : ℤ_[p]) ⊗ₜ ((n : R) * r) := by rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h2 : (t * p) ⊗ₜ[ℤ] r = (p : Op p R) * (t ⊗ₜ r) := by
      rw [Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm]
    rw [hz, TensorProduct.add_tmul, h1, h2]
  | add x y hx hy =>
    obtain ⟨r₁, t₁, h₁⟩ := hx
    obtain ⟨r₂, t₂, h₂⟩ := hy
    exact ⟨r₁ + r₂, t₁ + t₂, by rw [h₁, h₂, TensorProduct.tmul_add]; ring⟩

theorem exists_eq_add (w : Place p R) (s : w.Ow) :
    ∃ (r : R) (t : w.Ow), s = w.toOw r + (p : w.Ow) * t := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, t, h⟩ := exists_eq_one_tmul_add_mul x
  refine ⟨r, Ideal.Quotient.mk _ t, ?_⟩
  rw [h, map_add, map_mul, map_natCast]
  rfl

theorem exists_prime_under (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDedekindDomain R]
    [CharZero R] [Module.Finite ℤ R] (w : GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces.Place p R) :
    ∃ P : Ideal R, P.IsMaximal ∧ (p : R) ∈ P ∧ (P.map w.toOw).IsMaximal ∧
      ∀ Q : Ideal R, Q.IsMaximal → Q ≠ P → Q.map w.toOw = ⊤ := by
  have : HenselianLocalRing ℤ_[p] := GlobalTheory.henselianLocalRing_of_henselianRing ℤ_[p]
  have : Nontrivial w.Ow := nontrivial_Ow w
  have : IsLocalRing w.Ow := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal w.Ow
    exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun N hN => maximal_unique w M N hM hN⟩
  set m := IsLocalRing.maximalIdeal w.Ow with hm
  set P := m.comap w.toOw with hP
  have hpm : (p : w.Ow) ∈ m := by
    have hc := GlobalTheory.comap_eq_maximalIdeal_of_finite (R := ℤ_[p]) (S := w.Ow) m
    have h0 : (p : ℤ_[p]) ∈ m.comap (algebraMap ℤ_[p] w.Ow) := by
      rw [hc, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at h0
    exact h0
  have hpP : (p : R) ∈ P := by
    rw [hP, Ideal.mem_comap, map_natCast]
    exact hpm
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hpP
  have : P.IsPrime := Ideal.comap_isPrime _ _
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPne
  have hmap : P.map w.toOw = m := by
    refine le_antisymm Ideal.map_comap_le fun s hs => ?_
    obtain ⟨r, t, rfl⟩ := exists_eq_add w s
    have hpt : (p : w.Ow) * t ∈ P.map w.toOw := by
      rw [← map_natCast w.toOw p]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hpP)
    have hr : w.toOw r ∈ m := by
      have h1 := m.sub_mem hs (m.mul_mem_right t hpm)
      rwa [add_sub_cancel_right] at h1
    exact Ideal.add_mem _ (Ideal.mem_map_of_mem _ (show r ∈ P from hr)) hpt
  refine ⟨P, hPmax, hpP, by rw [hmap]; infer_instance, fun Q hQ hQP => ?_⟩
  by_contra hne
  have hle : Q.map w.toOw ≤ m := IsLocalRing.le_maximalIdeal hne
  exact hQP (hQ.eq_of_le hPmax.ne_top fun q hq => hle (Ideal.mem_map_of_mem _ hq))

end GlobalTheory.OnePrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesProperties
section
noncomputable section

namespace GlobalTheory.ConvSer

open MvPowerSeries Finsupp

open MvPowerSeries Finsupp in
theorem _root_.GlobalTheory.ConvSer.nMul_hasSubst_pair {R : Type*} [CommRing R] {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    MvPowerSeries.HasSubst (![f, g] : Fin 2 → MvPowerSeries Unit R) := by
  refine hasSubst_of_constantCoeff_zero fun s => ?_
  fin_cases s
  · exact hf
  · exact hg

open MvPowerSeries Finsupp in
theorem _root_.GlobalTheory.ConvSer.nMul_constantCoeff {R : Type*} [CommRing R] (F : FormalGroup R)
    (n : ℕ) : PowerSeries.constantCoeff (_root_.GlobalTheory.ConvSer.nMul F n) = 0 := by
  induction n with
  | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
  | succ n ih =>
    rw [_root_.GlobalTheory.ConvSer.nMul_succ]
    refine constantCoeff_subst_eq_zero
      (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair ih PowerSeries.constantCoeff_X) (fun s => ?_) F.2
    fin_cases s
    · exact ih
    · exact PowerSeries.constantCoeff_X

theorem nMul_hasSubst {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.HasSubst (nMul F n) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (nMul_constantCoeff F n)

theorem coeff_one_formalGroup_subst {R : Type*} [CommRing R] (F : FormalGroup R)
    {f g : PowerSeries R}
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries) = PowerSeries.coeff 1 f + PowerSeries.coeff 1 g := by
  have hne : (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp at this
  have key : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![f, g] : Fin 2 → MvPowerSeries Unit R) s ^ e)
      = (f ^ d 0 * g ^ d 1 : PowerSeries R) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    rfl
  have hc : ∀ h : PowerSeries R, MvPowerSeries.coeff (single () 1) h = PowerSeries.coeff 1 h :=
    fun _ => rfl
  rw [← hc, coeff_subst (nMul_hasSubst_pair hf hg),
    finsum_eq_sum_of_support_subset (s := {single 0 1, single 1 1})]
  · rw [Finset.sum_pair hne, key, key, hc, hc, F.lin_coeff_X, F.lin_coeff_Y]
    simp
  · intro d hd
    by_contra hn
    apply hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hn
    have h2 : d 0 + d 1 = 0 ∨ 2 ≤ d 0 + d 1 := by
      by_contra hh
      have : (d 0 = 1 ∧ d 1 = 0) ∨ (d 0 = 0 ∧ d 1 = 1) := by omega
      rcases this with h | h
      · apply hn.1
        ext s
        fin_cases s <;> simp [h]
      · apply hn.2
        ext s
        fin_cases s <;> simp [h]
    have h0 : PowerSeries.coeff 1 (f ^ d 0 * g ^ d 1) = 0 := by
      rcases h2 with h | h
      · have h0 : d 0 = 0 := by omega
        have h1 : d 1 = 0 := by omega
        simp [h0, h1, PowerSeries.coeff_one]
      · have hd : (PowerSeries.X : PowerSeries R) ^ (d 0 + d 1) ∣ f ^ d 0 * g ^ d 1 := by
          rw [pow_add]
          exact mul_dvd_mul (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hf) _)
            (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 hg) _)
        exact PowerSeries.X_pow_dvd_iff.1 hd 1 (by omega)
    show _ • _ = _
    rw [key, hc, h0, smul_zero]

theorem nMul_coeff_one {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    PowerSeries.coeff 1 (nMul F n) = (n : R) := by
  induction n with
  | zero => simp [nMul_zero]
  | succ n ih =>
    rw [nMul_succ, coeff_one_formalGroup_subst F (nMul_constantCoeff F n)
      PowerSeries.constantCoeff_X, ih]
    simp

theorem nMul_one {R : Type*} [CommRing R] (F : FormalGroup R) : nMul F 1 = PowerSeries.X := by
  rw [nMul_succ, nMul_zero]
  exact F.zeroX_eq_X

theorem nMul_add {R : Type*} [CommRing R] (F : FormalGroup R) (i j : ℕ) :
    MvPowerSeries.subst (![nMul F i, nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries
      = nMul F (i + j) := by
  induction j with
  | zero => exact F.add_zero (nMul_hasSubst F i)
  | succ j ih =>
    rw [← add_assoc, nMul_succ, nMul_succ, ← ih]
    exact (F.assoc' (nMul_hasSubst F i) (nMul_hasSubst F j) PowerSeries.HasSubst.X').symm

theorem nMul_subst_nMul {R : Type*} [CommRing R] (F : FormalGroup R) (i j : ℕ) :
    (nMul F i).subst (nMul F j) = nMul F (i * j) := by
  induction i with
  | zero =>
    rw [zero_mul, nMul_zero, ← PowerSeries.coe_substAlgHom (nMul_hasSubst F j), map_zero]
  | succ i ih =>
    rw [add_mul, one_mul, ← nMul_add F (i * j) j, nMul_succ F i, PowerSeries.subst,
      subst_comp_subst_apply
        (nMul_hasSubst_pair (nMul_constantCoeff F i) PowerSeries.constantCoeff_X)
        (nMul_hasSubst F j).const]
    congr! 2 with s
    fin_cases s
    · exact ih
    · exact PowerSeries.subst_X (nMul_hasSubst F j)

open MvPowerSeries Finsupp in
private theorem coeff_one_subst_pair_X {R : Type*} [CommRing R] (F : FormalGroup R)
    {f : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (![f, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries : PowerSeries R) = PowerSeries.coeff 1 f + 1 := by
  have ha := _root_.GlobalTheory.ConvSer.nMul_hasSubst_pair hf PowerSeries.constantCoeff_X
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![PowerSeries.X * g, PowerSeries.X] :
      Fin 2 → MvPowerSeries Unit R) s ^ e) = PowerSeries.X ^ (d 0 + d 1) * g ^ d 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    show (PowerSeries.X * g) ^ d 0 * PowerSeries.X ^ d 1 = _
    ring
  have hcoeff : ∀ h : PowerSeries R, MvPowerSeries.coeff (single () 1) h = PowerSeries.coeff 1 h :=
    fun _ => rfl
  have hne : (single 0 1 : Fin 2 →₀ ℕ) ≠ single 1 1 := by
    intro h
    have := congrArg (fun d => d 0) h
    simp at this
  show MvPowerSeries.coeff (single () 1) _ = _
  rw [coeff_subst ha, finsum_eq_sum_of_support_subset (s := {single 0 1, single 1 1}),
    Finset.sum_pair hne]
  · simp only [hprod, hcoeff, F.3, F.4]
    simp
  · intro d hd
    simp only [Function.mem_support, hprod, hcoeff, PowerSeries.coeff_X_pow_mul'] at hd
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h2 : d 0 + d 1 ≤ 1
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h2 with h | h
      · exfalso
        apply hd
        have hd0 : d = 0 := Finsupp.ext fun i => by fin_cases i <;> simp <;> omega
        simp [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, F.2]
      · have h0 : d 0 ≤ 1 := by omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h0 | h0
        · right
          ext i
          fin_cases i <;> simp <;> omega
        · left
          ext i
          fin_cases i <;> simp <;> omega
    · exact absurd (by simp [h2]) hd

open MvPowerSeries Finsupp in

theorem _root_.GlobalTheory.ConvSer.nMul_props : ∀ (R : Type) [CommRing R] (F : FormalGroup R), (∀ n, PowerSeries.constantCoeff (_root_.GlobalTheory.ConvSer.nMul F n) = 0 ∧ PowerSeries.coeff 1 (_root_.GlobalTheory.ConvSer.nMul F n) = (n : R)) ∧ _root_.GlobalTheory.ConvSer.nMul F 1 = PowerSeries.X ∧ (∀ i j, MvPowerSeries.subst (![_root_.GlobalTheory.ConvSer.nMul F i, _root_.GlobalTheory.ConvSer.nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries = _root_.GlobalTheory.ConvSer.nMul F (i + j)) ∧ (∀ i j, (_root_.GlobalTheory.ConvSer.nMul F i).subst (_root_.GlobalTheory.ConvSer.nMul F j) = _root_.GlobalTheory.ConvSer.nMul F (i * j)) ∧ (∀ (S : Type) [CommRing S] (φ : R →+* S) (n : ℕ), PowerSeries.map φ (_root_.GlobalTheory.ConvSer.nMul F n) = _root_.GlobalTheory.ConvSer.nMul (F.map φ) n) := by
  intro R _ F
  have hc := _root_.GlobalTheory.ConvSer.nMul_constantCoeff F
  have hs : ∀ n, PowerSeries.HasSubst (_root_.GlobalTheory.ConvSer.nMul F n) :=
    fun n => PowerSeries.HasSubst.of_constantCoeff_zero' (hc n)
  have hX : PowerSeries.HasSubst (PowerSeries.X : PowerSeries R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' PowerSeries.constantCoeff_X
  have hadd : ∀ i j, MvPowerSeries.subst (![_root_.GlobalTheory.ConvSer.nMul F i,
      _root_.GlobalTheory.ConvSer.nMul F j] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries =
      _root_.GlobalTheory.ConvSer.nMul F (i + j) := by
    intro i j
    induction j with
    | zero =>
      rw [_root_.GlobalTheory.ConvSer.nMul_zero, Nat.add_zero]
      exact F.add_zero (hs i)
    | succ j ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ F j, show i + (j + 1) = (i + j) + 1 by omega,
        _root_.GlobalTheory.ConvSer.nMul_succ F (i + j), ← ih]
      exact (F.assoc' (hs i) (hs j) hX).symm
  refine ⟨fun n => ⟨hc n, ?_⟩, ?_, hadd, ?_, ?_⟩
  · induction n with
    | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
    | succ n ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ, coeff_one_subst_pair_X F (hc n), ih]
      push_cast
      rfl
  · rw [_root_.GlobalTheory.ConvSer.nMul_succ, _root_.GlobalTheory.ConvSer.nMul_zero]
    exact F.zero_add hX
  · intro i j
    induction i with
    | zero =>
      rw [_root_.GlobalTheory.ConvSer.nMul_zero, Nat.zero_mul, _root_.GlobalTheory.ConvSer.nMul_zero,
        ← PowerSeries.coe_substAlgHom (hs j), map_zero]
    | succ i ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ F i, Nat.succ_mul, ← hadd (i * j) j, ← ih]
      show MvPowerSeries.subst (fun _ => _root_.GlobalTheory.ConvSer.nMul F j) _ = _
      rw [MvPowerSeries.subst_comp_subst_apply
        (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair (hc i) PowerSeries.constantCoeff_X)
        (hasSubst_of_constantCoeff_zero fun _ => hc j)]
      congr 1
      funext s
      fin_cases s
      · rfl
      · exact PowerSeries.subst_X (hs j)
  · intro S _ φ n
    induction n with
    | zero => simp [_root_.GlobalTheory.ConvSer.nMul_zero]
    | succ n ih =>
      rw [_root_.GlobalTheory.ConvSer.nMul_succ, _root_.GlobalTheory.ConvSer.nMul_succ, FormalGroup.map_toPowerSeries,
        ← ih]
      show MvPowerSeries.map φ _ = _
      rw [MvPowerSeries.map_subst
        (_root_.GlobalTheory.ConvSer.nMul_hasSubst_pair (hc n) PowerSeries.constantCoeff_X)]
      congr 1
      funext s
      fin_cases s
      · rfl
      · exact PowerSeries.map_X φ

end GlobalTheory.ConvSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvSqLeWignerCoeffSqLowering
section
open Finset

noncomputable section

namespace GlobalTheory.WigSh.LowerBound

private theorem prod_erase_succAbove {n : ℕ} (f : Fin (n + 1) → ℝ) (l : Fin (n + 1)) :
    ∏ j ∈ univ.erase l, f j = ∏ j : Fin n, f (l.succAbove j) := by
  rw [← Finset.compl_singleton, ← Fin.image_succAbove_univ]
  · rw [Finset.prod_image]
    intro a _ b _ hab
    exact Fin.succAbove_right_injective hab

private theorem ratio_pos_case {a b c : ℝ} (hb : 0 < b) (h : c ≤ a) :
    c * b / b ^ 2 ≤ a / b := by
  have : c * b / b ^ 2 = c / b := by field_simp
  rw [this]
  exact div_le_div_of_nonneg_right h hb.le

private theorem factor_lower {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (l : Fin (n + 1))
    (hs : StrictAnti L) (j : Fin n) (h1 : L j.succ < M j) (h2 : M j ≤ L j.castSucc)
    (h3 : M j ≠ L l) (G : Fin (n + 1) → ℤ)
    (hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i))) :
    (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2 ≤
      ((M j : ℝ) - L l) / ((L (l.succAbove j) : ℝ) - L l) := by
  have g1 := hG j.succ
  have g2 := hG j.castSucc
  rcases lt_or_ge j.castSucc l with hl | hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ hl]
    have a1 : L l < L j.castSucc := hs hl
    have a2 : L l ≤ L j.succ := hs.antitone (Fin.castSucc_lt_iff_succ_le.1 hl)
    have e : G j.castSucc = L j.castSucc - L l := by omega
    have e' : (L j.castSucc : ℝ) - L l = G j.castSucc := by rw [e]; push_cast; ring
    rw [e']
    apply ratio_pos_case
    · have : (0 : ℤ) < G j.castSucc := by omega
      exact_mod_cast this
    · have : G j.succ ≤ M j - L l := by omega
      exact_mod_cast this
  · rw [Fin.succAbove_of_le_castSucc _ _ hl]
    have a2 : L j.castSucc ≤ L l := hs.antitone hl
    have e : G j.succ = L l - L j.succ := by omega
    have e' : (L j.succ : ℝ) - L l = -G j.succ := by rw [e]; push_cast; ring
    rw [e', div_neg, ← neg_div, mul_comm]
    apply ratio_pos_case
    · have : (0 : ℤ) < G j.succ := by omega
      exact_mod_cast this
    · have : G j.castSucc ≤ -(M j - L l) := by omega
      exact_mod_cast this

end GlobalTheory.WigSh.LowerBound

namespace GlobalTheory.WigSh

open LowerBound

theorem inv_sq_le_wM (n : ℕ) (L : Fin (n+1) → ℤ) (M : Fin n → ℤ) (l : Fin (n+1)) (D : ℝ)
    (hs : StrictAnti L) (hbox : ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc)
    (hne : ∀ j, M j ≠ L l) (hD : 1 ≤ D) (h0 : (L 0 : ℝ) - L l ≤ D)
    (hlast : (L l : ℝ) - L (Fin.last n) ≤ D) : (D ^ 2)⁻¹ ≤ GlobalTheory.WigSh.wM L M l := by
  set G : Fin (n + 1) → ℤ := fun i => max 1 (max (L i - L l) (L l - L i)) with hGdef
  have hG : ∀ i, G i = max 1 (max (L i - L l) (L l - L i)) := fun i => rfl
  have hpos : ∀ i, (0 : ℝ) < G i := fun i => by
    have : (0 : ℤ) < G i := by rw [hG]; omega
    exact_mod_cast this
  have hl : G l = 1 := by rw [hG]; omega
  have hG0 : (G 0 : ℝ) ≤ D := by
    have a : L l ≤ L 0 := hs.antitone (Fin.zero_le l)
    have : G 0 = 1 ∨ G 0 = L 0 - L l := by rw [hG]; omega
    rcases this with e | e <;> rw [e] <;> push_cast <;> assumption
  have hGl : (G (Fin.last n) : ℝ) ≤ D := by
    have a : L (Fin.last n) ≤ L l := hs.antitone (Fin.le_last l)
    have : G (Fin.last n) = 1 ∨ G (Fin.last n) = L l - L (Fin.last n) := by rw [hG]; omega
    rcases this with e | e <;> rw [e] <;> push_cast <;> assumption
  set P : ℝ := ∏ i, (G i : ℝ) with hP
  have hPpos : 0 < P := Finset.prod_pos fun i _ => hpos i
  have p1 : ∏ j : Fin n, (G j.succ : ℝ) = P / G 0 := by
    rw [eq_div_iff (hpos 0).ne', hP, Fin.prod_univ_succ, mul_comm]
  have p2 : ∏ j : Fin n, (G j.castSucc : ℝ) = P / G (Fin.last n) := by
    rw [eq_div_iff (hpos _).ne', hP, Fin.prod_univ_castSucc]
  have p3 : ∏ j : Fin n, (G (l.succAbove j) : ℝ) = P := by
    rw [hP, Fin.prod_univ_succAbove _ l, hl]; simp
  unfold wM
  rw [prod_erase_succAbove, ← Finset.prod_div_distrib]
  refine le_trans ?_ (Finset.prod_le_prod
    (f := fun j : Fin n => (G j.succ : ℝ) * G j.castSucc / (G (l.succAbove j) : ℝ) ^ 2)
    (fun j _ => ?_) (fun j _ => factor_lower l hs j (hbox j).1 (hbox j).2 (hne j) G hG))
  · rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_pow, p1, p2, p3]
    have q0 := hpos 0
    have ql := hpos (Fin.last n)
    have : P / G 0 * (P / G (Fin.last n)) / P ^ 2 = ((G 0 : ℝ) * G (Fin.last n))⁻¹ := by
      field_simp
    rw [this]
    apply inv_anti₀ (mul_pos q0 ql)
    rw [sq]
    exact mul_le_mul hG0 hGl ql.le (by linarith)
  · have := hpos j.succ
    have := hpos j.castSucc
    positivity

end GlobalTheory.WigSh
end
end

