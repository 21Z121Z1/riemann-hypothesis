import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSolFiltered
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

open PowerSeries

namespace GlobalTheory.ExpImage

noncomputable def triSol {R : Type*} [CommRing R] (M : ℕ → ℕ → R) (g : ℕ → R) (n : ℕ) : R :=
  Ring.inverse (M n n) * (g n - ∑ i : Fin n, M n i * triSol M g i)
decreasing_by exact i.2

open PowerSeries in
private lemma constantCoeff_coeff_one_one_add_X_pow {R : Type*} [CommRing R] (N : ℕ) :
    constantCoeff ((1 + X : R⟦X⟧) ^ N) = 1 ∧ coeff 1 ((1 + X : R⟦X⟧) ^ N) = N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (1 + X : R⟦X⟧) ^ (N + 1) = (1 + X) ^ N + X * (1 + X) ^ N := by ring
    have h1 : coeff 1 (X * (1 + X : R⟦X⟧) ^ N) = constantCoeff ((1 + X : R⟦X⟧) ^ N) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
    refine ⟨?_, ?_⟩
    · rw [e, map_add, ih.1, map_mul, constantCoeff_X, zero_mul, add_zero]
    · rw [e, map_add, ih.2, h1, ih.1]
      push_cast
      ring

open PowerSeries in
private lemma isUnit_padicInt_of_not_dvd' {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) (hz : ¬ (l : ℤ_[l]) ∣ z) :
    IsUnit z :=
  PadicInt.isUnit_iff.2 (le_antisymm (PadicInt.norm_le_one z)
    (not_lt.1 fun h => hz ((PadicInt.norm_lt_one_iff_dvd z).1 h)))

open PowerSeries in
private lemma toZMod_eq_zero_iff_dvd {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) :
    PadicInt.toZMod z = 0 ↔ (l : ℤ_[l]) ∣ z := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

open PowerSeries in
private lemma three_le_prime_pow {l s : ℕ} (hl : l.Prime) (hs : 1 ≤ s) (h2 : l = 2 → 2 ≤ s) :
    3 ≤ l ^ s := by
  rcases hl.eq_two_or_odd' with rfl | hodd
  · calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (h2 rfl)
  · have h3 : 3 ≤ l := by
      have := hl.two_le
      rcases hodd with ⟨r, hr⟩
      omega
    calc 3 ≤ l := h3
      _ = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ s := Nat.pow_le_pow_right hl.pos hs

open PowerSeries in
private lemma coeff_one_mul_one_add_X_sq_mul_pow {R : Type*} [CommRing R] (f w : R⟦X⟧) (n : ℕ) :
    coeff 1 (f * (1 + X ^ 2 * w) ^ n) = coeff 1 f := by
  obtain ⟨q, hq⟩ : X ^ 2 ∣ (1 + X ^ 2 * w) ^ n - 1 ^ n := by
    have := sub_dvd_pow_sub_pow (1 + X ^ 2 * w) 1 n
    rw [add_sub_cancel_left] at this
    exact (dvd_mul_right _ _).trans this
  have e : f * (1 + X ^ 2 * w) ^ n = f + X ^ 2 * (f * q) := by
    rw [one_pow] at hq
    linear_combination f * hq
  rw [e, map_add, X_pow_dvd_iff.1 (dvd_mul_right _ _) 1 (by norm_num), add_zero]

open PowerSeries in
private lemma sum_mul_triSol_eq {R : Type*} [CommRing R] (M : ℕ → ℕ → R)
    (g : ℕ → R) (n : ℕ) (hn : IsUnit (M n n)) :
    ∑ i ∈ Finset.range (n + 1), M n i * _root_.GlobalTheory.ExpImage.triSol M g i = g n := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range (fun i => M n i *
    _root_.GlobalTheory.ExpImage.triSol M g i) n]
  conv_lhs => rw [_root_.GlobalTheory.ExpImage.triSol]
  rw [← mul_assoc, Ring.mul_inverse_cancel _ hn, one_mul]
  ring

open PowerSeries in

theorem _root_.GlobalTheory.ExpImage.solve_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (s : ℕ), _root_.GlobalTheory.Cyc.Lev l s →
    ∀ (m : ℕ), ¬ l ∣ m → ∀ U : ℤ_[l], (l : ℤ_[l]) ^ s ∣ U - 1 →
    ∀ (γ : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] PowerSeries ℤ_[l]) (v : PowerSeries ℤ_[l]),
    PowerSeries.X * v = (1 + PowerSeries.X) ^ (1 + l ^ s) - 1 →
    γ PowerSeries.X = PowerSeries.X * v → ∀ (k : ℕ) (F : PowerSeries ℤ_[l]),
    ∃ p F' : PowerSeries ℤ_[l], PowerSeries.C U * (1 + PowerSeries.X) ^ m * γ p - v ^ k * p =
      v ^ k * (PowerSeries.X * F - (l : PowerSeries ℤ_[l]) ^ s * F') := by
  intro l _ s hs m hm U hU γ v hv hγ k F
  obtain ⟨hs1, hs2⟩ : 1 ≤ s ∧ (l = 2 → 2 ≤ s) := by
    unfold _root_.GlobalTheory.Cyc.Lev at hs
    exact hs
  have hlp : l.Prime := Fact.out

  let T : PowerSeries ℤ_[l] →ₗ[ℤ_[l]] PowerSeries ℤ_[l] :=
    LinearMap.mulLeft ℤ_[l] (C U * (1 + X) ^ m) ∘ₗ γ.toLinearMap -
      LinearMap.mulLeft ℤ_[l] (v ^ k)
  have hT : ∀ f, T f = C U * (1 + X) ^ m * γ f - v ^ k * f := fun f => rfl
  have hTX : ∀ i : ℕ, T (X ^ i) = (C U * (1 + X) ^ m * v ^ i - v ^ k) * X ^ i := by
    intro i
    rw [hT, map_pow, hγ]
    ring

  have hloc : ∀ f g : PowerSeries ℤ_[l], ∀ j : ℕ, (∀ i < j + 1, coeff i f = coeff i g) →
      coeff j (T f) = coeff j (T g) := by
    intro f g j h
    obtain ⟨q, hq⟩ : X ^ (j + 1) ∣ f - g :=
      X_pow_dvd_iff.2 fun i hi => by rw [map_sub, h i hi, sub_self]
    have e : T f - T g = X ^ (j + 1) * (C U * (1 + X) ^ m * v ^ (j + 1) * γ q - v ^ k * q) := by
      rw [← map_sub, hq, hT, map_mul, map_pow, hγ]
      ring
    have h2 : coeff j (T f - T g) = 0 := by
      rw [e]
      exact X_pow_dvd_iff.1 (dvd_mul_right _ _) j (Nat.lt_succ_self j)
    rwa [map_sub, sub_eq_zero] at h2
  have hsum : ∀ (c : ℕ → ℤ_[l]) (j : ℕ),
      coeff j (T (mk c)) = ∑ i ∈ Finset.range (j + 1), c i * coeff j (T (X ^ i)) := by
    intro c j
    rw [hloc (mk c) (∑ i ∈ Finset.range (j + 1), c i • X ^ i) j]
    · simp [map_sum, map_smul]
    · intro i hi
      simp [coeff_mk, map_sum, coeff_X_pow, Finset.mem_range.2 hi]

  have hv0 : constantCoeff v = 1 + (l : ℤ_[l]) ^ s := by
    have h := congrArg (coeff 1) hv
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      map_sub, (constantCoeff_coeff_one_one_add_X_pow (R := ℤ_[l]) (1 + l ^ s)).2] at h
    rw [h]
    simp
  have hunitv : IsUnit v := by
    rw [isUnit_iff_constantCoeff, hv0]
    refine isUnit_padicInt_of_not_dvd' _ fun hd => ?_
    have h1 : (l : ℤ_[l]) ∣ 1 :=
      (dvd_add_left (dvd_pow_self (l : ℤ_[l]) (by omega : s ≠ 0))).1 hd
    have hn := PadicInt.isUnit_iff.1 (isUnit_of_dvd_one h1)
    have h2 := (PadicInt.norm_lt_one_iff_dvd (l : ℤ_[l])).2 dvd_rfl
    linarith

  have hdiag : ∀ i : ℕ, (l : ℤ_[l]) ^ s ∣ coeff i (T (X ^ i)) := by
    intro i
    have e := coeff_mul_X_pow (C U * (1 + X) ^ m * v ^ i - v ^ k) i 0
    rw [zero_add] at e
    rw [hTX, e, coeff_zero_eq_constantCoeff_apply]
    simp only [map_sub, map_mul, map_pow, constantCoeff_C, hv0,
      (constantCoeff_coeff_one_one_add_X_pow (R := ℤ_[l]) m).1, mul_one]
    have ha : ∀ n : ℕ, (l : ℤ_[l]) ^ s ∣ (1 + (l : ℤ_[l]) ^ s) ^ n - 1 := fun n => by
      simpa using sub_dvd_pow_sub_pow (1 + (l : ℤ_[l]) ^ s) 1 n
    have e2 : U * (1 + (l : ℤ_[l]) ^ s) ^ i - (1 + (l : ℤ_[l]) ^ s) ^ k =
        (U - 1) * (1 + (l : ℤ_[l]) ^ s) ^ i + ((1 + (l : ℤ_[l]) ^ s) ^ i - 1) -
          ((1 + (l : ℤ_[l]) ^ s) ^ k - 1) := by ring
    rw [e2]
    exact dvd_sub (dvd_add (dvd_mul_of_dvd_left hU _) (ha i)) (ha k)

  have hsub : ∀ n : ℕ, IsUnit (coeff (n + 1) (T (X ^ n))) := by
    intro n
    refine isUnit_padicInt_of_not_dvd' _ fun hd => hm ?_
    rw [← toZMod_eq_zero_iff_dvd] at hd
    haveI : CharP (PowerSeries (ZMod l)) l :=
      charP_of_injective_ringHom (PowerSeries.C_injective (R := ZMod l)) l
    obtain ⟨t, ht⟩ : ∃ t, l ^ s = t + 3 := ⟨l ^ s - 3, by have := three_le_prime_pow hlp hs1 hs2; omega⟩
    have hvb : PowerSeries.map PadicInt.toZMod v = 1 + X ^ 2 * (X ^ t * (1 + X)) := by
      apply X_mul_cancel
      have h := congrArg (PowerSeries.map (PadicInt.toZMod (p := l))) hv
      simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X] at h
      rw [h, pow_add, pow_one, add_pow_char_pow (1 : PowerSeries (ZMod l)) X l s, one_pow, ht]
      ring
    have hU1 : PadicInt.toZMod U = 1 := by
      have : PadicInt.toZMod (U - 1) = 0 := (toZMod_eq_zero_iff_dvd _).2
        ((dvd_pow_self (l : ℤ_[l]) (by omega : s ≠ 0)).trans hU)
      rwa [map_sub, map_one, sub_eq_zero] at this
    have hcomp : PadicInt.toZMod (coeff (n + 1) (T (X ^ n))) = (m : ZMod l) := by
      rw [← coeff_map, hTX, add_comm n 1]
      simp only [map_mul, map_sub, map_pow, map_add, map_one, PowerSeries.map_X,
        PowerSeries.map_C, hU1, one_mul]
      rw [coeff_mul_X_pow, hvb, map_sub, coeff_one_mul_one_add_X_sq_mul_pow,
        show ((1 : PowerSeries (ZMod l)) + X ^ 2 * (X ^ t * (1 + X))) ^ k =
          1 * (1 + X ^ 2 * (X ^ t * (1 + X))) ^ k by rw [one_mul],
        coeff_one_mul_one_add_X_sq_mul_pow, (constantCoeff_coeff_one_one_add_X_pow m).2]
      simp
    rw [hcomp] at hd
    exact (ZMod.natCast_eq_zero_iff m l).1 hd
  let g : ℕ → ℤ_[l] := fun j => coeff j (v ^ k * (X * F))
  let c : ℕ → ℤ_[l] := _root_.GlobalTheory.ExpImage.triSol (fun n i => coeff (n + 1) (T (X ^ i)))
    (fun n => g (n + 1))
  have hcoef : ∀ j : ℕ, (l : ℤ_[l]) ^ s ∣ coeff j (T (mk c) - v ^ k * (X * F)) := by
    intro j
    rw [map_sub, hsum]
    cases j with
    | zero =>
      have h0 : coeff 0 (v ^ k * (X * F)) = 0 := by
        simp [coeff_zero_eq_constantCoeff_apply]
      rw [h0, sub_zero, Finset.sum_range_one]
      exact dvd_mul_of_dvd_right (hdiag 0) _
    | succ n =>
      have hs' := sum_mul_triSol_eq (fun n i => coeff (n + 1) (T (X ^ i)))
        (fun n => g (n + 1)) n (hsub n)
      rw [Finset.sum_range_succ]
      convert dvd_mul_of_dvd_right (hdiag (n + 1)) (c (n + 1)) using 1
      simp only [g, c] at hs' ⊢
      rw [← hs', Finset.sum_congr rfl fun i _ => mul_comm _ _]
      ring
  let E : PowerSeries ℤ_[l] := mk fun j => (hcoef j).choose
  have hE : T (mk c) - v ^ k * (X * F) = C ((l : ℤ_[l]) ^ s) * E := by
    ext j
    rw [coeff_C_mul, coeff_mk]
    exact (hcoef j).choose_spec
  obtain ⟨u, hu⟩ := hunitv.pow k
  refine ⟨mk c, -(↑u⁻¹ * E), ?_⟩
  have hE' : T (mk c) = v ^ k * (X * F) + C ((l : ℤ_[l]) ^ s) * E := by
    rw [← hE]; ring
  rw [← hT, hE']
  have hl : (l : PowerSeries ℤ_[l]) ^ s = C ((l : ℤ_[l]) ^ s) := by simp
  rw [hl, ← hu]
  have : (u : PowerSeries ℤ_[l]) * ↑u⁻¹ = 1 := Units.mul_inv u
  linear_combination (-(C ((l : ℤ_[l]) ^ s) * E)) * this

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStableLatticeCompactGroup
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.StableLat

theorem exists_lattice : ∀ {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] {Qp LL O : Type} [Field Qp] [TopologicalSpace Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O), Nonempty (Lattice (O := O) A.ρ) := by
  intro G _ _ _ Qp LL O _ _ _ _ _ _ _ hO A
  classical
  obtain ⟨⟨hDom, hDVR, hFrac⟩, -, -, hTop, hOpen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFrac; haveI := hTop
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL

  let e := Module.finBasis LL A.V
  let n := Module.finrank LL A.V
  let T₀ : Submodule O A.V := Submodule.span O (Set.range e)
  have hT₀fg : T₀.FG := Submodule.fg_span (Set.finite_range e)
  have hT₀span : Submodule.span LL (T₀ : Set A.V) = ⊤ := by
    simp only [T₀, Submodule.span_span_of_tower, e.span_eq]
  have hT₀open : IsOpen (T₀ : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hOpen T₀ hT₀fg hT₀span

  have hcov : ∀ x : A.V, ∃ b : nonZeroDivisors O, (b : O) • x ∈ T₀ := by
    intro x
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ
      (fun i => e.repr x i)
    refine ⟨b, ?_⟩
    have hx : (b : O) • x = ∑ i, (b : O) • (e.repr x i • e i) := by
      rw [← Finset.smul_sum, e.sum_repr]
    rw [hx]
    refine T₀.sum_mem fun i _ => ?_
    obtain ⟨a, ha⟩ := hb i (Finset.mem_univ i)
    rw [← smul_assoc, ← ha, algebraMap_smul]
    exact T₀.smul_mem a (Submodule.subset_span ⟨i, rfl⟩)

  let C : Set A.V := ⋃ i, Set.range fun g : G => A.ρ g (e i)
  have hC : IsCompact C := isCompact_iUnion fun i => isCompact_range (A.cont (e i))
  let U : nonZeroDivisors O → Set A.V := fun b => (fun x => (b : O) • x) ⁻¹' (T₀ : Set A.V)
  have hU : ∀ b, IsOpen (U b) := by
    intro b
    have : (fun x : A.V => (b : O) • x) = fun x => algebraMap O LL b • x := by
      funext x; rw [algebraMap_smul]
    exact hT₀open.preimage (this ▸ continuous_const_smul _)
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hU (fun x _ => by
    obtain ⟨b, hb⟩ := hcov x; exact Set.mem_iUnion.2 ⟨b, hb⟩)
  let b : O := ∏ c ∈ t, (c : O)
  have hb0 : b ∈ nonZeroDivisors O := by
    simpa [b] using (∏ c ∈ t, c).2
  have hbC : ∀ y ∈ C, b • y ∈ T₀ := by
    intro y hy
    obtain ⟨c, hct, hc⟩ := Set.mem_iUnion₂.1 (ht hy)
    have : b = (∏ d ∈ t.erase c, (d : O)) * c := by
      simp only [b]; rw [← Finset.prod_erase_mul _ _ hct]
    rw [this, mul_smul]
    exact T₀.smul_mem _ hc

  let T : Submodule O A.V := Submodule.span O C
  have hCT : C ⊆ T := Submodule.subset_span
  have hstable : ∀ g, ∀ x ∈ T, A.ρ g x ∈ T := by
    intro g x hx
    have hle : T ≤ T.comap ((A.ρ g).restrictScalars O) := by
      refine Submodule.span_le.2 ?_
      intro y hy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
      obtain ⟨h, rfl⟩ := hi
      show A.ρ g (A.ρ h (e i)) ∈ T
      rw [← Module.End.mul_apply, ← map_mul]
      exact hCT (Set.mem_iUnion.2 ⟨i, g * h, rfl⟩)
    exact hle hx

  let f : A.V →ₗ[O] A.V := b • LinearMap.id
  have hbne : algebraMap O LL b ≠ 0 := by
    intro h
    exact nonZeroDivisors.ne_zero hb0 (hinj (by rw [h, map_zero]))
  have hf : Function.Injective f := by
    intro x y hxy
    have : algebraMap O LL b • x = algebraMap O LL b • y := by
      simpa [f, algebraMap_smul] using hxy
    exact smul_right_injective A.V hbne this
  have hfT : T.map f ≤ T₀ := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 fun y hy => ?_
    simpa [f] using hbC y hy
  have hTfg : T.FG := Submodule.fg_of_fg_map_injective f hf (Submodule.FG.of_le hT₀fg hfT)
  haveI : NoZeroSMulDivisors O A.V := ⟨fun {c x} h => by
    rw [← algebraMap_smul LL c x] at h
    rcases smul_eq_zero.1 h with h | h
    · left; exact hinj (by rw [h, map_zero])
    · right; exact h⟩
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hTfg
  have hfree : Module.Free O T := Module.free_of_finite_type_torsion_free'
  have hspan : Submodule.span LL (T : Set A.V) = ⊤ := by
    rw [eq_top_iff, ← e.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span (hCT (Set.mem_iUnion.2 ⟨i, 1, ?_⟩))
    simp
  exact ⟨⟨T, hstable, hTfg, hfree, hspan⟩⟩

end GlobalTheory.StableLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperMulInc
section
open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLp

theorem exists_upper_mul_inc : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (h : GL (Fin n) ℚ_[g]), ∃ (p : GL (Fin n) ℚ_[g]) (k : GL (Fin n) ℤ_[g]), (∀ i j : Fin n, j < i → (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j = 0) ∧ h = p * inc g n k := by
  intro g hg n h
  have hdet : ((h⁻¹ : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)).ne_zero
  obtain ⟨k, U, hk, hU, -, hA⟩ := Formalism.L2.Pj.iwasawa (V := ℤ_[g]) _ hdet

  have hUdet : IsUnit U.det := by
    rw [hA, Matrix.det_mul] at hdet
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  let K : GL (Fin n) ℤ_[g] := ((Matrix.isUnit_iff_isUnit_det k).mpr hk).unit
  have hinc : ((inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) =
      k.map (algebraMap ℤ_[g] ℚ_[g]) := rfl
  refine ⟨h * inc g n K, K⁻¹, ?_, ?_⟩
  · intro i j hij
    have e1 : ((h * inc g n K : GL (Fin n) ℚ_[g]) : Matrix (Fin n) (Fin n) ℚ_[g]) = U⁻¹ := by
      rw [Units.val_mul, hinc]
      calc (h : Matrix (Fin n) (Fin n) ℚ_[g]) * k.map (algebraMap ℤ_[g] ℚ_[g])
          = (h : Matrix (Fin n) (Fin n) ℚ_[g]) * (k.map (algebraMap ℤ_[g] ℚ_[g]) * U) * U⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv U hUdet, Matrix.mul_one]
        _ = U⁻¹ := by rw [← hA, Units.mul_inv, Matrix.one_mul]
    rw [e1]
    haveI := Matrix.invertibleOfIsUnitDet U hUdet
    exact Matrix.blockTriangular_inv_of_blockTriangular hU hij
  · rw [map_inv, mul_inv_cancel_right]

end GlobalTheory.GLp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedMemRange
section
open Polynomial

namespace GlobalTheory.FixedMemRange

theorem fixed_mem_range {g : ℕ} [hg : Fact (Nat.Prime g)] {d : ℕ} (hd : 0 < d)
    {w : AlgebraicClosure (ZMod g)} (hw : w ^ g ^ d = w) :
    ∃ k : GaloisField g d,
      ((IsAlgClosed.lift : GaloisField g d →ₐ[ZMod g] AlgebraicClosure (ZMod g)) : GaloisField g d → AlgebraicClosure (ZMod g)) k = w := by
  classical
  set ι : GaloisField g d →ₐ[ZMod g] AlgebraicClosure (ZMod g) := IsAlgClosed.lift with hι
  letI : Fintype (GaloisField g d) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField g d) = g ^ d := by rw [Fintype.card_eq_nat_card]; exact GaloisField.card g d hd.ne'
  have hq : 1 < g ^ d := Nat.one_lt_pow hd.ne' hg.out.one_lt
  set P : (AlgebraicClosure (ZMod g))[X] := X ^ (g ^ d) - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hq
  have hPdeg : P.natDegree = g ^ d := FiniteField.X_pow_card_sub_X_natDegree_eq _ hq
  have hsub : Finset.univ.image ι ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
    rw [Multiset.mem_toFinset, mem_roots hP0]
    have hk : k ^ g ^ d = k := by
      rw [← hcard]; exact FiniteField.pow_card k
    simp [hP, IsRoot, sub_eq_zero, ← map_pow, hk]
  have hle : P.roots.toFinset.card ≤ (Finset.univ.image ι).card := by
    have hinj : Function.Injective ι := fun a b h => (RingHom.injective ι.toRingHom) h
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard, ← hPdeg]
    exact (Multiset.toFinset_card_le _).trans (card_roots' P)
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have hwm : w ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hP0]
    simp [hP, IsRoot, sub_eq_zero, hw]
  rw [← heq] at hwm
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hwm
  exact ⟨k, hk⟩

theorem main : (let d1 : (g : ℕ) → ℕ → [Fact (Nat.Prime g)] → Type := @(fun (g d : ℕ) [Fact (Nat.Prime g)] ↦ GaloisField g d); let d2 : (g d : ℕ) → [inst : Fact (Nat.Prime g)] → d1 g d →ₐ[ZMod g] Formalism.CyclotomicNorms.Fbar g := @(fun (g d : ℕ) [Fact (Nat.Prime g)] ↦ IsAlgClosed.lift); ∀ {g : ℕ} [hg : Fact (Nat.Prime g)] {d : ℕ}, (0 : ℕ) < d → ∀ {w : Formalism.CyclotomicNorms.Fbar g}, w ^ g ^ d = w → ∃ (k : d1 g d), (d2 g d : d1 g d → Formalism.CyclotomicNorms.Fbar g) k = w) := by
  intro d1 d2 g hg d hd w hw
  exact fixed_mem_range hd hw

end GlobalTheory.FixedMemRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrKIsometricAndOneSubSurjective
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime]

theorem norm_algHom_self (F : IntermediateField ℚ_[l] (Om l)) (σ : ↥F →ₐ[ℚ_[l]] ↥F) (c : ↥F) :
    ‖((σ c : ↥F) : Om l)‖ = ‖(c : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  unfold spectralNorm
  have h1 := minpoly.algHom_eq F.val F.val.injective (σ c)
  have h2 := minpoly.algHom_eq F.val F.val.injective c
  have h3 := minpoly.algHom_eq σ σ.injective c
  simp only [IntermediateField.coe_val] at h1 h2
  exact congrArg spectralValue (h1.trans (h3.trans h2.symm))

theorem norm_l_pow_lt_one {j : ℕ} (hj : 1 ≤ j) : ‖(l : Om l) ^ j‖ < 1 := by
  rw [norm_pow]
  apply pow_lt_one₀ (norm_nonneg _) _ (by omega)
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem norm_sub_pow_mul_algHom (F : IntermediateField ℚ_[l] (Om l)) (σ : ↥F →ₐ[ℚ_[l]] ↥F)
    {j : ℕ} (hj : 1 ≤ j) (d : ↥F) :
    ‖((d - (l : ↥F) ^ j * σ d : ↥F) : Om l)‖ = ‖(d : Om l)‖ := by
  by_cases hd : d = 0
  · simp [hd]
  have hd' : 0 < ‖(d : Om l)‖ := norm_pos_iff.2 (by exact_mod_cast hd)
  have hlt : ‖-((l : Om l) ^ j * ((σ d : ↥F) : Om l))‖ < ‖(d : Om l)‖ := by
    rw [norm_neg, norm_mul, norm_algHom_self]
    exact mul_lt_of_lt_one_left hd' (norm_l_pow_lt_one hj)
  have e : ((d - (l : ↥F) ^ j * σ d : ↥F) : Om l) =
      (d : Om l) + -((l : Om l) ^ j * ((σ d : ↥F) : Om l)) := by
    push_cast
    ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

theorem frK_isometric_and_one_sub_surjective (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) :
    (∀ c : ↥(K0 K), ‖((frK P K c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖) ∧
    ∀ j : ℕ, 1 ≤ j → ∀ c : ↥(K0 K), ‖(c : Om l)‖ ≤ 1 →
      ∃ d : ↥(K0 K), ‖(d : Om l)‖ ≤ 1 ∧ d - (l : ↥(K0 K)) ^ j * frK P K d = c := by
  refine ⟨norm_algHom_self _ _, fun j hj c hc => ?_⟩
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  let T : ↥(K0 K) →ₗ[ℚ_[l]] ↥(K0 K) :=
    LinearMap.id - (LinearMap.mulLeft ℚ_[l] ((l : ↥(K0 K)) ^ j)).comp (frK P K).toLinearMap
  have hT : ∀ d, T d = d - (l : ↥(K0 K)) ^ j * frK P K d := fun d => rfl
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    have := norm_sub_pow_mul_algHom _ (frK P K) hj d
    rw [← hT, hd] at this
    have h0 : (d : Om l) = 0 := by
      rw [← norm_eq_zero, ← this]; simp
    exact_mod_cast h0
  obtain ⟨d, hd⟩ := LinearMap.injective_iff_surjective.1 hinj c
  rw [hT] at hd
  refine ⟨d, ?_, hd⟩
  rw [← norm_sub_pow_mul_algHom _ (frK P K) hj d, hd]
  exact hc

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodORingOfIntegers
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem goodO_ringOfIntegers :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  fun l _ LL => (GlobalTheory.LocalIntegers.good_integers l LL).1

end GlobalTheory.Pass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree : ∀ (G : Type) [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (χ : G → ℂ), (a * a = a → IsChar χ → ∃ n : ℕ, tr a χ = n) ∧ (IsIrr χ → ∃ d : ℕ, 0 < d ∧ χ 1 = d) ∧ (a * zOf χ).coeff 1 = χ 1 / (Fintype.card G : ℂ) * tr a χ := by
  first | exact @GlobalTheory.GLq.trIdem | exact GlobalTheory.GLq.trIdem | (intros; apply GlobalTheory.GLq.trIdem <;> assumption)
end

