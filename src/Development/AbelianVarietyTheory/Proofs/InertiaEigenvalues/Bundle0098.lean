import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ProjectionSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0084
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0075
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.HeckeFlatSpecialisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0057
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeSmulMem
section
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Gauge
section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
theorem _root_.GlobalTheory.PhiGam.Gauge.phi_sh {l : ℕ} (R : _root_.GlobalTheory.PhiGam.RingPG k l)
    (f : V →ₗ[k] V) (hf : _root_.GlobalTheory.PhiGam.Semi R.φ f)
    (N N' : Submodule k⟦X⟧ V) (w : ℤ)
    (h : _root_.GlobalTheory.PhiGam.pull f N' ≤ _root_.GlobalTheory.PhiGam.sh (-w) N) (m : ℕ) {x : V}
    (hx : x ∈ _root_.GlobalTheory.PhiGam.sh m N') :
    f x ∈ _root_.GlobalTheory.PhiGam.sh (l * m - w) N := by
  obtain ⟨y, hy, rfl⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.1 hx
  obtain ⟨u, hu⟩ := R.φ_v
  have hfy : f y ∈ _root_.GlobalTheory.PhiGam.sh (-w) N := h (Submodule.subset_span ⟨y, hy, rfl⟩)
  obtain ⟨z, hz, hz'⟩ := _root_.GlobalTheory.PhiGam.mem_sh_iff_exists.1 hfy
  rw [_root_.GlobalTheory.PhiGam.mem_sh_iff_exists]
  refine ⟨((u : k⟦X⟧) ^ m) • z, N.smul_mem _ hz, ?_⟩
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  rw [zpow_natCast, hf, map_pow, hu, ← hz', ← algebraMap_smul k⸨X⸩ ((u : k⟦X⟧) ^ m) z, smul_smul,
    smul_smul, LaurentSeries.coe_algebraMap, map_pow, sub_eq_add_neg, zpow_add₀ hX, mul_pow, ← pow_mul]
  congr 1
  rw [show ((l : ℤ) * (m : ℤ)) = ((l * m : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  ring

end

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
private theorem vv_smul_mem_sh_succ_iff (a : ℤ) (N : Submodule k⟦X⟧ V) (y : V) :
    _root_.GlobalTheory.PhiGam.vv k • y ∈ _root_.GlobalTheory.PhiGam.sh (a + 1) N ↔
      y ∈ _root_.GlobalTheory.PhiGam.sh a N := by
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  rw [_root_.GlobalTheory.PhiGam.mem_sh_iff_smul_mem, _root_.GlobalTheory.PhiGam.mem_sh_iff_smul_mem, smul_smul, ← zpow_add_one₀ hX]
  rw [show -(a + 1) + 1 = -a by ring]

open scoped LaurentSeries PowerSeries in
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] in
private theorem apply_sub_self_eq_vv_smul_nab (f : V →ₗ[k] V) (x : V) :
    f x - x = _root_.GlobalTheory.PhiGam.vv k • _root_.GlobalTheory.PhiGam.nab f x := by
  rw [_root_.GlobalTheory.PhiGam.nab_apply_eq, smul_smul, mul_inv_cancel₀ (_root_.GlobalTheory.PhiGam.vv_ne_zero k),
    one_smul]

open scoped LaurentSeries PowerSeries in

theorem _root_.GlobalTheory.PhiGam.Gauge.main : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l]
    (R : _root_.GlobalTheory.PhiGam.RingPG k l) {n : ℕ} [NeZero n] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V]
    [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
    [FiniteDimensional k⸨X⸩ V] (D : _root_.GlobalTheory.PhiGam.ModPG R n V), ∀ (w w' : ZMod n → ℤ) (s : ZMod n → ℕ)
    (N : ZMod n → Submodule k⟦X⟧ V), (∀ i, _root_.GlobalTheory.PhiGam.IsLat (N i)) →
    _root_.GlobalTheory.PhiGam.CondAB D.φ w w' N →
    (∀ i, _root_.GlobalTheory.PhiGam.CondC (D.γ i) (N i)) →
    (∀ i, (s i : ℤ) + 1 ≤ l * (s (i - 1) + 1) - w i) →
    (∀ i (a : ℕ), a ≤ s i + 1 → _root_.GlobalTheory.PhiGam.sen (D.γ i) (N i) (a : k) = 0) →
    ∀ b g : ZMod n → V, (∀ i, D.γ i (b i) - b i =
      D.φ i (g (i - 1)) - g i) →
    (∀ i, g i ∈ _root_.GlobalTheory.PhiGam.sh 1 (N i)) →
    (∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧
      ∀ i, g i - (D.γ i (m i) - m i) ∈ _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i)) ∧
    ((∀ i, g i ∈ _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i)) → (∀ i, b i ∈ N i) →
      ∃ m : ZMod n → V, (∀ i, m i ∈ N i) ∧ ∀ i, b i = D.φ i (m (i - 1)) - m i ∧
        g i = D.γ i (m i) - m i) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ D w w' s N hN hAB hC hs hsen b g hcoc hg
  have hX := _root_.GlobalTheory.PhiGam.vv_ne_zero k
  have hl : (2 : ℤ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hW : ∀ i, _ := fun i => _root_.GlobalTheory.PhiGam.Window.nab_bijective_window R (D.γ i)
    (D.γ_semi i) (N i) (hN i) (hC i) 0 (s i + 2) (fun j hj => by
      simpa using hsen i j (by omega))
  refine ⟨?_, fun hg3 hb => ?_⟩
  · have key : ∀ i, ∃ x ∈ N i, g i - (D.γ i x - x) ∈
        _root_.GlobalTheory.PhiGam.sh (s i + 3) (N i) := by
      intro i
      have hy : (_root_.GlobalTheory.PhiGam.vv k)⁻¹ • g i ∈ _root_.GlobalTheory.PhiGam.sh 0 (N i) := by
        rw [← vv_smul_mem_sh_succ_iff, smul_inv_smul₀ hX]
        simpa using hg i
      obtain ⟨x, hx, hxy⟩ := (hW i).2 _ hy
      refine ⟨x, by rwa [_root_.GlobalTheory.PhiGam.sh_zero_eq] at hx, ?_⟩
      have h3 := (vv_smul_mem_sh_succ_iff _ _ _).2 hxy
      rw [smul_sub, smul_inv_smul₀ hX, ← apply_sub_self_eq_vv_smul_nab] at h3
      convert h3 using 2
      push_cast
      ring
    choose m hm1 hm2 using key
    exact ⟨m, hm1, hm2⟩
  · set φ := D.φ
    set γ := D.γ
    have hφ : ∀ i (a : ℕ) {x : V}, x ∈ _root_.GlobalTheory.PhiGam.sh a (N (i - 1)) →
        φ i x ∈ _root_.GlobalTheory.PhiGam.sh (l * a - w i) (N i) := fun i a x hx =>
      _root_.GlobalTheory.PhiGam.Gauge.phi_sh R (φ i) (D.φ_semi i) (N i)
        (N (i - 1)) (w i) (hAB i).1 a hx
    have hγ : ∀ i (a : ℤ) {x : V}, x ∈ _root_.GlobalTheory.PhiGam.sh a (N i) →
        γ i x - x ∈ _root_.GlobalTheory.PhiGam.sh (a + 1) (N i) := fun i a x hx => by
      rw [apply_sub_self_eq_vv_smul_nab, vv_smul_mem_sh_succ_iff]
      exact _root_.GlobalTheory.PhiGam.Window.nab_mem_sh R (D.γ_semi i) (hC i) a hx
    have hb' : ∀ i, b i ∈ _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i) := by
      intro i
      have h1 : γ i (b i) - b i ∈ _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2 + 1) (N i) := by
        rw [hcoc i]
        refine sub_mem ?_ (by convert hg3 i using 2; ring)
        have h2 := hφ i (s (i - 1) + 3) (by push_cast; exact hg3 (i - 1))
        refine _root_.GlobalTheory.PhiGam.sh_le_sh_of_le ?_ _ h2
        have := hs i
        push_cast
        nlinarith
      rw [apply_sub_self_eq_vv_smul_nab, vv_smul_mem_sh_succ_iff] at h1
      have := (hW i).1 (b i) (by rw [_root_.GlobalTheory.PhiGam.sh_zero_eq]; exact hb i) (by convert h1 using 2; push_cast; ring)
      convert this using 2
      push_cast
      ring
    have hP : ∀ i, ∀ x ∈ _root_.GlobalTheory.PhiGam.sh ((s (i - 1) : ℤ) + 2) (N (i - 1)),
        φ i x ∈ _root_.GlobalTheory.PhiGam.sh 1
          (_root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i)) := by
      intro i x hx
      rw [_root_.GlobalTheory.PhiGam.sh_sh_eq]
      refine _root_.GlobalTheory.PhiGam.sh_le_sh_of_le ?_ _ (hφ i (s (i - 1) + 2) (by push_cast; exact hx))
      have := hs i
      push_cast
      nlinarith
    have hF := _root_.GlobalTheory.PhiGam.one_sub_frob_bij R D
      (fun i => _root_.GlobalTheory.PhiGam.sh ((s i : ℤ) + 2) (N i)) (fun i => (hN i).shift _) hP
    obtain ⟨m, hmP, hmb⟩ := hF.1 b hb'
    change ∀ i, φ i (m (i - 1)) - m i = b i at hmb
    have hg0 := hF.2 (fun i => g i - (γ i (m i) - m i))
      (fun i => sub_mem (_root_.GlobalTheory.PhiGam.sh_le_sh_of_le (by linarith) _ (hg3 i))
        (_root_.GlobalTheory.PhiGam.sh_le_sh_of_le (by linarith) _ (hγ i _ (hmP i))))
      (fun i => by
        show φ i (g (i - 1) - (γ (i - 1) (m (i - 1)) - m (i - 1))) = g i - (γ i (m i) - m i)
        have e := hcoc i
        rw [← hmb i, map_sub] at e
        have e2 := sub_eq_iff_eq_add.1 e.symm
        have hcomm : ∀ x, φ i (γ (i - 1) x) = γ i (φ i x) := D.comm i
        simp only [map_sub, hcomm]
        rw [e2]
        abel)
    refine ⟨m, fun i => ?_, fun i => ⟨(hmb i).symm, ?_⟩⟩
    · have := _root_.GlobalTheory.PhiGam.sh_le_sh_of_le (show (0 : ℤ) ≤ (s i : ℤ) + 2 by positivity) _ (hmP i)
      rwa [_root_.GlobalTheory.PhiGam.sh_zero_eq] at this
    · exact sub_eq_zero.1 (congrFun hg0 i)

end GlobalTheory.PhiGam.Gauge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionUniversalLocalHom
section
open IsLocalRing GlobalTheory.Pat

namespace GlobalTheory.Pat.CplMap

variable {R S S' : Type} [CommRing R] [CommRing S] [IsLocalRing S] [CommRing S'] [IsLocalRing S']
  {q : Ideal R} {φ : R →+* S} {ψ : R →+* S'}

theorem isUnit_mk (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) {b : R} (hb : b ∉ q) :
    IsUnit (Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b)) := by
  have h1 : IsUnit (ψ b) := by
    by_contra h
    exact hb (hψ ▸ (Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr h)))
  exact h1.map _

theorem map_mem_pow (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) {a : R} (ha : a ∈ q ^ n) :
    ψ a ∈ maximalIdeal S' ^ n := by
  have h : (q ^ n).map ψ ≤ maximalIdeal S' ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hψ.ge) n
  exact h (Ideal.mem_map_of_mem ψ ha)

theorem ext_mem_pow (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) {F : S →+* S'}
    (hF : F.comp φ = ψ) (n : ℕ) {x : S} (hx : x ∈ maximalIdeal S ^ n) :
    F x ∈ maximalIdeal S' ^ n := by
  have h1 : (maximalIdeal S).map F ≤ maximalIdeal S' := by
    rw [hφ.max_eq, Ideal.map_map, hF]
    exact Ideal.map_le_iff_le_comap.mpr hψ.ge
  have h2 : (maximalIdeal S ^ n).map F ≤ maximalIdeal S' ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h1 n
  exact h2 (Ideal.mem_map_of_mem F hx)

variable [hq : q.IsPrime]

def IsVal (q : Ideal R) (φ : R →+* S) (ψ : R →+* S') (n : ℕ) (s : S)
    (t : S' ⧸ maximalIdeal S' ^ n) : Prop :=
  ∀ a b : R, b ∉ q → φ b * s - φ a ∈ maximalIdeal S ^ n →
    Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b) * t = Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ a)

theorem exists_val (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) (s : S) :
    ∃ t, IsVal q φ ψ n s t := by
  obtain ⟨a0, b0, hb0, h0⟩ := (isCplAt_approx R S q φ hφ n).1 s
  obtain ⟨u, hu⟩ := isUnit_mk hψ n hb0
  refine ⟨Ideal.Quotient.mk _ (ψ a0) * (↑u⁻¹ : S' ⧸ maximalIdeal S' ^ n), fun a b _ h => ?_⟩
  have hm : φ (b * a0 - b0 * a) ∈ maximalIdeal S ^ n := by
    have : φ (b * a0 - b0 * a) = φ b0 * (φ b * s - φ a) - φ b * (φ b0 * s - φ a0) := by
      simp only [map_sub, map_mul]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h0)
  obtain ⟨c, hc, hcq⟩ := (isCplAt_approx R S q φ hφ n).2 _ hm
  have h1 := Ideal.Quotient.eq_zero_iff_mem.mpr (map_mem_pow hψ n hcq)
  simp only [map_mul, map_sub] at h1
  have h2 := sub_eq_zero.mp ((isUnit_mk hψ n hc).mul_right_eq_zero.mp h1)
  rw [← mul_assoc, h2, ← hu, mul_right_comm, Units.mul_inv, one_mul]

omit hq in
theorem val_unique_of_pair (hψ : (maximalIdeal S').comap ψ = q) {n : ℕ} {s : S}
    {t t' : S' ⧸ maximalIdeal S' ^ n} (ht : IsVal q φ ψ n s t) {a b : R} (hb : b ∉ q)
    (h : φ b * s - φ a ∈ maximalIdeal S ^ n)
    (e : Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ b) * t' =
      Ideal.Quotient.mk (maximalIdeal S' ^ n) (ψ a)) : t = t' :=
  (isUnit_mk hψ n hb).mul_left_cancel ((ht a b hb h).trans e.symm)

theorem one_notMem : (1 : R) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).mpr h)

theorem exists_levHom (hφ : IsCplAt q φ) (hψ : (maximalIdeal S').comap ψ = q) (n : ℕ) :
    ∃ f : S →+* S' ⧸ maximalIdeal S' ^ n, ∀ s, IsVal q φ ψ n s (f s) := by
  choose f hf using exists_val hφ hψ n
  have ap := (isCplAt_approx R S q φ hφ n).1
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · exact val_unique_of_pair hψ (hf 1) (a := 1) (b := 1) one_notMem (by simp) (by simp)
  · intro x y
    obtain ⟨a1, b1, hb1, h1⟩ := ap x
    obtain ⟨a2, b2, hb2, h2⟩ := ap y
    have hb : b1 * b2 ∉ q := fun h => (hq.mem_or_mem h).elim hb1 hb2
    refine val_unique_of_pair hψ (hf (x * y)) (a := a1 * a2) hb ?_ ?_
    · have : φ (b1 * b2) * (x * y) - φ (a1 * a2) =
          (φ b1 * x - φ a1) * (φ b2 * y) + φ a1 * (φ b2 * y - φ a2) := by
        simp only [map_mul]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · simp only [map_mul]
      rw [← hf x a1 b1 hb1 h1, ← hf y a2 b2 hb2 h2]; ring
  · exact val_unique_of_pair hψ (hf 0) (a := 0) (b := 1) one_notMem (by simp) (by simp)
  · intro x y
    obtain ⟨a1, b1, hb1, h1⟩ := ap x
    obtain ⟨a2, b2, hb2, h2⟩ := ap y
    have hb : b1 * b2 ∉ q := fun h => (hq.mem_or_mem h).elim hb1 hb2
    refine val_unique_of_pair hψ (hf (x + y)) (a := a1 * b2 + a2 * b1) hb ?_ ?_
    · have : φ (b1 * b2) * (x + y) - φ (a1 * b2 + a2 * b1) =
          φ b2 * (φ b1 * x - φ a1) + φ b1 * (φ b2 * y - φ a2) := by
        simp only [map_mul, map_add]; ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
    · simp only [map_mul, map_add]
      rw [← hf x a1 b1 hb1 h1, ← hf y a2 b2 hb2 h2]; ring

end GlobalTheory.Pat.CplMap

namespace GlobalTheory.Pat

open CplMap

theorem isCplAt_existsUnique_map : ∀ (R S S' : Type) [CommRing R] [CommRing S] [IsLocalRing S]
    [CommRing S'] [IsLocalRing S'] [IsAdicComplete (maximalIdeal S') S'] (q : Ideal R) [q.IsPrime]
    (φ : R →+* S) (ψ : R →+* S'), IsCplAt q φ → (maximalIdeal S').comap ψ = q →
    ∃! θ : S →+* S', IsLocalHom θ ∧ θ.comp φ = ψ := by
  intro R S S' _ _ _ _ _ _ q _ φ ψ hφ hψ
  choose f hf using exists_levHom hφ hψ
  have hc : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal S') hle).comp (f n) = f m := by
    intro m n hle
    ext s
    obtain ⟨a, b, hb, h⟩ := (isCplAt_approx R S q φ hφ n).1 s
    refine (val_unique_of_pair hψ (hf m s) hb (Ideal.pow_le_pow_right hle h) ?_).symm
    have e := congrArg (Ideal.Quotient.factorPow (maximalIdeal S') hle) (hf n s a b hb h)
    rw [map_mul] at e
    exact e
  have hcomp : (IsAdicComplete.liftRingHom (maximalIdeal S') f hc).comp φ = ψ := by
    ext r
    refine congrFun (IsHausdorff.funext' (maximalIdeal S')
      (f := fun r => IsAdicComplete.liftRingHom (maximalIdeal S') f hc (φ r)) (g := fun r => ψ r)
      (fun n r => ?_)) r
    rw [IsAdicComplete.mk_liftRingHom]
    exact val_unique_of_pair hψ (hf n (φ r)) (a := r) (b := 1) one_notMem (by simp) (by simp)
  refine ⟨IsAdicComplete.liftRingHom (maximalIdeal S') f hc, ⟨⟨fun s hs => ?_⟩, hcomp⟩, ?_⟩
  · by_contra hn
    have h1 := ext_mem_pow hφ hψ hcomp 1 (x := s) (by
      rw [pow_one]; exact (mem_maximalIdeal _).mpr hn)
    rw [pow_one] at h1
    exact (mem_maximalIdeal _).mp h1 hs
  · rintro F ⟨-, hF⟩
    refine IsAdicComplete.eq_liftRingHom _ f hc F (fun n => ?_)
    ext s
    obtain ⟨a, b, hb, h⟩ := (isCplAt_approx R S q φ hφ n).1 s
    refine (val_unique_of_pair hψ (hf n s) hb h ?_).symm
    have h1 := ext_mem_pow hφ hψ hF n h
    rw [RingHom.comp_apply, ← map_mul, Ideal.Quotient.eq, ← hF]
    simpa using h1

end GlobalTheory.Pat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOnHermitianBlockMatrixOfInvariantsStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_hermitianBlockMatrixOfInvariants : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E), ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det) → ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := by
  first | exact @GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det | exact GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det | (intros; apply GlobalTheory.JR.ImgSec.continuousOn_mkX_of_isUnit_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCommutatorMapEqCharpolyResultantStatement
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_commutator_map_eq_charpoly_resultant : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂] (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂), LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) = resultant f₁.charpoly f₂.charpoly := by
  first | exact @GlobalTheory.DetAdResultant.det_ad_eq_resultant | exact GlobalTheory.DetAdResultant.det_ad_eq_resultant | (intros; apply GlobalTheory.DetAdResultant.det_ad_eq_resultant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetModNeZeroIff
section
open scoped Classical BigOperators
open IsLocalRing Module Matrix

noncomputable section

namespace GlobalTheory.AdaptedLocalData

open GlobalTheory.IndefiniteRowSideFullHecke.HeckeFlatSpecialisation

section Field

variable {k : Type} [Field k]

theorem card_isCompl [Finite k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (R : Submodule k V) :
    Nat.card {U : Submodule k V // IsCompl R U} =
      Nat.card k ^ (finrank k (V ⧸ R) * finrank k R) := by
  obtain ⟨f₀, hf₀⟩ := R.subtype.exists_leftInverse_of_injective R.ker_subtype
  have h₀ : ∀ x : R, f₀ x = x := fun x => LinearMap.congr_fun hf₀ x
  rw [Nat.card_congr R.isComplEquivProj, ← Module.finrank_linearMap k k,
    ← Module.natCard_eq_pow_finrank (K := k)]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun g => ⟨f₀ + g.comp R.mkQ, fun x => by
      have : R.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero R).2 x.2
      rw [LinearMap.add_apply, LinearMap.comp_apply, this, map_zero, add_zero, h₀]⟩) ⟨?_, ?_⟩)
  · intro g g' h
    have h1 : g.comp R.mkQ = g'.comp R.mkQ := add_left_cancel (congrArg Subtype.val h)
    exact R.linearMap_qext h1
  · rintro ⟨f, hf⟩
    refine ⟨R.liftQ (f - f₀) fun x hx => ?_, Subtype.ext ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, hf ⟨x, hx⟩, h₀ ⟨x, hx⟩, sub_self]
    · simp

theorem card_sup_eq_top [Finite k] (r t : ℕ) (R : Submodule k (Fin (r + t) → k))
    (hR : finrank k R ≤ r) :
    Nat.card {U : Submodule k (Fin (r + t) → k) // finrank k U = t ∧ R ⊔ U = ⊤} =
      if finrank k R = r then Nat.card k ^ (r * t) else 0 := by
  have key : ∀ U : Submodule k (Fin (r + t) → k), R ⊔ U = ⊤ →
      r + t + finrank k ↥(R ⊓ U) = finrank k R + finrank k U := fun U h => by
    have := Submodule.finrank_sup_add_finrank_inf_eq R U
    rwa [h, finrank_top, finrank_fin_fun] at this
  split_ifs with h
  · have hq : finrank k ((Fin (r + t) → k) ⧸ R) = t := by
      have := R.finrank_quotient_add_finrank
      rw [finrank_fin_fun] at this
      omega
    have := card_isCompl R
    rw [hq, h, mul_comm] at this
    rw [← this]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun U => ⟨fun ⟨h1, h2⟩ => ?_, fun hc => ?_⟩)
    · refine ⟨disjoint_iff.2 (Submodule.finrank_eq_zero.1 ?_), codisjoint_iff.2 h2⟩
      have := key U h2
      omega
    · have := key U hc.sup_eq_top
      rw [hc.inf_eq_bot, finrank_bot] at this
      exact ⟨by omega, hc.sup_eq_top⟩
  · haveI : IsEmpty {U : Submodule k (Fin (r + t) → k) // finrank k U = t ∧ R ⊔ U = ⊤} :=
      ⟨fun U => by have := key U.1 U.2.2; have := U.2.1; omega⟩
    exact Nat.card_of_isEmpty

end Field

section Local

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]

variable [Finite (ResidueField O)]

end Local

end GlobalTheory.AdaptedLocalData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMassStatement
section
open GlobalTheory.UnimodMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass : ∀ (G : Type) [Group G] (Γ W K : Subgroup G), W ≤ K → Finite (GlobalTheory.UnimodMass.DC Γ W) → (∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) → W.relIndex K ≠ 0 ∧ GlobalTheory.UnimodMass.mass Γ W = (W.relIndex K : ℚ) * GlobalTheory.UnimodMass.mass Γ K := by
  first | exact @GlobalTheory.UnimodMass.mass_eq_relIndex_mul | exact GlobalTheory.UnimodMass.mass_eq_relIndex_mul | (intros; apply GlobalTheory.UnimodMass.mass_eq_relIndex_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairEventuallyIsUnitContinuousAtInStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHermitianPair_eventually_isUnit_continuousAt_inverse : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) := by
  first | exact @GlobalTheory.et_units_near_one_inverse_continuousAt | exact GlobalTheory.et_units_near_one_inverse_continuousAt | (intros; apply GlobalTheory.et_units_near_one_inverse_continuousAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleTraceAddCharNormEqOneNearZero
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.WeilQuad.NearZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem finite_E_L [Unram F E] (A : Et F E) : Module.Finite E A.L := by
  have hE : Module.Finite F E := Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  have h := A.push.out
  exact Module.Finite.equiv h.equiv

theorem finite_F_L [Unram F E] (A : Et F E) : Module.Finite F A.L := by
  have hE : Module.Finite F E := Module.finite_of_finrank_pos (by rw [Unram.finrank_eq (F := F) (E := E)]; norm_num)
  have := finite_E_L A
  exact Module.Finite.trans E A.L

theorem finite_K_L [Unram F E] (A : Et F E) : Module.Finite A.K A.L := by
  have := finite_F_L A
  exact Module.Finite.of_restrictScalars_finite F A.K A.L

theorem continuous_NL [Unram F E] (A : Et F E) (hK : IsField A.K) :
    Continuous (fun y : A.L => A.NL y) := by
  letI : Field A.K := hK.toField
  have := finite_K_L A
  let b := Module.Free.chooseBasis A.K A.L
  have hfun : (fun y : A.L => A.NL y) = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [hfun]
  refine Continuous.matrix_det (continuous_matrix fun i j => ?_)
  let φ : A.L →ₗ[A.K] A.K := (LinearMap.proj j : (_ → A.K) →ₗ[A.K] A.K) ∘ₗ
    (LinearMap.proj i : (_ → _ → A.K) →ₗ[A.K] _) ∘ₗ (Algebra.leftMulMatrix b).toLinearMap
  have hφ : Continuous (φ.restrictScalars F) := IsModuleTopology.continuous_of_linearMap _
  exact hφ

theorem NL_zero [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) : A.NL (0 : A.L) = 0 := by
  letI : Field A.K := hK.toField
  have := finite_K_L A
  haveI : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  exact Algebra.norm_zero

end GlobalTheory.JR.WeilQuad.NearZero

theorem GlobalTheory.JR.WeilQuad.psiK_norm_eq_one_near_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → {y : A.L | A.psiK ψ ((x : A.K) * A.NL y) = 1} ∈ 𝓝 (0 : A.L) := by
  intro F E _ _ _ _ _ A ψ x μ ω h
  obtain ⟨hK, hL, hψ, -, -⟩ := h
  let g : A.L → F := fun y => Algebra.trace F A.K ((x : A.K) * A.NL y)
  have hg : Continuous g := by
    have ht : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
    exact ht.comp (continuous_const.mul (NearZero.continuous_NL A hK))
  have hg0 : g 0 = 0 := by simp [g, NearZero.NL_zero A hK hL]
  have hmem : g ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : A.L) :=
    hg.continuousAt.preimage_mem_nhds (by rw [hg0]; exact Metric.ball_mem_nhds 0 one_pos)
  refine Filter.mem_of_superset hmem fun y hy => ?_
  have hy' : ‖g y‖ < 1 := by simpa using hy
  exact hψ.1 _ hy'.le
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerOperatorInjectiveEigenvectorStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerOperator_injective_eigenvector : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) → (∀ f, ‖B f‖ ≤ 1) → B x0 = 1 → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → ∃ W : H →L[ℂ] H, HasSum (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ v, a v (f.1 v)) • B f.1) W ∧ Function.Injective W ∧ ∀ (y : H) (z : ι → ℂ), (∀ v, Z v y = z v • y) → W y = (∏' v, z v) • y := by
  first | exact @GlobalTheory.eulerOp_injective_eigen | exact GlobalTheory.eulerOp_injective_eigen | (intros; apply GlobalTheory.eulerOp_injective_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfCharpolySeparableInvolutionStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_aeval_eq_of_charpoly_separable_involution : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable | exact GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable | (intros; apply GlobalTheory.UnitLemma.InvAlg.exists_aeval_eq_of_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactUnitariesIntegralOrbitOfHankelDetNeStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_unitaries_integral_orbit_of_hankelDet_ne_zero : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 → ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := by
  first | exact @GlobalTheory.JR.SuppBdd.exists_compact_of_integral | exact GlobalTheory.JR.SuppBdd.exists_compact_of_integral | (intros; apply GlobalTheory.JR.SuppBdd.exists_compact_of_integral <;> assumption)
end

