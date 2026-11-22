import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnramifiedSubfieldLeCyclotomicExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0607
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0596
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0536
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0542

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionsStdBelowLevel
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL GlobalTheory.NL.Model

noncomputable section

namespace GlobalTheory.NL.LatLow

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem conv_eq_sum (e : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) (k : ℤ) (N : ℕ)
    (hN : k - m < N) :
    conv e u k = ∑ j ∈ Finset.range N, PowerSeries.coeff j e • u (k - (j : ℤ)) := by
  unfold conv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  by_contra h
  simp only [Finset.coe_range, Set.mem_Iio, not_lt] at h
  apply hj
  have : k - (j : ℤ) < m := by omega
  simp [hm _ this]

theorem conv_van (e : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) :
    ∀ k < m, conv e u k = 0 := by
  intro k hk
  rw [conv_eq_sum e hm k 0 (by omega)]
  simp

theorem conv_mul (a b : PowerSeries L) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) :
    conv (a * b) u = conv a (conv b u) := by
  funext k
  set N := (k - m).toNat + 1 with hN
  rw [conv_eq_sum _ hm k N (by omega), conv_eq_sum _ (conv_van b hm) k N (by omega)]
  have h1 : ∀ i ∈ Finset.range N, PowerSeries.coeff i a • conv b u (k - (i : ℤ)) =
      ∑ j ∈ Finset.range (N - i), (PowerSeries.coeff i a * PowerSeries.coeff j b) •
        u (k - ((i + j : ℕ) : ℤ)) := by
    intro i hi
    have := Finset.mem_range.1 hi
    rw [conv_eq_sum _ hm _ (N - i) (by omega), Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_range_diag_flip N (fun i j =>
    (PowerSeries.coeff i a * PowerSeries.coeff j b) • u (k - ((i + j : ℕ) : ℤ)))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  have h2 : i + (n - i) = n := by omega
  rw [h2]

def tw (c : L) (Φ : M →ₗ[L] M) : (ℤ → M) →ₗ[L] (ℤ → M) where
  toFun f := fun k => c ^ k • Φ (f k)
  map_add' f g := by funext k; simp
  map_smul' a f := by funext k; simp [smul_comm a]

theorem tw_apply (c : L) (Φ : M →ₗ[L] M) (f : ℤ → M) (k : ℤ) : tw c Φ f k = c ^ k • Φ (f k) := rfl

theorem tw_van (c : L) (Φ : M →ₗ[L] M) {u : ℤ → M} {m : ℤ} (hm : ∀ k < m, u k = 0) :
    ∀ k < m, tw c Φ u k = 0 := fun k hk => by simp [tw_apply, hm k hk]

theorem tw_conv {c : L} (hc : c ≠ 0) (Φ : M →ₗ[L] M) (a : PowerSeries L) {u : ℤ → M} {m : ℤ}
    (hm : ∀ k < m, u k = 0) :
    tw c Φ (conv a u) = conv (PowerSeries.rescale c a) (tw c Φ u) := by
  funext k
  set N := (k - m).toNat + 1 with hN
  rw [tw_apply, conv_eq_sum _ hm k N (by omega), conv_eq_sum _ (tw_van c Φ hm) k N (by omega),
    map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tw_apply, map_smul, smul_smul, smul_smul, PowerSeries.coeff_rescale, zpow_sub₀ hc, zpow_natCast]
  congr 1
  field_simp

theorem std_step {A DD : Type} [CommRing A] [AddCommGroup DD] [Module A DD] (N : Submodule A DD)
    (φ : DD → DD) (Q : A) (lev : A →* PowerSeries L) (hQ : IsUnit (lev Q))
    (e e' : ↥N →+ (ℤ → M)) (D D' : Submodule L M) (c : L) (hc : c ≠ 0) (Φ : M →ₗ[L] M)
    (hΦ : Set.BijOn Φ D' D)
    (hD : ∀ x k, e x k ∈ D) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, e x k = 0)
    (hsm : ∀ (a : A) (x : ↥N), e (a • x) = conv (lev a) (e x))
    (hφ : ∀ x ∈ N, ∃ k : ℕ, Q ^ k • φ x ∈ N)
    (hφinv : ∀ y ∈ N, ∃ k : ℕ, Q ^ k • y ∈ Submodule.span A (φ '' (N : Set DD)))
    (heφ : ∀ (x : ↥N) (m : ℕ) (hx : Q ^ m • φ x ∈ N),
      e ⟨Q ^ m • φ x, hx⟩ = conv (lev (Q ^ m)) (tw c Φ (e' x)))
    (h' : Std D' (latSpan (LL := L) e')) : Std D (latSpan (LL := L) e) := by
  have hv' : ∀ x, ∀ k < (0 : ℤ), e' x k = 0 := fun x => ((h' _).1 (mem_latSpan _ x)).2
  have hinv : ∀ m : ℕ, ∃ w : PowerSeries L, w * lev (Q ^ m) = 1 := fun m => by
    rw [map_pow]
    exact (hQ.pow m).exists_left_inv
  have hspan : ∀ z ∈ Submodule.span A (φ '' (N : Set DD)), ∃ (m : ℕ) (hz : Q ^ m • z ∈ N),
      ∀ k < (0 : ℤ), e ⟨Q ^ m • z, hz⟩ k = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨m, hm⟩ := hφ x hx
      refine ⟨m, hm, ?_⟩
      rw [heφ ⟨x, hx⟩ m hm]
      exact conv_van _ (tw_van c Φ (hv' _))
    | zero =>
      refine ⟨0, by simp, fun k _ => ?_⟩
      have : (⟨Q ^ 0 • (0 : DD), by simp⟩ : ↥N) = 0 := Subtype.ext (by simp)
      rw [this, map_zero]; rfl
    | add z z' _ _ hz hz' =>
      obtain ⟨m, hm, hz⟩ := hz
      obtain ⟨m', hm', hz'⟩ := hz'
      have key : Q ^ (m + m') • (z + z') =
          ((Q ^ m' • (⟨_, hm⟩ : ↥N) + Q ^ m • (⟨_, hm'⟩ : ↥N) : ↥N) : DD) := by
        simp only [Submodule.coe_add, Submodule.coe_smul, smul_add, smul_smul, ← pow_add, add_comm m' m]
      refine ⟨m + m', key ▸ Subtype.mem _, fun k hk => ?_⟩
      have : (⟨Q ^ (m + m') • (z + z'), key ▸ Subtype.mem _⟩ : ↥N) =
          Q ^ m' • (⟨_, hm⟩ : ↥N) + Q ^ m • (⟨_, hm'⟩ : ↥N) := Subtype.ext key
      rw [this, map_add, hsm, hsm, Pi.add_apply, conv_van _ hz k hk, conv_van _ hz' k hk, add_zero]
    | smul a z _ hz =>
      obtain ⟨m, hm, hz⟩ := hz
      have key : Q ^ m • (a • z) = ((a • (⟨_, hm⟩ : ↥N) : ↥N) : DD) := by
        simp only [Submodule.coe_smul, smul_smul, mul_comm]
      refine ⟨m, key ▸ Subtype.mem _, fun k hk => ?_⟩
      have : (⟨Q ^ m • (a • z), key ▸ Subtype.mem _⟩ : ↥N) = a • (⟨_, hm⟩ : ↥N) := Subtype.ext key
      rw [this, hsm, conv_van _ hz k hk]
  have hv : ∀ x, ∀ k < (0 : ℤ), e x k = 0 := by
    intro y
    obtain ⟨j, hj⟩ := hφinv y y.2
    obtain ⟨m, hm, hz⟩ := hspan _ hj
    have : (⟨Q ^ m • Q ^ j • (y : DD), hm⟩ : ↥N) = Q ^ (m + j) • y :=
      Subtype.ext (by simp only [Submodule.coe_smul, smul_smul, pow_add])
    rw [this, hsm] at hz
    obtain ⟨w, hw⟩ := hinv (m + j)
    obtain ⟨b, hb⟩ := hs y
    have h2 := conv_van w hz
    rwa [← conv_mul _ _ hb, hw, conv_one] at h2
  have hmap : ∀ g ∈ latSpan (LL := L) e', tw c Φ g ∈ latSpan (LL := L) e := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, x, rfl⟩ := hg
      obtain ⟨m, hm⟩ := hφ x x.2
      obtain ⟨w, hw⟩ := hinv m
      refine Submodule.subset_span ⟨PowerSeries.rescale c a * w, ⟨_, hm⟩, ?_⟩
      rw [heφ x m hm, ← conv_mul _ _ (tw_van c Φ (hv' x)), mul_assoc, hw, mul_one,
        tw_conv hc Φ a (hv' x)]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
    | smul a f _ hf => rw [map_smul]; exact Submodule.smul_mem _ a hf
  intro f
  constructor
  · intro hf
    refine ⟨(latSpan_coeff _ D hD hs f hf).1, ?_⟩
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, x, rfl⟩ := hf
      exact conv_van a (hv x)
    | zero => exact fun _ _ => rfl
    | add f g _ _ hf hg => intro k hk; simp [hf k hk, hg k hk]
    | smul a f _ hf => intro k hk; simp [hf k hk]
  · rintro ⟨h1, h2⟩
    have : ∀ k, ∃ d ∈ D', Φ d = f k ∧ (k < 0 → d = 0) := by
      intro k
      by_cases hk : k < 0
      · exact ⟨0, D'.zero_mem, by rw [map_zero, h2 k hk], fun _ => rfl⟩
      · obtain ⟨d, hd, hd'⟩ := hΦ.surjOn (h1 k)
        exact ⟨d, hd, hd', fun h => absurd h hk⟩
    choose d hd hd1 hd2 using this
    have hg : (fun k => (c ^ k)⁻¹ • d k) ∈ latSpan (LL := L) e' :=
      (h' _).2 ⟨fun k => D'.smul_mem _ (hd k), fun k hk => by simp [hd2 k hk]⟩
    have h3 := hmap _ hg
    have : tw c Φ (fun k => (c ^ k)⁻¹ • d k) = f := by
      funext k
      rw [tw_apply, map_smul, smul_smul, mul_inv_cancel₀ (zpow_ne_zero k hc), one_smul, hd1]
    rwa [this] at h3

end Series

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in

theorem lat_low : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 → Std (Di (HW l) h T i) (Lat C h T i ζ) := by
  intro D HW F Cm l hl K s LL h W E C T hT
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have main : ∀ (j : ℕ) (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ζ ^ (l ^ (s - 1)) = 1 →
      Std (Di (HW l) h T i) (Lat C h T i ζ) := by
    intro j
    induction j with
    | zero =>
      intro i ζ h1 _
      obtain rfl : ζ = 1 := by simpa using h1
      exact GlobalTheory.T.wach_lattice_eq_std_powerSeries_at_zero D HW F Cm l K s LL h T hT i
    | succ j ih =>
      intro i ζ h1 h2
      have hprim : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
        obtain ⟨r, -, hr⟩ := (Nat.dvd_prime_pow hl.out).1 (orderOf_dvd_of_pow_eq_one h1)
        exact ⟨r, hr ▸ IsPrimitiveRoot.orderOf ζ⟩
      have ih' := ih (i - 1) (ζ ^ l) (by rw [← pow_mul, ← pow_succ', h1])
        (by rw [← pow_mul, mul_comm, pow_mul, h2, one_pow])
      have hQ : IsUnit (W.lev i ζ W.Q) :=
        ((GlobalTheory.T.wachLevel_expansion_at_root_of_unity D HW l K s LL h i ζ hprim).2.2.1 h2).2
      have hΦ := (GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT).1 i
      have hc : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
      refine std_step (W.N T) (W.φD T) W.Q (MonoidHomClass.toMonoidHom (W.lev i ζ)) hQ
        ((C.C K s LL h).tie.levB T i ζ) ((C.C K s LL h).tie.levB T (i - 1) (ζ ^ l))
        (Di (HW l) h T i) (Di (HW l) h T (i - 1)) (l : ↥LL.1) hc _ hΦ
        ((C.C K s LL h).tie.levB_mem T i ζ) ((C.C K s LL h).tie.levB_supp T i ζ)
        (ex_smul C h T i ζ) (W.N_φ T) (W.N_φinv T) ?_ ih'
      intro x m hx
      funext k
      have := (C.C K s LL h).tie.levB_φ T hT i ζ (by rw [hp]; exact hprim) x m hx k
      rw [hp] at this
      exact this
  intro i ζ hζ
  exact main (s - 1) i ζ hζ hζ

end GlobalTheory.NL.LatLow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiValueGaloisSubMemFilZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

open GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.ValueFil in

theorem GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∃ m₀ : ℕ, ∀ w ∈ D.Mext (invL l (A O K)), (∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m₀ * h) → ∀ (hw : D.xiExt w ∈ D.MMl) (g : Gl l), sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩)) - R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ ι _ _ η H D T R
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  refine ⟨η, fun w hwA hN hw g hg C => ?_⟩
  have hwS : ∀ τ j, w τ j ∈ invL l (S O K e) := fun τ j =>
    away_mono (A_le_S l e) (by simp) (mem_tot.1 hwA τ j)
  have hd : ∀ j : ι, D.xi (fun _ => Pi.single j (1 : K)) ∈ D.MMl := fun j =>
    ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2 _).2 (mem_tot.2 fun τ i => by
      rw [cst_apply]
      exact HasK.C_mem _)
  obtain ⟨V, hV⟩ : ∃ V : ι → TW (OB l O) T,
      V = fun j => R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ι → OB l O, c = fun j => ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) := ⟨_, rfl⟩
  have hval : R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) = ∑ j, c j • V j := by
    rw [GlobalTheory.T.tensorBcris_frobenius_value_eq_sum_coordinates l a e O K t ϖ ι D.toPhiMod w hwS hw hd, map_sum, hV, hc]
    simp only [map_smul]
  have hfix : ∀ j, actB (sQ l) T g (V j) = V j := fun j => by
    rw [hV]
    exact R.horiz g hg _ (hd j)
  have hgval : actB (sQ l) T g (∑ j, c j • V j) = ∑ j, galOB O (sQ l g) (c j) • V j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change TWact (galOB O (sQ l g)) T g (c j • V j) = _
    rw [TWact_smul]
    change _ • actB (sQ l) T g (V j) = _
    rw [hfix j]
  rw [hval, hgval, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have h1 : galOB O (sQ l g) (c j) - c j ∈ filO O C η := by
    rw [hc]
    refine GlobalTheory.T.galOB_iB_sub_iB_mem_filO l a e O K t ϖ C η (fun τ => ⟨w τ j, hwS τ j⟩) (fun τ => mem_tot.1 hwA τ j)
      (fun τ => ?_) g hg
    obtain ⟨h, hh, k, hk⟩ := hN τ j
    exact ⟨h, hh, k, hk⟩
  have h2 : V j ∈ filT C T (-(η : ℤ)) := by
    rw [hV]
    dsimp only
    obtain ⟨u, hu⟩ : ∃ u, u = toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩ := ⟨_, rfl⟩
    rw [← hu]
    have hsum : u = ∑ i, u i • Pi.single i (1 : OB l O) := by
      ext1 k
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    refine smul_mem_filT_of_zero ?_ (GlobalTheory.T.jB_single_mem_filT' l a e O K t ϖ ι η H D T R C i)
    rw [hu, toBcris_apply]
    exact GlobalTheory.T.invariant_lattice_filtration_zero l a e O K t ϖ C _
  exact smul_mem_filT_neg h1 h2
end

