import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0392
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPolyEqZeroOfDiscDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DiscRem

theorem norm_add_le_max' (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (x y : Disc l u ρ) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y
  rw [← map_add, norm_ofPre, norm_ofPre, norm_ofPre]
  exact gauge_add_le_max l u ρ a b

theorem norm_toDisc_l_le (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) :
    ‖toDisc l u ρ (l : A)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  exact (norm_ofPre l u ρ _).trans_le (gauge_le l u ρ (by positivity)
    (Submodule.subset_span ⟨1, 0, 0, by simp [hl0.ne'], by simp⟩))

theorem coeff_mul_disc (l : ℕ) {R : Type} [CommRing R] (ρ : ℝ≥0)
    (a : ℕ → (Disc l (X : R⟦X⟧) ρ →+ Disc l (0 : R) 1))
    (h1 : ∀ n x, a n (toDisc l (X : R⟦X⟧) ρ x) = toDisc l (0 : R) 1 (coeff n x))
    (hc : ∀ n, Continuous (a n)) (s : R⟦X⟧) (n : ℕ) (y : Disc l (X : R⟦X⟧) ρ) :
    a n (toDisc l (X : R⟦X⟧) ρ s * y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, toDisc l (0 : R) 1 (coeff p.1 s) * a p.2 y := by
  refine (denseRange_ofPre l (X : R⟦X⟧) ρ).induction_on y
    (isClosed_eq ((hc n).comp (continuous_const.mul continuous_id))
      (continuous_finset_sum _ fun p _ => continuous_const.mul (hc p.2))) fun z => ?_
  obtain ⟨k, b, h⟩ := IsLocalization.Away.surj (l : R⟦X⟧) z
  have h' : (l ^ k : ℕ) • ofPre l (X : R⟦X⟧) ρ z = toDisc l (X : R⟦X⟧) ρ b := by
    have := congrArg (ofPre l (X : R⟦X⟧) ρ) h
    rw [map_mul, map_pow, map_natCast, map_natCast] at this
    rw [nsmul_eq_mul, Nat.cast_pow, mul_comm]
    exact this
  refine ((isUnit_l_disc l (0 : R) 1).pow k).mul_left_cancel ?_
  rw [← Nat.cast_pow, ← nsmul_eq_mul, ← nsmul_eq_mul, ← map_nsmul, ← mul_smul_comm, h', ← map_mul, h1,
    coeff_mul, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← mul_smul_comm, ← map_nsmul, h', h1, map_mul]

theorem rho_zero {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) :
    0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree = (l : ℝ)⁻¹ := by
  have he : (0 : ℝ) < bk.Ep.natDegree := Nat.cast_pos.2 bk.deg_pos
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
    have : 0 < 1 / (bk.Ep.natDegree : ℝ) := by positivity
    linarith), ?_⟩
  rw [BK.ρ₀, NNReal.coe_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), neg_mul,
    one_div_mul_cancel he.ne', Real.rpow_neg_one, NNReal.coe_natCast]

theorem eq_zero_of_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (r : Polynomial (Wq l bk.a)),
    r.degree < bk.Ep.degree →
    toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ (r : bk.S) → r = 0 := by
  intro l hl K bk r hr ⟨y, hy⟩
  obtain ⟨h0, h1, hpow⟩ := rho_zero bk
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk bk.ρ₀ h0 h1
  obtain ⟨-, -, hinj, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk
  have h0' : (0 : ℝ) < bk.ρ₀ := h0
  have h1' : (bk.ρ₀ : ℝ) < 1 := h1
  have hc : ∀ n, Continuous (a n) := fun n =>
    AddMonoidHomClass.continuous_of_bound _ ((bk.ρ₀ : ℝ) ^ n)⁻¹ fun z => by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; exact ha2 n z
  have hy0 : y = 0 := by
    refine norm_le_zero_iff.1 (ha3 y 0 le_rfl fun m₀ => ?_)
    by_contra hneg
    push Not at hneg
    set c := ‖a m₀ y‖ * (bk.ρ₀ : ℝ) ^ m₀ with hcdef
    have hfin : {n | c ≤ ‖a n y‖ * (bk.ρ₀ : ℝ) ^ n}.Finite := by
      have := (ha4 y).eventually (gt_mem_nhds hneg)
      rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at this
      simpa only [not_lt] using this
    obtain ⟨m, hm, hmax⟩ := hfin.exists_maximal ⟨m₀, le_refl c⟩
    have hlt : ∀ n, m < n → ‖a n y‖ * (bk.ρ₀ : ℝ) ^ n < c := fun n hn => by
      by_contra h
      exact (hmax (not_lt.1 h) hn.le).not_gt hn
    have key := coeff_mul_disc l bk.ρ₀ a ha1 hc bk.E (bk.Ep.natDegree + m) y
    have hz : coeff (bk.Ep.natDegree + m) (r : bk.S) = 0 := by
      rw [Polynomial.coeff_coe]
      refine Polynomial.coeff_eq_zero_of_degree_lt (hr.trans_le ?_)
      rw [Polynomial.degree_eq_natDegree bk.monic.ne_zero]
      exact_mod_cast Nat.le_add_right _ _
    rw [← hy, ha1, hz, map_zero, ← Finset.add_sum_erase _ _
      (show (bk.Ep.natDegree, m) ∈ Finset.HasAntidiagonal.antidiagonal (bk.Ep.natDegree + m) by simp)] at key
    have hlead : coeff bk.Ep.natDegree bk.E = 1 := by
      rw [Polynomial.coeff_coe]; exact bk.monic
    simp only [hlead, map_one, one_mul] at key
    have hsum : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (bk.Ep.natDegree + m)).erase (bk.Ep.natDegree, m),
        toDisc l (0 : Wq l bk.a) 1 (coeff p.1 bk.E) * a p.2 y‖ * (bk.ρ₀ : ℝ) ^ m < c := by
      refine Finset.sum_induction _ (fun x => ‖x‖ * (bk.ρ₀ : ℝ) ^ m < c) (fun x z hx hz => ?_)
        (by simpa using hneg) fun p hp => ?_
      · refine (mul_le_mul_of_nonneg_right (norm_add_le_max' l _ _ x z) (by positivity)).trans_lt ?_
        rcases max_cases ‖x‖ ‖z‖ with h | h <;> rw [h.1] <;> assumption
      · obtain ⟨i, j⟩ := p
        simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at hp
        rw [Polynomial.coeff_coe]
        rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
        · obtain ⟨w, hw⟩ := bk.dvd_coeff i h
          have hn : ‖toDisc l (0 : Wq l bk.a) 1 (bk.Ep.coeff i)‖ ≤ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := by
            rw [hw, map_mul, hpow]
            exact (norm_mul_le _ _).trans ((mul_le_mul (norm_toDisc_l_le l _ _) (norm_toDisc_le _)
              (norm_nonneg _) (by positivity)).trans (mul_one _).le)
          refine lt_of_le_of_lt ?_ (hlt j (by omega))
          have hp2 : (bk.ρ₀ : ℝ) ^ (bk.Ep.natDegree + m) ≤ (bk.ρ₀ : ℝ) ^ j :=
            pow_le_pow_of_le_one h0'.le h1'.le (by omega)
          calc _ ≤ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree * ‖a j y‖ * (bk.ρ₀ : ℝ) ^ m :=
                mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) (by positivity)
            _ = ‖a j y‖ * (bk.ρ₀ : ℝ) ^ (bk.Ep.natDegree + m) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hp2 (norm_nonneg _)
        · exact (hp.1 ⟨h, by omega⟩).elim
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]
          simpa using hneg
    rw [eq_neg_of_add_eq_zero_right key.symm, norm_neg] at hsum
    exact hsum.not_ge hm
  ext1 n
  apply hinj
  have := ha1 n (r : bk.S)
  rw [hy, hy0, mul_zero, map_zero, Polynomial.coeff_coe] at this
  rw [← this, Polynomial.coeff_zero, map_zero]

end GlobalTheory.BSP.DiscRem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKCoord

theorem semiBC_injective {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) [Module.Projective A M]
    (hf : Function.Injective f) : Function.Injective u := by
  refine (injective_iff_map_eq_zero u).2 fun x hx => ?_
  by_contra h0
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero A h0
  obtain ⟨w, hw, -⟩ := h B (f.toSemilinearMap.comp φ)
  have h1 := hw x
  rw [hx, map_zero] at h1
  exact hφ (hf (h1.symm.trans (map_zero f).symm))

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]

theorem ev_eis_ne_zero (ϖ : PiSys l e) : ϖ.ev a (eis l a e) ≠ 0 := fun h =>
  (ϖ.isUnit_inclW_ev_eis a).ne_zero (by rw [h, map_zero])

theorem ev_injective (ϖ : PiSys l e) : Function.Injective (ϖ.ev a) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have key : ∀ n : ℕ, ∃ y, x = eis l a e ^ n * y ∧ ϖ.ev a y = 0 := fun n => by
    induction n with
    | zero => exact ⟨x, by simp, hx⟩
    | succ n ih =>
      obtain ⟨y, h1, h2⟩ := ih
      obtain ⟨z, rfl⟩ := (ϖ.theta_ev_eq_zero_iff a y).1 (by rw [h2, map_zero])
      rw [map_mul] at h2
      exact ⟨z, by rw [h1]; ring, (mul_eq_zero.1 h2).resolve_left (ev_eis_ne_zero ϖ)⟩
  refine (complete_eis l a e).haus x fun n => ?_
  obtain ⟨y, h1, -⟩ := key n
  rw [SModEq.zero, h1]
  exact Submodule.smul_mem_smul
    (Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) n) Submodule.mem_top

section Kappa

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K]
  {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O)

theorem kappa_smul (w : WCb l) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (w • y) = ((1 : O) ⊗ₜ[ℤ_[l]] w : OW l O) • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul v x =>
    rw [smul_tmul', kappa_tmul, kappa_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

theorem kappa_frob :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      TWmap (frobOW l O) T (kappa T y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def mulZ (o : O) :
    letI := zlLat T
    ↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T :=
  letI := zlLat T
  { toFun := fun x => o • x
    map_add' := smul_add o
    map_smul' := fun c x => smul_comm o (algebraMap ℤ_[l] O c) x }

theorem kappa_mulZ (o : O) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T ((mulZ T o).lTensor (WCb l) y) = o • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul v x => exact tmul_smul o ((1 : O) ⊗ₜ[ℤ_[l]] v : OW l O) x
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

end Kappa

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G] {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

theorem exists_coord (I : Ident t ϖ P T) {N : Type} [AddCommGroup N] (J : N →+ TW (OW l O) T)
    (h : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) :
    ∃ (c : N →+ Vec K a ι) (hc : ∀ x, c x ∈ P.M),
      (∀ x, J x = I.j (toW t ϖ P ⟨c x, mem_ME_of_mem_M (hc x)⟩)) ∧ ∀ m ∈ P.M, ∃ x, c x = m := by
  choose c hc hJ using fun x => (h (J x)).1 ⟨x, rfl⟩
  refine ⟨AddMonoidHom.mk' c fun x y => ?_, hc, hJ, fun m hm => ?_⟩
  · have h1 := map_add J x y
    rw [hJ, hJ, hJ, ← map_add, ← map_add] at h1
    exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h1))
  · obtain ⟨x, hx⟩ := (h _).2 ⟨m, hm, rfl⟩
    rw [hJ] at hx
    exact ⟨x, (congrArg Subtype.val (toW_injective t ϖ P (I.j.injective hx))).symm⟩

theorem eq_of_j_eq (I : Ident t ϖ P T) (f : ZMod a → A O K) (v w : ME P)
    (h : I.j (toW t ϖ P w) = inclO l O (ϖ.iTot t K f) • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => (f τ : K⟦X⟧) * v.1 τ i := by
  have hm : (fun τ i => (f τ : K⟦X⟧) * v.1 τ i) ∈ ME P :=
    mem_tot.2 fun τ i => mul_mem (le_away _ _ (f τ).2) (mem_tot.1 v.2 τ i)
  have h1 := toW_smul t ϖ P (fun τ => ⟨f τ, le_away _ _ (f τ).2⟩) v ⟨_, hm⟩ fun τ => rfl
  rw [← map_smul, ← ϖ.iW_of_mem t K, ← h1] at h
  exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h))

variable (K t ϖ) in

theorem inclO_iTot_E_pow (k : ℕ) : inclO l O (ϖ.iTot t K ((fun _ => EIn l e _) ^ k)) =
    (1 : O) ⊗ₜ[ℤ_[l]] (inclW l (ϖ.ev a (eis l a e)) ^ k) := by
  rw [map_pow, map_pow, PiSys.iTot_E, inclO_tmul, Algebra.TensorProduct.tmul_pow, one_pow]

theorem eq_of_j_eq_const (I : Ident t ϖ P T) (o : O) (v w : ME P)
    (h : I.j (toW t ϖ P w) = o • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => PowerSeries.C (algebraMap O K o) * v.1 τ i := by
  refine (eq_of_j_eq I (algebraMap O _ o) v w ?_).trans
    (funext fun τ => funext fun i => congrArg (· * v.1 τ i) (algebraMap_eq_C o))
  rwa [AlgHom.commutes, AlgHom.commutes, algebraMap_smul]

theorem eq_of_j_eq_toAc (I : Ident t ϖ P T) (f : (Wq l a)⟦X⟧) (v w : ME P)
    (h : I.j (toW t ϖ P w) = ((1 : O) ⊗ₜ[ℤ_[l]] inclW l (ϖ.ev a f) : OW l O) • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => (toAc t K f τ : K⟦X⟧) * v.1 τ i := by
  refine eq_of_j_eq I (toAc t K f) v w ?_
  rwa [PiSys.iTot_toAc, inclO_tmul]

theorem eq_of_j_eq_phi (I : Ident t ϖ P T) (k : ℕ) {v : Vec K a ι} (hv : v ∈ P.M) (w : ME P)
    (h : I.j (toW t ϖ P w) = ((1 : O) ⊗ₜ[ℤ_[l]] (inclW l (ϖ.ev a (eis l a e)) ^ k) : OW l O) •
      TWmap (frobOW l O) T (I.j (toW t ϖ P ⟨v, mem_ME_of_mem_M hv⟩))) :
    w.1 = fun τ i => E K l e ^ k * P.phi v τ i := by
  refine eq_of_j_eq I ((fun _ => EIn l e _) ^ k) ⟨_, mem_ME_of_mem_L (P.phi_mem_L hv)⟩ w ?_
  rwa [toW_phi t ϖ P hv, I.j_φ, inclO_iTot_E_pow]

theorem j_frob {EE : FCrys l ↥(OL (ϖ.field a))} {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    {ρ : ↥(GK (ϖ.field a)) → (T →ₗ[ℤ_[l]] T)}
    {j : EE.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (H : Realises (ϖ.field a) EE (ainfObj _) (ainfId _) T ρ j) (x m : EE.M (ϖ.prism a)) (k : ℕ)
    (h : IsFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k) :
    j (EE.tr (ϖ.toAinf a) m) = inclW l (ϖ.ev a (eis l a e)) ^ k •
      TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (EE.tr (ϖ.toAinf a) x)) := by
  let d : ↥(ainfObj (ϖ.field a)).I := ⟨ϖ.ev a (eis l a e), ϖ.theta_ev_eis a⟩
  obtain ⟨n, i, hn⟩ := exists_isFrac (d : (ainfObj (ϖ.field a)).A) (EE.Φ _ d (EE.tr (ϖ.toAinf a) x))
  obtain ⟨r, hr⟩ := EE.Φ_nat (ϖ.toAinf a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ d x m k n i h hn
  have h1 := H.j_φ d (ev_eis_ne_zero ϖ) _ n i hn
  have : IsDomain (ainfObj (ϖ.field a)).A := (ainfId (ϖ.field a)).toMulEquiv.isDomain
  have := EE.proj (ainfObj (ϖ.field a))
  have h0 : (d : (ainfObj (ϖ.field a)).A) ≠ 0 := ev_eis_ne_zero ϖ
  have h2 : (d : (ainfObj (ϖ.field a)).A) ^ i • EE.tr (ϖ.toAinf a) m = (d : (ainfObj (ϖ.field a)).A) ^ k • n :=
    sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero h0 h0)))
  exact (smul_eq_of_isUnit j (ϖ.isUnit_inclW_ev_eis a) h2 h1).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : GlobalTheory.BKReal.Lat a O K ϖ) (I : Ident t ϖ P T), GlobalTheory.Published.BhattScholzeCrystallineLattices → IsBK I → ∃ (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c ∧ (∀ x, c x ∈ P.M) ∧ (∀ m ∈ P.M, ∃ x, c x = m) ∧ (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) ∧ (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) ∧ (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I hBS hBK
  letI := zlLat T
  obtain ⟨EE, j, H, him⟩ := hBK
  have h0 : ∃ J : EE.M (ϖ.prism a) →+ TW (OW l O) T, ∀ x, J x = kappa T (j (EE.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (j.toAddMonoidHom.comp (EE.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  obtain ⟨J, hJ⟩ := h0
  have h1 : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun y => by
    simp only [hJ]
    exact him y
  have h2 := exists_coord I J h1
  obtain ⟨c, hc, hcJ, hs⟩ := h2
  have hi : Function.Injective J := by
    have := EE.proj (ainfObj (ϖ.field a))
    have := EE.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact semiBC_injective (EE.tr_bc (ϖ.toAinf a)) (ev_injective ϖ)
      (semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  refine ⟨EE, c, fun x y hxy => hi ?_, hc, hs, fun w x => ?_, fun o => ?_, fun x m k h => ?_⟩
  · rw [hcJ, hcJ]
    simp only [hxy]
  · refine eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := congrArg j ((EE.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (j.map_smulₛₗ _ _))
    have h5 := h4.trans (kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  · have h3 := (hBS l _ _ _ (isAinf_ainfObj (ϖ.field a))).2 _ _ _ _ EE EE j j H H (mulZ T o)
      fun g x => ((T.actT g).map_smul o x).symm
    obtain ⟨U, hU, -⟩ := h3
    refine ⟨U, fun x => eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_⟩
    have h3 := (congrArg j (U.u_tr (ϖ.toAinf a) x)).symm.trans (hU _)
    have h4 := (congrArg (kappa T) h3).trans (kappa_mulZ T o _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  · refine eq_of_j_eq_phi I k (hc x) ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := (congrArg (kappa T) (j_frob H x m k h)).trans (kappa_smul T _ _)
    have h4 := kappa_frob T (j (EE.tr (ϖ.toAinf a) x))
    rewrite [← hcJ, ← hcJ, hJ, hJ, ← h4]
    exact h3

end GlobalTheory.BKCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomExtOfXStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_prism_hom_ext_of_X : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (g g' : Hom bk.prism C), BK.hf g X = BK.hf g' X → g = g' := by
  first | exact @GlobalTheory.BSP.BK.hom_ext_of_hf_X | exact GlobalTheory.BSP.BK.hom_ext_of_hf_X | (intros; apply GlobalTheory.BSP.BK.hom_ext_of_hf_X <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinCompactnessStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_quotient_eisenstein_compactness : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type) [Finite ι] (m : ℕ) (Q : ℕ → (ι → bk.S) → Prop), (∀ n x, Q (n + 1) x → Q n x) → (∀ n x y, Q n x → (∀ i, x i - y i ∈ Ideal.span {(l : bk.S) ^ n} ⊔ Ideal.span {bk.E ^ m}) → Q n y) → (∀ n, ∃ x, Q n x) → ∃ x, ∀ n, Q n x := by
  first | (exact @GlobalTheory.BKLim.Cpt.compact) | (exact GlobalTheory.BKLim.Cpt.compact) | (intros; apply GlobalTheory.BKLim.Cpt.compact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem toDisc_injective_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 →
    Function.Injective (toDisc l (s X) ρ) ∧
    (∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s) ∧
    ∀ ρ' : ℝ≥0, 0 < ρ' → ρ' ≤ ρ → ∀ R : Disc l (s X) ρ →+* Disc l (s X) ρ', IsDiscMap (RingHom.id A) R →
      Function.Injective R := by
  intro l _ K bk A _ s ι TB ρ hρ hρ1
  have hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
  obtain ⟨-, -, -, -, h5⟩ := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
  have hlW : (l : Wq l bk.a) ≠ 0 := WittVector.p_nonzero l (Fq l bk.a)
  have hCl : (C (l : Wq l bk.a) : bk.S) = (l : bk.S) := map_natCast _ l
  have hlS0 : (l : bk.S) ≠ 0 := by
    rw [← hCl]; exact fun h => hlW (C_injective (h.trans (map_zero _).symm))
  have hlA : (l : A) ∈ nonZeroDivisors A := by
    simpa [map_natCast] using h5 _ (mem_nonZeroDivisors_of_ne_zero hlS0)
  have htor : ∀ x : A, (l : A) * x = 0 → x = 0 := fun x hx =>
    (mem_nonZeroDivisors_iff_right.1 hlA x) (by rw [mul_comm]; exact hx)
  have hdvd : ∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x := by
    intro m x y hxy
    rw [← map_pow, GlobalTheory.T.dvd_iff_dvd_coeff_breuilKisin l K bk A s ι TB]
    intro i
    have e := congrArg (TB.c i) hxy
    rw [← map_natCast s l, ← map_pow, TB.c_mul, TB.c_mul] at e
    have hd : X ^ m ∣ (l : bk.S) * TB.c i x := ⟨_, e⟩
    rw [PowerSeries.X_pow_dvd_iff] at hd ⊢
    intro k hk
    have := hd k hk
    rw [← hCl, coeff_C_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hlW
  have small := GlobalTheory.T.mem_breuilKisinIdeal_pow_of_norm_le l K bk A s htor hdvd ρ hρ hρ1
  refine ⟨?_, small, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have hmem : ∀ n : ℕ, x ∈ (bk.J.map s) ^ n := fun n => by
      obtain ⟨r, hr, h⟩ := small n
      rw [← Ideal.map_pow]
      exact h x (by rw [hx, norm_zero]; exact hr.le)
    have hHA : IsHausdorff (bk.J.map s) A := TB.complete.toIsHausdorff
    refine hHA.haus x fun n => ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact hmem n
  · intro ρ' hρ' hρ'ρ R hR
    have hρ'1 : ρ' < 1 := lt_of_le_of_lt hρ'ρ hρ1
    have h1 : ‖toDisc l (s X) ρ (s X)‖ ≤ ρ := by
      simpa using norm_toDisc_pow_le (l := l) (u := s X) (ρ := ρ) 1 hρ
    have h1' : ‖toDisc l (s X) ρ' (s X)‖ ≤ ρ' := by
      simpa using norm_toDisc_pow_le (l := l) (u := s X) (ρ := ρ') 1 hρ'
    have h2 : ‖toDisc l (X : bk.S) ρ' (RingHom.id bk.S X)‖ ≤ ρ := by
      have := norm_toDisc_pow_le (l := l) (u := (X : bk.S)) (ρ := ρ') 1 hρ'
      simp only [pow_one] at this
      exact this.trans (by exact_mod_cast hρ'ρ)
    obtain ⟨cD, hc1, -, hcn, -, -, hsup, -, -⟩ :=
      GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ hρ1 (Disc.map s h1) (isDiscMap_map s h1)
    obtain ⟨cD', hc1', -, hcn', -, -, -, -, -⟩ :=
      GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ' hρ' hρ'1 (Disc.map s h1') (isDiscMap_map s h1')
    set RS : bk.DS ρ →+* bk.DS ρ' := Disc.map (RingHom.id bk.S) h2 with hRS
    have hRSd : IsDiscMap (RingHom.id bk.S) RS := isDiscMap_map _ h2
    have injS : Function.Injective RS := GlobalTheory.T.breuilKisin_closedDisc_restrict_injective l K bk ρ ρ' hρ' hρ'ρ hρ1 RS hRSd
    obtain ⟨-, hlnorm, -, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ'
    obtain ⟨-, -, hext, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ
    have hlpos : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
    have htorD : ∀ z : bk.DS ρ', l • z = 0 → z = 0 := by
      intro z hz
      rw [nsmul_eq_mul] at hz
      have := hlnorm z
      rw [hz, norm_zero] at this
      exact norm_eq_zero.1 ((div_eq_zero_iff.1 this.symm).resolve_right hlpos.ne')
    have hRc : Continuous R :=
      AddMonoidHomClass.continuous_of_bound R 1 fun x => (hR.norm_le x).trans (one_mul _).ge
    have hRSc : Continuous RS :=
      AddMonoidHomClass.continuous_of_bound RS 1 fun x => (hRSd.norm_le x).trans (one_mul _).ge
    have key : ∀ i y, cD' i (R y) = RS (cD i y) := by
      intro i y
      have hF : Continuous ((cD' i).comp R.toAddMonoidHom) :=
        (AddMonoidHomClass.continuous_of_bound (cD' i) 1 fun z => (hcn' i z).trans (one_mul _).ge).comp hRc
      have hG : Continuous (RS.toAddMonoidHom.comp (cD i)) :=
        hRSc.comp (AddMonoidHomClass.continuous_of_bound (cD i) 1 fun z => (hcn i z).trans (one_mul _).ge)
      have := hext (bk.DS ρ') htorD ((cD' i).comp R.toAddMonoidHom) (RS.toAddMonoidHom.comp (cD i)) hF hG
        (fun a => by
          change cD' i (R (toDisc l (s X) ρ a)) = RS (cD i (toDisc l (s X) ρ a))
          rw [hR.ext, hc1, hc1', hRSd.ext]; rfl)
      exact DFunLike.congr_fun this y
    refine (injective_iff_map_eq_zero R).2 fun y hy => ?_
    have hz : ∀ i, cD i y = 0 := fun i =>
      injS (by rw [← key, hy, map_zero, map_zero])
    exact norm_le_zero_iff.1 (hsup y 0 le_rfl fun i => by rw [hz, norm_zero])

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateNegativeJumpCountOfGoodHodgeJumpsStatement
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateNegativeJumpCount_of_goodHodgeJumps : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NegCount bkP i s := by
  first | exact @GlobalTheory.TripleGal.negCount_of_goodJ | exact GlobalTheory.TripleGal.negCount_of_goodJ | (intros; apply GlobalTheory.TripleGal.negCount_of_goodJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupDivisibleImageCoboundaryIffFiniteLevelStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_divisible_image_coboundary_iff_finite_level : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (d : ↥(latticeCocycles LA)) (c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => GlobalTheory.BKFinLevel.ioL LA' ϖ r (c' g))) ↔ CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r (redT LA _ d) c') := by
  first | exact @GlobalTheory.BKFinLevel.cobO_cupLD_ioL_iff | exact GlobalTheory.BKFinLevel.cobO_cupLD_ioL_iff | (intros; apply GlobalTheory.BKFinLevel.cobO_cupLD_ioL_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaAddSubMemPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ) (x : A), ∀ y ∈ J ^ (n + 1), D.δ (x + y) - D.δ x ∈ J ^ n := by
  first | exact @GlobalTheory.BSP.delta_add_sub_mem_pow | exact GlobalTheory.BSP.delta_add_sub_mem_pow | (intros; apply GlobalTheory.BSP.delta_add_sub_mem_pow <;> assumption)
end

