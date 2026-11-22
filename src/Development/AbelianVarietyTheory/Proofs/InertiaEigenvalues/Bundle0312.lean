import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelOrderExponentsSmallValuationDetermina
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0298
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnits
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.BdRTied

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def tu : P.R.BdRˣ := Units.map (P.ιB : P.R.B →* P.R.BdR) (isUnit_tB P).unit

theorem tu_val : (tu P : P.R.BdR) = P.ιB P.tB := by
  simp [tu]

theorem tz_eq (a : ℤ) : tz P a = ((tu P ^ a : P.R.BdRˣ) : P.R.BdR) := by
  rw [tz, tu, ← map_zpow]
  rfl

theorem fil_anti_le {a b : ℤ} (h : a ≤ b) (x : P.R.BdR) (hx : x ∈ Fil P b) : x ∈ Fil P a := by
  induction b, h using Int.le_induction with
  | base => exact hx
  | succ b _ ih => exact ih ((P.PD (botExt l)).Fil_anti b hx)

theorem ι_injective : Function.Injective P.ιB := fun a b h =>
  (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι]; exact h)

theorem fil_mul (a b : ℤ) (x y : P.R.BdR) (hx : x ∈ Fil P a) (hy : y ∈ Fil P b) : x * y ∈ Fil P (a + b) :=
  (P.PD (botExt l)).Fil_mul a b x y hx hy

theorem fil_act (a : ℤ) (g : GQ l) (x : P.R.BdR) (hx : x ∈ Fil P a) : P.actQdR g x ∈ Fil P a := by
  have h := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_botExt g⟩ a x hx
  rwa [P.PD_actdR] at h

theorem actQ_tpow (g : GQ l) (a : ℤ) : P.actQ g (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (isUnit_tB P).unit =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * (isUnit_tB P).unit := by
    apply Units.ext
    simpa [Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  have hι : ∀ b : P.R.B, P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := fun b => by
    have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
    rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
    exact h.symm
  rw [tz, hι, actQ_tpow, map_mul, AlgHom.commutes]

variable {AI : LocAinf l P}

theorem fil_step (T : LocTied l P AI) (a : ℤ) (x : P.R.BdR) : x ∈ Fil P a ↔ P.ιB P.tB * x ∈ Fil P (a + 1) := by
  have h := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 (botExt l) a (P.ιB P.tB * x))
  change x ∈ (P.PD (botExt l)).Fil a ↔ P.ιB P.tB * x ∈ (P.PD (botExt l)).Fil (a + 1)
  rw [h]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, e⟩
    have hu : IsUnit (P.ιB P.tB) := tu_val P ▸ (tu P).isUnit
    rwa [hu.mul_left_cancel e]

theorem fil_tz (T : LocTied l P AI) (b : ℤ) : ∀ (a : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b) := by
  induction b using Int.induction_on with
  | zero => intro a x; simp [tz_eq]
  | succ b ih =>
    intro a x
    rw [ih a x, fil_step P T (a + b), tz_eq, tz_eq, zpow_add_one, Units.val_mul, tu_val, ← add_assoc]
    ring_nf
  | pred b ih =>
    intro a x
    rw [ih a x, fil_step P T (a + (-(b : ℤ) - 1)), tz_eq, tz_eq, ← tu_val, ← mul_assoc, ← Units.val_mul,
      ← zpow_one_add]
    ring_nf

theorem isField (T : LocTied l P AI) : IsField P.R.BdR := by
  obtain ⟨-, -, hF, -⟩ := GlobalTheory.MemLoc.BdRField.bdR_isField l
  exact MulEquiv.isField hF T.eD.toMulEquiv

theorem unit_of_fil (T : LocTied l P AI) (x : P.R.BdR) (h0 : x ∈ Fil P 0) (h1 : x ∉ Fil P 1) :
    ∃ y ∈ Fil P 0, x * y = 1 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have he : GlobalTheory.MemLoc.IsEps AI.ε := hC.ε ▸ GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨-, hker, hunit, -, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  have h0' : T.eD x ∈ Formalism.Per.FilD l 0 := (T.fil (botExt l) 0 x).1 h0
  obtain ⟨w, hw⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he 0 (T.eD x)).1 h0'
  rw [zpow_zero, Units.val_one, one_mul] at hw
  have hθ : Formalism.Per.θD l w ≠ 0 := by
    intro hz
    apply h1
    change x ∈ (P.PD (botExt l)).Fil 1
    rw [T.fil, hw]
    have := GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD 1 ((hker w).1 hz)
    simpa using this
  obtain ⟨w', hw'⟩ := (hunit w hθ).exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) w'), ?_, T.eD.injective ?_⟩
  · change _ ∈ (P.PD (botExt l)).Fil 0
    rw [T.fil, RingEquiv.apply_symm_apply]
    exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero w'
  · rw [map_mul, RingEquiv.apply_symm_apply, hw, ← map_mul, hw', map_one, map_one]

theorem exact_deg (x : P.R.BdR) (hx : x ≠ 0) : ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1) := by
  classical
  obtain ⟨a₀, ha₀⟩ := (P.PD (botExt l)).Fil_exh x
  have hc : ∃ c, x ∉ Fil P c := by
    by_contra h
    push_neg at h
    exact hx ((P.PD (botExt l)).Fil_sep x h)
  obtain ⟨c, hc⟩ := hc
  have hbd : ∀ z : ℤ, x ∈ Fil P z → z ≤ c := fun z hz => by
    by_contra hlt
    exact hc (fil_anti_le P (le_of_lt (not_le.1 hlt)) x hz)
  obtain ⟨a, ha, hmax⟩ := Int.exists_greatest_of_bdd ⟨c, hbd⟩ ⟨a₀, ha₀⟩
  exact ⟨a, ha, fun h => by have := hmax _ h; omega⟩

end GlobalTheory.PMon.BdRTied

namespace GlobalTheory.PMon

theorem bdR_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    IsField P.R.BdR ∧ Function.Injective P.ιB ∧
    (∀ (a b : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b)) ∧
    (∀ x ∈ Fil P 0, x ∉ Fil P 1 → ∃ y ∈ Fil P 0, x * y = 1) ∧
    (∀ x : P.R.BdR, x ≠ 0 → ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1)) ∧
    (∀ (a b : ℤ) (x y : P.R.BdR), x ∈ Fil P a → y ∈ Fil P b → x * y ∈ Fil P (a + b)) ∧
    (∀ (a : ℤ) (g : GQ l) (x : P.R.BdR), x ∈ Fil P a → P.actQdR g x ∈ Fil P a) ∧
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 ∧ tz P 1 = P.ιB P.tB := by
  intro l _ P AI T
  refine ⟨BdRTied.isField P T, BdRTied.ι_injective P, fun a b x => BdRTied.fil_tz P T b a x,
    fun x h0 h1 => BdRTied.unit_of_fil P T x h0 h1, BdRTied.exact_deg P, BdRTied.fil_mul P,
    BdRTied.fil_act P, fun a g => BdRTied.act_tz P g a, fun a b => ?_, ?_, ?_⟩
  · rw [BdRTied.tz_eq, BdRTied.tz_eq, BdRTied.tz_eq, zpow_add, Units.val_mul]
  · rw [BdRTied.tz_eq, zpow_zero, Units.val_one]
  · rw [BdRTied.tz_eq, zpow_one, BdRTied.tu_val]

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiAdicFiltrationModEll
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl

section Abstract

variable {O : Type} [CommRing O] {n : ℕ} {EE RA R : Type} [CommRing EE] [CommRing RA] [CommRing R]

theorem letA_dvd_of_forall_pow (p : ℕ) (a : LetA O n)
    (h : ∀ m : ℕ, ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2) :
    ∃ b : LetA O n, a = (p : LetA O n) * b := by
  have h1 : ∀ (i : ZMod n) (k : ℕ), ∃ c : O, PowerSeries.coeff k (a i) = (p : O) * c := by
    intro i k
    obtain ⟨a1, a2, h2⟩ := h (k + 1)
    refine ⟨PowerSeries.coeff k (a2 i), ?_⟩
    have h3 : a i = PowerSeries.X ^ (k + 1) * a1 i + PowerSeries.C (p : O) * a2 i := by
      rw [h2, map_natCast]; rfl
    rw [h3, map_add, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_add,
      PowerSeries.coeff_C_mul]
  choose c hc using h1
  refine ⟨fun i => PowerSeries.mk (c i), funext fun i => PowerSeries.ext fun k => ?_⟩
  have h3 : ((p : LetA O n) * fun i => PowerSeries.mk (c i)) i =
      PowerSeries.C (p : O) * PowerSeries.mk (c i) := by
    rw [map_natCast]; rfl
  rw [h3, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem near_abstract (p : ℕ) (f : LetA O n →+* EE) (io : EE →+* R) (ι : RA →+* R) (t : R)
    (τ : RA) (hτ : ι τ = t) (ht : io (f letπ) = t) (hu : IsUnit (f letπ))
    (hd : ∀ x : EE, ∃ (a : LetA O n) (m : ℕ), x * f (letπ ^ m) - f a ∈ Ideal.span {(p : EE) ^ 1})
    (hs : ∀ a : LetA O n, f a ∈ Ideal.span {(p : EE) ^ 1} →
      ∃ b : LetA O n, a = (p : LetA O n) ^ 1 * b)
    (key : ∀ (m : ℕ) (a : LetA O n), Near ι p t m (io (f a)) →
      ∃ a1 a2 : LetA O n, a = letπ ^ m * a1 + (p : LetA O n) * a2) :
    (∀ (m : ℕ) (e : EE), Near ι p t m (io e) →
      ∃ (a : LetA O n) (e' : EE), e = f (letπ ^ m * a) + (p : EE) * e') ∧
    ∀ (e : EE) (r : R), io e = (p : R) * r → ∃ e' : EE, e = (p : EE) * e' := by
  have H1 : ∀ (m : ℕ) (e : EE), Near ι p t m (io e) →
      ∃ (a : LetA O n) (e' : EE), e = f (letπ ^ m * a) + (p : EE) * e' := by
    intro m e he
    obtain ⟨a, N, h1⟩ := hd e
    rw [pow_one, Ideal.mem_span_singleton] at h1
    obtain ⟨e1, h1⟩ := h1
    have h2 : f a = f letπ ^ N * e - p * e1 := by
      rw [map_pow] at h1; linear_combination -h1
    have h3 : Near ι p t (N + m) (io (f a)) := by
      rw [h2, map_sub, map_mul, map_mul, map_pow, ht, map_natCast]
      refine Near.sub (Near.mul ?_ he) (Near.of_mul _ _)
      simpa using Near.pow_mul (ι := ι) (p := p) (t := t) N 1
    obtain ⟨a1, a2, h4⟩ := key _ _ h3
    obtain ⟨u, hu'⟩ := hu.exists_right_inv
    have h5 : f letπ ^ N * u ^ N = 1 := by rw [← mul_pow, hu', one_pow]
    refine ⟨a1, u ^ N * (e1 + f a2), ?_⟩
    rw [h4, map_add, map_mul, map_mul, map_pow, map_natCast, pow_add] at h2
    rw [map_mul, map_pow]
    linear_combination (-u ^ N) * h2 - (e - f letπ ^ m * f a1) * h5
  refine ⟨H1, fun e r he => ?_⟩
  have h1 := fun m => H1 m e (he ▸ Near.of_mul m r)
  choose a e' h2 using h1
  obtain ⟨b, hb⟩ := letA_dvd_of_forall_pow p (a 0) fun m => by
    obtain ⟨b, hb⟩ := hs (a 0 - letπ ^ m * a m) (by
      rw [pow_one, Ideal.mem_span_singleton]
      refine ⟨e' m - e' 0, ?_⟩
      have h3 := h2 0
      rw [pow_zero, one_mul] at h3
      rw [map_sub]
      linear_combination h2 m - h3)
    exact ⟨a m, b, by linear_combination hb⟩
  refine ⟨f b + e' 0, ?_⟩
  have h3 := h2 0
  rw [pow_zero, one_mul, hb, map_mul, map_natCast] at h3
  linear_combination h3

end Abstract

set_option maxHeartbeats 1000000 in

theorem near_ioE : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : Wach P K LL) (E : EtSit P AI K s LL h W), (∀ (m : ℕ) (e : W.EE), NearPi AI LL s m (E.tie.ioE e) → ∃ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) (e' : W.EE), e = algebraMap (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) W.EE (letπ ^ m * a) + (l : W.EE) * e') ∧ ∀ (e : W.EE) (r : RW LL), E.tie.ioE e = (l : RW LL) * r → ∃ e' : W.EE, e = (l : W.EE) * e' := by
  intro l _ P AI K s LL h W E
  have hd := W.EE_dense
  have hs := W.EE_sat
  rw [P.PD_p K] at hd hs
  exact near_abstract l (algebraMap _ W.EE) (E.tie.ioE : W.EE →+* RW LL)
    (inclR LL : RA LL →+* RW LL) (piR AI LL s) _ rfl (GlobalTheory.T.etaleEmbedding_frobenius_galois_compat l P AI K s LL h W E).2.2.1
    W.EE_π (fun x => hd x 1) (fun a => hs a 1)
    (fun m a ha => GlobalTheory.T.mem_pi_pow_ell_of_nearPi l P AI K s LL h W E m a (E.tie.ioE_ext a ▸ ha))

end GlobalTheory.Decompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffTensorAcrisWithFrobeniusGalois
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.MemLoc GlobalTheory.ExpImage
open scoped Formalism.Per

namespace GlobalTheory.HWLCris

section

variable {l : ℕ} [Fact l.Prime]

theorem alg_alg (a : Per.Ainf l) : algebraMap (Per.Acris0 l) (Per.Acris l)
    (algebraMap (Per.Ainf l) (Per.Acris0 l) a) = algebraMap (Per.Ainf l) (Per.Acris l) a :=
  (GlobalTheory.RingIface.tower l a).symm

theorem exists_acris (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) :
    ∃ (W : Type) (_ : CommRing W) (a : Ainf l →+* W) (c : W →+* P.R.B) (φ : W →+* W)
      (γ : GQ l → (W →+* W)) (t : W), GlobalTheory.Decompl.LAdic.Good l W ∧ (∀ w, c (a w) = AI.ιA w) ∧
      (∀ w, φ (a w) = a (WittVector.frobenius w)) ∧ (∀ x, c (φ x) = P.φB (c x)) ∧
      (∀ g w, γ g (a w) = a (AI.actW g w)) ∧ (∀ g x, c (γ g x) = P.actQ g (c x)) ∧ c t = P.tB ∧
      (l : W) ∣ a AI.μ ^ (l - 1) ∧
      (∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ u z : W, ((n.factorial : ℕ) : W) * u =
        ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : W) * a AI.μ ^ (k + 1) ∧
        t - u = (l : W) ^ r * z) ∧
      ∀ m : ℕ, ∃ N : ℕ, ∀ x : W, (l : P.R.BdR) ^ N * P.ιB (c x) ∈ Lat AI m 0 := by
  obtain ⟨C, hC⟩ := FitsEx.exists_fits l P AI T
  have he : IsEps AI.ε := hC.ε ▸ core_isEps l C
  have hlog : IsLogA AI.ε C.t := hC.ε ▸ C.t_log
  have hc : ∀ x, T.eB ((T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x) =
      algebraMap (Per.Acris l) (Per.Bcris l) x := fun x => T.eB.apply_symm_apply _
  haveI := (acris_basic l).1
  refine ⟨Per.Acris l, inferInstance, algebraMap (Per.Ainf l) (Per.Acris l),
    T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l)), phiA l, fun g => sigA g, C.t,
    GlobalTheory.Decompl.LAdic.good_of_complete l _ (acris_basic l).2.1, fun w => T.eB.injective ?_, fun w => ?_,
    fun x => T.eB.injective ?_, fun g w => ?_, fun g x => T.eB.injective ?_, T.eB.injective ?_, ?_,
    fun r => ?_, fun m => ?_⟩
  · rw [hc, T.ιA]
    exact (GlobalTheory.RingIface.aB_eq_alg l w).symm
  · rw [← GlobalTheory.RingBasics.φA_apply]
    exact (GlobalTheory.CrisMaps.phiA_extends l).alg w
  · rw [T.frob, hc, hc]
    exact ((ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 x).symm
  · rw [locAinf_actW]
    exact (GlobalTheory.CrisMaps.sigA_extends g).alg w
  · rw [T.actB, hc, hc]
    exact ((ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.1 g x).symm
  · rw [hc, hC.t]
    rfl
  · obtain ⟨w, hw, -⟩ := exists_mu_pow_div l AI.ε he.1
    have hw' : ((l : ℕ) : Per.Acris0 l) * w =
        algebraMap (Per.Ainf l) (Per.Acris0 l) (mu AI.ε) ^ (l - 1) :=
      Subtype.ext (by simpa using hw)
    have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw'
    rw [map_mul, map_natCast, map_pow, alg_alg] at h2
    exact ⟨_, h2.symm⟩
  · obtain ⟨N, hN⟩ := hlog r
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨s, hs, z, hz⟩ := hN n hn
    refine ⟨_, z, ?_, hz⟩
    have hs' : ((n.factorial : ℕ) : Per.Acris0 l) * s =
        ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.Acris0 l) *
          (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu AI.ε)) ^ (k + 1) := by
      apply Subtype.val_injective
      rw [← Subalgebra.val_apply, ← Subalgebra.val_apply]
      simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, AlgHom.commutes]
      exact hs
    have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hs'
    simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, alg_alg] at h2
    exact h2
  · obtain ⟨j, hj, -, hb⟩ := GlobalTheory.CrisIncl.exists_restrict l _ T.incl
    obtain ⟨N, hN⟩ := hb m
    refine ⟨N, fun x => ?_⟩
    obtain ⟨a, h'⟩ := hN x
    refine ⟨a, ?_⟩
    have h1 : T.eD (P.ιB ((T.eB.symm.toRingHom.comp (algebraMap (Per.Acris l) (Per.Bcris l))) x)) =
        algebraMap (Per.BdRp l) (Per.BdR l) (j x) := hj x
    rw [T.fil, pow_zero, one_mul, map_sub, map_mul, map_pow, map_natCast, h1, io_apply,
      TiedUnif.eD_ιA T, ← map_natCast (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_pow, ← map_mul,
      ← map_sub]
    refine TiedUnif.alg_mem_FilD m ?_
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_sub, h', TiedUnif.ev_aDp, sub_self]

end

variable {l : ℕ} [Fact l.Prime]

theorem root_pow {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem dvd_sub_pow {R : Type} [CommRing R] (x : R) (s : ℕ) :
    (l : R) ∣ (x - 1) ^ l ^ s - (x ^ l ^ s - 1) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq (Fact.out : l.Prime) (x - 1) 1 s
  rw [sub_add_cancel, one_pow] at hr
  rw [hr]
  exact ⟨-((x - 1) * 1 * r), by ring⟩

theorem bounded_OL (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (LL : FinExt l)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ) :
    ∃ k : ℕ, ∀ o : ↥(OL LL), (l : P.R.BdR) ^ k * ι (o : ↥LL.1) ∈ Lat AI m 0 := by
  let e := GlobalTheory.Decompl.basisO LL
  choose k hk using fun i => (bounded_and_eventually_sub_mem_Lat l P AI T _
    (EmbFil.emb_mem_fil_zero l P AI T LL ι (e i : ↥LL.1)) m 0).1
  refine ⟨∑ i, k i, fun o => ?_⟩
  have ho : o ∈ Submodule.span ℤ_[l] (Set.range e) := e.mem_span o
  induction ho using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le'
      (Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
    rw [hj, pow_add, mul_assoc]
    exact Lat_anti AI (Nat.zero_le _) ((pow_mul_mem_Lat_iff AI).2 (hk i))
  | zero => simpa using zero_mem _
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add, map_add, mul_add]
    exact add_mem hx hy
  | smul z x _ hx =>
    have := qB_mul_mem_Lat AI T z hx
    rw [Subalgebra.coe_smul, ← algebraMap_smul ℚ_[l] z, map_smul, Algebra.smul_def, mul_left_comm]
    exact this

set_option maxHeartbeats 800000 in

theorem exists_tensor_acris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B), IsBeta AI β → ∃ (A : Type) (_ : CommRing A) (b : RA LL →+* A) (κ : A →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (φ : A →+* A) (γ : GQ l → (A →+* A)) (t : A), GlobalTheory.Decompl.LAdic.Good l A ∧ ((∀ y, κ (b y) = β y) ∧ (∀ o w, φ (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) ∧ (∀ x, κ (φ x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB (κ x)) ∧ (∀ g o w, γ g (b (o ⊗ₜ[ℤ_[l]] w)) = b (o ⊗ₜ[ℤ_[l]] AI.actW g w)) ∧ (∀ g x, κ (γ g x) = Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) (P.actQ g).toAlgHom (κ x)) ∧ κ t = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] P.tB) ∧ (∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (l : A) ∣ b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) ^ d) ∧ (∀ r : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ u z : A, ((n.factorial : ℕ) : A) * u = ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : A) * b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] AI.μ) ^ (k + 1) ∧ t - u = (l : A) ^ r * z) ∧ ∀ (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (m : ℕ), ∃ C : ℕ, ∀ y : A, (l : P.R.BdR) ^ C * Algebra.TensorProduct.productMap ι P.ιB (κ y) ∈ GlobalTheory.ExpImage.Lat AI m 0 := by
  intro l _ P AI T LL β hβ
  obtain ⟨W, _, a, c, φ, γ, t, hg, hca, hφa, hcφ, hγa, hcγ, hct, hμ, hlog, hb⟩ := exists_acris P AI T
  let _ : Algebra ℤ_[l] W := (a.comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra
  have hz : ∀ z : ℤ_[l], algebraMap ℤ_[l] W z = a (algebraMap ℤ_[l] (Ainf l) z) := fun _ => rfl
  let _ : Algebra ℤ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) :=
    ((algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  let f₁ : ↥(OL LL) →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom).comp (OL LL).val.toRingHom
      commutes' := fun z => by
        show ((algebraMap ℤ_[l] ↥LL.1 z) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1] }
  let f₂ : W →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)).toRingHom.comp c
      commutes' := fun z => by
        show Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)
            (c (a (algebraMap ℤ_[l] (Ainf l) z))) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [hca, ιA_zl AI T, AlgHom.commutes]
        rfl }
  obtain ⟨κ, hκ⟩ : ∃ κ : ↥(OL LL) ⊗[ℤ_[l]] W →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B,
      ∀ o x, κ (o ⊗ₜ[ℤ_[l]] x) = (o : ↥LL.1) ⊗ₜ[ℚ_[l]] c x := by
    refine ⟨(Algebra.TensorProduct.productMap f₁ f₂).toRingHom, fun o x => ?_⟩
    show Algebra.TensorProduct.productMap f₁ f₂ (o ⊗ₜ[ℤ_[l]] x) = _
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    show ((o : ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) * ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] c x) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  obtain ⟨b, hb'⟩ : ∃ b : RA LL →+* ↥(OL LL) ⊗[ℤ_[l]] W,
      ∀ o w, b (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] a w :=
    ⟨(Algebra.TensorProduct.map (AlgHom.id ℤ_[l] ↥(OL LL))
      ({ toRingHom := a, commutes' := fun _ => rfl } : Ainf l →ₐ[ℤ_[l]] W)).toRingHom, fun _ _ => rfl⟩
  have ext : ∀ f : W →+* W, (∀ z, f (algebraMap ℤ_[l] W z) = algebraMap ℤ_[l] W z) →
      ∃ F : ↥(OL LL) ⊗[ℤ_[l]] W →+* ↥(OL LL) ⊗[ℤ_[l]] W,
        ∀ o x, F (o ⊗ₜ[ℤ_[l]] x) = o ⊗ₜ[ℤ_[l]] f x := fun f hf =>
    ⟨(Algebra.TensorProduct.map (AlgHom.id ℤ_[l] ↥(OL LL))
      ({ toRingHom := f, commutes' := hf } : W →ₐ[ℤ_[l]] W)).toRingHom, fun _ _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ := ext φ fun z => by
    rw [hz, hφa, WittVector.frobenius_eq_map_frobenius]
    exact congrArg a (map_zlW l _ z)
  choose Γ hΓ using fun g => ext (γ g) fun z => by rw [hz, hγa, actW_zl]
  let j : W →+* ↥(OL LL) ⊗[ℤ_[l]] W := (Algebra.TensorProduct.includeRight (R := ℤ_[l])).toRingHom
  have hj : ∀ w, b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w) = j (a w) := fun w => hb' 1 w
  refine ⟨↥(OL LL) ⊗[ℤ_[l]] W, inferInstance, b, κ, Φ, Γ, j t,
    GlobalTheory.Decompl.LAdic.good_tensor (GlobalTheory.Decompl.basisO LL) l hg, ⟨fun y => ?_, fun o w => ?_, fun x => ?_,
    fun g o w => ?_, fun g x => ?_, ?_⟩, fun s => ?_, fun r => ?_, fun ι m => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w => rw [hb', hκ, hca, hβ]
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [hb', hb', hΦ, hφa]
  · induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w => rw [hΦ, hκ, hκ, hcφ]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [hb', hb', hΓ, hγa]
  · induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w => rw [hΓ, hκ, hκ, hcγ]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  · rw [← hct]
    exact hκ 1 t
  · have hl : 1 < l := (Fact.out : l.Prime).one_lt
    refine ⟨l ^ s * (l - 1), Nat.mul_pos (by positivity) (by omega), ?_⟩
    have h1 := dvd_sub_pow (l := l) (WittVector.teichmuller l (AI.εroot s)) s
    rw [← map_pow, root_pow] at h1
    have h2 := map_dvd a (h1.trans (sub_dvd_pow_sub_pow _ _ (l - 1)))
    rw [map_natCast, map_sub, map_pow a (_ - 1) (l - 1)] at h2
    have h3 := map_dvd j (dvd_add h2 hμ)
    rw [LocAinf.μ, sub_add_cancel, map_natCast, ← pow_mul, map_pow, map_pow] at h3
    rwa [hj]
  · obtain ⟨N, hN⟩ := hlog r
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨u, z, h1, h2⟩ := hN n hn
    refine ⟨j u, j z, ?_, ?_⟩
    · have := congrArg j h1
      simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast] at this
      rwa [hj]
    · have := congrArg j h2
      rwa [map_sub, map_mul, map_pow, map_natCast] at this
  · obtain ⟨k, hk⟩ := bounded_OL P AI T LL ι m
    obtain ⟨N, hN⟩ := hb m
    refine ⟨k + N, fun y => ?_⟩
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, map_zero, mul_zero]
      exact zero_mem _
    | tmul o w =>
      rw [hκ, Algebra.TensorProduct.productMap_apply_tmul, pow_add, mul_mul_mul_comm]
      exact Lat_anti AI (Nat.zero_le _) (Lat_mul AI (hk o) (hN w))
    | add x y hx hy =>
      rw [map_add, map_add, mul_add]
      exact add_mem hx hy

end GlobalTheory.HWLCris
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelOrderExponentsSmallValuationDeterminaStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_order_exponents_small_valuation_determinants : ∀ (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Finite (IsLocalRing.ResidueField O₀)] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)], Function.Injective (algebraMap O₀ O) → ∀ (l : ℕ), l.Prime → (l : O₀) ≠ 0 → ¬ IsUnit (l : O₀) → ∀ (R D nmax M₀ : ℕ) (I J : Type) [Finite I] [Finite J] (μ : I → ℕ) (v : J → ℕ) (F : ℕ → I → MvPolynomial (Fin R ⊕ Fin R) O₀) (f Dd g : ℕ → J → MvPolynomial (Fin R ⊕ Fin R) O), (∀ M, M₀ ≤ M → ∀ x, ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ D ∧ IsDiscreteValuationRing.addVal O₀ ((F M x).coeff m) ≤ μ x) → (∀ M, M₀ ≤ M → ∀ y, f M y - Dd M y * g M y ∈ Ideal.span (Set.range (fun i : Fin R => (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪ Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) ∧ IsDiscreteValuationRing.addVal O ((g M y).coeff 0) ≤ v y ∧ ∃ (u : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) (n : Fin R → ℕ), u.coeff 0 ≠ 0 ∧ (∀ i, n i ≤ nmax) ∧ (Dd M y).map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i ∈ Ideal.span (Set.range fun q => (MvPolynomial.X q : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M))) → ∀ ε : ℝ, 0 < ε → ∃ (M k : ℕ) (e : Fin R ⊕ Fin R → ℕ), M₀ ≤ M ∧ 1 ≤ k ∧ k ≤ M ∧ (∀ q, e q < k ∧ (l : ℝ) ^ e q / (Nat.totient (l ^ k) : ℝ) ≤ ε) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → (∀ x, MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) ((F M x).map (algebraMap O₀ O)) ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) ((F M x).map (algebraMap O₀ O))) ≤ (μ x : ℝ) / ((IsDiscreteValuationRing.addVal O₀ (l : O₀)).toNat : ℝ) + ε) ∧ (∀ y, MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) (f M y) ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) (f M y)) ≤ (v y : ℝ) / ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ) + ε) := by
  first | exact @GlobalTheory.OrderEval.order_eval | exact GlobalTheory.OrderEval.order_eval | (intros; apply GlobalTheory.OrderEval.order_eval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionModuleExtendingResidueMapsStatement
section
open CategoryTheory GlobalTheory.SelFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_module_extending_residue_maps : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] (P : Type) [AddCommGroup P] [Module Λ P] [Module.Finite Λ P] (N : Submodule Λ P),
  ∃ (B : ModuleCat.{0} Λ) (f : IsLocalRing.ResidueField Λ →ₗ[Λ] B), Tors Λ B ∧ Function.Injective f ∧
    ∀ φ : N →ₗ[Λ] IsLocalRing.ResidueField Λ, ∃ u : P →ₗ[Λ] B, u ∘ₗ N.subtype = f ∘ₗ φ := by
  first | exact @GlobalTheory.SelFun.exists_torsion_extension | exact GlobalTheory.SelFun.exists_torsion_extension | (intros; apply GlobalTheory.SelFun.exists_torsion_extension <;> assumption)
end

