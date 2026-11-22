import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0225
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamInvariantsCoordinatesFinrankEq
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem deRham_invariants_coord_finrank :
    ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), FiniteDimensional Qp LL → Module.Finite LL ↥(DdR PD ρ) → Module.finrank LL ↥(DdR PD ρ) = Module.finrank Qp K * Module.finrank LL V → ∀ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i))) → ∃ D : Submodule K (Fin d → BdR), (∀ y, y ∈ D ↔ ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (y i)) = y) ∧ Module.Finite K ↥D ∧ Module.finrank K ↥D = d := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ d bV hL hfin hrk Φ hΦ
  haveI := PD.finK
  let D : Submodule K (Fin d → BdR) :=
    { carrier := {y | ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec
          (fun i => PD.actdR g (y i)) = y}
      add_mem' := by
        intro a b ha hb g
        have : (fun i => PD.actdR g ((a + b) i)) =
            (fun i => PD.actdR g (a i)) + (fun i => PD.actdR g (b i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, ha g, hb g]
      zero_mem' := by
        intro g
        have : (fun i => PD.actdR g ((0 : Fin d → BdR) i)) = 0 := by
          funext i; simp
        rw [this, Matrix.mulVec_zero]
      smul_mem' := by
        intro c a ha g
        have : (fun i => PD.actdR g ((c • a) i)) = c • (fun i => PD.actdR g (a i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_smul, ha g] }
  have hmem : ∀ z, z ∈ DdR PD ρ ↔ Φ z ∈ D := by
    intro z
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    refine forall_congr' fun g => ?_
    rw [← hΦ g z]
    exact Φ.injective.eq_iff.symm
  let e : ↥(DdR PD ρ) ≃ₗ[Qp] ↥D :=
    { toFun := fun z => ⟨Φ z.1, (hmem _).1 z.2⟩
      invFun := fun y => ⟨Φ.symm y.1, (hmem _).2 (by simpa using y.2)⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp)
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  haveI : Module.Finite Qp ↥(DdR PD ρ) := Module.Finite.trans LL _
  haveI : Module.Finite Qp ↥D := Module.Finite.equiv e
  refine ⟨D, fun y => Iff.rfl, Module.Finite.of_restrictScalars_finite Qp K _, ?_⟩
  have h1 := Module.finrank_mul_finrank Qp K ↥D
  have h2 := Module.finrank_mul_finrank Qp LL ↥(DdR PD ρ)
  have h3 := Module.finrank_mul_finrank Qp LL V
  have h4 : Module.finrank Qp V = d := by simpa using Module.finrank_eq_card_basis bV
  have h5 := e.finrank_eq
  have hpos : 0 < Module.finrank Qp K := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, ← h5, ← h2, hrk, ← h4, ← h3]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfPowEqOneOfNormSubLtOne
section
namespace GlobalTheory.RootsOfUnityClose

theorem geom_sum_close {K : Type*} [NormedField K] [IsUltrametricDist K] {z : K}
    (hz : ‖z - 1‖ < 1) (n : ℕ) :
    ‖z ^ n - 1‖ < 1 ∧ ‖(∑ i ∈ Finset.range n, z ^ i) - (n : K)‖ < 1 := by
  have hz1 : ‖z‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (z - 1) 1
    rw [sub_add_cancel, norm_one] at h
    exact h.trans (max_le hz.le le_rfl)
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    constructor
    · have e : z ^ (n + 1) - 1 = z * (z ^ n - 1) + (z - 1) := by ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ hz)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hz1).trans_lt h1
    · have e : (∑ i ∈ Finset.range (n + 1), z ^ i) - ((n + 1 : ℕ) : K)
          = ((∑ i ∈ Finset.range n, z ^ i) - (n : K)) + (z ^ n - 1) := by
        rw [Finset.sum_range_succ]; push_cast; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h1)

theorem norm_natCast_eq_one {l : ℕ} [Fact l.Prime] {m : ℕ} (h : ¬ l ∣ m) :
    ‖(m : PadicAlgCl l)‖ = 1 := by
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := by simp
  rw [e, norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h)

theorem eq_of_pow_eq_one_of_norm_sub_lt_one {l : ℕ} [Fact l.Prime] {m : ℕ} (hm : 0 < m)
    (hl : ¬ l ∣ m) {a b : Formalism.BasicNotions.Loc.Om l} (ha : a ^ m = 1) (hb : b ^ m = 1)
    (hab : ‖a - b‖ < 1) : a = b := by
  have hb1 : ‖b‖ = 1 := by
    have h : ‖b‖ ^ m = 1 := by rw [← norm_pow, hb, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').mp h
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hb1; exact zero_ne_one hb1
  have hz : ‖a / b - 1‖ < 1 := by
    rw [div_sub_one hb0, norm_div, hb1, div_one]; exact hab
  have hzm : (a / b) ^ m = 1 := by rw [div_pow, ha, hb, div_one]
  by_contra hne
  have hne1 : a / b - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    exact hne ((div_eq_one_iff_eq hb0).mp h)
  have hs : (∑ i ∈ Finset.range m, (a / b) ^ i) = 0 := by
    have h := geom_sum_mul (a / b) m
    rw [hzm, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right hne1
  have h := (geom_sum_close hz m).2
  rw [hs, zero_sub, norm_neg, norm_natCast_eq_one hl] at h
  exact lt_irrefl _ h

end GlobalTheory.RootsOfUnityClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfFrobeniusIterateEqXiMul
section
open Formalism
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PeriodSol
open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem dvd_of_constantCoeff (x : Per.Ainf l) (h : WittVector.constantCoeff x = 0) :
    (l : Per.Ainf l) ∣ x := by
  have h0 := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) x 0
  have hI : (Finset.Iic 0 : Finset ℕ) = {0} := by ext i; simp
  rw [hI, Finset.sum_singleton] at h0
  rw [WittVector.constantCoeff_apply] at h
  simpa [h] using h0

theorem constantCoeff_natCast_mul (x : Per.Ainf l) :
    WittVector.constantCoeff ((l : Per.Ainf l) * x) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem iterate_tm (n : ℕ) (y : Per.Fl l) :
    (⇑(Per.φA l))^[n] (Per.tm y) = Per.tm (y ^ (l ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller,
      frobenius_def, ← pow_mul, ← pow_succ]

theorem smod_iff (m : ℕ) (x y : Per.Ainf l) :
    x ≡ y [SMOD ((Ideal.span {(l : Per.Ainf l)}) ^ m • ⊤ : Submodule (Per.Ainf l) (Per.Ainf l))] ↔
      (l : Per.Ainf l) ^ m ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem xi_bar_ne_zero (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) :
    WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) ≠ 0 := by
  set e' := (frobeniusEquiv (Per.Fl l) l).symm e with he'
  have hxi : WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) = ∑ i ∈ Finset.range l, e' ^ i := by
    simp [GlobalTheory.MemLoc.xi, map_sum, map_pow, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, he']
  have hpow : e' ^ l = e := by
    have := (frobeniusEquiv (Per.Fl l) l).apply_symm_apply e
    rwa [frobeniusEquiv_apply, ← he'] at this
  intro h0
  rw [hxi] at h0
  have h1 := geom_sum_mul e' l
  rw [h0, zero_mul, hpow] at h1
  have he1 : e = 1 := (sub_eq_zero.1 h1.symm)
  apply he.2
  rw [he1, map_one]
  simp

end GlobalTheory.PeriodSol

namespace GlobalTheory.PeriodSol
open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem exists_step (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) (n : ℕ) (hn : 0 < n) (c : Per.Ainf l) :
    ∃ y : Per.Fl l, (l : Per.Ainf l) ∣
      c + ((⇑(Per.φA l))^[n] (Per.tm y) - GlobalTheory.MemLoc.xi e * Per.tm y) := by
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
  set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)
  set b := WittVector.constantCoeff c
  have hdeg : (C b - C a * X : (Per.Fl l)[X]).degree < ((l ^ n : ℕ) : WithBot ℕ) := by
    have h1 : (C b - C a * X : (Per.Fl l)[X]).degree ≤ 1 := by compute_degree
    exact lt_of_le_of_lt h1 (by exact_mod_cast hq)
  have hmon : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).Monic := monic_X_pow_add hdeg
  have hnd : (X ^ (l ^ n) + (C b - C a * X) : (Per.Fl l)[X]).natDegree ≠ 0 := by
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
    omega
  obtain ⟨y, hy⟩ := GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd
  refine ⟨y, dvd_of_constantCoeff _ ?_⟩
  rw [iterate_tm]
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hy
  rw [map_add, map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _),
    WittVector.constantCoeff_apply (x := Per.tm _), WittVector.teichmuller_coeff_zero,
    WittVector.teichmuller_coeff_zero]
  rw [← hy]
  ring

theorem exists_start (e : Per.Fl l) (he : GlobalTheory.MemLoc.IsEps e) (n : ℕ) (hn : 0 < n) :
    ∃ w₀ : Per.Fl l, w₀ ≠ 0 ∧ w₀ ^ (l ^ n) = WittVector.constantCoeff (GlobalTheory.MemLoc.xi e) * w₀ := by
  have hq : 1 < l ^ n := Nat.one_lt_pow hn.ne' (Fact.out : l.Prime).one_lt
  set a := WittVector.constantCoeff (GlobalTheory.MemLoc.xi e)
  have hq1 : l ^ n - 1 ≠ 0 := by omega
  have hmon : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).Monic := monic_X_pow_sub_C a hq1
  have hnd : (X ^ (l ^ n - 1) - C a : (Per.Fl l)[X]).natDegree ≠ 0 := by
    rw [natDegree_X_pow_sub_C]; exact hq1
  obtain ⟨y, hy⟩ := GlobalTheory.TiltAlgClosed.exists_root_preTilt ℂ_[l] hmon hnd
  simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy
  refine ⟨y, ?_, ?_⟩
  · rintro rfl
    rw [zero_pow hq1] at hy
    exact xi_bar_ne_zero e he hy.symm
  · rw [← hy, ← pow_succ, Nat.sub_add_cancel hq.le]

theorem period_solution : ∀ (l : ℕ) [Fact l.Prime] (e : Per.Fl l), GlobalTheory.MemLoc.IsEps e →
    ∀ n : ℕ, 0 < n → ∃ w : Per.Ainf l, GlobalTheory.MemLoc.xi e * w ≠ 0 ∧
      (⇑(Per.φA l))^[n] w = GlobalTheory.MemLoc.xi e * w := by
  intro l _ e he n hn
  set ξ := GlobalTheory.MemLoc.xi e
  let Φ : Per.Ainf l →+* Per.Ainf l := Per.φA l ^ n
  have hΦ : ∀ x, (⇑(Per.φA l))^[n] x = Φ x := fun x => by simp [Φ, RingHom.coe_pow]
  let F : Per.Ainf l → Per.Ainf l := fun w => Φ w - ξ * w
  have F_sub : ∀ a b, F (a - b) = F a - F b := fun a b => by simp only [F, map_sub]; ring
  have F_lin : ∀ (m : ℕ) a b, F (a + (l : Per.Ainf l) ^ m * b) = F a + (l : Per.Ainf l) ^ m * F b :=
    fun m a b => by simp only [F, map_add, map_mul, map_pow, map_natCast]; ring
  have step : ∀ (k : ℕ) (w : Per.Ainf l), ∃ w' : Per.Ainf l,
      (l : Per.Ainf l) ^ (k + 1) ∣ F w →
        (l : Per.Ainf l) ^ (k + 2) ∣ F w' ∧ (l : Per.Ainf l) ^ (k + 1) ∣ w' - w := by
    intro k w
    by_cases hw : (l : Per.Ainf l) ^ (k + 1) ∣ F w
    · obtain ⟨c, hc⟩ := hw
      obtain ⟨y, d, hd⟩ := exists_step e he n hn c
      refine ⟨w + (l : Per.Ainf l) ^ (k + 1) * Per.tm y, fun _ => ⟨⟨d, ?_⟩, ⟨Per.tm y, by ring⟩⟩⟩
      rw [F_lin, hc, ← mul_add]
      have : F (Per.tm y) = (⇑(Per.φA l))^[n] (Per.tm y) - ξ * Per.tm y := by simp only [F, hΦ]
      rw [this, hd]; ring
    · exact ⟨w, fun h => absurd h hw⟩
  choose g hg using step
  obtain ⟨w₀, hw₀, hw₀q⟩ := exists_start e he n hn
  let seq : ℕ → Per.Ainf l := fun k => Nat.rec (Per.tm w₀) (fun k w => g k w) k
  have hseq0 : seq 0 = Per.tm w₀ := rfl
  have hseqS : ∀ k, seq (k + 1) = g k (seq k) := fun k => rfl
  have hF0 : (l : Per.Ainf l) ^ (0 + 1) ∣ F (seq 0) := by
    rw [zero_add, pow_one, hseq0]
    apply dvd_of_constantCoeff
    simp only [F, ← hΦ, iterate_tm, map_sub, map_mul, WittVector.constantCoeff_apply (x := Per.tm _),
      WittVector.teichmuller_coeff_zero, hw₀q]
    exact sub_self _
  have hF : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ F (seq k) := by
    intro k
    induction k with
    | zero => exact hF0
    | succ k ih => rw [hseqS]; exact (hg k (seq k) ih).1
  have hdiff : ∀ k, (l : Per.Ainf l) ^ (k + 1) ∣ seq (k + 1) - seq k := fun k => by
    rw [hseqS]; exact (hg k (seq k) (hF k)).2
  have hcau : ∀ m d, (l : Per.Ainf l) ^ m ∣ seq m - seq (m + d) := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have h2 : (l : Per.Ainf l) ^ m ∣ seq (m + d + 1) - seq (m + d) :=
        (pow_dvd_pow _ (by omega)).trans (hdiff (m + d))
      have : seq m - seq (m + (d + 1)) = (seq m - seq (m + d)) - (seq (m + d + 1) - seq (m + d)) := by
        rw [← add_assoc]; ring
      rw [this]; exact dvd_sub ih h2
  have hcomp : IsAdicComplete (Ideal.span {(l : Per.Ainf l)}) (Per.Ainf l) :=
    WittVector.isAdicCompleteIdealSpanP
  obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := seq) (fun {m n} hmn => by
    rw [smod_iff]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcau m d)
  have hL' : ∀ k, (l : Per.Ainf l) ^ k ∣ seq k - L := fun k => (smod_iff k _ _).1 (hL k)
  have hFL : F L = 0 := by
    refine hcomp.toIsHausdorff.haus (F L) fun k => ?_
    rw [smod_iff, sub_zero]
    obtain ⟨c, hc⟩ := hL' k
    have e1 : L = seq k + (l : Per.Ainf l) ^ k * (-c) := by rw [mul_neg, ← hc]; ring
    rw [e1, F_lin]
    exact dvd_add ((pow_dvd_pow _ (Nat.le_succ k)).trans (hF k)) (dvd_mul_right _ _)
  have hL0 : WittVector.constantCoeff L = w₀ := by
    obtain ⟨c, hc⟩ := hL' 1
    obtain ⟨c', hc'⟩ := hdiff 0
    have e1 : L = Per.tm w₀ + (l : Per.Ainf l) * (c' - c) := by
      rw [pow_one] at hc; rw [zero_add, pow_one] at hc'
      rw [mul_sub, ← hc, ← hc', ← hseq0]; ring
    rw [e1, map_add, constantCoeff_natCast_mul, add_zero, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
  refine ⟨L, fun h0 => ?_, ?_⟩
  · have := congrArg WittVector.constantCoeff h0
    rw [map_mul, map_zero, hL0] at this
    exact mul_ne_zero (xi_bar_ne_zero e he) hw₀ this
  · rw [hΦ]; exact sub_eq_zero.1 hFL

end GlobalTheory.PeriodSol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfFullLattice
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

theorem exists_basis_of_fullLattice {R F M V ι : Type} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module F V]
    (f : M →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (m : M), f (c • m) = algebraMap R F c • f m)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ m, algebraMap R F c • v = f m)
    (b0 : Module.Basis ι R M) :
    ∃ b : Module.Basis ι F V, (∀ j, b j = f (b0 j)) ∧
      ∀ m i, b.repr (f m) i = algebraMap R F (b0.repr m i) := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  haveI : IsScalarTower R F V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : M →ₗ[R] V := { toFun := f, map_add' := map_add f, map_smul' := hs }
  haveI : IsLocalizedModule (nonZeroDivisors R) g :=
    { map_units := fun s => by
        have h0 : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        rw [Module.End.isUnit_iff]
        exact MulAction.bijective (β := V) (Units.mk0 _ h0 : Fˣ)
      surj := fun v => by
        obtain ⟨c, hc, m, hm⟩ := hfull v
        exact ⟨(m, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hm⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  exact ⟨b0.ofIsLocalizedModule F (nonZeroDivisors R) g,
    fun j => b0.ofIsLocalizedModule_apply F _ g j,
    fun m i => b0.ofIsLocalizedModule_repr_apply F _ g m i⟩

theorem exists_basis_of_locLat {R G F LL O ι : Type} [CommRing R] [IsDomain R] [Group G]
    [TopologicalSpace G] [Field F] [Field LL] [Algebra F LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] [Algebra R F] [IsFractionRing R F] [Algebra R O] [Fintype ι]
    (T : LocLat G F LL O)
    (hc : ∀ c : R, algebraMap O LL (algebraMap R O c) = algebraMap F LL (algebraMap R F c))
    (hden : ∀ a : LL, ∃ c : R, c ≠ 0 ∧
      ∃ o : O, algebraMap O LL o = algebraMap F LL (algebraMap R F c) * a) :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ b0 : Module.Basis ι R ↥T.L.T, ∃ b : Module.Basis ι F T.V, (∀ j, b j = (b0 j : T.V)) ∧
      (∀ (m : ↥T.L.T) i, b.repr (m : T.V) i = algebraMap R F (b0.repr m i)) ∧
      (∀ (a : O) j i, b.repr (algebraMap O LL a • b j) i =
        algebraMap R F (b0.repr ⟨_, T.L.T.smul_mem a (b0 j).2⟩ i)) ∧
      ∀ v : T.V, (∀ i, ∃ c : R, b.repr v i = algebraMap R F c) → v ∈ T.L.T := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  intro b0
  have key : ∀ (c : R) (w : T.V), algebraMap R F c • w = algebraMap R O c • w := by
    intro c w
    rw [← algebraMap_smul LL (algebraMap R F c) w, ← algebraMap_smul LL (algebraMap R O c) w, hc]
  have hfull : ∀ v : T.V, ∃ c : R, c ≠ 0 ∧ algebraMap R F c • v ∈ T.L.T := by
    intro v
    have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨c', hc', hy⟩ := hy
      refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, map_mul, mul_smul, key c']
        exact T.L.T.smul_mem _ hx
      · rw [map_mul, mul_smul, key c]
        exact T.L.T.smul_mem _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨c', hc', o, ho⟩ := hden a
      refine ⟨c' * c, mul_ne_zero hc' hc, ?_⟩
      have := T.L.T.smul_mem o hx
      rw [← algebraMap_smul LL, ho, mul_smul, algebraMap_smul,
        smul_comm a (algebraMap R F c) x] at this
      rwa [map_mul, mul_smul]
  obtain ⟨b, hb, hr⟩ := exists_basis_of_fullLattice (R := R) (F := F)
    (T.L.T.subtype.toAddMonoidHom) Subtype.val_injective
    (fun c m => (key c m).symm)
    (fun v => by
      obtain ⟨c, hc, hv⟩ := hfull v
      exact ⟨c, hc, ⟨_, hv⟩, rfl⟩) b0
  refine ⟨b, hb, hr, fun a j i => ?_, fun v hv => ?_⟩
  · rw [← hr, hb, algebraMap_smul]
    rfl
  · rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hv i
    rw [hc, key, hb]
    exact T.L.T.smul_mem _ (b0 i).2

theorem exists_ratBasis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ b : Module.Basis (Fin d) ℚ_[l] T.V, (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr (T.ρ g (b j)) i)) ∧ (∀ (a : ↥(OL LL)) (i j : Fin d), A a i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr ((a : ↥LL.1) • b j) i)) ∧ ∀ v : T.V, v ∈ T.L.T ↔ ∀ i, ‖b.repr v i‖ ≤ 1 := by
  intro l _ K LL T d M A h
  letI := zlMod LL T
  obtain ⟨b0, hM, hA⟩ := h
  obtain ⟨b, hb, hr, ha, hv⟩ := exists_basis_of_locLat (R := ℤ_[l]) T (fun _ => rfl) (fun a => by
    have ha : IsAlgebraic ℤ_[l] a :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨c, hc, hint⟩ := ha.exists_integral_multiple
    exact ⟨c, hc, ⟨c • a, hint⟩, Algebra.smul_def c a⟩) b0
  refine ⟨b, fun g i j => ?_, fun a i j => ?_, fun v => ⟨fun h i => ?_, fun h => ?_⟩⟩
  · have e : T.ρ g (b j) = ((actTZ LL T g (b0 j) : ↥T.L.T) : T.V) := congrArg (T.ρ g) (hb j)
    rw [e]
    exact (hM g i j).trans
      (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (hr (actTZ LL T g (b0 j)) i).symm)
  · exact (hA a i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (ha a j i).symm)
  · exact (congrArg norm (hr ⟨v, h⟩ i)).trans_le (b0.repr ⟨v, h⟩ i).2
  · exact hv v fun i => ⟨⟨_, h i⟩, rfl⟩

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBeta
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWLBeta

theorem exists_beta : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ LL : FinExt l, ∃ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β := by
  intro l _ P AI T LL
  have hz := (GlobalTheory.TiedMu.tied_mu_units l P AI T).2.2.2
  let _ : Algebra ℤ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) :=
    ((algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B)).comp (algebraMap ℤ_[l] ℚ_[l])).toAlgebra
  let f : ↥(OL LL) →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeLeftRingHom).comp (OL LL).val.toRingHom
      commutes' := fun z => by
        show ((algebraMap ℤ_[l] ↥LL.1 z) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1] }
  let g : Ainf l →ₐ[ℤ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B :=
    { toRingHom := (Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)).toRingHom.comp AI.ιA
      commutes' := fun z => by
        show Algebra.TensorProduct.includeRight (R := ℚ_[l]) (A := ↥LL.1)
            (AI.ιA (algebraMap ℤ_[l] (Ainf l) z)) =
          algebraMap ℚ_[l] (↥LL.1 ⊗[ℚ_[l]] P.R.B) (algebraMap ℤ_[l] ℚ_[l] z)
        rw [hz, AlgHom.commutes]
        rfl }
  refine ⟨(Algebra.TensorProduct.productMap f g).toRingHom, fun o w => ?_⟩
  show Algebra.TensorProduct.productMap f g (o ⊗ₜ[ℤ_[l]] w) = _
  rw [Algebra.TensorProduct.productMap_apply_tmul]
  show ((o : ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : P.R.B)) * ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] AI.ιA w) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end GlobalTheory.HWLBeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteExtensionEntriesOfCompactRep
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.CompactRepField

theorem exists_finiteDimensional_entries_mem_of_continuous :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ ∀ g i j, ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ L := by
  intro l _ Γ _ _ _ _ a r hr
  let H : Subgroup (GL (Fin a) (PadicAlgCl l)) := r.range
  haveI : CompactSpace H := by
    have hc : IsCompact (H : Set (GL (Fin a) (PadicAlgCl l))) := by
      have : (H : Set (GL (Fin a) (PadicAlgCl l))) = Set.range r := by
        ext x; simp [H]
      rw [this]; exact isCompact_range hr
    exact isCompact_iff_compactSpace.1 hc
  obtain ⟨K, hK, hmem⟩ := exists_finiteDimensional_entries_mem l H a H.subtype
    fun i j => ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j)
  refine ⟨K, hK, fun g i j => ?_⟩
  exact hmem ⟨r g, ⟨g, rfl⟩⟩ i j

end GlobalTheory.CompactRepField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTorsionCocycleFiniteLevelLiftStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsionCocycle_finite_level_lift : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (ϖ : O), Irreducible ϖ → ∀ c ∈ divisibleCocycles LA', c ∉ BD LA' → ∀ r : ℕ, (∀ g, (algebraMap O LL ϖ) ^ r • liftD LA' (c g) ∈ LA'.T) → ∀ n : ℕ, r ≤ n → ∀ hI' : StableSub LA' (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA'.T), ∃ c' ∈ quotientCocycles LA' _ hI', c' ∉ BQ LA' _ hI' ∧ ∀ h, ∃ t ∈ LA'.T, Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h) = (algebraMap O LL ϖ) ^ n • liftD LA' (c h) + (algebraMap O LL ϖ) ^ n • t := by
  first | exact @GlobalTheory.TorsionLevel.exists_cocycle_level | exact GlobalTheory.TorsionLevel.exists_cocycle_level | (intros; apply GlobalTheory.TorsionLevel.exists_cocycle_level <;> assumption)
end

