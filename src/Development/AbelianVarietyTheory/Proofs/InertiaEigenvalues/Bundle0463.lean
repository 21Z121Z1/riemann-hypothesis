import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0061
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0441
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal.SepFil

variable {l : ℕ} [Fact l.Prime]

theorem ev_eq_zero_iff_pt {e : Per.Fl l} (he : GlobalTheory.MemLoc.IsEps e) (m : ℕ) (y : Per.BdRp l) :
    Per.ev l m y = 0 ↔ GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m ∣ y := by
  have hk := GlobalTheory.T.kerThetaLocalized_eq_span_fontaineXiElement l e he
  obtain ⟨-, hθ, hu, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have hfil := (GlobalTheory.MemLoc.filtration_eq_xi_pow l e he).1 1
  have hx : GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) = algebraMap (Per.AinfP l) (Per.BdRp l)
      (algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e)) := by
    rw [GlobalTheory.MemLoc.aDp, RingHom.comp_apply]
  have hmem : ∀ (n : ℕ) (a : Per.AinfP l), a ∈ Per.kerP l ^ n ↔
      algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n ∣ a := by
    intro n a
    rw [hk, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hback : ∀ (n : ℕ) (w : Per.BdRp l), GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ n ∣ w → Per.ev l n w = 0 := by
    rintro n w ⟨z, rfl⟩
    rw [map_mul, hx, ← map_pow (algebraMap (Per.AinfP l) (Per.BdRp l)), GlobalTheory.MemLoc.CrisUnique.ev_alg,
      Ideal.Quotient.eq_zero_iff_mem.2 ((hmem n _).2 dvd_rfl), zero_mul]
  have hnu : ¬ IsUnit (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e)) := by
    intro h
    have h1 := (hθ _).2 ((hfil (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e))).2 (by rw [pow_one]))
    exact (h.map (Per.θD l)).ne_zero h1
  have hone : ∀ w : Per.BdRp l, Per.ev l 1 w = 0 → GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ∣ w := by
    intro w hw
    by_cases h0 : Per.θD l w = 0
    · have h1 := (hfil w).1 ((hθ w).1 h0)
      rwa [pow_one] at h1
    · exfalso
      have h1 := (hu w h0).map (Per.ev l 1)
      rw [hw, isUnit_zero_iff, eq_comm, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 1)),
        Ideal.Quotient.eq_zero_iff_mem, hmem, pow_one] at h1
      apply hnu
      rw [hx]
      exact (isUnit_of_dvd_one h1).map _
  have hdense : ∀ (n : ℕ) (w : Per.BdRp l), ∃ (a : Per.AinfP l) (z : Per.BdRp l),
      w = algebraMap (Per.AinfP l) (Per.BdRp l) a + GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ n * z := by
    intro n w
    induction n with
    | zero => exact ⟨0, w, by rw [map_zero, pow_zero, one_mul, zero_add]⟩
    | succ n ih =>
      obtain ⟨a, z, hz⟩ := ih
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Per.ev l 1 z)
      obtain ⟨z', hz'⟩ := hone (z - algebraMap (Per.AinfP l) (Per.BdRp l) b) (by
        rw [map_sub, GlobalTheory.MemLoc.CrisUnique.ev_alg, hb, sub_self])
      refine ⟨a + algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n * b, z', ?_⟩
      rw [map_add, map_mul, map_pow, ← hx, pow_succ, mul_assoc, ← hz', hz]
      ring
  refine ⟨fun hy ↦ ?_, hback m y⟩
  obtain ⟨a, z, hz⟩ := hdense m y
  have h1 := hback m _ (dvd_mul_right (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m) z)
  rw [hz, map_add, h1, add_zero, GlobalTheory.MemLoc.CrisUnique.ev_alg, Ideal.Quotient.eq_zero_iff_mem, hmem] at hy
  rw [hz]
  refine dvd_add ?_ (dvd_mul_right _ _)
  rw [hx, ← map_pow]
  exact map_dvd _ hy

theorem dvd_of_forall_near {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) (m : ℕ)
    (c : Per.BdRp l)
    (h : ∀ r : ℕ, ∃ (a : Ainf l) (z : Per.BdRp l),
      c - (l : Per.BdRp l) ^ r * GlobalTheory.MemLoc.aDp l a = GlobalTheory.MemLoc.aDp l d ^ m * z) :
    GlobalTheory.MemLoc.aDp l d ^ m ∣ c := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.CrisUnique.exists_isEps l
  have hk := GlobalTheory.MemLoc.ker_theta_eq_span_xi he
  have hxd : GlobalTheory.MemLoc.xi e ∣ d := by
    rw [← Ideal.mem_span_singleton, ← hk, ← hd]
    exact Ideal.mem_span_singleton_self d
  have hdx : d ∣ GlobalTheory.MemLoc.xi e := by
    rw [← Ideal.mem_span_singleton, hd, hk]
    exact Ideal.mem_span_singleton_self _
  have hev : ∀ y : Per.BdRp l, Per.ev l m y = 0 ↔ GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi e) ^ m ∣ y :=
    ev_eq_zero_iff_pt he m
  have h0 : Per.ev l m c = 0 := by
    refine GlobalTheory.MemLoc.CrisUnique.sep m _ fun r ↦ ?_
    obtain ⟨a, z, hz⟩ := h r
    refine ⟨a, ?_⟩
    have h1 : Per.ev l m (GlobalTheory.MemLoc.aDp l d ^ m * z) = 0 :=
      (hev _).2 (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (map_dvd _ hxd) m) z)
    rw [← hz, map_sub, sub_eq_zero, map_mul, map_pow, map_natCast,
      GlobalTheory.MemLoc.CrisUnique.ev_aDp] at h1
    exact h1
  exact (pow_dvd_pow_of_dvd (map_dvd _ hdx) m).trans ((hev c).1 h0)

end GlobalTheory.BKReal.SepFil

namespace GlobalTheory.BKReal.SepFil

theorem dvd_of_forall_near_OD : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e) (m : ℕ) (w : OD l O),
    (∀ k : ℕ, ∃ y : OA l O, ϖ.iAl O K (EIn l e _) ^ m ∣ w - (l : OD l O) ^ k * toOD l O y) →
    ϖ.iAl O K (EIn l e _) ^ m ∣ w := by
  intro l _ e _ O K _ _ _ _ _ _ _ _ _ ϖ m w h
  have hE : ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) :=
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))
  set d := ϖ.ev 1 (eis l 1 e) with hd_def
  have hd : Ideal.span {d} = RingHom.ker (Per.θ l) := ϖ.span_ev_eis 1
  have hξ : ϖ.iAl O K (EIn l e _) ^ m = (1 : O) ⊗ₜ[ℤ_[l]] (GlobalTheory.MemLoc.aDp l d ^ m) := by
    rw [hE, Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  rw [hξ] at h ⊢
  let b := Module.Free.chooseBasis ℤ_[l] O
  have key : ∀ i, GlobalTheory.MemLoc.aDp l d ^ m ∣ GlobalTheory.Decompl.crd b i w := by
    intro i
    refine dvd_of_forall_near hd m _ fun r ↦ ?_
    obtain ⟨y, z, hz⟩ := h r
    refine ⟨GlobalTheory.Decompl.crd b i y, GlobalTheory.Decompl.crd b i z, ?_⟩
    have h1 := congrArg (GlobalTheory.Decompl.crd b i) hz
    have h2 : GlobalTheory.Decompl.crd b i (toOD l O y) = GlobalTheory.MemLoc.aDp l (GlobalTheory.Decompl.crd b i y) :=
      GlobalTheory.Decompl.crd_map b (ainfToBdRp l) i y
    rw [LinearMap.map_sub, ← Nat.cast_pow, GlobalTheory.Decompl.crd_natCast_mul, GlobalTheory.Decompl.crd_mul, h2,
      Nat.cast_pow] at h1
    exact h1
  choose c hc using key
  refine ⟨∑ j, b j ⊗ₜ[ℤ_[l]] c j, GlobalTheory.Decompl.ext_crd b fun i ↦ ?_⟩
  rw [GlobalTheory.Decompl.crd_mul, GlobalTheory.Decompl.crd_sum, ← hc i]

end GlobalTheory.BKReal.SepFil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonSubOneDvdAinfCoeffZeroOfThetaVanishing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.BKGal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.EpsCoeff

variable {l : ℕ} [hl : Fact l.Prime]

abbrev rt (ε : OCb l) (n : ℕ) : OCb l := ((frobeniusEquiv (OCb l) l).symm)^[n] ε

theorem rt_pow (ε : OCb l) (n k : ℕ) : rt ε (n + k) ^ (l ^ k) = rt ε n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih, ← Nat.add_assoc, pow_succ', pow_mul]
    congr 1
    rw [rt, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]

theorem frob_iter_teich (x : OCb l) (m : ℕ) :
    (⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[m] (WittVector.teichmuller l x) =
      WittVector.teichmuller l (x ^ (l ^ m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius,
      WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]

def xin (ε : OCb l) (n : ℕ) : Ainf l :=
  ∑ i ∈ Finset.range l, (WittVector.teichmuller l (rt ε (n + 1))) ^ i

theorem frob_iter_xin (ε : OCb l) (n k : ℕ) :
    (⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n + k] (xin ε n) =
      ∑ i ∈ Finset.range l, (WittVector.teichmuller l (rt ε 1 ^ (l ^ k))) ^ i := by
  rw [xin, ← RingHom.coe_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, RingHom.coe_pow, frob_iter_teich, pow_add, pow_mul, add_comm n 1, rt_pow]

theorem xi_eq (ε : OCb l) (n : ℕ) :
    GlobalTheory.MemLoc.xi ε = (⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n] (xin ε n) := by
  have h := frob_iter_xin ε n 0
  rw [Nat.add_zero] at h
  rw [h]
  simp [GlobalTheory.MemLoc.xi, rt]

theorem natCast_ne_zero : ((l : ℕ) : Per.OC l) ≠ 0 := by
  intro h
  apply GlobalTheory.RingBasics.p_ne_zero (p := l)
  have := congrArg Subtype.val h
  simpa using this

theorem theta_frob_xin (ε : OCb l) (hε : ε.untilt = 1) (n j : ℕ) :
    Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n + (j + 1)] (xin ε n)) = l := by
  rw [frob_iter_xin, map_sum]
  have h1 : (rt ε 1 ^ (l ^ (j + 1))).untilt = 1 := by
    rw [pow_succ', pow_mul]
    have : rt ε 1 ^ l = ε := by
      have h := rt_pow ε 0 1
      rw [zero_add, pow_one] at h
      exact h
    rw [this, map_pow, hε, one_pow]
  rw [Finset.sum_congr rfl (fun i _ => by rw [map_pow, WittVector.fontaineTheta_teichmuller, h1, one_pow])]
  simp

theorem xin_dvd (ε : OCb l) (hε : GlobalTheory.MemLoc.IsEps ε) (n : ℕ) (b : Ainf l)
    (hb : Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n] b) = 0) : xin ε n ∣ b := by
  obtain ⟨y, hy⟩ := (GlobalTheory.MemLoc.theta_eq_zero_iff_xi_dvd l ε hε _).1 hb
  have hbij := (WittVector.frobenius_bijective l (OCb l)).iterate n
  obtain ⟨y', rfl⟩ := hbij.2 y
  refine ⟨y', hbij.1 ?_⟩
  rw [hy, ← RingHom.coe_pow, map_mul, RingHom.coe_pow, xi_eq ε n]

theorem coeff_xin (ε : OCb l) (n : ℕ) :
    (xin ε n).coeff 0 * (rt ε (n + 1) - 1) = rt ε n - 1 := by
  rw [← WittVector.constantCoeff_apply, xin, map_sum]
  simp only [map_pow, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  rw [geom_sum_mul]
  have := rt_pow ε n 1
  rw [pow_one] at this
  rw [this]

theorem step (ε : OCb l) (hε : GlobalTheory.MemLoc.IsEps ε) (a : Ainf l)
    (ha : ∀ n : ℕ, Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[n] a) = 0) (n : ℕ) :
    ∃ b c : Ainf l, a = c * b ∧
      (∀ m, n ≤ m → Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[m] c) ≠ 0) ∧
      c.coeff 0 * (rt ε n - 1) = ε - 1 := by
  induction n with
  | zero =>
    refine ⟨a, 1, (one_mul a).symm, fun m _ => ?_, ?_⟩
    · rw [← RingHom.coe_pow, map_one, map_one]; exact one_ne_zero
    · simp [rt]
  | succ n ih =>
    obtain ⟨b, c, rfl, hc, h0⟩ := ih
    have hb : ∀ m, n ≤ m → Per.θ l ((⇑(WittVector.frobenius : Ainf l →+* Ainf l))^[m] b) = 0 :=
      fun m hm => by
        have := ha m
        rw [← RingHom.coe_pow, map_mul, map_mul, RingHom.coe_pow] at this
        exact (mul_eq_zero.1 this).resolve_left (hc m hm)
    obtain ⟨b', rfl⟩ := xin_dvd ε hε n b (hb n le_rfl)
    refine ⟨b', c * xin ε n, by ring, fun m hm => ?_, ?_⟩
    · rw [← RingHom.coe_pow, map_mul, map_mul, RingHom.coe_pow]
      refine mul_ne_zero (hc m (by omega)) ?_
      obtain ⟨j, rfl⟩ : ∃ j, m = n + (j + 1) := ⟨m - n - 1, by omega⟩
      rw [theta_frob_xin ε hε.1]
      exact natCast_ne_zero
    · rw [WittVector.mul_coeff_zero, mul_assoc, coeff_xin, h0]

theorem memLoc_isEps {ε : OCb l} (h : IsEps ε) : GlobalTheory.MemLoc.IsEps ε := by
  obtain ⟨h1, δ, hδ, hne⟩ := h
  have : (frobeniusEquiv (OCb l) l).symm ε = δ :=
    (RingEquiv.symm_apply_eq _).2 (by rw [frobeniusEquiv_def, hδ])
  exact ⟨h1, by rw [this]; exact hne⟩

theorem norm_untilt_mul (x y : OCb l) :
    ‖(((x * y).untilt : OC l) : ℂ_[l])‖ =
      ‖((x.untilt : OC l) : ℂ_[l])‖ * ‖((y.untilt : OC l) : ℂ_[l])‖ := by
  rw [map_mul, MulMemClass.coe_mul, norm_mul]

theorem norm_untilt_le_one (x : OCb l) : ‖((x.untilt : OC l) : ℂ_[l])‖ ≤ 1 :=
  (GlobalTheory.RingBasics.mem_OC _).1 x.untilt.2

theorem norm_rt_pow (x : OCb l) (n : ℕ) :
    ‖(((rt x n).untilt : OC l) : ℂ_[l])‖ ^ (l ^ n) = ‖((x.untilt : OC l) : ℂ_[l])‖ := by
  have h := rt_pow x 0 n
  rw [zero_add] at h
  rw [← norm_pow, ← SubmonoidClass.coe_pow, ← map_pow, h]
  rfl

theorem norm_le_of_dvd (a b : OCb l) (hb : b ≠ 0) (h : ∀ n, b ∣ a * rt b n) :
    ‖((a.untilt : OC l) : ℂ_[l])‖ ≤ ‖((b.untilt : OC l) : ℂ_[l])‖ := by
  set A := ‖((a.untilt : OC l) : ℂ_[l])‖ with hAdef
  set B := ‖((b.untilt : OC l) : ℂ_[l])‖ with hBdef
  have hB : 0 < B := by
    refine norm_pos_iff.2 fun h0 => GlobalTheory.FrobInt.sharpRoot_ne_zero b hb 0 ?_
    exact_mod_cast h0
  by_contra hlt
  push_neg at hlt
  have hA : 0 < A := hB.trans hlt
  have key : ∀ n : ℕ, A ^ (l ^ n) * B ≤ B ^ (l ^ n) := by
    intro n
    obtain ⟨c, hc⟩ := h n
    have h1 := congrArg (fun x : OCb l => ‖((x.untilt : OC l) : ℂ_[l])‖ ^ (l ^ n)) hc
    simp only [norm_untilt_mul, mul_pow, norm_rt_pow] at h1
    have hc1 : ‖((c.untilt : OC l) : ℂ_[l])‖ ^ (l ^ n) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (norm_untilt_le_one c)
    calc A ^ (l ^ n) * B = B ^ (l ^ n) * ‖((c.untilt : OC l) : ℂ_[l])‖ ^ (l ^ n) := h1
      _ ≤ B ^ (l ^ n) := mul_le_of_le_one_right (by positivity) hc1
  have hr : B / A < 1 := (div_lt_one hA).2 hlt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hB hr
  have h2 : (B / A) ^ (l ^ n) ≤ (B / A) ^ n :=
    pow_le_pow_of_le_one (by positivity) hr.le (Nat.lt_pow_self hl.out.one_lt).le
  have h3 : B ≤ (B / A) ^ (l ^ n) := by
    rw [div_pow, le_div_iff₀ (by positivity), mul_comm]
    exact key n
  linarith

theorem dvd_of_norm_le (x y : OC l) (hx : x ≠ 0) (h : ‖(y : ℂ_[l])‖ ≤ ‖(x : ℂ_[l])‖) : x ∣ y := by
  have hx' : (x : ℂ_[l]) ≠ 0 := fun h0 => hx (by exact_mod_cast h0)
  refine ⟨⟨(y : ℂ_[l]) / x, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, div_le_one (norm_pos_iff.2 hx')]
    exact h
  · show (y : ℂ_[l]) = (x : ℂ_[l]) * ((y : ℂ_[l]) / x)
    field_simp

theorem dvd_of_forall_dvd_mul_rt (a b : OCb l) (hb : b ≠ 0) (h : ∀ n, b ∣ a * rt b n) : b ∣ a := by
  refine GlobalTheory.FrobInt.dvd_of_sharpRoot_dvd b a (GlobalTheory.FrobInt.sharpRoot_ne_zero b hb) fun k => ?_
  refine dvd_of_norm_le _ _ (GlobalTheory.FrobInt.sharpRoot_ne_zero b hb k) ?_
  have hbk : rt b k ≠ 0 := by
    intro h0
    apply hb
    apply (frobeniusEquiv (OCb l) l).symm.injective.iterate k
    rw [iterate_map_zero]
    exact h0
  refine norm_le_of_dvd (rt a k) (rt b k) hbk fun n => ?_
  obtain ⟨c, hc⟩ := h n
  refine ⟨rt c k, ?_⟩
  have := congrArg (((frobeniusEquiv (OCb l) l).symm)^[k]) hc
  rw [iterate_map_mul, iterate_map_mul] at this
  have hcomm : rt (rt b k) n = rt (rt b n) k := by
    simp only [rt, ← Function.iterate_add_apply, add_comm]
  rw [hcomm]
  exact this

end GlobalTheory.EpsCoeff

namespace GlobalTheory

open GlobalTheory.EpsCoeff in

theorem eps_sub_one_dvd_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (ε : OCb l), IsEps ε → ∀ a : Ainf l,
    (∀ n : ℕ, Per.θ l (WittVector.frobenius^[n] a) = 0) → (ε - 1) ∣ a.coeff 0 := by
  intro l _ ε hε a ha
  have hε' := memLoc_isEps hε
  have hne : ε - 1 ≠ 0 := by
    intro h0
    rw [sub_eq_zero] at h0
    apply hε'.2
    rw [h0, map_one, map_one]
  refine dvd_of_forall_dvd_mul_rt _ _ hne fun n => ?_
  obtain ⟨b, c, rfl, -, h0⟩ := step ε hε' a ha n
  refine ⟨b.coeff 0, ?_⟩
  have hr : rt (ε - 1) n = rt ε n - 1 := by simp only [rt, iterate_map_sub, iterate_map_one]
  rw [hr, WittVector.mul_coeff_zero, ← h0]
  ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfFrobeniusPeriodicMemDeRhamFilZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem fil_add_nat_le {l : ℕ} [Fact l.Prime] (P : LocPrime l) (a : ℤ) (k : ℕ) {x : P.R.BdR}
    (hx : x ∈ (P.PD (botExt l)).Fil (a + k)) : x ∈ (P.PD (botExt l)).Fil a := by
  induction k generalizing a with
  | zero => simpa using hx
  | succ k ih =>
    apply ih
    have h := (P.PD (botExt l)).Fil_anti (a + k)
    apply h
    have : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rwa [← this]

theorem no_fil_zero_neg_slope : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (h d : ℕ), 0 < h → 0 < d → ∀ c : P.R.B, (l : P.R.B) ^ d * P.φB^[h] c = c →
    (∀ j < h, ev P j c ∈ Fil P 0) → c = 0 := by
  intro l _ P AI T h d hh hd c hc hfil
  have hF : IsField P.R.BdR := GlobalTheory.RegularRing.isField_of_tied T
  have hι : Function.Injective P.ιB := fun a b hab => (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι, hab])
  set PD := P.PD (botExt l) with hPD
  have hdom : ∀ a b : P.R.B, a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b hab
    have h0 : P.ιB a * P.ιB b = 0 := by rw [← map_mul, hab, map_zero]
    by_cases ha : P.ιB a = 0
    · exact Or.inl (hι (by rw [ha, map_zero]))
    · right
      obtain ⟨y, hy⟩ := hF.mul_inv_cancel ha
      apply hι
      rw [map_zero]
      calc P.ιB b = (y * P.ιB a) * P.ιB b := by rw [mul_comm y, hy, one_mul]
        _ = 0 := by rw [mul_assoc, h0, mul_zero]
  haveI : NoZeroDivisors P.R.B := ⟨fun {a b} hab => hdom a b hab⟩
  haveI : Nontrivial P.R.B := nontrivial_B P
  by_contra hc0
  set N : P.R.B := ∏ j ∈ Finset.range h, P.φB^[j] c with hN
  have hφN : c * P.φB N = N * P.φB^[h] c := by
    have e1 : P.φB N = ∏ j ∈ Finset.range h, P.φB^[j + 1] c := by
      rw [hN, map_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Function.iterate_succ_apply']
    rw [e1, hN]
    have e2 := Finset.prod_range_succ' (fun j => P.φB^[j] c) h
    have e3 := Finset.prod_range_succ (fun j => P.φB^[j] c) h
    simp only [Function.iterate_zero, id] at e2
    rw [mul_comm c, ← e2, e3]
  have hlN : (l : P.R.B) ^ d * P.φB N = N := by
    have : c * ((l : P.R.B) ^ d * P.φB N - N) = 0 := by
      calc c * ((l : P.R.B) ^ d * P.φB N - N) = (l : P.R.B) ^ d * (c * P.φB N) - N * c := by ring
        _ = N * ((l : P.R.B) ^ d * P.φB^[h] c) - N * c := by rw [hφN]; ring
        _ = 0 := by rw [hc, sub_self]
    rcases hdom _ _ this with h1 | h1
    · exact absurd h1 hc0
    · exact sub_eq_zero.mp h1
  set x : P.R.B := N * P.tB ^ d with hx
  have hφx : PD.φ x = x := by
    rw [P.PD_φ, hx, map_mul, map_pow, localPrime_frobenius_periodT, Algebra.smul_def, map_natCast, mul_pow]
    linear_combination (P.tB ^ d) * hlN
  have hmul : ∀ (a b : ℤ) (u v : P.R.BdR), u ∈ PD.Fil a → v ∈ PD.Fil b → u * v ∈ PD.Fil (a + b) :=
    fun a b u v hu hv => PD.Fil_mul a b u v hu hv
  have hιN : P.ιB N ∈ PD.Fil 0 := by
    rw [hN, map_prod]
    refine Finset.prod_induction _ (fun u => u ∈ PD.Fil 0) (fun u v hu hv => by simpa using hmul 0 0 u v hu hv)
      (by simpa using PD.one_mem) fun j hj => ?_
    exact hfil j (Finset.mem_range.mp hj)
  have hιt : P.ιB P.tB ∈ PD.Fil 1 := by
    have := PD.mem_filtration_one
    rwa [P.PD_ι, P.period_datum_t_eq] at this
  have hιtd : ∀ k : ℕ, P.ιB (P.tB ^ k) ∈ PD.Fil k := by
    intro k
    induction k with
    | zero => simpa using PD.one_mem
    | succ k ih =>
      rw [pow_succ, map_mul]
      have := hmul k 1 _ _ ih hιt
      simpa using this
  have hιx1 : P.ιB x ∈ PD.Fil 1 := by
    have h1 : P.ιB x ∈ PD.Fil (0 + d) := by rw [hx, map_mul]; exact hmul 0 d _ _ hιN (hιtd d)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d = k + 1 := ⟨d - 1, by omega⟩
    apply fil_add_nat_le P 1 k
    have : (1 : ℤ) + (k : ℤ) = 0 + (d : ℤ) := by rw [hk]; push_cast; ring
    rwa [this]
  have hιx0 : P.ιB x ∈ PD.Fil 0 := fil_add_nat_le P 0 1 (by simpa using hιx1)
  obtain ⟨q, hq⟩ := PD.fund x hφx (by rw [P.PD_ι]; exact hιx0)
  by_cases hq0 : q = 0
  · have hx0 : x = 0 := by rw [← hq, hq0, map_zero]
    have hN0 : N = 0 := by
      rcases hdom _ _ hx0 with h1 | h1
      · exact h1
      · exact absurd (pow_eq_zero_iff (by omega) |>.mp h1) (isUnit_tB P).ne_zero
    rw [hN, Finset.prod_eq_zero_iff] at hN0
    obtain ⟨j, -, hj⟩ := hN0
    apply hc0
    apply (phiB_injective P).iterate j
    rw [hj, iterate_map_zero]
  · have hqx : P.ιB x = algebraMap ℚ_[l] P.R.BdR q := by rw [← hq, AlgHom.commutes]
    have hinv : algebraMap ℚ_[l] P.R.BdR q⁻¹ ∈ PD.Fil 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_of_tower_mem _ _ PD.one_mem
    have hone : algebraMap ℚ_[l] P.R.BdR q⁻¹ * P.ιB x = 1 := by
      rw [hqx, ← map_mul, inv_mul_cancel₀ hq0, map_one]
    have h2 : P.ιB P.tB ∈ PD.Fil 2 := by
      have := hmul 1 (0 + 1) _ _ hιt (hmul 0 1 _ _ hinv hιx1)
      rw [hone, mul_one] at this
      simpa using this
    have := PD.not_mem_filtration_two
    rw [P.PD_ι, P.period_datum_t_eq] at this
    exact this h2

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLattices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.LatExact

theorem W_exact : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) (O := ↥(OL LL)) ι π → Function.Injective (W.map ι) ∧ Function.Surjective (W.map π) ∧ ∀ x, W.map π x = 0 ↔ ∃ y, W.map ι y = x := by
  intro D HW F l _ K s LL h W T₀ T₁ T₂ ι π hses
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h T₀ T₁ T₂ ι π hses
  exact ⟨h1, h3, fun x => h2 x⟩

end GlobalTheory.LatExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisin_module_basis_of_fCrystal : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (T : Lat a O K ϖ), (letI := zlLat T; ∃ E : FCrys l ↥(OL (ϖ.field a)), IsRealisation (ϖ.field a) E ↥T.L.T (actZ T)) → Nonempty (BKMod t ϖ T) := by
  first | exact @GlobalTheory.BKReal.OfCrystal.main | exact GlobalTheory.BKReal.OfCrystal.main | (intros; apply GlobalTheory.BKReal.OfCrystal.main <;> assumption)
end

