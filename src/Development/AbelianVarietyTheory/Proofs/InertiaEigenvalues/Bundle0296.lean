import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstantCoeffTeichSub
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc.IoMap

section General

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

theorem X_pow_dvd_sub_trunc (a : R⟦X⟧) (n : ℕ) :
    (X : R⟦X⟧) ^ n ∣ a - (trunc n a : Polynomial R) := by
  rw [X_pow_dvd_iff]
  intro m hm
  simp [coeff_trunc, hm]

theorem algHom_coe (f : R⟦X⟧ →ₐ[R] A) (p : Polynomial R) :
    f (p : R⟦X⟧) = Polynomial.aeval (f X) p := by
  have : f.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (f X) := by
    ext
    simp
  simpa using DFunLike.congr_fun this p

theorem algHom_unique (f g : R⟦X⟧ →ₐ[R] A) (h : f X = g X)
    (hs : ∀ x : A, (∀ n, f X ^ n ∣ x) → x = 0) : f = g := by
  ext a
  rw [← sub_eq_zero]
  refine hs _ fun n => ?_
  obtain ⟨b, hb⟩ := X_pow_dvd_sub_trunc a n
  have h1 := congrArg f hb
  have h2 := congrArg g hb
  rw [map_sub, map_mul, map_pow, algHom_coe] at h1 h2
  rw [← h] at h2
  exact ⟨f b - g b, by linear_combination h1 - h2⟩

theorem algHom_exists (y : A) (hc : GlobalTheory.Per.AinfComplete.Summ y)
    (hs : ∀ x : A, (∀ n, y ^ n ∣ x) → x = 0) : ∃ f : R⟦X⟧ →ₐ[R] A, f X = y := by
  have h1 : ∀ a : R⟦X⟧, ∃ L : A, ∀ n, y ^ n ∣ L - Polynomial.aeval y (trunc n a) := by
    intro a
    obtain ⟨L, hL⟩ := hc fun i => algebraMap R A (coeff i a)
    refine ⟨L, fun n => ?_⟩
    have e : Polynomial.aeval y (trunc n a) =
        ∑ i ∈ Finset.range n, y ^ i * algebraMap R A (coeff i a) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [trunc_succ, map_add, ih, Finset.sum_range_succ, Polynomial.aeval_monomial, mul_comm]
    rw [e]
    exact Ideal.mem_span_singleton.1 (hL n)
  choose L hL using h1
  have h2 : ∀ (a : R⟦X⟧) (p : Polynomial R) (n : ℕ), (X : R⟦X⟧) ^ n ∣ a - p →
      y ^ n ∣ L a - Polynomial.aeval y p := by
    intro a p n h
    have h3 : (Polynomial.X : Polynomial R) ^ n ∣ trunc n a - p := by
      rw [Polynomial.X_pow_dvd_iff]
      intro d hd
      have := X_pow_dvd_iff.1 h d hd
      simpa [coeff_trunc, hd] using this
    have h4 := map_dvd (Polynomial.aeval y) h3
    rw [map_pow, Polynomial.aeval_X, map_sub] at h4
    convert dvd_add (hL a n) h4 using 1
    ring
  have h3 : ∀ p : Polynomial R, L p = Polynomial.aeval y p := fun p => by
    rw [← sub_eq_zero]
    exact hs _ fun n => h2 _ _ _ (by simp)
  have hadd : ∀ a b, L (a + b) = L a + L b := fun a b => by
    rw [← sub_eq_zero]
    refine hs _ fun n => ?_
    have := hL (a + b) n
    rw [map_add, map_add] at this
    convert dvd_sub (dvd_sub this (hL a n)) (hL b n) using 1
    ring
  have hmul : ∀ a b, L (a * b) = L a * L b := fun a b => by
    rw [← sub_eq_zero]
    refine hs _ fun n => ?_
    have := h2 (a * b) (trunc n a * trunc n b) n (by
      rw [Polynomial.coe_mul]
      convert dvd_add ((X_pow_dvd_sub_trunc a n).mul_right b)
        ((X_pow_dvd_sub_trunc b n).mul_left (trunc n a : Polynomial R)) using 1
      ring)
    rw [map_mul] at this
    convert dvd_sub (dvd_sub this ((hL a n).mul_right (L b)))
      ((hL b n).mul_left (Polynomial.aeval y (trunc n a))) using 1
    ring
  refine ⟨{ toFun := L
            map_one' := by simpa using h3 1
            map_mul' := hmul
            map_zero' := by simpa using h3 0
            map_add' := hadd
            commutes' := fun r => by simpa using h3 (Polynomial.C r) }, ?_⟩
  simpa using h3 Polynomial.X

end General

variable (l : ℕ) [Fact l.Prime]

theorem ne_zero_of_coeff {B : Type*} [CommRing B] [IsDomain B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B)
    (hX : ψ X ≠ 0) (m : ℕ) : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ coeff m a → ψ a ≠ 0 := by
  have h0 : ∀ a : ℤ_[l]⟦X⟧, ¬ ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a → ψ a ≠ 0 := by
    intro a ha
    have : IsUnit (constantCoeff a) := by
      by_contra hn
      exact ha ((PadicInt.norm_lt_one_iff_dvd _).1 (PadicInt.not_isUnit_iff.1 hn))
    exact ((isUnit_iff_constantCoeff.2 this).map ψ).ne_zero
  induction m with
  | zero => intro a ha; exact h0 a (by simpa using ha)
  | succ m ih =>
    intro a ha
    by_cases h : ((l : ℕ) : ℤ_[l]) ∣ constantCoeff a
    · obtain ⟨c, hc⟩ := h
      rw [eq_X_mul_shift_add_const a, hc, map_add, map_mul, map_mul, map_mul, map_natCast,
        map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]
      exact mul_ne_zero hX (ih _ (by simpa using ha))
    · exact h0 a h

theorem ne_zero_of_not_dvd {B : Type*} [CommRing B] [IsDomain B] [CharP B l] (ψ : ℤ_[l]⟦X⟧ →+* B)
    (hX : ψ X ≠ 0) (a : ℤ_[l]⟦X⟧) (ha : ¬ ((l : ℕ) : ℤ_[l]⟦X⟧) ∣ a) : ψ a ≠ 0 := by
  by_contra h
  apply ha
  have : ∀ m, ((l : ℕ) : ℤ_[l]) ∣ coeff m a := fun m => by
    by_contra hm
    exact ne_zero_of_coeff l ψ hX m a hm h
  choose c hc using this
  refine ⟨PowerSeries.mk c, ?_⟩
  ext m
  rw [← map_natCast (C : ℤ_[l] →+* ℤ_[l]⟦X⟧), coeff_C_mul, coeff_mk, hc]

theorem phi_X : phi l ℤ_[l] X = (1 + X) ^ l - 1 := by
  rw [phi, act, substAlgHom_X, cyc, binomialSeries_nat]
  simp

theorem constantCoeff_teich_sub (e : OCb l) :
    WittVector.constantCoeff (WittVector.teichmuller l e - 1 : Ainf l) = e - 1 := by
  rw [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem complete_teich (e : OCb l) (he : ¬ IsUnit (e - 1)) :
    GlobalTheory.Per.AinfComplete.Summ (WittVector.teichmuller l e - 1 : Ainf l) ∧
      ∀ x : Ainf l, (∀ n, (WittVector.teichmuller l e - 1 : Ainf l) ^ n ∣ x) → x = 0 := by
  have hy : ¬ IsUnit (WittVector.teichmuller l e - 1 : Ainf l) := fun h =>
    he (constantCoeff_teich_sub l e ▸ h.map WittVector.constantCoeff)
  have := (GlobalTheory.Per.AinfComplete.main l _ hy).2
  exact ⟨GlobalTheory.Per.AinfComplete.summ_of_precomplete _, fun x hx =>
    GlobalTheory.Per.AinfComplete.eq_zero_of_haus _ x fun n => Ideal.mem_span_singleton.2 (hx n)⟩

noncomputable def frobA : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

theorem frobA_apply (x : Ainf l) : frobA l x = WittVector.frobenius x := by
  rw [WittVector.frobenius_eq_map_frobenius]
  rfl

theorem main : ∀ (l : ℕ) [Fact l.Prime], ∀ e : OCb l, ¬ IsUnit (e - 1) →
    (∃! io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l, IsIo e io) ∧
    ∀ io : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] Ainf l, IsIo e io →
      (∀ a, io (phi l ℤ_[l] a) = WittVector.frobenius (io a)) ∧
      (e ≠ 1 → ∀ a, ¬ ((l : ℕ) : PowerSeries ℤ_[l]) ∣ a → IsUnit (inclW l (io a))) := by
  intro l hl e he
  obtain ⟨hc, hs⟩ := complete_teich l e he
  refine ⟨?_, fun io hio => ⟨?_, fun he1 a ha => ?_⟩⟩
  · obtain ⟨f, hf⟩ := algHom_exists (R := ℤ_[l]) _ hc hs
    refine ⟨f, hf, fun g hg => algHom_unique g f (Eq.trans hg hf.symm) ?_⟩
    rw [show g X = _ from hg]
    exact hs
  · have he' : ¬ IsUnit (e ^ l - 1) := fun h => he (by
      rw [← geom_sum_mul] at h
      exact isUnit_of_mul_isUnit_right h)
    have hio' : io X = WittVector.teichmuller l e - 1 := hio
    have e1 : (io.comp (phi l ℤ_[l])) X = WittVector.teichmuller l (e ^ l) - 1 := by
      rw [AlgHom.comp_apply, phi_X, map_sub, map_pow, map_add, map_one, hio', map_pow]
      ring
    have e2 : ((frobA l).comp io) X = WittVector.teichmuller l (e ^ l) - 1 := by
      rw [AlgHom.comp_apply, hio', map_sub, map_one]
      congr 1
      exact WittVector.map_teichmuller l (frobenius (OCb l) l) e
    have := algHom_unique _ _ (e1.trans e2.symm) (by rw [e1]; exact (complete_teich l _ he').2)
    intro a
    rw [← frobA_apply]
    exact DFunLike.congr_fun this a
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [inclW, WittVector.map_coeff]
    have hio' : io X = WittVector.teichmuller l e - 1 := hio
    have := ne_zero_of_not_dvd l
      ((WittVector.constantCoeff : Ainf l →+* OCb l).comp io.toRingHom) (by
        change WittVector.constantCoeff (io X) ≠ 0
        rw [hio', constantCoeff_teich_sub]
        exact sub_ne_zero.2 he1) a ha
    intro hz
    exact this ((IsFractionRing.injective (OCb l) (Cb l)) (hz.trans (map_zero _).symm))

end GlobalTheory.Cyc.IoMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterOfBcrisUnitFilOne
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LtCharCont

open GlobalTheory.ExpImage Filter Topology Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem oB_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (w : Om l) :
    oB P w ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om w
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem norm_th_le_of_mem_Lat {P : LocPrime l} {AI : LocAinf l P} (Θ : ThetaL P AI) {n : ℕ}
    {y : P.R.BdR} (hy : y ∈ Lat AI 1 n) : ‖Θ.θ y‖ ≤ ‖(l : ℚ_[l])‖ ^ n := by
  obtain ⟨a, ha⟩ := hy
  have hy0 : y ∈ FilB P 0 := Lat_mem_zero AI ⟨a, ha⟩
  have hi0 : io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P 0 := io_mem AI _
  have hd0 : y - io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P 0 := sub_mem hy0 hi0
  have h1 : Θ.θ (y - io AI (((l : ℕ) : Ainf l) ^ n * a)) = 0 :=
    (Θ.θ_ker _ hd0).2 (by simpa using ha)
  have h2 : Θ.θ y = Θ.θ (io AI (((l : ℕ) : Ainf l) ^ n * a)) := by
    have := Θ.θ_add _ hd0 _ hi0
    rw [sub_add_cancel, h1, zero_add] at this
    exact this
  have e : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    rw [map_mul, map_pow, map_natCast, map_pow, map_natCast]
  rw [h2, e, Θ.θ_mul _ (qB_mem _) _ (io_mem AI a), norm_mul]
  have e2 : qB P ((l : ℚ_[l]) ^ n) = oB P (algebraMap ℚ_[l] (Om l) ((l : ℚ_[l]) ^ n)) :=
    IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR _
  rw [e2, Θ.θ_Om, PadicComplex.norm_extends]
  have e3 : ‖algebraMap ℚ_[l] (Om l) ((l : ℚ_[l]) ^ n)‖ = ‖(l : ℚ_[l])‖ ^ n := by
    rw [← norm_pow]; exact PadicAlgCl.norm_extends (p := l) _
  rw [e3]
  have := Θ.θ_int a
  rw [← io_apply AI a] at this
  calc _ ≤ ‖(l : ℚ_[l])‖ ^ n * 1 := by gcongr
    _ = _ := mul_one _

theorem continuous_char_of_act : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → P.ιB x ∈ (P.PD K).Fil 1 →
    P.ιB x ∉ (P.PD K).Fil 2 → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ,
    (∀ g : ↥(GK K), P.actQ (g : GQ l) x =
      algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) →
    Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) := by
  intro l _ P AI T K x _hxu hx1 hx2 c hc
  let Θ := GlobalTheory.ThetaTie.thetaL T
  have hF : ∀ (a : ℤ) (y : P.R.BdR), y ∈ (P.PD K).Fil a ↔ y ∈ FilB P a := fun a y =>
    Set.ext_iff.1 (P.PD_Fil K (botExt l) a) y
  have hX1 : P.ιB x ∈ FilB P 1 := (hF 1 _).1 hx1
  have hX2 : P.ιB x ∉ FilB P 2 := fun h => hx2 ((hF 2 _).2 h)
  obtain ⟨s, hs, hts⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T
  have hb0 : s * P.ιB x ∈ FilB P 0 := by
    have := FilB_mul hs hX1
    simpa using this
  have hθb : Θ.θ (s * P.ιB x) ≠ 0 := by
    intro h0
    have h1 : s * P.ιB x ∈ FilB P 1 := (Θ.θ_ker _ hb0).1 h0
    apply hX2
    have := FilB_mul (tD_mem (P := P)) h1
    have e : tD P * (s * P.ιB x) = P.ιB x := by
      rw [← mul_assoc]
      change P.ιB P.tB * s * P.ιB x = P.ιB x
      rw [hts, one_mul]
    rw [e] at this
    simpa using this
  let cv : ↥(GK K) → Om l := fun g => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)
  let χv : ↥(GK K) → Om l := fun g => algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])
  let uv : ↥(GK K) → Om l := fun g => cv g * (χv g)⁻¹
  have hK0 : ∀ z : ↥(K0 K), P.ιB (algebraMap ↥(K0 K) P.R.B z) = oB P (z : Om l) := fun z =>
    GlobalTheory.LocIota.ιB_algebraMap_Kur P (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) z)
  have hqo : ∀ z : ℚ_[l], qB P z = oB P (algebraMap ℚ_[l] (Om l) z) := fun z =>
    IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z
  have hact : ∀ g : ↥(GK K), P.actQdR (g : GQ l) (s * P.ιB x) = oB P (uv g) * (s * P.ιB x) := by
    intro g
    have hX : P.actQdR (g : GQ l) (P.ιB x) = oB P (cv g) * P.ιB x := by
      rw [← ιB_act, hc g, map_mul, hK0]
    have ht := act_tD (P := P) (g : GQ l)
    have h1 : P.actQdR (g : GQ l) (tD P) * P.actQdR (g : GQ l) s = 1 := by
      rw [← map_mul]
      change P.actQdR (g : GQ l) (P.ιB P.tB * s) = 1
      rw [hts, map_one]
    have h2 : qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * qB P (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (Units.ne_zero _), map_one]
    have hts' : tD P * s = 1 := hts
    rw [ht] at h1
    have hs' : P.actQdR (g : GQ l) s = qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * s := by
      linear_combination (qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * s) * h1
        - P.actQdR (g : GQ l) s * h2
        - (P.actQdR (g : GQ l) s * qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹
            * qB P (P.χQ (g : GQ l) : ℚ_[l])) * hts'
    have hu : oB P (uv g) = oB P (cv g) * qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ := by
      rw [hqo, map_inv₀]
      change oB P (cv g * (χv g)⁻¹) = _
      rw [map_mul]
    rw [map_mul, hs', hX, hu]
    ring
  have hl : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hθpos : 0 < ‖Θ.θ (s * P.ιB x)‖ := norm_pos_iff.2 hθb
  have htv : Tendsto (fun g : ↥(GK K) => (g : GQ l)) (𝓝 1) (𝓝 1) := by
    simpa using continuous_subtype_val.tendsto (1 : ↥(GK K))
  have huv : Tendsto uv (𝓝 1) (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hθpos) hl
    have hev := (bounded_and_eventually_sub_mem_Lat l P AI T _ hb0 1 n).2
    filter_upwards [htv.eventually hev] with g hg
    rw [hact g] at hg
    have e : oB P (uv g) * (s * P.ιB x) - s * P.ιB x = oB P (uv g - 1) * (s * P.ιB x) := by
      rw [map_sub, map_one]; ring
    rw [e] at hg
    have h3 := norm_th_le_of_mem_Lat Θ hg
    rw [Θ.θ_mul _ (oB_mem T _) _ hb0, Θ.θ_Om, norm_mul, PadicComplex.norm_extends] at h3
    rw [dist_eq_norm]
    have h4 : ‖uv g - 1‖ * ‖Θ.θ (s * P.ιB x)‖ < ε * ‖Θ.θ (s * P.ιB x)‖ := h3.trans_lt hn
    exact lt_of_mul_lt_mul_right h4 hθpos.le
  have hqc : Continuous (algebraMap ℚ_[l] (Om l)) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] (Om l))
      (fun z => PadicAlgCl.norm_extends (p := l) z)).continuous
  have hχ : Tendsto χv (𝓝 1) (𝓝 1) := by
    have hcont : Continuous χv :=
      hqc.comp ((GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val)
    simpa [χv] using hcont.tendsto 1
  have hcv1 : Tendsto cv (𝓝 1) (𝓝 1) := by
    have := huv.mul hχ
    rw [mul_one] at this
    refine this.congr fun g => ?_
    have hne : χv g ≠ 0 := by
      simp only [χv, ne_eq, map_eq_zero]
      exact Units.ne_zero _
    exact inv_mul_cancel_right₀ hne (cv g)
  have hmul : ∀ g h : ↥(GK K), cv (g * h) = cv g * cv h := by
    intro g h
    simp [cv, map_mul]
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have t1 : Tendsto (fun g : ↥(GK K) => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    simpa using (continuous_mul_left g₀⁻¹).tendsto g₀
  have t2 := (hcv1.comp t1).const_mul (cv g₀)
  rw [mul_one] at t2
  refine t2.congr fun g => ?_
  change cv g₀ * cv (g₀⁻¹ * g) = cv g
  rw [← hmul, mul_inv_cancel_left]

end GlobalTheory.LtCharCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisOrbitWittTensorLatticeWeakTopolo
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section
open Filter Topology

namespace GlobalTheory.WeakClosed

theorem continuous_orbit_twTop : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T), letI := twTop T b; Continuous fun g : ↥(GK K) => TWact (AI.gRW LL (g : GQ l)) T g y := by
  intro l _ P AI K LL T d b y

  letI := zlMod T
  haveI := zlTower T
  letI tC : TopologicalSpace (Cb l) := cbTop l
  letI tW : TopologicalSpace (WCb l) := wTop l
  haveI hWr : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  have hW : Continuous (algebraMap ℤ_[l] (WCb l)) :=
    GlobalTheory.WeakTop.continuous_padicInt_witt (zlW l (Cb l))
  have ha : Continuous fun q : GQ l × WCb l => (AI.actWCbHom q.1).toAlgHom q.2 :=
    GlobalTheory.WeakTop.continuous_map_witt (fun g : GQ l => (autCb l (AI.actT g)).toRingHom)
      (continuous_autCb_cbTop AI)
  haveI := LL.2
  have hc : ∀ c : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := fun c =>
    (IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1 c).symm.trans
      (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 c)
  have hemb : Topology.IsInducing (algebraMap ℤ_[l] ℚ_[l]) := Topology.IsInducing.subtypeVal
  have hρ : ∀ i j, Continuous fun g : ↥(GK K) => b.repr (T.actT g (b j)) i := fun i j =>
    hemb.continuous_iff.2 (GlobalTheory.Cyc.continuous_coord_lat hc T b (b j) i)
  have h2 : ∀ w : WCb l, Continuous fun g : ↥(GK K) => (AI.actWCbHom (g : GQ l)).toAlgHom w := fun w =>
    Continuous.comp (g := fun q : GQ l × WCb l => (AI.actWCbHom q.1).toAlgHom q.2)
      (f := fun g : ↥(GK K) => ((g : GQ l), w)) ha (continuous_subtype_val.prodMk continuous_const)
  have hs : ∀ i, Continuous fun g : ↥(GK K) => ∑ j, algebraMap ℤ_[l] (WCb l) (b.repr (T.actT g (b j)) i) *
      (AI.actWCbHom (g : GQ l)).toAlgHom (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b y j) := fun i =>
    continuous_finset_sum _ fun j _ => (hW.comp (hρ i j)).mul (h2 _)
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  refine (hs i).congr fun g => ?_
  exact (GlobalTheory.WeakTop.coords_map b _ _ y i).symm

end GlobalTheory.WeakClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousZlSmulStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_padicInt_smul_latB : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (m : TW (RW LL) T), letI := twTop T b; Continuous fun c : ℤ_[l] => algebraMap ℤ_[l] ↥(OL LL) c • m := by
  first | exact @GlobalTheory.WeakClosed.continuous_zl_smul | exact GlobalTheory.WeakClosed.continuous_zl_smul | (intros; apply GlobalTheory.WeakClosed.continuous_zl_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycEqImageStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_cyclotomicCharacter_of_isCyc : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G], PadicCoeff p O → ∀ (φ : ℤ_[p] →+* O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ g : G, ((ε g : Oˣ) : O) = φ ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) := by
  first | exact @GlobalTheory.CycImage.cyc_eq_image | exact GlobalTheory.CycImage.cyc_eq_image | (intros; apply GlobalTheory.CycImage.cyc_eq_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicAdmissibleSemistable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Inhab

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

include P in
theorem fixed_frob (c : ↥(MaximalUnramifiedExtension l)) (hc : frobUr l c = c) : ∃ q : ℚ_[l], algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q = c := by
  let K := adjExt (c : Om l)
  let x : ↥(K0 K) := ⟨c, mem_adjExt _, c.2⟩
  have h1 : (P.PD K).φ (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c := by
    rw [P.PD_φ, phiB_algebraMap, hc]
  have h2 : (P.PD K).ι (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) ∈ (P.PD K).Fil 0 := by
    have e : (P.PD K).ι (algebraMap ↥(K0 K) P.R.B x) = algebraMap ↥(K0 K) P.R.BdR x := (P.PD K).ι.commutes x
    have e2 : algebraMap ↥(K0 K) P.R.BdR x = (algebraMap ↥(K0 K) ↥K.1 x) • (1 : P.R.BdR) := by
      rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR, Algebra.algebraMap_eq_smul_one]
    have e3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c = algebraMap ↥(K0 K) P.R.B x := rfl
    rw [e3, e, e2]
    exact Submodule.smul_mem _ _ (P.PD K).one_mem
  obtain ⟨q, hq⟩ := (P.PD K).fund _ h1 h2
  haveI := nontrivial_B P
  refine ⟨q, (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective ?_⟩
  rw [← hq, ← IsScalarTower.algebraMap_apply]

def cyc (K : FinExt l) (a : ℤ) : ↥(GK K) →* GL (Fin 1) ↥(MaximalUnramifiedExtension l) :=
  (Units.map ((Matrix.scalar (Fin 1)).comp (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))).toMonoidHom).comp
    ((zpowGroupHom a).comp (P.χQ.comp (GK K).subtype))

theorem kd_alg (q : ℚ_[l]) : kd P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] P.R.BdR q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR]; rfl

theorem act_zpow (g : GQ l) (a : ℤ) :
    P.actQ g (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) =
      algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (isUnit_tB P).unit =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * (isUnit_tB P).unit := by
    ext; simp [localPrime_galoisAction_periodT, Algebra.smul_def]
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at h2
  rw [← map_zpow P.χQ]
  exact h2

end GlobalTheory.PMon.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicLevelIntegersMemClosureLevelsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicLevel_integers_mem_closure_levels : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s : ℕ, 1 ≤ s → ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → α ∈ AddSubgroup.closure {x : Om l | ∃ (j n : ℕ) (c : Om l), 1 ≤ j ∧ j ≤ s ∧ ¬ l ∣ n ∧ c ∈ K0 K ∧ ‖c‖ ≤ 1 ∧ x = c * ζ j ^ n} := by
  first | exact @GlobalTheory.Cyc.integers_mem_closure_levels | exact GlobalTheory.Cyc.integers_mem_closure_levels | (intros; apply GlobalTheory.Cyc.integers_mem_closure_levels <;> assumption)
end

