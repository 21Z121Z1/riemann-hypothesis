import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefMajorantOfPositiveIndexOne
section
open Matrix GlobalTheory.LKTrip

namespace GlobalTheory.HermitianMajorantIdentities

theorem mul_vecMulVec_mul' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    A * vecMulVec u v * B = vecMulVec (A *ᵥ u) (v ᵥ* B) := by
  ext i j
  simp only [mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem form_vecMulVec {n : ℕ} (u x : Fin n → ℂ) :
    star x ⬝ᵥ vecMulVec u (star u) *ᵥ x = (star x ⬝ᵥ u) * (star u ⬝ᵥ x) := by
  rw [vecMulVec_mulVec, dotProduct_smul, op_smul_eq_mul]

theorem herm_swap {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (x y : Fin n → ℂ) :
    star y ⬝ᵥ H *ᵥ x = star (star x ⬝ᵥ H *ᵥ y) := by
  rw [star_dotProduct, star_mulVec, hH.eq, ← dotProduct_mulVec]

end GlobalTheory.HermitianMajorantIdentities

namespace GlobalTheory

open GlobalTheory.HermitianMajorantIdentities in

theorem exists_posDef_majorant_of_sigPosH_eq_one : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 → ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re → ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H → Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P := by
  intro n H hH hdet hsig z hz
  set a : ℝ := (star z ⬝ᵥ H *ᵥ z).re with ha
  have hzz : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := by
    have h := herm_swap hH z z
    exact (Complex.conj_eq_iff_re.mp h.symm).symm
  set u : Fin n → ℂ := H *ᵥ z with hu
  have hux : ∀ x, star u ⬝ᵥ x = star z ⬝ᵥ H *ᵥ x := by
    intro x; rw [hu, star_mulVec, hH.eq, ← dotProduct_mulVec]
  refine ⟨((2 / a : ℝ) : ℂ) • vecMulVec u (star u) - H, ?_, ?_, ?_⟩
  · unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_smul, hH.eq, conjTranspose_vecMulVec, star_star]
    simp [Complex.star_def]
  · intro x hx
    set q := star z ⬝ᵥ H *ᵥ x with hq
    set t : ℂ := q / (a : ℂ) with ht
    set x' := x - t • z with hx'
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hzx' : star z ⬝ᵥ H *ᵥ x' = 0 := by
      rw [hx', mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hzz, ← hq, ht, smul_eq_mul]
      field_simp; ring
    have hx'z : star x' ⬝ᵥ H *ᵥ z = 0 := by
      rw [herm_swap hH z x', hzx', star_zero]
    have hzz' : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := hzz
    have hxe : x = t • z + x' := by rw [hx']; abel
    have hxx : star x ⬝ᵥ H *ᵥ x = star t * t * (a : ℂ) + star x' ⬝ᵥ H *ᵥ x' := by
      conv_lhs => rw [hxe]
      simp only [star_add, star_smul, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hzx', hx'z, hzz']
      ring
    have hxz : star x ⬝ᵥ H *ᵥ z = star q := herm_swap hH z x
    have hP : star x ⬝ᵥ (((2 / a : ℝ) : ℂ) • vecMulVec u (star u) - H) *ᵥ x
        = ((2 / a : ℝ) : ℂ) * (star q * q) - (star t * t * (a : ℂ) + star x' ⬝ᵥ H *ᵥ x') := by
      rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, form_vecMulVec, hux, hxx,
        smul_eq_mul]
      rw [show star x ⬝ᵥ u = star q from hxz]
    have hqt : q = t * (a : ℂ) := by rw [ht]; field_simp
    have hnt : star t * t = ((Complex.normSq t : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [hP, hqt, star_mul', Complex.star_def, Complex.conj_ofReal]
    have e1 : ((starRingEnd ℂ) t * (a : ℂ) * (t * (a : ℂ))) = ((Complex.normSq t * a * a : ℝ) : ℂ) := by
      rw [← Complex.star_def, show star t * (a:ℂ) * (t * (a:ℂ)) = (star t * t) * ((a * a : ℝ) : ℂ) by push_cast; ring, hnt]
      push_cast; ring
    rw [e1, ← Complex.star_def, hnt]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_mul]
    have hapos : 0 < a := hz
    by_cases h0 : x' = 0
    · have htne : t ≠ 0 := by
        intro ht0
        apply hx
        rw [hxe, h0, ht0, zero_smul, add_zero]
      have hnpos : 0 < Complex.normSq t := Complex.normSq_pos.mpr htne
      rw [h0]
      simp only [star_zero, zero_dotProduct, Complex.zero_re, add_zero]
      field_simp
      nlinarith [mul_pos hnpos hapos]
    · have hneg := re_form_neg_of_orth_of_sigPosH_eq_one H hH hdet hsig z x' hz hzx' h0
      have hn0 : 0 ≤ Complex.normSq t := Complex.normSq_nonneg t
      have : 2 / a * (Complex.normSq t * a * a) - Complex.normSq t * a = Complex.normSq t * a := by
        field_simp; ring
      nlinarith [mul_nonneg hn0 hapos.le]
  · intro Y s c hs hY hYz
    have hzz' : star z ⬝ᵥ H *ᵥ z = (a : ℂ) := hzz
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
    have hA : ∀ x, star (Y *ᵥ z) ⬝ᵥ H *ᵥ (Y *ᵥ x) = (s : ℂ) * (star z ⬝ᵥ H *ᵥ x) := by
      intro x
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hY,
        smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hB : ∀ x, star (Y *ᵥ z) ⬝ᵥ H *ᵥ (Y *ᵥ x) = star c * (star z ⬝ᵥ H *ᵥ (Y *ᵥ x)) := by
      intro x
      rw [hYz, star_smul, smul_dotProduct, smul_eq_mul]
    have hsc : (s : ℂ) = star c * c := by
      have h1 := (hA z).symm.trans (hB z)
      rw [hYz, mulVec_smul, dotProduct_smul, smul_eq_mul, hzz'] at h1
      have h2 : ((s : ℂ) - star c * c) * (a : ℂ) = 0 := by rw [sub_mul, h1]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right ha0)
    have hc0 : star c ≠ 0 := by
      intro h0
      have : (s : ℂ) = 0 := by rw [hsc, h0, zero_mul]
      exact hs.ne' (by exact_mod_cast this)
    have hrow : ∀ x, star z ⬝ᵥ H *ᵥ (Y *ᵥ x) = c * (star z ⬝ᵥ H *ᵥ x) := by
      intro x
      have h1 := (hA x).symm.trans (hB x)
      rw [hsc, mul_assoc] at h1
      exact (mul_left_cancel₀ hc0 h1).symm
    have hrowv : star u ᵥ* Y = c • star u := by
      funext j
      have h1 : (star u ᵥ* Y) ⬝ᵥ Pi.single j 1 = (c • star u) ⬝ᵥ Pi.single j 1 := by
        rw [← dotProduct_mulVec, hux, hrow, smul_dotProduct, hux, smul_eq_mul]
      simpa [dotProduct_single] using h1
    have hcolv : Yᴴ *ᵥ u = star c • u := by
      have h1 := congrArg star hrowv
      rw [star_vecMul, star_star, star_smul, star_star] at h1
      exact h1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec_mul', hcolv,
      hrowv, hY]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hsc]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeEqSpanOfCoheightLeOne
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_prime_eq_span_of_coheight_le_one (R : Type) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R) (hq : GeneralizingMap q)
    (x : X) (hx : Order.coheight x ≤ 1) (hne : (q x).asIdeal ≠ ⊥) :
    ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  obtain ⟨π, hπP, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (q x).isPrime hne
  refine ⟨π, hπ, ?_⟩
  by_contra hQP
  have hQle : Ideal.span {π} ≤ (q x).asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hπP
  have hQprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  let Q : PrimeSpectrum R := ⟨_, hQprime⟩
  have hQsp : Q ⤳ q x := (PrimeSpectrum.le_iff_specializes Q (q x)).1 hQle
  obtain ⟨x', hx'x, hqx'⟩ := hq hQsp
  let B : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hBQ : B ⤳ Q := (PrimeSpectrum.le_iff_specializes B Q).1 bot_le
  obtain ⟨x'', hx''x', hqx''⟩ := hq (hqx' ▸ hBQ)
  have h1 : x < x' := by
    refine lt_of_le_not_ge hx'x ?_
    intro h
    have h' : q x ⤳ q x' := h.map q.continuous
    rw [hqx'] at h'
    exact hQP (le_antisymm ((PrimeSpectrum.le_iff_specializes (q x) Q).2 h') hQle)
  have h2 : x' < x'' := by
    refine lt_of_le_not_ge hx''x' ?_
    intro h
    have h' : q x' ⤳ q x'' := h.map q.continuous
    rw [hqx', hqx''] at h'
    have hle : Ideal.span {π} ≤ ⊥ := (PrimeSpectrum.le_iff_specializes Q B).2 h'
    exact hπ.ne_zero (Ideal.span_singleton_eq_bot.1 (le_bot_iff.1 hle))
  have c1 := Order.coheight_add_one_le h1
  have c2 := Order.coheight_add_one_le h2
  have : (2 : ℕ∞) ≤ Order.coheight x := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight x'' + 1 + 1 := by gcongr; exact bot_le
      _ ≤ Order.coheight x' + 1 := by gcongr
      _ ≤ Order.coheight x := c1
  have := this.trans hx
  norm_num at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulRatEqIntOfIntegralAway
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

open IsDedekindDomain

theorem ratint_away : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ),
    (∀ v : AwayP p, algebraMap ℚ (v.1.adicCompletion ℚ) q ∈ v.1.adicCompletionIntegers ℚ) →
    ∃ m : ℕ, ∃ z : ℤ, (p : ℚ) ^ m * q = z := by
  intro p hp q h
  have hp' : p.Prime := hp.out
  have key : ∀ {l : ℕ}, l.Prime → l ∣ q.den → l = p := by
    intro l hl hld
    by_contra hne
    have hlI : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
    let v : HeightOneSpectrum ℤ :=
      ⟨Ideal.span {(l : ℤ)}, (Ideal.span_singleton_prime hlI.ne_zero).2 hlI, by simpa using hl.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro e
      have h1 : (l : ℤ) ∣ (p : ℤ) := Ideal.mem_span_singleton.1 (by
        have : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.mem_span_singleton_self _
        rw [← e] at this
        exact Ideal.mem_span_singleton.1 this |>.elim (fun c hc => by
          exact Ideal.mem_span_singleton.2 ⟨c, hc⟩))
      have h2 : l ∣ p := Int.natCast_dvd_natCast.1 h1
      exact hne ((Nat.prime_dvd_prime_iff_eq hl hp').1 h2)
    have hq := h ⟨v, hv⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hq
    have hq2 : v.valuation ℚ q ≤ 1 := by
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact hq
    have hb : ((q.den : ℤ)) ≠ 0 := by exact_mod_cast q.den_nz
    have hcop : ((q.den : ℤ)) ∈ v.asIdeal → q.num ∉ v.asIdeal := by
      intro hd hn
      have hd' : (l : ℤ) ∣ (q.den : ℤ) := Ideal.mem_span_singleton.1 hd
      have hn' : (l : ℤ) ∣ q.num := Ideal.mem_span_singleton.1 hn
      have hc : IsCoprime q.num (q.den : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        exact_mod_cast q.reduced
      exact hlI.not_unit (hc.isUnit_of_dvd' hn' hd')
    have e : q = ((algebraMap ℤ ℚ q.num) / (algebraMap ℤ ℚ (q.den : ℤ))) := by
      simp [Rat.num_div_den]
    rw [e, v.valuation_div_le_one_iff ℚ q.num hb hcop] at hq2
    exact hq2 (Ideal.mem_span_singleton.2 (Int.natCast_dvd_natCast.2 hld))
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hld => key hl hld)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  have : ((p : ℚ) ^ q.den.primeFactorsList.length) = (q.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.den_mul_eq_num]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPsiOfOverK
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift

theorem overK_of_sqrt {D : D7} (σ : D.what₂.LL →+* ℂ)
    (h : σ (D.embE D.host.sqrtMinusD) = D.what₂.embLL (D.embE D.host.sqrtMinusD)) : OverK σ := by
  intro x hx
  have hx' : x ∈ IntermediateField.adjoin ℚ {D.host.sqrtMinusD} := hx
  clear hx
  induction hx' using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact h
  | algebraMap q => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, map_mul, hx, hy]

theorem embLL_embE (D : D7) (x : D.host.E) : D.what₂.embLL (D.embE x) = D.host.φ₀ x :=
  RingHom.congr_fun D.embE_φ₀ x

theorem sqrtMinusD_sq (D : D7) : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem overK_conj {D : D7} (σ : D.what₂.LL →+* ℂ) (h : ¬ OverK σ) : OverK ((starRingEnd ℂ).comp σ) := by
  apply overK_of_sqrt
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have h1 : σ (D.embE D.host.sqrtMinusD) ^ 2 = D.what₂.embLL (D.embE D.host.sqrtMinusD) ^ 2 := by
    rw [← map_pow, ← map_pow, ← map_pow, ← map_pow, sqrtMinusD_sq]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact absurd (overK_of_sqrt σ h2) h
  · rw [RingHom.comp_apply, h2, embLL_embE, h0]; simp

theorem exists_psi_of_overK {D : D7} (σ : D.what₂.LL →+* ℂ) (h : OverK σ) :
    ∃ g ∈ D.R.Psi, ∀ τ, labE σ τ = D.host.emb (g * (D.eTau τ).1) := by
  obtain ⟨g0, h0⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  refine ⟨g0, ((factEmb D.R D.host).2 _).1 ?_, fun τ => ?_⟩
  · have h1 := h D.host.sqrtMinusD (IntermediateField.mem_adjoin_simple_self ℚ _)
    have h2 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
    rw [h0]
    exact h1.trans ((embLL_embE D _).trans h2)
  · rw [ConjReading.emb_mul, h0]; rfl

theorem labels_overK : ∀ {D : D7} (σ : D.what₂.LL →+* ℂ),
    (OverK σ → Function.Bijective (lab (D := D) σ) ∧ ∀ ρ, labE σ (lab σ ρ) = tauE D ρ) ∧
      (¬ OverK σ → OverK ((starRingEnd ℂ).comp σ)) := by
  intro D σ
  refine ⟨fun h => ?_, overK_conj σ⟩
  obtain ⟨g, hg, key⟩ := exists_psi_of_overK σ h
  have inj := (factEmb D.R D.host).1.1
  have main : ∀ ρ, labE σ (lab σ ρ) = tauE D ρ := by
    intro ρ
    have hs : labE σ (lab σ ρ) = tauE D ρ ∨ labE σ (lab σ ρ) = (starRingEnd ℂ).comp (tauE D ρ) := by
      unfold lab; rw [dif_pos (ConjReading.lab_exists σ ρ)]; exact (ConjReading.lab_exists σ ρ).choose_spec
    refine hs.resolve_right fun h' => ?_
    rw [key] at h'
    exact ConjReading.conj_not_mem D ρ _ h' (Subgroup.mul_mem _ hg (D.eTau _).2)
  refine ⟨⟨fun ρ ρ' e => ?_, fun τ => ?_⟩, main⟩
  · have e' : tauE D ρ = tauE D ρ' := by rw [← main, ← main, e]
    exact D.eTau.injective (Subtype.ext (inj e'))
  · refine ⟨D.eTau.symm ⟨g * (D.eTau τ).1, Subgroup.mul_mem _ hg (D.eTau τ).2⟩, ?_⟩
    have e := main (D.eTau.symm ⟨g * (D.eTau τ).1, Subgroup.mul_mem _ hg (D.eTau τ).2⟩)
    rw [key, tauE, Equiv.apply_symm_apply] at e
    exact D.eTau.injective (Subtype.ext (mul_left_cancel (inj e)))

end GlobalTheory.GalLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyFiniteSubgroupSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_abelianVariety_finite_subgroupScheme : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A), IsMonHom i → Mono i → IsFinite H.hom → ∃ (A' : Over (Sp K)) (_ : GrpObj A'), IsAbelianScheme A' ∧ ∃ q : A ⟶ A', IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsPullback i (toUnit H) q η[A'] := by
  first | exact @GlobalTheory.AbelianQuotientField.exists_quotient | exact GlobalTheory.AbelianQuotientField.exists_quotient | (intros; apply GlobalTheory.AbelianQuotientField.exists_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalPointPolynomialIdempotentUnitValue
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.DenseAvoid

theorem finite_maximal_not_mem {F B E K : Type} [Field F] [CommRing B] [Algebra F B] [Field E] [Algebra F E]
    [FiniteDimensional F E] [CommRing K] [Algebra F K] [IsArtinianRing K]
    (ρ : B →ₐ[F] K) (hρ : Function.Surjective ρ) (f : B) (hf : f * f = f)
    (hk : ∀ x, ρ x = 0 → f * x = 0) :
    {m : Ideal (B ⊗[F] E) | m.IsMaximal ∧ algebraMap B (B ⊗[F] E) f ∉ m}.Finite := by
  classical
  let Φ : B ⊗[F] E →+* K ⊗[F] E := (Algebra.TensorProduct.map ρ (AlgHom.id F E)).toRingHom
  have hΦ : Function.Surjective Φ :=
    Algebra.TensorProduct.map_surjective ρ (AlgHom.id F E) hρ (fun y => ⟨y, rfl⟩)
  haveI : IsArtinianRing (K ⊗[F] E) := IsArtinianRing.of_finite K (K ⊗[F] E)
  refine ((IsArtinianRing.setOfPred_isMaximal_finite (K ⊗[F] E)).image (Ideal.comap Φ)).subset ?_
  rintro m ⟨hm, hfm⟩
  have h1 : 1 - algebraMap B (B ⊗[F] E) f ∈ m := by
    have h0 : algebraMap B (B ⊗[F] E) f * (1 - algebraMap B (B ⊗[F] E) f) ∈ m := by
      rw [mul_sub, mul_one, ← map_mul, hf, sub_self]; exact m.zero_mem
    exact (hm.isPrime.mem_or_mem h0).resolve_left hfm
  have hker : RingHom.ker Φ ≤ m := by
    have h := Algebra.TensorProduct.rTensor_ker (R := F) (C := E) ρ hρ
    change RingHom.ker (Algebra.TensorProduct.map ρ (AlgHom.id F E)) ≤ m
    rw [h, Ideal.map_le_iff_le_comap]
    intro x hx
    have hx' : f * x = 0 := hk x hx
    change x ⊗ₜ[F] (1 : E) ∈ m
    have e1 : algebraMap B (B ⊗[F] E) f * (x ⊗ₜ[F] (1 : E)) = 0 := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        Algebra.TensorProduct.tmul_mul_tmul, hx', TensorProduct.zero_tmul]
    have e2 : x ⊗ₜ[F] (1 : E) = (1 - algebraMap B (B ⊗[F] E) f) * (x ⊗ₜ[F] (1 : E)) := by
      rw [sub_mul, one_mul, e1, sub_zero]
    rw [e2]; exact m.mul_mem_right _ h1
  have hc : Ideal.comap Φ (m.map Φ) = m := by
    rw [Ideal.comap_map_of_surjective' Φ hΦ, sup_eq_left.2 hker]
  refine ⟨m.map Φ, ?_, hc⟩
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective Φ hΦ hm with h | h
  · exact absurd (by rw [← hc, h, Ideal.comap_top]) hm.ne_top
  · exact h

end GlobalTheory.DenseAvoid

namespace GlobalTheory.DenseAvoid

open GlobalTheory.LocalGlobalChar

variable {F : Type} [Field F] [NumberField F]

theorem eps_eq_sum (S : Finset (HeightOneSpectrum (𝓞 F))) :
    eps S = pairA F 1 0 + ∑ v ∈ S, pairA F 0 (ind {v}) := by
  classical
  have hext : ∀ a b : AF F, fstA F a = fstA F b → sndA F a = sndA F b → a = b := fun a b h1 h2 => Prod.ext h1 h2
  refine hext _ _ ?_ (fin_ext fun u => ?_)
  · rw [map_add, map_sum]
    change (1 : Ainf F) = 1 + ∑ v ∈ S, (0 : Ainf F)
    rw [Finset.sum_const_zero, add_zero]
  · rw [map_add, map_sum, map_add, map_sum]
    change evalV F u (ind S) = evalV F u 0 + ∑ v ∈ S, evalV F u (ind {v})
    simp_rw [ev_ind, Finset.mem_singleton, map_zero, zero_add]
    rw [Finset.sum_ite_eq]

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E]

theorem finite_maximal_not_mem_eps (S : Finset (HeightOneSpectrum (𝓞 F))) :
    {m : Ideal (AF F ⊗[F] E) | m.IsMaximal ∧ algebraMap (AF F) (AF F ⊗[F] E) (eps S) ∉ m}.Finite := by
  classical
  haveI : IsArtinianRing (Ainf F) := inferInstanceAs (IsArtinianRing ((w : InfinitePlace F) → w.Completion))
  have hinf := finite_maximal_not_mem (E := E) (fstA F) (fun y => ⟨pairA F y 0, rfl⟩) (pairA F 1 0)
    (Prod.ext (mul_one _) (mul_zero _)) (fun x hx => Prod.ext (by
      change (1 : Ainf F) * x.1 = 0
      rw [one_mul]; exact hx) (zero_mul _))
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F),
      {m : Ideal (AF F ⊗[F] E) | m.IsMaximal ∧ algebraMap (AF F) (AF F ⊗[F] E) (pairA F 0 (ind {v})) ∉ m}.Finite :=
    fun v => finite_maximal_not_mem (E := E) ((evalV F v).comp (sndA F))
      (fun y => ⟨pairA F 0 (singleV F v y), GlobalTheory.SplitCoord.evalV_single v y⟩) (pairA F 0 (ind {v}))
      (pl_mul_self v) (fun x hx => Prod.ext (zero_mul _) (fin_ext fun u => by
        change evalV F u (ind {v} * x.2) = evalV F u 0
        rw [map_mul, ev_ind, map_zero]
        split_ifs with h
        · rw [Finset.mem_singleton] at h
          subst h
          change evalV F u x.2 = 0 at hx
          rw [hx, mul_zero]
        · exact zero_mul _))
  refine (hinf.union (S.finite_toSet.biUnion fun v _ => hfin v)).subset ?_
  rintro m ⟨hm, hem⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_and, not_not, not_exists] at hn
  apply hem
  rw [eps_eq_sum, map_add, map_sum]
  exact m.add_mem (hn.1 hm) (m.sum_mem fun v hv => hn.2 v hv hm)

end GlobalTheory.DenseAvoid

open GlobalTheory.DenseAvoid in

theorem GlobalTheory.DenseAvoid.exists_unit_eval : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (S : Finset (HeightOneSpectrum (𝓞 F))) (ψ : Polynomial (AE F E)), (∀ (Ω : Type) [Field Ω] (φ : AE F E →+* Ω), φ (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S)) = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) * ψ.eval (algebraMap F (AE F E) t) + (1 - algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S))) := by
  intro F E _ _ _ _ _ S ψ hψ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  set e := algebraMap (AF F) (AE F E) (GlobalTheory.LocalGlobalChar.eps S) with he_def
  have he : e * e = e := by rw [he_def, ← map_mul, GlobalTheory.LocalGlobalChar.eps_mul_self]
  have hone : ∀ m : Ideal (AE F E), m.IsPrime → e ∉ m → 1 - e ∈ m := fun m hm hem => by
    have h0 : e * (1 - e) ∈ m := by rw [mul_sub, mul_one, he, sub_self]; exact m.zero_mem
    exact (hm.mem_or_mem h0).resolve_left hem
  have hM := finite_maximal_not_mem_eps (E := E) S
  let bad : Set F := ⋃ m ∈ {m : Ideal (AE F E) | m.IsMaximal ∧ e ∉ m},
    {t : F | Ideal.Quotient.mk m (ψ.eval (algebraMap F (AE F E) t)) = 0}
  have hbad : bad.Finite := by
    refine hM.biUnion fun m hm => ?_
    haveI := hm.1
    letI := Ideal.Quotient.field m
    have h1 : Ideal.Quotient.mk m e = 1 := by
      rw [← map_one (Ideal.Quotient.mk m), Ideal.Quotient.eq, ← neg_sub]
      exact m.neg_mem (hone m hm.1.isPrime hm.2)
    have hne := hψ (AE F E ⧸ m) (Ideal.Quotient.mk m) h1
    let j : F →+* AE F E ⧸ m := (Ideal.Quotient.mk m).comp (algebraMap F (AE F E))
    refine ((Polynomial.finite_setOf_isRoot hne).preimage j.injective.injOn).subset fun t ht => ?_
    change Ideal.Quotient.mk m (ψ.eval (algebraMap F (AE F E) t)) = 0 at ht
    change Polynomial.IsRoot _ (j t)
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, RingHom.comp_apply, Polynomial.eval₂_hom, ht]
  obtain ⟨t, ht⟩ := hbad.infinite_compl.nonempty
  refine ⟨t, ?_⟩
  by_contra hn
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hn)
  by_cases hem : e ∈ m
  · have h2 : 1 - e ∈ m := by
      have := m.sub_mem hxm (m.mul_mem_right (ψ.eval (algebraMap F (AE F E) t)) hem)
      rwa [add_sub_cancel_left] at this
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (by simpa using m.add_mem hem h2))
  · have h2 : e * ψ.eval (algebraMap F (AE F E) t) ∈ m := by
      have := m.sub_mem hxm (hone m hm.isPrime hem)
      rwa [add_sub_cancel_right] at this
    have h3 := (hm.isPrime.mem_or_mem h2).resolve_left hem
    apply ht
    simp only [bad, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨m, ⟨hm, hem⟩, Ideal.Quotient.eq_zero_iff_mem.2 h3⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryDoubledBlockDiagOne
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

namespace GlobalTheory

theorem unitary_diag_one_mem_dbl : ∀ (R E : Type) [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) (β : Type)
    [Fintype β] [DecidableEq β] (J : Matrix β β E) (g : UG c J), ∃ gd : UG c (dbl J),
    ((gd : GL (β ⊕ β) E) : Matrix (β ⊕ β) (β ⊕ β) E) = Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1 := by
  intro R E _ _ _ c β _ _ J g
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * J * ((g : GL β E) : Matrix β β E).map c = J := g.2
  have h1 : ((g : GL β E) : Matrix β β E) * (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) = 1 := Units.mul_inv _
  have h2 : (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) * ((g : GL β E) : Matrix β β E) = 1 := Units.inv_mul _
  have hm1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  have hm0 : (0 : Matrix β β E).map c = 0 := Matrix.map_zero _ (map_zero c)
  refine ⟨⟨⟨Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1,
    Matrix.fromBlocks (((g : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1, ?_, ?_⟩, ?_⟩, rfl⟩
  · rw [Matrix.fromBlocks_multiply]; simp [h1, Matrix.fromBlocks_one]
  · rw [Matrix.fromBlocks_multiply]; simp [h2, Matrix.fromBlocks_one]
  · show (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
        (Matrix.fromBlocks ((g : GL β E) : Matrix β β E) 0 0 1).map c = dbl J
    rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, hm0, hm1, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp [hg]

end GlobalTheory
end

