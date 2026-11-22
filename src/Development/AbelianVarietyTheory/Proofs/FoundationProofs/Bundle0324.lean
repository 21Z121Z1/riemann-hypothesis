import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0320
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateSeriesEqConstMulIntegralOneSeries
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaUnit
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

section
variable {p : ℕ} [Fact p.Prime]

theorem lamC_eq (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) : lamC lam x = lam ⟨x, hx⟩ := dif_pos hx

theorem lamC_mul' (lam : Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ Qbar) (hy : y ∈ Qbar) :
    lamC lam (x * y) = lamC lam x * lamC lam y := by
  rw [lamC_eq lam hx, lamC_eq lam hy, lamC_eq lam (mul_mem hx hy), ← map_mul]; rfl

theorem lamC_ne_zero (lam : Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ Qbar) (h0 : x ≠ 0) : lamC lam x ≠ 0 := by
  rw [lamC_eq lam hx]
  intro h
  apply h0
  have := (map_eq_zero_iff lam lam.injective).1 h
  exact congrArg Subtype.val this

theorem intSer_one : IntSer (1 : PowerSeries ℂ_[p]) := by
  have := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 1).2 norm_one.le
  rwa [map_one] at this

theorem intSer_pow {f : PowerSeries ℂ_[p]} (hf : IntSer f) (n : ℕ) : IntSer (f ^ n) := by
  induction n with
  | zero => simpa using intSer_one (p := p)
  | succ n ih => rw [pow_succ]; exact ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ ih hf).2.2

end

theorem tors_neg' {p : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 p Λ t) : GL3Theta.Tors1 p Λ (-t) := by
  obtain ⟨h0, n, hn, hc, h⟩ := h
  exact ⟨by simpa using h0, n, hn, hc, by simpa using h⟩

theorem laQ_of_tors {p : ℕ} {Λ : AddSubgroup ℂ} {t : ℂ} (h : GL3Theta.Tors1 p Λ t) : InRationalLattice Λ t :=
  let ⟨_, n, hn, _, h⟩ := h; ⟨n, hn, h⟩

theorem thetaTranslateOperator_zero_eq_self (Λ : AddSubgroup ℂ) (F : ℂ → ℂ) : U1 Λ 0 F = F := by
  funext z; simp [U1]

theorem thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice {Λ : AddSubgroup ℂ} (hlat : IsLat Λ) {t : ℂ} (ht : t ∉ Λ) :
    U1 Λ t (sgStar Λ) 0 ≠ 0 := by
  simp only [U1, zero_add]
  exact mul_ne_zero ((hlat.sg_eq_zero t).not.2 ht) (Complex.exp_ne_zero _)

theorem atU_smul' {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) {c : ℂ} (hc : c ∈ Qbar) {F : ℂ → ℂ} (hF : AlgEnt F) :
    AlgEnt (fun z => c * F z) ∧ g.atU (fun z => c * F z) = PowerSeries.C (lamC g.lam c) * g.atU F := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 c hc
  rw [← h2]
  exact ((GlobalTheory.SerTransport.transport p g).1 _ _ h1 hF).1

theorem tau_eq_C_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g t = PowerSeries.C (GlobalTheory.ThetaTransl.cval g t) * w := by
  intro D p _ cc δ g hg hx t ht
  have hA := GlobalTheory.T.thetaTranslatePowerSeries_pow_boundedCoeffs_of_torsion D p cc δ g hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  obtain ⟨-, hw, -, hE, -⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hsg : AlgEnt (sgStar g.abelian₂) := by
    have := halg 0 ⟨1, one_pos, by simp⟩
    rwa [thetaTranslateOperator_zero_eq_self] at this
  have hEi : (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hE]; exact one_ne_zero)
  have hcon : ∀ s, InRationalLattice g.abelian₂ s → PowerSeries.constantCoeff (tau g s) = cval g s ∧
      U1 g.abelian₂ s (sgStar g.abelian₂) 0 ∈ Qbar := by
    intro s hs
    obtain ⟨c, d⟩ := (GlobalTheory.SerTransport.transport p g).2.2.1 _ (halg s hs)
    refine ⟨?_, c⟩
    rw [tau, map_mul, PowerSeries.constantCoeff_inv, hE, inv_one, one_mul, d, cval]
  have hq := laQ_of_tors ht
  have hq' := laQ_of_tors (tors_neg' ht)
  obtain ⟨c1, c2⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t ht.1 (hwp t hq ht.1).1
  have a3 := (hcon t hq).2
  have b3 := (hcon (-t) hq').2
  have e := (atU_smul' g (mul_mem a3 b3) c1).2
  rw [funext (hlat'.sqTh_mul ht.1), ((GlobalTheory.SerTransport.transport p g).1 _ _ (halg _ hq) (halg _ hq')).1.2,
    c2, lamC_mul' _ a3 b3] at e
  have hprod : tau g t * tau g (-t) = PowerSeries.C (cval g t * cval g (-t)) *
      lineSer g.wq⁻¹ (xAt g t) := by
    simp only [tau, cval]
    linear_combination ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * (ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹) * e +
      PowerSeries.C (lamC g.lam (U1 g.abelian₂ t (sgStar g.abelian₂) 0) * lamC g.lam (U1 g.abelian₂ (-t) (sgStar g.abelian₂) 0)) *
        lineSer g.wq⁻¹ (xAt g t) * ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq + 1) * hEi

  have hL : IntSer (lineSer g.wq⁻¹ (xAt g t)) := by
    have h1 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 (xAt g t)).2 (hx t ht)
    have h2 := (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1
    have h3 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ h2 h2).2.2
    have h4 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ h1 h3).2.2
    have h5 := ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).1 _ _ hw h4).2.1
    simpa [lineSer, _root_.sq, mul_assoc] using h5
  obtain ⟨n, hn, hcop, hnt⟩ := ht.2
  have hnt' : (n : ℂ) * (-t) ∈ g.abelian₂ := by rw [mul_neg]; exact neg_mem hnt
  have B1 := hA t ht n hn hnt
  have B2 := hA (-t) (tors_neg' ht) n hn hnt'
  set c := cval g t with hc
  set c' := cval g (-t) with hc'
  have hc0 : c ≠ 0 := lamC_ne_zero _ a3 (thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice hlat' ht.1)
  have hc0' : c' ≠ 0 := lamC_ne_zero _ b3 (thetaTranslate_sigmaStar_at_zero_ne_zero_of_not_mem_lattice hlat' (tors_neg' ht).1)
  have hpow : tau g t ^ n * tau g (-t) ^ n = PowerSeries.C ((c * c') ^ n) * lineSer g.wq⁻¹ (xAt g t) ^ n := by
    rw [← mul_pow, hprod, mul_pow, map_pow]
  have hbound : ∀ k, ‖PowerSeries.coeff k (tau g t ^ n * tau g (-t) ^ n)‖ ≤ ‖c * c'‖ ^ n := by
    intro k
    rw [hpow, PowerSeries.coeff_C_mul, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (intSer_pow hL n k)
  have G := GlobalTheory.EvenTheta.sup_norm_mul_padicComplex p _ _ _ B1 B2 hbound
  have h0' : PowerSeries.coeff 0 (tau g (-t) ^ n) = c' ^ n := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, (hcon _ hq').1]
  have hcn : 0 < ‖c'‖ ^ n := pow_pos (norm_pos_iff.2 hc0') n
  have hle : ∀ i, ‖PowerSeries.coeff i (tau g t ^ n)‖ ≤ ‖c‖ ^ n := by
    intro i
    have := G i 0
    rw [h0', norm_pow, norm_mul, mul_pow] at this
    exact le_of_mul_le_mul_right this hcn
  set s := PowerSeries.C c⁻¹ * tau g t with hs
  have hsn : IntSer (s ^ n) := by
    intro k
    rw [hs, mul_pow, ← map_pow, PowerSeries.coeff_C_mul, norm_mul, norm_pow, norm_inv]
    have hcp : 0 < ‖c‖ ^ n := pow_pos (norm_pos_iff.2 hc0) n
    calc ‖c‖⁻¹ ^ n * ‖PowerSeries.coeff k (tau g t ^ n)‖ ≤ ‖c‖⁻¹ ^ n * ‖c‖ ^ n :=
          mul_le_mul_of_nonneg_left (hle k) (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (norm_ne_zero_iff.2 hc0), one_pow]
  have hs0 : PowerSeries.constantCoeff s = 1 := by
    rw [hs, map_mul, PowerSeries.constantCoeff_C, (hcon t hq).1, inv_mul_cancel₀ hc0]
  refine ⟨s, GlobalTheory.T.powerSeriesCoeffNormLeOne_root_coprime_padic p n hn hcop s hs0 hsn, hs0, ?_⟩
  rw [hs, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]

end GlobalTheory.ThetaUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
section
noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GlobalTheory.CMPrimeIdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace EulerTie

variable (F E) in

def finComp : AE F E →+* FiniteAdeleRing (𝓞 E) E := (toFinAd F E).comp (finPart F E)

omit [NumberField E] in
theorem parts_extZero (y : Af F ⊗[F] E) :
    infPart F E (extZero F E y) = 0 ∧ finPart F E (extZero F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, and_self]
  | tmul a x => exact ⟨TensorProduct.zero_tmul _ _, rfl⟩
  | add a b ha hb => simp only [map_add, ha.1, ha.2, hb.1, hb.2, add_zero, and_self]

theorem comp_finComp : Comp (finComp F E) := by
  let c := (Algebra.TensorProduct.comm F E (Af F)).toRingEquiv
  have hι : ∀ x a, ((toFinAd F E).comp c.toRingHom) (x ⊗ₜ[F] a) =
      algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F E a := fun x a => (toFinAd_tmul a x).trans (mul_comm _ _)
  have hs : ∀ y, ((toFinAd F E).comp c.toRingHom) (swapAf F E y) = toFinAd F E y := fun y =>
    congrArg (toFinAd F E) ((Algebra.TensorProduct.comm F (Af F) E).symm_apply_apply y)
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨fun z h1 h2 => ?_, fun s => ?_, fun x => ?_, fun z => ?_, fun a Q => ?_⟩
  · have h3 : finPart F E z = 0 := toFinAd_bijective.1 (h2.trans (map_zero _).symm)
    apply e.injective
    rw [map_zero]
    exact Prod.ext ((he z).1.trans h1) ((he z).2.trans h3)
  · obtain ⟨y, rfl⟩ := (toFinAd_bijective (F := F)).2 s
    exact ⟨_, (parts_extZero y).1, congrArg (toFinAd F E) (parts_extZero y).2⟩
  · change toFinAd F E ((1 : Af F) ⊗ₜ[F] x) = _
    rw [toFinAd_tmul, map_one, one_mul]
  · rw [mem_intAE_iff]
    refine ⟨fun h => ?_, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι ?_⟩
    · have := GlobalTheory.AdeleBaseChange.map_mem_int hι h
      rw [hs] at this
      exact this
    · rw [hs]; exact h
  · change toFinAd F E (a.2 ⊗ₜ[F] (1 : E)) Q = _
    rw [toFinAd_tmul, map_one, mul_one]
    rfl

theorem parts_locIdele (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    infPart F E (locIdele F P u : AE F E) = 1 ∧
      finComp F E (locIdele F P u : AE F E) = (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 E) E) := by
  have e : (locIdele F P u : AE F E) = 1 - extZero F E 1 +
      extZero F E ((finAdEquiv F E).symm (GlobalTheory.CMVal.single P u : FiniteAdeleRing (𝓞 E) E)) := rfl
  rw [e]
  constructor
  · rw [RingHom.map_add, RingHom.map_sub, RingHom.map_one, (parts_extZero _).1, (parts_extZero _).1, sub_zero, add_zero]
  · change toFinAd F E (finPart F E _) = _
    rw [RingHom.map_add, RingHom.map_sub, RingHom.map_one, (parts_extZero _).2, (parts_extZero _).2, sub_self, zero_add]
    exact (finAdEquiv F E).apply_symm_apply _

theorem comp_glue {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (he : IsDelta (finComp F E) P e) (a : AE F E) :
    infPart F E (e * a + (1 - e)) = 1 ∧ finComp F E (e * a + (1 - e)) P = finComp F E a P ∧
      ∀ Q, Q ≠ P → finComp F E (e * a + (1 - e)) Q = 1 := by
  have h : ∀ Q, finComp F E (e * a + (1 - e)) Q = finComp F E e Q * finComp F E a Q + (1 - finComp F E e Q) :=
    fun Q => by rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]; rfl
  refine ⟨?_, ?_, fun Q hQ => ?_⟩
  · rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, he.1, zero_mul, sub_zero, zero_add]
  · rw [h, he.2.1, one_mul, sub_self, add_zero]
  · rw [h, he.2.2 Q hQ, zero_mul, sub_zero, zero_add]

theorem finComp_locIdele_self (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    finComp F E (locIdele F P u : AE F E) P = u := by
  rw [(parts_locIdele P u).2, GlobalTheory.CMVal.single_self]

theorem finComp_locIdele_ne {P Q : HeightOneSpectrum (𝓞 E)} (h : Q ≠ P) (u : (P.adicCompletion E)ˣ) :
    finComp F E (locIdele F P u : AE F E) Q = 1 := by
  classical
  rw [(parts_locIdele P u).2, GlobalTheory.CMVal.single_apply]
  exact Function.update_of_ne h _ _

theorem glue_eq_locIdele {P : HeightOneSpectrum (𝓞 E)} {e : AE F E} (he : IsDelta (finComp F E) P e) {a : AE F E}
    {u : (P.adicCompletion E)ˣ} (h : finComp F E a P = u) : e * a + (1 - e) = (locIdele F P u : AE F E) := by
  obtain ⟨h1, h2, h3⟩ := comp_glue he a
  refine comp_finComp.ext' (h1.trans (parts_locIdele P u).1.symm) fun Q => ?_
  by_cases hQ : Q = P
  · subst hQ; rw [h2, h, finComp_locIdele_self]
  · rw [h3 Q hQ, finComp_locIdele_ne hQ]

theorem locIdele_int_iff (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    finPart F E (locIdele F P u : AE F E) ∈ intAE F E ↔ Valued.v (u : P.adicCompletion E) ≤ 1 := by
  rw [comp_finComp.2.2.2.1]
  refine ⟨fun h => ?_, fun h Q => ?_⟩
  · have := h P
    rwa [finComp_locIdele_self] at this
  · by_cases hQ : Q = P
    · subst hQ; rw [finComp_locIdele_self]; exact h
    · rw [finComp_locIdele_ne hQ]; exact one_mem _

theorem isUnitAt_iff (P : HeightOneSpectrum (𝓞 E)) (u : (P.adicCompletion E)ˣ) :
    Formalism.L2.Host.IsUnitAt P u ↔ Valued.v (u : P.adicCompletion E) ≤ 1 ∧
      Valued.v ((u⁻¹ : (P.adicCompletion E)ˣ) : P.adicCompletion E) ≤ 1 := by
  have h0 : 0 < Valued.v (u : P.adicCompletion E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 u.ne_zero)
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ h0]
  exact le_antisymm_iff

variable {σ : E →ₐ[F] E}

theorem isDelta_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 E)} {e f : AE F E} (h : IsPrimeIdem σ P e f) :
    IsDelta (finComp F E) P e := by
  rcases h with ⟨⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩, -⟩ | ⟨-, ⟨v, ε, hε, h3⟩, ht⟩
  · refine (tie_iff comp_finComp h1 ?_ P).1 ht
    have : e = e * algebraMap (AF F) (AE F E) ε := by rw [← h3, mul_add, h1, h2, add_zero]
    rw [this, RingHom.map_mul, (place_comp (comp_finComp (E := E)) hε).1, mul_zero]
  · obtain ⟨k0, k1, k2⟩ := place_comp (comp_finComp (E := E)) hε
    rw [← h3] at k0 k1 k2
    refine (tie_iff comp_finComp (comp_finComp.ext' (by rw [RingHom.map_mul, k0, mul_zero]) fun Q => ?_) k0 P).1 ht
    rw [ev_mul]
    by_cases hQ : Q.under (𝓞 F) = v
    · rw [k1 Q hQ, mul_one]
    · rw [k2 Q hQ, mul_zero]

theorem valuation_of_mem_notMem_sq (P : HeightOneSpectrum (𝓞 E)) {a : 𝓞 E} (h1 : a ∈ P.asIdeal)
    (h2 : a ∉ P.asIdeal ^ 2) : P.valuation E (a : E) = WithZero.exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have k1 : P.intValuation a ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; simpa using h1
  have k2 : ¬ P.intValuation a ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]; exact h2
  have h0 : P.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero P a ha
  refine (HeightOneSpectrum.valuation_of_algebraMap P a).trans ?_
  rw [← WithZero.exp_log h0] at k1 k2 ⊢
  rw [WithZero.exp_le_exp] at k1 k2
  congr 1
  omega

theorem exists_of_isUnifIdele {P : HeightOneSpectrum (𝓞 E)} {x : (AE F E)ˣ} (h : IsUnifIdele σ P x) :
    ∃ u, Formalism.L2.Host.IsUnifAt P u ∧ x = locIdele F P u := by
  obtain ⟨e, f, ϖ, he, h1, h2, hx⟩ := h
  have hv : Valued.v (algebraMap E (P.adicCompletion E) (ϖ : E)) = WithZero.exp (-1 : ℤ) :=
    (Formalism.UG.P.levelaf_valued_algebraMap _ _).trans (valuation_of_mem_notMem_sq P h1 h2)
  have h0 : algebraMap E (P.adicCompletion E) (ϖ : E) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  refine ⟨Units.mk0 _ h0, hv, Units.ext (hx.trans (glue_eq_locIdele (isDelta_of_isPrimeIdem he) ?_))⟩
  rw [comp_finComp.2.2.1]
  rfl

end EulerTie

open EulerTie

variable {σ : E →ₐ[F] E}

theorem isUnramAt_iff_unrAt (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) :
    IsUnramAt σ χ P ↔ UnrAt χ P := by
  constructor
  · rintro ⟨e, f, he, h⟩ u hu
    obtain ⟨h1, h2⟩ := (isUnitAt_iff P u).1 hu
    have := h (locIdele F P u) (glue_eq_locIdele (isDelta_of_isPrimeIdem he) (finComp_locIdele_self P u)).symm
      ((locIdele_int_iff P u).2 h1) (by rw [← map_inv]; exact (locIdele_int_iff P u⁻¹).2 h2)
    exact (congrArg Circle.toUnits this).trans (map_one _)
  · intro h
    obtain ⟨e, f, -, he⟩ := exists_isPrimeIdem hσ P
    refine ⟨e, f, he, fun x hx h1 h2 => ?_⟩
    let π : AE F E →+* P.adicCompletion E := (evalV E P).toRingHom.comp (finComp F E)
    obtain ⟨u, rfl⟩ : ∃ u, x = locIdele F P u :=
      ⟨Units.map π.toMonoidHom x, Units.ext (hx.trans (glue_eq_locIdele (isDelta_of_isPrimeIdem he) rfl))⟩
    rw [← map_inv] at h2
    have := h u ((isUnitAt_iff P u).2 ⟨(locIdele_int_iff P u).1 h1, (locIdele_int_iff P u⁻¹).1 h2⟩)
    exact Circle.ext (congrArg Units.val this)

theorem chiAt_eq_val (hσ : IsCMExt F E σ) {χ : (AE F E)ˣ →* Circle} {P : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ P) :
    chiAt σ χ P = (val χ P : ℂ) := by
  have hc : IsUnramAt σ χ P ∧ ∃ x, IsUnifIdele σ P x := ⟨(isUnramAt_iff_unrAt hσ χ P).2 h, exists_isUnifIdele hσ P⟩
  obtain ⟨u, hu, e⟩ := exists_of_isUnifIdele hc.2.choose_spec
  rw [chiAt, dif_pos hc, e, ← h.locChar_eq_val hu]
  rfl

theorem chiAt_eq_zero (hσ : IsCMExt F E σ) {χ : (AE F E)ˣ →* Circle} {P : HeightOneSpectrum (𝓞 E)}
    (h : ¬ UnrAt χ P) : chiAt σ χ P = 0 :=
  dif_neg fun hc => h ((isUnramAt_iff_unrAt hσ χ P).1 hc.1)

theorem lfac_eq_locL (hσ : IsCMExt F E σ) (χ : (AE F E)ˣ →* Circle) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    lfac σ χ P s = locL (charFam χ) P s := by
  unfold lfac locL charFam
  split_ifs with h
  · rw [chiAt_eq_val hσ h, eulerFac_singleton]; rfl
  · rw [chiAt_eq_zero hσ h, eulerFac_zero, zero_mul, sub_zero, inv_one]

end GlobalTheory.LFun

end
end

