import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousAeval

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IntDimBounds
section
set_option linter.style.haveILetI false

namespace GroundTheory.Heights₂.Heights

open Algebra Cardinal
open scoped TensorProduct

noncomputable section

theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hb : P = ⊥
  · subst hb
    refine le_antisymm (fun n hn => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at hn
    have h := hn n
    rw [Int.isUnit_iff] at h
    rw [Ideal.mem_bot]
    rcases h with h | h
    · exact mul_self_eq_zero.mp (by linarith)
    · nlinarith [mul_self_nonneg n]
  · haveI := hP
    haveI : P.IsMaximal := IsPrime.to_maximal_ideal hb
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem ringKrullDim_le_add_one_of_quotient_le {B : Type} [CommRing B] [IsDomain B] (n : ℕ∞)
    (h : ∀ Q : Ideal B, Q.IsPrime → Q ≠ ⊥ → ringKrullDim (B ⧸ Q) ≤ n) :
    ringKrullDim B ≤ ((n + 1 : ℕ∞) : WithBot ℕ∞) := by
  let P0 : PrimeSpectrum B := ⟨⊥, Ideal.isPrime_bot⟩
  have hco : Order.coheight P0 ≤ n + 1 := by
    rw [Order.coheight_eq_iSup_gt_coheight]
    refine iSup₂_le fun Q hQ => ?_
    have hQ0 : Q.asIdeal ≠ ⊥ := by
      intro h0
      have : Q = P0 := PrimeSpectrum.ext h0
      rw [this] at hQ
      exact lt_irrefl _ hQ
    have h1 := h Q.asIdeal Q.isPrime hQ0
    rw [← GroundTheory.Arith.Abelian.Jacobian.coheight_eq_ringKrullDim_quotient] at h1
    have h2 : Order.coheight Q ≤ n := by exact_mod_cast h1
    exact add_le_add h2 le_rfl
  show Order.krullDim (PrimeSpectrum B) ≤ _
  rw [Order.krullDim_eq_iSup_coheight_of_nonempty]
  refine WithBot.coe_le_coe.mpr (iSup_le fun Q => ?_)
  have hle : P0 ≤ Q := by
    change (⊥ : Ideal B) ≤ Q.asIdeal
    exact bot_le
  exact (Order.coheight_anti hle).trans hco

theorem ringKrullDim_le_trdeg_add_one_int (t : ℕ) : ∀ (B : Type) [CommRing B] [IsDomain B]
    [Algebra ℤ B] [Algebra.FiniteType ℤ B], Function.Injective (algebraMap ℤ B) →
    trdeg ℤ B = t → ringKrullDim B ≤ (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro B _ _ _ _ hinj ht
  have hfin : trdeg ℤ B < ℵ₀ := by rw [ht]; exact Cardinal.natCast_lt_aleph0
  have key := ringKrullDim_le_add_one_of_quotient_le (B := B) (t : ℕ∞) (fun Q hQ hQ0 => by
    haveI := hQ
    haveI : Algebra.FiniteType ℤ (B ⧸ Q) :=
      .of_surjective (Ideal.Quotient.mkₐ ℤ Q) (Ideal.Quotient.mkₐ_surjective ℤ Q)
    by_cases hc : Function.Injective (algebraMap ℤ (B ⧸ Q))
    · have hlt := trdeg_lt_of_surjective_of_ker_ne_bot (Ideal.Quotient.mkₐ ℤ Q)
        (Ideal.Quotient.mkₐ_surjective ℤ Q)
        (fun h => hQ0 (by rw [← Ideal.mk_ker (I := Q)]; exact h)) hc hfin
      obtain ⟨t', ht'⟩ := Cardinal.lt_aleph0.mp (hlt.trans hfin)
      rw [ht, ht'] at hlt
      have hlt' : t' < t := by exact_mod_cast hlt
      refine (ih t' hlt' (B ⧸ Q) hc ht').trans ?_
      exact_mod_cast (show t' + 1 ≤ t by omega)
    · have hp0 : ringChar (B ⧸ Q) ≠ 0 := by
        intro h0
        have hc0 := ringChar.charP (B ⧸ Q)
        rw [h0] at hc0
        haveI : CharZero (B ⧸ Q) := (CharP.charP_zero_iff_charZero _).mp hc0
        apply hc
        have e : algebraMap ℤ (B ⧸ Q) = Int.castRingHom (B ⧸ Q) := RingHom.ext_int _ _
        rw [e]
        exact Int.cast_injective
      haveI : CharP (B ⧸ Q) (ringChar (B ⧸ Q)) := ringChar.charP _
      have hpp : (ringChar (B ⧸ Q)).Prime :=
        (CharP.char_is_prime_or_zero (B ⧸ Q) (ringChar (B ⧸ Q))).resolve_right hp0
      haveI : Fact (ringChar (B ⧸ Q)).Prime := ⟨hpp⟩
      letI := ZMod.algebra (B ⧸ Q) (ringChar (B ⧸ Q))
      haveI := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (B ⧸ Q))
        ((algebraMap (ZMod (ringChar (B ⧸ Q))) (B ⧸ Q)).comp (algebraMap ℤ (ZMod (ringChar (B ⧸ Q))))))
      haveI : Algebra.FiniteType (ZMod (ringChar (B ⧸ Q))) (B ⧸ Q) :=
        Algebra.FiniteType.of_restrictScalars_finiteType ℤ _ _
      have hle := trdeg_zmod_quotient_le hinj (ringChar (B ⧸ Q)) Q
      rw [ht] at hle
      obtain ⟨s, hs⟩ := Cardinal.lt_aleph0.mp (hle.trans_lt Cardinal.natCast_lt_aleph0)
      rw [hs] at hle
      have hst : s ≤ t := by exact_mod_cast hle
      rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg (ZMod (ringChar (B ⧸ Q))), hs,
        Cardinal.toENat_nat]
      exact_mod_cast hst)
  refine key.trans (le_of_eq ?_)
  push_cast
  rfl

theorem le_ringKrullDim_int (B : Type) [CommRing B] [IsDomain B] [Algebra.FiniteType ℤ B]
    (hinj : Function.Injective (algebraMap ℤ B)) (t : ℕ) (ht : trdeg ℤ B = t) :
    (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim B := by
  letI : Algebra B (ℚ ⊗[ℤ] B) := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors ℤ)
  have hM : M ≤ nonZeroDivisors B := by
    rintro _ ⟨n, hn, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    exact nonZeroDivisors.ne_zero hn (hinj (h.trans (map_zero _).symm))
  haveI : IsLocalization M (ℚ ⊗[ℤ] B) := IsLocalization.tensorRight _ _
  haveI : IsDomain (ℚ ⊗[ℤ] B) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM

  have hBL : Function.Injective (algebraMap B (ℚ ⊗[ℤ] B)) := IsLocalization.injective _ hM
  haveI : FaithfulSMul B (ℚ ⊗[ℤ] B) := (faithfulSMul_iff_algebraMap_injective _ _).2 hBL
  haveI : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  haveI : FaithfulSMul ℤ ℚ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℤ ℚ).injective_int
  haveI : FaithfulSMul ℚ (ℚ ⊗[ℤ] B) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap ℚ (ℚ ⊗[ℤ] B)).injective
  haveI := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap B (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ B)))
  haveI := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int (algebraMap ℤ (ℚ ⊗[ℤ] B))
    ((algebraMap ℚ (ℚ ⊗[ℤ] B)).comp (algebraMap ℤ ℚ)))
  haveI : Algebra.IsAlgebraic B (ℚ ⊗[ℤ] B) := IsLocalization.isAlgebraic _ M
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have h1 := trdeg_add_eq ℤ B (A := ℚ ⊗[ℤ] B)
  have h2 := trdeg_add_eq ℤ ℚ (A := ℚ ⊗[ℤ] B)
  rw [trdeg_eq_zero (R := B) (A := ℚ ⊗[ℤ] B), add_zero] at h1
  rw [trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add] at h2
  have htL : trdeg ℚ (ℚ ⊗[ℤ] B) = t := by rw [h2, ← h1, ht]

  obtain ⟨m, hm⟩ := Ideal.exists_maximal (ℚ ⊗[ℤ] B)
  have hmh : m.height = t := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field (K := ℚ) t htL m
  have hPh : (m.under B).height = t := (IsLocalization.height_under M m).trans hmh
  have hdisj : Disjoint (M : Set B) (m.under B) :=
    (IsLocalization.disjoint_under_iff M _ m).2 hm.ne_top
  have hnm : ¬ (m.under B).IsMaximal := by
    intro hPm
    letI := Ideal.Quotient.field (m.under B)
    haveI : IsJacobsonRing ℤ := isJacobsonRing_int
    haveI : Algebra.FiniteType ℤ (B ⧸ m.under B) :=
      .of_surjective (Ideal.Quotient.mkₐ ℤ _) (Ideal.Quotient.mkₐ_surjective ℤ _)
    haveI := finite_of_finite_type_of_isJacobsonRing ℤ (B ⧸ m.under B)
    haveI : Algebra.IsIntegral ℤ (B ⧸ m.under B) := Algebra.IsIntegral.of_finite ℤ _
    apply Int.not_isField
    refine isField_of_isIntegral_of_isField ?_ (Field.toIsField (B ⧸ m.under B))
    have e : algebraMap ℤ (B ⧸ m.under B) = (Ideal.Quotient.mk _).comp (algebraMap ℤ B) :=
      RingHom.ext_int _ _
    rw [e, injective_iff_map_eq_zero]
    intro n hn
    by_contra hn0
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at hn
    exact Set.disjoint_left.mp hdisj ⟨n, mem_nonZeroDivisors_of_ne_zero hn0, rfl⟩ hn
  obtain ⟨N, hN, hPN⟩ := (m.under B).exists_le_maximal (Ideal.IsPrime.ne_top inferInstance)
  have hlt : m.under B < N := lt_of_le_of_ne hPN (fun h => hnm (h ▸ hN))
  have hh := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hPh] at hh
  calc (((t + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (N.height : WithBot ℕ∞) := by
        exact_mod_cast hh
    _ ≤ ringKrullDim B := Ideal.height_le_ringKrullDim_of_isPrime

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LocalChangeOfVectorSpace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ chartLat)

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace SectionInjectivityEquivalence

theorem val_ne_zero {P : ArithVariety n} {f : MvPolynomial (Coord n) ℤ} (hf : f ∉ P.ideal) :
    val P f ≠ 0 := by
  rw [← funFieldEquiv_mkF, Ne, map_eq_zero_iff _ (funFieldEquiv P).injective]
  exact fun h ↦ hf ((P.mkF_eq_zero_iff f).mp h)

theorem sectionVal_ne_zero {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a)
    (he : e.num ∉ P.ideal) : sectionVal e ≠ 0 :=
  div_ne_zero (val_ne_zero he) (val_ne_zero e.den_not_mem)

theorem toFun_ne_zero {P : ArithVariety n} {a : ι → ℤ} (e : IntegralSection P a)
    (he : e.num ∉ P.ideal) : e.toFun ≠ 0 := by
  rw [toFun_eq_symm_sectionVal, Ne, map_eq_zero_iff _ (funFieldEquiv P).symm.injective]
  exact sectionVal_ne_zero e he

theorem supNormLE_cast {P : ArithVariety n} {A B : HermLine n} (h : A = B) (s : IntegralSection P A.deg)
    {C : ℝ} (hs : s.SupNormLE A C) : (s.cast (congrArg HermLine.deg h)).SupNormLE B C := by
  subst h
  exact hs

theorem mkF_div_chartPow_mem {P : ArithVariety n} {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ} (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    P.mkF f / P.chartPow c (fun k ↦ (δ k : ℤ)) ∈ P.chartRing c := by
  have h := P.chart_homogeneous c hc hf
  have hpow : P.chartPow c (fun k ↦ (δ k : ℤ)) = ∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k := by
    simp only [ArithVariety.chartPow, zpow_natCast]
  have hne : ∏ k, P.mkF (X ⟨k, c k⟩) ^ δ k ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ fun h0 ↦ hc k ((P.mkF_eq_zero_iff _).mp h0)
  rw [hpow, ← h, mul_div_cancel_left₀ _ hne]
  refine MvPolynomial.eval₂_mem (fun i _ ↦ intCast_mem _ _) fun v ↦ ?_
  exact Subring.subset_closure ⟨v, rfl⟩

theorem chartPow_add (P : ArithVariety n) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    (u v : ι → ℤ) : P.chartPow c (u + v) = P.chartPow c u * P.chartPow c v := by
  simp only [ArithVariety.chartPow, Pi.add_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  exact zpow_add₀ (fun h0 ↦ hc k ((P.mkF_eq_zero_iff _).mp h0)) _ _

theorem sectionVal_mem_chartLat {P : ArithVariety n} {b : ι → ℤ} (σ : IntegralSection P b) (τ : ℕ)
    (a : ι → ℤ) (hb : ∀ k, b k = (τ : ℤ) * a k) : sectionVal σ ∈ chartLat (genPt P) a τ := by
  intro c hc
  have hlive : P.IsLive c := fun k hk ↦ hc k (by
    show val P (X ⟨k, c k⟩) = 0
    rw [← funFieldEquiv_mkF, (P.mkF_eq_zero_iff _).mpr hk, map_zero])
  obtain ⟨d, ε, ⟨δ, hε, hδ⟩, hmem⟩ := σ.regular c hlive
  have hmk := SectionSmall.mkF_eq_of_mem σ hmem
  have hX : P.mkF (chartMonomial c d) = P.chartPow c (fun k ↦ (d k : ℤ)) := by
    simp only [chartMonomial, map_prod, map_pow, ArithVariety.chartPow, zpow_natCast]
  have hXne : P.chartPow c (fun k ↦ (d k : ℤ)) ≠ 0 := by
    unfold ArithVariety.chartPow
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ fun h1 ↦ hlive k ((P.mkF_eq_zero_iff _).mp h1)
  have hδ' : (fun k ↦ (δ k : ℤ)) = b + fun k ↦ (d k : ℤ) := funext fun k ↦ hδ k
  have key : σ.toFun / P.chartPow c b = P.mkF ε / P.chartPow c (fun k ↦ (δ k : ℤ)) := by
    rw [hδ', chartPow_add P hlive, hmk, hX, mul_div_mul_right _ _ hXne]
  have hm := mkF_div_chartPow_mem hlive hε
  rw [← key, ← funFieldEquiv_mem_chartRing_iff, funFieldEquiv_div_chartPow, funFieldEquiv_toFun] at hm
  have hb' : -b = fun k ↦ -((τ : ℤ) * a k) := funext fun k ↦ by rw [Pi.neg_apply, hb k]
  rw [hb'] at hm
  exact hm

theorem funFieldEquiv_aeval {P : ArithVariety n} (D : AddBlockData P) (F : MvPolynomial (Fin (D.m + 1)) ℤ) :
    funFieldEquiv P (aeval (AddBlockData.toObjects D).elt F) = aeval D.x F := by
  have hZ : ∀ (R : Type) [Ring R] [Algebra ℤ R], algebraMap ℤ R = Int.castRingHom R :=
    fun _ _ _ ↦ RingHom.ext_int _ _
  show funFieldEquiv P (eval₂ (algebraMap ℤ P.FunField) (fun j : Fin (D.m + 1) ↦ (funFieldEquiv P).symm (D.x j)) F) =
    eval₂ (algebraMap ℤ (FunField P)) D.x F
  rw [hZ, hZ]
  induction F using MvPolynomial.induction_on with
  | C r =>
    rw [eval₂_C, eval₂_C]
    exact map_intCast (funFieldEquiv P) r
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p j hp =>
    simp only [eval₂_mul, eval₂_X, map_mul, hp]
    exact congrArg _ (RingEquiv.apply_symm_apply _ _)

theorem localChange_of_vectorSpace (hA : GroundTheory.Heights₂.Heights.SectionInjectivity.Statement)
    (hS : GroundTheory.Heights₂.Heights.SmallSections.Statement) : SectionInjectivity.Statement := by
  intro ι _ _ n P M k q a C hkq ha e he0 heC D hD G Γ m
  have hsv : sectionVal e ≠ 0 := sectionVal_ne_zero e he0
  refine ⟨fun s₁ _ s₂ _ h ↦ mul_right_cancel₀ (pow_ne_zero _ hsv) h, fun s hs ↦ ?_⟩
  obtain ⟨F, hF, rfl, hbd⟩ := hs
  set N := twistPow M (q - k) a C with hN
  set D₁ := AddBlockData.toObjects D
  obtain ⟨sF, hsF⟩ := (hS ι n P D₁).1 m F hF
  have hsmall := (hS ι n P D₁).2 N hD.symm G.d G.g G.isFormSystem Γ.r Γ.f Γ.δ Γ.isHomogGenerators
    m F hF
  have hpts : D₁.extPoints = conePoints D.ext ℂ := AddBlockEq.addBlockEquiv_symm_conePoints D
  have hbd₁ : ∀ w ∈ D₁.extPoints,
      ‖eval₂ (Int.castRingHom ℂ) (D₁.newPart w) F‖ ≤ D₁.plusMetric N G.d G.g Γ.f Γ.δ w ^ m := by
    intro w hw
    rw [hpts] at hw
    exact hbd w hw
  set t := a * m with ht
  set L := ((M.pow (q - k)).mul (HermLine.standard n)).pow t with hL
  have hdeg : m • D₁.deg = L.deg := by
    show m • D.deg = _
    rw [hD, twistPow_deg]
    funext b
    simp only [hL, HermLine.pow, HermLine.mul, Pi.smul_apply, Pi.add_apply, nsmul_eq_mul, Pi.mul_apply,
      Pi.natCast_apply, ht]
    push_cast
    ring
  set sA := sF.cast hdeg
  have hsA : sA.SupNormLE L (-(t * C)) := by
    intro z hz c d' ε hform hzc
    have hmk : P.mkF ε = sF.toFun * P.mkF (chartMonomial c d') :=
      SectionSmall.mkF_eq_of_mem sF hform.2
    rw [hsF] at hmk
    have hb := (hsmall ε (chartMonomial c d') hmk).2 hbd₁ z hz
    have hμ := norm_pos_iff.mpr (GroundTheory.Heights₂.Heights.SectionInjectivity.evalCone_chartMonomial_ne_zero hzc d')
    have hLz := L.metric_pos z hz.1
    have hNm : N.metric z ^ m = Real.exp (-(t * C)) * L.metric z := by
      rw [hN, twistPow_metric, mul_pow, ← Real.exp_nat_mul, hL, hermLine_pow_metric, hermLine_pow_metric,
        ← pow_mul, ht]
      congr 2
      push_cast
      ring
    rw [div_le_iff₀ (by positivity)]
    calc _ ≤ _ := hb
      _ = _ := by rw [hNm]; ring
  set e' := e.cast (congrArg HermLine.deg (powDivStd_eq M k)) with he'_def
  have he' : e'.SupNormLE ((M.pow k).mul (HermLine.standard n).inv) C := supNormLE_cast (powDivStd_eq M k) e heC
  have he'0 : e'.toFun ≠ 0 := toFun_ne_zero e' he0
  obtain ⟨s', hs'val, hs'sup⟩ := (hA ι n P M k q hkq e' C he'0 he' t).1 sA hsA
  have h1 : funFieldEquiv P sA.toFun = aeval D.x F := by
    show funFieldEquiv P sF.toFun = _
    rw [hsF]
    exact funFieldEquiv_aeval D F
  have h2 : funFieldEquiv P e'.toFun = sectionVal e := funFieldEquiv_toFun e
  have hx : aeval D.x F * sectionVal e ^ t = sectionVal s' := by
    rw [← funFieldEquiv_toFun s', hs'val, map_mul, map_pow, h1, h2]
  rw [hx]
  refine ⟨sectionVal_mem_chartLat s' (a * q * m) M.deg fun b ↦ ?_, ?_⟩
  · show ((q * t) • M.deg) b = _
    simp only [Pi.smul_apply, nsmul_eq_mul, ht]
    push_cast
    ring
  · intro g f dg df _ _ _ hval z hz
    have hmk : P.mkF g = s'.toFun * P.mkF f := by
      apply (funFieldEquiv P).injective
      rw [map_mul, funFieldEquiv_mkF, funFieldEquiv_mkF, funFieldEquiv_toFun]
      exact hval
    have h := (SectionSmall.proof ι n P (M.pow (q * t)) s').1 0 hs'sup g f hmk z hz
    rw [Real.exp_zero, one_mul, hermLine_pow_metric] at h
    rwa [show q * t = a * q * m by rw [ht]; ring] at h

end SectionInjectivityEquivalence

theorem SectionInjectivity.equiv_of (hS : GroundTheory.Heights₂.Heights.SmallSections.Statement) :
    GroundTheory.Heights₂.Heights.SectionInjectivity.Statement ↔ SectionInjectivity.Statement :=
  ⟨fun hA ↦ SectionInjectivityEquivalence.localChange_of_vectorSpace hA hS, fun _ ↦ GroundTheory.Heights₂.Heights.SectionInjectivity.proof⟩

theorem SectionInjectivity.equiv : GroundTheory.Heights₂.Heights.SectionInjectivity.Statement ↔ SectionInjectivity.Statement :=
  SectionInjectivity.equiv_of (GroundTheory.Heights₂.Heights.SmallSections.proof GroundTheory.Heights₂.Heights.ChartFormsAlt.proof)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end

