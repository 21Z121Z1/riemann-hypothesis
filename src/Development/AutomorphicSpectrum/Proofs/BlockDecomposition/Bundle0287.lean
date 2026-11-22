import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0273
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0280
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0250
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0274
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0276
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0277
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemFBOfNear
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem keyL : ∀ {l : ℕ} [Fact l.Prime] (b : Formalism.Per6.BdRp l) (k : ℕ),
    ∃ (c : ℕ) (a : Wl l), (l : Formalism.Per6.BdRp l) ^ c * b - wB l a ∈ FB l k := by
  intro l _ b k
  have hξ := GroundTheory.PAdicHodge.IsPerfectoidField.ker_fontaineTheta_eq_span_kerThetaGenerator ℂ_[l] l
  set ξ := GroundTheory.PAdicHodge.IsPerfectoidField.kerThetaGenerator ℂ_[l] l with hξdef
  have hfg := GroundTheory.PAdicHodge.fg_ker_fontaineThetaInvertP hξ
  have hm : FB l k = Ideal.span {GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l ξ ^ k} := by
    rw [FB, ker_thB_eq, GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span hξ,
      Ideal.span_singleton_pow]
  have h' : Ideal.span {GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l ξ ^ k} =
      (RingHom.ker (fontaineThetaInvertP _ l) ^ k).map
        (GroundTheory.PAdicHodge.toBDeRhamPlus _ l) := by
    rw [GroundTheory.PAdicHodge.ker_fontaineThetaInvertP hξ, Ideal.span_singleton_pow, Ideal.map_span,
      Set.image_singleton, map_pow]
    rfl
  obtain ⟨a0, ha0⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (RingHom.ker (fontaineThetaInvertP _ l)) k b)
  have hz : b - GroundTheory.PAdicHodge.toBDeRhamPlus _ l a0 ∈ FB l k := by
    let I := RingHom.ker (fontaineThetaInvertP (↥(GroundTheory.PAdicHodge.normInteger ℂ_[l])) l)
    let b' : AdicCompletion I (Localization.Away (l : Wl l)) := b
    let c' : AdicCompletion I (Localization.Away (l : Wl l)) := algebraMap _ _ a0
    have e : (AdicCompletion.evalₐ I k) c' = Ideal.Quotient.mk _ a0 := by
      simp only [c']
      rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        AdicCompletion.evalₐ_of]
    have h1 : b' - c' ∈ RingHom.ker (AdicCompletion.evalₐ I k).toRingHom := by
      rw [RingHom.mem_ker]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub]
      rw [e, ha0, sub_self]
    rw [GroundTheory.PAdicHodge.ker_adicCompletion_evalₐ hfg k] at h1
    rw [hm, h']
    exact h1
  obtain ⟨⟨w, ⟨_, c, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers ((l : Wl l))) a0
  refine ⟨c, w, ?_⟩
  have e : (l : Formalism.Per6.BdRp l) ^ c * GroundTheory.PAdicHodge.toBDeRhamPlus _ l
      (IsLocalization.mk' _ w (⟨(l : Wl l) ^ c, c, rfl⟩ : Submonoid.powers (l : Wl l))) = wB l w := by
    have h2 := IsLocalization.mk'_spec (Localization.Away (l : Wl l)) w
      (⟨(l : Wl l) ^ c, c, rfl⟩ : Submonoid.powers (l : Wl l))
    have h3 := congrArg (GroundTheory.PAdicHodge.toBDeRhamPlus _ l) h2
    rw [map_mul] at h3
    have h4 : GroundTheory.PAdicHodge.toBDeRhamPlus _ l (algebraMap (Wl l) (Localization.Away (l : Wl l)) ((l : Wl l) ^ c)) =
        (l : Formalism.Per6.BdRp l) ^ c := by
      simp only [map_pow, map_natCast]
    simp only [] at h3
    rw [h4] at h3
    rw [mul_comm]
    exact h3
  rw [← e, ← mul_sub]
  exact Ideal.mul_mem_left _ _ hz

theorem normL : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)),
    ∀ s ∈ latS K', ‖thB l s‖ ≤ 1 := by
  intro l _ K' s hs
  have hle : latS K' ≤ (GroundTheory.PAdicHodge.normInteger ℂ_[l]).comap (thB l) := by
    refine (Subring.closure_le).2 ?_
    rintro z (⟨a, rfl⟩ | ⟨x, ⟨hx, hi⟩, rfl⟩)
    · change thB l (wB l a) ∈ GroundTheory.PAdicHodge.normInteger ℂ_[l]
      have e : thB l (wB l a) = _ :=
        GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus (K := ℂ_[l]) l a
      rw [e]
      exact Subtype.property _
    · change thB l (rB l x) ∈ GroundTheory.PAdicHodge.normInteger ℂ_[l]
      have e : thB l (rB l x) = ((x : Om l) : ℂ_[l]) := GroundTheory.PAdicHodge.thetaAlgHom_algClToBdR l x
      rw [e, GroundTheory.PAdicHodge.mem_normInteger, PadicComplex.norm_extends,
        ← GlobalTheory.isIntegral_padicInt_iff_norm_le_one]
      exact hi
  exact GroundTheory.PAdicHodge.mem_normInteger.1 (hle hs)

theorem galL : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) [Normal ℚ_[l] K']
    (g : GQ l), ∀ s ∈ latS K', actB g s ∈ latS K' := by
  intro l _ K' hn g s hs
  have hle : latS K' ≤ (latS K').comap (actB g) := by
    refine (Subring.closure_le).2 ?_
    rintro z (⟨a, rfl⟩ | ⟨x, ⟨hx, hi⟩, rfl⟩)
    · change actB g (wB l a) ∈ latS K'
      have e : actB g (wB l a) = wB l (Formalism.Per6.toBot g • a) :=
        GroundTheory.PAdicHodge.gal_smul_wittToBDeRhamPlus (Formalism.Per6.toBot g) a
      rw [e]
      exact wB_mem_latS K' _
    · change actB g (rB l x) ∈ latS K'
      have e : actB g (rB l x) = rB l (g x) :=
        GroundTheory.PAdicHodge.gal_smul_algClToBdR (Formalism.Per6.toBot g) x
      rw [e]
      refine rB_mem_latS K' ?_ (hi.map ((g : Om l →ₐ[ℚ_[l]] Om l).restrictScalars ℤ_[l]))
      exact (IntermediateField.normal_iff_forall_map_le.1 hn) (g : Om l →ₐ[ℚ_[l]] Om l) ⟨x, hx, rfl⟩
  exact hle hs

theorem xpowL : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) (x : Om l),
    x ∈ K' → ‖((x : Om l) : ℂ_[l])‖ < 1 →
    ∃ (N : ℕ) (y : Om l), 0 < N ∧ y ∈ K' ∧ IsIntegral ℤ_[l] y ∧ x ^ N = (l : Om l) * y := by
  intro l _ K' x hx h1
  rw [PadicComplex.norm_extends] at h1
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hlp : 0 < ‖(l : Om l)‖ := norm_pos_iff.2 hl0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hlp h1
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · exfalso
      have hle : ‖(l : Om l)‖ ≤ 1 := by
        rw [← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends]
        exact Padic.norm_p_lt_one.le
      rw [pow_zero] at hN
      exact absurd hN (not_lt.2 hle)
    · exact h
  refine ⟨N, x ^ N / (l : Om l), hNpos, ?_, ?_, ?_⟩
  · refine div_mem (pow_mem hx N) ?_
    exact natCast_mem K' l
  · rw [GlobalTheory.isIntegral_padicInt_iff_norm_le_one, norm_div, norm_pow]
    exact (div_le_one hlp).2 hN.le
  · field_simp

end GlobalTheory.CompanionTheory.LTPer

namespace GlobalTheory.CompanionTheory.LTPer

theorem mem_FB_of_near {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)) (T : Finset (Formalism.Per6.BdRp l))
    (hS : ∀ s ∈ S, ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t)) (k : ℕ)
    (x : Formalism.Per6.BdRp l) (h : ∀ m : ℕ, ∃ s ∈ S, x - (l : Formalism.Per6.BdRp l) ^ m * s ∈ FB l k) :
    x ∈ FB l k := by
  choose cf af hcf using fun t : Formalism.Per6.BdRp l => keyL t k
  set c := T.sup cf with hc
  have hT : ∀ t ∈ T, (l : Formalism.Per6.BdRp l) ^ c * t -
      wB l ((l : Wl l) ^ (c - cf t) * af t) ∈ FB l k := by
    intro t ht
    have hle : cf t ≤ c := Finset.le_sup ht
    have e : (l : Formalism.Per6.BdRp l) ^ c * t - wB l ((l : Wl l) ^ (c - cf t) * af t) =
        (l : Formalism.Per6.BdRp l) ^ (c - cf t) * ((l : Formalism.Per6.BdRp l) ^ cf t * t - wB l (af t)) := by
      rw [map_mul, map_pow, map_natCast, mul_sub, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [e]
    exact Ideal.mul_mem_left _ _ (hcf t)
  have hSa : ∀ s ∈ S, ∃ a : Wl l, (l : Formalism.Per6.BdRp l) ^ c * s - wB l a ∈ FB l k := by
    intro s hs
    obtain ⟨a, rfl⟩ := hS s hs
    refine ⟨∑ t ∈ T, (l : Wl l) ^ (c - cf t) * af t * a t, ?_⟩
    rw [map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun t ht => ?_
    have e : (l : Formalism.Per6.BdRp l) ^ c * (t * wB l (a t)) -
        wB l ((l : Wl l) ^ (c - cf t) * af t * a t) =
        ((l : Formalism.Per6.BdRp l) ^ c * t - wB l ((l : Wl l) ^ (c - cf t) * af t)) * wB l (a t) := by
      rw [map_mul (wB l) _ (a t)]; ring
    rw [e]
    exact Ideal.mul_mem_right _ _ (hT t ht)
  have hm : FB l k = IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l) ^ k := by rw [FB, ker_thB_eq]
  rw [hm]
  refine GroundTheory.PAdicHodge.IsPerfectoidField.mem_maximalIdeal_pow_of_forall_sub_mem (K := ℂ_[l]) (p := l)
    fun M => ?_
  obtain ⟨s, hs, hx⟩ := h (M + c)
  obtain ⟨a, ha⟩ := hSa s hs
  refine ⟨a, ?_⟩
  rw [← hm]
  have e : x - (l : Formalism.Per6.BdRp l) ^ M * GroundTheory.PAdicHodge.wittToBDeRhamPlus _ l a =
      (x - (l : Formalism.Per6.BdRp l) ^ (M + c) * s) +
        (l : Formalism.Per6.BdRp l) ^ M * ((l : Formalism.Per6.BdRp l) ^ c * s - wB l a) := by
    rw [pow_add, wB]; ring
  rw [e]
  exact add_mem hx (Ideal.mul_mem_left _ _ ha)

theorem FB_sep {l : ℕ} [Fact l.Prime] (x : Formalism.Per6.BdRp l) (h : ∀ k, x ∈ FB l k) : x = 0 := by
  refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l)) inferInstance x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← ker_thB_eq]
  exact h n

theorem FB_complete {l : ℕ} [Fact l.Prime] (x : ℕ → Formalism.Per6.BdRp l)
    (h : ∀ k, x (k + 1) - x k ∈ FB l k) : ∃ t, ∀ k, t - x k ∈ FB l k := by
  have hc : IsPrecomplete (IsLocalRing.maximalIdeal (Formalism.Per6.BdRp l)) (Formalism.Per6.BdRp l) := inferInstance
  have hstep : ∀ m n, m ≤ n → x n - x m ∈ FB l m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : x (n + 1) - x n ∈ FB l m := Ideal.pow_le_pow_right hmn (h n)
      have := add_mem h1 ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨t, ht⟩ := hc.prec (f := x) (fun {m n} hmn => by
    rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← ker_thB_eq]
    exact hstep m n hmn)
  refine ⟨t, fun k => ?_⟩
  have := ht k
  rw [SModEq.comm, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← ker_thB_eq] at this
  exact this

theorem lattice_main : ∀ {l : ℕ} [Fact l.Prime] (K' : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] K'] [Normal ℚ_[l] K'],
    ∃ S : Subring (Formalism.Per6.BdRp l), (∀ a, wB l a ∈ S) ∧
      (∀ x ∈ K', IsIntegral ℤ_[l] x → rB l x ∈ S) ∧
      (∀ (g : GQ l), ∀ s ∈ S, actB g s ∈ S) ∧ (∀ s ∈ S, ‖thB l s‖ ≤ 1) ∧
      ∀ x ∈ K', IsIntegral ℤ_[l] x → x ≠ 0 → ‖((x : Om l) : ℂ_[l])‖ < 1 →
        PerEnv S (FB l) (rB l x) ∧ ∀ u : Tl l, u ≠ 0 → ∀ s ∈ S, tch l u ≠ rB l x * s := by
  intro l _ K' _ _
  refine ⟨latS K', wB_mem_latS K', fun x hx hi => rB_mem_latS K' hx hi, galL K', normL K', ?_⟩
  intro x hxK hxi hx0 hx1
  obtain ⟨T, hT, hS⟩ := latS_finite_span K'
  obtain ⟨N, y, hN, hyK, hyi, hxy⟩ := xpowL K' x hxK hx1
  have hϖ : rB l x ∈ latS K' := rB_mem_latS K' hxK hxi
  have hy : rB l y ∈ latS K' := rB_mem_latS K' hyK hyi
  have hϖy : rB l x ^ N = (l : Formalism.Per6.BdRp l) * rB l y := by
    rw [← map_pow, hxy, map_mul, map_natCast]
  have hnear : ∀ k x', (∀ m : ℕ, ∃ s ∈ latS K', x' - (l : Formalism.Per6.BdRp l) ^ m * s ∈ FB l k) → x' ∈ FB l k :=
    fun k x' h => mem_FB_of_near (latS K') T hS k x' h
  have hsep : ∀ x' : Formalism.Per6.BdRp l, (∀ m : ℕ, ∃ s ∈ latS K', x' = (l : Formalism.Per6.BdRp l) ^ m * s) → x' = 0 := by
    intro x' h
    refine FB_sep x' fun k => hnear k x' fun m => ?_
    obtain ⟨s, hs, e⟩ := h m
    exact ⟨s, hs, by rw [← e, sub_self]; exact zero_mem _⟩
  refine ⟨⟨by simp [FB], fun k => Ideal.pow_le_pow_right (Nat.le_succ k),
    fun a b => by rw [FB, FB, FB, pow_add], FB_sep, FB_complete,
    (IsUnit.map (rB l) (isUnit_iff_ne_zero.2 hx0)), hϖ, ?_, ?_⟩,
    tch_ne_mul_of_pow_eq (latS K') T (wB_mem_latS K') hT hS (rB l x) (rB l y) N hy hϖy⟩
  · exact PowerSeriesSum.sum_with_tails (wB l) l (latS K') T (wB_mem_latS K') hT hS hsep (rB l x) (rB l y) N hN hϖ hy hϖy
  · intro k x' _ h
    refine hnear k x' fun m => ?_
    obtain ⟨s, hs, e⟩ := h (N * m)
    refine ⟨rB l y ^ m * s, mul_mem (pow_mem hy m) hs, ?_⟩
    have e2 : rB l x ^ (N * m) * s = (l : Formalism.Per6.BdRp l) ^ m * (rB l y ^ m * s) := by
      rw [pow_mul, hϖy, mul_pow, mul_assoc]
    rwa [e2] at e

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalBasisBaseChangeStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_basis_base_change : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (K : Type) [Field K] [Algebra F K], ∃ e : Fin M → Fin M → K ⊗[F] E, (∀ i j, i ≠ j → Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e j) = 0) ∧ (∀ i, IsUnit (Formalism.UG.hform (sigR K σ) (JR K J) (e i) (e i))) ∧ IsUnit (Matrix.of e).det := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.exists_rational_orth | exact GlobalTheory.CompanionTheory.SaGen.exists_rational_orth | (intros; apply GlobalTheory.CompanionTheory.SaGen.exists_rational_orth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodProductFiltrationLevelsStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_product_filtration_levels : ∀ {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (t : ι → Formalism.Per6.BdRp l) (i₀ : ι), i₀ ∈ s →
    ∀ u : (Formalism.Per6.BdRp l)ˣ, ∏ μ ∈ s, t μ = GroundTheory.PAdicHodge.tBdR l * (u : Formalism.Per6.BdRp l) →
      thB l (t i₀) = 0 →
      ∀ μ ∈ s, (μ = i₀ → t μ ∉ FB l 2) ∧ (μ ≠ i₀ → t μ ∉ FB l 1) := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.prod_eq_t_mul_unit_count | exact GlobalTheory.CompanionTheory.LTPer.prod_eq_t_mul_unit_count | (intros; apply GlobalTheory.CompanionTheory.LTPer.prod_eq_t_mul_unit_count <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodRingBaseChangeFromUniversal
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.AcrMod

theorem factor_factor {R : Type} [CommRing R] {I J K : Ideal R} (h1 : I ≤ J) (h2 : J ≤ K) (y : R ⧸ I) :
    Ideal.Quotient.factor h2 (Ideal.Quotient.factor h1 y) = Ideal.Quotient.factor (h1.trans h2) y := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

theorem fil_extend {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    (δ : DividedPowers J) (δ' : DividedPowers J') (φ : B →+* B') (hJ : J' = J.map φ)
    (h : IsDPMorphism δ δ' φ) (r : ℕ) : fil δ' r = (fil δ r).map φ := by
  subst hJ
  exact (GlobalTheory.CompanionTheory.PDMap.extended_dividedPowers δ φ δ' h).1 r

theorem pow_mem_span {R : Type} [CommRing R] {I : Ideal R} (δ : DividedPowers I) {p : ℕ} (hp : p ≠ 0)
    {x : R} (hx : x ∈ I) : x ^ p ∈ Ideal.span {(p : R)} := by
  rw [← δ.factorial_mul_dpow_eq_pow hx]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  rw [Nat.factorial_succ, Nat.cast_mul, mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

variable {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ)

theorem l_mem_pfil : (l : A.Acr n) ∈ A.PFil n :=
  Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)

theorem sharp_zero : A.sharp 0 = 0 := by
  change A.th (WittVector.teichmuller l 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

theorem uToPQ_th (x : A.W) : A.uToPQ n (A.th x) = Ideal.Quotient.mk _ (A.toAcr n x) := by
  rw [uToPQ, RingHom.comp_apply, uToQ_th, Ideal.Quotient.factor_mk]

theorem exists_pi : ∃ π : A.A →+* A.Acr n ⧸ A.PFil n,
    (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧
      π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi}) := by
  let g : A.W →+* A.Acr n ⧸ A.PFil n := (Ideal.Quotient.mk _).comp (A.toAcr n)
  let π : A.A →+* A.Acr n ⧸ A.PFil n :=
    (WittVector.constantCoeff : A.W →+* A.A).liftOfSurjective A.constantCoeff_surjective ⟨g, fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ((A.mem_span_l_iff x).2 hx)
      rw [RingHom.mem_ker, map_mul, RingHom.comp_apply (Ideal.Quotient.mk _) (A.toAcr n) (l : A.W), map_natCast,
        Ideal.Quotient.eq_zero_iff_mem.2 (l_mem_pfil A n), mul_zero]⟩
  have hπ : ∀ x : A.W, π (x.coeff 0) = g x := fun x => RingHom.liftOfSurjective_comp_apply _ _ _ x
  have ht : ∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a)) := fun a => by
    have := hπ (WittVector.teichmuller l a)
    rwa [WittVector.teichmuller_coeff_zero] at this
  have hs : ∀ a, π a = A.uToPQ n (A.sharp a) := fun a => by
    rw [ht]
    exact (uToPQ_th A n _).symm
  refine ⟨π, ht, fun y => ?_, ?_, fun hn => ?_⟩
  · obtain ⟨u, rfl⟩ := (RL.uToQ A n).2.2.1 y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
    exact ⟨x.coeff 0, (hπ x).trans (uToPQ_th A n x).symm⟩
  · rw [hs, sharp_pi, map_natCast, ← map_natCast (Ideal.Quotient.mk (A.PFil n))]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (l_mem_pfil A n)
  · ext a
    have h := (RL.sharp_cong A).2.1 a 0
    rw [sharp_zero, sub_zero, sub_zero] at h
    rw [RingHom.mem_ker, hs, ← RingHom.mem_ker, (RL.uToQ A n).2.2.2 hn, h]

theorem fil_eq_map (r : ℕ) : A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n) := by
  refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.2 (mapAcr_fil A.fromBase n r))
  rw [PAlg.Fil, Ideal.span_le]
  rintro _ ⟨k, hk, rfl⟩
  rw [← mapAcr_dxi A.fromBase n k]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨k, hk, rfl⟩)

theorem pfil_eq_map : A.PFil n = ((base l).PFil n).map (mapAcr A.fromBase n) := by
  rw [PFil, PFil, Ideal.map_sup, ← fil_eq_map, Ideal.map_span, Set.image_singleton, map_natCast]

theorem jj_eq_map (k : Bool) : JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n) := by
  cases k
  · exact fil_eq_map A n 1
  · exact pfil_eq_map A n

theorem fil_mono {r s : ℕ} (h : r ≤ s) : A.Fil n s ≤ A.Fil n r := by
  refine Ideal.span_mono ?_
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨k, h.trans hk, rfl⟩

theorem fil_pdFil (r : ℕ) : fil (A.pdFil n) r = A.Fil n r := by
  refine le_antisymm ?_ ?_
  · have hprod : ∀ L : List (ℕ × A.Acr n), (∀ p ∈ L, p.2 ∈ A.Fil n 1) →
        (L.map fun p => (A.pdFil n).dpow p.1 p.2).prod ∈ A.Fil n (L.map Prod.fst).sum := by
      intro L
      induction L with
      | nil =>
        intro _
        simp only [List.map_nil, List.prod_nil, List.sum_nil]
        rw [(RL.filtration_multiplicative A).2.2.2.2.2.2.1 n]
        trivial
      | cons p L ih =>
        intro hL
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        exact (RL.filtration_multiplicative A).2.2.2.2.2.2.2 n _ _ (Ideal.mul_mem_mul
          (A.dpow_mem_fil n p.1 (hL p (by simp))) (ih fun q hq => hL q (by simp [hq])))
    refine Ideal.span_le.2 ?_
    rintro _ ⟨L, h1, h2, rfl⟩
    exact fil_mono A n h2 (hprod L h1)
  · rw [PAlg.Fil, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [← A.dpow_dxi n k]
    have h1 : A.dxi n 1 ∈ A.Fil n 1 := Ideal.subset_span ⟨1, le_rfl, rfl⟩
    exact GlobalTheory.CompanionTheory.PDMap.fil_anti (A.pdFil n) hk (GlobalTheory.CompanionTheory.PDMap.dpow_mem_fil (A.pdFil n) h1 k)

theorem pfil_pow (x : A.Acr n) (hx : x ∈ A.PFil n) : IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)} := by
  have h := pow_mem_span (A.pdPFil n) (Fact.out : l.Prime).ne_zero hx
  refine ⟨?_, h⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  exact ⟨l * n, by rw [pow_mul, ← hc, mul_pow, A.pow_l_acr n, mul_zero]⟩

theorem uJ_facts (k : Bool) (hn : n ≠ 0) :
    Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨u, hu⟩ := (RL.uToQ A n).1 (Ideal.Quotient.mk _ z)
    refine ⟨u, ?_⟩
    rw [uJ, RingHom.comp_apply, hu, Ideal.Quotient.factor_mk]
  · have e : A.uToPQ n x = Ideal.Quotient.factor (le_pfil k A n) (uJ k A n x) := by
      rw [uJ, RingHom.comp_apply, factor_factor]
      rfl
    have h0 : x ∈ RingHom.ker (A.uToPQ n) := by
      rw [RingHom.mem_ker, e, RingHom.mem_ker.1 hx, map_zero]
    rw [(RL.uToQ A n).2.2.2 hn] at h0
    exact (Ideal.span_singleton_le_iff_mem _).2 (R.mem_jacobson_of_complete (l : A.U)) h0

theorem acr_modp : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∃ π : A.A →+* A.Acr n ⧸ A.PFil n, (∀ a, π a = Ideal.Quotient.mk _ (A.toAcr n (WittVector.teichmuller l a))) ∧ Function.Surjective π ∧ π A.pi = 0 ∧ (n ≠ 0 → RingHom.ker π = Ideal.span {A.pi})) ∧ (∀ r, A.Fil n r = ((base l).Fil n r).map (mapAcr A.fromBase n)) ∧ (∀ k, JJ k A n = (JJ k (base l) n).map (mapAcr A.fromBase n)) ∧ (∀ r, fil (A.pdFil n) r = A.Fil n r) ∧ (∀ k r, fil (DD k A n) r = (fil (DD k (base l) n) r).map (mapAcr A.fromBase n)) ∧ (∀ x ∈ A.PFil n, IsNilpotent x ∧ x ^ l ∈ Ideal.span {(l : A.Acr n)}) ∧ ∀ k, n ≠ 0 → Function.Surjective (uJ k A n) ∧ RingHom.ker (uJ k A n) ≤ (⊥ : Ideal A.U).jacobson := by
  intro l _ A n
  exact ⟨exists_pi A n, fil_eq_map A n, jj_eq_map A n, fil_pdFil A n,
    fun k r => fil_extend _ _ _ (jj_eq_map A n k) (dd_map k A.fromBase n) r,
    pfil_pow A n, fun k hn => uJ_facts A n k hn⟩

end GlobalTheory.CompanionTheory.AcrMod
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PlacesIdempotentMulAbsorbStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.places_idempotent_mul_absorb : ∀ {F : Type} [Field F] [NumberField F] {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {a b : AF F}, IsPlacesIdem A₁ A₂ a → IsPlacesIdem B₁ B₂ b → A₁ ⊆ B₁ → A₂ ⊆ B₂ → b * a = a := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.idem_mul_eq_of_subset | exact GlobalTheory.CompanionTheory.SaGen.idem_mul_eq_of_subset | (intros; apply GlobalTheory.CompanionTheory.SaGen.idem_mul_eq_of_subset <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeCriterionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_prime_criterion : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme) (V : X.Opens) (hV : IsAffineOpen V) (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ q : Ideal Γ(Z, U), q.IsPrime → f ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) → (∀ c : Γ(Z, U), ∃ b t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ ∃ v : Γ(Z, U), v ∉ q ∧ v * (algebraMap Γ(X, V) Γ(Z, U) t * c) = v * algebraMap Γ(X, V) Γ(Z, U) b) ∧ (∀ b : Γ(X, V), (∃ v : Γ(Z, U), v ∉ q ∧ v * algebraMap Γ(X, V) Γ(Z, U) b = 0) → ∃ t : Γ(X, V), t ∉ q.comap (algebraMap Γ(X, V) Γ(Z, U)) ∧ t * b ∈ J.ideal ⟨V, hV⟩) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Krull.stalk_over_isoLocus | exact GlobalTheory.CompanionTheory.GE.Krull.stalk_over_isoLocus | (intros; apply GlobalTheory.CompanionTheory.GE.Krull.stalk_over_isoLocus <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalPrimeExistsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_prime_exists : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) {R : Type} [CommRing R] [Algebra Γ(X, V) R] (f : Γ(X, V)), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ p : Ideal R, p.IsPrime → (J.ideal ⟨V, hV⟩).map (algebraMap Γ(X, V) R) ≤ p → algebraMap Γ(X, V) R f ∉ p → ∃ (U : Z.Opens) (_ : IsAffineOpen U) (h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V), letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∃ Q₀ Q₁ : Ideal (R ⊗[Γ(X, V)] Γ(Z, U)), Q₀.IsPrime ∧ Q₁.IsPrime ∧ Q₀ ≤ Q₁ ∧ Q₀.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U)) = p ∧ (Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[Γ(X, V)] Γ(Z, U))).IsMaximal := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_chart_primes_of_isProper | exact GlobalTheory.CompanionTheory.GE.exists_chart_primes_of_isProper | (intros; apply GlobalTheory.CompanionTheory.GE.exists_chart_primes_of_isProper <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperPushforwardCoherentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_pushforward_coherent : ∀ {X Z : Scheme.{0}} [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → ∀ {G : Z.Modules}, IsCoherent G → IsCoherent ((Scheme.Modules.pushforward φ).obj G) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper | exact GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper | (intros; apply GlobalTheory.CompanionTheory.GE.PushCoh.isCoherent_pushforward_of_isProper <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperSupportPullbackSystemStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_support_pullback_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsLocallyNoetherian X] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → PropSupp A (pullSys I φ E S 0) := by
  first | exact @GlobalTheory.CompanionTheory.GE.PullSupp.propSupp_pullSys | exact GlobalTheory.CompanionTheory.GE.PullSupp.propSupp_pullSys | (intros; apply GlobalTheory.CompanionTheory.GE.PullSupp.propSupp_pullSys <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PushforwardClosedSystemUnseenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushforward_closed_system_auxiliary : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] {X Z : Scheme.{0}} [X.Over (Spec (.of A))] [Z.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (φ : Z ⟶ X), IsProper φ → φ ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ {E : X.Modules} (B : Subobject ((Scheme.Modules.pullback φ).obj E)), PropSupp A B → PropSupp A (adjKer φ B) := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer | exact GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer | (intros; apply GlobalTheory.CompanionTheory.GE.KerSupp.propSupp_adjKer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionAnisotropicTraceStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_anisotropic_trace : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 →
  (∀ x : Q d β K, qn x = 0 → x = 0) → ∀ b : Q d β K, qn b = 1 → b.re ^ 2 ≠ 1 →
  ∀ r : K, r ^ 2 ≠ (2 * b.re) ^ 2 - 4 := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.anis_trace_sq_sub_four_ne_sq | exact GlobalTheory.CompanionTheory.PlaneSA.anis_trace_sq_sub_four_ne_sq | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.anis_trace_sq_sub_four_ne_sq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuaternionClassNumberFiniteStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_class_number_finite : ∀ {F : Type} [Field F] [NumberField F] (d β : F), (∀ x : Q d β F, qn x = 0 → x = 0) →
  ∃ C : Set (Q d β (AF F))ˣ, IsCompact C ∧ ∀ y : (Q d β (AF F))ˣ, ∃ c ∈ C, ∃ δ : (Q d β F)ˣ, ∃ z : (AF F)ˣ,
    y = c * Units.map (rat (R := AF F) : Q d β F →+* Q d β (AF F)).toMonoidHom δ *
      Units.map (algebraMap (AF F) (Q d β (AF F))).toMonoidHom z := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.Compact.exists_isCompact_units | exact GlobalTheory.CompanionTheory.PlaneSA.Compact.exists_isCompact_units | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.Compact.exists_isCompact_units <;> assumption)
end

