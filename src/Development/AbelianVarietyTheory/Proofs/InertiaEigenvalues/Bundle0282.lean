import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0265
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitCocycleOfCompatibleModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Filter Topology Pointwise

namespace GlobalTheory.LimCocycle

theorem eventually_smul_mem {LL W : Type} [Field LL] [TopologicalSpace LL] [AddCommGroup W] [Module LL W]
    [TopologicalSpace W] [ContinuousSMul LL W] (c : ℕ → LL) (hc : Tendsto c atTop (𝓝 0))
    {K : Set W} (hK : IsCompact K) {U : Set W} (hU : U ∈ 𝓝 (0 : W)) :
    ∀ᶠ m in atTop, ∀ y ∈ K, c m • y ∈ U := by
  have h : ∀ᶠ a in 𝓝 (0 : LL), ∀ y ∈ K, a • y ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun y _ => ?_)
    have := (continuous_fst.smul continuous_snd : Continuous fun p : LL × W => p.1 • p.2).tendsto ((0 : LL), y)
    exact this.eventually_mem (by simpa using hU)
  exact hc.eventually h

theorem isCompact_of_fg {O LL V : Type} [CommRing O] [Field LL] [Algebra O LL] [TopologicalSpace LL]
    [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousSMul LL V]
    (hc : IsCompact (Set.range (algebraMap O LL))) (T : Submodule O V) (hT : T.FG) :
    IsCompact (T : Set V) := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hT
  have heq : (T : Set V) = (fun c : Fin n → LL => ∑ i, c i • s i) ''
      (Set.univ.pi fun _ => Set.range (algebraMap O LL)) := by
    ext x
    constructor
    · intro hx
      rw [SetLike.mem_coe, ← hs] at hx
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
      refine ⟨fun i => algebraMap O LL (a i), fun i _ => ⟨a i, rfl⟩, ?_⟩
      simp only [algebraMap_smul]
      exact ha
    · rintro ⟨c, hc', rfl⟩
      have : ∀ i, ∃ a : O, algebraMap O LL a = c i := fun i => hc' i (Set.mem_univ i)
      choose a ha using this
      rw [SetLike.mem_coe, ← hs]
      have : (∑ i, c i • s i) = ∑ i, a i • s i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← ha i, algebraMap_smul]
      show ∑ i, c i • s i ∈ _
      rw [this]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  rw [heq]
  exact (isCompact_univ_pi fun _ => hc).image
    (continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const)

end GlobalTheory.LimCocycle

namespace GlobalTheory.LimCocycle

theorem limit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (hI : ∀ n : ℕ, StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) (w : ℕ → ↥(GK K) → ↥LA.T), (∀ n, (fun g => (Submodule.Quotient.mk (w n g) : ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))) ∈ quotientCocycles LA _ (hI n)) → (∀ n g, w (n + 1) g - w n g ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) → ∃ d ∈ latticeCocycles LA, ∀ n g, ∃ t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T), d g = (w n g : A.V) + (t : A.V) := by
  intro l _ K LL _ _ _ O _ _ hG A LA ϖ hϖ hI w hw hstep
  have hcO : IsCompact (Set.range (algebraMap O LL)) := (GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hG).2.1
  obtain ⟨⟨hD, hDVR, hFr⟩, hfin, hmod, htop, hopen⟩ := hG
  haveI := hD
  haveI := hDVR
  haveI := hFr
  haveI : FiniteDimensional ℚ_[l] LL := hfin
  haveI := hmod
  haveI := htop
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  haveI : ContinuousSMul LL A.V := IsModuleTopology.toContinuousSMul LL A.V
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  haveI : T2Space LL := by
    let e := (Module.finBasis ℚ_[l] LL).equivFun
    exact T2Space.of_injective_continuous e.injective (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
  haveI : T2Space A.V := by
    let e := (Module.finBasis LL A.V).equivFun
    exact T2Space.of_injective_continuous e.injective (IsModuleTopology.continuous_of_linearMap e.toLinearMap)

  have hlpr : l.Prime := Fact.out
  let c : ℕ → LL := fun m => algebraMap O LL (((l : ℕ) : O) ^ m)
  have hc : Tendsto c atTop (𝓝 0) := by
    have hcont : Continuous (algebraMap ℚ_[l] LL) := by
      have h : (algebraMap ℚ_[l] LL : ℚ_[l] → LL) = fun a => a • (1 : LL) :=
        funext Algebra.algebraMap_eq_smul_one
      rw [h]
      exact continuous_id.smul continuous_const
    have h1 := (hcont.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one (Padic.norm_p_lt_one (p := l)))
    rw [map_zero] at h1
    refine h1.congr (fun m => ?_)
    simp [c, Function.comp, map_pow, map_natCast]

  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap O LL) h
    rw [map_natCast, map_zero, ← map_natCast (algebraMap ℚ_[l] LL),
      map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective, Nat.cast_eq_zero] at h2
    exact hlpr.ne_zero h2
  have hlnu : ¬ IsUnit ((l : ℕ) : O) := by
    intro hu
    obtain ⟨a, ha⟩ := hu.exists_right_inv
    have hU : ({1}ᶜ : Set LL) ∈ 𝓝 (0 : LL) := isOpen_compl_singleton.mem_nhds (by simp)
    obtain ⟨m, hm⟩ := (eventually_smul_mem c hc hcO hU).exists
    apply hm (algebraMap O LL (a ^ m)) ⟨_, rfl⟩
    simp only [c, smul_eq_mul, ← map_mul, ← mul_pow, ha, one_pow, map_one, Set.mem_singleton_iff]
  obtain ⟨v, u, hlu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ

  let Q : ℕ → Submodule O A.V := fun n => ϖ ^ n • LA.T
  have hQT : ∀ n, Q n ≤ LA.T := by
    intro n x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact LA.T.smul_mem _ hy
  have hQmono : ∀ m n, m ≤ n → Q n ≤ Q m := by
    intro m n hmn x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨ϖ ^ (n - m) • y, LA.T.smul_mem _ hy, ?_⟩
    rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hmn]
  have hmem : ∀ n (t : ↥LA.T), t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) ↔ (t : A.V) ∈ Q n := by
    intro n t
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨b, -, hb⟩
      exact ⟨b, b.2, by rw [← hb]; rfl⟩
    · rintro ⟨b, hbT, hb⟩
      exact ⟨⟨b, hbT⟩, trivial, Subtype.ext hb⟩
  have hTc : IsCompact (LA.T : Set A.V) := isCompact_of_fg hcO LA.T LA.fg
  have hQc : ∀ n, IsCompact (Q n : Set A.V) := by
    intro n
    have h : (Q n : Set A.V) = (fun x => algebraMap O LL (ϖ ^ n) • x) '' (LA.T : Set A.V) := by
      simp only [Q, Submodule.coe_pointwise_smul, algebraMap_smul]
      rfl
    rw [h]
    exact hTc.image (continuous_const_smul _)
  have hQρ : ∀ n g, ∀ x ∈ Q n, A.ρ g x ∈ Q n := by
    intro n g x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨A.ρ g y, LA.stable g y hy, ?_⟩
    rw [LinearMap.map_smul_of_tower]

  have hshrink : ∀ U ∈ 𝓝 (0 : A.V), ∃ N, ∀ x ∈ Q N, x ∈ U := by
    intro U hU
    obtain ⟨M, hM⟩ := (eventually_smul_mem c hc hTc hU).exists
    refine ⟨v * M, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    have hpow : ϖ ^ (v * M) = ((l : ℕ) : O) ^ M * (↑u⁻¹ : O) ^ M := by
      rw [← mul_pow, hlu, pow_mul, mul_comm (↑u : O), mul_assoc, Units.mul_inv, mul_one]
    have h := hM (((↑u⁻¹ : O) ^ M) • y) (LA.T.smul_mem _ hy)
    rw [hpow, mul_smul]
    simpa only [c, algebraMap_smul] using h
  have hsep : ∀ x : A.V, (∀ n, x ∈ Q n) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨N, hN⟩ := hshrink {x}ᶜ (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    exact hN x (hx N) rfl

  have hlim : ∀ g, ∃ x : A.V, ∀ n, x - (w n g : A.V) ∈ Q n := by
    intro g
    let C : ℕ → Set A.V := fun n => (fun x => x - (w n g : A.V)) ⁻¹' (Q n : Set A.V)
    have hne := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C
      (fun n x hx => by
        have h1 : x - (w (n + 1) g : A.V) ∈ Q n := hQmono n (n + 1) (Nat.le_succ n) hx
        have h2 : ((w (n + 1) g : A.V) - (w n g : A.V)) ∈ Q n := by
          have := (hmem n _).1 (hstep n g)
          simpa using this
        show x - (w n g : A.V) ∈ Q n
        have := (Q n).add_mem h1 h2
        simpa using this)
      (fun n => ⟨w n g, by simp [C]⟩)
      (by
        have : C 0 = (Homeomorph.subRight (w 0 g : A.V)) ⁻¹' (Q 0 : Set A.V) := rfl
        rw [this]
        exact (Homeomorph.subRight (w 0 g : A.V)).isCompact_preimage.2 (hQc 0))
      (fun n => (hQc n).isClosed.preimage (continuous_sub_right _))
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, fun n => Set.mem_iInter.1 hx n⟩
  choose d hd using hlim
  have hdT : ∀ g, d g ∈ LA.T := by
    intro g
    have := LA.T.add_mem (hQT 0 (hd g 0)) (w 0 g).2
    simpa using this

  have hcocn : ∀ n g h, (w n (g * h) : A.V) - w n g - A.ρ g (w n h) ∈ Q n := by
    intro n g h
    have h1 := (hw n).2 g h
    simp only [actQ, Submodule.mapQ_apply] at h1
    rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq] at h1
    have := (hmem n _).1 h1
    simp only [Submodule.coe_sub, Submodule.coe_add] at this
    rw [sub_sub]
    exact this
  have hcoc : ∀ g h, d (g * h) = d g + A.ρ g (d h) := by
    intro g h
    have : d (g * h) - d g - A.ρ g (d h) = 0 := by
      refine hsep _ (fun n => ?_)
      have e : d (g * h) - d g - A.ρ g (d h) = (d (g * h) - w n (g * h)) - (d g - w n g)
          - A.ρ g (d h - w n h) + ((w n (g * h) : A.V) - w n g - A.ρ g (w n h)) := by
        rw [map_sub]; abel
      rw [e]
      exact (Q n).add_mem ((Q n).sub_mem ((Q n).sub_mem (hd _ n) (hd g n)) (hQρ n g _ (hd h n)))
        (hcocn n g h)
    exact sub_eq_zero.1 (by rw [← sub_sub]; exact this)

  have hcont : Continuous d := by
    rw [continuous_iff_continuousAt]
    intro g₀
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
    intro U hU
    obtain ⟨N, hN⟩ := hshrink U hU
    have hlc := (IsLocallyConstant.iff_eventually_eq _).1 (hw N).1 g₀
    refine Filter.mem_map.2 ?_
    filter_upwards [hlc] with g hg
    show d g - d g₀ ∈ U
    apply hN
    rw [Submodule.Quotient.eq] at hg
    have h3 := (hmem N _).1 hg
    simp only [Submodule.coe_sub] at h3
    have e : d g - d g₀ = (d g - w N g) - (d g₀ - w N g₀) + ((w N g : A.V) - w N g₀) := by abel
    rw [e]
    exact (Q N).add_mem ((Q N).sub_mem (hd g N) (hd g₀ N)) h3
  refine ⟨d, ⟨⟨hcont, hcoc⟩, fun g _ => hdT g⟩, fun n g => ?_⟩
  refine ⟨⟨d g - w n g, hQT n (hd g n)⟩, (hmem n _).2 (hd g n), ?_⟩
  simp

end GlobalTheory.LimCocycle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatio
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem exists_extend_residue {O A F : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Algebra.IsIntegral O A] (hinj : Function.Injective (algebraMap O A)) [Field F] [IsAlgClosed F]
    (κ : IsLocalRing.ResidueField O →+* F) :
    ∃ g : A →+* F, g.comp (algebraMap O A) = κ.comp (IsLocalRing.residue O) := by
  obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) (IsLocalRing.maximalIdeal O)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)
  letI : Field (A ⧸ Q) := Ideal.Quotient.field Q
  let j : IsLocalRing.ResidueField O →+* A ⧸ Q := Ideal.quotientMap Q (algebraMap O A) hQm.ge
  have hj : j.comp (IsLocalRing.residue O) = (Ideal.Quotient.mk Q).comp (algebraMap O A) := by
    ext x; rfl
  letI : Algebra (IsLocalRing.ResidueField O) (A ⧸ Q) := j.toAlgebra
  letI : Algebra (IsLocalRing.ResidueField O) F := κ.toAlgebra
  haveI : Algebra.IsIntegral (IsLocalRing.ResidueField O) (A ⧸ Q) := ⟨fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hp, hpa⟩ := Algebra.IsIntegral.isIntegral (R := O) a
    refine ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩
    rw [eval₂_map]
    change eval₂ (j.comp (IsLocalRing.residue O)) _ _ = 0
    rw [hj, ← hom_eval₂, hpa, map_zero]⟩
  let L : (A ⧸ Q) →ₐ[IsLocalRing.ResidueField O] F := IsAlgClosed.lift
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  rw [RingHom.comp_assoc, ← hj, ← RingHom.comp_assoc]
  congr 1
  ext x
  exact L.commutes x

theorem exists_redVia : ∀ (D : D7) (i : D.nd.Loc) (k : Fin 2), D.nd.l i ≠ D.host.g k →
    ∃ ι : Fb (D.host.g k) (D.host.g_prime k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i),
      InjPrimeTo (D.nd.l i) ι ∧ RedVia D i k ι := by
  intro D i k _
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hφ : Function.Injective (iotaO D.nd D.naut i) :=
    (((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).injective).comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  letI : Algebra (D.nd.O i) ℂ := (iotaO D.nd D.naut i).toAlgebra
  let A := integralClosure (D.nd.O i) ℂ
  have hA : Function.Injective (algebraMap (D.nd.O i) A) := fun x y h => hφ (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := exists_extend_residue hA (D.naut.kFbar i)
  have hmem : ∀ x, D.ntypes.teichC k x ∈ A := by
    intro x
    by_cases hx : x = 0
    · rw [hx, GlobalTheory.TameLabels.teich_zero _ (D.ntypes.teichC_inj k)]; exact A.zero_mem
    · obtain ⟨n, hn, h1⟩ := isOfFinOrder_iff_pow_eq_one.1
        ((D.ntypes.teichC k).isOfFinOrder (GlobalTheory.TameLabels.isOfFinOrder_of_ne_zero hx))
      exact IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)
  let t : Fb (D.host.g k) (D.host.g_prime k) →* A := (D.ntypes.teichC k).codRestrict A.toSubmonoid hmem
  have ht : ∀ x, (t x : ℂ) = D.ntypes.teichC k x := fun _ => rfl
  refine ⟨g.toMonoidHom.comp t, fun x y hx hy hcx hcy h => ?_, fun p s hp => ?_⟩
  · refine D.ntypes.teichC_inj k x y hx hy ?_
    rw [← ht, ← ht]
    congr 1
    refine GlobalTheory.TameRed.eq_of_map_eq g (M := orderOf x * orderOf y) ?_ ?_ ?_ h
    · rw [Ne, CharP.cast_eq_zero_iff _ (D.nd.l i)]
      exact (Nat.Prime.coprime_iff_not_dvd (D.nd.lPrime i).out).1 (Nat.Coprime.mul_left hcx hcy).symm
    · rw [← map_pow, pow_mul, pow_orderOf_eq_one, one_pow, map_one]
    · rw [← map_pow, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow, map_one]
  · have h1 : p.map (algebraMap (D.nd.O i) A) = (s.map fun x => X - C (t x)).prod := by
      apply Polynomial.map_injective A.val.toRingHom Subtype.val_injective
      rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
      refine hp.trans (congrArg _ (Multiset.map_congr rfl fun x _ => ?_))
      simp [ht]
    rw [← hg, ← Polynomial.map_map, h1, Polynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
    simp

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameInertiaElementAtAuxiliaryPrime
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys
open scoped TensorProduct

namespace GlobalTheory.TwSys.InertiaElt

open Filter Topology

theorem exists_coprime_dvd_mul_pow (m : ℕ) (o : ℕ) (ho : o ≠ 0) : ∃ t K : ℕ, Nat.Coprime t m ∧ o ∣ t * m ^ K := by
  induction o using Nat.recOnMul with
  | zero => exact absurd rfl ho
  | one => exact ⟨1, 0, Nat.coprime_one_left m, one_dvd _⟩
  | prime p hp =>
    by_cases h : p ∣ m
    · exact ⟨1, 1, Nat.coprime_one_left m, by simpa using h⟩
    · exact ⟨p, 0, (Nat.Prime.coprime_iff_not_dvd hp).2 h, by simp⟩
  | mul a b iha ihb =>
    obtain ⟨t, K, ht, hK⟩ := iha (left_ne_zero_of_mul ho)
    obtain ⟨t', K', ht', hK'⟩ := ihb (right_ne_zero_of_mul ho)
    refine ⟨t * t', K + K', Nat.Coprime.mul_left ht ht', ?_⟩
    have : t * t' * m ^ (K + K') = (t * m ^ K) * (t' * m ^ K') := by ring
    rw [this]
    exact mul_dvd_mul hK hK'

theorem exists_limit_pow {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (σ : Γ) (m : ℕ) : ∃ z : Γ, (∀ I : Subgroup Γ, IsClosed (I : Set Γ) → σ ∈ I → z ∈ I) ∧
      (∀ U : Subgroup Γ, IsOpen (U : Set Γ) → ∃ k : ℕ, z⁻¹ * σ ^ (m ^ k) ∈ U) ∧
      ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → U.Normal → ∃ n : ℕ, Nat.Coprime n m ∧ z ^ n ∈ U := by
  obtain ⟨z, hz⟩ : ∃ z : Γ, MapClusterPt z atTop (fun k : ℕ => σ ^ (m ^ k)) :=
    exists_clusterPt_of_compactSpace (map (fun k : ℕ => σ ^ (m ^ k)) atTop)
  have key : ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → ∃ᶠ k : ℕ in atTop, z⁻¹ * σ ^ (m ^ k) ∈ U := by
    intro U hU
    have ho : IsOpen ((fun x : Γ => z⁻¹ * x) ⁻¹' (U : Set Γ)) := hU.preimage (by fun_prop)
    exact hz.frequently (p := fun x => z⁻¹ * x ∈ U) (ho.mem_nhds (by simp))
  refine ⟨z, fun I hI hσ => ?_, fun U hU => (key U hU).exists, fun U hU hN => ?_⟩
  · exact hI.mem_of_mapClusterPt hz (Eventually.of_forall fun k => I.pow_mem hσ _)
  · have : Finite (Γ ⧸ U) := U.quotient_finite_of_isOpen hU
    obtain ⟨t, K, ht, hK⟩ := exists_coprime_dvd_mul_pow m (orderOf (QuotientGroup.mk' U σ)) (orderOf_pos _).ne'
    obtain ⟨k, hk, hmem⟩ := frequently_atTop.1 (key U hU) K
    refine ⟨t, ht, ?_⟩
    have e : QuotientGroup.mk' U z = QuotientGroup.mk' U σ ^ (m ^ k) := by
      rw [← map_pow]
      exact QuotientGroup.eq.2 hmem
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' U (z ^ t) = 1
    rw [map_pow, e, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
    refine hK.trans ?_
    rw [mul_comm]
    exact Nat.mul_dvd_mul_right (pow_dvd_pow m hk) t

theorem isUnit_sub_one {O : Type*} [CommRing O] [IsDomain O] {n : ℕ} {ζ : O} (hn : IsUnit (n : O))
    (h : IsPrimitiveRoot ζ n) (h1 : 1 < n) : IsUnit (ζ - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 := ⟨n - 2, by omega⟩
  have e := h.prod_one_sub_pow_eq_order
  rw [Finset.prod_range_succ'] at e
  have hu : IsUnit (1 - ζ ^ (0 + 1)) := by
    refine isUnit_of_mul_isUnit_right (x := ∏ j ∈ Finset.range k, (1 - ζ ^ (j + 1 + 1))) ?_
    rw [e]
    exact_mod_cast hn
  rw [← neg_sub]
  simpa using hu.neg

theorem exists_place_mem (E : Type) [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 E), ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 E) := by
    intro h
    have h2 : IsUnit (Algebra.norm ℤ ((p : ℕ) : 𝓞 E)) := h.map _
    have e : Algebra.norm ℤ ((p : ℕ) : 𝓞 E) = (p : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [← Algebra.norm_algebraMap]
      simp
    rw [e, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h2
    exact hp.one_lt.ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 E)}) (by
    rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.1 hmem))

end GlobalTheory.TwSys.InertiaElt

open GlobalTheory.TwSys.InertiaElt in

theorem GlobalTheory.TwSys.exists_tameInertiaElementAtAuxiliaryPrime : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (i : X.Tw), ∃ z, IsTameInertiaElementAtTwistPrime X i z := by
  intro D N X i
  have hl : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨v, hv⟩ : ∃ v, v ∈ X.pD i := by
    have hp : (if X.l i = D.host.pde then D.host.pde' else D.host.pde).Prime := by
      split_ifs
      · exact D.host.pde'_prime
      · exact D.host.pde_prime
    obtain ⟨v, hv⟩ := exists_place_mem D.host.E hp
    refine ⟨v, ?_⟩
    rw [← Finset.mem_coe, X.pD_eq i]
    exact hv
  obtain ⟨A, hA⟩ := exists_isPlaceOver N.Om v

  obtain ⟨p, hp, hp15, hp2, hpl⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ 15 ∧ p ≠ 2 ∧ p ≠ X.l i := by
    by_cases h : X.l i = 3
    · exact ⟨5, by norm_num, by norm_num, by norm_num, by omega⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, fun h' => h h'.symm⟩
  have : Fact p.Prime := ⟨hp⟩
  have hcard := X.delta_15 i v hv A hA
  have : Finite ((Ine (F := D.host.E) A).map (X.delta i)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨⟨y, hy⟩, hyo⟩ := exists_prime_orderOf_dvd_card' (G := (Ine (F := D.host.E) A).map (X.delta i)) p
    (by rw [hcard]; exact hp15)
  obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hy
  have hord : orderOf (X.delta i σ) = p := by
    rw [← hyo, ← Subgroup.orderOf_coe]
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_limit_pow σ (X.l i * Ideal.absNorm v.asIdeal)
  refine ⟨z, v, hv, A, hA, hz1 _ (isClosed_Ine A) hσ, ?_, hz3⟩
  obtain ⟨k, hk⟩ := hz2 _ (X.delta_open i)
  have hz : X.delta i z = X.delta i σ ^ ((X.l i * Ideal.absNorm v.asIdeal) ^ k) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, inv_mul_eq_one] at hk
    exact hk
  have hpl' : Nat.Coprime p (X.l i) := (Nat.coprime_primes hp hl).2 hpl
  have hpq : Nat.Coprime p (Ideal.absNorm v.asIdeal) := by
    refine Nat.Coprime.coprime_dvd_left hp15 ?_
    have := X.delta_tame i v hv
    rw [Nat.Coprime, Nat.gcd_rec, this]
    norm_num
  have hprim : IsPrimitiveRoot (X.delta i σ) p := hord ▸ IsPrimitiveRoot.orderOf _
  have hcop : Nat.Coprime ((X.l i * Ideal.absNorm v.asIdeal) ^ k * 2) p :=
    Nat.Coprime.symm (Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (Nat.Coprime.mul_right hpl' hpq))
      ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  have hprim2 : IsPrimitiveRoot (((X.delta i z : (X.O0 i)ˣ) : X.O0 i) ^ 2) p := by
    have := hprim.pow_of_coprime _ hcop
    rw [pow_mul, ← hz] at this
    rw [← Units.val_pow_eq_pow_val]
    exact IsPrimitiveRoot.coe_units_iff.2 this
  refine isUnit_sub_one ?_ hprim2 hp.one_lt
  have hlnu : ¬ IsUnit ((X.l i : ℕ) : X.O0 i) := by
    intro h
    have h2 := h.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at h2
    exact X.O_l i h2
  have hc : IsCoprime ((p : ℕ) : X.O0 i) ((X.l i : ℕ) : X.O0 i) := hpl'.cast
  obtain ⟨a, b, hab⟩ := hc
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hab ▸ isUnit_one) with h | h
  · exact isUnit_of_mul_isUnit_right h
  · exact absurd (isUnit_of_mul_isUnit_right h) hlnu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCharacterOfGaloisStableLineCLTate
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem exists_unit_character_of_stable_line (l : ℕ) [Fact l.Prime] (y : ℂ_[l]) (hy : y ≠ 0)
    (h : ∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) :
    ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l,
      Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  choose x hx using h
  have hn : ∀ g, ‖x g‖ = 1 := fun g => by
    have h1 := GlobalTheory.RingBasics.norm_σC g y
    rw [hx, norm_mul, norm_algebraMap'] at h1
    exact mul_right_cancel₀ (norm_ne_zero_iff.2 hy) (h1.trans (one_mul _).symm)
  have hm : ∀ g k, x (g * k) = x g * x k := fun g k => by
    apply (algebraMap ℚ_[l] ℂ_[l]).injective
    apply mul_right_cancel₀ hy
    rw [← hx, GlobalTheory.RingBasics.σC_mul, hx k, map_mul, TateTwist.σC_algebraMap, hx g, map_mul]
    ring
  refine ⟨MonoidHom.mk' (fun g => PadicInt.mkUnits (hn g)) fun g k => ?_, fun g => hx g⟩
  apply Units.ext
  apply Subtype.ext
  exact hm g k

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusConstantsPiAdicFiltrationModEllStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_constants_piAdic_filtration_modEll : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (s : ℕ), (∀ a : RA LL, ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a') ∧ NearPi AI LL s 2 (φRW LL (piR AI LL s)) ∧ (∀ (m : ℕ) (x : RW LL), NearPi AI LL s m x → NearPi AI LL s m (φRW LL x)) ∧ ∀ o : ↥(OL LL), NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o) → ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  first | exact @GlobalTheory.DecomplFrob.frobenius_and_constants | exact GlobalTheory.DecomplFrob.frobenius_and_constants | (intros; apply GlobalTheory.DecomplFrob.frobenius_and_constants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusFixedTensorEqConstantStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_fixed_tensor_eq_constant : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) (k : Type) [Field k] [Algebra ↥(OL LL) k] [CharP k l] (x : k ⊗[↥(OL LL)] RW LL), Algebra.TensorProduct.map (AlgHom.id k k) (φRW LL) x = x → ∃ c : k, x = algebraMap k (k ⊗[↥(OL LL)] RW LL) c := by
  first | exact @GlobalTheory.RedFixed.fixed_red | exact GlobalTheory.RedFixed.fixed_red | (intros; apply GlobalTheory.RedFixed.fixed_red <;> assumption)
end

