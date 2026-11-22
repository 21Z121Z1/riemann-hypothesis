import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsRegularSectionGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0011

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FiniteNonvanishingSelection
section
open MvPolynomial

theorem PositivityTheory.Xgn.finite_nonvanishing_selection : ∀ (σ : Type) [Finite σ] (F : Set (MvPolynomial σ ℤ)), ∃ T : Finset (MvPolynomial σ ℤ), (T : Set (MvPolynomial σ ℤ)) ⊆ F ∧ ∀ z : σ → ℂ, (∃ s ∈ F, eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0) → ∃ s ∈ T, eval z (MvPolynomial.map (Int.castRingHom ℂ) s) ≠ 0 := by
  intro σ _ F
  have hfg : (Submodule.span (MvPolynomial σ ℤ) F).FG := IsNoetherian.noetherian _
  obtain ⟨T, hTF, hT⟩ := (Submodule.fg_span_iff_fg_span_finset_subset F).1 hfg
  refine ⟨T, hTF, fun z hz => ?_⟩
  obtain ⟨s, hsF, hs⟩ := hz
  by_contra hall
  push_neg at hall
  let φ : MvPolynomial σ ℤ →+* ℂ := (eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))
  have hle : Ideal.span (T : Set (MvPolynomial σ ℤ)) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    intro t ht
    exact RingHom.mem_ker.2 (hall t ht)
  have hsT : s ∈ Submodule.span (MvPolynomial σ ℤ) (T : Set (MvPolynomial σ ℤ)) := by
    rw [← hT]
    exact Submodule.subset_span hsF
  exact hs (RingHom.mem_ker.1 (hle hsT))
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HomogeneousPairComponent
section
open MvPolynomial

namespace PositivityTheory.Xgn.HomogeneousComponentProduct

theorem comp_mul {σ M R : Type*} [CommRing R] [AddCancelCommMonoid M] (w : σ → M)
    (g : MvPolynomial σ R) (bg : M) (hg : IsWeightedHomogeneous w g bg) (b : M)
    (s : MvPolynomial σ R) :
    weightedHomogeneousComponent w (b + bg) (s * g) = weightedHomogeneousComponent w b s * g := by
  conv_lhs => rw [s.as_sum, Finset.sum_mul]
  conv_rhs => rw [s.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hm : IsWeightedHomogeneous w (monomial d (coeff d s)) (Finsupp.weight w d) :=
    isWeightedHomogeneous_monomial _ _ _ rfl
  by_cases h : Finsupp.weight w d = b
  · subst h
    rw [(hm.mul hg).weightedHomogeneousComponent_same, hm.weightedHomogeneousComponent_same]
  · rw [(hm.mul hg).weightedHomogeneousComponent_ne _ (fun h' => h (add_right_cancel h').symm),
      hm.weightedHomogeneousComponent_ne _ (Ne.symm h), zero_mul]

theorem comp_mul_zero {σ M R : Type*} [CommRing R] [AddCommMonoid M] (w : σ → M)
    (g : MvPolynomial σ R) (bg : M) (hg : IsWeightedHomogeneous w g bg) (c : M)
    (hc : ∀ b, c ≠ b + bg) (s : MvPolynomial σ R) :
    weightedHomogeneousComponent w c (s * g) = 0 := by
  rw [s.as_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  exact ((isWeightedHomogeneous_monomial _ _ _ rfl).mul hg).weightedHomogeneousComponent_ne _ (hc _)

end PositivityTheory.Xgn.HomogeneousComponentProduct

theorem PositivityTheory.Xgn.homogeneous_pair_component : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), P.IsPrime → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → ∀ (f g u₀ v₀ : MvPolynomial (Σ k, ι k) ℤ) (bf bg a : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → f ∉ P → u₀ * f - v₀ * g ∈ P → weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀ ∉ P → ∃ (b : K → ℕ) (v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a u₀) * f - v * g ∈ P := by
  intro K _ _ ι _ P hP hH f g u₀ v₀ bf bg a hf hg hfP hrel hu
  have h := hH _ hrel (a + bf)
  rw [map_sub, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ f bf hf] at h
  by_cases hb : ∃ b, a + bf = b + bg
  · obtain ⟨b, hb⟩ := hb
    rw [hb, PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul _ g bg hg] at h
    exact ⟨b, _, weightedHomogeneousComponent_isWeightedHomogeneous b v₀, hb, h⟩
  · rw [PositivityTheory.Xgn.HomogeneousComponentProduct.comp_mul_zero _ g bg hg _
      (fun b hb' => hb ⟨b, hb'⟩), sub_zero] at h
    rcases hP.mem_or_mem h with h | h
    · exact absurd h hu
    · exact absurd h hfP
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MultihomogeneousEvalScale
section
open MvPolynomial

theorem PositivityTheory.Xgn.multihomogeneous_eval_scale : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (s : MvPolynomial (Σ k, ι k) ℤ) (a : K → ℕ) (c : K → ℂ) (z : ((Σ k, ι k) → ℂ)), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog s a → eval (fun p => c p.1 * z p) (MvPolynomial.map (Int.castRingHom ℂ) s) = (∏ k, c k ^ a k) * eval z (MvPolynomial.map (Int.castRingHom ℂ) s) := by
  intro K _ _ ι _ s a c z hs
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m = a :=
    hs (mem_support_iff.mp hm)
  have ha : ∀ k, a k = ∑ i : ι k, m ⟨k, i⟩ := by
    intro k
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
      Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
    · intro j _ hj
      simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_apply, hj, hj.symm]
    · simp
  have h1 : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ha k, ← Finset.prod_pow_eq_pow_sum]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, h1]
  ring
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MultihomogeneousNonvanishingOff
section
open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousNonvanishing

open GroundTheory.Heights₂.Heights.NumbersDVR

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

theorem exists_component_ne (z : (Σ k, ι k) → ℂ) (q : MvPolynomial (Σ k, ι k) ℤ)
    (hq : eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0) :
    ∃ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (weightedHomogeneousComponent (blockWeight ι) a q)) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hq
  have hfin := weightedHomogeneousComponent_finsupp (w := blockWeight ι) q
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) q]
  have key := map_finsum ((eval z).comp (MvPolynomial.map (Int.castRingHom ℂ))) hfin
  simp only [RingHom.coe_comp, Function.comp_apply] at key
  rw [key]
  simp [h]

theorem exists_form_ne (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (d : K → ℕ) :
    ∃ m : MvPolynomial (Σ k, ι k) ℤ, IsWeightedHomogeneous (blockWeight ι) m d ∧
      eval z (MvPolynomial.map (Int.castRingHom ℂ) m) ≠ 0 := by
  choose i hi using hz
  refine ⟨∏ k, X ⟨k, i k⟩ ^ d k, ?_, ?_⟩
  · have h := IsWeightedHomogeneous.prod Finset.univ
      (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℤ) ^ d k)
      (fun k => d k • blockWeight ι ⟨k, i k⟩)
      (fun k _ => (isWeightedHomogeneous_X ℤ (blockWeight ι) ⟨k, i k⟩).pow (d k))
    convert h using 1
    conv_lhs => rw [← Finset.univ_sum_single d]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ext j
    simp [blockWeight, Pi.single_apply]
  · simp [Finset.prod_ne_zero_iff, hi]

end PositivityTheory.Xgn.MultihomogeneousNonvanishing

theorem PositivityTheory.Xgn.multihomogeneous_nonvanishing_off : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (bf bg : K → ℕ) (z : ((Σ k, ι k) → ℂ)) (q : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → q ∈ P → eval z (MvPolynomial.map (Int.castRingHom ℂ) q) ≠ 0 → ∃ (a b : K → ℕ) (u v : MvPolynomial (Σ k, ι k) ℤ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog u a ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog v b ∧ a + bf = b + bg ∧ u ∈ P ∧ v ∈ P ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) u) ≠ 0 ∧ eval z (MvPolynomial.map (Int.castRingHom ℂ) v) ≠ 0 := by
  intro K _ _ ι _ P bf bg z q hP hz hqP hq
  obtain ⟨a, ha⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_component_ne z q hq
  obtain ⟨m1, hm1, hm1z⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_form_ne z hz bg
  obtain ⟨m2, hm2, hm2z⟩ := PositivityTheory.Xgn.MultihomogeneousNonvanishing.exists_form_ne z hz bf
  have hcP : weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a q ∈ P :=
    hP q hqP a
  have hch := weightedHomogeneousComponent_isWeightedHomogeneous
    (w := GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a q
  refine ⟨a + bg, a + bf, _ * m1, _ * m2, hch.mul hm1, hch.mul hm2, by abel,
    P.mul_mem_right _ hcP, P.mul_mem_right _ hcP, ?_, ?_⟩
  · simpa using mul_ne_zero ha hm1z
  · simpa using mul_ne_zero ha hm2z
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.NormalProperLineOrder
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.ProperZeroNumerical

theorem subset_of_specializes {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] [QuasiSober T]
    {Z V : Set T} (hZ : IsClosed Z) (hc : IsPreconnected Z) (hV : IsOpen V) (hne : (Z ∩ V).Nonempty)
    (hs : ∀ y x : T, y ∈ Z → y ∈ V → y ⤳ x → x ∈ V) : Z ⊆ V := by
  have hcl : IsClosed (Z ∩ V) := by
    obtain ⟨S, hfin, hScl, hSirr, hU⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
    have e : Z ∩ V = ⋃ t ∈ {t ∈ S | (t ∩ V).Nonempty}, t := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq, exists_prop]
      constructor
      · rintro ⟨hx, hxV⟩
        rw [hU] at hx
        obtain ⟨t, ht, hxt⟩ := hx
        exact ⟨t, ⟨ht, x, hxt, hxV⟩, hxt⟩
      · rintro ⟨t, ⟨ht, htV⟩, hxt⟩
        have hsub : t ⊆ Z := by rw [hU]; exact Set.subset_sUnion_of_mem ht
        obtain ⟨y, hy⟩ := QuasiSober.sober (hSirr t ht) (hScl t ht)
        exact ⟨hsub hxt, hs y x (hsub hy.mem) ((hy.mem_open_set_iff hV).2 htV) (hy.specializes hxt)⟩
    rw [e]
    exact (hfin.subset fun t ht => ht.1).isClosed_biUnion fun t ht => hScl t ht.1
  intro x hx
  by_contra hxV
  obtain ⟨z, hz, hzV, hz'⟩ := hc V (Z ∩ V)ᶜ hV hcl.isOpen_compl
    (fun w hw => by
      by_cases h : w ∈ V
      · exact Or.inl h
      · exact Or.inr fun h' => h h'.2) hne ⟨x, hx, fun h => hxV h.2⟩
  exact hz' ⟨hz, hzV⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unit_mul {p : Cpt ξ} {a b : Ω} (ha : unitAt ξ p a) (hb : unitAt ξ p b) : unitAt ξ p (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem unit_inv {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) : unitAt ξ p a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

theorem unit_pow {p : Cpt ξ} {a : Ω} (ha : unitAt ξ p a) (n : ℕ) : unitAt ξ p (a ^ n) :=
  ⟨pow_ne_zero n ha.1, pow_mem ha.2.1 n, by rw [← inv_pow]; exact pow_mem ha.2.2 n⟩

theorem unit_change {L : Lat ξ Ω} {p : Cpt ξ} {σ π e f : Ω} {M : ℕ} (he : L.IsGenAt p e) (hf : L.IsGenAt p f)
    (h : unitAt ξ p (π / (σ / f) ^ M)) : unitAt ξ p (π / (σ / e) ^ M) := by
  rw [CurvePositivity.change_gen σ π e f M hf.1]
  exact unit_mul h (unit_pow (ProjectiveLinePlaces.unitAt_div he hf) M)

theorem exists_local_gen {L : Lat ξ Ω} (h : L.IsVB 1 ⊤) (p : Cpt ξ) :
    ∃ (U : X.Opens) (e : Ω), p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U → L.IsGenAt q e := by
  obtain ⟨U, hp, b, -, hb⟩ := h p (Set.mem_univ p)
  refine ⟨U, b 0, hp, fun q hq => ?_⟩
  obtain ⟨hli, hspan⟩ := hb q (Set.mem_univ q) hq
  refine ⟨hli.ne_zero 0, ?_⟩
  rw [hspan]
  congr 1
  ext x
  simp [eq_comm]

end PositivityTheory.Xgn.ProperZeroNumerical

open PositivityTheory.Xgn.ProperZeroNumerical in
theorem PositivityTheory.Xgn.normal_proper_line_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → NormalCpt ξ → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) → ∀ (L : Lat ξ Ω) (σ : Ω), L.IsVB 1 ⊤ → NumTrivMod L (algebraMap O Ω ϖ) → (∀ p ∈ genFibre O ξ, L.IsGenAt p σ) → ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, OrderAt L σ (algebraMap O Ω ϖ) M a p := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hn hconn L σ hvb hnum hgen
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := { }
  obtain ⟨M, a, hM, hreg, p₀, hp₀, -, e₀, c₀, he₀, hL₀, hσ₀, hu₀⟩ :=
    exists_regular_section_generator X Ω ξ O s ϖ hϖ hinj hs hg hn hconn.1 L σ hvb hgen
  have hunit : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal :=
    fun p o => (ConstReg.regular_const X Ω ξ O s hs p o).2 hg
  set π : Ω := algebraMap O Ω ϖ ^ a with hπ
  let Good : Cpt ξ → Prop := fun p => ∃ e, L.IsGenAt p e ∧ unitAt ξ p (π / (σ / e) ^ M)
  let V : Set X := ⋃₀ {W | IsOpen W ∧ ∀ q : Cpt ξ, q.1 ∈ W → Good q}
  have hVo : IsOpen V := isOpen_sUnion fun W hW => hW.1
  have hV : ∀ q : Cpt ξ, q.1 ∈ V ↔ Good q := by
    intro q
    constructor
    · rintro ⟨W, hW, hq⟩
      exact hW.2 q hq
    · rintro ⟨e, he, hu⟩
      obtain ⟨U, b, hqU, hb⟩ := exists_local_gen hvb q
      obtain ⟨U', hqU', hU'⟩ := (regAt_unitAt_open X Ω ξ q _).2 (unit_change (hb q hqU) he hu)
      exact ⟨(U : Set X) ∩ U', ⟨U.isOpen.inter U'.isOpen, fun r hr => ⟨b, hb r hr.1, hU' r hr.2⟩⟩, hqU, hqU'⟩
  have hZ : IsClosed (zeroSet ξ (algebraMap O Ω ϖ)) := by
    have e : zeroSet ξ (algebraMap O Ω ϖ) =
        closure {genPt ξ} ∩ s ⁻¹' (PrimeSpectrum.zeroLocus ({ϖ} : Set O)) := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨specializes_iff_mem_closure.1 h1,
          Set.singleton_subset_iff.2 (not_not.1 fun h => h2 ((hunit ⟨x, h1⟩ ϖ).2 h))⟩
      · rintro ⟨h1, h2⟩
        exact ⟨specializes_iff_mem_closure.2 h1, fun h =>
          (hunit ⟨x, specializes_iff_mem_closure.2 h1⟩ ϖ).1 h (Set.singleton_subset_iff.1 h2)⟩
    rw [e]
    exact isClosed_closure.inter ((PrimeSpectrum.isClosed_zeroLocus _).preimage s.continuous)
  have hsub : zeroSet ξ (algebraMap O Ω ϖ) ⊆ V := by
    refine subset_of_specializes hZ hconn.2 hVo ⟨p₀.1, ⟨p₀.2, hp₀⟩, (hV p₀).2 ⟨e₀, ⟨he₀, hL₀⟩, ?_⟩⟩ ?_
    · have e1 : σ / e₀ = c₀ := by rw [hσ₀, smul_eq_mul, mul_div_cancel_right₀ _ he₀]
      rw [e1, ← inv_div]
      exact unit_inv hu₀
    · rintro y x ⟨hy, hyn⟩ hyV hyx
      obtain ⟨x', hx', hcl⟩ :=
        (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton ⟨x, subset_closure rfl⟩
      have hxx : x ⤳ x' := specializes_iff_mem_closure.2 hx'
      refine hxx.mem_open hVo ?_
      have hyx' : y ⤳ x' := hyx.trans hxx
      let q : Cpt ξ := ⟨x', hy.trans hyx'⟩
      obtain ⟨U, b, hqU, hb⟩ := exists_local_gen hvb q
      refine (hV q).2 ⟨b, hb q hqU, ?_⟩
      by_contra hnu
      obtain ⟨e, he, hue⟩ := (hV ⟨y, hy⟩).1 hyV
      obtain ⟨Γ, i, -, hη, hz⟩ := GlobalTheory.T.special_fibre_closed_specialization X Ω ξ O s ϖ hϖ hinj hs hg ⟨y, hy⟩ q (π / (σ / b) ^ M) hyn hyx' hcl
        (hreg q b (hb q hqU)) (unit_change (hb ⟨y, hy⟩ (hyx'.mem_open U.isOpen hqU)) he hue) hnu
      have hq : q = ⟨centre (Γ.z i), Γ.z_spec i⟩ := Subtype.ext hz.symm
      have hηU : centre Γ.η ∈ U := (Γ.generic_centre_specializes i).mem_open U.isOpen (by rw [hz]; exact hqU)
      apply hnu
      have hbq := hb q hqU
      rw [hq] at hbq ⊢
      exact PositivityTheory.Xgn.degree_zero_curve_positive X Ω ξ O s _ L σ π M Γ hg hvb hM (hnum Γ) hreg
        (fun e' he' => unit_change he' (hb ⟨centre Γ.η, Γ.η_spec⟩ hηU) hη) i (Γ.z_spec i) b hbq
  refine ⟨M, a, hM, fun p => ?_⟩
  by_cases hu : unitAt ξ p (algebraMap O Ω ϖ)
  · have hp : p ∈ genFibre O ξ := by
      intro o ho
      obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ
      rw [map_mul, map_pow]
      refine unit_mul ((hunit p _).2 fun h => ?_) (unit_pow hu n)
      exact (s p.1).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)
    refine ⟨σ, 1, (hgen p hp).1, (hgen p hp).2, (one_smul _ _).symm, ?_⟩
    rw [one_pow, one_div]
    refine unit_inv ⟨zpow_ne_zero a hu.1, ZLat.zpow_mem_regAt hu a, ?_⟩
    rw [← zpow_neg]
    exact ZLat.zpow_mem_regAt hu _
  · obtain ⟨e, he, hue⟩ := (hV p).1 (hsub ⟨p.2, hu⟩)
    refine ⟨e, σ / e, he.1, he.2, ?_, ?_⟩
    · rw [smul_eq_mul, div_mul_cancel₀ _ he.1]
    · rw [← inv_div]
      exact unit_inv hue
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.PolynomialEvalComplexConjugate
section
open MvPolynomial

theorem PositivityTheory.Xgn.polynomial_eval_complex_conjugate : ∀ (σ : Type) (s : MvPolynomial σ ℤ) (z : σ → ℂ), eval (fun p => (starRingEnd ℂ) (z p)) (MvPolynomial.map (Int.castRingHom ℂ) s) = (starRingEnd ℂ) (eval z (MvPolynomial.map (Int.castRingHom ℂ) s)) := by
  intro σ s z
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.PolynomialNormSquareSmooth
section
open MvPolynomial

namespace PositivityTheory.Xgn.SmoothPolynomialNormSquare

theorem contDiff_eval (σ : Type) [Fintype σ] (p : MvPolynomial σ ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : σ → ℂ => MvPolynomial.eval z p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact contDiff_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (contDiff_apply ℝ ℂ i)

end PositivityTheory.Xgn.SmoothPolynomialNormSquare

theorem PositivityTheory.Xgn.polynomial_norm_square_smooth : ∀ (σ : Type) [Fintype σ] (s : MvPolynomial σ ℤ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : σ → ℂ => ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) s)‖ ^ 2) := by
  intro σ _ s
  exact (PositivityTheory.Xgn.SmoothPolynomialNormSquare.contDiff_eval σ _).norm_sq ℝ
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.RelevantPrimeOrbitClosure
section
open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousOrbit

open GroundTheory.Heights₂.Heights.NumbersDVR

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}

noncomputable def orb (z : (Σ k, ι k) → ℂ) : MvPolynomial (Σ k, ι k) ℤ →+* MvPolynomial K ℂ :=
  eval₂Hom (Int.castRingHom _) (fun v => C (z v) * X v.1)

lemma prod_weight (d : (Σ k, ι k) →₀ ℕ) :
    (d.prod fun v n => (X v.1 : MvPolynomial K ℂ) ^ n) =
      ∏ k, (X k : MvPolynomial K ℂ) ^ (Finsupp.weight (blockWeight ι) d k) := by
  refine Finsupp.induction d ?_ ?_
  · simp
  · intro v b f _ _ ih
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    have h1 : ((Finsupp.single v b).prod fun x n => (X x.1 : MvPolynomial K ℂ) ^ n) = X v.1 ^ b :=
      Finsupp.prod_single_index (pow_zero _)
    rw [h1, ih, map_add]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    simp [blockWeight, Pi.single_apply, Finsupp.weight_apply]

lemma orb_homog (z : (Σ k, ι k) → ℂ) (a : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℤ)
    (hs : s.IsWeightedHomogeneous (blockWeight ι) a) :
    orb z s = C (eval z (MvPolynomial.map (Int.castRingHom ℂ) s)) *
      ∏ k, (X k : MvPolynomial K ℂ) ^ a k := by
  conv_lhs => rw [s.as_sum]
  conv_rhs => rw [s.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hw : Finsupp.weight (blockWeight ι) d = a := hs (mem_support_iff.mp hd)
  simp only [orb, coe_eval₂Hom, eval₂_monomial, map_monomial, eval_monomial, mul_pow,
    Finsupp.prod_mul]
  rw [prod_weight, hw]
  simp [map_finsuppProd, mul_assoc]

lemma orb_eq_zero (z : (Σ k, ι k) → ℂ) (s : MvPolynomial (Σ k, ι k) ℤ)
    (h : ∀ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ)
      (weightedHomogeneousComponent (blockWeight ι) a s)) = 0) : orb z s = 0 := by
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) s,
    map_finsum (orb z) (weightedHomogeneousComponent_finsupp s)]
  have h0 : ∀ a, orb z (weightedHomogeneousComponent (blockWeight ι) a s) = 0 := fun a => by
    rw [orb_homog z a _ (weightedHomogeneousComponent_isWeightedHomogeneous a s), h a, map_zero,
      zero_mul]
  simp [h0]

end PositivityTheory.Xgn.MultihomogeneousOrbit

theorem PositivityTheory.Xgn.relevant_prime_orbit_closure : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)) (z : ((Σ k, ι k) → ℂ)), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P → z ∈ ReciprocityTheory.ChartRestriction.G.Geo.mcPts P → ∃ W : Ideal (MvPolynomial (Σ k, ι k) ℤ), W.IsPrime ∧ P ≤ W ∧ GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W ∧ (∀ p : Nat.Primes, (C ((p : ℕ) : ℤ) : MvPolynomial (Σ k, ι k) ℤ) ∉ W) ∧ ∀ s : MvPolynomial (Σ k, ι k) ℤ, s ∉ W → ∃ a : K → ℕ, eval z (MvPolynomial.map (Int.castRingHom ℂ) (weightedHomogeneousComponent (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) a s)) ≠ 0 := by
  intro K _ _ ι _ P z hP hz
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨RingHom.ker (PositivityTheory.Xgn.MultihomogeneousOrbit.orb z), RingHom.ker_isPrime _, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rw [RingHom.mem_ker]
    exact PositivityTheory.Xgn.MultihomogeneousOrbit.orb_eq_zero z q (fun a => hz2 _ (hP q hq a))
  · intro k
    obtain ⟨i, hi⟩ := hz1 k
    refine ⟨i, ?_⟩
    rw [RingHom.mem_ker]
    simp [PositivityTheory.Xgn.MultihomogeneousOrbit.orb, hi, X_ne_zero]
  · intro p
    rw [RingHom.mem_ker]
    simp [PositivityTheory.Xgn.MultihomogeneousOrbit.orb, p.prop.ne_zero]
  · intro s hs
    by_contra hne
    push_neg at hne
    exact hs (RingHom.mem_ker.mpr (PositivityTheory.Xgn.MultihomogeneousOrbit.orb_eq_zero z s hne))
end

