import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0215
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0197
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionShapeOfTorsionCounts
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiInjectiveQuotientH2
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.NatQuot

theorem exists_continuous_div {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O]
    [IsTopologicalRing O] [CompactSpace O] [T2Space O] {X : Type} [TopologicalSpace X]
    {π : O} (hπ : π ≠ 0) (u : X → O) (hu : Continuous u) (hd : ∀ x, π ∣ u x) :
    ∃ w : X → O, Continuous w ∧ ∀ x, u x = π * w x := by
  choose w hw using hd
  have hemb : Topology.IsClosedEmbedding (fun a : O => π * a) :=
    (continuous_const.mul continuous_id).isClosedEmbedding (mul_right_injective₀ hπ)
  refine ⟨w, hemb.isEmbedding.continuous_iff.2 ?_, hw⟩
  have : ((fun a : O => π * a) ∘ w) = u := funext fun x => (hw x).symm
  rw [this]; exact hu

theorem phi_quot_pow_injective :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
      [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G],
      PadicCoeff p O → ∀ {ε : G →* Oˣ}, Continuous (fun g : G => ((ε g : Oˣ) : O)) →
      ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ,
      Function.Injective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  intro p O _ _ _ _ _ G _ _ _ hO ε hε z hz k
  haveI : CompactSpace O := hO.compact
  haveI : T2Space O := hO.t2
  haveI hdisc := (quot_pow_maximalIdeal_discrete_finite hO k).1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hI : IsLocalRing.maximalIdeal O ^ k = Ideal.span {ϖ ^ k} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hπ : ϖ ^ k ≠ 0 := pow_ne_zero k hϖ.ne_zero
  generalize IsLocalRing.maximalIdeal O ^ k = I at hI hdisc
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hm' : cocycles2Map (twist ε O) (twist ε (O ⧸ I))
      (LinearMap.toSpanSingleton O (O ⧸ I) (Ideal.Quotient.mk I a)) (cont_span _ _)
      (span_twist ε _ _) z₀ ∈ (B2 (twist ε (O ⧸ I))).comap (Z2 (twist ε (O ⧸ I))).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 hm
  obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem _ _).1 hm'
  have hcf' : ∀ g h : G, (ε g : O) • c h - c (g * h) + c g =
      z₀.1 (g, h) • Ideal.Quotient.mk I a := fun g h => congrFun hcf (g, h)
  choose s hs using (Ideal.Quotient.mk_surjective (I := I))
  have hcs : Continuous (fun g => s (c g)) := continuous_of_discreteTopology.comp hc
  set u : G × G → O := fun q =>
    a * z₀.1 q - ((ε q.1 : O) * s (c q.2) - s (c (q.1 * q.2)) + s (c q.1)) with hu
  have huc : Continuous u :=
    (continuous_const.mul z₀.2.1).sub
      ((((hε.comp continuous_fst).mul (hcs.comp continuous_snd)).sub
        (hcs.comp (continuous_fst.mul continuous_snd))).add (hcs.comp continuous_fst))
  have hud : ∀ q, ϖ ^ k ∣ u q := by
    rintro ⟨g, h⟩
    rw [← Ideal.mem_span_singleton, ← hI, ← Ideal.Quotient.eq_zero_iff_mem]
    have e := hcf' g h
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at e
    simp only [hu, map_sub, map_add, map_mul, hs]
    rw [e]; ring
  obtain ⟨w, hwc, hw⟩ := exists_continuous_div hπ u huc hud
  have hwZ : w ∈ Z2 (twist ε O) := by
    refine ⟨hwc, fun g h l => ?_⟩
    apply mul_left_cancel₀ hπ
    have e : (ε g : O) * z₀.1 (h, l) - z₀.1 (g * h, l) + z₀.1 (g, h * l) - z₀.1 (g, h) = 0 :=
      z₀.2.2 g h l
    have e1 := hw (h, l)
    have e2 := hw (g * h, l)
    have e3 := hw (g, h * l)
    have e4 := hw (g, h)
    simp only [hu, map_mul, Units.val_mul, mul_assoc] at e1 e2 e3 e4
    show ϖ ^ k * ((ε g : O) * w (h, l) - w (g * h, l) + w (g, h * l) - w (g, h)) = ϖ ^ k * 0
    linear_combination a * e - (ε g : O) * e1 + e2 - e3 + e4
  obtain ⟨b, hb⟩ := hz.2 (Submodule.Quotient.mk ⟨w, hwZ⟩)
  have key : a • (Submodule.Quotient.mk z₀ : H2 (twist ε O)) =
      (ϖ ^ k * b) • (Submodule.Quotient.mk z₀ : H2 (twist ε O)) := by
    simp only at hb
    rw [mul_smul, hb, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.eq]
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨fun g => s (c g), hcs, funext fun q => ?_⟩
    have e := hw q
    show (ε q.1 : O) * s (c q.2) - s (c (q.1 * q.2)) + s (c q.1) = a * z₀.1 q - ϖ ^ k * w q
    rw [← e, hu]; ring
  have hab : a = ϖ ^ k * b := hz.1 key
  rw [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  exact ⟨b, hab⟩

end GlobalTheory.NatQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RangeLeRangeOfIsUnramifiedAt
section
open Polynomial IsLocalRing NumberField

namespace GlobalTheory.UnramifiedEmbedding

theorem algHom_eq_of_residue_eq {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing T] [Algebra R S] [Algebra R T] [Algebra.IsStandardEtale R S] {χ₁ χ₂ : S →ₐ[R] T}
    (h : ∀ s, residue T (χ₁ s) = residue T (χ₂ s)) : χ₁ = χ₂ := by
  obtain ⟨P⟩ : Nonempty (StandardEtalePresentation R S) := inferInstance
  refine P.hom_ext ?_
  have h₁ : P.P.HasMap (χ₁ P.x) := P.hasMap.map χ₁
  have h₂ : P.P.HasMap (χ₂ P.x) := P.hasMap.map χ₂
  set y := χ₁ P.x with hy
  set d := χ₂ P.x - y with hd
  have hdm : d ∈ maximalIdeal T := by
    rw [← residue_eq_zero_iff, hd, map_sub, hy, h, sub_self]
  obtain ⟨k, hk⟩ := binomExpansion (P.f.map (algebraMap R T)) y d
  have hu : IsUnit (aeval y (derivative P.f)) := h₁.isUnit_derivative_f
  rw [show y + d = χ₂ P.x by rw [hd]; ring, eval_map_algebraMap, eval_map_algebraMap,
    derivative_map, eval_map_algebraMap, h₂.1, h₁.1, zero_add] at hk
  have hu' : IsUnit (aeval y (derivative P.f) + k * d) := by
    by_contra hn
    have : aeval y (derivative P.f) + k * d - k * d ∈ maximalIdeal T :=
      Ideal.sub_mem _ ((mem_maximalIdeal _).2 hn) (Ideal.mul_mem_left _ _ hdm)
    rw [add_sub_cancel_right] at this
    exact (mem_maximalIdeal _).1 this hu
  have h0 : d * (aeval y (derivative P.f) + k * d) = 0 := by
    rw [hk]; ring
  have : d = 0 := (hu'.mul_left_eq_zero).1 h0
  rw [hd, sub_eq_zero] at this
  exact this.symm

end GlobalTheory.UnramifiedEmbedding

namespace GlobalTheory.UnramifiedEmbedding

theorem quotientMap_bijective {O S : Type*} [CommRing O] [IsLocalRing O] [CommRing S]
    [Algebra O S] [Algebra.IsIntegral O S] [IsAlgClosed (ResidueField O)] (M : Ideal S)
    [M.IsMaximal] (hM : M.comap (algebraMap O S) = maximalIdeal O) :
    Function.Bijective (Ideal.quotientMap M (algebraMap O S) hM.ge) := by
  letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  haveI : IsAlgClosed (O ⧸ maximalIdeal O) := ‹IsAlgClosed (ResidueField O)›
  letI : Field (S ⧸ M) := Ideal.Quotient.field _
  letI := (Ideal.quotientMap M (algebraMap O S) hM.ge).toAlgebra
  refine ⟨RingHom.injective _, fun x => ?_⟩
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hs : IsIntegral (O ⧸ maximalIdeal O) (Ideal.Quotient.mk M s) :=
    (Algebra.IsIntegral.isIntegral (R := O) s).map_of_comp_eq (Ideal.Quotient.mk _)
      (Ideal.Quotient.mk M) (Ideal.quotientMap_comp_mk _)
  exact minpoly.mem_range_of_degree_eq_one _ _
    (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hs))

theorem range_le_range_of_isUnramifiedAt
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [IsAlgClosed (ResidueField O)]
    (l : ℕ) [Fact l.Prime] (hl : (l : O) ∈ maximalIdeal O)
    (e : FractionRing O →+* ℂ)
    (K₀ L : Type) [Field K₀] [NumberField K₀] [Field L] [NumberField L] [Algebra K₀ L]
    (ι : K₀ →+* FractionRing O) (σ : L →+* ℂ) (hσ : σ.comp (algebraMap K₀ L) = e.comp ι)
    (hur : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], (l : 𝓞 L) ∈ P → Algebra.IsUnramifiedAt (𝓞 K₀) P) :
    σ.range ≤ e.range := by
  classical
  have hint : ∀ x : 𝓞 K₀, ∃ o : O, algebraMap O (FractionRing O) o = ι x := fun x =>
    IsIntegrallyClosed.isIntegral_iff.1
      (x.isIntegral_coe.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _))
  choose g₀ hg₀ using hint
  have hinj := IsFractionRing.injective O (FractionRing O)
  let ιO : 𝓞 K₀ →+* O :=
    { toFun := g₀
      map_one' := hinj (by simp [hg₀])
      map_mul' := fun x y => hinj (by simp [hg₀])
      map_zero' := hinj (by simp [hg₀])
      map_add' := fun x y => hinj (by simp [hg₀]) }
  have hιO : ∀ x, algebraMap O (FractionRing O) (ιO x) = ι x := hg₀
  letI : Algebra (𝓞 K₀) O := ιO.toAlgebra
  letI : Algebra O ℂ := (e.comp (algebraMap O (FractionRing O))).toAlgebra
  have hOC : ∀ o : O, algebraMap O ℂ o = e (algebraMap O (FractionRing O) o) := fun _ => rfl
  let S := integralClosure O ℂ
  have hOS : Function.Injective (algebraMap O S) := fun a b h => by
    have := congrArg (fun s : S => (s : ℂ)) h
    simp only [Subalgebra.coe_algebraMap, hOC] at this
    exact hinj (e.injective this)
  obtain ⟨M, hMmax, hMc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) (maximalIdeal O)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hOS]; exact bot_le)
  let σA : 𝓞 L →+* S := (σ.comp (algebraMap (𝓞 L) L)).codRestrict S fun a =>
    (a.isIntegral_coe.map_of_comp_eq (Int.castRingHom O) σ (RingHom.ext_int _ _) :)
  have hσA : ∀ a, (σA a : ℂ) = σ a := fun _ => rfl
  have hSR : ∀ r : 𝓞 K₀, σA (algebraMap (𝓞 K₀) (𝓞 L) r) = algebraMap O S (ιO r) := fun r => by
    apply Subtype.ext
    rw [hσA, Subalgebra.coe_algebraMap, hOC, hιO]
    exact congrArg (fun φ => φ (r : K₀)) hσ
  let P := M.comap σA
  have hlP : (l : 𝓞 L) ∈ P := by
    show σA l ∈ M
    rw [map_natCast, ← map_natCast (algebraMap O S), ← Ideal.mem_comap, hMc]
    exact hl
  haveI := hur P hlP
  haveI : Algebra.FinitePresentation (𝓞 K₀) (𝓞 L) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI : Module.Flat (𝓞 K₀) (𝓞 L) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 (by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨r, hr⟩, hrx⟩ := hx
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have : algebraMap (𝓞 K₀) (𝓞 L) r * x = 0 := by rw [← Algebra.smul_def]; exact hrx
    rcases mul_eq_zero.1 this with h | h
    · exact absurd ((FaithfulSMul.algebraMap_injective _ _) (h.trans (map_zero _).symm)) hr0
    · exact h)
  obtain ⟨f, hfP, hfU⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt (R := 𝓞 K₀) P
  haveI : Algebra.FinitePresentation (𝓞 K₀) (Localization.Away f) :=
    .trans _ (𝓞 L) _
  haveI : Module.Flat (𝓞 K₀) (Localization.Away f) := .trans _ (𝓞 L) _
  haveI : Algebra.Etale (𝓞 K₀) (Localization.Away f) := Algebra.Etale.of_formallyUnramified_of_flat
  haveI : Algebra.IsEtaleAt (𝓞 K₀) P :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.2 this
      (show (⟨P, inferInstance⟩ : PrimeSpectrum (𝓞 L)) ∈ PrimeSpectrum.basicOpen f from hfP)
  obtain ⟨g, hgP, hgE⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := 𝓞 K₀) P
  letI : Field (O ⧸ maximalIdeal O) := Ideal.Quotient.field _
  let q := Ideal.quotientMap M (algebraMap O S) hMc.ge
  have hq := quotientMap_bijective M hMc
  let qe := RingEquiv.ofBijective q hq
  let φ₀ : 𝓞 L →+* O ⧸ maximalIdeal O := qe.symm.toRingHom.comp ((Ideal.Quotient.mk M).comp σA)
  have hφ₀ : ∀ a, q (φ₀ a) = Ideal.Quotient.mk M (σA a) := fun a => qe.apply_symm_apply _
  have hφg : IsUnit (φ₀ g) := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hgP
    show σA g ∈ M
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφ₀, h0, map_zero]
  let φr : Localization.Away g →+* O ⧸ maximalIdeal O := IsLocalization.Away.lift g hφg
  have hφr : ∀ a, φr (algebraMap _ _ a) = φ₀ a := fun a => IsLocalization.lift_eq _ _
  let φ : Localization.Away g →ₐ[𝓞 K₀] O ⧸ maximalIdeal O :=
    { φr with
      commutes' := fun r => by
        change φr (algebraMap (𝓞 K₀) (Localization.Away g) r) = _
        rw [IsScalarTower.algebraMap_apply (𝓞 K₀) (𝓞 L) (Localization.Away g), hφr]
        apply hq.1
        rw [hφ₀, hSR]
        rfl }
  haveI := hgE
  obtain ⟨ψ, hψ⟩ := GlobalTheory.exists_algHom_lift_of_smooth (maximalIdeal O)
    (Ideal.Quotient.mkₐ (𝓞 K₀) (maximalIdeal O)) Ideal.Quotient.mk_surjective
    (fun b => Ideal.Quotient.eq_zero_iff_mem.symm) φ
  haveI := hMmax
  let T := Localization.AtPrime M
  letI : Algebra (𝓞 K₀) T := ((algebraMap S T).comp ((algebraMap O S).comp ιO)).toAlgebra
  have hgT : IsUnit ((algebraMap S T).comp σA g) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff T M (σA g)).2 hgP
  let χ₂r : Localization.Away g →+* T := IsLocalization.Away.lift g hgT
  have hχ₂r : ∀ a, χ₂r (algebraMap _ _ a) = algebraMap S T (σA a) := fun a =>
    IsLocalization.lift_eq _ _
  let χ₁ : Localization.Away g →ₐ[𝓞 K₀] T :=
    { (algebraMap S T).comp ((algebraMap O S).comp ψ.toRingHom) with
      commutes' := fun r => by
        change algebraMap S T (algebraMap O S (ψ (algebraMap _ _ r))) = _
        rw [ψ.commutes]; rfl }
  let χ₂ : Localization.Away g →ₐ[𝓞 K₀] T :=
    { χ₂r with
      commutes' := fun r => by
        change χ₂r (algebraMap (𝓞 K₀) (Localization.Away g) r) = _
        rw [IsScalarTower.algebraMap_apply (𝓞 K₀) (𝓞 L) (Localization.Away g), hχ₂r, hSR]
        rfl }
  have hres : ∀ a : 𝓞 L,
      algebraMap O S (ψ (algebraMap _ (Localization.Away g) a)) - σA a ∈ M := by
    intro a
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    have h1 := congrArg (fun φ' : Localization.Away g →ₐ[𝓞 K₀] _ => φ' (algebraMap _ _ a)) hψ
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h1
    change q (Ideal.Quotient.mk _ (ψ _)) = _
    rw [h1]
    change q (φr _) = _
    rw [hφr, hφ₀]
  have hχ : χ₁ = χ₂ := algHom_eq_of_residue_eq (fun s => by
    have : (residue T).comp χ₁.toRingHom = (residue T).comp χ₂.toRingHom := by
      refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
      simp only [RingHom.comp_apply]
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      change algebraMap S T _ - χ₂r (algebraMap _ _ a) ∈ _
      rw [hχ₂r, ← map_sub]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff T M _).2 (hres a)
    exact congrArg (fun j => j s) this)
  have hA : ∀ a : 𝓞 L,
      σ a = e (algebraMap O (FractionRing O) (ψ (algebraMap _ (Localization.Away g) a))) := by
    intro a
    have h := congrArg (fun χ : Localization.Away g →ₐ[𝓞 K₀] T => χ (algebraMap _ _ a)) hχ
    change algebraMap S T _ = χ₂r _ at h
    rw [hχ₂r] at h
    have h' := IsLocalization.injective T M.primeCompl_le_nonZeroDivisors h
    have h'' := congrArg (fun s : S => (s : ℂ)) h'
    simp only [Subalgebra.coe_algebraMap, hOC, hσA] at h''
    exact h''.symm
  rintro _ ⟨y, rfl⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) y
  refine ⟨algebraMap O _ (ψ (algebraMap _ (Localization.Away g) a)) /
    algebraMap O _ (ψ (algebraMap _ (Localization.Away g) b)), ?_⟩
  rw [map_div₀, map_div₀, ← hA, ← hA]

end GlobalTheory.UnramifiedEmbedding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShapeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_of_local_cohomology_shape : ReciprocityTheory.ChartRestriction.T2.JSpan := by
  first | exact @GlobalTheory.jSpan_holds | exact GlobalTheory.jSpan_holds | (intros; apply GlobalTheory.jSpan_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussNegOneEqOneStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableQuadraticGauss_neg_one_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ G₁ : ℂ, IsStableGauss A ψ x μ 1 G₁ → IsStableGauss A ψ x μ (-1) G₁ := by
  first | exact @GlobalTheory.JR.WeilQuad.stableGauss_neg_one | exact GlobalTheory.JR.WeilQuad.stableGauss_neg_one | (intros; apply GlobalTheory.JR.WeilQuad.stableGauss_neg_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPart
section
namespace GlobalTheory.WachSum

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

theorem sumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumPart l P H := by
  intro K s LL h
  exact GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumFor_of_crys fun _ _ _ i i' hs hT hT' =>
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_isSumLat i i' hT hT' hs

end GlobalTheory.WachSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableInvAbsNormPrimesOfNotPrimeNormStatement
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_inv_absNorm_primes_of_not_prime_norm : ∀ (K : Type) [Field K] [NumberField K], Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} => ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by
  first | exact @GlobalTheory.summable_inv_absNorm_of_not_prime | exact GlobalTheory.summable_inv_absNorm_of_not_prime | (intros; apply GlobalTheory.summable_inv_absNorm_of_not_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionShapeOfTorsionCountsStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_shape_of_torsion_counts : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {X : Type} [AddCommGroup X] [Module O X] (Hc : Submodule O X) (d a : ℕ)
    {F : Type} [AddCommGroup F] [Module O F] [Finite F], (Hc ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) →
    (∃ C : ℕ, ∀ n : ℕ, 0 < n →
      Nat.card (IsLocalRing.ResidueField O) ^ (n * d) ≤ Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ∧
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ≤ C * Nat.card (IsLocalRing.ResidueField O) ^ (n * d)) →
    Nat.card (LinearMap.ker (ϖ ^ 1 • LinearMap.id : Hc →ₗ[O] Hc)) ≤ Nat.card (IsLocalRing.ResidueField O) ^ (d + 1) →
    Formalism.RepresentationBoundsCohomology.JT.QuotShape Hc ⊥ d := by
  first | exact @GlobalTheory.ShapeNeg.Shape.quotShape_of_counts | exact GlobalTheory.ShapeNeg.Shape.quotShape_of_counts | (intros; apply GlobalTheory.ShapeNeg.Shape.quotShape_of_counts <;> assumption)
end

