import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem bijective_of_existsUnique_field_point {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) :
    Function.Bijective f := by
  constructor
  · intro x x' hx
    obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) x x' hx
    let p : Sp ((pullback f f).residueField z) ⟶ pullback f f :=
      (pullback f f).fromSpecResidueField z
    have e : p ≫ pullback.fst f f = p ≫ pullback.snd f f :=
      (h _ (p ≫ pullback.fst f f ≫ f)).unique (by simp) (by simp [pullback.condition])
    let a : Sp ((pullback f f).residueField z) := IsLocalRing.closedPoint _
    have ha : p a = z := Scheme.fromSpecResidueField_apply z a
    have e' : (p ≫ pullback.fst f f) a = (p ≫ pullback.snd f f) a := by rw [e]
    rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ha, hz, hz'] at e'
  · intro t
    obtain ⟨z, hz, -⟩ := h (T.residueField t) (T.fromSpecResidueField t)
    let a : Sp (T.residueField t) := IsLocalRing.closedPoint _
    refine ⟨z a, ?_⟩
    rw [← Scheme.Hom.comp_apply, hz]
    exact Scheme.fromSpecResidueField_apply t a

theorem existsUnique_field_point_morphismRestrict {S T : Scheme.{0}} (f : S ⟶ T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) (V : T.Opens)
    (k : Type) [Field k] (w : Sp k ⟶ V) : ∃! z : Sp k ⟶ (f ⁻¹ᵁ V), z ≫ (f ∣_ V) = w := by
  obtain ⟨z, hz, hu⟩ := h k (w ≫ V.ι)
  have P := (isPullback_morphismRestrict f V).flip
  refine ⟨P.lift z w hz, P.lift_snd _ _ _, fun y hy ↦ ?_⟩
  apply P.hom_ext
  · rw [P.lift_fst]
    apply hu
    show (y ≫ _) ≫ f = _
    rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy]
  · rw [P.lift_snd]; exact hy

theorem isIso_stalkMap_genericPoint_of_lift {S T : Scheme.{0}} (f : S ⟶ T) [IsIntegral S]
    [IsIntegral T] [IsDominant f] (hf : Function.Injective f)
    (z : Spec T.functionField ⟶ S) (hz : z ≫ f = T.fromSpecStalk (genericPoint T)) :
    IsIso (f.stalkMap (genericPoint S)) := by
  have hs : z (IsLocalRing.closedPoint _) = genericPoint S := by
    apply hf
    rw [apply_genericPoint_of_isDominant f]
    refine (Scheme.Hom.comp_apply z f _).symm.trans ?_
    rw [hz]
    exact Scheme.fromSpecStalk_closedPoint
  have hF : IsField (S.presheaf.stalk (z (IsLocalRing.closedPoint _))) := by
    rw [hs]; exact Field.toIsField S.functionField
  rw [← hs]
  have h1 : IsIso (Scheme.stalkClosedPointTo (z ≫ f)) := by
    rw [hz, Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  rw [Scheme.stalkClosedPointTo_comp] at h1
  have h2 : IsIso (Scheme.stalkClosedPointTo z) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · letI := hF.toField
      exact (Scheme.stalkClosedPointTo z).hom.injective
    · intro y
      obtain ⟨x, hx⟩ := (@ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ _ h1).2 y
      exact ⟨_, hx⟩
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (Scheme.stalkClosedPointTo z) h2 h1

theorem isIso_of_isProper_of_existsUnique_field_point_of_isIntegral {S T : Scheme.{0}} (f : S ⟶ T)
    [IsProper f] [IsReduced S] [IsIntegral T] [GlobalTheory.IsNormalScheme T]
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by
  have hb := bijective_of_existsUnique_field_point f h
  have hh : IsHomeomorph f :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨f.continuous, f.isClosedMap, hb⟩
  have : IrreducibleSpace S := hh.homeomorph.symm.irreducibleSpace_iff.mp inferInstance
  have : IsIntegral S := isIntegral_of_irreducibleSpace_of_isReduced S
  have : IsDominant f := ⟨hb.2.denseRange⟩
  have : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f
    fun t ↦ (Set.finite_singleton t).preimage hb.1.injOn
  obtain ⟨z, hz, -⟩ := h T.functionField (T.fromSpecStalk (genericPoint T))
  have := isIso_stalkMap_genericPoint_of_lift f hb.1 z hz
  exact isIso_of_isProper_of_quasiFinite_of_isIso_stalkMap f fun _ ↦ inferInstance

theorem isIso_of_isProper_of_existsUnique_field_point (S T : Scheme.{0}) (f : S ⟶ T)
    (hf : IsProper f) (hS : IsReduced S) (hT : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme T)
    (hN : IsLocallyNoetherian T)
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ T), ∃! z : Sp k ⟶ S, z ≫ f = w) : IsIso f := by
  have := GlobalTheory.IsNormalScheme.of_pred hT
  refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _)
    GlobalTheory.IsNormalScheme.component (GlobalTheory.IsNormalScheme.iSup_component T)).mpr fun Z ↦ ?_
  exact isIso_of_isProper_of_existsUnique_field_point_of_isIntegral
    (f ∣_ GlobalTheory.IsNormalScheme.component Z) (existsUnique_field_point_morphismRestrict f h _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
section
open IsLocalRing

namespace GlobalTheory.AdicNoeth

theorem isNoetherianRing_adicCompletion : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    IsNoetherianRing (AdicCompletion I R) := by
  intro R _ _ I
  have fg : I.FG := I.fg_of_isNoetherianRing
  have hc := AdicCompletion.isAdicComplete_self I fg
  have e : (AdicCompletion I R ⧸ I.map (algebraMap R (AdicCompletion I R))) ≃+* R ⧸ I := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I fg]
    exact RingHom.quotientKerEquivOfSurjective (AdicCompletion.evalOneₐ_surjective I)
  exact isNoetherianRing_of_isAdicComplete _ _ (fg.map _) hc
    (isNoetherianRing_of_ringEquiv _ e.symm)

end GlobalTheory.AdicNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeThetaAsymptotics
section
open Complex Filter Asymptotics
open scoped RealInnerProductSpace

namespace GlobalTheory.PlaneTheta

theorem exists_pos_le_of_summable {ι : Type*} {q : ι → ℝ}
    (h : Summable fun i => Real.exp (-q i)) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, 0 < q i → δ ≤ q i := by
  have h1 := h.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-1)))
  rw [Filter.eventually_cofinite] at h1
  have h2 : {i | ¬ Real.exp (-q i) < Real.exp (-1) ∧ 0 < q i}.Finite := h1.subset fun i hi => hi.1
  have h3 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ i ∈ {i | ¬ Real.exp (-q i) < Real.exp (-1) ∧ 0 < q i}, δ < q i :=
    (Filter.eventually_all_finite h2).2 fun i hi => nhdsWithin_le_nhds (gt_mem_nhds hi.2)
  have h4 : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  obtain ⟨δ, ⟨h5, h6⟩, h7⟩ := ((h3.and h4).and self_mem_nhdsWithin).exists
  refine ⟨δ, h7, fun i hi => ?_⟩
  by_cases hc : Real.exp (-q i) < Real.exp (-1)
  · rw [Real.exp_lt_exp] at hc
    linarith
  · exact (h5 i ⟨hc, hi⟩).le

theorem abs_tsum_le {ι : Type*} {q f : ι → ℝ} {δ s : ℝ} (hs : 1 ≤ s)
    (h : Summable fun i => Real.exp (-q i)) (hf : ∀ i, |f i| ≤ Real.exp (-(s * q i)))
    (hδ : ∀ i, f i ≠ 0 → δ ≤ q i) :
    |∑' i, f i| ≤ (Real.exp δ * ∑' i, Real.exp (-q i)) * Real.exp (-δ * s) := by
  have hb : ∀ i, ‖f i‖ ≤ Real.exp δ * Real.exp (-q i) * Real.exp (-δ * s) := by
    intro i
    by_cases h0 : f i = 0
    · rw [h0, norm_zero]; positivity
    · refine (hf i).trans ?_
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [hδ i h0]
  have := tsum_of_norm_bounded ((h.hasSum.mul_left (Real.exp δ)).mul_right (Real.exp (-δ * s))) hb
  exact this

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
theorem atTop_bound (u : E) (hu : ∀ x : L, (x : E) + u ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' x : L, Real.exp (-Real.pi * t * ‖(x : E) + u‖ ^ 2))
      =O[atTop] (fun t => Real.exp (-c * t)) := by
  have h : Summable fun x : L => Real.exp (-(Real.pi * ‖(x : E) + u‖ ^ 2)) := by
    simpa only [neg_mul] using summable_lattice_exp_neg_mul_norm_add_sq L Real.pi_pos u
  obtain ⟨δ, hδ, hq⟩ := exists_pos_le_of_summable h
  refine ⟨δ, hδ, IsBigO.of_bound (Real.exp δ * ∑' x : L, Real.exp (-(Real.pi * ‖(x : E) + u‖ ^ 2))) ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  refine abs_tsum_le ht h (fun x => ?_) (fun x _ => hq x ?_)
  · rw [abs_of_pos (Real.exp_pos _)]
    apply le_of_eq; congr 1; ring
  · have := norm_pos_iff.2 (hu x)
    have := Real.pi_pos
    positivity

theorem zero_bound (hE : Module.finrank ℝ E = 2) (u : E) :
    ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => (∑' x : L, Real.exp (-Real.pi * t * ‖(x : E) + u‖ ^ 2))
      - 1 / (t * ZLattice.covolume L))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  classical
  have h : Summable fun y : dualLattice L => Real.exp (-(Real.pi * ‖(y : E)‖ ^ 2)) := by
    simpa only [neg_mul] using summable_lattice_exp_neg_mul_norm_sq (dualLattice L) Real.pi_pos
  obtain ⟨δ, hδ, hq⟩ := exists_pos_le_of_summable h
  have hV := ZLattice.covolume_pos L MeasureTheory.volume
  set C := Real.exp δ * ∑' y : dualLattice L, Real.exp (-(Real.pi * ‖(y : E)‖ ^ 2)) with hC
  have hC0 : 0 ≤ C := mul_nonneg (Real.exp_pos _).le (tsum_nonneg fun _ => (Real.exp_pos _).le)
  refine ⟨δ / 2, by positivity, IsBigO.of_bound ((ZLattice.covolume L)⁻¹ * (2 / δ) * C) ?_⟩
  have h4 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds one_pos)
  filter_upwards [h4, self_mem_nhdsWithin] with t ht1 ht
  have ht : 0 < t := ht
  obtain ⟨h1, h2⟩ := poisson_gaussian_lattice_cos L ht u
  rw [h2, h1.tsum_eq_add_tsum_ite 0, hE]
  have hs : 1 ≤ t⁻¹ := (one_le_inv₀ ht).2 ht1.le
  have h5 := abs_tsum_le (δ := δ) (f := fun y : dualLattice L => if y = 0 then 0 else
      Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * Real.pi * ⟪(y : E), u⟫)) hs h
      (fun y => ?_) (fun y hy => hq y ?_)
  · generalize (∑' y : dualLattice L, if y = 0 then 0 else
      Real.exp (-Real.pi * ‖(y : E)‖ ^ 2 / t) * Real.cos (2 * Real.pi * ⟪(y : E), u⟫)) = S at h5 ⊢
    rw [← hC] at h5
    have h6 : t ^ (-(((2 : ℕ) : ℝ) / 2)) = t⁻¹ := by
      rw [← Real.rpow_neg_one]; norm_num
    rw [h6]
    have h7 : (ZLattice.covolume L)⁻¹ * t⁻¹ * (Real.exp (-Real.pi * ‖((0 : dualLattice L) : E)‖ ^ 2 / t) *
        Real.cos (2 * Real.pi * ⟪((0 : dualLattice L) : E), u⟫) + S) - 1 / (t * ZLattice.covolume L)
        = (ZLattice.covolume L)⁻¹ * t⁻¹ * S := by
      simp only [ZeroMemClass.coe_zero, norm_zero, inner_zero_left]
      simp
      ring
    rw [h7, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity)]
    have h8 : t⁻¹ ≤ 2 / δ * Real.exp (δ / 2 * t⁻¹) := by
      have := Real.add_one_le_exp (δ / 2 * t⁻¹)
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      nlinarith
    calc (ZLattice.covolume L)⁻¹ * t⁻¹ * |S|
        ≤ (ZLattice.covolume L)⁻¹ * (2 / δ * Real.exp (δ / 2 * t⁻¹)) * (C * Real.exp (-δ * t⁻¹)) := by
          gcongr
      _ = (ZLattice.covolume L)⁻¹ * (2 / δ) * C * (Real.exp (δ / 2 * t⁻¹) * Real.exp (-δ * t⁻¹)) := by
          ring
      _ = (ZLattice.covolume L)⁻¹ * (2 / δ) * C * Real.exp (-(δ / 2) / t) := by
          rw [← Real.exp_add]; congr 2; ring
  · split_ifs
    · rw [abs_zero]; positivity
    · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      refine (mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)).trans ?_
      apply le_of_eq; congr 1; ring
  · have hy0 : y ≠ 0 := fun h0 => hy (if_pos h0)
    have : 0 < ‖(y : E)‖ := norm_pos_iff.2 (by simpa using hy0)
    have := Real.pi_pos
    positivity

end Lattice

theorem covolume_lattice (L : PeriodPair) :
    ZLattice.covolume L.lattice = |(starRingEnd ℂ L.ω₁ * L.ω₂).im| := by
  rw [ZLattice.covolume_eq_det_mul_measureReal _ _ L.latticeBasis Complex.orthonormalBasisOneI.toBasis,
    MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
    MeasureTheory.Measure.real, OrthonormalBasis.coe_toBasis,
    Complex.orthonormalBasisOneI.volume_parallelepiped, ENNReal.toReal_one, _root_.mul_one]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply]
  ring

theorem theta_asymptotics : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ c : ℝ, 0 < c ∧ (fun t : ℝ => ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) =O[atTop] (fun t => Real.exp (-c * t)) ∧ (fun t : ℝ => (∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2)) - 1 / (t * |(starRingEnd ℂ w₁ * w₂).im|)) =O[nhdsWithin 0 (Set.Ioi 0)] (fun t => Real.exp (-c / t)) := by
  intro w₁ w₂ x₀ hw hx
  let L : PeriodPair := ⟨w₁, w₂, by
    rw [LinearIndependent.pair_iff]
    intro s t e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 hw
    constructor
    · apply mul_left_cancel₀ hw
      linear_combination w₂.im * e1 - w₂.re * e2
    · apply mul_left_cancel₀ hw
      linear_combination w₁.re * e2 - w₁.im * e1⟩
  have hsum : ∀ t : ℝ, ∑' p : ℤ × ℤ, Real.exp (-Real.pi * t * ‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2) =
      ∑' x : L.lattice, Real.exp (-Real.pi * t * ‖(x : ℂ) + x₀‖ ^ 2) := by
    intro t
    rw [← L.latticeEquivProd.symm.toEquiv.tsum_eq]
    refine tsum_congr fun p => ?_
    have := L.latticeEquiv_symm_apply p
    have e : ((L.latticeEquivProd.symm.toEquiv p : L.lattice) : ℂ) + x₀
        = x₀ + p.1 * w₁ + p.2 * w₂ := by
      change (L.latticeEquivProd.symm p).1 + x₀ = _
      rw [this]
      ring
    rw [e]
  have hu : ∀ x : L.lattice, (x : ℂ) + x₀ ≠ 0 := by
    intro x h
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 x.2
    apply hx m n
    rw [← h, ← hmn]
    ring
  obtain ⟨c₁, hc₁, h₁⟩ := atTop_bound L.lattice x₀ hu
  obtain ⟨c₂, hc₂, h₂⟩ := zero_bound L.lattice Complex.finrank_real_complex x₀
  rw [covolume_lattice] at h₂
  simp only [hsum]
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, h₁.trans (IsBigO.of_bound' ?_), h₂.trans (IsBigO.of_bound' ?_)⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_exp]
    nlinarith [min_le_left c₁ c₂]
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : 0 < t := ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.exp_le_exp]
    gcongr
    exact min_le_right _ _

end GlobalTheory.PlaneTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationAtPrimeIsDiscreteValuationRingOfHeigStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDiscreteValuationRing_localization_of_height_eq_one' : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime], q.height = 1 → IsDiscreteValuationRing (Localization.AtPrime q) := by
  first | exact @GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one | exact GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one | (intros; apply GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
section
set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace GlobalTheory.UnifDens

theorem measurePreserving_comp_equiv {κ : Type} [Fintype κ] {n : ℕ} (e : κ ≃ Fin n) :
    MeasurePreserving (fun x : Fin n → ℂ => fun i : κ => x (e i)) volume volume := by
  have := MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : κ => ℂ) e.symm
  convert this using 1
  funext x i
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ => ℂ) e.symm x (e i)
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm

variable {ι : Type} [Fintype ι] {p q n : ℕ}

def flatL (h : Fintype.card (ι × Fin p × Fin q) = n) : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (ι × Fin p × Fin q → ℂ) :=
  (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq h)).toContinuousLinearEquiv

theorem flatL_mp (h : Fintype.card (ι × Fin p × Fin q) = n) :
    MeasurePreserving (flatL h) volume volume := by
  let E' : (Fin n → ℂ) ≃ᵐ ReciprocityTheory.L2DbarEstimates.V n :=
    (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).symm.toHomeomorph.toMeasurableEquiv
  have h1 : MeasurePreserving E' volume volume := GlobalTheory.measurePreserving_toLp_complex
  have h2 : MeasurePreserving E'.symm volume volume := h1.symm
  exact (measurePreserving_comp_equiv (Fintype.equivFinOfCardEq h)).comp h2

end GlobalTheory.UnifDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalLocalIsLocalisationOfFiniteOverPolynomialA
section
open IsLocalRing

namespace GlobalTheory.QFNN

theorem integralClosure_of_fractions (P A : Type) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [CharZero P] [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsIntegrallyClosed A] [Algebra P A] [Algebra.EssFiniteType P A]
    (hinj : Function.Injective (algebraMap P A))
    (hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b) :
    Module.Finite P (integralClosure P A) ∧ IsIntegrallyClosed (integralClosure P A) ∧
      Function.Injective (algebraMap P (integralClosure P A)) ∧
      IsLocalization.AtPrime A
        ((maximalIdeal A).comap (algebraMap (integralClosure P A) A)) := by
  let K := FractionRing A
  let F := FractionRing P
  let B := integralClosure P A
  have hιinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hPK : Function.Injective (algebraMap P K) := by
    rw [IsScalarTower.algebraMap_eq P A K]
    exact hιinj.comp hinj
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr hPK
  letI : Algebra F K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P F K := FractionRing.isScalarTower_liftAlgebra P K

  have halgA : ∀ a : A, IsAlgebraic P (algebraMap A K a) := by
    intro a
    obtain ⟨b, t, hb, ht, hu, hab⟩ := hloc a
    have ht0 : algebraMap A K t ≠ 0 := by
      simpa using (map_ne_zero_iff _ hιinj).mpr hu.ne_zero
    have : algebraMap A K a = algebraMap A K b * (algebraMap A K t)⁻¹ := by
      rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ ht0, mul_one]
    rw [this]
    exact (hb.algebraMap (B := K)).isAlgebraic.mul (ht.algebraMap (B := K)).isAlgebraic.inv
  haveI hPKalg : Algebra.IsAlgebraic P K := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, s, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [div_eq_mul_inv]
    exact (halgA a).mul (halgA s).inv
  haveI : Algebra.IsAlgebraic F K := (IsFractionRing.comap_isAlgebraic_iff (A := P) (K := F)).mp hPKalg
  haveI : Algebra.EssFiniteType A K := .of_isLocalization K (nonZeroDivisors A)
  haveI : Algebra.EssFiniteType P K := .comp P A K
  haveI : Algebra.EssFiniteType F K := .of_comp P F K
  haveI : FiniteDimensional F K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective P F)
  haveI hic : IsIntegralClosure B P K :=
    { algebraMap_injective := hιinj.comp Subtype.val_injective
      isIntegral_iff := by
        intro x
        constructor
        · intro hx
          obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := A))
          have ha : IsIntegral P a := (isIntegral_algebraMap_iff hιinj).mp hx
          exact ⟨⟨a, ha⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact (y.2.algebraMap (B := K)) }
  haveI hfrac : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension P F K B
  refine ⟨IsIntegralClosure.finite P F K B, ?_, ?_, ?_⟩
  · refine (isIntegrallyClosed_iff K).mpr ?_
    intro x hx
    have hxP : IsIntegral P x := isIntegral_trans x hx
    exact (IsIntegralClosure.isIntegral_iff (A := B)).mp hxP
  · intro x y h
    exact hinj (congrArg Subtype.val h)
  · have hne : ∀ b : B, b ∈ ((maximalIdeal A).comap (algebraMap B A)).primeCompl →
        IsUnit (algebraMap B A b) := by
      intro b hb
      by_contra hu
      exact hb ((mem_maximalIdeal _).mpr hu)
    refine ⟨fun y => hne y.1 y.2, fun a => ?_, fun {x y} h => ⟨1, ?_⟩⟩
    · obtain ⟨b, t, hb, ht, hu, hab⟩ := hloc a
      refine ⟨(⟨b, hb⟩, ⟨⟨t, ht⟩, ?_⟩), hab⟩
      intro hmem
      exact (mem_maximalIdeal _).mp hmem hu
    · have : x = y := Subtype.val_injective h
      rw [this]

end GlobalTheory.QFNN

theorem GlobalTheory.normal_local_is_localisation_of_finite_over_polynomial :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A]
      [Algebra.EssFiniteType ℤ A], ∃ (r : ℕ) (B : Type) (_ : CommRing B) (_ : IsDomain B)
      (_ : IsIntegrallyClosed B) (_ : Algebra (MvPolynomial (Fin r) ℤ) B)
      (_ : Module.Finite (MvPolynomial (Fin r) ℤ) B) (_ : Algebra B A) (𝔫 : Ideal B) (_ : 𝔫.IsPrime),
      Function.Injective (algebraMap (MvPolynomial (Fin r) ℤ) B) ∧ IsLocalization.AtPrime A 𝔫 := by
  intro A _ _ _ _ _ hess
  obtain ⟨S₀, M, hft, hlocM⟩ := (Algebra.essFiniteType_iff_exists_subalgebra ℤ A).mp hess
  let 𝔮 : Ideal S₀ := (maximalIdeal A).comap (algebraMap S₀ A)
  haveI h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  have hunit : ∀ s : S₀, s ∉ 𝔮 → IsUnit (algebraMap S₀ A s) := by
    intro s hs
    by_contra hu
    exact hs ((mem_maximalIdeal _).mpr hu)
  have hM : M ≤ 𝔮.primeCompl := by
    intro m hm hmem
    exact (mem_maximalIdeal _).mp hmem (IsLocalization.map_units A ⟨m, hm⟩)
  haveI hat : IsLocalization 𝔮.primeCompl A :=
    IsLocalization.of_le M _ hM (fun s hs => hunit s hs)
  haveI : CharZero S₀ := (algebraMap S₀ A).charZero
  obtain ⟨r, y, hy, hqf⟩ := GlobalTheory.T.exists_quasi_finite_polynomial_map S₀ 𝔮
  let P := MvPolynomial (Fin r) ℤ
  letI algPS : Algebra P S₀ := (MvPolynomial.aeval y : P →ₐ[ℤ] S₀).toRingHom.toAlgebra
  letI algPA : Algebra P A := ((algebraMap S₀ A).comp (algebraMap P S₀)).toAlgebra
  haveI : IsScalarTower P S₀ A := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ P S₀ := .of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : IsScalarTower ℤ P A := .of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : Algebra.FiniteType P S₀ := .of_restrictScalars_finiteType ℤ P S₀
  haveI : Algebra.EssFiniteType P A := .of_comp ℤ P A
  have hinj : Function.Injective (algebraMap P A) :=
    (Subtype.val_injective : Function.Injective (algebraMap S₀ A)).comp
      ((algebraicIndependent_iff_injective_aeval).mp hy)
  have hzmp : Algebra.ZariskisMainProperty P 𝔮 := Algebra.ZariskisMainProperty.of_finiteType 𝔮
  obtain ⟨ρ, hρq, hρ, H⟩ := Algebra.zariskisMainProperty_iff.mp hzmp
  have hloc : ∀ a : A, ∃ b t : A, IsIntegral P b ∧ IsIntegral P t ∧ IsUnit t ∧ a * t = b := by
    intro a
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj 𝔮.primeCompl a
    obtain ⟨m₁, h₁⟩ := H x
    obtain ⟨m₂, h₂⟩ := H s
    have hb : IsIntegral P (ρ ^ (m₁ + m₂) * x) := by
      have : ρ ^ (m₁ + m₂) * x = ρ ^ m₂ * (ρ ^ m₁ * x) := by ring
      rw [this]
      exact (hρ.pow _).mul h₁
    have ht : IsIntegral P (ρ ^ (m₁ + m₂) * (s : S₀)) := by
      have : ρ ^ (m₁ + m₂) * (s : S₀) = ρ ^ m₁ * (ρ ^ m₂ * (s : S₀)) := by ring
      rw [this]
      exact (hρ.pow _).mul h₂
    refine ⟨_, _, hb.algebraMap (B := A), ht.algebraMap (B := A), hunit _ ?_, ?_⟩
    · exact h𝔮.mul_notMem (fun h => hρq (h𝔮.mem_of_pow_mem _ h)) s.2
    · simp only [map_mul, map_pow]
      rw [← hxs]
      ring
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.QFNN.integralClosure_of_fractions P A hinj hloc
  exact ⟨r, integralClosure P A, inferInstance, inferInstance, h2, inferInstance, h1, inferInstance,
    _, Ideal.comap_isPrime _ _, h3, h4⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageGenericFiberIsOpenStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_generic_fiber_isOpen : ∀ (O K R : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing R] [IsLocalRing R] (g : Sp R ⟶ Sp O), IsOpen (g ⁻¹' Set.range (spMap (algebraMap O K))) := by
  first | exact @GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction | exact GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction | (intros; apply GlobalTheory.GenericFibreOpen.isOpen_preimage_range_spMap_fraction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayDataNonemptyStatement
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_data_nonempty : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → Nonempty (RayData K M) := by
  first | exact @GlobalTheory.Mem.RayEx.nonempty_rayData | exact GlobalTheory.Mem.RayEx.nonempty_rayData | (intros; apply GlobalTheory.Mem.RayEx.nonempty_rayData <;> assumption)
end

