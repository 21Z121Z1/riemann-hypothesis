import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumLengthMulLogCardEqNegLogAdicAbvNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0325
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0324
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0335
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LowerTieTwAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Formalism.LocalToGlobal.Columns.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroLevelTypePrimeOrientationFramesFunctiona
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaOrder
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.PlaceFormula

theorem coheight_eq_one {Z : Scheme.{0}} [IsIntegral Z] (hd : topologicalKrullDim Z = 1) {z : Z}
    (hz : z ≠ genericPoint Z) : Order.coheight z = 1 := by
  have hg (w : Z) : w ≤ genericPoint Z := genericPoint_specializes w
  refine le_antisymm ((Order.coheight_le_coe_iff (n := 1)).2 fun y hy => ?_) (Order.one_le_iff_ne_zero.2 fun h => ?_)
  · have h1 : y = genericPoint Z := by
      by_contra h
      have h2 : y ⤳ z := hy.le
      have h3 := (SmallSecHeight.isClosed_of_ne hd h).closure_eq ▸ specializes_iff_mem_closure.1 h2
      exact hy.ne h3
    have h2 : Order.coheight y = 0 := Order.coheight_eq_zero.2 fun w _ => h1 ▸ hg w
    simp [h2]
  · have h1 : z ⤳ genericPoint Z := Order.coheight_eq_zero.1 h (hg z)
    exact hz (h1.antisymm (genericPoint_specializes z)).eq

theorem spec_appTop {K : CommRingCat.{0}} {Z : Scheme.{0}} [IsAffine Z] (y : Spec K ⟶ Z) :
    Spec.map (y.appTop ≫ (Scheme.ΓSpecIso K).hom) ≫ (isAffineOpen_top Z).fromSpec = y := by
  rw [IsAffineOpen.fromSpec_top, Spec.map_comp, ← Scheme.isoSpec_Spec_hom, Scheme.isoSpec_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem fromSpec_comp {k : CommRingCat.{0}} {Z : Scheme.{0}} [IsAffine Z] (q : Z ⟶ Spec k) :
    (isAffineOpen_top Z).fromSpec ≫ q = Spec.map ((Scheme.ΓSpecIso k).inv ≫ q.appTop) := by
  rw [IsAffineOpen.fromSpec_top, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]

theorem valAt_spec {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] [IsAffine Z] (ψ : Γ(Z, ⊤) ⟶ CommRingCat.of K)
    (a : Γ(Z, ⊤)) :
    valAt (K := K) (Spec.map ψ ≫ (isAffineOpen_top Z).fromSpec) (fnOf ⊤ trivial a) = ψ.hom a := by
  have h := Spec.map_injective ((cancel_mono _).1 (spec_appTop (Spec.map ψ ≫ (isAffineOpen_top Z).fromSpec)))
  rw [OfModel.valAt_fnOf (U := ⊤) _ trivial le_rfl]
  conv_rhs => rw [← h]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem injective_of_charZero {F R : Type} [Field F] [NumberField F] [CommRing R] [CharZero R] (φ : 𝓞 F →+* R) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => ?_)
  simpa [RingHom.mem_ker] using hn

set_option maxHeartbeats 400000 in

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (t : Z.functionFieldˣ),
    ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal),
      (Scheme.ord (t : Z.functionField) z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
    -∑ᶠ y : {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))},
      Real.log (e.w (valAt y.1 (t : Z.functionField))) := by
  intro F _ _ Z _ _ q hZ v e t
  have := GlobalTheory.ArithCurveFinite.isFinite _ Z q hZ
  have : IsAffine Z := isAffine_of_isAffineHom q
  have hU := isAffineOpen_top Z
  have := hZ.charZero
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  let φ : CommRingCat.of (𝓞 F) ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso _).inv ≫ q.appTop
  have hq : hU.fromSpec ≫ q = Spec.map φ := fromSpec_comp q
  let : Algebra (𝓞 F) Γ(Z, ⊤) := φ.hom.toAlgebra
  have hbij : Function.Bijective hU.fromSpec := by
    refine ⟨hU.fromSpec.isOpenEmbedding.injective, fun z => ?_⟩
    have : z ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; trivial
    exact this
  have : Module.Finite (𝓞 F) Γ(Z, ⊤) := (IsFinite.SpecMap_iff φ).1 (by
    rw [← hq, IsAffineOpen.fromSpec_top]; infer_instance)
  have := functionField_isFractionRing_of_isAffineOpen Z ⊤ hU
  have hφ : Function.Injective (algebraMap (𝓞 F) Γ(Z, ⊤)) := injective_of_charZero _
  have := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have hi : Function.Injective ((algebraMap Γ(Z, ⊤) Z.functionField).comp (algebraMap (𝓞 F) Γ(Z, ⊤))) :=
    (IsFractionRing.injective _ _).comp hφ
  let : Algebra F Z.functionField := (IsFractionRing.lift hi).toAlgebra
  have : IsScalarTower (𝓞 F) Γ(Z, ⊤) Z.functionField :=
    .of_algebraMap_eq fun a => IsFractionRing.lift_algebraMap (K := F) hi a
  have : Module.Finite F Z.functionField := Module.Finite.of_isLocalization (𝓞 F) Γ(Z, ⊤) (nonZeroDivisors _)

  let P (τ : Z.functionField →ₐ[F] AlgebraicClosure F) :
      {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))} :=
    ⟨Spec.map (CommRingCat.ofHom (τ.toRingHom.comp (algebraMap Γ(Z, ⊤) Z.functionField))) ≫ hU.fromSpec, by
      rw [Category.assoc, hq, ← Spec.map_comp]
      congr 1
      ext a
      change τ (algebraMap Γ(Z, ⊤) _ (algebraMap (𝓞 F) _ a)) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 F) F, τ.commutes]
      rfl⟩
  have hP : Function.Bijective P := by
    refine ⟨fun τ τ' h => ?_, fun y => ?_⟩
    · have h1 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 (congrArg Subtype.val h)))
      exact AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors Γ(Z, ⊤)) h1)
    · obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ(Z, ⊤) ⟶ CommRingCat.of (AlgebraicClosure F), Spec.map ψ ≫ hU.fromSpec = y.1 :=
        ⟨_, spec_appTop y.1⟩
      have h1 := y.2
      rw [← hψ, Category.assoc, hq, ← Spec.map_comp] at h1
      have h2 (a : 𝓞 F) : ψ.hom (algebraMap _ _ a) = algebraMap _ _ a :=
        congrArg (fun f => f.hom a) (Spec.map_injective h1)
      have h3 : Function.Injective ψ.hom := by
        rw [RingHom.injective_iff_ker_eq_bot]
        refine Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 F) (eq_bot_iff.2 fun a ha => ?_)
        rw [Ideal.mem_comap, RingHom.mem_ker, h2] at ha
        exact injective_of_charZero (algebraMap (𝓞 F) (AlgebraicClosure F)) (ha.trans (map_zero _).symm)
      have h4 : (IsFractionRing.lift (K := Z.functionField) h3).comp (algebraMap F _) = algebraMap F _ :=
        IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) (RingHom.ext fun a => by
          simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
          rw [IsScalarTower.algebraMap_apply (𝓞 F) Γ(Z, ⊤), IsFractionRing.lift_algebraMap, h2])
      refine ⟨⟨IsFractionRing.lift h3, fun a => congrArg (fun f => f a) h4⟩, Subtype.ext ?_⟩
      rw [← hψ]
      exact congrArg (fun f => Spec.map f ≫ hU.fromSpec)
        (CommRingCat.hom_ext (RingHom.ext fun a =>
          IsFractionRing.lift_algebraMap (K := Z.functionField) h3 a))
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(Z, ⊤)) (t : Z.functionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap _ Z.functionField b ≠ 0 := by simpa using hb0
  have hab' : algebraMap _ Z.functionField a = t * algebraMap _ _ b := by rw [← hab, div_mul_cancel₀ _ hb1]
  have ha1 : algebraMap _ Z.functionField a ≠ 0 := hab' ▸ mul_ne_zero t.ne_zero hb1
  have ha0 : a ≠ 0 := by simpa using ha1
  have hval (τ) : valAt (P τ).1 (t : Z.functionField) = τ t := by
    have hg : below (P τ).1 = genericPoint Z :=
      SmallSecHeight.eq_genericPoint hZ (Scheme.SpecToEquivOfField _ Z (P τ).1).2.hom.charZero
    have h1 (c : Γ(Z, ⊤)) : valAt (P τ).1 (algebraMap _ Z.functionField c) = τ (algebraMap _ _ c) := valAt_spec _ c
    have h2 := h1 a
    rw [hab', OfModel.valAt_mul _ (hg ▸ regAt_genericPoint _) (hg ▸ regAt_genericPoint _), h1, map_mul] at h2
    exact mul_right_cancel₀ ((map_ne_zero τ).2 hb1) h2
  have hR : ∑ᶠ y : {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))},
      Real.log (e.w (valAt y.1 (t : Z.functionField))) =
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F (t : Z.functionField))) := by
    rw [← finsum_eq_of_bijective P hP (f := fun τ => Real.log (e.w (τ t))) fun τ => by rw [hval],
      finsum_eq_sum_of_fintype, ← e.w_alg, Algebra.norm_eq_prod_embeddings, map_prod, Real.log_prod]
    exact fun τ _ => e.w.ne_zero ((map_ne_zero τ).2 t.ne_zero)

  have hL (c : Γ(Z, ⊤)) (hc : c ≠ 0) : ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal),
      (Scheme.ord (algebraMap _ Z.functionField c) z : ℝ) * Real.log (Nat.card (Z.residueField z)) =
      -Real.log (NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F (algebraMap _ Z.functionField c))) := by
    let (m : PrimeSpectrum Γ(Z, ⊤)) : Algebra Γ(Z, ⊤) (Z.presheaf.stalk (hU.fromSpec m)) :=
      TopCat.Presheaf.algebra_section_stalk Z.presheaf (⟨hU.fromSpec m, trivial⟩ : (⊤ : Z.Opens))
    have (m : PrimeSpectrum Γ(Z, ⊤)) : IsLocalization.AtPrime (Z.presheaf.stalk (hU.fromSpec m)) m.asIdeal :=
      hU.isLocalization_stalk' m trivial
    have (m : PrimeSpectrum Γ(Z, ⊤)) : IsLocalRing (Z.presheaf.stalk (hU.fromSpec m)) :=
      Z.toLocallyRingedSpace.isLocalRing _
    rw [← GlobalTheory.finsum_length_mul_log_card_eq_neg_log_adicAbv_norm F Γ(Z, ⊤) Z.functionField (fun m => Z.presheaf.stalk (hU.fromSpec m)) v c hc]
    refine (finsum_eq_of_bijective _ hbij fun m => ?_).symm
    have hqm (m) : (q (hU.fromSpec m)).asIdeal = m.asIdeal.comap (algebraMap (𝓞 F) Γ(Z, ⊤)) := by
      rw [← Scheme.Hom.comp_apply, hq]; rfl
    refine finsum_congr_Prop (by rw [hqm]) fun h => ?_
    have hne : hU.fromSpec m ≠ genericPoint Z := fun h' => v.ne_bot (by
      have h1 := genericPoint_eq_of_isOpenImmersion hU.fromSpec
      rw [genericPoint_eq_bot_of_affine] at h1
      rw [← h, h', ← h1]
      exact (hqm _).trans (Ideal.comap_bot_of_injective _ hφ))
    have h1 := ord_algebraMap (coheight_eq_one hZ.dim_eq hne)
      ((map_ne_zero_iff _ (germ_injective_of_isIntegral Z (U := ⊤) _ trivial)).2 hc)
    rw [algebraMap_germ (U := ⊤) trivial c] at h1
    exact congrArg (· * _) ((Int.cast_natCast _).symm.trans (congrArg _ h1.symm))
  have hfin : {z : Z | (q z).asIdeal = v.asIdeal}.Finite :=
    (q.finite_preimage_singleton ⟨v.asIdeal, v.isPrime⟩).subset fun z hz => PrimeSpectrum.ext hz
  have h1 := hL a ha0
  have h2 := hL b hb0
  have hn (x : Z.functionField) (hx : x ≠ 0) :
      NumberField.HeightOneSpectrum.adicAbv F v (Algebra.norm F x) ≠ 0 :=
    AbsoluteValue.ne_zero _ (Algebra.norm_ne_zero_iff.2 hx)
  rw [hab', map_mul, map_mul, Real.log_mul (hn _ t.ne_zero) (hn _ hb1)] at h1
  simp only [Scheme.ord_mul t.ne_zero hb1, Int.cast_add, add_mul] at h1
  have h3 := finsum_mem_add_distrib
    (f := fun z => (Scheme.ord (t : Z.functionField) z : ℝ) * Real.log (Nat.card (Z.residueField z)))
    (g := fun z => (Scheme.ord (algebraMap _ Z.functionField b) z : ℝ) * Real.log (Nat.card (Z.residueField z))) hfin
  simp only [Set.mem_ofPred_eq] at h3
  rw [hR]
  linear_combination h1 - h2 - h3

end GlobalTheory.TrueGeo.PlaceFormula
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankinSelbergTestFunction
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands

open scoped Pointwise in

theorem exists_compact_mod_unipB_whittaker : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (m + 1)) k) V), IsSmooth ρ → (∀ (a b : ℕ) (h : ∑ i, ![a, b] i = m + 1), 0 < a → 0 < b → ∀ x : V, x ∈ twKer ρ (unipRad k (stdBlocks ![a, b] h)) 1) → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ v : V, ∃ C : Set (GL (Fin m) k), IsCompact C ∧ ∀ g : GL (Fin m) k, l (ρ (corner g) v) ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c := by
  intro k _ _ _ _ ψ hψc hψ1 m V _ _ ρ hs hJ l hl v
  have hcm : ∀ g h : GL (Fin m) k, corner (g * h) = corner g * corner h := fun g h => by
    simp only [corner]
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hcc : Continuous (corner : GL (Fin m) k → GL (Fin (m + 1)) k) :=
    (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (continuous_id.prodMk continuous_const))
  have hdc : Continuous (diagT k (Fin m)) :=
    (continuous_leviEmb k _).comp (continuous_leviTorus k (Fin m))
  set X : Set V := (fun g => ρ g v) '' (corner '' (KO k (Fin m) : Set (GL (Fin m) k))) with hX
  have hXf : X.Finite := GlobalTheory.T.finite_image_of_isOpen_stabilizer_alt _ V ρ v (hs v) _ (GlobalTheory.SplitFlip.isCompact_KO.image hcc)
  choose r1 hr1 using GlobalTheory.T.whittaker_functional_torus_valuation_bound k ψ hψc hψ1 (m + 1) V ρ hs l hl
  have hlow : ∀ (x : V) (i : Fin m), ∃ r : kˣ, ∀ t : Fin (m + 1) → kˣ,
      l (ρ (diagT k (Fin (m + 1)) t) x) ≠ 0 → valuation k (r : k) ≤ valuation k ((t i.castSucc : k) / t i.succ) := by
    intro x i
    have hi := i.2
    have h : ∑ j, ![(i : ℕ) + 1, m - i] j = m + 1 := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    exact GlobalTheory.T.whittaker_torus_twKer_rootBound' k ψ hψc (m + 1) V ρ l hl _ _ h i.castSucc i.succ (by simp) (by simp) x
      (hJ _ _ h (Nat.succ_pos _) (by omega) x)
  choose r2 hr2 using hlow
  choose R1 R2 hR using fun x => GlobalTheory.T.exists_torus_bounds_of_consecutive_ratio_bounds k m (fun _ => r1 x) (r2 x)
  refine ⟨⋃ x ∈ X, diagT k (Fin m) '' {t : Fin m → kˣ | ∀ i, valuation k (R2 x : k) ≤ valuation k (t i : k) ∧
      valuation k (t i : k) ≤ valuation k (R1 x : k)} * (KO k (Fin m) : Set (GL (Fin m) k)),
    hXf.isCompact_biUnion fun x _ => ((GlobalTheory.T.isCompact_boundedTorus' k m (R1 x) (R2 x)).image hdc).mul GlobalTheory.SplitFlip.isCompact_KO,
    fun g hg => ?_⟩
  obtain ⟨u, hu, t, κ, hκ, rfl⟩ := GlobalTheory.T.exists_iwasawa_decomposition_upperUnitriangular_integral k m g
  have hcu := GlobalTheory.T.glCornerEmbedding_upperUnitriangular_superDiagonalSum k m u hu
  rw [hcm, hcm, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hl _ hcu.1, GlobalTheory.T.glCornerEmbedding_diagonalTorus_eq_snoc_one] at hg
  have hg' := right_ne_zero_of_mul hg
  have hxX : ρ (corner κ) v ∈ X := ⟨corner κ, ⟨κ, hκ, rfl⟩, rfl⟩
  have hlast : (Fin.snoc t 1 : Fin (m + 1) → kˣ) (Fin.last m) = 1 := Fin.snoc_last _ _
  have hb := hR _ _ hlast (fun i => ⟨hr2 _ i _ hg', hr1 _ _ i.castSucc i.succ (by simp) hg'⟩)
  refine ⟨u, hu, diagT k (Fin m) t * κ, Set.mem_biUnion hxX ⟨_, ⟨t, fun i => ?_, rfl⟩, κ, hκ, rfl⟩,
    mul_assoc _ _ _⟩
  have := hb i.castSucc
  simpa [Fin.snoc_castSucc] using this

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadUpdSKeep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in

theorem read_updS_keep (R : RealDat3 D A3 Ks) (F : Face3 D A3) (lam : type_of% R.lam3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (err : type_of% R.err0)
    (hX : ∀ b, (((R.updS R.kap lam).toCx3 F).data F.cr b).XE = ((R.toCx3 F).data F.cr b).XE) (X0 : BaseLevelRowSide D)
    (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) :
    ∃ (Y' : Read (A3 := A3) ((R.updS R.kap lam).withErr err).toRealDat (reFace F Dc Sp Zsc).lv2 X0) (Z' : ReadL ((R.updS R.kap lam).withErr err) (reFace F Dc Sp Zsc) X0 Y'), Y'.tup = Y.tup ∧ Y'.tupT = Y.tupT ∧ HEq Y'.jA Y.jA ∧ HEq Y'.jA0 Y.jA0 ∧ HEq Y'.eMt Y.eMt ∧ HEq Y'.PY Y.PY ∧ HEq Y'.eFT Y.eFT ∧ HEq Y'.IL Y.IL ∧ HEq Y'.PW Y.PW ∧ HEq Y'.eE Y.eE ∧ HEq Y'.mj.eW Y.mj.eW ∧ HEq Z'.eRR Z.eRR ∧ HEq Z'.jW Z.jW := by
  refine ⟨reFaceRead (R.updS R.kap lam) F Dc Sp Zsc err X0 Y,
    reFaceReadL (R.updS R.kap lam) F Dc Sp Zsc err X0 Y (scalReadL R F lam hX X0 Y Z),
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kexactB HEq.refl Y.jA
  · exact (by with_unfolding_all exact (HEq.refl Y.jA0 :))
  · exact (by with_unfolding_all exact (HEq.refl Y.eMt :))
  · exact (by with_unfolding_all exact (HEq.refl Y.PY :))
  · exact (by with_unfolding_all exact (HEq.refl Y.eFT :))
  · kexactB HEq.refl Y.IL
  · exact (by with_unfolding_all exact (HEq.refl Y.PW :))
  · exact (by with_unfolding_all exact (HEq.refl Y.eE :))
  · exact (by with_unfolding_all exact (HEq.refl Y.mj.eW :))
  · kexactB HEq.refl Z.eRR
  · exact (by with_unfolding_all exact (HEq.refl Z.jW :))

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEmbeddingsCard
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ResidueCard

theorem card_ringHom_eq {X Z : Scheme.{0}} (i : Z ⟶ X) [IsPreimmersion i] (z : Z) :
    Nat.card (X.residueField (i z) →+* ℂ) = Nat.card (Z.residueField z →+* ℂ) := by
  have hs : Function.Surjective (i.residueFieldMap z).hom := fun a => by
    obtain ⟨b, rfl⟩ := Z.residue_surjective z a
    obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
    exact ⟨X.residue _ c, congrArg (fun f => f.hom c) (Scheme.residue_residueFieldMap i z)⟩
  let e := RingEquiv.ofBijective _ ⟨(i.residueFieldMap z).hom.injective, hs⟩
  exact Nat.card_congr ⟨fun φ => φ.comp e.symm.toRingHom, fun φ => φ.comp e.toRingHom,
    fun φ => by ext; simp, fun φ => by ext; simp⟩

theorem card_emb (F L : Type) [Field F] [NumberField F] [Field L] [Algebra F L] [Module.Finite F L] :
    Nat.card (L →+* ℂ) = Module.finrank ℚ F * Nat.card (L →ₐ[F] AlgebraicClosure F) := by
  haveI : NumberField L := NumberField.of_module_finite F L
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AlgHom.card, NumberField.Embeddings.card,
    Module.finrank_mul_finrank]

theorem card_parity_sign_length_of_eq {F : Type} [Field F] [NumberField F] {X : Scheme.{0}} (s : X ⟶ Sp F)
    [LocallyOfFiniteType s] (x : X) (hx : IsClosed ({x} : Set X)) :
    Nat.card (X.residueField x →+* ℂ) = Module.finrank ℚ F *
      Nat.card {y : {y : Sp (AlgebraicClosure F) ⟶ X // y ≫ s = spMap (algebraMap F (AlgebraicClosure F))} //
        below y.1 = x} := by
  have := isClosed_singleton_iff_isClosedImmersion.1 hx
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.fromSpecResidueField x ≫ s)
  have hfin : IsFinite (Spec.map φ) := by
    rw [hφ]
    exact isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 inferInstance
  letI : Algebra F (X.residueField x) := φ.hom.toAlgebra
  haveI : Module.Finite F (X.residueField x) := (IsFinite.SpecMap_iff φ).1 hfin
  have hP (ψ : X.residueField x →ₐ[F] AlgebraicClosure F) :
      (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x) ≫ s =
        spMap (algebraMap F (AlgebraicClosure F)) := by
    have h : φ ≫ CommRingCat.ofHom ψ.toRingHom = CommRingCat.ofHom (algebraMap F (AlgebraicClosure F)) :=
      CommRingCat.hom_ext ψ.comp_algebraMap
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    exact congrArg Spec.map h
  let P : (X.residueField x →ₐ[F] AlgebraicClosure F) →
      {y : {y : Sp (AlgebraicClosure F) ⟶ X // y ≫ s = spMap (algebraMap F (AlgebraicClosure F))} //
        below y.1 = x} :=
    fun ψ => ⟨⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, hP ψ⟩,
      ExtConj.below_comp x _⟩
  have hb : Function.Bijective P := by
    refine ⟨fun a b h => ?_, ?_⟩
    · have h1 : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ X.fromSpecResidueField x =
          Spec.map (CommRingCat.ofHom b.toRingHom) ≫ X.fromSpecResidueField x := congrArg (fun t => t.1.1) h
      have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h1))
      exact AlgHom.coe_ringHom_injective h2
    · rintro ⟨⟨y, hy⟩, hyx⟩
      obtain ⟨ψ, h⟩ := ExtConj.factor y x hyx
      have h2 : Spec.map (φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap F (AlgebraicClosure F))) := by
        rw [Spec.map_comp, hφ, ← Category.assoc, h]
        exact hy
      have h3 := Spec.map_injective h2
      exact ⟨⟨ψ.hom, fun a => congrArg (fun t => t.hom a) h3⟩, Subtype.ext (Subtype.ext h)⟩
  rw [card_emb F (X.residueField x), Nat.card_congr (Equiv.ofBijective P hb)]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → Nat.card (M.X.residueField (M.j x) →+* ℂ) = Module.finrank ℚ F * Nat.card {y : AlgPt Y // below y.1 = x} := by
  intro F _ _ Y M x hx
  have h1 : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F))
  haveI : IsPreimmersion M.j := MorphismProperty.of_isPullback (P := @IsPreimmersion) M.pb.flip h1
  rw [card_ringHom_eq]
  exact card_parity_sign_length_of_eq Y.str x hx

end GlobalTheory.TrueGeo.ResidueCard
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormMetricEqClassSumMetric
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

noncomputable section

namespace GlobalTheory.Mem.Df

set_option maxHeartbeats 1000000

theorem card_stabilizer_eq_of_smul {G α : Type*} [Group G] [MulAction G α] (g : G) (x : α) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv).symm

private theorem finset_sum_univ_eq_of_equiv {α β M : Type*} [AddCommMonoid M] (i1 : Fintype α) (i2 : Fintype β) (e : α ≃ β)
    (f : α → M) (g : β → M) (h : ∀ x, f x = g (e x)) :
    @Finset.sum α M _ (@Finset.univ α i1) f = @Finset.sum β M _ (@Finset.univ β i2) g :=
  @Fintype.sum_equiv α β M i1 i2 _ e f g h

theorem ipMt_eq_cSum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (hX : B.fields.Ok) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (F G : (I.per l u a).Mt) (F' G' : MtCx I a), SameForm I l u a F' F → SameForm I l u a G' G → I.ipMt l u a F G = cSum I hX a F' G' := by
  intro B X I hOk hP l hX Z u a F G F' G' hF hG
  rw [GlobalTheory.Mem.Col2.IpMt.ipMt_sum I hOk hP l Z u a F G]
  have hd : Disjoint (B.primes X).vGs (QE I.sel (I.tup a : Chr B.fields.F B.fields.E B.fields.K)) :=
    (GlobalTheory.TopStep.tilOk_of_avoid (mu := I.tup a) l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.2
  have hs : (I.perIn u a).sgT = B.wts.sgTrue := by
    funext τ
    rfl
  rw [hs, GlobalTheory.Mem.Df.cSum_apply]
  refine finset_sum_univ_eq_of_equiv _ _ (GlobalTheory.PeriodOnStep.clEquiv (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd) _ _ (fun c => ?_)
  have hFc := hF ((stepX I.Ch I.sel (I.tup a) I.Ps).rep c)
  have hGc := hG ((stepX I.Ch I.sel (I.tup a) I.Ps).rep c)
  have hcls : (rowS I a).cls ((rowS I a).outSec.rep ((GlobalTheory.PeriodOnStep.clEquiv (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd) c)) =
      (rowS I a).cls (GlobalTheory.PeriodOnStep.rowPt (X := B.fields) (Pr := B.primes X) (R := B.R) I.Ch I.sel (I.tup a) I.Ps c) :=
    (rowS I a).outSec.spec _
  obtain ⟨g, hg⟩ := ((rowS I a).cls_eq_iff _ _).1 hcls
  have hcard := GlobalTheory.PeriodOnStep.card_stab (X := B.fields) (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps hd c
  have hpair := GlobalTheory.T.pairing_complexForms_const_on_row_classes I hX a F' G' _ _ hcls
  unfold cTerm
  rw [hpair, ← hg, @card_stabilizer_eq_of_smul (rowS I a).G (rowS I a).D _ (rowS I a).actD g _, ← hcard]
  exact congrArg₂ (fun x y => (((Nat.card ((stepX I.Ch I.sel (I.tup a) I.Ps).Stab c) : ℕ) : ℂ))⁻¹ *
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) x) y) hFc hGc

end GlobalTheory.Mem.Df

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalityDimPairingEqInnerStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_orthogonality_dim_pairing_eq_inner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → ∀ (t : T) (h h' : (R.HX t).H), (((∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) : ℝ) : ℂ) * ipMT R.MX (R.νX t) (R.fdX t) (R.cX.toMap R.prX ((R.HX t).e h)) (R.cX.toMap R.prX ((R.HX t).e h')) = ⟪h, h'⟫_ℂ := by
  first | exact @GlobalTheory.Mem.TopSchur.topSchur | exact GlobalTheory.Mem.TopSchur.topSchur | (intros; apply GlobalTheory.Mem.TopSchur.topSchur <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCuspFormMemUnitaryRapidDecayFormsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothCuspForm_mem_unitaryRapidDecayForms : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ F, IsCuspForm θ V F → F ∈ Decay θ V := by
  first | exact @GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay | exact GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay | (intros; apply GlobalTheory.Mem.CuspDeriv.cuspForm_mem_decay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevContinuousFormGardingVectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevContinuous_form_gardingVector : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → ∀ ℓ : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG G) (trRep σ P) ℓ → (∀ φ, IsTest φ → ∃ C : ℝ, ∀ w, ‖ℓ (gard ε σ φ w)‖ ≤ C * ‖w‖) ∧ ∀ w ∈ smSub G (trRep σ P), (Continuous fun g : Formalism.REAL.UJ ε => ℓ (σ (umat g) w)) ∧ ∀ φ, IsTest φ → ℓ (gard ε σ φ w) = ∫ g : Formalism.REAL.UJ ε, φ (umat g) • ℓ (σ (umat g) w) ∂(Formalism.REAL.muG ε) := by
  first | exact @GlobalTheory.SobGarding.sobCont_gard | exact GlobalTheory.SobGarding.sobCont_gard | (intros; apply GlobalTheory.SobGarding.sobCont_gard <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanLiftFormsBaseLevelEqHilbertImageStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_liftForms_baseLevel_eq_hilbertImage : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → A.fam.Ok 1 → (∀ i t, Function.Injective (R.extV i t)) → ∀ (i : Fin D.R.m) (t : T), Submodule.span ℂ (Set.range fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) = LinearMap.range (R.extV i t) ⊓ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  first | exact @GlobalTheory.LiftSpan.span_liftForm_eq | exact GlobalTheory.LiftSpan.span_liftForm_eq | (intros; apply GlobalTheory.LiftSpan.span_liftForm_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroFormsIdentificationReferenceTupleEqSelfStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroFormsIdentification_referenceTuple_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (x : ((I.fm l u I.mu0).lat 0).V), (l0 u I.mu0).choose x = x := by
  first | exact @GlobalTheory.Mem.Col2.TC.MuZeroForms.law0_choose_mu0_eq_self | exact GlobalTheory.Mem.Col2.TC.MuZeroForms.law0_choose_mu0_eq_self | (intros; apply GlobalTheory.Mem.Col2.TC.MuZeroForms.law0_choose_mu0_eq_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroLevelTypePrimeOrientationFramesFunctionaStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroLevel_typePrimeOrientation_frames_functionals : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → (∀ u (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((A u).piU : (I.rec7 l Z).host.E) → ∀ m : (H.lev0 u).fM w h, a • m = 0) → ∀ u, ∃ x : Formalism.L2.Herm.ColLevelX (H.lev0 u) (fun x => x ∈ (I.rec7 l Z).host.K) (A u).piU (H.vT u) (fun v c z => ((I.rec7 l Z).fm u).fv 0 v c ((A u).pr 0 v c z)), x.piG = X.piG := by
  first | exact @GlobalTheory.Mem.Col2.TC.intV_coe_eq_inclE_of_T_mem | exact GlobalTheory.Mem.Col2.TC.intV_coe_eq_inclE_of_T_mem | (intros; apply GlobalTheory.Mem.Col2.TC.intV_coe_eq_inclE_of_T_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionScalarProductPreservedIsometryStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFunction_scalarProduct_preserved_isometry : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ M : Module.End ℂ (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (M f)) → (∀ f, IsThetaFunO ψ S T f → ∫⁻ w in 𝓕, ‖M f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) → ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → ∫ x in 𝓕, M f x * star (M f' x) ∂μ = ∫ x in 𝓕, f x * star (f' x) ∂μ := by
  first | exact @GlobalTheory.Mem.LiftPolar.scalar_eq | exact GlobalTheory.Mem.LiftPolar.scalar_eq | (intros; apply GlobalTheory.Mem.LiftPolar.scalar_eq <;> assumption)
end

