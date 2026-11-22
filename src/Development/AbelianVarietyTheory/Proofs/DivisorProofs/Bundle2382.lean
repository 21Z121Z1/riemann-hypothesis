import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0086
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAdditiveLineBundleFamilyAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeformationBaseRingLocalDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deformation_base_ring_local_domain : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [CharZero C] (e : C →+* ℂ) (I I' : Type) [Finite I] [Finite I'] (Φ : I → PowerSeries C) (c : I' → C) (π : C) (b ε : ℝ), ‖π‖ < 1 → 0 < ε → (∀ a n, ‖PowerSeries.coeff n (Φ a)‖ ≤ b) → (∀ u : ℂ, u ≠ 0 → ‖u‖ < ε → ∀ a, Summable fun n => ‖e (PowerSeries.coeff n (Φ a)) * u ^ n‖) → ∃ (u : ℂ) (o : Type) (_ : Field o) (_ : CharZero o) (j : o →+* C) (c₀ : I' → o), u ≠ 0 ∧ ‖u‖ < ε ∧ (∀ a, j (c₀ a) = c a) ∧ ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsNoetherianRing W) (_ : IsLocalRing W) (_ : IsIntegrallyClosed W) (_ : CharZero W) (β : o →+* W) (i₀ : W →+* ℂ) (i₁ : W →+* C) (φ : I → W), Function.Injective i₀ ∧ i₀.comp β = e.comp j ∧ i₁.comp β = j ∧ (∀ a, i₁ a ≠ 0 → IsUnit a) ∧ (∀ q : Ideal W, q.IsPrime → q = RingHom.ker i₀ ∨ q = RingHom.ker i₁) ∧ ∀ a, i₀ (φ a) = ∑' n, e (PowerSeries.coeff n (Φ a)) * u ^ n ∧ i₁ (φ a) = ∑' n, PowerSeries.coeff n (Φ a) * π ^ n := by
  first | exact @GlobalTheory.MBLow.ring_of_deformation | exact GlobalTheory.MBLow.ring_of_deformation | (intros; apply GlobalTheory.MBLow.ring_of_deformation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendAdicCompletionLocalization
section
open IsLocalRing TensorProduct

noncomputable section

namespace GlobalTheory

def intDerivationOfLeibniz {A M : Type} [CommRing A] [AddCommGroup M] {instZA : Algebra ℤ A}
    {_ : Module A M} {instZM : Module ℤ M} (f : A →+ M) (h : ∀ a b, f (a * b) = a • f b + b • f a) :
    Derivation ℤ A M :=
  { toFun := f
    map_add' := f.map_add
    map_smul' := fun c x => by
      simp only [RingHom.id_apply]
      obtain rfl : instZM = AddCommGroup.toIntModule M := Subsingleton.elim _ _
      obtain rfl : instZA = Ring.toIntAlgebra A := Subsingleton.elim _ _
      exact map_zsmul f c x
    map_one_eq_zero' := by
      have h1 := h 1 1
      rw [one_mul, one_smul] at h1
      simpa using h1
    leibniz' := h }

theorem derivation_extend_completion_localization_atPrime (S : Type) [CommRing S] (P : Ideal S)
    [P.IsPrime] (d : Derivation ℤ S S) :
    ∃ D : Derivation ℤ (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P))
      (AdicCompletion (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P)),
      ∀ x, D (algebraMap S _ x) = algebraMap S _ (d x) := by
  obtain ⟨D', hD'⟩ := derivation_extend_localization_atPrime ℤ S (Localization.AtPrime P) P
    (intDerivationOfLeibniz
      ((algebraMap S (Localization.AtPrime P)).toAddMonoidHom.comp d.toLinearMap.toAddMonoidHom)
      (fun a b => by simp [d.leibniz, Algebra.smul_def]))
  have hadd : ∀ y z, BK.complDerFun (maximalIdeal (Localization.AtPrime P)) D' (y + z) =
      BK.complDerFun _ D' y + BK.complDerFun _ D' z := fun y z => by
    refine AdicCompletion.ext_evalₐ fun n => ?_
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime P)) (n + 1) y)
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime P)) (n + 1) z)
    rw [BK.evalₐ_complDerFun _ D' (r := r + t) (by rw [map_add, map_add, hr, ht]), map_add,
      map_add, map_add, BK.evalₐ_complDerFun _ D' hr.symm, BK.evalₐ_complDerFun _ D' ht.symm]
  refine ⟨intDerivationOfLeibniz
    { toFun := BK.complDerFun (maximalIdeal (Localization.AtPrime P)) D'
      map_zero' := by
        have h0 := hadd 0 0
        rw [add_zero] at h0
        simpa using h0
      map_add' := hadd }
    (fun a b => by simpa [smul_eq_mul] using BK.complDerFun_mul _ D' a b),
    fun x => ?_⟩
  have h2 := BK.complDerFun_algebraMap (maximalIdeal (Localization.AtPrime P)) D'
    (algebraMap S (Localization.AtPrime P) x)
  rw [hD'] at h2
  exact h2

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedNormIdealSheafFiniteNormal
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.NormSheafDescent

theorem descendedIdealSheaf_exists : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π], IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) → CharZero Γ(Y, ⊤) →
    ∀ I : Y.IdealSheafData, ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      CharZero K ∧ ∃ J : Z.IdealSheafData, (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ U : Z.affineOpens, (U : Set Z) ⊆ Set.range π → (U : Set Z).Nonempty →
        ∃ (_ : Algebra Γ(Z, U) K) (_ : Algebra Γ(Y, π ⁻¹ᵁ U.1) L),
          IsDomain Γ(Z, U) ∧ IsIntegrallyClosed Γ(Z, U) ∧ IsDomain Γ(Y, π ⁻¹ᵁ U.1) ∧ (π.app U.1).hom.Finite ∧
          IsFractionRing Γ(Z, U) K ∧ IsFractionRing Γ(Y, π ⁻¹ᵁ U.1) L ∧
          (algebraMap K L).comp (algebraMap Γ(Z, U) K) = (algebraMap Γ(Y, π ⁻¹ᵁ U.1) L).comp (π.app U.1).hom ∧
          J.ideal U = GlobalTheory.NormSheaf.normIdeal Γ(Z, U) K L Γ(Y, π ⁻¹ᵁ U.1) (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) := by
  intro Y Z π _ hY _ _ hnZ hW hchar I
  have hK := GlobalTheory.T.isField_stalk_imageOfGenericPoint Y Z π hW
  have hfd := GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint Y Z π hK
  letI := GlobalTheory.NormSheafDescent.fieldK π hK
  letI := GlobalTheory.NormSheafDescent.algKL π
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  obtain ⟨J, hJ, hJs⟩ := GlobalTheory.T.exists_idealSheafData_of_isClopen_family Z (Set.range π) ⟨hcl, hW⟩ (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I)
    (fun U f hU => GlobalTheory.T.normCoeffIdealFamily_map_basicOpen Y Z π hK hfd I U f hU)
  have hgen : ∀ (U : Z.Opens) (x : Z), x ∈ U → x ∈ Set.range π →
      GlobalTheory.NormSheafDescent.genPt π ∈ U := by
    rintro U _ hx ⟨y, rfl⟩
    exact ((genericPoint_specializes y).map π.continuous).mem_open U.isOpen hx
  refine ⟨Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π), Y.functionField, inferInstance, inferInstance,
    inferInstance, hfd, GlobalTheory.T.charZero_stalk_imageOfGenericPoint Y Z π hchar hK, J, ?_, ?_⟩
  · intro x hx
    by_contra hne
    push_neg at hne
    have hxW := hJs hx
    have hS : IsClosed (π '' (I.support : Set Y)) := π.isClosedMap _ I.support.isClosed
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUsub⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (π '' (I.support : Set Y))ᶜ ∩ Set.range π from ⟨fun ⟨y, hy, e⟩ => hne y hy e, hxW⟩)
      (hS.isOpen_compl.inter hW)
    have htop := GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint Y Z π hK hfd I ⟨U, hU⟩ (fun y hy hyU => (hUsub hyU).1 ⟨y, hy, rfl⟩)
    have hx' := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    rw [hJ ⟨U, hU⟩ (fun z hz => (hUsub hz).2), htop] at hx'
    exact (Scheme.mem_zeroLocus_iff _ _ _).mp hx' 1 Submodule.mem_top (by simpa using hxU)
  · rintro U hUW ⟨x, hxU⟩
    have h := hgen U.1 x hxU (hUW hxU)
    obtain ⟨hdom, hfr⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π U.1 U.2 hUW h
    letI := GlobalTheory.NormSheafDescent.algAK π U.1 h
    letI := GlobalTheory.NormSheafDescent.algBL π U.1 h
    haveI : Nonempty (π ⁻¹ᵁ U.1) := ⟨⟨genericPoint Y, h⟩⟩
    refine ⟨inferInstance, inferInstance, hdom, GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen U.2,
      inferInstance, ?_, hfr, ?_, ?_, ?_⟩
    · exact π.finite_app U.1 U.2
    · exact functionField_isFractionRing_of_isAffineOpen Y _ (U.2.preimage π)
    · ext a
      exact Scheme.Hom.germ_stalkMap_apply π U.1 (genericPoint Y) h a
    · rw [hJ U hUW]
      simp only [GlobalTheory.NormSheafDescent.famIdeal, dif_pos h]

end GlobalTheory.NormSheafDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMorphismToLocalScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
noncomputable section

namespace GlobalTheory.Desc

theorem exists_desc_specStalk : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R), f ≠ 0 → ∀ (x : Sp R)
    (S₁ B Z B₀ B₁ : Scheme.{0}) (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)), Flat ξ' → Surjective ξ' →
    QuasiCompact ξ' → ∀ (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → IsSeparated pZ →
    ∀ (φ₀ : B₀ ⟶ B) (q₀ : B₀ ⟶ Sp (Localization.Away f)) (u₀ : B₀ ⟶ Z) (φ₁ : B₁ ⟶ B) (q₁ : B₁ ⟶ S₁)
      (u₁ : B₁ ⟶ Z), IsPullback φ₀ q₀ pB (awayMap f) → IsPullback φ₁ q₁ pB (ξ' ≫ (Sp R).fromSpecStalk x) →
    u₁ ≫ pZ = φ₁ ≫ pB →
    (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t₁ : T ⟶ B₁), t₀ ≫ φ₀ = t₁ ≫ φ₁ → t₀ ≫ u₀ = t₁ ≫ u₁) →
    ∃ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB ∧
      ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)),
        t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u := by
  intro R _ _ f hf x S₁ B Z B₀ B₁ ξ' hξf hξs hξq pB pZ hpB hpZ φ₀ q₀ u₀ φ₁ q₁ u₁ h₀ h₁ hu₁ H
  have hs : Flat ((Sp R).fromSpecStalk x) := GenericExt.flat_fromSpecStalk _ x
  let π : B₁ ⟶ pullback pB ((Sp R).fromSpecStalk x) :=
    pullback.lift φ₁ (q₁ ≫ ξ') (by rw [h₁.w, Category.assoc])
  have hπ₁ : π ≫ pullback.fst _ _ = φ₁ := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ pullback.snd _ _ = q₁ ≫ ξ' := pullback.lift_snd _ _ _
  have hsq : IsPullback π q₁ (pullback.snd pB ((Sp R).fromSpecStalk x)) ξ' := by
    refine IsPullback.of_right ?_ hπ₂ (IsPullback.of_hasPullback pB ((Sp R).fromSpecStalk x))
    rw [hπ₁]; exact h₁
  have : Flat π := MorphismProperty.of_isPullback hsq.flip hξf
  have : Surjective π := MorphismProperty.of_isPullback hsq.flip hξs
  have : QuasiCompact π := MorphismProperty.of_isPullback hsq.flip hξq
  have : Flat φ₁ := by rw [← hπ₁]; infer_instance
  have key : pullback.fst π π ≫ u₁ = pullback.snd π π ≫ u₁ := by
    let g : pullback π π ⟶ Sp R := pullback.fst π π ≫ φ₁ ≫ pB
    have hg : Flat g := inferInstance
    have hφ : pullback.fst π π ≫ φ₁ = pullback.snd π π ≫ φ₁ := by
      rw [← hπ₁, pullback.condition_assoc]
    have hAf : IsSchemeTheoreticallyDominant (awayMap f) :=
      schDom_spec_map _ (IsLocalization.injective (Localization.Away f)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hf))
    have hdom : IsSchemeTheoreticallyDominant (pullback.fst g (awayMap f)) :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback g (awayMap f)).flip
    refine ext_of_schDom pZ ?_ (pullback.fst g (awayMap f)) ?_
    · simp only [Category.assoc, hu₁]; exact (reassoc_of% hφ) pB
    · let t₀ : pullback g (awayMap f) ⟶ B₀ :=
        h₀.lift (pullback.fst g (awayMap f) ≫ pullback.fst π π ≫ φ₁) (pullback.snd g (awayMap f))
          (by simpa [g] using pullback.condition (f := g) (g := awayMap f))
      have ht₀ : t₀ ≫ φ₀ = pullback.fst g (awayMap f) ≫ pullback.fst π π ≫ φ₁ := h₀.lift_fst _ _ _
      have e₁ := H _ t₀ (pullback.fst g (awayMap f) ≫ pullback.fst π π) (by rw [ht₀, Category.assoc])
      have e₂ := H _ t₀ (pullback.fst g (awayMap f) ≫ pullback.snd π π) (by rw [ht₀, Category.assoc, hφ])
      simp only [Category.assoc] at e₁ e₂
      rw [← e₁, ← e₂]
  have hE : EffectiveEpi π := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  let u := EffectiveEpi.desc π u₁ (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hu : π ≫ u = u₁ := EffectiveEpi.fac _ _ _
  have : Epi π := Flat.epi_of_flat_of_surjective π
  refine ⟨u, ?_, ?_⟩
  · rw [← cancel_epi π, reassoc_of% hu, hu₁, reassoc_of% hπ₁]
  · intro T t₀ t ht
    have : Epi (pullback.fst t π) := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.fst t π), pullback.condition_assoc, hu]
    have := H _ (pullback.fst t π ≫ t₀) (pullback.snd t π) (by
      rw [Category.assoc, ht, pullback.condition_assoc, hπ₁])
    simpa only [Category.assoc] using this

end GlobalTheory.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetGenHolUnif
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem Obj.exists_detGen_holUnif : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (κ : ℂ), κ ≠ 0 →
    ∃ δ : X.DetGen, ∀ (v : Fin (Module.finrank ℚ F) → X.Lie)
      (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ i, u.IsDiff (W i) (v i).hom) → δ.1 v = κ * W.det := by
  intro F _ _ 𝔠 X L u κ hκ
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  obtain ⟨d, hdi, hd⟩ := GlobalTheory.DiagCoord.exists_diff_linear u X.rm h₁ h₂
  have hds : Function.Surjective d := fun w => by
    obtain ⟨v, hv, hw⟩ := (h₂ w).exists
    refine ⟨GlobalTheory.Serre.Lie.mk X.rm v hv, ?_⟩
    exact (h₁ _ hv).unique (hd _) hw
  let e : X.Lie ≃ₗ[ℂ] (Fin (Module.finrank ℚ F) → ℂ) := LinearEquiv.ofBijective d ⟨hdi, hds⟩
  let b : Module.Basis (Fin (Module.finrank ℚ F)) ℂ X.Lie := (Pi.basisFun ℂ _).map e.symm
  refine ⟨⟨κ • b.det, ?_⟩, fun v W hW => ?_⟩
  · rw [show κ • b.det = (Units.mk0 κ hκ : ℂˣ) • b.det from rfl, Submodule.span_singleton_group_smul_eq]
    exact (Obj.DetGen.ofBasis X b).2
  · have hv : ∀ i, d (v i) = W i := fun i => (h₁ _ (v i).isTangent).unique (hd _) (hW i)
    have hm : b.toMatrix v = W.transpose := by
      ext i j
      rw [Module.Basis.toMatrix_apply, Matrix.transpose_apply]
      rw [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, Pi.basisFun_repr]
      exact congrFun (hv j) i
    rw [AlternatingMap.smul_apply, Module.Basis.det_apply, hm, Matrix.det_transpose, smul_eq_mul]

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeterminantLineSectionRestriction
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine.Restrict

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem exists_bar (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {R : Type} [CommRing R]
    {x : Sp R ⟶ Xo.XF c} {v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)} (h : ∃ j, FrU Xo c U τ j x v w) :
    ∃ vb wb, FrY Y (compactOf Y U) τ h.choose (x ≫ Y.jQ) vb wb ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb :=
  (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R h.choose x).1 v w h.choose_spec

def restrictRule (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y) : RuleU Xo c :=
  fun R _ x v w =>
    haveI := Classical.propDecidable (∃ j, FrU Xo c U τ j x v w)
    if h : ∃ j, FrU Xo c U τ j x v w then
      σb R (x ≫ Y.jQ) (exists_bar Y U τ h).choose (exists_bar Y U τ h).choose_spec.choose
    else 0

theorem restrictRule_eq (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {σb : RuleY Y}
    (hσb : SecY Y (compactOf Y U) τ σb) {R : Type} [CommRing R] {j : c.F →+* R} {x : Sp R ⟶ Xo.XF c}
    {v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)} {w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)}
    {vb : Fin D.p → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)} {wb : Fin D.q → (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G)}
    (h : FrU Xo c U τ j x v w) (hb : FrY Y (compactOf Y U) τ j (x ≫ Y.jQ) vb wb) (hv : SameVecs Y x v vb)
    (hw : SameVecs Y x w wb) : restrictRule Y U τ σb R x v w = σb R (x ≫ Y.jQ) vb wb := by
  have hex : ∃ j, FrU Xo c U τ j x v w := ⟨j, h⟩
  obtain ⟨hb0, hv0, hw0⟩ := (exists_bar Y U τ hex).choose_spec.choose_spec
  have e : restrictRule Y U τ σb R x v w =
      σb R (x ≫ Y.jQ) (exists_bar Y U τ hex).choose (exists_bar Y U τ hex).choose_spec.choose := by
    unfold restrictRule
    rw [dif_pos hex]
  rw [e]
  have hx : x ≫ Y.jQ = spMap (RingHom.id R) ≫ (x ≫ Y.jQ) := by
    rw [DetExtendZero.spMap_id, Category.id_comp]
  have hx' : x = spMap (RingHom.id R) ≫ x := by rw [DetExtendZero.spMap_id, Category.id_comp]
  have cv : ∀ i, FramedFlatCoordinates.IsCombination ((x ≫ Y.jQ) ≫ genι Y) ((1 : Matrix (Fin D.p) (Fin D.p) R) i)
      (fun k => spMap (Chart.dualMapR (RingHom.id R)) ≫ (vb k).left) ((exists_bar Y U τ hex).choose i) := by
    intro i
    refine (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R (RingHom.id R) x x D.p v vb v _ hx' hv hv0 _ i).mp ?_
    simp only [DetExtendZero.dual_id, Category.id_comp]
    exact DetExtendZero.comb_one (fun k => (h.2.2.1.1 k).1) i
  have cw : ∀ i, FramedFlatCoordinates.IsCombination ((x ≫ Y.jQ) ≫ genι Y) ((1 : Matrix (Fin D.q) (Fin D.q) R) i)
      (fun k => spMap (Chart.dualMapR (RingHom.id R)) ≫ (wb k).left)
      ((exists_bar Y U τ hex).choose_spec.choose i) := by
    intro i
    refine (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R (RingHom.id R) x x D.q w wb w _ hx' hw hw0 _ i).mp ?_
    simp only [DetExtendZero.dual_id, Category.id_comp]
    exact DetExtendZero.comb_one (fun k => (h.2.2.2.1 k).1) i
  have key := sec_chg hσb hb hb0 (g := RingHom.id R) (M := 1) (N := 1) ⟨hx, cv, cw⟩
  simpa using key.symm

theorem exists_restriction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σb : RuleY Y), SecY Y (compactOf Y U) τ σb → ∃ σ : RuleU Xo c, SecU Xo c U τ σ ∧ Restricts Y U τ σb σ ∧ (NzY Y (compactOf Y U) τ σb → NzU Xo c U τ σ) := by
  intro E _ _ _ H D l Xo c O _ β Y U τ σb hσb
  refine ⟨restrictRule Y U τ σb, isSection_of_chg ?_, ?_, ?_⟩
  · intro R R' _ _ g j j' x v w x' v' w' M N h h' hc
    obtain ⟨vb, wb, hb, hv, hw⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R j x).1 v w h
    obtain ⟨vb', wb', hb', hv', hw'⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R' j' x').1 v' w' h'
    rw [restrictRule_eq Y U τ hσb h hb hv hw, restrictRule_eq Y U τ hσb h' hb' hv' hw']
    refine sec_chg hσb hb hb' ⟨by rw [hc.1, Category.assoc], fun i => ?_, fun i => ?_⟩
    · exact (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R' g x x' D.p v vb v' vb' hc.1 hv hv'
        _ i).mp (hc.2.1 i)
    · exact (GlobalTheory.DetLine.isCombination_iff_of_sameVecs E H D l Xo c O β Y R R' g x x' D.q w wb w' wb' hc.1 hw hw'
        _ i).mp (hc.2.2 i)
  · intro R _ j x v w vb wb h hb hv hw
    exact (restrictRule_eq Y U τ hσb h hb hv hw).symm
  · intro hnz R _ j x v w h
    obtain ⟨vb, wb, hb, hv, hw⟩ := (GlobalTheory.DetLine.frame_transfer E H D l Xo c O β Y U τ R j x).1 v w h
    rw [restrictRule_eq Y U τ hσb h hb hv hw]
    exact hnz R j _ vb wb hb

end GlobalTheory.DetLine.Restrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualNumberTangentPointOfLogarithmicDerivatStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dualNumberTangentPoint_of_logarithmicDerivation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (K : Type) [Field K] [Algebra c.F K] (P₀ : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1), ∃ (y' : Sp (DualNumber K) ⟶ Xo.XF c) (hU' : ⊤ ≤ (y' ≫ TF.Y.j) ⁻¹ᵁ U.1), y' ≫ pullback.snd _ _ = spMap (algebraMap c.F (DualNumber K)) ∧ spMap (FlagTan.red c K).toRingHom ≫ y' = frX P₀ ∧ ∀ r, ev (y' ≫ TF.Y.j) U.1 hU' r = TrivSqZeroExt.inl (ev (frX P₀ ≫ TF.Y.j) U.1 hU r) + TrivSqZeroExt.inr (ev (frX P₀ ≫ TF.Y.j) U.1 hU (D.1 r)) := by
  first | exact @GlobalTheory.LogPole.exists_tanPt_of_logDer | exact GlobalTheory.LogPole.exists_tanPt_of_logDer | (intros; apply GlobalTheory.LogPole.exists_tanPt_of_logDer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionOfArcVanishingSmoothChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_of_arc_vanishing_smooth_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ) (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)), ArcZero X Z la σ m → ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι) (p : Γ(Y₀ X Z, W)) (hi : W ≤ (L₀ X Z la).U i), IsDomain Γ(Y₀ X Z, W) → RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom → p ≠ 0 → (∀ y' ∈ W, (y' ∈ bd₀ X Z ↔ y' ∉ (Y₀ X Z).basicOpen p)) → ∃ b : Γ(Y₀ X Z, W), (∀ y' (h : y' ∈ W) (h' : y' ∈ U₀ X Z), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∈ bd₀ X Z → ger y' h b ∈ IsLocalRing.maximalIdeal ((Y₀ X Z).presheaf.stalk y') := by
  first | exact @GlobalTheory.CompHS.exists_extension_of_arcZero | exact GlobalTheory.CompHS.exists_extension_of_arcZero | (intros; apply GlobalTheory.CompHS.exists_extension_of_arcZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTruncatedFrameChartResidueCharZerStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_truncatedFrame_chart_residue_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), CharZero (ResidueField T.V) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (r : ℕ) (C : IntegralChartA3 Xo c T' io' y') (P : PELUnif (maximalIdeal T'.V) C.I.G), CharZero (ResidueField T'.V) ∧ 0 < r ∧ FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ GlobalTheory.SlopeRec.HasPhi y' (r * φ) ∧ ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ) (s : c.F), ∀ f ∈ thGen Xo c nab a n, nval T'.V (r * e) (io' s * evI y' f) = nval T.V e (io s * evI y f) := by
  first | exact @GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero | exact GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero | (intros; apply GlobalTheory.ExtScaleZero.exists_ext_chart_scale_charZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorFieldPointThroughGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.factor_gp (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (L : Type) [Field L] (ρ : R →+* L)
    (y : Sp L ⟶ M.S) (hρ : Function.Injective ρ) (hy : y ≫ M.π = spMap ρ) :
    ∃ ga : FractionRing R →+* L, (∀ r, ga (algebraMap R _ r) = ρ r) ∧ y = spMap ga ≫ M.gp := by
  have hI := M.integral
  have hdom := M.dominant
  have hsub : ∀ (K : Type) [Field K] (a b : Sp K), a = b := fun K _ a b =>
    PrimeSpectrum.ext (by haveI := a.isPrime; haveI := b.isPrime; rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])
  let p : Sp L := IsLocalRing.closedPoint L
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y p) (U := ⊤) trivial
  have hyV : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]; rintro _ ⟨z, rfl⟩; rw [hsub L z p]; exact hxV
  obtain ⟨q, hq⟩ := M.gp.denseRange.exists_mem_open V.isOpen ⟨y p, hxV⟩
  have hgV : Set.range M.gp ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]; rintro _ ⟨z, rfl⟩; rw [hsub (FractionRing R) z q]; exact hq
  haveI : Nonempty V := ⟨⟨y p, hxV⟩⟩
  haveI : IsDomain Γ(M.S, V) := IsIntegral.component_integral V
  set yV := IsOpenImmersion.lift hV.fromSpec y hyV with hyVdef
  set gV := IsOpenImmersion.lift hV.fromSpec M.gp hgV with hgVdef
  have hyf : yV ≫ hV.fromSpec = y := IsOpenImmersion.lift_fac _ _ _
  have hgf : gV ≫ hV.fromSpec = M.gp := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨by', hby⟩ := Spec.map_surjective yV
  obtain ⟨bg, hbg⟩ := Spec.map_surjective gV
  obtain ⟨c, hc⟩ := Spec.map_surjective (hV.fromSpec ≫ M.π)
  have hcy : by'.hom.comp c.hom = ρ := by
    have e : Spec.map (c ≫ by') = Spec.map (CommRingCat.ofHom ρ) := by
      rw [Spec.map_comp, hby, hc, ← Category.assoc, hyf, hy]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hcg : bg.hom.comp c.hom = algebraMap R (FractionRing R) := by
    have e : Spec.map (c ≫ bg) = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
      rw [Spec.map_comp, hbg, hc, ← Category.assoc, hgf, M.gp_π]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  have hdV : IsDominant gV := by
    haveI : IsDominant (gV ≫ hV.fromSpec) := by rw [hgf]; exact hdom
    exact IsDominant.of_comp_of_isOpenImmersion gV hV.fromSpec
  have hinj : Function.Injective bg.hom := by
    rw [← hbg] at hdV
    have h := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical bg.hom).1 hdV.denseRange
    rw [nilradical_eq_zero] at h
    exact (RingHom.injective_iff_ker_eq_bot _).2 (le_bot_iff.1 h)
  let ga : FractionRing R →+* L := IsFractionRing.lift hρ
  have hga : ∀ r, ga (algebraMap R _ r) = ρ r := IsFractionRing.lift_algebraMap hρ
  have key : ∀ b, by'.hom b = ga (bg.hom b) := by
    intro b
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) (bg.hom b)
    have hs0 : ρ s ≠ 0 := (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero s.2)
    have hcs : bg.hom (c.hom s) = algebraMap R (FractionRing R) s := RingHom.congr_fun hcg s
    have hcr : bg.hom (c.hom r) = algebraMap R (FractionRing R) r := RingHom.congr_fun hcg r
    have h1 : c.hom s * b = c.hom r := hinj (by
      rw [map_mul, hcs, hcr, ← hrs]; exact IsLocalization.mk'_spec' (FractionRing R) r s)
    have h2 := congrArg by'.hom h1
    have hys : by'.hom (c.hom s) = ρ s := RingHom.congr_fun hcy s
    have hyr : by'.hom (c.hom r) = ρ r := RingHom.congr_fun hcy r
    rw [map_mul, hys, hyr] at h2
    rw [← hrs, IsFractionRing.lift_mk', eq_div_iff hs0, mul_comm]
    exact h2
  refine ⟨ga, hga, ?_⟩
  have e : by' = bg ≫ CommRingCat.ofHom ga := by ext b; exact key b
  rw [← hyf, ← hby, e, Spec.map_comp, Category.assoc, hbg, hgf]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAdditiveLineBundleFamilyAffineStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_additiveLineBundleFamily_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (T : Over (Sp R)) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ∃ (T₀ : Over (Sp R)) (h : T ⟶ T₀) (N₀ : LB (A ⊗ T₀).left), IsAffine T₀.left ∧ LocallyOfFiniteType T₀.hom ∧ Fam A N₀ ∧ Same A N N₀ (𝟙 T) h := by
  first | exact @GlobalTheory.DualApprox.exists_fam_finiteType | exact GlobalTheory.DualApprox.exists_fam_finiteType | (intros; apply GlobalTheory.DualApprox.exists_fam_finiteType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAwayOfAtPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime : ∀ (R C : Type) [CommRing R] [IsNoetherianRing R] [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime], algebraMap R C f ≠ 0 → Algebra.FiniteType R (Localization.Away (algebraMap R C f)) → Algebra.FiniteType (Localization.AtPrime 𝔭) (TensorProduct R (Localization.AtPrime 𝔭) C) → ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by
  first | exact @GlobalTheory.Desc.exists_finiteType_away_of_atPrime | exact GlobalTheory.Desc.exists_finiteType_away_of_atPrime | (intros; apply GlobalTheory.Desc.exists_finiteType_away_of_atPrime <;> assumption)
end

