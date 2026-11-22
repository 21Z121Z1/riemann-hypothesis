import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsProperCurveThroughPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0047
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfIsEtaleCompletion
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.RegSmooth

theorem spanFinrank_top_eq_finrank_residueField (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    (⊤ : Submodule R M).spanFinrank = Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) := by
  rw [← TensorProduct.spanFinrank_top_eq_of_residueField (⊤ : Submodule R M) Module.Finite.fg_top,
    ← Module.finrank_eq_spanFinrank_of_free]
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (ResidueField R) (ResidueField R))
    (Submodule.topEquiv (R := R) (M := M))).finrank_eq

theorem spanFinrank_top_tensor_eq {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] {N : Type*} [AddCommGroup N]
    [Module A N] [Module.Finite A N] :
    (⊤ : Submodule B (B ⊗[A] N)).spanFinrank = (⊤ : Submodule A N).spanFinrank := by
  rw [spanFinrank_top_eq_finrank_residueField, spanFinrank_top_eq_finrank_residueField]
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange A B (ResidueField B)
    (ResidueField B) N
  let e₂ := TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField B)
    (ResidueField B) N
  rw [e₁.finrank_eq, ← e₂.finrank_eq, Module.finrank_baseChange]

theorem spanFinrank_map_eq_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] (I : Ideal A) :
    (I.map (algebraMap A B)).spanFinrank = (⊤ : Submodule B (B ⊗[A] I)).spanFinrank := by
  let g : B ⊗[A] I →ₗ[B] B :=
    (TensorProduct.AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ
      TensorProduct.AlgebraTensorModule.lTensor B B I.subtype
  have hg : Function.Injective g := by
    have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor B B I.subtype) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective
    exact (TensorProduct.AlgebraTensorModule.rid A B B).injective.comp h1
  have hr : Submodule.map g ⊤ = I.map (algebraMap A B) := by
    apply le_antisymm
    · rintro _ ⟨x, -, rfl⟩
      induction x with
      | zero => simp
      | tmul b i =>
        have : g (b ⊗ₜ i) = b * algebraMap A B i := by
          simp [g, Algebra.smul_def, mul_comm]
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ i.2)
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rw [Ideal.map, Ideal.span_le]
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨(1 : B) ⊗ₜ ⟨i, hi⟩, trivial, ?_⟩
      simp [g, Algebra.smul_def]
  rw [← hr, Submodule.spanFinrank_map_eq_of_injective g hg]

theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim A = ringKrullDim B := by
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have e := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [h, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at e
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, e]

theorem isRegularLocalRing_of_flat_of_map_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  have hd := ringKrullDim_eq_of_flat_of_map_maximalIdeal h
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le A ?_, hd⟩
  have e : (maximalIdeal A).spanFinrank = (maximalIdeal B).spanFinrank := by
    rw [← h, spanFinrank_map_eq_of_flat, spanFinrank_top_tensor_eq, Submodule.spanFinrank_top]
  rw [e, hd]
  exact ((isRegularLocalRing_iff B).mp inferInstance).le

theorem isRegularLocalRing_of_flat_of_map_maximalIdeal' {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B) (hf : φ.Flat)
    (h : (maximalIdeal A).map φ = maximalIdeal B) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B := by
  algebraize [φ]
  have : IsLocalHom (algebraMap A B) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hna
    have : algebraMap A B a ∈ maximalIdeal B := h ▸ Ideal.mem_map_of_mem _ hm
    exact (mem_maximalIdeal _).1 this ha
  exact isRegularLocalRing_of_flat_of_map_maximalIdeal h

theorem isRegularLocalRing_of_isEtaleCompletion {A B : Type} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsRegularLocalRing B] (φ : A →+* B)
    (h : GlobalTheory.Toroidal.IsEtaleCompletion φ) :
    IsRegularLocalRing A ∧ ringKrullDim A = ringKrullDim B :=
  isRegularLocalRing_of_flat_of_map_maximalIdeal' φ h.1 h.2.1

theorem smoothOfRelativeDimension_of_isRegularLocalRing {F : Type} [Field F] [PerfectField F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of F)) [LocallyOfFiniteType f] (n : ℕ)
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      IsRegularLocalRing (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) = n) :
    SmoothOfRelativeDimension n f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension n)
    X.affineOpenCover.openCover fun i => ?_
  let R : CommRingCat.{0} := X.affineOpenCover.X i
  let x : Spec R ⟶ X := X.affineOpenCover.f i
  have hx : IsOpenImmersion x := X.affineOpenCover.map_prop i
  let φ : CommRingCat.of F ⟶ R := Spec.preimage (x ≫ f)
  letI : Algebra F R := φ.hom.toAlgebra
  have hφ : x ≫ f = spMap (algebraMap F R) := (Spec.map_preimage (x ≫ f)).symm
  change SmoothOfRelativeDimension n (x ≫ f)
  rw [hφ]
  have hft : LocallyOfFiniteType (spMap (algebraMap F R)) := by rw [← hφ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType F R := RingHom.finiteType_algebraMap.mp hft
  refine GlobalTheory.RegGenSmooth.smooth_of_regular F R n fun m hm => ?_
  let y : Spec R := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  have hcl : IsClosed ({x y} : Set X) := by
    have h1 : IsClosed ({y} : Set (Spec R)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
    have he := x.isOpenEmbedding
    have hlc := IsLocallyClosed.image h1.isLocallyClosed he.isInducing
      he.isOpen_range.isLocallyClosed
    rw [Set.image_singleton] at hlc
    exact isClosed_singleton_of_isLocallyClosed_singleton hlc
  obtain ⟨h1, h2⟩ := h (x y) hcl
  let e := (asIso (x.stalkMap y) ≪≫ Spec.stalkIso R y).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

end GlobalTheory.RegSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.NefCurveTest

theorem smoothOfRelativeDimension_one {k : Type} [Field k] {C : Scheme.{0}} [IsIntegral C] (s : C ⟶ Sp k) [Smooth s]
    (hd : topologicalKrullDim C = 1) : SmoothOfRelativeDimension 1 s := by
  obtain ⟨n, hn⟩ : ∃ n, SmoothOfRelativeDimension n s := exists_dim_of_preconnected s (genericPoint C)
  obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have e := (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).symm.trans
    (SmoothDim.ringKrullDim_affineOpen k _ _ _ hn U hU ⟨x, hxU⟩)
  obtain rfl : 1 = n := by exact_mod_cast e
  exact hn

theorem exists_smooth_finite {k : Type} [Field k] [IsAlgClosed k] {D : Scheme.{0}} [IsIntegral D] (s : D ⟶ Sp k)
    [IsProper s] (hd : topologicalKrullDim D = 1) :
    ∃ (C : Scheme.{0}) (_ : IsIntegral C) (f : C ⟶ D), IsFinite f ∧ f (genericPoint C) = genericPoint D ∧
      topologicalKrullDim C = 1 ∧ Smooth (f ≫ s) := by
  let f := D.fromSpecResidueField (genericPoint D)
  let c := f.fromNormalization
  haveI : IsFinite c := NormCurve.isFinite_fromNormalization f s
  have htr : letI := (NormCurve.constHom (f ≫ s) ⊤).toAlgebra
      Algebra.trdeg k Γ(Spec (D.residueField (genericPoint D)), ⊤) ≤ 1 := by
    obtain ⟨x, hx⟩ := ProperCurve.exists_ne_genericPoint hd
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    have e : ⊤ ≤ f ⁻¹ᵁ U := fun z _ => by
      change f z ∈ U
      rw [Scheme.fromSpecResidueField_apply]
      exact VB.genericPoint_mem hxU
    letI := (NormCurve.constHom s U).toAlgebra
    haveI : Algebra.FiniteType k Γ(D, U) := NormCurve.finiteType_constHom s hU
    haveI : Nonempty (⊤ : (Spec (D.residueField (genericPoint D))).Opens) :=
      ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
    letI := (NormCurve.isField_sections (⊤ : (Spec (D.residueField (genericPoint D))).Opens)).toField
    letI := (NormCurve.constHom (f ≫ s) ⊤).toAlgebra
    letI := (f.appLE U ⊤ e).hom.toAlgebra
    haveI : IsScalarTower k Γ(D, U) Γ(Spec (D.residueField (genericPoint D)), ⊤) :=
      .of_algebraMap_eq' (NormCurve.appLE_comp_constHom s f U ⊤ e).symm
    exact (NormCurve.finite_integralClosure k (NormCurve.surjectiveOnStalks_appLE f hU ⊤ e)).2
      ((ringKrullDim_quotient_le _).trans (ProperCurve.ringKrullDim_eq_one hd hU hxU hx).le)
  have hξ : genericPoint D ∈ Set.range c := by
    refine ⟨f.toNormalization (Nonempty.some inferInstance), ?_⟩
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization, Scheme.fromSpecResidueField_apply]
  have hs : Function.Surjective c := fun y =>
    (genericPoint_specializes y).mem_closed c.isClosedMap.isClosed_range hξ
  have hη : c (genericPoint _) = genericPoint D := by
    obtain ⟨y, hy⟩ := hξ
    refine ((genericPoint_specializes _).antisymm ?_).eq.symm
    exact ((genericPoint_specializes y).map c.continuous).trans (specializes_of_eq hy)
  exact ⟨f.normalization, inferInstance, c, inferInstance, hη,
    ((Published.dim_le_of_isIntegralHom c).antisymm (PosBaseChange.dim_le_of_isClosedMap c.isClosedMap hs)).trans hd,
    CurveThrough.smooth_of_dedekind_charts k _ _ (NormCurve.isDedekindDomain_sections f s htr)⟩

def CurveTest (K : Type) [Field K] {X : Scheme.{0}} (L : LB X) : Prop :=
  ∀ (C : Scheme.{0}) [Algebra K Γ(C, ⊤)], SmoothOfRelativeDimension 1 (strHom K C) → IsProjOver (strHom K C) →
    GeometricallyConnected (strHom K C) → ∀ g : C ⟶ X, 0 ≤ interNum K (structureModule C) ![L.pull g]

theorem CurveTest.pull {K : Type} [Field K] {X Y : Scheme.{0}} {L : LB X} (h : CurveTest K L) (hL : L.IsLB)
    (π : Y ⟶ X) : CurveTest K (L.pull π) := fun C _ hs hp hc g => by
  refine (h C hs hp hc (g ≫ π)).trans_eq (interNum_congr_cls K _ (isLB_vecOne (LB.isLB_pull hL _))
    (isLB_vecOne (LB.isLB_pull (LB.isLB_pull hL _) _)) fun j => ?_)
  fin_cases j
  exact pull_comp g π (cls L hL)

theorem CurveTest.isNef_of_isAlgClosed {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} [Algebra K Γ(X, ⊤)]
    {L : LB X} (h : CurveTest K L) (hL : L.IsLB) : IsNef K L := by
  refine isNef_iff_isClosedImmersion.2 ⟨hL, fun D i _ _ hd hp => ?_⟩
  letI := algebraΓAlong K i
  have hi := appTop_algebraMap_along K i
  rw [comp_strHom hi] at hp
  obtain ⟨C, _, f, _, hη, hdC, hs⟩ := exists_smooth_finite (strHom K D) hd
  letI := algebraΓAlong K f
  have hf := appTop_algebraMap_along K f
  have hpC : IsProper (f ≫ strHom K D) := inferInstance
  rw [comp_strHom hf] at hs hpC
  have hM := LB.isLB_pull hL i
  have h₀ := h.pull hL i C (smoothOfRelativeDimension_one _ hdC) (ProperCurve.isProjOver_of_isProper _ hdC)
    (geometricallyConnected_of_isAlgClosed _) f
  have e₁ := ProjFin.interNumOn_eq_residueDegree_mul K D C f (ProperCurve.isProjOver_of_isProper _ hd) hd hη _ hM
  rw [interNumOn_eq_interNum_pull hf (isLB_vecOne hM)] at e₁
  rw [interNumOn_eq_interNum_pull hi (isLB_vecOne hL)]
  have hdeg : 0 < f.residueDegree (genericPoint C) := Nat.pos_of_ne_zero
    ((PullbackFinitePoint.residueDegree_ne_zero_iff_finite f _).2 (residueFieldMap_finite_of_locallyQuasiFinite f _))
  have e₂ : (fun j => ((![L.pull i] : Fin 1 → LB D) j).pull f) = ![(L.pull i).pull f] :=
    funext fun j => by fin_cases j; rfl
  have e₃ : (fun j => ((![L] : Fin 1 → LB X) j).pull i) = ![L.pull i] := funext fun j => by fin_cases j; rfl
  rw [e₂] at e₁
  rw [e₃]
  rw [e₁] at h₀
  exact nonneg_of_mul_nonneg_right h₀ (by exact_mod_cast hdeg)

theorem CurveTest.isNef (hN : Published.NefProductNonneg) {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)]
    {L : LB X} (h : CurveTest (AlgebraicClosure k) L) (hL : L.IsLB) : IsNef k L := by
  refine isNef_iff_isClosedImmersion.2 ⟨hL, fun D i _ _ hd hp => ?_⟩
  letI := algebraΓAlong k i
  have hi := appTop_algebraMap_along k i
  rw [comp_strHom hi] at hp
  have hM := LB.isLB_pull hL i
  obtain ⟨D', _, π, hp', hd', -, -, he⟩ :=
    Published.exists_algClosed_baseChange (ProperCurve.isProjOver_of_isProper (strHom k D) hd)
  rw [interNumOn_eq_interNum_pull hi (isLB_vecOne hL), ← he 1 _ fun j => LB.isLB_pull (isLB_vecOne hL j) i]
  refine hN _ D' 1 hp' (hd'.trans hd) _ fun j => ?_
  fin_cases j
  exact ((h.pull hL i).pull hM π).isNef_of_isAlgClosed (LB.isLB_pull hM π)

end GlobalTheory.NefCurveTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdParEqFlag
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open scoped TensorProduct

namespace GlobalTheory.TieStd

def leftStab {G : Type} [Group G] (φ : G → ℂ) : Subgroup G where
  carrier := {γ | ∀ g, φ (γ * g) = φ g}
  one_mem' := fun g => by simp
  mul_mem' := fun {a b} ha hb g => by rw [mul_assoc, ha, hb]
  inv_mem' := fun {a} ha g => by rw [← ha (a⁻¹ * g), mul_inv_cancel_left]

theorem stdPar_eq_flag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (S : Finset (Fin r)) (s : ℕ) (hs : s ≤ r), (∀ i : Fin r, i.val < s ↔ ∃ k ∈ S, i ≤ k) → ∀ d : Fin s → ℕ, (∀ i, d i = (S.filter (· < Fin.castLE hs i)).card) → GlobalTheory.StdPar.unip σ J X S = GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ∧ GlobalTheory.StdPar.levi σ J X Y S = GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d ∧ ∀ (K : Subgroup (GAd σ J)) (φ : GAd σ J → ℂ), GlobalTheory.StdPar.IsAutOn σ J X Y S K φ ↔ GlobalTheory.UAut.IsAutOn σ J (GlobalTheory.UAut.leftGrp σ J (X.submatrix id (Fin.castLE hs)) d) K φ := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW S s hs hS d hd
  have hu := le_antisymm (GlobalTheory.T.hermitianWittFrame_unipotent_le_flag_unipotent F E σ h n J hJ r X Y hW S s hs hS d hd) (GlobalTheory.T.unipotent_radical_graded_isotropic_flag_le F E σ h n J hJ r X Y hW S s hs hS d hd)
  have hl := le_antisymm (GlobalTheory.T.leviSubgroup_le_gradedIsotropicFlagLevi F E σ h n J hJ r X Y hW S s hs hS d hd) (GlobalTheory.T.gradedIsotropicFlagLevi_le_leviSubgroup F E σ h n J hJ r X Y hW S s hs hS d hd)
  have hg := (GlobalTheory.T.leviDecomposition_gradedIsotropicFlag F E σ h n J hJ s (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xx]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.yy]; ext; simp)
    (by rw [GlobalTheory.TieStd.cT_submatrix_mul, hW.xy]; exact Matrix.submatrix_one _ (Fin.castLE_injective hs))).2.2.1
  refine ⟨hu, hl, fun K φ => ⟨fun hφ => ⟨?_, hφ.level, hφ.cont, hφ.smooth, hφ.growth, GlobalTheory.UAut.kfin_iff.1 hφ.kfin, hφ.zfin⟩,
    fun hφ => ⟨fun u hu' g => hφ.left u ?_ g, fun γ hγ hγ' g => hφ.left γ ?_ g, hφ.level, hφ.cont, hφ.smooth, hφ.growth,
      GlobalTheory.UAut.kfin_iff.2 hφ.kfin, hφ.zfin⟩⟩⟩
  · rw [hg]
    have : GlobalTheory.UAut.unipFlag σ J (X.submatrix id (Fin.castLE hs)) d ⊔ (ratPts σ J ⊓ GlobalTheory.UAut.leviFlag σ J (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs)) d) ≤ leftStab φ :=
      sup_le (fun u hu' => hφ.leftN u (hu ▸ hu')) (fun γ hγ => hφ.leftM γ hγ.1 (hl ▸ hγ.2))
    exact fun γ hγ => this hγ
  · rw [hg]; exact Subgroup.mem_sup_left (hu ▸ hu')
  · rw [hg]; exact Subgroup.mem_sup_right ⟨hγ, hl ▸ hγ'⟩

end GlobalTheory.TieStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMeanValueFlagChartInvariantMeasure
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.SubmeanChart

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem card_strictLower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by
  have e : {p : Fin r × Fin r // p.2 < p.1} ≃ Σ a : Fin r, Finset.Iio a :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Finset.mem_Iio.2 p.2⟩
      invFun := fun x => ⟨(x.1, x.2.1), Finset.mem_Iio.1 x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_coe, Fin.card_Iio]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

theorem nd_eq_dimFl (X : Data E r) : nd X = dimFl E r := by
  unfold nd dimFl
  rw [Fintype.card_prod, card_strictLower, QuadraticCoefficientForms.card_Psi]

theorem cpt_zero (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ a b
  have h1 : mat (nmat X 0) τ = 1 := by
    ext i j
    simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
    by_cases h : j < i
    · rw [dif_pos h, if_neg (ne_of_gt h)]
      rfl
    · rw [dif_neg h]
  show (mat x0 τ * mat (nmat X 0) τ) a b = x0 τ a b
  rw [h1, Matrix.mul_one]
  rfl

theorem differentiable_cpt (X : Data E r) (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) := by
  rw [differentiable_pi]; intro τ
  rw [differentiable_pi]; intro a
  rw [differentiable_pi]; intro b
  simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  refine Differentiable.fun_sum fun k _ => Differentiable.const_mul ?_ _
  by_cases h : b < k
  · simp only [nmat, dif_pos h]
    fun_prop
  · simp only [nmat, dif_neg h]
    exact differentiable_const _

theorem norm_dmin_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm x τ i‖ = 1 := by
  unfold dmin lminor
  rw [hx τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  simp only [Function.comp_apply, sgn]
  split_ifs <;> simp

theorem nfac_of_orth (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : IsOrth X x) : X.nfac la x = 1 := by
  unfold Data.nfac
  refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun i _ => ?_
  rw [norm_div, norm_dmin_of_orth X hx, norm_dmin_of_orth X hx, div_one, Real.one_rpow]

theorem pnorm_eq (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl

theorem spread_nonneg (X : Data E r) (la : Wt X.Ψ r) (hr : 0 < r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  unfold Data.spread
  have i : Fin r := ⟨0, hr⟩
  have h1 := ciInf_le (Set.finite_range fun i => (la τ i : ℝ)).bddBelow i
  have h2 := le_ciSup (Set.finite_range fun i => (la τ i : ℝ)).bddAbove i
  linarith

theorem chartRad_pos (X : Data E r) (la : Wt X.Ψ r) {w : ℝ} (hr : 0 < r) (hw : (∑ τ, X.spread la τ) ≤ w) :
    0 < chartRad E r w := by
  have h0 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => spread_nonneg X la hr τ) hw
  have hf : (0 : ℝ) < fdeg E := by exact_mod_cast (QuadraticCoefficientForms.card_Psi X) ▸ QuadraticCoefficientForms.card_Psi_pos X
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  unfold chartRad
  positivity

end

end GlobalTheory.SubmeanChart

namespace GlobalTheory.SubmeanChart
noncomputable section

theorem submean_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r) (P : Frame X.Ψ r → ℂ), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w → DifferentiableOn ℂ P X.dom → ENNReal.ofReal (X.pnorm la P x ^ 2) ≤ ENNReal.ofReal (2 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r) * ∫⁻ z in Metric.ball (0 : V (nd X)) (chartRad E r w), ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
  intro E _ _ _ r X la w x P hr hx hw hP
  set ρ := chartRad E r w with hρdef
  have hρ : 0 < ρ := chartRad_pos X la hr hw
  have hch := GlobalTheory.T.normFactor_and_density_near_one_in_flagChart E r X la w x hr hx hw

  set φ : V (nd X) → ℂ := fun z => P (cpt X x z) with hφdef
  have hφ : DifferentiableOn ℂ φ (Metric.ball 0 ρ) :=
    hP.comp (differentiable_cpt X x).differentiableOn fun z hz =>
      (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).1
  have hsub := GlobalTheory.enorm_pow_le_inv_measure_mul_lintegral_ball (volume : Measure (V (nd X))) (a := 0) hρ hφ 2
  have hne : ENNReal.ofReal (Real.pi ^ nd X * ρ ^ (2 * nd X) / ((nd X).factorial : ℝ)) =
      ENNReal.ofReal (Real.pi ^ dimFl E r * ρ ^ (2 * dimFl E r) / ((dimFl E r).factorial : ℝ)) := by
    rw [nd_eq_dimFl]
  rw [GlobalTheory.volume_ball_euclideanSpace_complex (0 : V (nd X)) hρ, Fintype.card_fin, hne] at hsub
  set D := dimFl E r with hD

  have h1 : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ‖φ z‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp (1 / 20)) *
        ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    obtain ⟨-, hn, -⟩ := hch z (le_of_lt (mem_ball_zero_iff.1 hz))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [pnorm_eq, mul_pow]
    have he : 1 ≤ Real.exp (1 / 20) * X.nfac la (cpt X x z) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hn (Real.exp_pos (1 / 20)).le
      rwa [← Real.exp_add, show (1 / 20 : ℝ) + -(1 / 20) = 0 by norm_num, Real.exp_zero] at this
    calc ‖φ z‖ ^ 2 = ‖φ z‖ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖φ z‖ ^ 2 * (Real.exp (1 / 20) * X.nfac la (cpt X x z) ^ 2) :=
          mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by rw [hφdef]; ring

  have hμ : ENNReal.ofReal (Real.exp (-(1 / 10))) • (volume.restrict (Metric.ball (0 : V (nd X)) ρ)) ≤
      (muF X x).restrict (Metric.ball 0 ρ) := by
    have hb : Metric.ball (0 : V (nd X)) ρ ∩ OmF X x = Metric.ball 0 ρ :=
      Set.inter_eq_left.2 fun z hz => (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).1
    rw [muF, restrict_withDensity measurableSet_ball, Measure.restrict_restrict measurableSet_ball, hb,
      ← withDensity_const]
    refine withDensity_mono (ae_restrict_of_forall_mem measurableSet_ball fun z hz => ?_)
    exact ENNReal.ofReal_le_ofReal (hch z (le_of_lt (mem_ball_zero_iff.1 hz))).2.2
  have h2 : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ≤
      ENNReal.ofReal (Real.exp (1 / 10)) *
        ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
    have h3 := lintegral_mono' hμ (le_refl (fun z => ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2)))
    rw [lintegral_smul_measure, smul_eq_mul] at h3
    calc _ = ENNReal.ofReal (Real.exp (1 / 10)) * (ENNReal.ofReal (Real.exp (-(1 / 10))) *
          ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            show (1 / 10 : ℝ) + -(1 / 10) = 0 by norm_num, Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ _ := by gcongr

  have h0 : ENNReal.ofReal (X.pnorm la P x ^ 2) = ‖φ 0‖ₑ ^ 2 := by
    rw [pnorm_eq, nfac_of_orth X la hx, mul_one, show φ 0 = P x by simp only [hφdef, cpt_zero], ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

  have hvol : (ENNReal.ofReal (Real.pi ^ D * ρ ^ (2 * D) / (D.factorial : ℝ)))⁻¹ =
      ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), inv_div, mul_pow, ← pow_mul, mul_comm 2 D]
  have hexp : Real.exp (1 / 20) * Real.exp (1 / 10) ≤ 2 := by
    rw [← Real.exp_add]
    calc Real.exp (1 / 20 + 1 / 10) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.2 (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log two_pos
  have hc : ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
      (ENNReal.ofReal (Real.exp (1 / 20)) * ENNReal.ofReal (Real.exp (1 / 10))) ≤
      ENNReal.ofReal (2 * (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hq : 0 ≤ (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D := by positivity
    calc (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D * (Real.exp (1 / 20) * Real.exp (1 / 10))
        ≤ (D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D * 2 := mul_le_mul_of_nonneg_left hexp hq
      _ = _ := by ring
  rw [h0]
  calc ‖φ 0‖ₑ ^ 2 ≤ _ := hsub
    _ ≤ ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
          (ENNReal.ofReal (Real.exp (1 / 20)) * (ENNReal.ofReal (Real.exp (1 / 10)) *
            ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x))) := by
        rw [hvol]
        gcongr
        exact h1.trans (by gcongr)
    _ = (ENNReal.ofReal ((D.factorial : ℝ) / (Real.pi * ρ ^ 2) ^ D) *
          (ENNReal.ofReal (Real.exp (1 / 20)) * ENNReal.ofReal (Real.exp (1 / 10)))) *
            ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (X.pnorm la P (cpt X x z) ^ 2) ∂(muF X x) := by
        ring
    _ ≤ _ := by gcongr

end
end GlobalTheory.SubmeanChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitriangularChartMemDomainSmallBallStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangularChart_mem_domain_small_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (z : ReciprocityTheory.L2DbarEstimates.V (nd X)), IsOrth X x → ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → cpt X x z ∈ X.dom := by
  first | exact @GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le | exact GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le | (intros; apply GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le <;> assumption)
end

