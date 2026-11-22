import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilDatumAdelicSchwartz
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical

namespace GlobalTheory.WeilCont

theorem continuous_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om → GlobalTheory.WeilM.IsContOn (GlobalTheory.WeilM.adeleClass D.host.F) om := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ _ co hco ω hω om htr
  have hfin := GlobalTheory.T.exists_local_finiteDim_finiteParts_weilOperators D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hpt := GlobalTheory.T.continuous_transportedWeilOperator_groupVariable D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hbd := GlobalTheory.T.weilOperator_archimedeanSlice_schwartzSeminorm_bounded D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr
  have hpres := (GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr).1
  refine GlobalTheory.WeilCont.isContOn_of_local D.host.F hfin (fun Φ hΦ y => ?_)
  choose s hs using fun p => GlobalTheory.WeilCont.exists_slice D.host.F (hpres p Φ hΦ) y
  refine ⟨s, continuous_iff_continuousAt.2 fun p0 => GlobalTheory.T.schwartz_continuousAt_of_continuousAt_apply_of_bounded s p0 (fun v => ?_) (fun k n => ?_), hs⟩
  · simp_rw [hs]
    exact (hpt Φ hΦ _).continuousAt
  · obtain ⟨C, hC⟩ := hbd Φ hΦ y p0 k n
    refine ⟨C, hC.mono fun p hp v => ?_⟩
    have e : (⇑(s p)) = fun x => om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F x y) := funext (hs p)
    rw [e]
    exact hp v

end GlobalTheory.WeilCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh
open GlobalTheory.TopForm

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AdaptedFrame

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in

theorem exists_basis_dFun {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ)
    [SmoothOfRelativeDimension D p] {O : Y.Opens} {x : Y} (hxO : x ∈ O) :
    ∃ (U : Y.Opens) (f : Fin D → Γ(Y, U)) (b : Module.Basis (Fin D) Γ(Y, U) (Omega (algX p U))),
      U ≤ O ∧ x ∈ U ∧ IsAffineOpen U ∧ ∀ i, b i = dFun (algX p U) (f i) := by
  classical
  obtain ⟨V, hV, hx, hVO⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hxO
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), x ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  letI := (algX p (Y.basicOpen (t : Γ(Y, V)))).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k Γ(Y, Y.basicOpen (t : Γ(Y, V))) := h₂
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    ‹Algebra.IsStandardSmoothOfRelativeDimension D k Γ(Y, Y.basicOpen (t : Γ(Y, V)))›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨_, fun i => P.val (e.symm i), P.basisKaehler.reindex e, (Y.basicOpen_le _).trans hVO, hxt,
    hV.basicOpen _, fun i => by simp⟩

theorem linearIndependent_tmul_D {k A : Type} [CommRing k] [CommRing A] [IsLocalRing A] [Algebra k A]
    [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)] {J : Type} (f : J → A)
    (hf : ∀ j, f j ∈ IsLocalRing.maximalIdeal A)
    (h : LinearIndependent (IsLocalRing.ResidueField A) (fun j =>
      ((IsLocalRing.maximalIdeal A).toCotangent ⟨f j, hf j⟩ : IsLocalRing.CotangentSpace A))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun j => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f j)) := by
  have hs : Function.Surjective (algebraMap A (IsLocalRing.ResidueField A)) :=
    IsLocalRing.residue_surjective
  have hinj := GlobalTheory.SmoothTangent.kerCotangentToTensor_injective k A (IsLocalRing.ResidueField A) hs
  have hker : IsLocalRing.maximalIdeal A = RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)) :=
    IsLocalRing.ker_residue.symm
  let c := Ideal.Cotangent.equivOfEq _ _ hker
  let e : IsLocalRing.CotangentSpace A →ₗ[A] IsLocalRing.ResidueField A ⊗[A] Ω[A⁄k] :=
    KaehlerDifferential.kerCotangentToTensor k A (IsLocalRing.ResidueField A) ∘ₗ c.toLinearMap
  have he : Function.Injective (e.extendScalarsOfSurjective hs) := hinj.comp c.injective
  have := h.map' (e.extendScalarsOfSurjective hs) (LinearMap.ker_eq_bot.2 he)
  have key : ⇑(e.extendScalarsOfSurjective hs) ∘ (fun j =>
      ((IsLocalRing.maximalIdeal A).toCotangent ⟨f j, hf j⟩ : IsLocalRing.CotangentSpace A)) =
      fun j => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] KaehlerDifferential.D k A (f j) := by
    funext j
    simp only [Function.comp_apply, LinearMap.extendScalarsOfSurjective_apply, e, LinearMap.comp_apply,
    LinearEquiv.coe_coe, c]
    rw [Ideal.Cotangent.equivOfEq_toCotangent, KaehlerDifferential.kerCotangentToTensor_toCotangent]
    rfl
  rw [key] at this
  exact this

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in

theorem formallySmooth_residueField {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    (p : X ⟶ Sp k) {n : ℕ} [SmoothOfRelativeDimension n p] {U : X.Opens} (hU : IsAffineOpen U)
    (y : X) (hy : y ∈ U) [Algebra k (X.presheaf.stalk y)]
    (h : algebraMap k (X.presheaf.stalk y) = (X.presheaf.germ U y hy).hom.comp (algX p U)) :
    Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk y)) := by
  letI : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hy).hom.toAlgebra
  letI : Algebra k Γ(X, U) := (algX p U).toAlgebra
  haveI : IsScalarTower k Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' h
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  have hft : (algX p U).FiniteType := by
    have h₀ := HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    exact RingHom.FiniteType.comp h₀
      (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  haveI : Algebra.FiniteType k Γ(X, U) := hft
  haveI : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  haveI : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk y) :=
    Algebra.EssFiniteType.of_isLocalization _ (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
  haveI : Algebra.EssFiniteType k (X.presheaf.stalk y) :=
    Algebra.EssFiniteType.comp k Γ(X, U) (X.presheaf.stalk y)
  haveI : Algebra.EssFiniteType (X.presheaf.stalk y) (IsLocalRing.ResidueField (X.presheaf.stalk y)) :=
    inferInstance
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk y)) :=
    Algebra.EssFiniteType.comp k (X.presheaf.stalk y) _
  exact Algebra.FormallySmooth.of_perfectField

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in

theorem exists_adapted_frame : ∀ {X : Scheme.{0}} {p : X ⟶ Sp ℂ} {n : ℕ} [SmoothOfRelativeDimension n p] (y : X) {J : Type}
    [Fintype J] (f : J → X.presheaf.stalk y)
    (hf : ∀ j, f j ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y)),
    LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y))
      (fun j => ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).toCotangent ⟨f j, hf j⟩ :
        IsLocalRing.CotangentSpace (X.presheaf.stalk y))) →
    ∃ (U : X.Opens) (hy : y ∈ U) (z : Fin n → Γ(X, U)) (e : J → Fin n), Function.Injective e ∧
      (∀ j, X.presheaf.germ U y hy (z (e j)) = f j) ∧ IsFrame (dOn p z) := by
  classical
  intro X p n _ y J _ f hf hli

  choose V hyV s hs using fun j => X.presheaf.germ_exist (x := y) (f j)
  let O : X.Opens := ⟨⋂ j, (V j : Set X), isOpen_iInter_of_finite fun j => (V j).isOpen⟩
  have hyO : y ∈ O := Set.mem_iInter.2 hyV
  have hOV (j : J) : O ≤ V j := fun _ hx => Set.mem_iInter.1 hx j
  obtain ⟨U, x, b, hUO, hyU, hU, hb⟩ := exists_basis_dFun p n hyO
  let z₀ : J → Γ(X, U) := fun j => resG X (hUO.trans (hOV j)) (s j)
  have hz₀ (j : J) : (X.presheaf.germ U y hyU).hom (z₀ j) = f j := by
    rw [germ_resG]
    exact hs j

  let a : J → Fin n → Γ(X, U) := fun j l => b.repr (dFun (algX p U) (z₀ j)) l
  have ha (j : J) : dFun (algX p U) (z₀ j) = ∑ l, a j l • dFun (algX p U) (x l) := by
    conv_lhs => rw [← b.sum_repr (dFun (algX p U) (z₀ j))]
    simp only [hb, a]

  letI iΓ : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  letI iA : Algebra ℂ (X.presheaf.stalk y) :=
    ((X.presheaf.germ U y hyU).hom.comp (algX p U)).toAlgebra
  letI iΓA : Algebra Γ(X, U) (X.presheaf.stalk y) := (X.presheaf.germ U y hyU).hom.toAlgebra
  haveI : IsScalarTower ℂ Γ(X, U) (X.presheaf.stalk y) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := formallySmooth_residueField (n := n) p hU y hyU rfl
  have hw := linearIndependent_tmul_D (k := ℂ) f hf hli
  let ρ : Γ(X, U) →+* IsLocalRing.ResidueField (X.presheaf.stalk y) :=
    (IsLocalRing.residue (X.presheaf.stalk y)).comp (X.presheaf.germ U y hyU).hom
  let ab : J → Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) := fun j l => ρ (a j l)
  have hab : LinearIndependent (IsLocalRing.ResidueField (X.presheaf.stalk y)) ab := by
    let wx : Fin n → IsLocalRing.ResidueField (X.presheaf.stalk y) ⊗[X.presheaf.stalk y]
        Ω[(X.presheaf.stalk y)⁄ℂ] :=
      fun l => 1 ⊗ₜ KaehlerDifferential.D ℂ (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (x l))
    refine LinearIndependent.of_comp (Fintype.linearCombination _ wx) ?_
    have key : ⇑(Fintype.linearCombination (IsLocalRing.ResidueField (X.presheaf.stalk y)) wx) ∘ ab =
        fun j => (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)) ⊗ₜ[X.presheaf.stalk y]
          KaehlerDifferential.D ℂ (X.presheaf.stalk y) (f j) := by
      funext j
      rw [Function.comp_apply, Fintype.linearCombination_apply, ← hz₀ j]
      have e1 := congrArg (KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y)) (ha j)
      rw [map_sum] at e1
      change KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D ℂ Γ(X, U) (z₀ j)) = _ at e1
      rw [KaehlerDifferential.map_D] at e1
      change KaehlerDifferential.D ℂ (X.presheaf.stalk y) ((X.presheaf.germ U y hyU).hom (z₀ j)) = _ at e1
      rw [e1, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      change _ = 1 ⊗ₜ (a j l • KaehlerDifferential.map ℂ ℂ Γ(X, U) (X.presheaf.stalk y)
        (KaehlerDifferential.D ℂ Γ(X, U) (x l)))
      rw [KaehlerDifferential.map_D, ← algebraMap_smul (X.presheaf.stalk y) (a j l),
        TensorProduct.tmul_smul, ← algebraMap_smul (IsLocalRing.ResidueField (X.presheaf.stalk y))]
      rfl
    rw [key]
    exact hw

  obtain ⟨e, he, hdet⟩ := GlobalTheory.T.exists_standard_basis_extension_det_ne_zero ab hab
  let z : Fin n → Γ(X, U) := Function.extend e z₀ x
  let c : Matrix (Fin n) (Fin n) Γ(X, U) :=
    Matrix.of (Function.extend e a (fun i => Pi.single i (1 : Γ(X, U))))
  have hdz (i : Fin n) : dFun (algX p U) (z i) = ∑ l, c i l • dFun (algX p U) (x l) := by
    by_cases hi : ∃ j, e j = i
    · obtain ⟨j, rfl⟩ := hi
      simp only [z, c, Matrix.of_apply, he.extend_apply]
      exact ha j
    · simp only [z, c, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
      simp [Pi.single_apply]
  have hform : dOn p z = c.det • dOn p x := dForm_eq_det_smul z x c hdz
  have hρ : ρ c.det ≠ 0 := by
    have hm : c.map ρ = Matrix.of (Function.extend e ab
        (fun i => Pi.single i (1 : IsLocalRing.ResidueField (X.presheaf.stalk y)))) := by
      ext i l
      by_cases hi : ∃ j, e j = i
      · obtain ⟨j, rfl⟩ := hi
        simp only [c, ab, Matrix.map_apply, Matrix.of_apply, he.extend_apply]
      · simp only [c, Matrix.map_apply, Matrix.of_apply, Function.extend_apply' _ _ _ hi]
        by_cases hil : l = i
        · subst hil
          simp
        · simp [Pi.single_apply, hil]
    rw [RingHom.map_det]
    exact (congrArg Matrix.det hm).trans_ne hdet
  have hunit : IsUnit ((X.presheaf.germ U y hyU).hom c.det) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hρ
  have hyW : y ∈ X.basicOpen c.det := (X.mem_basicOpen c.det y hyU).2 hunit
  have hWU : X.basicOpen c.det ≤ U := X.basicOpen_le _
  refine ⟨X.basicOpen c.det, hyW, fun i => resG X hWU (z i), e, he, fun j => ?_, ?_⟩
  · rw [germ_resG]
    simp only [z, he.extend_apply]
    exact hz₀ j
  · have hx : IsFrame (dOn p x) := ⟨hU, isFreeGen_dForm x b hb⟩
    have h1 := hx.res (hU.basicOpen c.det) hWU
    refine ⟨hU.basicOpen c.det, ?_⟩
    rw [← resForm_dOn hWU, hform, resForm_smul]
    exact h1.gen.smul_iff.2 (RingedSpace.isUnit_res_basicOpen X.toRingedSpace c.det)

end GlobalTheory.AdaptedFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoversOfLifts
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.CovSz

theorem covers_and
    {Q Q' : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : Covers fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP)
    (h' : Covers fun Fm x hx ι p i Y PP _ => Q' Fm x hx ι p i Y PP) :
    Covers fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP ∧ Q' Fm x hx ι p i Y PP := by
  refine (Formalism.MainNotions.Closed.and h h').imp fun Fm CH _ hh => ?_
  obtain ⟨⟨C, hC, a, ha⟩, ⟨C', hC', b, hb⟩⟩ := hh
  exact ⟨C, hC, max a b, fun x hx hle ι p hp i hi Y hY =>
    ⟨ha x hx ((le_max_left _ _).trans hle) ι p hp i hi Y hY, hb x hx ((le_max_right _ _).trans hle) ι p hp i hi Y hY⟩⟩

theorem covers_of_lifts
    {P : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (PP C : ℝ), Prop}
    {Q : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : Lifts P)
    (hQ : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (C : ℝ), RowsT p → P Fm x hx ι p i (Fm.parT x hx ι).PP C → (i : ℕ) + 1 < (Fm.D x ι).R.m →
      ∀ Y : Cov p i, GoodCov p i Y → Q Fm x hx ι p i Y (Fm.parT x hx ι).PP) :
    Covers fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP := by
  refine h.imp fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY => hQ Fm x hx ι p i C hp (ha x hx hle ι p hp i) hi Y hY⟩

theorem covers_imp
    {Q R : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP : ℝ), Prop}
    (h : Covers fun Fm x hx ι p i Y PP _ => Q Fm x hx ι p i Y PP)
    (hQ : ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (PP : ℝ), Q Fm x hx ι p i Y PP → R Fm x hx ι p i Y PP) :
    Covers fun Fm x hx ι p i Y PP _ => R Fm x hx ι p i Y PP := by
  refine h.imp fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY => hQ Fm x hx ι p i Y _ (ha x hx hle ι p hp i hi Y hY)⟩

end GlobalTheory.CovTop.CovSz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology

namespace GlobalTheory.CovTop.Assembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tendsto_exp_mul_rpow {c : ℝ} (hc : 0 < c) (A : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-(x ^ c)) * x ^ A) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / c) 1 one_pos).comp (tendsto_rpow_atTop hc)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp]
  rw [← Real.rpow_mul hx, mul_div_cancel₀ _ hc.ne', mul_comm, neg_mul, one_mul]

theorem exists_loss_le {c : ℝ} (hc : 0 < c) (A B C : ℝ) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → 12 * Real.exp (-(x ^ c)) * (x ^ A + x ^ B + C) ≤ 1 := by
  have h := ((((tendsto_exp_mul_rpow hc A).add (tendsto_exp_mul_rpow hc B)).add
    ((tendsto_exp_mul_rpow hc 0).mul_const C)).const_mul 12)
  have h1 : (12 : ℝ) * (0 + 0 + 0 * C) < 1 := by norm_num
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds h1))
  refine ⟨x0, fun x hx => ?_⟩
  have := hx0 x hx
  simp only [Real.rpow_zero] at this
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem lcv_le {A B PP C1 C2 : ℝ} (hx : 0 < L.sc.x) (h1 : 0 ≤ C1) (h2 : 0 ≤ C2)
    (hs : 12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * (L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) ≤ 1)
    (hG : GramAt p i) (hR : RecAt p i) (hC : CutAt p i) (hB : BadAt p i) (hL : LamAt p i A) (hS : SizeAt p i PP B)
    (hK : CoreAt p i C1) (hW : LowAt p i C2) :
    Formalism.DivisionValues.lcv ((p.S false).XW i) ((p.S false).M i) / ((p.S false).D : ℝ) ≤ mainT p i + (C1 + C2 + 1) * unitE p := by
  haveI : IsTotallyComplex D.what₂.LL := D.tcLL
  obtain ⟨g1, g2, g3, -⟩ := hG
  obtain ⟨c1, c2, c3, c4⟩ := hC
  obtain ⟨s1, s2, -, s4, -⟩ := hS
  unfold RecAt at hR
  unfold LamAt at hL
  unfold CoreAt at hK
  unfold LowAt at hW
  have hA := Real.rpow_pos_of_pos hx A
  have hB' := Real.rpow_pos_of_pos hx B
  have hδ := Real.exp_pos (-(L.sc.x ^ (L.sc.ez / 7)))
  have hm := (abs_le.1 s4).2
  have key := GlobalTheory.CutNum.slope_good_ge D.what₂.LL _ (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i)
    (latAll p.R.toRealDat i) (eGood p.R.toRealDat i) (Fintype.card p.P.Gp) (Real.exp (-(L.sc.x ^ (L.sc.ez / 7))))
    ((L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p) g1 g2 inf_le_left
    (fun h => g3 (le_bot_iff.1 (h ▸ latGood_le p.R.toRealDat p.F.lv2 i))) c1 c2 Fintype.card_pos c3 hδ.le
  have key' : slope_sq (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i) -
      12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * ((L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p) ≤
      slope_sq (nrmR p.R.toRealDat i) (latGood p.R.toRealDat p.F.lv2 i) := by
    refine key ?_ hB ?_ ?_ ?_
    all_goals
      clear key hR
      generalize Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) = δ at *
      generalize L.sc.x ^ A = a at *
      generalize L.sc.x ^ B = b at *
      generalize unitE p = E at *
      have hE : 0 ≤ E := by linarith
      have ea := mul_le_mul_of_nonneg_left s2 hA.le
      have eb := mul_le_mul_of_nonneg_left s2 hB'.le
      have e1 := mul_nonneg h1 hE
      have e2 := mul_nonneg h2 hE
      have e3 := mul_nonneg hA.le hE
      have e4 := mul_nonneg hB'.le hE
    · nlinarith [mul_nonneg hδ.le hA.le, mul_nonneg hδ.le hB'.le, mul_nonneg hδ.le h1, mul_nonneg hδ.le h2]
    · linarith
    · linarith
    · linarith
  have hE : 0 ≤ unitE p := by linarith
  have := mul_le_mul_of_nonneg_right hs hE
  rw [mul_assoc] at this
  linarith

theorem covolX_of_steps : Gram → Rec → Cut → Bad → abelian₂ → Size → CoreLe → Low → CovolX := by
  intro hG hR hC hB hL hS hK hW
  refine Closed.imp (Closed.and (Closed.and (Closed.and hG hR) (Closed.and hC hB))
    (Closed.and (Closed.and hL hS) (Closed.and hK hW))) ?_
  rintro eps Fm CH he ⟨⟨⟨⟨_, -, g⟩, ⟨_, -, r⟩⟩, ⟨⟨_, -, c⟩, ⟨_, -, b⟩⟩⟩, ⟨⟨A, -, l⟩, ⟨B, -, s⟩⟩, ⟨C1, h1, k⟩, ⟨C2, h2, w⟩⟩
  have hez : 0 < Fm.ez := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_ez 0 i]
    exact (Fm.L 0 i).sc.ez_pos
  obtain ⟨x0, hx0⟩ := exists_loss_le (show 0 < Fm.ez / 7 by positivity) A B (C1 + C2 + 1)
  obtain ⟨x1, h⟩ := (((g.and r).and (c.and b)).and ((l.and s).and (k.and w)))
  refine ⟨C1 + C2 + 1, by linarith, max x0 x1, fun x hx hle ι p hp C hC i => ?_⟩
  obtain ⟨⟨⟨g, r⟩, c, b⟩, ⟨l, s⟩, k, w⟩ := h x hx ((le_max_right _ _).trans hle) ι p hp
  have ex := Fm.L_x x ι hx
  have ee := Fm.L_ez x ι
  have hs := hx0 x ((le_max_left _ _).trans hle)
  have hx' : 0 < x := (zero_lt_one.trans Fm.one_lt_family_threshold).trans hx
  have main := lcv_le p i (ex.symm ▸ hx') h1 h2 (by rw [ex, ee]; exact hs) (g i) (r i) (c i) (b i) (l i) (s i) (k i) (w i)
  have hE : 0 ≤ unitE p := by
    obtain ⟨s1, s2, -⟩ := s i
    linarith
  refine main.trans ?_
  show mainT p i + (C1 + C2 + 1) * unitE p ≤ mainT p i + C * unitE p
  have := mul_le_mul_of_nonneg_right hC hE
  linarith

end GlobalTheory.CovTop.Assembly

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormProductLatticeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_product_lattice : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b), GlobalTheory.CovTop.Hypotheses₂ → ∃ g : Cusp Z Y.U (a + b), g.1 = w.1 * f.1 ∧ (w ∈ latOn Y.U Z _ → f ∈ latOn Y.U Z _ → g ∈ latOn Y.U Z _) := by
  first | exact @GlobalTheory.HSApp.cusp_mul | exact GlobalTheory.HSApp.cusp_mul | (intros; apply GlobalTheory.HSApp.cusp_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLargeInertPrimeStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthOscillation_large_inertPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ discr E → InertInK H p → k ≤ m * p → OscLe Xo c p cx ((6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1) := by
  first | exact @GlobalTheory.RefSum.InertOsc.oscLe_inert_large | exact GlobalTheory.RefSum.InertOsc.oscLe_inert_large | (intros; apply GlobalTheory.RefSum.InertOsc.oscLe_inert_large <;> assumption)
end

