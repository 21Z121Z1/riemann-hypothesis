import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0003
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0324
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
open scoped Pointwise Topology

namespace GlobalTheory.AutomorphicL2Local

theorem continuous_integral_inv_mul_of_locallyIntegrable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] {μ : Measure G} {f φ : G → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hφ : LocallyIntegrable φ μ) :
    (∀ x, Integrable (fun y => f (x⁻¹ * y) * φ y) μ) ∧ Continuous fun x => ∫ y, f (x⁻¹ * y) * φ y ∂μ := by
  have hi : ∀ x, Integrable (fun y => f (x⁻¹ * y) * φ y) μ := fun x =>
    hφ.integrable_smul_left_of_hasCompactSupport (g := fun y => f (x⁻¹ * y)) (by fun_prop)
      (hc.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  refine ⟨hi, continuous_iff_continuousAt.2 fun x₀ => ?_⟩
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hK : IsCompact (U * tsupport f) := hU.mul hc.isCompact
  refine continuousAt_of_dominated (bound := (U * tsupport f).indicator fun y => M * ‖φ y‖)
    (.of_forall fun x => (hi x).1) ?_ ?_ (.of_forall fun y => ?_)
  · filter_upwards [hx] with x hxU
    refine .of_forall fun y => ?_
    by_cases hy : y ∈ U * tsupport f
    · rw [Set.indicator_of_mem hy, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy,
        image_eq_zero_of_notMem_tsupport (f := f) fun h => hy ⟨x, hxU, _, h, by simp⟩]
      simp
  · exact (integrable_indicator_iff hK.measurableSet).2 ((hφ.integrableOn_isCompact hK).norm.const_mul M)
  · exact Continuous.continuousAt (by fun_prop)

theorem continuous_convR_lift : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f : G → ℂ, Continuous f → HasCompactSupport f → ∀ F : L2 Γ μ, (∀ x, Integrable (fun y => f y * lift Γ F (x * y)) μ) ∧ Continuous (convR μ f (lift Γ F)) := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ f hf hc F
  have hφ : LocallyIntegrable (lift Γ F) μ :=
    locallyIntegrable_iff.2 fun C hC => (memLp_restrict_compact G Γ μ F C hC).2
  obtain ⟨h1, h2⟩ := continuous_integral_inv_mul_of_locallyIntegrable hf hc hφ
  refine ⟨fun x => ?_, h2.congr fun x => (convR_eq f _ x).symm⟩
  simpa using (h1 x).comp_mul_left x

end GlobalTheory.AutomorphicL2Local
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivSplitPrime
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.SplitCompletion

theorem continuous_of_valued_eq {A B Γ : Type*} [Ring A] [Ring B] [LinearOrderedCommGroupWithZero Γ]
    [Valued A Γ] [Valued B Γ] (hs : Function.Surjective (Valued.v : A → Γ)) (f : A →+* B)
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : Continuous f := by
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero A _).tendsto_iff (Valued.hasBasis_nhds_zero B _)]
  intro γ _
  obtain ⟨a, ha⟩ := hs (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have ha0 : (Valued.v : Valuation A Γ).restrict a ≠ 0 := by
    simp [ha]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  rw [hf, ← ha]
  exact hx

open scoped WithZeroTopology in

theorem exists_extension {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (w : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 L)) (f : K →+* u.adicCompletion L)
    (hf : ∀ x, Valued.v (f x) = w.valuation K x) :
    ∃ φ : w.adicCompletion K →+* u.adicCompletion L, Continuous φ ∧
      (∀ x : K, φ (algebraMap K _ x) = f x) ∧ ∀ y, Valued.v (φ y) = Valued.v y := by
  first
  | exact @_root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension
  | exact _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension
  | (apply _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ContinuousValuationExtension.exists_continuous_extension ..)

theorem exists_ringEquiv_splitPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v),
    ∃ φ : (GlobalTheory.AdelicU.splitPrime τ).adicCompletion E ≃+* Fv F v, (∀ x : E, φ (algebraMap E _ x) = τ x) ∧
      (∀ y, Valued.v (φ y) = Valued.v y) ∧ Continuous φ ∧ Continuous φ.symm := by
  intro F E _ _ _ _ _ v τ
  obtain ⟨φ, hφc, hφ, hφv⟩ := exists_extension (GlobalTheory.AdelicU.splitPrime τ) v (τ : E →+* Fv F v)
    (GlobalTheory.AdelicU.valued_apply_eq_valuation τ)
  obtain ⟨ψ, hψc, hψ, -⟩ := exists_extension v (GlobalTheory.AdelicU.splitPrime τ)
    ((algebraMap E _).comp (algebraMap F E)) fun a =>
      (ReciprocityTheory.Aut.adic_valued_algebraMap _ _).trans ((GlobalTheory.AdelicU.valued_apply_eq_valuation τ _).symm.trans
        (GlobalTheory.AdelicU.valued_apply_algebraMap τ a))
  have hid : φ ∘ ψ = id := (HeightOneSpectrum.denseRange_algebraMap F v).equalizer (hφc.comp hψc) continuous_id
    (funext fun a => ((congrArg φ (hψ a)).trans (hφ _)).trans (τ.commutes a))
  let e := RingEquiv.ofBijective φ ⟨φ.injective, fun y => ⟨ψ y, congrFun hid y⟩⟩
  refine ⟨e, hφ, hφv, hφc, continuous_of_valued_eq (v.valuedAdicCompletion_surjective F) e.symm.toRingHom fun y => ?_⟩
  exact (hφv _).symm.trans (congrArg _ (e.apply_symm_apply y))

end GlobalTheory.SplitCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAndMass
section
noncomputable section

namespace GlobalTheory.DefiniteDecomp

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers GlobalTheory.Mass NumberField
open scoped TensorProduct Matrix

theorem exists_reps {G : Type} [Group G] {Γ K : Subgroup G} (h : FiniteClasses Γ K) :
    ∃ (n : ℕ) (g : Fin n → G), (∀ x : G, ∃ i, ∃ γ : Γ, ∃ k : K, x = (γ : G) * g i * k) ∧
      (∀ i j (γ γ' : Γ) (k k' : K), (γ : G) * g i * k = (γ' : G) * g j * k' → i = j) ∧
      (∀ i, (Unfold.stab Γ K (g i)).Finite) ∧
      ∑ i, ((Nat.card (Unfold.stab Γ K (g i)) : ℝ))⁻¹ = classMass Γ K := by
  haveI := h.1
  obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin (Formalism.UG.ClassSet Γ K)
  have e : ∀ g, Unfold.stab Γ K g = Formalism.UG.stabAt Γ K g := fun g => by
    ext γ; simp only [Unfold.stab, Formalism.UG.stabAt, mul_assoc]
  refine ⟨n, fun i => (φ.symm i).out, fun x => ?_, fun i j γ γ' k k' e => ?_, fun i => ?_, ?_⟩
  · obtain ⟨γ, hγ, k, hk, e⟩ := (DoubleCoset.eq Γ K _ x).1 (DoubleCoset.out_eq' Γ K (DoubleCoset.mk Γ K x))
    refine ⟨φ (DoubleCoset.mk Γ K x), ⟨γ, hγ⟩, ⟨k, hk⟩, ?_⟩
    exact e.trans (congrArg (fun c : Formalism.UG.ClassSet Γ K => γ * c.out * k) (φ.symm_apply_apply _).symm)
  · apply φ.symm.injective
    rw [← DoubleCoset.out_eq' _ _ (φ.symm i), ← DoubleCoset.out_eq' _ _ (φ.symm j)]
    refine (DoubleCoset.eq _ _ _ _).2 ⟨(γ'⁻¹ * γ : Γ), (γ'⁻¹ * γ).2, (k * k'⁻¹ : K), (k * k'⁻¹).2, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_assoc, mul_assoc, ← mul_assoc (γ : G), ← mul_assoc, ← mul_assoc,
      mul_assoc _ _ (k : G), e]
    simp [mul_assoc]
  · rw [e]
    exact h.2 _
  · rw [classMass_eq_sum_of_bijective (fun i => (φ.symm i).out)]
    · simp only [e]
    · simp only [DoubleCoset.out_eq']
      exact φ.symm.bijective

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem levelK_eq {π : HA (AF F) σ J →* HA (Af F) σ J} (hπ : IsFinProj σ J π)
    (Λ : Submodule (𝓞 E) (Fin M → E)) :
    levelK σ J (Λ : Set (Fin M → E)) =
      ((((Formalism.UG.levelAfL σ J Λ).subgroupOf (Formalism.UG.UPts σ J (Af F))).comap
        (swapPts (Af F) σ J : HA (Af F) σ J →* Formalism.UG.UPts σ J (Af F))).comap π) := by
  ext g
  have h1 : g ∈ ((((Formalism.UG.levelAfL σ J Λ).subgroupOf (Formalism.UG.UPts σ J (Af F))).comap
        (swapPts (Af F) σ J : HA (Af F) σ J →* Formalism.UG.UPts σ J (Af F))).comap π) ↔
      (swapPts (Af F) σ J (π g) : GL (Fin M) (E ⊗[F] Af F)) ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := F) Λ) :=
    ⟨fun h => h.2, fun h => ⟨(swapPts (Af F) σ J (π g)).2, h⟩⟩
  rw [h1, coe_swapPts, hπ g]
  have h2 : ∀ y : Fin M → Af F ⊗[F] E, (fun i => GlobalTheory.LevSplit.swp F E ((finMat σ J g *ᵥ y) i)) =
      (finMat σ J g).map (GlobalTheory.LevSplit.swp F E) *ᵥ fun i => GlobalTheory.LevSplit.swp F E (y i) :=
    fun y => funext fun i => RingHom.map_mulVec _ _ _ i
  change (∀ y, y ∈ latHat F E (Λ : Set (Fin M → E)) ↔ finMat σ J g *ᵥ y ∈ latHat F E (Λ : Set (Fin M → E))) ↔
    ∀ x, x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔
      (finMat σ J g).map (GlobalTheory.LevSplit.swp F E) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ
  simp only [GlobalTheory.LevSplit.latHat_iff, h2]
  refine ⟨fun h x => ?_, fun h y => h _⟩
  choose y hy using fun i => (GlobalTheory.LevSplit.swp_bij (F := F) (E := E)).2 (x i)
  have := h y
  simpa only [hy] using this

end Level

section Space

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [inst : StarRing E] [Algebra F E]

theorem mass_coord (hc : CMData F E) (W : HSpace E) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (W.rank, 0))
    (hσ : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e) :
    (letI := Formalism.UG.CS.starOfInv (hc.sig : E →+* E) hσ
    Formalism.HermitianLatticesTheory.mass (Formalism.UG.CS.formJ (hc.sig : E →+* E) hσ W.gram 1) (tMap (Formalism.L2.Herm.crd W) W.L0)) =
      Formalism.HermitianLatticesTheory.mass W.hT W.L0 := by
  let h' : (Fin W.rank → E) →ₗ⋆[E] (Fin W.rank → E) →ₗ[E] E :=
    Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) ((1 : E) • W.gram)
  change Formalism.HermitianLatticesTheory.mass h' (tMap (Formalism.L2.Herm.crd W) W.L0) = _
  have he : ∀ x y, h' (Formalism.L2.Herm.crd W x) (Formalism.L2.Herm.crd W y) = W.hT x y := fun x y => by
    rw [Formalism.L2.Herm.hT_crd hc]
    simp only [h', one_smul, Matrix.toLinearMapₛₗ₂'_apply, Formalism.UG.hform, RingHom.id_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change star _ * _ = star _ * _ * _
    ring
  obtain ⟨h1, h2, -⟩ := Formalism.HermitianLatticesTheory.massBasic _ _ W.hT W.herm
    (GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.trace_pos hc.cmUnram.2.1 W hW hs) W.L0 W.standardTuple_isLattice
  have h3 := mass_transport (Formalism.L2.Herm.crd W).symm (isoSymm _ he) (tMap (Formalism.L2.Herm.crd W) W.L0)
    (by rwa [tMap_symm]) (by rwa [tMap_symm])
  rwa [tMap_symm] at h3

theorem coe_tMap (W : HSpace E) : (tMap (Formalism.L2.Herm.crd W) W.L0 : Set (Fin W.rank → E)) = latCoord W := by
  ext x
  rw [SetLike.mem_coe, mem_tMap]
  change W.frame.equivFun.symm x ∈ W.L0 ↔ _
  rw [Module.Basis.equivFun_symm_apply]
  rfl

theorem finite_and_mass (hc : CMData F E) (W : HSpace E) (hW : W.SigOK) (hs : ∀ τ, W.sig τ = (W.rank, 0))
    (hJ : IsHermND hc.sig W.gram) (hd : Formalism.UG.IsTotDef hc.sig W.gram) :
    FiniteClasses (ratIn (AF F) hc.sig W.gram) (levelW hc W) ∧
      classMass (ratIn (AF F) hc.sig W.gram) (levelW hc W) = Formalism.HermitianLatticesTheory.mass W.hT W.L0 := by
  have hσ : IsCMExt F E hc.sig := ⟨hc.totReal, hc.cmUnram.1, hc.deg2, hc.cmUnram.2.1⟩
  have hL := tMap_lattice (Formalism.L2.Herm.crd W) W.L0 W.standardTuple_isLattice
  have hf : Module.Finite (𝓞 E) (tMap (Formalism.L2.Herm.crd W) W.L0) := Module.Finite.iff_fg.2 hL.fg
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj hc.sig W.gram
  rw [levelW, ← coe_tMap, levelK_eq hπ]
  constructor
  · rw [finiteClasses_comap π _ _ hπ.surjective hπ.injOn, hπ.map_ratIn]
    exact finiteClasses_lattice hσ hJ hd _ hf hL.span_eq_top
  · have hi : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e := fun e => star_star e
    rw [← hπ.unitaryMass_eq, unitaryMass_lattice_eq_genus_mass hσ hJ hd hi _ hf hL.span_eq_top]
    exact mass_coord hc W hW hs hi

end Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem defClassDecomp : ∀ D : D7, DefClassDecomp D := by
  intro D W hW hs θ hθ A hA
  rw [GlobalTheory.DecompCompare.KSub_eq D W hW hs θ hθ A hA]
  have hd : Formalism.UG.IsTotDef D.sp.cm.sig W.gram := GlobalTheory.DefiniteQuotient.isTotDef_of_posDef W fun τ => by
    have := hW (Formalism.BasicNotions.TH.tauE D τ)
    rw [hs] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨h1, h2⟩ := finite_and_mass D.sp.cm W hW hs (GlobalTheory.DefiniteQuotient.gram_hermND W) hd
  haveI := Unfold.borelHA D.sp.cm.sig W.gram
  refine ⟨(GlobalTheory.DecompCompare.isOpen_levelW D W).measurableSet, ?_⟩
  rw [← h2]
  exact exists_reps h1

end GlobalTheory.DefiniteDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusStickelbergerPadicDeterminantFormulaStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pAdicFrobeniusStickelberger_of_d7_datum : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicFrobeniusStickelberger D := by
  first | exact @GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | exact GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula | (intros; apply GlobalTheory.FrobStick.frobenius_stickelberger_padic_determinant_formula <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceIncl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev Ser : Type := (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) → GA D (Wc D i) → ℂ

def kernA (t : T0) (h : GA D (Vc D i)) : (R.cV i).W →ₗ[ℂ] Ser R i where
  toFun w v := singleSeries R i (R.ωP i t) (R.vP i t) h ((R.cV i).ρ h⁻¹ w) v
  map_add' w w' := by
    funext v g
    simp [singleSeries, Datum.thetaKO]
  map_smul' c w := by
    funext v g
    simp [singleSeries, Datum.thetaKO]

def kern (t : T0) (h : Bridge.Gf (Vc D i)) : (R.cV i).W →ₗ[ℂ] Ser R i :=
  kernA R i t (MonoidHom.mem_range.1 h.2).choose

def DatumType (t : T0) : Prop :=
  ∀ (g0 : G0 R.Pg D.R.r) κ κ', IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ →
    IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ' →
    R.ωP i t (κ, κ') (R.vP i t) = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.vP i t

def GoodLiftOnto (t : T0) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) : Prop :=
  ∀ θ, OnTies.IsClassSum R i t U ψ ph θ →
    (R.FW i).Wgood U ψ (fun g => (idemOf A.X).coeff g) ≤
      LinearMap.range ((R.FW i).eOp (fun g => (idemOf A.X).coeff g) ∘ₗ θ)

end GlobalTheory.TraceIncl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompactStatement
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memLp_lift_L2DiscreteQuotient_on_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ (F : L2 Γ μ) (C : Set G), IsCompact C → MemLp (lift Γ F) 2 (μ.restrict C) ∧ IntegrableOn (lift Γ F) C μ := by
  first | exact @GlobalTheory.AutomorphicL2Local.memLp_restrict_compact | exact GlobalTheory.AutomorphicL2Local.memLp_restrict_compact | (intros; apply GlobalTheory.AutomorphicL2Local.memLp_restrict_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthGoodSubProj
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCoord

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Cx
open GlobalTheory.FormTies GlobalTheory.OnTies
open GlobalTheory.OntoChain (coordMap thetaMat thetaOp liftLvl liftSub supLat Mir mirIncl uni mirToGL)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Block

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {Z : Submodule K B.S.Forms} {v0 : InfinitePlace K} {s : ℕ}

theorem gaMat_mem_coord (hZ : ∀ g, Z.map (B.r g) ≤ Z) (a : MonoidAlgebra K G) {z : Fin B.S.dim → K} (hz : z ∈ B.coord Z) :
    (B.S.gaMat B.r a).mulVec z ∈ B.coord Z := by
  obtain ⟨f, hf, rfl⟩ := hz
  unfold CSD.gaMat
  rw [Matrix.sum_mulVec]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ ⟨B.r t f, hZ t ⟨f, hf, rfl⟩, CyclotomicLifting.equivFun_end (B := B) (B.r t) f⟩

theorem orth_good_sub_proj (h : BlockHyp B ℓ v0 s) (hZ : ∀ g, Z.map (B.r g) ≤ Z)
    (x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) {z : Fin B.S.dim → K} (hz : z ∈ B.coord Z) :
    hform B.S.H z ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec ((B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X)).mulVec x) -
      (B.fE ℓ Z).mulVec ((B.lPr ℓ Z).mulVec x)) = 0 := by
  have hc := idempotent_central K G ℓ.X h.irr
  have h1 := (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ (idemOf ℓ.X) (hc.2 _).symm).1
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := BlockDat.lf_v_proj h
  obtain ⟨⟨hl1, -⟩, hl3⟩ := BlockDat.lf_lvl_proj h
  have hz2 := (BlockDat.lf_z_proj (Z := Z) h).2
  have hO := orthogonal_tower_projection B.S.H (B.vE ℓ) (B.vPr ℓ) (B.zE ℓ Z) (B.Pq ℓ Z) _ (BlockDat.lf_card_inv_ne (ℓ := ℓ)) hv2 hz2
  have hg := good_at_spec K v0 h.conj G ℓ.X h.irr ℓ.P ℓ.ψ
  have hadj : (B.vE ℓ * B.vPr ℓ)ᴴ * B.S.H = B.S.H * (B.vE ℓ * B.vPr ℓ) := by
    have := group_action_matrix_adjoint K B.S G B.r h.ok.act (goodAt ℓ.X ℓ.P ℓ.ψ)
    rwa [hg.selfAdj, ← hv3] at this
  have h2 : B.S.lvlE B.r ℓ.P ℓ.ψ * B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) = B.vE ℓ * B.vPr ℓ * B.S.lvlE B.r ℓ.P ℓ.ψ := by
    rw [h1, hv3, goodAt, (group_action_matrix_hom K B.S G B.r).2, ← hl3, Matrix.mul_assoc, Matrix.mul_assoc, hl1, Matrix.mul_one]
  have h3 : (B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec ((B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X)).mulVec x) -
      (B.fE ℓ Z).mulVec ((B.lPr ℓ Z).mulVec x) =
      (B.vE ℓ * B.vPr ℓ).mulVec ((1 - B.vE ℓ * B.zE ℓ Z * B.Pq ℓ Z * B.vPr ℓ).mulVec ((B.S.lvlE B.r ℓ.P ℓ.ψ).mulVec x)) := by
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.sub_mulVec, h2]
    congr 1
    unfold BlockDat.fE BlockDat.lPr
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (B.vPr ℓ) (B.vE ℓ), hv1, Matrix.one_mul]
  have h4 : (B.vPr ℓ).mulVec z ∈ B.Z0 ℓ Z := by
    show (B.vE ℓ).mulVec ((B.vPr ℓ).mulVec z) ∈ B.coord Z
    rw [Matrix.mulVec_mulVec, hv3]
    exact gaMat_mem_coord hZ _ hz
  obtain ⟨u, hu⟩ := (subspace_image_spec K _ (B.Z0 ℓ Z)).2.ge h4
  have hu' : (B.vE ℓ * B.vPr ℓ).mulVec z = (B.vE ℓ * B.zE ℓ Z).mulVec u := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu]; rfl
  rw [h3, ← CyclotomicLifting.hform_adj hadj, hu', RationalHermitianForm.hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hO, Matrix.zero_mulVec, dotProduct_zero]

end Block

end GlobalTheory.OnCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupMulClosed
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_mul_int_left (χ : kˣ →* ℂˣ) {x y : k} (hx : valuation k x ≤ 1) (hy : Triv χ y) :
    Triv χ (x * y) :=
  triv_mono χ y (x * y) (by rw [map_mul]; exact mul_le_of_le_one_left' hx) hy

theorem triv_mul_int_right (χ : kˣ →* ℂˣ) {x y : k} (hy : valuation k y ≤ 1) (hx : Triv χ x) :
    Triv χ (x * y) := by
  rw [mul_comm]; exact triv_mul_int_left χ hy hx

theorem grp_mul {n : ℕ} (ψ : Fin n → kˣ →* ℂˣ) (hψ : Ordered ψ) {a b : GL (Fin n) k}
    (ha : a ∈ grp ψ) (hb : b ∈ grp ψ) : a * b ∈ grp ψ := by
  refine ⟨(KO k (Fin n)).mul_mem ha.1 hb.1, fun i j hij => ?_⟩
  rw [Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_induction _ (fun x => Triv (ψ i / ψ j) x) (fun x y hx hy => triv_add _ x y hx hy)
    (triv_zero _) (fun l _ => ?_)
  rcases le_or_gt l i with hli | hil
  ·
    have h1 : Triv (ψ l / ψ j) (b.val l j) := hb.2 l j (lt_of_le_of_lt hli hij)
    have h2 : Triv (ψ i / ψ j) (b.val l j) := hψ l i j j hli hij.le le_rfl _ h1
    exact triv_mul_int_left _ (GlobalTheory.BlockType.val_le_one_of_mem_KO ha.1 i l) h2
  · rcases lt_or_ge l j with hlj | hjl
    · have h1 : Triv (ψ i / ψ l) (a.val i l * b.val l j) :=
        triv_mul_int_right _ (GlobalTheory.BlockType.val_le_one_of_mem_KO hb.1 l j) (ha.2 i l hil)
      have h2 : Triv (ψ l / ψ j) (a.val i l * b.val l j) :=
        triv_mul_int_left _ (GlobalTheory.BlockType.val_le_one_of_mem_KO ha.1 i l) (hb.2 l j hlj)
      have h3 := triv_mul _ _ _ h1 h2
      rwa [div_mul_div_cancel] at h3
    · have h1 : Triv (ψ i / ψ l) (a.val i l) := ha.2 i l hil
      have h2 : Triv (ψ i / ψ j) (a.val i l) := hψ i i j l le_rfl hij.le hjl _ h1
      exact triv_mul_int_right _ (GlobalTheory.BlockType.val_le_one_of_mem_KO hb.1 l j) h2

theorem grp_mul_closed : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), Ordered ψ → ∀ a ∈ grp ψ, ∀ b ∈ grp ψ, a * b ∈ grp ψ :=
  fun _ _ _ _ _ _ ψ hψ _ ha _ hb => grp_mul ψ hψ ha hb

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankOneBaseWeightEqCmTheta
section
noncomputable section

namespace GlobalTheory.HalfOnRecord

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Pj.LPb Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign GlobalTheory.HalfCompare GlobalTheory.CoverHalf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)
open Formalism.L2.Host (PiBar)

variable {D : D7}

def designLevel (P : PiBar D.host) : Level (hostOfRecord D) :=
  IndefiniteRowSideFullHecke.HalfLevelCoefficients.levelAt D (IndefiniteRowSideFullHecke.HalfLevelCoefficients.halfOf D P.pb) ((ParAtCompare.levelPb_iff D P.pb).1 (levelPb_exists D P.pb P.pb_over))

theorem designLevel_spec (P : PiBar D.host) :
    (designLevel P).M = D.host.g 0 * D.host.g 1 ∧ (designLevel P).A = 1 := ⟨rfl, rfl⟩

theorem designLevel_Mb (P : PiBar D.host) :
    (designLevel P).Mb = ∏ k, (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := rfl

theorem bar_eq (H : ModHost D) : (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D :=
  RingHom.ext fun a => RingOfIntegers.ext (H.bar_eq a)

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def RowAt (R : RealDat D A Ks) (t : T0) {H : ModHost D} (l : Level H) : Prop :=
  ∃ (n : ℕ) (l₂ : Level H), IsCoverHalf l (R.Q t) n (coverHalf D (R.Q t)) l₂ ∧
    HalfIs R t l.Mb (coverHalf D (R.Q t)) ∧ AAPrimeToLevel l₂

end Rec

end GlobalTheory.HalfOnRecord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateSeriesEqConstMulIntegralOneSeriesStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslateSeries_eq_const_mul_integral_one_series : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → (∀ s : ℂ, GL3Theta.Tors1 p g.abelian₂ s → ‖GlobalTheory.EvenTheta.xAt g s‖ ≤ 1) →
    ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∃ w : PowerSeries ℂ_[p], GlobalTheory.EvenTheta.IntSer w ∧
      PowerSeries.constantCoeff w = 1 ∧ GlobalTheory.ThetaTransl.tau g t = PowerSeries.C (GlobalTheory.ThetaTransl.cval g t) * w := by
  first | exact @GlobalTheory.ThetaUnit.tau_eq_C_mul | exact GlobalTheory.ThetaUnit.tau_eq_C_mul | (intros; apply GlobalTheory.ThetaUnit.tau_eq_C_mul <;> assumption)
end

