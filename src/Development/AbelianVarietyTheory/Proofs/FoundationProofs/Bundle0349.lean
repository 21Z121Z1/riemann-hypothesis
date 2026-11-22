import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0006
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0328
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormPrime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0318
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0159
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0219
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0069
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLaws
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.CMEndo

section Series
open Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ : Type*}

theorem const_l : PowerSeries.constantCoeff g.l = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem ex_l (h : g.Ok) : PowerSeries.subst g.l g.ex = PowerSeries.X := by
  obtain ⟨-, -, h0, h1⟩ := h
  have hl : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.l : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => const_l g
  have he : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.ex : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => h0
  have h2 : ∀ i : Unit, MvPowerSeries.subst (fun _ : Unit => (g.ex : MvPowerSeries Unit ℂ_[p]))
      (g.l : MvPowerSeries Unit ℂ_[p]) = MvPowerSeries.X i := fun _ => h1
  have h3 := GlobalTheory.FormalInv.eq_substInv_of_right hl he h2
  have h4 := GlobalTheory.FormalInv.subst_substInv_left hl
    (IsUnit.of_mul_eq_one _ (GlobalTheory.FormalInv.linearPart_mul_eq_one hl he h2)) ()
  rw [← h3] at h4
  exact h4

theorem pt_lg (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.pt (g.lg a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [GL3Theta.G1.pt, GL3Theta.G1.lg, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (const_l g)) ha', ex_l g h, PowerSeries.subst_X ha']

theorem subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries σ ℂ_[p]) f = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries σ ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, zero_mul]

theorem mulBy_one (h : g.Ok) (i : σ) : g.mulBy 1 (GL3Theta.Xv i) = GL3Theta.Xv i := by
  rw [GL3Theta.G1.mulBy, map_one, one_mul, pt_lg g h (MvPowerSeries.constantCoeff_X i)]

theorem mulBy_zero (h : g.Ok) (a : MvPowerSeries σ ℂ_[p]) : g.mulBy 0 a = 0 := by
  rw [GL3Theta.G1.mulBy, map_zero, zero_mul, GL3Theta.G1.pt, subst_zero h.2.2.1]

theorem constantCoeff_subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0)
    {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, map_mul, ha, zero_mul]

theorem constantCoeff_lg {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.lg a) = 0 :=
  constantCoeff_subst_zero (const_l g) ha

theorem constantCoeff_pt (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.pt a) = 0 :=
  constantCoeff_subst_zero h.2.2.1 ha

theorem lg_pt (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.lg (g.pt a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [G1.lg, G1.pt, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' h.2.2.1) ha', h.2.2.2, PowerSeries.subst_X ha']

theorem lg_mulBy (h : g.Ok) (c : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.lg (g.mulBy c a) = MvPowerSeries.C c * g.lg a := by
  rw [G1.mulBy, lg_pt g h]
  rw [map_mul, constantCoeff_lg g ha, mul_zero]

theorem mulBy_add (h : g.Ok) (c c' : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.mulBy (c + c') a = g.add (g.mulBy c a) (g.mulBy c' a) := by
  rw [G1.add, lg_mulBy g h c ha, lg_mulBy g h c' ha, G1.mulBy, map_add, add_mul]

theorem add_eq_subst (h : g.Ok) (A B : MvPowerSeries σ ℂ_[p]) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    g.add A B = MvPowerSeries.subst ![A, B] (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
  have hab : MvPowerSeries.HasSubst ![A, B] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hA, hB])
  have hs : MvPowerSeries.constantCoeff (g.lg (Xv 0) + g.lg (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add, constantCoeff_lg g (MvPowerSeries.constantCoeff_X _),
      constantCoeff_lg g (MvPowerSeries.constantCoeff_X _), add_zero]
  have hsl : ∀ i : Fin 2, MvPowerSeries.subst ![A, B] (g.lg (Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) =
      g.lg (![A, B] i) := by
    intro i
    have hX : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)
    rw [G1.lg, G1.lg, PowerSeries.subst, PowerSeries.subst,
      MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X i)) hab]
    congr 1
    funext _
    exact MvPowerSeries.subst_X hab i
  rw [G1.add, G1.add, G1.pt, G1.pt, PowerSeries.subst, PowerSeries.subst,
    MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hs)) hab]
  congr 1
  funext _
  rw [MvPowerSeries.subst_add hab, hsl 0, hsl 1]
  rfl

theorem integralMv_zero : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := fun n => by
  simp [IsIntP]

theorem integralMv_X (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := fun n => by
  unfold IsIntP
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem integral_mulBy_semiring : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok →
    IntegralMv (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    IntegralMv (g.mulBy 0 (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
    IntegralMv (g.mulBy 1 (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
    ∀ c c' : ℂ_[p], IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (g.mulBy c' (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (g.mulBy (c + c') (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  intro p _ g h hadd
  have hX : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := MvPowerSeries.constantCoeff_X _
  refine ⟨?_, ?_, ?_⟩
  · rw [mulBy_zero g h]; exact integralMv_zero
  · rw [mulBy_one g h]; exact integralMv_X ()
  · intro c c' hc hc'
    have h0 : ∀ d : ℂ_[p], MvPowerSeries.constantCoeff (g.mulBy d (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
      fun d => constantCoeff_pt g h (by rw [map_mul, constantCoeff_lg g hX, mul_zero])
    rw [mulBy_add g h c c' hX, add_eq_subst g h _ _ (h0 c) (h0 c')]
    exact ReciprocityTheory.ChartRestriction.L1.integralMv_subst2 (fun d => hadd d)
      (fun i => by fin_cases i <;> simp [h0]) (fun i => by
        fin_cases i
        · exact fun d => hc d
        · exact fun d => hc' d)

end Series

theorem endInt_all (D : D7) : GL3Theta.endInt D := by
  intro p _ cc δ g hA α hα
  have hok : g.Ok := hA.2.2.2.2
  have hadd := ((GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.1 p cc δ g hA).1
  obtain ⟨h0, h1, hplus⟩ := integral_mulBy_semiring p g hok hadd
  set S : Set ℂ_[p] := {c | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} with hS
  have hcl : IsClosed S := GlobalTheory.mulBy_integral_isClosed p g
  have hnat : ∀ n : ℕ, (n : ℂ_[p]) ∈ S := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero]; exact h0
    | succ n ih =>
      rw [Nat.cast_succ]; exact hplus _ _ ih h1
  by_cases hp : p = 2
  · subst hp
    have h2 := GlobalTheory.TwoAdicFirst.fst_mem_closure_natCast D g.lam α hα
    have hsub : closure (Set.range (Nat.cast : ℕ → ℂ_[2])) ⊆ S :=
      closure_minimal (by rintro _ ⟨n, rfl⟩; exact hnat n) hcl
    exact hsub h2
  · obtain ⟨β, hβ, γ, hγ, hb1, hb2, hc1, hc2, rfl⟩ := Formalism.MainNotions.Ext.CutA.okpTwoUnits2_holds D p g.lam hp α hα
    have hunit : ∀ β ∈ GL3Theta.OKp D g.lam, ‖β.1‖ = 1 → ‖β.2‖ = 1 → β.1 ∈ S := by
      intro β hβ h1 h2
      have hc := Formalism.MainNotions.Ext.CutA.okpUnitsDense_holds D p g.lam hp β hβ h1 h2
      have hm := map_mem_closure continuous_fst hc (t := S) (by
        rintro _ ⟨a, ha, rfl⟩
        exact GlobalTheory.CMUnit.unit_endo D p cc δ g hA hp a ha)
      rwa [hcl.closure_eq] at hm
    exact hplus _ _ (hunit β hβ hb1 hb2) (hunit γ hγ hc1 hc2)

theorem endo_all : ∀ D : D7, GL3Theta.endInt D ∧ GL3Theta.phNorm D ∧ GL3Theta.beConj D := by
  intro D
  have he := endInt_all D
  have ha := (GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.1
  have hB := (GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.2
  have hok : Formalism.MainNotions.Ext.CutA.PhNormOK D := GlobalTheory.CMNormPhi.phAt_mulBy_norm D he ha
  have hn := Formalism.MainNotions.Ext.CutA.phNorm_of' Formalism.MainNotions.Ext.CutA.phNormOfUnits_holds Formalism.MainNotions.Ext.CutA.phNormClosed_holds D hok he ha hB
  exact ⟨he, hn, Formalism.MainNotions.Ext.CutA.beConj_of' Formalism.MainNotions.Ext.CutA.beConjOfNorm_holds D he ha hn hB⟩

end GlobalTheory.CMEndo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdOfLandherrHasse
section
open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem genusMassStd (D : D7) : GenusMassStd D :=
  GlobalTheory.DefiniteMass.mass_eq_massI D

theorem genusMassStd_of_landherrHasse :
    (∀ D : D7, LandherrHasse D) → ∀ D : D7, GenusMassStd D :=
  fun _ D => genusMassStd D

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.DefiniteOrthonormal

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_orthonormal (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) (hs : W.SigOK)
    (hp : ∀ τ : E →+* ℂ, W.sig τ = (W.rank, 0)) :
    ∃ b : Fin W.rank → W.V, LinearIndependent E b ∧
      ∀ a c, W.hT (b a) (b c) = if a = c then 1 else 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.DefiniteMass.exists_isometry hc W hs hp
  refine ⟨(Pi.basisFun E (Fin W.rank)).map e.symm, Module.Basis.linearIndependent _, fun a c => ?_⟩
  rw [← he]
  simp only [Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  change ∑ i, star ((Pi.single a (1 : E) : Fin W.rank → E) i) * (Pi.single c (1 : E) : Fin W.rank → E) i = _
  rw [Finset.sum_eq_single a]
  · simp [Pi.single_apply]
  · intro i _ hi
    simp [Pi.single_apply, hi]
  · simp

end

theorem landherrHasse : ∀ D : D7, LandherrHasse D := fun D =>
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W hs hp => exists_orthonormal (E := D.host.E) D.sp.cm.cmUnram W hs hp

end GlobalTheory.DefiniteOrthonormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RightInvariantOfFiniteCovolume
section
noncomputable section

namespace GlobalTheory.VolumeRatioTypings

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular
open GlobalTheory.VolRatioCompare (reLat)
open scoped TensorProduct Matrix ENNReal

theorem rightInvariant_of_finite_covolume {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G)
    [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) : μ.IsMulRightInvariant := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup Γ
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup Γ μ
  refine ⟨fun g => ?_⟩
  have e : μ.map (· * g) = ((μ.map (· * g)).haarScalarFactor μ : ℝ≥0∞) • μ :=
    Measure.isMulLeftInvariant_eq_smul _ μ
  have h' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv (f := (· * g)) ⟨measurable_mul_const g, by rw [e]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id fun γ x => mul_assoc _ _ _
  have h1 : μ.map (· * g) 𝓕 = μ 𝓕 :=
    ((MeasurableEquiv.mulRight g).map_apply 𝓕).trans (h'.measure_eq h)
  rw [e, Measure.smul_apply, smul_eq_mul] at h1
  have h2 := (ENNReal.mul_left_inj (h.measure_ne_zero (NeZero.ne μ)) hfin).1 (h1.trans (one_mul _).symm)
  rw [e, h2, one_smul]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem volMeas_unique (V : HSp D) {P Q : ℕ} {μ μ' : Measure (GA D V)} (h : IsVolMeas D V P Q μ)
    (h' : IsVolMeas D V P Q μ') : μ' = μ := by
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : BorelSpace (UpqT P Q) := ⟨rfl⟩
  have : LocallyCompactSpace (UpqT P Q) :=
    (UpqUnimodular.modelEquiv P Q).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have := D.cd.haar P Q
  have := h.1
  have := h'.1
  have e : μ' = (μ'.haarScalarFactor μ : ℝ≥0∞) • μ := Measure.isMulLeftInvariant_eq_smul μ' μ
  obtain ⟨U, hU1, hU, hfin⟩ := (D.cd.cd P Q).exists_isOpen_measure_lt_top 1
  obtain ⟨θ, hθ⟩ := h.2.1
  obtain ⟨A, hA⟩ := (h.2.2 θ hθ).1
  have h1 := (h.2.2 θ hθ).2 A hA (fun _ => U) fun _ => hU.measurableSet
  have h2 := (h'.2.2 θ hθ).2 A hA (fun _ => U) fun _ => hU.measurableSet
  rw [e, Measure.smul_apply, smul_eq_mul, h1] at h2
  have h3 := (ENNReal.mul_left_inj (Finset.prod_ne_zero_iff.2 fun _ _ => hU.measure_ne_zero _ ⟨1, hU1⟩)
    (ENNReal.prod_ne_top fun _ _ => hfin.ne)).1 (h2.trans (one_mul _).symm)
  rw [e, h3, one_smul]

theorem isVol_of_pair (V : HSp D) {P Q : ℕ} {μ : Measure (GA D V)} (h : IsVolMeas D V P Q μ) {𝓕 : Set (GA D V)}
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {x : ℝ} (hx : 0 < x) (e : μ 𝓕 = ENNReal.ofReal x) : IsVol D V P Q x := by
  refine ⟨hx, ⟨μ, h⟩, fun μ' h' => ?_⟩
  obtain rfl := volMeas_unique V h h'
  refine ⟨⟨𝓕, h𝓕⟩, fun 𝓖 h𝓖 => ?_⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := h.1
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) μ'
  have h𝓖' : IsFundamentalDomain (GQ V) 𝓖 μ' := h𝓖
  exact (h𝓖'.measure_eq h𝓕).trans e

theorem exists_pair (V : HSp D) (hs : V.SigOK) {P Q : ℕ} (hPQ : ∀ τ, V.sig τ = (P, Q)) :
    ∃ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsVolMeas D V P Q μ ∧ IsFundamentalDomain (GQ V) 𝓕 μ := by
  obtain ⟨p, h1, h2⟩ := GlobalTheory.VolPairExists.exists_volPair V hs
  simp only [hPQ] at h1
  exact ⟨p.1, p.2, h1, h2⟩

theorem exists_conj (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) : ∃ k ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      (finMat D.sp.cm.sig V.gram k).mulVec y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2)) := by
  obtain ⟨γ, hfin, hγ⟩ := GlobalTheory.T.exists_local_conjugation_selfDual_lattices_host D V L h1 h2
  obtain ⟨k, hk, hkv⟩ := GlobalTheory.T.exists_adelicUnitary_of_localFamily_almostAll_trivial D V γ hfin
  refine ⟨k, hk, fun y => ?_⟩
  refine (GlobalTheory.LatticeLocalGlobal.mem_latHat_iff D.host.F D.host.E V y).trans (Iff.trans ?_
    (GlobalTheory.LatticeLocalGlobal.mem_latHat_iff D.host.F D.host.E (reLat V L h1 h2) _).symm)
  refine forall_congr' fun v => (hγ v _).trans (iff_of_eq ?_)
  congr 1
  rw [← hkv v]
  funext i
  exact (RingHom.map_mulVec (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v)
    (AlgHom.id D.host.F D.host.E)).toRingHom _ y i).symm

theorem isVolMeas_reLat (V : HSp D) (L : Submodule (𝓞 D.host.E) V.V) (h1 : Submodule.IsLattice D.host.E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) {P Q : ℕ} {μ : Measure (GA D V)} (h : IsVolMeas D V P Q μ)
    (hr : μ.IsMulRightInvariant) : IsVolMeas D (reLat V L h1 h2) P Q μ := by
  obtain ⟨k, hk, hkL⟩ := exists_conj V L h1 h2
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := h.1
  refine ⟨h.1, h.2.1, fun θ hθ => ⟨(h.2.2 θ hθ).1, fun A hA B hB => ?_⟩⟩
  rw [← (h.2.2 θ hθ).2 A hA B hB, ← measure_preimage_mul μ k⁻¹, ← measure_preimage_mul_right μ k]
  refine congrArg μ (Set.ext fun (g : GA D V) => and_congr ?_ ?_)
  · show (∀ y : Fin V.rank → _, y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2)) ↔
        (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L0c D (reLat V L h1 h2))) ↔
      ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
        (finMat D.sp.cm.sig V.gram (k⁻¹ * (g * k))).mulVec y ∈ latHat D.host.F D.host.E (L0c D V)
    have hm : ∀ (a b : GA D V) y, (finMat D.sp.cm.sig V.gram (a * b)).mulVec y =
        (finMat D.sp.cm.sig V.gram a).mulVec ((finMat D.sp.cm.sig V.gram b).mulVec y) := fun a b y => by
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, Matrix.mulVec_mulVec]
    have ho : ∀ y, (finMat D.sp.cm.sig V.gram k).mulVec ((finMat D.sp.cm.sig V.gram k⁻¹).mulVec y) = y := fun y => by
      rw [← hm, mul_inv_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one, Matrix.one_mulVec]
    constructor
    · intro hg y
      refine (hkL y).trans (Iff.trans (hg _) (Iff.trans (iff_of_eq ?_) (hkL _).symm))
      rw [hm, ho, hm]
    · intro hg y
      have := hg ((finMat D.sp.cm.sig V.gram k⁻¹).mulVec y)
      have := (hkL _).symm.trans (this.trans (hkL _))
      rw [hm, hm, ho, ho] at this
      exact this
  · have hk1 : ∀ a ∈ GfC V, ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) a = 1 := fun a ha ρ => by
      have ha' : infHom V a = 1 := ha
      rw [GlobalTheory.SmoothForms.RealPts.infMat_eq V, ha', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    refine forall_congr' fun ρ => ?_
    have e : infMat D.sp.cm.sig V.gram (θ ρ) (k⁻¹ * (g * k)) = infMat D.sp.cm.sig V.gram (θ ρ) g := by
      rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul, hk1 k hk, hk1 _ (inv_mem hk), one_mul, mul_one]
    exact iff_of_eq (congrArg (fun m : Matrix (Fin (reLat V L h1 h2).rank) (Fin (reLat V L h1 h2).rank) ℂ =>
      ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * m) e.symm)

theorem tMap_unimod (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V) (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y) :
    Formalism.HermitianLatticesTheory.IsUnimodular V'.hT (tMap e V.L0) := by
  have h : ∀ x, (∀ y ∈ V.L0, V.hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) ↔ x ∈ V.L0 := fun x => by
    conv_rhs => rw [← V.baseLattice_isUnimodular]
    simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual]
  ext x
  rw [mem_tMap, ← h]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply,
    mem_tMap]
  refine ⟨fun H y hy => ?_, fun H y hy => ?_⟩
  · have := H (e y) (by simpa using hy)
    rwa [← e.apply_symm_apply x, he] at this
  · rw [← isoSymm e he]
    exact H _ hy

theorem isVol_of_isometry (V V' : HSp D) (e : V.V ≃ₗ[D.host.E] V'.V) (he : ∀ x y, V'.hT (e x) (e y) = V.hT x y)
    {P Q : ℕ} {x : ℝ} (h : IsVol D V P Q x) : IsVol D V' P Q x := by
  obtain ⟨hx, ⟨μ, hμ⟩, hall⟩ := h
  obtain ⟨⟨𝓕, h𝓕⟩, hv⟩ := hall μ hμ
  let V₁ := reLat V' (tMap e V.L0) (tMap_lattice e _ V.standardTuple_isLattice) (tMap_unimod V V' e he)
  obtain ⟨φ, hc, hc', hQ, hφ⟩ := GlobalTheory.T.exists_volume_transport_of_lattice_isometry D V V₁ e he fun x => by
    show _ ↔ e x ∈ tMap e V.L0
    rw [mem_tMap, e.symm_apply_apply]
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary D.host.F D.host.E D.sp.cm.sig V₁.rank V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V₁.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : Countable (GQ V₁) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  let ψ : GA D V ≃ᵐ GA D V₁ := ⟨φ.toEquiv, hc.measurable, hc'.measurable⟩
  have hν := hφ P Q μ hμ
  have := hν.1
  have h𝓕' : IsFundamentalDomain (GQ V) 𝓕 μ := h𝓕
  have h𝓖 : IsFundamentalDomain (GQ V₁) (φ.symm ⁻¹' 𝓕) (μ.map φ) :=
    h𝓕'.preimage_of_equiv (f := φ.symm)
      (MeasurePreserving.symm ψ ⟨ψ.measurable, rfl⟩).quasiMeasurePreserving
      (e := fun γ => ⟨φ γ, (hQ γ).1 γ.2⟩)
      ⟨fun a b hab => Subtype.ext (φ.injective (congrArg Subtype.val hab)),
        fun b => ⟨⟨φ.symm b, (hQ _).2 (by simp)⟩, Subtype.ext (by simp)⟩⟩
      fun γ y => by
        show φ.symm (φ γ * y) = γ * φ.symm y
        rw [map_mul, φ.symm_apply_apply]
  have hvol : μ.map φ (φ.symm ⁻¹' 𝓕) = ENNReal.ofReal x := by
    rw [← hv 𝓕 h𝓕]
    refine (ψ.map_apply _).trans (congrArg μ ?_)
    ext g
    exact iff_of_eq (congrArg (· ∈ 𝓕) (φ.symm_apply_apply g))
  have hr := rightInvariant_of_finite_covolume (GQ V₁) (μ.map φ) h𝓖 (hvol ▸ ENNReal.ofReal_ne_top)
  exact isVol_of_pair V' (isVolMeas_reLat V₁ V'.L0 V'.standardTuple_isLattice V'.baseLattice_isUnimodular hν hr) h𝓖 hx hvol

theorem sig_eq {W₁ W₂ : HSp D} (e : W₁.V ≃ₗ[D.host.E] W₂.V) (he : ∀ a b, W₂.hT (e a) (e b) = W₁.hT a b)
    (hr : W₁.rank = W₂.rank) (h₁ : W₁.SigOK) (h₂ : W₂.SigOK) (τ : D.host.E →+* ℂ) : W₂.sig τ = W₁.sig τ := by
  have hw : (Matrix.of fun i j => W₂.hT (e (W₁.frame i)) (e (W₁.frame j))) = W₁.gram :=
    Matrix.ext fun i j => he _ _
  have := sig_family W₂ τ (D.sp.cm.cmUnram.2.1 τ) _ (hw ▸ h₁ τ) (h₂ τ)
  have s1 := sig_sum W₁ h₁ τ
  have s2 := sig_sum W₂ h₂ τ
  exact Prod.ext (by omega) (by omega)

def OneVector (D : D7) (W : HSp D) (P Q : ℕ) (β : D.host.E) (P' Q' : ℕ) : Prop :=
  ∃ x : W.V, W.hT x x = β ∧ ∃ (W' : HSp D) (ι : W'.V →ₗ[D.host.E] W.V),
    HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧ (∀ τ, W'.sig τ = (P', Q')) ∧
    ∀ (μ : Measure (GA D W)) (𝓕 : Set (GA D W)) (μ' : Measure (GA D W')) (𝓕' : Set (GA D W')),
      IsVolMeas D W P Q μ → IsFundamentalDomain (GQ W) 𝓕 μ → IsVolMeas D W' P' Q' μ' →
      IsFundamentalDomain (GQ W') 𝓕' μ' →
      (μ 𝓕).toReal / (μ' 𝓕').toReal = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E W.rank

end GlobalTheory.VolumeRatioTypings
end
end

