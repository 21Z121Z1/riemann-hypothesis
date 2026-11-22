import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0405
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0436
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0447
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0449
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0450
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0007
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesMeanEqGenusMean
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0092
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0071
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemOfPerpPerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CyclicDiscriminantLatticesFormOneGenus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0425
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0230
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0433
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0452
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0229
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0442
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0233
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0401
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0451
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatPassesToLocalCongruence
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IotaLoc

section Gen

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}
  (H : HermSp M V) (Λ : Submodule M.L.O V) (f f' : Fin (r + 1) → V)

theorem cong_add {v w : V} (hv : Cong H Λ f f' v) (hw : Cong H Λ f f' w) : Cong H Λ f f' (v + w) := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hv
  obtain ⟨a', ha', b', hb', c', hc', hbX', hcX', rfl⟩ := hw
  exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', c + c', add_mem hc hc', add_mem hbX hbX',
    add_mem hcX hcX', by abel⟩

theorem cong_neg {v : V} (hv : Cong H Λ f f' v) : Cong H Λ f f' (-v) := by
  obtain ⟨a, ha, b, hb, c, hc, hbX, hcX, rfl⟩ := hv
  exact ⟨-a, neg_mem ha, -b, neg_mem hb, -c, neg_mem hc, neg_mem hbX, neg_mem hcX, by abel⟩

theorem cong_of_mem {v : V} (hv : v ∈ H.smulLat (algebraMap F E (theta M)) Λ) : Cong H Λ f f' v :=
  ⟨v, hv, 0, zero_mem _, 0, zero_mem _, zero_mem _, zero_mem _, by simp⟩

theorem cong_iff_of_sub {v w : V} (h : v - w ∈ H.smulLat (algebraMap F E (theta M)) Λ) :
    Cong H Λ f f' v ↔ Cong H Λ f f' w := by
  constructor
  · intro hv
    have := cong_add H Λ f f' hv (cong_neg H Λ f f' (cong_of_mem H Λ f f' h))
    rwa [show v + -(v - w) = w by abel] at this
  · intro hw
    have := cong_add H Λ f f' hw (cong_of_mem H Λ f f' h)
    rwa [show w + (v - w) = v by abel] at this

end Gen

section Glob

variable {D : D7}

theorem ext_latP (Z : LocDat D) (p : PlF D) {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : Ext p β g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hβΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ) {v : Vp D p} (hv : v ∈ lattice₂ D Z.M p Λ) : g v ∈ lattice₂ D Z.M p Λ := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, hy, rfl⟩ := hv
    rw [hg y]
    refine Submodule.subset_span ⟨β y, ?_, rfl⟩
    rw [← hβΛ]
    exact Submodule.mem_map_of_mem hy
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : g (o • v) = o • g v := by rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ o hv

theorem ext_smulLat (Z : LocDat D) (p : PlF D) {β : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : Ext p β g) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hβΛ : Formalism.HermitianLatticesTheory.gmap β Λ = Λ) (c : (D.s.atP p).Ep) {v : Vp D p}
    (hv : v ∈ (locH Z p).smulLat c (lattice₂ D Z.M p Λ)) : g v ∈ (locH Z p).smulLat c (lattice₂ D Z.M p Λ) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    show g (c • w) ∈ _
    rw [map_smul]
    exact Submodule.subset_span ⟨g w, ext_latP Z p hg hβΛ hw, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul o v _ hv =>
    have e : g (o • v) = o • g v := by rw [Subring.smul_def, Subring.smul_def, map_smul]
    rw [e]; exact Submodule.smul_mem _ o hv

end Glob

theorem iota_typed : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → ∀ β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, Formalism.HermitianLatticesTheory.gmap β Λ = Λ → (∀ a, frame F₂ a = β (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ β (gS D) → ∀ (p : PlF D) (g), Ext p β g → (Z.M p).split ≠ none → ∀ x' ∈ lattice₂ D Z.M p Λ, ∀ x ∈ lattice₂ D Z.M p Λ, x' ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame F₁))) → x ∈ (locH Z p).perp ((locH Z p).X (scaled Z p (frame (lf D F0)))) → (Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔ Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x')) := by
  intro D Z u u' F0 Λ hR F₁ F₂ _ _ β _ hβΛ _ hIota p g hg hsp x' hx'Λ x hxΛ hx' hx
  have hΛ : Submodule.IsLattice D.host.E Λ := hR.2.1.1
  have hLD := GlobalTheory.T.integers_dense_localIntegers_mod_g D p
  obtain ⟨l, hl, hxl⟩ := GlobalTheory.T.exists_global_vector_congruent_local_orthogonal D Z p hLD Λ hΛ (lf D F0) x hxΛ hx
  obtain ⟨l', hl', hxl'⟩ := GlobalTheory.T.exists_global_vector_congruent_local_orthogonal D Z p hLD Λ hΛ F₁ x' hx'Λ hx'
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.exists_integer_one_mod_g_at_place_zero_elsewhere D p
  have hlΛ : l ∈ Λ := (Submodule.mem_inf.1 hl).1
  have hl'Λ : l' ∈ Λ := (Submodule.mem_inf.1 hl').1
  have hβl' : β l' ∈ Λ := by rw [← hβΛ]; exact Submodule.mem_map_of_mem hl'Λ
  have e1 : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (x - x') ↔
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₁)) (baseChange₂ D p (l - l')) := by
    apply cong_iff_of_sub
    have e : x - x' - baseChange₂ D p (l - l') = (x - baseChange₂ D p l) - (x' - baseChange₂ D p l') := by rw [map_sub]; abel
    rw [e]; exact sub_mem hxl hxl'
  have e2 : Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (x - g x') ↔
      Cong (locH Z p) (lattice₂ D Z.M p Λ) (scaled Z p (frame (lf D F0))) (scaled Z p (frame F₂)) (baseChange₂ D p (l - β l')) := by
    apply cong_iff_of_sub
    have e : x - g x' - baseChange₂ D p (l - β l') = (x - baseChange₂ D p l) - g (x' - baseChange₂ D p l') := by
      rw [map_sub, map_sub, hg l']; abel
    rw [e]; exact sub_mem hxl (ext_smulLat Z p hg hβΛ _ hxl')
  rw [e1, e2, ← GlobalTheory.T.local_global_congruence_lattice_typed_place D Z p hsp a ha1 ha2 Λ hΛ (lf D F0) F₁ (l - l') (sub_mem hlΛ hl'Λ), ← GlobalTheory.T.local_global_congruence_lattice_typed_place D Z p hsp a ha1 ha2 Λ hΛ (lf D F0) F₂ (l - β l') (sub_mem hlΛ hβl')]
  have hal : a • l ∈ Lrep Λ (lf D F0) := Submodule.smul_mem _ a hl
  have hal' : a • l' ∈ Lrep Λ F₁ := Submodule.smul_mem _ a hl'
  have h := hIota (a • l') hal' (a • l) hal
  have e3 : β (a • l') = a • β l' := by
    rw [← algebraMap_smul D.host.E a l', LinearEquiv.map_smul, algebraMap_smul]
  rw [e3] at h
  rw [smul_sub, smul_sub]
  exact h

end GlobalTheory.IotaLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InverseMajorantLengthMomentLargeGapStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseMajorantLength_moment_largeGap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → 1 ≤ Tz k r z → ∀ ν (q : ℕ), n1 ν ≤ q0 → r * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) := by
  first | exact @GlobalTheory.InvLenMomentGap.inv_len_moment_gap | exact GlobalTheory.InvLenMomentGap.inv_len_moment_gap | (intros; apply GlobalTheory.InvLenMomentGap.inv_len_moment_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalUnipotentFrameCorrespondsUnderIsometryStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnipotent_frame_corresponds_under_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r k : ℕ} {P : LocNG.FPair H r} {S : Frames M.L r k} (c : WCoord P S) (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V), g ∈ NU H f ↔ (c.e.symm.trans g).trans c.e ∈ S.Nof (fun a => c.e (f a)) := by
  first | exact @GlobalTheory.HL.NUTransport.mem_NU_iff_mem_Nof | exact GlobalTheory.HL.NUTransport.mem_NU_iff_mem_Nof | (intros; apply GlobalTheory.HL.NUTransport.mem_NU_iff_mem_Nof <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanCountPrimitiveSublatticesOverGenusStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_count_primitive_sublattices_over_genus : ∀ c₀ : ℝ, 0 < c₀ → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), c₀ ≤ Cl → UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C := by
  first | exact @GlobalTheory.Mass.PrimMeanRow.main | exact GlobalTheory.Mass.PrimMeanRow.main | (intros; apply GlobalTheory.Mass.PrimMeanRow.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanPrimitiveCorankOneSublatticesBound
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMeanCorankOne

theorem num (a b Mk X Y c₁ c₂ de NT HH l m : ℝ) (j : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hMk : 0 ≤ Mk)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hA : a ≤ Mk * (X * Y)) (hB : b ≤ c₁ * c₂) (hm : Mk * NT ^ j ≤ m) (hde : 1 ≤ de) (hdH : de ≤ HH)
    (hN : 1 ≤ NT) (hNH : NT ≤ HH) (hl : 0 ≤ l) :
    a * b * de ^ j * (de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l)) ≤
      ((de / NT) ^ j * X * (Y * c₁ * c₂ * HH ^ (11 + 3 * l))) * m := by
  have hd0 : 0 ≤ de := by linarith
  have hN0 : 0 < NT := by linarith
  have hH1 : 1 ≤ HH := le_trans hde hdH
  have hH0 : 0 < HH := by linarith
  have hR : de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l) ≤ HH ^ (11 + 3 * l) := by
    have e1 : de ^ (4 + l) ≤ HH ^ (4 + l) := Real.rpow_le_rpow hd0 hdH (by linarith)
    have e2 : NT ^ 2 ≤ HH ^ 2 := pow_le_pow_left₀ hN0.le hNH 2
    have e3 : (de * NT) ^ (2 + l) ≤ (HH * HH) ^ (2 + l) :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul hdH hNH hN0.le hH0.le) (by linarith)
    have e4 : HH ^ (4 + l) * HH ^ 2 * (HH * HH) ^ (2 + l) = HH ^ (10 + 3 * l) := by
      rw [Real.mul_rpow hH0.le hH0.le, ← Real.rpow_natCast HH 2, ← Real.rpow_add hH0,
        ← Real.rpow_add hH0, ← Real.rpow_add hH0]
      congr 1; push_cast; ring
    have e5 : HH ^ (10 + 3 * l) ≤ HH ^ (11 + 3 * l) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)
    calc _ ≤ HH ^ (4 + l) * HH ^ 2 * (HH * HH) ^ (2 + l) := by
          gcongr
      _ = HH ^ (10 + 3 * l) := e4
      _ ≤ _ := e5
  have hR0 : 0 ≤ de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l) := by positivity
  calc a * b * de ^ j * (de ^ (4 + l) * NT ^ 2 * (de * NT) ^ (2 + l))
      ≤ (Mk * (X * Y)) * (c₁ * c₂) * de ^ j * HH ^ (11 + 3 * l) := by gcongr
    _ = ((de / NT) ^ j * X * (Y * c₁ * c₂ * HH ^ (11 + 3 * l))) * (Mk * NT ^ j) := by
        rw [div_pow]; field_simp
    _ ≤ _ := by gcongr

end GlobalTheory.Mass.PrimMeanCorankOne

namespace GlobalTheory.Mass.PrimMeanCorankOne

theorem main : ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ), UnitaryVolumeMass.stMassRatio D → Formalism.MainNotions.BridgeLemma₂.PrimitiveMeanCorankOne D large₂ u u' C' Cl Cg cb Cu cT CT C0 A := by
  intro D large₂ u u' C' Cl Cg cb Cu cT CT C0 A hR
  letI := D.host.cmStar
  intro hyp F0 he hz what₂ hrows de hde HH hdH hNH
  obtain ⟨-, ⟨-, hTp, -, hT3, -, hTs, -⟩, -⟩ := hyp
  unfold Cnt.MeanLe
  rcases what₂.eq_empty_or_nonempty with e | ⟨Λ₀, hΛ₀⟩
  · subst e; simp
  have hΛ₀r := hrows.1 Λ₀ hΛ₀
  have hK : IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨⟨hPD, hrk⟩, hrow⟩ := GlobalTheory.Mass.RowPerp.main D u F0 he hz
  obtain ⟨hint, hcyc⟩ := hrow Λ₀ hΛ₀r
  have hs := (D.sp.X 0).herm
  have hM := (GlobalTheory.Mass.RowPerpMass.main D u F0 he hz hTp hTs Λ₀ hΛ₀r).2
  have hgen := (GlobalTheory.Mass.CyclicGenus.main _ _ _ hK hs (D.sp.X 0).nondeg _ hTp hTs).2
  have hMG := GlobalTheory.MeanGenus.mean_rows_eq_mean_genus D u hTp hT3 hTs F0 he hz what₂ hrows Λ₀ hΛ₀r
  set h := (D.sp.X 0).hT with hh
  obtain ⟨reps, hreps⟩ := (final_massBasic _ _ h hs (GlobalTheory.Mass.GenusOrb.trace_pos_of_PD h hPD) _ hint.1).1
  set N : Submodule (𝓞 D.host.E) (D.sp.X 0).V → ℕ∞ := fun L => (primSp h L (D.R.k - 1) (de ^ 2)).encard with hN
  have hNinv : ∀ γ ∈ isom h, ∀ L, N (gmap γ L) = N L := fun γ hγ L =>
    (GlobalTheory.Mass.PrimMove.main _ _ h hK hs (D.sp.X 0).nondeg ⟨γ, hγ⟩ L ⊥ _ _).2
  have hMG' := hMG reps hreps N hNinv
  have hl : (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) *
      (Cnt.cntPrim h (Lat.L0X D Λ (lf D F0)) (D.R.k - 1) de : ℝ≥0∞)) =
      ∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * (N (Lat.L0X D Λ (lf D F0)) : ℝ≥0∞) := by
    refine Finset.sum_congr rfl fun Λ hΛ => ?_
    rw [(GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD _ (hrow Λ (hrows.1 Λ hΛ)).1).2.2.1]
  generalize Lat.L0X D Λ₀ (lf D F0) = L₀ at *
  obtain ⟨hm1, hm2, hst, -, hsum⟩ := GlobalTheory.Mass.GenusOrb.main _ _ h hK hs hPD L₀ hint.1
  have hr := hsum reps (fun L => (N L : ℝ≥0∞)) hreps (fun g M => by
    change ((N (gmap g.1 M) : ℕ∞) : ℝ≥0∞) = _
    rw [hNinv g.1 g.2 M])
  rw [hl]
  have hf : 1 ≤ D.R.f := by
    have h1 := D.R.toFrame.ord_pos
    have h2 : D.R.f = 2 * D.R.toFrame.ord := rfl
    omega
  have hk3 : 3 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  set t : ℕ := Lat.Tu D u ^ D.R.f with ht_def
  have ht : 1 ≤ t := Nat.one_le_pow _ _ hTp.pos
  have hmem : ∀ L ∈ genus h L₀, IsIntLat h L ∧ discN h L = t ^ 2 ∧
      (∃ s : Finset (D.sp.X 0).V, s.card ≤ 1 ∧
        dual h L = L ⊔ Submodule.span (𝓞 D.host.E) (s : Set (D.sp.X 0).V)) ∧
      ∀ x ∈ dual h L, ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) • x ∈ L := by
    intro L hL
    obtain ⟨a, ⟨e⟩⟩ := (hgen L₀ L hint hcyc).1 hL
    obtain ⟨b, c⟩ := GlobalTheory.Mass.PrimMeanRow.disc_of_equiv h L _ e
    refine ⟨a, by rw [b, GlobalTheory.Mass.PrimMeanRow.finrank_E, ht_def, ← pow_mul]; ring_nf,
      ((GlobalTheory.Mass.DetAgree.main _ _ h hK hs hPD L a).2.2.2.1 1).1 c, ?_⟩
    intro x hx
    have h1 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) • e (Submodule.Quotient.mk ⟨x, hx⟩) = 0 := by
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e (Submodule.Quotient.mk ⟨x, hx⟩))
      rw [← hr, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have h3 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) •
        (Submodule.Quotient.mk ⟨x, hx⟩ : ↥(dual h L) ⧸ L.comap (dual h L).subtype) = 0 :=
      e.injective (by rw [map_smul, h1, map_zero])
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h3
    exact h3
  have hU := GlobalTheory.Mass.StdMass.main _ hK
  have hT0 : ((Lat.Tu D u : ℕ) : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hTp.ne_zero
  have hnorm : Ideal.absNorm (Ideal.span {((Lat.Tu D u : ℕ) : 𝓞 D.host.E)}) = t ^ 2 := by
    rw [Ideal.absNorm_span_singleton, Algebra.norm_natCast, RingOfIntegers.rank,
      GlobalTheory.Mass.PrimMeanRow.finrank_E, ht_def, ← pow_mul]
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    ring_nf
  have hP := GlobalTheory.Mass.PrimMeanOne.main GlobalTheory.Mass.MaxFormula.main _ _ h hK hs hPD
    (GlobalTheory.Mass.exists_orthoLattice_of_unimodular _ hK) (D.R.k - 1) (by omega) (by rw [hrk]; omega)
    _ _ _ (hU (D.R.k - 1)).1 (hU (D.R.k - 1)).2.1 _ _ _ (hU 1).1 (hU 1).2.1 de t _ hde ht hT0 hnorm
    (genus h L₀) hst hmem
  have hv : 0 < D.host.v := Formalism.MainNotions.StandardLattice.host_v_pos D
  have hNT1 : 1 ≤ Cnt.NT D u := one_le_pow₀ (by exact_mod_cast hTp.one_le)
  have htNT : ((t : ℕ) : ℝ) = Cnt.NT D u := by
    rw [ht_def, Cnt.NT]; push_cast; rfl
  have hfd : fDeg D.host.E = D.R.f := GlobalTheory.Mass.PrimMeanRow.fDeg_E D
  have hA : Cnt.massU D.host.E (D.R.k - 1) ≤ Cnt.massS D D.R.k *
      ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) :=
    GlobalTheory.MassRatioInvBound.mass_pred_le D hR
  have hB : Cnt.massU D.host.E 1 ≤ (classNumber D.host.E : ℝ) * 2 ^ D.R.f := by
    have e1 := ((hU 1).2.2.2.2 _ (Formalism.HermitianLattices.Ext.L3.stdForm D.host.E 1) (Formalism.HermitianLattices.Ext.L3.stdLat D.host.E 1)
      (Formalism.HermitianLattices.Ext.L3.stdLat_isOrtho D.host.E 1)).1
    have e2 := Formalism.MainNotions.BridgeLemVN.mass_std_one_le hK
    rw [e1, hfd] at e2
    push_cast at e2
    exact e2
  have hbound := num (Cnt.massU D.host.E (D.R.k - 1)) (Cnt.massU D.host.E 1) (Cnt.massS D D.R.k)
    ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f))
    ((2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) (classNumber D.host.E : ℝ) (2 ^ D.R.f)
    de (Cnt.NT D u) HH (Real.logb 2 D.R.f) (mass h L₀) (D.R.k - 1)
    (hU (D.R.k - 1)).2.2.1.le (hU 1).2.2.1.le (hU D.R.k).2.2.1.le (by positivity)
    (by have := GlobalTheory.Mass.PrimMeanRow.one_le_rdE D; positivity) (Nat.cast_nonneg _) (by positivity)
    hA hB hM (by exact_mod_cast hde) hdH hNT1 hNH
    (Real.logb_nonneg one_lt_two (by exact_mod_cast hf))
  have key : (∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ) * ((N (Lat.L0X D Λ (lf D F0)) : ℕ∞) : ℝ≥0∞)) *
      ENNReal.ofReal (mass h L₀) ≤
      ((∑ Λ ∈ what₂, ENNReal.ofReal (wRow D F0 Λ)) *
        ENNReal.ofReal (((de : ℝ) / Cnt.NT D u) ^ (D.R.k - 1) *
          (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
          (Formalism.MainNotions.BridgeLemma₂.classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)))) * ENNReal.ofReal (mass h L₀) := by
    rw [hMG', hr, mul_assoc, ← ENNReal.ofReal_mul' hm2.le]
    refine mul_le_mul' le_rfl (hP.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [hfd, htNT]
    unfold Formalism.MainNotions.BridgeLemma₂.classWeightAlt
    exact hbound
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.ofReal_pos.2 hm2).ne' ENNReal.ofReal_ne_top).1 key

end GlobalTheory.Mass.PrimMeanCorankOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfTrivialOffSplitPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maximalCompact_of_trivial_off_splitPair : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (ε : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), ε * ε = ε → ε * Formalism.L2.SG.HidaSetting.sigA I ε = 0 → ε ∈ Formalism.MainNotions.S.IntAf I.F I.E → ∀ (k : I.Gf), (∀ i j, (1 - ε - Formalism.L2.SG.HidaSetting.sigA I ε) * (I.fmat k - 1) i j = 0) → (∀ i j, ε * ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → (∀ i j, ε * ((β₀⁻¹ * ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → k ∈ I.Kset := by
  first | exact @GlobalTheory.SplitPairK.mem_kset_of_split | exact GlobalTheory.SplitPairK.mem_kset_of_split | (intros; apply GlobalTheory.SplitPairK.mem_kset_of_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRationalUnipotentOfLocalExtensionStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_rationalUnipotent_of_local_extension : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p), GlobalTheory.LocOver.Ext p γ g → g ∈ NU (locH Z p) (scaled Z p (frame F)) → γ ∈ NRat F := by
  first | exact @GlobalTheory.LocReflect.mem_nrat_of_ext | exact GlobalTheory.LocReflect.mem_nrat_of_ext | (intros; apply GlobalTheory.LocReflect.mem_nrat_of_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovesToDeterminesUnipotentFactorisationStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moves_to_determines_unipotent_factorisation : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (t₀ : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∃ A A' : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧ IsUpUni A' ∧ (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) ∧ (∀ b, m (frame (lf D (X.Fu u')) b) = ∑ a, A' a b • frame (lf D (X.Fu u')) a) ∧ MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
  first | exact @GlobalTheory.FrameStep.step | exact GlobalTheory.FrameStep.step | (intros; apply GlobalTheory.FrameStep.step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneBessel_torusTranslates_largeGap : GlobalTheory.GapIn.Hyp → ∃ Cgf : ℝ, ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf := by
  first | exact @GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp | exact GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp | (intros; apply GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OpenCellAmplitudeNormEqConstDivDegreeLargeGapStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openCellAmplitudeNorm_eq_const_div_degree_largeGap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ Cg cb Cu cT CT C0 C1 Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∃ K : ℝ, 0 < K ∧ ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A : LocS W, GoodS D lam' A → MMv D w w' A μsec = ENNReal.ofReal (K / A.deg) := by
  first | exact @GlobalTheory.Amp.OpenCellNormGap.norm_eq_const_div_deg_gap | exact GlobalTheory.Amp.OpenCellNormGap.norm_eq_const_div_deg_gap | (intros; apply GlobalTheory.Amp.OpenCellNormGap.norm_eq_const_div_deg_gap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentConjIffOfUnitriangularIsometryStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_unipotent_conj_iff_of_unitriangular_isometry : ∀ (D : D7) {T : D.host.E} (F F0 : LFlag (VS D) D.R.rS T) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → IsUpUni U → (∀ b, σ (frame F b) = ∑ a, U a b • frame F0 a) → ∀ n, n ∈ NRat F ↔ σ * n * σ⁻¹ ∈ NRat F0 := by
  first | exact @GlobalTheory.FlagMove.nrat_conj_iff | exact GlobalTheory.FlagMove.nrat_conj_iff | (intros; apply GlobalTheory.FlagMove.nrat_conj_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ResidueCmFieldFiniteAdeleTensorEquivEqNatCastStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_cmFieldFiniteAdeleTensorEquiv_eq_natCast : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E) (ha : GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (m : ℕ), a ∈ ReciprocityTheory.Aut.ALint D.host.E → Valued.v (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) < 1 → Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩ = (m : Formalism.L2.DIV.kP s.w) := by
  first | exact @GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast | exact GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast | (intros; apply GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast <;> assumption)
end

