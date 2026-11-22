import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalThetaGraphRationalIsometryMovedLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0294
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0295
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0296

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrbitLatticesInfFrameSpanEq
section
noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameSpanLat

variable {D : D7}

theorem localComplementUnitary_fixes_both_frames {Z : LocDat D} {p : PlF D} (P : LocNG.FPair (locH Z p) D.R.rS)
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : g ∈ P.UW0) :
    ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact fun _ => ⟨rfl, rfl⟩
  | mul x y _ _ hx hy =>
    intro b
    change x (y _) = _ ∧ x (y _) = _
    rw [(hy b).1, (hy b).2]; exact hx b
  | inv x _ hx =>
    intro b
    refine ⟨?_, ?_⟩
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq, (hx b).1]
    · change x.symm _ = _
      rw [LinearEquiv.symm_apply_eq, (hx b).2]

theorem h_zero_left {Z : LocDat D} {p : PlF D} (y : Vp D p) : (locH Z p).h 0 y = 0 := by
  show LocFacts₂ Z.M p 0 y = 0
  simp [LocFacts₂]

theorem frame_ne_zero {Z : LocDat D} {p : PlF D} (Fr : LocNG.FrameD (locH Z p) D.R.rS) (hT : Fr.T ≠ 0)
    (a : Fin (D.R.rS + 1)) : Fr.f a ≠ 0 := by
  intro h0
  induction a using Fin.lastCases with
  | last =>
    have h1 := Fr.h_zz
    rw [h0, h_zero_left] at h1
    have h2 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep Fr.T = 0 := neg_eq_zero.mp h1.symm
    exact hT ((map_eq_zero_iff _ (RingHom.injective _)).mp h2)
  | cast i =>
    have h1 := Fr.h_es i i
    rw [h0, h_zero_left, if_pos rfl] at h1
    exact zero_ne_one h1

theorem frFac_unit {p : PlF D} (δ : ∀ p, (D.s.atP p).Fp) (a : Fin (D.R.rS + 1)) (v : Vp D p)
    (hv : frFac δ p a • v ≠ 0) : IsUnit (frFac δ p a) := by
  unfold frFac at hv ⊢
  by_cases hu : IsUnit ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
    (D.R.rS - a.val))
  · exact isUnit_ringInverse.mpr hu
  · rw [Ring.inverse_non_unit _ hu, zero_smul] at hv
    exact absurd rfl hv

def fixSub (p : PlF D) (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) : Submodule D.host.E (VS D).V where
  carrier := {u | g (baseChange₂ D p u) = baseChange₂ D p u}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    rw [ha, hb]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [baseChange_smul₂, map_smul, ha]

theorem xplus_le {T : D.host.E} (F : LFlag (VS D) D.R.rS T) (S : Submodule D.host.E (VS D).V)
    (h : ∀ a, frame F a ∈ S) : Xplus F ≤ S := by
  show F.fl.X ⊔ Submodule.span _ {F.fl.z} ≤ S
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    have := h i.castSucc
    simpa [frame, FlagG.fvec] using this
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have := h (Fin.last _)
    simpa [frame, FlagG.fvec] using this

theorem le_of_loc (Z : LocDat D) (Λ₂ : LV D) (h2 : Submodule.IsLattice D.host.E Λ₂) (N : LV D)
    (hN : ∀ z ∈ N, ∀ p, baseChange₂ D p z ∈ lattice₂ D Z.M p Λ₂) : N ≤ Λ₂ := by
  intro x hx
  have hlat : Submodule.IsLattice D.host.E (Λ₂ ⊔ Submodule.span (𝓞 D.host.E) {x}) := by
    refine ⟨h2.fg.sup (Submodule.fg_span_singleton x), ?_⟩
    rw [eq_top_iff, ← h2.span_eq_top]
    exact Submodule.span_mono (by intro y hy; exact Submodule.mem_sup_left hy)
  have heq : ∀ p, lattice₂ D Z.M p (Λ₂ ⊔ Submodule.span (𝓞 D.host.E) {x}) = lattice₂ D Z.M p Λ₂ := by
    intro p
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [map_add]
      exact add_mem (Submodule.subset_span ⟨y, hy, rfl⟩) (hN _ (N.smul_mem c hx) p)
    · exact Submodule.span_mono (Set.image_mono (by intro y hy; exact Submodule.mem_sup_left hy))
  have := ((GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).1 _ Λ₂ hlat h2).2 heq
  rw [← this]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

theorem fix_span {u u' : D.what₂.Word}
    (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS)
    (hB : Based Z FP (Tu D u) (Tu D u') F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p))) (p : PlF D)
    {g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p} (hg : g ∈ (FP p).UW0) :
    Xplus F ⊔ Xplus F' ≤ fixSub p g := by
  have hN := (hR p).2.2.2.2.2.2
  refine sup_le (xplus_le F _ fun a => ?_) (xplus_le F' _ fun a => ?_)
  · have hfa := (localComplementUnitary_fixes_both_frames (FP p) hg a).1
    have hne := frame_ne_zero (FP p).A hN.2.1 a
    rw [(hB p).1] at hfa hne
    have hu := frFac_unit Z.δ a _ hne
    show g (baseChange₂ D p (frame F a)) = baseChange₂ D p (frame F a)
    rw [map_smul] at hfa
    exact hu.smul_left_cancel.mp hfa
  · have hfa := (localComplementUnitary_fixes_both_frames (FP p) hg a).2
    have hne := frame_ne_zero (FP p).B hN.2.2.2.1 a
    rw [(hB p).2.1] at hfa hne
    have hu := frFac_unit Z.δ a _ hne
    show g (baseChange₂ D p (frame F' a)) = baseChange₂ D p (frame F' a)
    rw [map_smul] at hfa
    exact hu.smul_left_cancel.mp hfa

theorem inf_span_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') := by
  intro D X Y u u' F F' w _ _ Z FP hB hR Λ₀ h0 Λ h1 hloc
  apply le_antisymm
  · refine le_inf (le_of_loc Z Λ₀ h0 _ fun z hz p => ?_) inf_le_right
    obtain ⟨g, hg, himg⟩ := hloc p
    have hfix : g (baseChange₂ D p z) = baseChange₂ D p z := fix_span F F' Z FP hB hR p hg hz.2
    have hm : baseChange₂ D p z ∈ lattice₂ D Z.M p Λ := Submodule.subset_span ⟨z, hz.1, rfl⟩
    rw [← himg] at hm
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.1 hm
    have : g y = g (baseChange₂ D p z) := by rw [hfix]; exact hyz
    rw [g.injective this] at hy
    exact hy
  · refine le_inf (le_of_loc Z Λ h1 _ fun z hz p => ?_) inf_le_right
    obtain ⟨g, hg, himg⟩ := hloc p
    have hfix : g (baseChange₂ D p z) = baseChange₂ D p z := fix_span F F' Z FP hB hR p hg hz.2
    have hm : baseChange₂ D p z ∈ lattice₂ D Z.M p Λ₀ := Submodule.subset_span ⟨z, hz.1, rfl⟩
    rw [← himg, ← hfix]
    exact Submodule.mem_map_of_mem hm

end GlobalTheory.FrameSpanLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalThetaGraphRationalIsometryMovedLatticeStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localThetaGraph_rationalIsometry_moved_lattice : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (p : PlF D) (σ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (gσ : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (U₁ U₂ : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) F₂ σ U₁ U₂ → Ext p σ gσ → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (q : (G.S p).V × (G.S p).V), (q ∈ (G.datOf (c.lat σ Λ) p).2.2 ↔ ∃ y' ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, ∃ y ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, y' ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F₂))) ∧ y ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).perp ((locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u))))) ∧ y' - gσ.symm ((c.c p).e.symm q.1) ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F₂)) ∧ y - gσ.symm ((c.c p).e.symm q.2) ∈ (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p).X (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame (lf D (X.Fu u)))) ∧ ∃ v ∈ lattice₂ D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p Λ, y' - y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (LocNG.theta ((⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).M p)) • v) := by
  first | exact @GlobalTheory.HL.graph_moved_local | exact GlobalTheory.HL.graph_moved_local | (intros; apply GlobalTheory.HL.graph_moved_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_bound_low_types : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ (l : ℕ) (hl : l ≤ r + 1) ν, n1 ν + (r + 1) ^ 2 ≤ q0 → NzOn (R ν) (lb ν) → ∃ w ∈ (R ν).sm, ‖w‖ = 1 ∧ ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, lenA k r z (Matrix.of x) (Fin.castLE hl a) ^ 2) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (Hsq r (Formalism.QuantumDeterminants.Tz k r z) b ^ l) := by
  first | exact @GlobalTheory.MomProdPart.product_moment_first | exact GlobalTheory.MomProdPart.product_moment_first | (intros; apply GlobalTheory.MomProdPart.product_moment_first <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassLowTypesFirstStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_low_types_first : Hyps → GlobalTheory.Dec.LowKMultOne → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → ∀ ν, n1 ν ≤ q0 → ∀ (φ : (Fin (r + 1) → ℝ) → ℝ) (Bd : ℝ≥0∞), Measurable φ → (∀ y, 0 ≤ φ y) → (∀ (Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (E : ∀ ν', Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν').smSub), PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν', n1 ν' ≤ q0 → (R ν').IsE Q (E ν') ∧ Formalism.REAL.GlRel (E ν')) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + (ν a : ℝ)) 0 w → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd) → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∫⁻ x, ENNReal.ofReal (φ (fun a => lenA k r z (Matrix.of x) a) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ Bd := by
  first | exact @GlobalTheory.LowTypeMass.mass_low | exact GlobalTheory.LowTypeMass.mass_low | (intros; apply GlobalTheory.LowTypeMass.mass_low <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetTransportedRealPointsImageStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_transported_real_points_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (S : Set X.B.I.Ginf), MeasurableSet S → MeasurableSet (Gm D '' (trX X C '' S)) := by
  first | exact @GlobalTheory.CovDom.measurableSet_Gm_trX_image | exact GlobalTheory.CovDom.measurableSet_Gm_trX_image | (intros; apply GlobalTheory.CovDom.measurableSet_Gm_trX_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureEqOfStrictFundamentalSetsPlacewiseStatement
section
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_eq_of_strictFundamentalSetsPlacewise : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (Γ Ω₁ Ω₂ : Set (ι → Formalism.QuantumDeterminants.Mt k r)),
    Γ.Countable → (fun _ => Matrix.of.symm 1) ∈ Γ → (∀ m ∈ Γ, ∀ m' ∈ Γ, GlobalTheory.DegVol.mulP m m' ∈ Γ) →
    (∀ m ∈ Γ, (fun v => Matrix.of.symm (Matrix.of (m v))⁻¹) ∈ Γ) →
    (∀ m ∈ Γ, ∀ v, Matrix.of (m v) ∈ Formalism.QuantumDeterminants.Nset k r) →
    GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₁ → GlobalTheory.DegVol.IsFund Γ (GlobalTheory.DegVol.RP k r (fun _ => 1)) Ω₂ →
    Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₁ = Measure.pi (fun _ : ι => GlobalTheory.Amp.lebN k r) Ω₂ := by
  first | exact @GlobalTheory.FundEq.measure_eq | exact GlobalTheory.FundEq.measure_eq | (intros; apply GlobalTheory.FundEq.measure_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureLeCardMul
section
open MeasureTheory Formalism.MainNotions.S NumberField Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongIndex

theorem measure_le_card_mul {G Q : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [Finite Q] (K H : Set G) (q : K → Q)
    (hq : ∀ x y : K, q x = q y → (y : G)⁻¹ * x ∈ H) : μ K ≤ (Nat.card Q : ENNReal) * μ H := by
  classical
  haveI := Fintype.ofFinite Q
  have h1 : K ⊆ ⋃ c : Q, Subtype.val '' (q ⁻¹' {c}) := fun x hx =>
    Set.mem_iUnion.2 ⟨q ⟨x, hx⟩, ⟨x, hx⟩, rfl, rfl⟩
  have h2 : ∀ c : Q, μ (Subtype.val '' (q ⁻¹' {c})) ≤ μ H := by
    intro c
    by_cases h : ∃ y, q y = c
    · obtain ⟨y, rfl⟩ := h
      rw [← measure_preimage_mul μ (y : G)⁻¹ H]
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hq x y hx
    · have : q ⁻¹' {c} = ∅ := Set.eq_empty_of_forall_notMem fun y hy => h ⟨y, hy⟩
      simp [this]
  calc μ K ≤ ∑ c : Q, μ (Subtype.val '' (q ⁻¹' {c})) :=
        (measure_mono h1).trans (measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _c : Q, μ H := Finset.sum_le_sum fun c _ => h2 c
    _ = _ := by simp [Nat.card_eq_fintype_card]

section Lift

variable {O A L n : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype n] [DecidableEq n]
  [AddCommGroup L] [Module O L] (S : Subring A) (ι : L →ₗ[O] (n → A)) (a : A)

theorem exists_approx (hO : ∀ o : O, algebraMap O A o ∈ S)
    (hS : ∀ s ∈ S, ∃ o : O, ∃ w ∈ S, s = algebraMap O A o + a * w) (ha : a ∈ S)
    {y : n → A} (hy : y ∈ Submodule.span S (Set.range ι)) :
    ∃ l : L, ∃ z ∈ Submodule.span S (Set.range ι), y = ι l + a • z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    exact ⟨l, 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, z, hz, rfl⟩ := hx
    obtain ⟨l', z', hz', rfl⟩ := hy
    exact ⟨l + l', z + z', add_mem hz hz', by rw [map_add, smul_add]; abel⟩
  | smul s x _ hx =>
    obtain ⟨l, z, hz, rfl⟩ := hx
    obtain ⟨o, w, hw, e⟩ := hS s s.2
    refine ⟨o • l, (⟨w, hw⟩ : S) • ι l + s • z,
      add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)) (Submodule.smul_mem _ _ hz), ?_⟩
    rw [map_smul, ← algebraMap_smul A o]
    simp only [Subring.smul_def, smul_add, smul_smul]
    rw [e, add_smul, mul_comm a (_ + _), add_assoc]

theorem exists_end [Module.Projective O L] (hO : ∀ o : O, algebraMap O A o ∈ S)
    (hS : ∀ s ∈ S, ∃ o : O, ∃ w ∈ S, s = algebraMap O A o + a * w) (ha : a ∈ S)
    (x : Matrix n n A) (hx : ∀ y ∈ Submodule.span S (Set.range ι), x *ᵥ y ∈ Submodule.span S (Set.range ι)) :
    ∃ φ : L →ₗ[O] L, ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), x *ᵥ ι l = ι (φ l) + a • z := by
  let N : Submodule O (n → A) :=
    { carrier := {w | ∃ z ∈ Submodule.span S (Set.range ι), w = a • z}
      add_mem' := by
        rintro _ _ ⟨z, hz, rfl⟩ ⟨z', hz', rfl⟩
        exact ⟨z + z', add_mem hz hz', (smul_add _ _ _).symm⟩
      zero_mem' := ⟨0, zero_mem _, by simp⟩
      smul_mem' := by
        rintro o _ ⟨z, hz, rfl⟩
        refine ⟨(⟨_, hO o⟩ : S) • z, Submodule.smul_mem _ _ hz, ?_⟩
        rw [Subring.smul_def, smul_comm a, algebraMap_smul] }
  let f : L →ₗ[O] ((n → A) ⧸ N) := N.mkQ ∘ₗ ι
  let h : L →ₗ[O] ((n → A) ⧸ N) := N.mkQ ∘ₗ (Matrix.mulVecLin x).restrictScalars O ∘ₗ ι
  have hh : ∀ l, h l ∈ LinearMap.range f := by
    intro l
    obtain ⟨l', z, hz, e⟩ := exists_approx S ι a hO hS ha (hx _ (Submodule.subset_span ⟨l, rfl⟩))
    refine ⟨l', ((Submodule.Quotient.eq N).2 ⟨z, hz, ?_⟩).symm⟩
    exact sub_eq_of_eq_add' e
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property f.rangeRestrict (h.codRestrict _ hh)
    f.surjective_rangeRestrict
  refine ⟨φ, fun l => ?_⟩
  have e : f (φ l) = h l := congrArg Subtype.val (LinearMap.congr_fun hφ l)
  obtain ⟨z, hz, e'⟩ := (Submodule.Quotient.eq N).1 e.symm
  exact ⟨z, hz, eq_add_of_sub_eq' e'⟩

theorem congr_of_end (g : ℕ) (x y : GL n A)
    (hx : x ∈ Formalism.UG.stabGL (Submodule.span S (Set.range ι)))
    (hy : y ∈ Formalism.UG.stabGL (Submodule.span S (Set.range ι))) (φ ψ θ : L →ₗ[O] L)
    (hφ : ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), (x : Matrix n n A) *ᵥ ι l = ι (φ l) + (g : A) • z)
    (hψ : ∀ l, ∃ z ∈ Submodule.span S (Set.range ι), (y : Matrix n n A) *ᵥ ι l = ι (ψ l) + (g : A) • z)
    (hθ : φ = ψ + g • θ) :
    y⁻¹ * x ∈ GlobalTheory.CongTop.cong (Submodule.span S (Set.range ι)) (g : A) := by
  refine ⟨mul_mem (inv_mem hy) hx, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨l, rfl⟩ := hv
    obtain ⟨z, hz, e⟩ := hφ l
    obtain ⟨z', hz', e'⟩ := hψ l
    refine ⟨((y⁻¹ : GL n A) : Matrix n n A) *ᵥ (ι (θ l) + z - z'),
      (inv_mem hy _).1 (sub_mem (add_mem (Submodule.subset_span ⟨_, rfl⟩) hz) hz'), ?_⟩
    have e2 : (x : Matrix n n A) *ᵥ ι l - (y : Matrix n n A) *ᵥ ι l = (g : A) • (ι (θ l) + z - z') := by
      rw [e, e', hθ, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_nsmul,
        ← Nat.cast_smul_eq_nsmul A, smul_sub, smul_add]
      abel
    rw [← Matrix.mulVec_smul, ← e2, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Units.inv_mul, Units.val_mul, Matrix.sub_mulVec]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨z, hz, e⟩ := hv
    obtain ⟨z', hz', e'⟩ := hw
    exact ⟨z + z', add_mem hz hz', by rw [Matrix.mulVec_add, e, e', smul_add]⟩
  | smul s v _ hv =>
    obtain ⟨z, hz, e⟩ := hv
    refine ⟨s • z, Submodule.smul_mem _ _ hz, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, Matrix.mulVec_smul, e, smul_comm]

end Lift

section Rank

variable {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))

theorem exists_inj (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ m ≤ n, ∃ e : (L →ₗ[𝓞 E] L) →ₗ[ℤ] (Fin m → Fin n → E), Function.Injective e := by
  obtain ⟨b, hbL, hb, hli⟩ := exists_linearIndependent E (L : Set (Fin n → E))
  haveI : Finite b := hli.finite
  haveI := Fintype.ofFinite b
  have hc : Fintype.card b ≤ n := by simpa using hli.fintype_card_le_finrank
  let u := (Fintype.equivFin b).symm
  let e : (L →ₗ[𝓞 E] L) →+ (Fin (Fintype.card b) → Fin n → E) :=
    { toFun := fun φ i => (φ ⟨u i, hbL (u i).2⟩ : L)
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  refine ⟨_, hc, e.toIntLinearMap, (injective_iff_map_eq_zero e).2 fun φ hφ => ?_⟩
  ext1 l
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E b (l : Fin n → E)
    (by rw [hb, hL]; trivial)
  have hle : Submodule.span (𝓞 E) b ≤ (LinearMap.ker φ).map L.subtype := by
    refine Submodule.span_le.2 fun w hw => ⟨⟨w, hbL hw⟩, ?_, rfl⟩
    have := congrFun hφ (u.symm ⟨w, hw⟩)
    simpa [e] using this
  obtain ⟨l', hl', e'⟩ := hle ht
  have e2 : l' = (t : 𝓞 E) • l := Subtype.ext e'
  rw [e2, SetLike.mem_coe, LinearMap.mem_ker, map_smul, smul_eq_zero] at hl'
  exact hl'.resolve_left (nonZeroDivisors.ne_zero t.2)

theorem card_end_quot (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) (g : ℕ) :
    ∃ r ≤ n ^ 2 * Module.finrank ℚ E,
      (nsmulAddMonoidHom (α := L →ₗ[𝓞 E] L) g).range.index = g ^ r := by
  obtain ⟨m, hm, e, he⟩ := exists_inj L hL
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hfg
  haveI : IsNoetherian (𝓞 E) L := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian (𝓞 E) (L →ₗ[𝓞 E] L) := isNoetherian_linearMap _ _ _
  haveI : Module.Finite (𝓞 E) (L →ₗ[𝓞 E] L) := Module.IsNoetherian.finite _ _
  haveI : Module.Finite ℤ (L →ₗ[𝓞 E] L) := Module.Finite.trans (𝓞 E) _
  haveI : Module.IsTorsionFree ℤ (L →ₗ[𝓞 E] L) := he.moduleIsTorsionFree e e.map_smul
  refine ⟨_, ?_, AddSubgroup.index_range_nsmul _ g⟩
  have h1 := e.rank_le_of_injective he
  rw [← IsFractionRing.rank_right_eq ℤ ℚ (Fin m → Fin n → E), ← Module.finrank_eq_rank,
    ← Module.finrank_eq_rank, Nat.cast_le] at h1
  refine h1.trans ?_
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← mul_assoc, sq]
  gcongr

end Rank

theorem measure_Kset_le : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] (g : ℕ), 1 ≤ g → μf I.Kset ≤ (g : ENNReal) ^ (2 * (I.n ^ 2 * I.f)) * μf (I.Kg g) ∧ 0 < μf (I.Kg g) ∧ μf I.Kset < ⊤ := by
  intro I μf _ g hg
  obtain ⟨-, -, hsc, hc, -, -, h⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨ho, ⟨H, hH⟩, -⟩ := h g hg
  refine ⟨?_, ho.measure_pos μf ⟨1, hH ▸ H.one_mem⟩, hc.measure_lt_top⟩
  haveI : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.2 I.L_fg
  haveI : Module.FinitePresentation (𝓞 I.E) I.L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 I.E) I.L := Module.Flat.projective_of_finitePresentation
  let ι : I.L →ₗ[𝓞 I.E] (Fin I.n → I.E ⊗[I.F] Af I.F) :=
    { toFun := fun x i => Formalism.UG.inclE (F := I.F) (Af I.F) ((x : Fin I.n → I.E) i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => rfl }
  have hL : I.Lf = Submodule.span (IntAf I.F I.E) (Set.range ι) := rfl
  have hO : ∀ o : 𝓞 I.E, algebraMap _ (I.E ⊗[I.F] Af I.F) o ∈ IntAf I.F I.E := fun o =>
    Formalism.UG.P.levelaf_tmul_mem o (one_mem _)
  have hS : ∀ s ∈ IntAf I.F I.E, ∃ o : 𝓞 I.E, ∃ w ∈ IntAf I.F I.E,
      s = algebraMap _ (I.E ⊗[I.F] Af I.F) o + (g : I.E ⊗[I.F] Af I.F) * w := by
    intro s hs
    obtain ⟨x, hx, w, hw, e⟩ := Formalism.UG.P.csSpan_approx Formalism.UG.P.csGlob_intAdApprox (g : 𝓞 I.F)
      (Nat.cast_ne_zero.2 (by omega)) hs
    refine ⟨⟨x, hx⟩, w, hw, ?_⟩
    rw [e, ← Formalism.UG.P.adelstab_incl_C, map_natCast, map_natCast]
    rfl
  have key := fun x : I.Kset => exists_end (IntAf I.F I.E) ι (g : I.E ⊗[I.F] Af I.F) hO hS
    (natCast_mem _ g) (I.fmat x) fun y hy => (x.2 y).1 hy
  choose φ hφ using key
  obtain ⟨r, hr, hi⟩ := card_end_quot I.L I.L_span I.L_fg g
  set N := (nsmulAddMonoidHom (α := I.L →ₗ[𝓞 I.E] I.L) g).range
  have hi' : Nat.card ((I.L →ₗ[𝓞 I.E] I.L) ⧸ N) = g ^ r := hi
  haveI : Finite ((I.L →ₗ[𝓞 I.E] I.L) ⧸ N) := Nat.finite_of_card_ne_zero (by rw [hi']; positivity)
  have h1 := measure_le_card_mul μf I.Kset (I.Kg g) (fun x => (QuotientAddGroup.mk (φ x) : _ ⧸ N))
    fun x y hxy => by
      obtain ⟨θ, hθ⟩ := QuotientAddGroup.eq.1 hxy.symm
      exact congr_of_end (IntAf I.F I.E) ι g _ _ x.2 y.2 (φ x) (φ y) θ (hφ x) (hφ y)
        (by rw [show g • θ = -φ y + φ x from hθ]; abel)
  refine h1.trans ?_
  rw [hi', Nat.cast_pow]
  have h2 : Module.finrank ℚ I.E = I.f * 2 := by
    rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]; rfl
  gcongr
  · exact_mod_cast hg
  · rw [h2] at hr; linarith

end GlobalTheory.CongIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePiPointsAtInfinitePlacesCMTypeImageStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePi_pointsAtInfinitePlacesCMType_image : ∀ (D : D7) (S : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)), Measure.pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (Gm D '' S) = Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) S := by
  first | exact @GlobalTheory.CovDom.measure_Gm_image | exact GlobalTheory.CovDom.measure_Gm_image | (intros; apply GlobalTheory.CovDom.measure_Gm_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureUnipotentTuplesFreeEntryBlocksStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_unipotent_tuples_free_entry_blocks : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (DU : UTr r → Set (ι → ℂ)) (DH : Fin r → Set (ι → Fin (k + 1) → ℂ)) (DC : UTr r → Set (ι → ℂ)) (DG : Fin r → Set (ι → ℝ)), (∀ p, MeasurableSet (DU p)) → (∀ a, MeasurableSet (DH a)) → (∀ p, MeasurableSet (DC p)) → (∀ a, MeasurableSet (DG a)) → MeasurableSet {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} = (2 : ℝ≥0∞) ^ (Fintype.card ι * (r * (r - 1) + r * (k + 1))) * ((∏ p, volume (DU p)) * (∏ a, volume (DH a)) * (∏ p, volume (DC p)) * ∏ a, volume (DG a)) := by
  first | exact @GlobalTheory.SnMass.VolN.BlockMeas.measure_blocks | exact GlobalTheory.SnMass.VolN.BlockMeas.measure_blocks | (intros; apply GlobalTheory.SnMass.VolN.BlockMeas.measure_blocks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralTensorBoundHypProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegralTensorBoundHyp_proof : GlobalTheory.TypeAsm.TensC := by
  first | exact @GlobalTheory.TensHS.tensC_holds | exact GlobalTheory.TensHS.tensC_holds | (intros; apply GlobalTheory.TensHS.tensC_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalDecompositionLocalNondegenerateStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_decomposition_local_nondegenerate : ∀ (D : D7) (U : Submodule D.host.E (VS D).V), U ⊓ orth (VS D) U = ⊥ → (∀ x : (VS D).V, ∃ a ∈ orth (VS D) U, ∃ b ∈ U, x = a + b) ∧ ∀ (Z : LocDat D) (p : PlF D) (v : Vp D p), v ∈ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (U : Set (VS D).V)) → (∀ u ∈ U, LocFacts₂ Z.M p v (baseChange₂ D p u) = 0) → v = 0 := by
  first | exact @GlobalTheory.decomp_orth_complement | exact GlobalTheory.decomp_orth_complement | (intros; apply GlobalTheory.decomp_orth_complement <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PiUnipotentModelMeasurableFullMeasureStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_unipotentModel_measurable_full_measure : ∀ (ι : Type) [Fintype ι] (k r : ℕ), MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.pi_nset_full | exact GlobalTheory.SnMass.VolN.pi_nset_full | (intros; apply GlobalTheory.SnMass.VolN.pi_nset_full <;> assumption)
end

