import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Bundle0003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.Transfer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.NilpotentMeasureRecursion
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0014
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PairingOmegaPrimeZ
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0053

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXLeaves
section
noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace Formalism.L2.SG.Pf.MassDataX

theorem hinfCompact_holds : MassDataMassesW.HinfCompact :=
  PIW.MassDataColumns.hinfCompact_of Formalism.L2.SG.Closed.AdBridgeIso_holds Formalism.L2.SG.Pf.MeasInfW.measure_isomorphism_at_infinity
    Formalism.L2.SG.Pf.MeasInfW.hermitian_measure_recursion (fun X u => Formalism.L2.SG.Pf.hinf_compact X u)

theorem finHA_eq_eFin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    finHA X hb x = Formalism.L2.SG.Pf.Meas.eFin X.B.I hb x := rfl

theorem kCompactOpen_holds : MassDataMassesW.KCompactOpen := by
  intro D X
  have hb := Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I
  have hs : Function.Surjective (finHA X hb) := by
    intro y
    obtain ⟨x, hx⟩ := (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).surjective y
    exact ⟨x, by rw [finHA_eq_eFin]; exact hx⟩
  have himg : ((MassDataMassesW.KX X : Subgroup _) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
      Formalism.L2.SG.Pf.Meas.eFin X.B.I hb '' X.B.I.Kset := by
    rw [MassDataMassesW.KX, PIW.MassDataColumns.kf_eq_image X hb hs]
    rfl
  rw [himg]
  exact ⟨(Formalism.L2.SG.Closed.AutKCompact_holds X.B.I).image (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).continuous,
    (Formalism.L2.SG.Pf.Meas.eFin X.B.I hb).isOpenMap _ (Formalism.L2.SG.Pf.kset_open X.B.I)⟩

theorem dc_finite_mono {G : Type} [Group G] (Γ K' K : Subgroup G) (h : K' ≤ K)
    (hf : Finite (DoubleCoset.Quotient (Γ : Set G) (K' : Set G))) :
    Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)) := by
  haveI : Finite (Quotient (DoubleCoset.setoid (Γ : Set G) (K' : Set G))) := hf
  have hr : ∀ a b : G, (DoubleCoset.setoid (Γ : Set G) (K' : Set G)) a b → (DoubleCoset.setoid (Γ : Set G) (K : Set G)) a b := by
    intro a b hab
    rw [DoubleCoset.rel_iff] at hab ⊢
    obtain ⟨x, hx, y, hy, hxy⟩ := hab
    exact ⟨x, hx, y, h hy, hxy⟩
  show Finite (Quotient (DoubleCoset.setoid (Γ : Set G) (K : Set G)))
  refine Finite.of_surjective (Quotient.map' id hr) ?_
  intro q
  induction q using Quotient.inductionOn' with
  | h a => exact ⟨Quotient.mk'' a, rfl⟩

theorem hermitian_level_le {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) :
    PIW.MassDataColumns.unitaryLevelClosureSubgroup X hb u ≤ MassDataMassesW.KH X u := by
  rw [PIW.MassDataColumns.unitaryLevelClosureSubgroup, Subgroup.closure_le]
  rintro ⟨h, hh⟩ hk
  obtain ⟨y, ⟨k, hk2, rfl⟩, hy⟩ := hk
  show h ∈ MassDataMassesW.KX X
  have hy' : finHA X hb (X.xu u) * finHA X hb k * (finHA X hb (X.xu u))⁻¹ = h := hy
  rw [← hy']
  have hxu : finHA X hb (X.xu u) ∈ MassDataMassesW.KX X :=
    (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 (X.xu_K u)
  have hkK : finHA X hb k ∈ MassDataMassesW.KX X :=
    (PIW.MassDataColumns.finHA_mem_Kf_iff X hb _).2 ((Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 k hk2)
  exact (MassDataMassesW.KX X).mul_mem ((MassDataMassesW.KX X).mul_mem hxu hkK) ((MassDataMassesW.KX X).inv_mem hxu)

theorem classFinite_holds : MassDataMassesW.ClassFinite := by
  intro D X u
  have hb := Formalism.L2.SG.Closed.AdBridgeIso_holds X.B.I
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hF := Formalism.L2.SG.Closed.ClassFin_holds X u hK
  have hc := PIW.MassDataColumns.class_sets_equal_card X hb hK u (Formalism.L2.SG.Closed.AdBridgeGF_holds X.B.I)
    (Formalism.L2.SG.Closed.level_subgroup_properties X)
  have hne : Nonempty (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) := inferInstance
  haveI : Finite (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) := hF
  have hfin : Finite (PIW.MassDataColumns.ClsHA X hb u) := by
    have hpos : 0 < Nat.card (Formalism.L2.SG.ColsDim.Classes (Formalism.L2.SG.PoincareInHH.PoincareSetting.iotaF X u) (Formalism.L2.SG.PoincareInHH.PoincareSetting.Ku X u hK)) :=
      Nat.card_pos
    exact Nat.finite_of_card_ne_zero (hc ▸ hpos.ne')
  exact dc_finite_mono _ _ _ (hermitian_level_le X hb u) hfin

end Formalism.L2.SG.Pf.MassDataX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemSpanAaF
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {D : D7} (Z : LocDat D) (p : PlF D)

theorem mem_span_aaF {N : D.host.E} {c b : Fin (D.R.rS + 1)} (hN : ∀ x ∈ aaF D b, x * N ∈ aaF D c)
    {y : (D.s.atP p).Ep}
    (hy : y ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D b : FractionalIdeal _ _) : Set D.host.E))) :
    (D.s.atP p).ιE N * y ∈
      Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D c : FractionalIdeal _ _) : Set D.host.E)) := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨x * N, hN x hx, ?_⟩
    rw [map_mul, mul_comm]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul o y _ hy =>
    have e : (D.s.atP p).ιE N * (o • y) = o • ((D.s.atP p).ιE N * y) := by
      show _ * ((o : (D.s.atP p).Ep) * y) = (o : (D.s.atP p).Ep) * (_ * y)
      ring
    rw [e]
    exact Submodule.smul_mem _ _ hy

theorem loc_int {N : D.host.E} {c b : Fin (D.R.rS + 1)} (hN : ∀ x ∈ aaF D b, x * N ∈ aaF D c) :
    ∃ o ∈ (Z.M p).L.O, (D.s.atP p).ιE N * frFac Z.δ p b = frFac Z.δ p c * o := by
  have hD := Formalism.L2.SG.Pf.locDiffC_holds D Z
  have hb : frFac Z.δ p b ∈
      Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' ((aaF D b : FractionalIdeal _ _) : Set D.host.E)) := by
    rw [hD p b]
    exact Submodule.subset_span rfl
  have h := mem_span_aaF Z p hN hb
  rw [hD p c, Submodule.mem_span_singleton] at h
  obtain ⟨o, ho⟩ := h
  refine ⟨o, o.2, ?_⟩
  rw [← ho]
  show (o : (D.s.atP p).Ep) * frFac Z.δ p c = frFac Z.δ p c * o
  ring

def locU (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  Matrix.diagonal (fun a => Ring.inverse (frFac Z.δ p a)) * N.map (D.s.atP p).ιE *
    Matrix.diagonal (frFac Z.δ p)

theorem locU_apply (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (c b : Fin (D.R.rS + 1)) :
    locU Z p N c b = Ring.inverse (frFac Z.δ p c) * (D.s.atP p).ιE (N c b) * frFac Z.δ p b := by
  simp [locU, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem locU_int (N : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hU : ∀ a b, b < a → N a b = 0) (hd : ∀ a, N a a = 1)
    (hN : ∀ c b, c < b → ∀ x ∈ aaF D b, x * N c b ∈ aaF D c) :
    (∀ a, locU Z p N a a = 1) ∧ (∀ a b, b < a → locU Z p N a b = 0) ∧ ∀ a b, locU Z p N a b ∈ (Z.M p).L.O := by
  have hu : ∀ a, Ring.inverse (frFac Z.δ p a) * frFac Z.δ p a = 1 := fun a =>
    Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)
  refine ⟨fun a => ?_, fun a b h => ?_, fun a b => ?_⟩
  · rw [locU_apply, hd, map_one, mul_one, hu]
  · rw [locU_apply, hU a b h, map_zero, mul_zero, zero_mul]
  · rcases lt_trichotomy a b with h | h | h
    · obtain ⟨o, ho, he⟩ := loc_int Z p (hN a b h)
      rw [locU_apply, mul_assoc, he, ← mul_assoc, hu, one_mul]
      exact ho
    · subst h
      rw [locU_apply, hd, map_one, mul_one, hu]
      exact Subring.one_mem _
    · rw [locU_apply, hU a b h, map_zero, mul_zero, zero_mul]
      exact Subring.zero_mem _

end Loc

end Formalism.L2.SG.Pf.FibQ
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCOfOcc
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp

set_option linter.dupNamespace false

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def OccT (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (t : TauC Y u u') : Prop :=
  t ∈ (Y.tO u u').ngSet ∧ (Y.tO u u').vec t ≠ 0 ∧ clsOf Y u u' t = c ∧ ptPN t = γ

def yT (t : TauC Y u u') : (VS D).V := yv (X.Fu u) t.frame.fl

def yT' (t : TauC Y u u') : (VS D).V := t.lin.symm (yv t.frame.fl (X.Fu u))

def coefA (t0 t : TauC Y u u') : D.host.E :=
  brS (VS D) (yT Y u u' t) (yT Y u u' t0) / brS (VS D) (yT Y u u' t0) (yT Y u u' t0)

def coefA' (t0 t : TauC Y u u') : D.host.E :=
  brS (VS D) (yT' Y u u' t) (yT' Y u u' t0) / brS (VS D) (yT' Y u u' t0) (yT' Y u u' t0)

theorem occ_iff (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
    (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :
    PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν ↔ ∃ t, OccT Y u u' c γ t ∧ nmlOf Y u u' t = ν := by
  constructor
  · rintro ⟨t, h1, h2, h3, h4, h5⟩
    exact ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
  · rintro ⟨t, ⟨h1, h2, h3, h4⟩, h5⟩
    exact ⟨t, h1, h2, h3, h4, h5⟩

end Defs

section Rel

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def RelC (t0 t : TauC Y u u') : Prop :=
  (Y.tO u u').rowOf t = (Y.tO u u').rowOf t0 ∧ (Y.tO u u').s0 t0 t = 1

end Rel

def NmlLine : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 t : TauC Y u u', Gt t0 ≠ 0 → Gt t ≠ 0 → ptPN t0 = γ → ptPN t = γ → RelC Y u u' t0 t →
          coefA Y u u' t0 t * star (coefA Y u u' t0 t) = 1 ∧ coefA' Y u u' t0 t * star (coefA' Y u u' t0 t) = 1

def NmlInt : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 : TauC Y u u', Gt t0 ≠ 0 → ptPN t0 = γ →
        ∃ J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E, J ≠ 0 ∧ J' ≠ 0 ∧
          (∀ t : TauC Y u u', Gt t ≠ 0 → ptPN t = γ → RelC Y u u' t0 t →
            coefA Y u u' t0 t ∈ J ∧ coefA' Y u u' t0 t ∈ J') ∧
          (1 : ℝ) ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * NormalInvariants.PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2 ∧
          (1 : ℝ) ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u' : ℕ) : ℝ) ^ (2 * D.R.f) * NormalInvariants.PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2

def NmlSep : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ γ : PN.Pts D.host.E D.R.rS, 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∀ t0 t1 t2 : TauC Y u u', Gt t0 ≠ 0 → Gt t1 ≠ 0 → Gt t2 ≠ 0 →
          ptPN t0 = γ → ptPN t1 = γ → ptPN t2 = γ → RelC Y u u' t0 t1 → RelC Y u u' t0 t2 →
          coefA Y u u' t0 t1 = coefA Y u u' t0 t2 → coefA' Y u u' t0 t1 = coefA' Y u u' t0 t2 →
          nmlOf Y u u' t1 = nmlOf Y u u' t2

theorem relC_of_occ {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (hTie : ConcTie X Y)
    {c : Set (TauC Y u u')} {γ : PN.Pts D.host.E D.R.rS} {t0 t : TauC Y u u'}
    (h0 : OccT Y u u' c γ t0) (h : OccT Y u u' c γ t) : RelC Y u u' t0 t := by
  have hrefl := (CorankRelation.corankOne_equivalence_holds D X Y u u' hTie).1 t h.1
  have ht : t ∈ clsOf Y u u' t := ⟨h.1, rfl, hrefl⟩
  rw [h.2.2.1, ← h0.2.2.1] at ht
  exact ⟨ht.2.1, ht.2.2⟩

theorem nmlInv_of (hL : NmlLine) (hI : NmlInt) (hS : NmlSep) : NormalInvariants.NmlInv := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a1, b1, H1⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨a2, b2, H2⟩ := hI Cg cb Cw cT CT C0
  obtain ⟨a3, b3, H3⟩ := hS Cg cb Cw cT CT C0
  refine ⟨max a1 (max a2 a3), max b1 (max b2 b3), fun C' Cl hC hCl D large₂ X Y u u' hctx νL νB ng c γ hocc hNG => ?_⟩
  have hC1 : a1 ≤ C' := le_trans (le_max_left _ _) hC
  have hC2 : a2 ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC
  have hC3 : a3 ≤ C' := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC
  have hl1 : b1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hl2 : b2 ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hl3 : b3 ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  obtain ⟨ν0, hν0⟩ := hocc
  obtain ⟨t0, ht0, -⟩ := (occ_iff Y u u' νL νB ng c γ ν0).1 hν0
  have hTie : ConcTie X Y := hctx.2.2
  have hG0 : Gt t0 ≠ 0 := ht0.1.1
  obtain ⟨J, J', hJ, hJ', hmem, hb, hb'⟩ := H2 C' Cl hC2 hl2 D large₂ X Y u u' hctx γ hNG t0 hG0 ht0.2.2.2
  set pick : NuC D → TauC Y u u' := fun ν =>
    if h : ∃ t, OccT Y u u' c γ t ∧ nmlOf Y u u' t = ν then h.choose else t0 with hpick
  have hpick_spec : ∀ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν →
      OccT Y u u' c γ (pick ν) ∧ nmlOf Y u u' (pick ν) = ν := by
    intro ν hν
    have h := (occ_iff Y u u' νL νB ng c γ ν).1 hν
    simp only [hpick, dif_pos h]
    exact h.choose_spec
  refine ⟨J, J', 1, 1, fun ν => (coefA Y u u' t0 (pick ν), coefA' Y u u' t0 (pick ν)), hJ, hJ', one_ne_zero,
    one_ne_zero, fun ν hν => ?_, fun ν₁ ν₂ h₁ h₂ hκ => ?_, ?_, ?_⟩
  · obtain ⟨hp, -⟩ := hpick_spec ν hν
    obtain ⟨m1, m2⟩ := hmem _ hp.1.1 hp.2.2.2 (relC_of_occ hTie ht0 hp)
    obtain ⟨n1, n2⟩ := H1 C' Cl hC1 hl1 D large₂ X Y u u' hctx γ hNG t0 _ hG0 hp.1.1 ht0.2.2.2 hp.2.2.2
      (relC_of_occ hTie ht0 hp)
    exact ⟨m1, n1, m2, n2⟩
  · obtain ⟨hp1, he1⟩ := hpick_spec ν₁ h₁
    obtain ⟨hp2, he2⟩ := hpick_spec ν₂ h₂
    have hk1 := congrArg Prod.fst hκ
    have hk2 := congrArg Prod.snd hκ
    simp only at hk1 hk2
    rw [← he1, ← he2]
    exact H3 C' Cl hC3 hl3 D large₂ X Y u u' hctx γ hNG t0 _ _ hG0 hp1.1.1 hp2.1.1 ht0.2.2.2 hp1.2.2.2 hp2.2.2.2
      (relC_of_occ hTie ht0 hp1) (relC_of_occ hTie ht0 hp2) hk1 hk2
  · rw [map_one]
    simpa using hb
  · rw [map_one]
    simpa using hb'

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SmulCancelQ
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem dec_of {U W : Submodule E V} (h : IsCompl U W) (x : V) : ∃ a ∈ U, ∃ b ∈ W, a + b = x := by
  have hx : x ∈ U ⊔ W := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  exact Submodule.mem_sup.mp hx

theorem dec_unique {U W : Submodule E V} (h : IsCompl U W) {a a' b b' : V} (ha : a ∈ U) (ha' : a' ∈ U)
    (hb : b ∈ W) (hb' : b' ∈ W) (e : a + b = a' + b') : a = a' ∧ b = b' := by
  have h1 : a - a' ∈ U := U.sub_mem ha ha'
  have heq : a - a' = b' - b := by
    rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
  have h2 : a - a' ∈ W := by
    rw [heq]
    exact W.sub_mem hb' hb
  have h0 : a - a' = 0 := by
    have hbot := h.inf_eq_bot
    rw [Submodule.eq_bot_iff] at hbot
    exact hbot _ ⟨h1, h2⟩
  have haa : a = a' := sub_eq_zero.mp h0
  refine ⟨haa, ?_⟩
  rw [haa] at e
  exact add_left_cancel e

theorem dec_diff {U W : Submodule E V} (h : IsCompl U W) (c : E) {a a' a'' b b' b'' x x' y : V}
    (ha : a ∈ U) (ha' : a' ∈ U) (ha'' : a'' ∈ U) (hb : b ∈ W) (hb' : b' ∈ W) (hb'' : b'' ∈ W)
    (hx : a + b = x) (hx' : a' + b' = x') (hy : a'' + b'' = y) (hd : x - x' = c • y) :
    a - a' = c • a'' ∧ b - b' = c • b'' := by
  have hsum : (a - a') + (b - b') = c • a'' + c • b'' := by
    rw [← smul_add, hy, ← hd, ← hx, ← hx']
    abel
  exact dec_unique h (U.sub_mem ha ha') (U.smul_mem c ha'') (W.sub_mem hb hb') (W.smul_mem c hb'') hsum

theorem part_MMsharp (t : Term V M r) (Λ : Submodule M.L.O V) (hsd : H.IsSelfDual Λ) (hMM : MMo H t ≤ Λ)
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t.f t.f'))) (hb : b ∈ H.W0 t.f t.f')
    (hab : a + b ∈ Λ) : a ∈ MMsharp H t := by

  have hmm_le : ∀ i, H.MMfam t i ∈ H.Xp t.f ⊔ H.Xp t.f' := by
    intro i
    unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
    rcases hs : M.split with _ | g
    · dsimp only
      rcases i with i | i
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
    · dsimp only
      rcases i with i | i
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩))
          (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
  have hspan : Submodule.span E (Set.range (Sum.elim t.f t.f')) ≤ Submodule.span E (Set.range (H.MMfam t)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    unfold Formalism.MainNotions.S.Loc.HermSp.MMfam
    rcases hs : M.split with _ | g
    · dsimp only
      exact Submodule.subset_span ⟨i, rfl⟩
    · dsimp only
      rcases i with i | i
      · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
      · have hq : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
        have e : t.f' i = t.f i + algebraMap F E (g.q : F) • (algebraMap F E ((g.q : F)⁻¹) • (t.f' i - t.f i)) := by
          rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul]
          abel
        show t.f' i ∈ _
        rw [e]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩))
  refine ⟨hspan ha, fun m hm => ?_⟩
  have hmΛ : m ∈ Λ := hMM hm
  have hab' := (hsd.2.2 (a + b)).mp hab m hmΛ
  have hmX : m ∈ H.Xp t.f ⊔ H.Xp t.f' := by
    have hle : MMo H t ≤ (H.Xp t.f ⊔ H.Xp t.f').restrictScalars M.L.O := by
      unfold Formalism.L2.SG.LsDatumA.MMo
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmm_le i
    exact hle hm
  have hbm : H.h b m = 0 := (show ∀ x ∈ H.Xp t.f ⊔ H.Xp t.f', H.h b x = 0 from hb) m hmX
  rw [H.h_add_left, hbm, add_zero] at hab'
  exact hab'

theorem perp_left {g : Fin (r + 1) → V} {a b : V} (hb : b ∈ H.perp (H.X g)) (hab : a + b ∈ H.perp (H.X g)) :
    a ∈ H.perp (H.X g) := by
  have h1 := (H.perp (H.X g)).sub_mem hab hb
  simpa using h1

theorem smul_cancel_q (g : SplitG M.L) {v w : V}
    (h : algebraMap F E (g.q : F) • v = algebraMap F E (g.q : F) • w) : v = w := by
  have hq : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (Subtype.ext h0)
  have hu : IsUnit (algebraMap F E (g.q : F)) := (IsUnit.mk0 _ hq).map _
  exact (hu.smul_left_cancel).mp h

theorem transfer (t₁ t₂ : Term V M r) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (H.W0 t₂.f t₂.f'))
    (g₁ g₂ : Fin (r + 1) → V)
    (hY₂ : H.X g₂ ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')))
    (hW₁ : H.W0 t₁.f t₁.f' ≤ H.perp (H.X g₁)) (hW₂ : H.W0 t₂.f t₂.f' ≤ H.perp (H.X g₂))
    (χ : H.Wb g₁ ≃ₗ[E] H.Wb g₂)
    (hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'), χ (H.mkW g₁ ⟨w, hW₁ w.2⟩) = H.mkW g₂ ⟨ψ w, hW₂ (ψ w).2⟩)
    (hC2 : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X g₁),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X g₂),
        χ (H.mkW g₁ ⟨u, hu⟩) = H.mkW g₂ ⟨u', hu'⟩)
    {u₁ : V} (hu₁U : u₁ ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (hu₁p : u₁ ∈ H.perp (H.X g₁))
    (n : ↥(H.W0 t₁.f t₁.f')) (hx₁ : u₁ + n ∈ H.perp (H.X g₁))
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (hb : b ∈ H.W0 t₂.f t₂.f')
    (hap : a ∈ H.perp (H.X g₂)) (hx₂ : a + b ∈ H.perp (H.X g₂))
    (h : χ (H.mkW g₁ ⟨u₁ + n, hx₁⟩) = H.mkW g₂ ⟨a + b, hx₂⟩) :
    b = ψ n ∧ χ (H.mkW g₁ ⟨u₁, hu₁p⟩) = H.mkW g₂ ⟨a, hap⟩ := by
  obtain ⟨u', hu'U, hu'p, hχu⟩ := hC2 u₁ hu₁U hu₁p
  have hsplit : (⟨u₁ + n, hx₁⟩ : H.perp (H.X g₁)) = ⟨u₁, hu₁p⟩ + ⟨(n : V), hW₁ n.2⟩ := rfl
  rw [hsplit, map_add, map_add, hχu, hC1, ← map_add] at h
  unfold HermSp.mkW at h
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  have hz : u' + (ψ n : V) - (a + b) ∈ H.X g₂ := h
  have hzU := hY₂ hz
  have e : (u' - a - (u' + (ψ n : V) - (a + b))) + ((ψ n : V) - b) = 0 + 0 := by abel
  have key := dec_unique hU₂
    (Submodule.sub_mem _ (Submodule.sub_mem _ hu'U ha) hzU) (Submodule.zero_mem _)
    (Submodule.sub_mem _ (ψ n).2 hb) (Submodule.zero_mem _) e
  have hbψ : b = ψ n := (sub_eq_zero.mp key.2).symm
  refine ⟨hbψ, ?_⟩
  rw [hχu]
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  show u' - a ∈ H.X g₂
  have : u' - a = u' + (ψ n : V) - (a + b) := by rw [hbψ]; abel
  rw [this]
  exact hz

end RG2

end Formalism.L2.SG.LsDatumA
end
end

