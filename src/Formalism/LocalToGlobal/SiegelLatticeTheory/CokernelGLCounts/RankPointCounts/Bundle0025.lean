import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0024
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0018
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountableConjSub

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ClassFrameNormal
section
noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

namespace ClassFrameNormal

open MeasureTheory

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

theorem oo_map_mulLeft {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [CompleteSpace V] (Ph : G → V) (Ph' : G → V') (γ s s' : G) (a b : ℂ)
    (A : V ≃ₗᵢ[ℂ] V) (B : V' ≃ₗᵢ[ℂ] V') (hA : ∀ x, Ph (s * x) = a • A (Ph x))
    (hB : ∀ x, Ph' (s' * x) = b • B (Ph' x)) :
    Formalism.L2.SG.TermOp.OO (μ.map (fun x => s * x)) Set.univ Ph Ph' (s * γ * s'⁻¹) =
      (a * conj b) • ((A.toContinuousLinearEquiv : V →L[ℂ] V).comp
        ((Formalism.L2.SG.TermOp.OO μ Set.univ Ph Ph' γ).comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V'))) := by
  classical
  have hEF : ∀ F : V' →L[ℂ] V,
      (B.toContinuousLinearEquiv.arrowCongr A.toContinuousLinearEquiv) F =
        (A.toContinuousLinearEquiv : V →L[ℂ] V).comp
          (F.comp (B.symm.toContinuousLinearEquiv : V' →L[ℂ] V')) := by
    intro F
    ext ξ
    simp [ContinuousLinearEquiv.arrowCongr_apply]
  have hmap : ∀ f : G → (V' →L[ℂ] V),
      ∫ x, f x ∂(μ.map fun x => s * x) = ∫ x, f (s * x) ∂μ :=
    fun f => (MeasurableEquiv.mulLeft s).measurableEmbedding.integral_map f
  have hpt : ∀ x, Formalism.L2.SG.TermOp.rk1 (Ph (s * x)) (Ph' ((s * γ * s'⁻¹)⁻¹ * (s * x))) =
      (a * conj b) • (B.toContinuousLinearEquiv.arrowCongr A.toContinuousLinearEquiv)
        (Formalism.L2.SG.TermOp.rk1 (Ph x) (Ph' (γ⁻¹ * x))) := by
    intro x
    have h1 : (s * γ * s'⁻¹)⁻¹ * (s * x) = s' * (γ⁻¹ * x) := by group
    rw [h1, hA, hB, hEF, Formalism.L2.SG.RealObj.InfCut.rank_one_smul_isometry]
  unfold Formalism.L2.SG.TermOp.OO
  rw [Measure.restrict_univ, Measure.restrict_univ, hmap]
  simp_rw [hpt]
  rw [integral_smul, ContinuousLinearEquiv.integral_comp_comm, hEF]

end Gen

end ClassFrameNormal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def LiftAtSomeC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∃ w, s.1.toTerm.atPt w

def LiftDecompC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹

def DFrameAtS (sc : ℝ) : Prop :=
  0 < sc → ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) →
    (∀ v, 0 < Formalism.L2.SG.RealObj.GX X u u' D.host.rdE (Formalism.L2.SG.RealObj.gamW X u u' w) v) →
      ∃ h h', Formalism.L2.SG.RealObj.IsDFrameX X u u' sc i0 i0' (Formalism.L2.SG.RealObj.gamW X u u' w) h h'

def LiftGPosC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ v, 0 < Formalism.L2.SG.RealObj.GX X u u' D.host.rdE
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) v

def FormTranspC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ g ∈ X.SinfU u, ∀ g' ∈ X.SinfU u',
      s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ →
      Formalism.L2.SG.TermOp.OOt s.1 = ((vR s.1.toTerm : ℝ) : ℂ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
         Formalism.L2.SG.TermOp.OO
          ((νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).map (fun x => g * x))
          Set.univ (X.Wu u) (X.Wu u') s.1.pt.1)

def PhaseTieC : Prop :=
  ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (ρ : ℕ) (s : LiftT X Y u u' κ R ρ), s.1.relevant →
    ∀ g ∈ X.SinfU u, ∀ g' ∈ X.SinfU u',
      s.1.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * g'⁻¹ →
      Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.1.lam) : X.B.I.Gf)
                ((Y.cs u').h ((Y.cs u').base s.1.lam') : X.B.I.Gf) s.1.pt) *
        (X.psiInfU u g * conj (X.psiInfU u' g')) =
        Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)

theorem normalFormC_of (h1 : LiftAtSomeC X Y u u' κ)
    (h2 : Formalism.L2.SG.PairVal.CellPtUnique D u u' (X.Fu u) (Y.what₂ u))
    (h3 : LiftDecompC X Y u u' κ) (h4 : DFrameAtS X u u' i0 i0' 1) (h4' : LiftGPosC X Y u u' κ)
    (h5 : FormTranspC X Y u u' vR νq κ) (h6 : PhaseTieC X Y u u' κ) :
    NormalFormC X Y u u' vR i0 i0' νq κ := by
  classical
  haveI := FiniteDimensional.complete ℂ (X.Vpi u)
  haveI := FiniteDimensional.complete ℂ (X.Vpi u')
  intro R ρ s hs
  obtain ⟨⟨γ0, hγ0⟩, g, hg, g', hg', hpt⟩ := h3 R ρ s hs
  obtain ⟨w0, hw0⟩ := h1 R ρ s hs
  have hex : ∃ w, s.1.toTerm.atPt w ∧ s.1.toTerm.relevant := ⟨w0, hw0, hs⟩
  have hptOf : Formalism.L2.SG.PairVal.ptOf s.1.toTerm = w0 := by
    have e : Formalism.L2.SG.PairVal.ptOf s.1.toTerm = hex.choose := by
      unfold Formalism.L2.SG.PairVal.ptOf
      rw [dif_pos hex]
    rw [e]
    exact h2 _ _ _ hex.choose_spec.1 hw0
  have hex1 : ∃ w, s.1.toTerm.atPt w := ⟨w0, hw0⟩
  have hc : Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm =
      Formalism.L2.SG.PairVal.phaseAt s.1.toTerm (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) * (vR s.1.toTerm : ℂ) := by
    unfold Formalism.L2.SG.PairVal.cTerm
    rw [dif_pos hex1]
    unfold Formalism.L2.SG.PairVal.cAt
    rw [hptOf, h2 _ _ _ hex1.choose_spec hw0]
  have hexF : ∃ p : X.B.I.Ginf × X.B.I.Ginf, Formalism.L2.SG.RealObj.IsDFrameX X u u' 1 i0 i0'
      (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) p.1 p.2 := by
    obtain ⟨h, h', hh⟩ := h4 one_pos _ ⟨γ0, hγ0⟩ (h4' R ρ s hs)
    exact ⟨(h, h'), hh⟩
  have hS := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u hexF.choose_spec.1
  have hS' := Formalism.L2.SG.RealObj.InfCut.hsetU_sub X u' hexF.choose_spec.2.1
  have hV : Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative X u u' 1 i0 i0' νq (Formalism.L2.SG.PairVal.ptOf s.1.toTerm) =
      ((Formalism.L2.SG.RealObj.InfCut.piIso X u hexF.choose.1 hS).symm.toContinuousLinearEquiv :
          X.Vpi u →L[ℂ] X.Vpi u).comp
        ((Formalism.L2.SG.TermOp.OO (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)))
          Set.univ (X.Wu u) (X.Wu u')
          (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm))).comp
          ((Formalism.L2.SG.RealObj.InfCut.piIso X u' hexF.choose.2 hS').toContinuousLinearEquiv :
            X.Vpi u' →L[ℂ] X.Vpi u')) := by
    rw [Formalism.L2.SG.RealObj.InfCut.piIso_symm, Formalism.L2.SG.RealObj.InfCut.piIso_coe]
    unfold Formalism.L2.SG.RealObj.unscaledOperatorAtPointRepresentative
    rw [if_pos ⟨γ0, hγ0⟩]
    unfold Formalism.L2.SG.RealObj.unscaledFrameConjugatedOperator
    rw [dif_pos hexF]
  refine ⟨(Formalism.L2.SG.RealObj.InfCut.piIso X u hexF.choose.1 hS).trans
      (Formalism.L2.SG.RealObj.InfCut.piIso X u g hg),
    (Formalism.L2.SG.RealObj.InfCut.piIso X u' hexF.choose.2 hS').trans
      (Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg'), ?_⟩
  have hA : ∀ x, X.Wu u (g * x) =
      X.psiInfU u g • Formalism.L2.SG.RealObj.InfCut.piIso X u g hg (X.Wu u x) := by
    intro x
    rw [Formalism.L2.SG.RealObj.InfCut.piIso_apply]
    exact (X.Wu_spec u).1 g hg x
  have hB : ∀ x, X.Wu u' (g' * x) =
      X.psiInfU u' g' • Formalism.L2.SG.RealObj.InfCut.piIso X u' g' hg' (X.Wu u' x) := by
    intro x
    rw [Formalism.L2.SG.RealObj.InfCut.piIso_apply]
    exact (X.Wu_spec u').1 g' hg' x
  have hO := ClassFrameNormal.oo_map_mulLeft
    (νq (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)))
    (X.Wu u) (X.Wu u') (Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf s.1.toTerm)) g g'
    (X.psiInfU u g) (X.psiInfU u' g') _ _ hA hB
  have hph := h6 R ρ s hs g hg g' hg' hpt
  unfold chiOO frameVal
  rw [h5 R ρ s hs g hg g' hg' hpt, hc, hV, hpt, hO, ← hph]
  ext ξ
  simp [smul_smul, LinearIsometryEquiv.trans_apply]
  try ring_nf

end Formalism.L2.SG.Pf.RowForm
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CplxNF
section
noncomputable section

open scoped Classical InnerProductSpace
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals Formalism.MainNotions.BridgeLemma

namespace PI.SchurPlaces

open Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nfRat : NFRat := by
  intro D X u u' Λ Λ' q hrel hG
  obtain ⟨σ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  have hpos : ∀ w : D.what₂.Word, 0 < (σ ((Tu D w : ℕ) : D.host.E)).re := by
    intro w
    rw [map_natCast, Complex.natCast_re]
    exact_mod_cast tie_Tu_pos D w
  obtain ⟨j, hj, c, hN⟩ := Formalism.HermitianLatticeCounting.Final.S6.normalForm D.host.E (VS D).V σ (nfH (VS D)) D.R.rS
    (nfF (lf D (X.Fu u)).fl (nf_T_ne D u)) (nfF (frq X q).fl (nf_T_ne D u')) (fun x => p_starConj D σ x)
    (hpos u) (hpos u') (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u) _) σ)
    (nf_pos _ _ (p_posX D _ (tie_Tu_pos D u') _) σ)
    (nf_rel D.host.F (tie_trace D.sp.cm) _ _ _ _ hrel) ((nf_G _ _ _ _).trans hG)
  obtain ⟨-, -, -, -, ⟨h1, h2⟩, ⟨-, h3⟩⟩ := nf_gen _ _ _ _ j hj c hN
  exact ⟨h1, h2, h3⟩

theorem cplxNF : CplxNF := cplxNF_of nfRat

end PI.SchurPlaces
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Attr

variable {D : D7} {X : HidaSetting D}

abbrev GTu (Y : Full X) (u : D.what₂.Word) : Type :=
  GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)

def jT {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) : ℕ :=
  D.R.rS - Module.finrank D.host.E (Isp (lf D (X.Fu u)).fl (frq X t.rep).fl)

def labT {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) : ℕ → D.host.E :=
  fun l => if l ≤ jT t then Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l else 0

def relSet (Y : Full X) (u : D.what₂.Word) : Set (GTu Y u) := (Y.tO u u).degSet ∩ {t | t.relevant}

def massC (Y : Full X) (u : D.what₂.Word) : ℝ := massRows D (X.Fu u) (Y.what₂ u)

def dpiC (X : HidaSetting D) (u : D.what₂.Word) : ℝ := (Module.finrank ℂ (X.Vpi u) : ℝ)

def H1C (large₂ : SizeData₂ D) (CH : ℝ) : ℝ := large₂.sc.b ^ (CH * (D.R.m : ℝ))

end Attr

section Steps

def TypeAt {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (CH Cs C Ch Cp : ℝ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * massC Y u * ((k2a large₂ CH Cs C j' δ' * k2e large₂ CH Ch Cp j' δ') *
        (k2a large₂ CH Cs C j'' δ'' * k2e large₂ CH Ch Cp j'' δ''))

def IrrVecC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    ∀ t ∈ (Y.tO u u).degSet, ¬ t.relevant → (Y.tO u u).vec t = 0

def JPosC : Prop :=
  ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ t ∈ relSet Y u, 1 ≤ jT t

def TypeC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ CH Ch Cp : ℝ, 0 ≤ CH ∧ 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∀ Cs : ℝ, Cp + 4 ≤ Cs → ∃ C₀ : ℝ,
    ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
        TypeAt large₂ Y u CH Cs C Ch Cp

def DelC : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
      ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
        k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2

def CosetsC : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ Cc : ℝ, 0 ≤ Cc ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
      ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
        (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
        ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ))

def DimFormC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    0 ≤ (Y.tO u u).Gam1 ∧ (Y.tO u u).Gam1 * massC Y u * dpiC X u ≤ Formalism.L2.SG.RowsConc.duC X Y u

def PgLeC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.PgC Y ≤ 2

end Steps

end Formalism.L2.SG.KappaOffDiagonal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GoodFamilyMassFormula
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.GoodFamilyMass

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

def StepDataOne (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d d' : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d' t' → Datum.Rel d d'

def StepDataMove (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d d' : Datum P), Datum.Rel d d' → (∃ t : Term V M r, IsTermOver P d' t) →
          ∃ t : Term V M r, IsTermOver P d t

def StepTermOne (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d : Datum P) (t t' : Term V M r), IsTermOver P d t → IsTermOver P d t' → TRel P t t'

def StepMuPos (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → 0 < mu P t

def StepWtPos (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo →
        ∀ (d0 d : Datum P) (t : Term V M r), IsTermOver P d t → 0 < Datum.wt d0 d

def GoodFamilyMassFormula (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → P.PrimeTo → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) →
        ∀ (R : Reps P) (d0 : Datum P), 0 < nn R d0 ∧ nn R d0 ≠ ⊤

section Idx

variable {G : Type*} [Group G]

end Idx

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

end Formalism.L2.SG.GoodFamilyMass
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IndexEqRelIndex
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

theorem index_eq_relIndex (hD : Data W S N' K π) :
    ((Hk W K g).map (πk W S N' K π hD)).index = ((Hs W K g).map π).relIndex (K ⊓ S) := by
  let e : ↥(K ⊓ S) →* ↥(Ak S K) :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by simp only [Ak, Subgroup.mem_subgroupOf]; exact x.2.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have he : Function.Surjective e := fun a =>
    ⟨⟨a.1.1, a.1.2, by have h := a.2; simp only [Ak, Subgroup.mem_subgroupOf] at h; exact h⟩, rfl⟩
  rw [← Subgroup.index_comap_of_surjective _ he]
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, hkx⟩
    refine ⟨k.1, ?_, ?_⟩
    · simpa [Hk, Subgroup.mem_subgroupOf] using hk
    · have h2 := congrArg (fun y : ↥(Ak S K) => ((y : ↥K) : G)) hkx
      simpa [πk, e] using h2
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨y, hy.1⟩, ?_, ?_⟩
    · simpa [Hk, Subgroup.mem_subgroupOf] using hy
    · apply Subtype.ext
      apply Subtype.ext
      simpa [πk, e] using hyx

theorem card_cells' (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hs W K g).map π).relIndex (K ⊓ S) := (card_cells W S N' K π g hD).trans (index_eq_relIndex W S N' K π g hD)

end Formalism.L2.SG.Pf.CountAb
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ShiftCore
section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.CovariantRepresentation

theorem shiftCore : ShiftCore := by
  intro G _ _ _ _ _ _ μ _ _ R Γ _ V _ _ f Ω h ν _ hΓR hK hn hσ hne hcon hfin hleft hinv hconj hf hΩ hfi
  by_cases hV : CompleteSpace V
  · exact Formalism.L2.SG.MeasureShiftInvariance.shift_general μ R Γ f Ω h ν hΓR hK hn hσ hne hcon hfin hleft hinv hconj
      hf hΩ hfi
  · rw [integral_of_not_completeSpace hV, integral_of_not_completeSpace hV]

end Formalism.L2.SG.CovariantRepresentation
end
end

