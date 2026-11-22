import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinkUnique
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.UG NumberField IsDedekindDomain Matrix Formalism.L2.SG.HidaSetting Formalism.L2.SG.ColDict
open Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct

namespace GlobalTheory.St.G.LinkCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
  (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)

theorem mem_Mq (x : Fin (D.R.N 0) → D.host.E) : x ∈ Mq wt ↔ (∑ j, x j • qFr wt j) ∈ (VS D).L0 := by
  simp [Mq, Fintype.linearCombination_apply]

theorem embA_add (x y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (x + y) = embA X wt ιA x + embA X wt ιA y := by
  simp [embA, add_smul, Finset.sum_add_distrib]

theorem embA_smul (a : D.host.E ⊗[D.host.F] Ad D.host.F) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    embA X wt ιA (a • x) = ιA.symm a • embA X wt ιA x := by
  simp [embA, Finset.smul_sum, mul_smul]

theorem embA_rep (h : X.B.I.Gf)
    (y : UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
    (hr : RepF X wt ιA h y) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    X.B.I.fmat h *ᵥ embA X wt ιA x = embA X wt ιA (y.1.1 *ᵥ x) := by
  unfold embA
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, hr _, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : ∀ f : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F, ιA.symm (∑ j, f j) = ∑ j, ιA.symm (f j) :=
    fun f => map_sum ιA.symm.toAddEquiv.toAddMonoidHom f Finset.univ
  simp only [Matrix.mulVec, dotProduct, hs, RingEquiv.map_mul, Finset.sum_smul, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem embA_rat (hι : GlobalTheory.St.IsAdeleIso X ιA) (x : Fin (D.R.N 0) → D.host.E) :
    embA X wt ιA (fun j => inclE (F := D.host.F) (Ad D.host.F) (x j)) =
      incl X.B.I (X.crd (∑ j, x j • qFr wt j)) := by
  have h1 : ∀ a : D.host.E, ιA.symm (inclE (F := D.host.F) (Ad D.host.F) a) =
      inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm a) := by
    intro a
    rw [RingEquiv.symm_apply_eq, hι.1, RingEquiv.apply_symm_apply]
  funext i
  simp [embA, qA, incl, HidaSetting.crd, crdOf, h1, Finset.sum_apply]

theorem embA_mem (hι : GlobalTheory.St.IsAdeleIso X ιA) (x : Fin (D.R.N 0) → D.host.E) (hx : x ∈ Mq wt) :
    embA X wt ιA (fun j => inclE (F := D.host.F) (Ad D.host.F) (x j)) ∈ X.B.I.Lf := by
  rw [embA_rat X wt ιA hι]
  have hL : X.crd (∑ j, x j • qFr wt j) ∈ X.B.I.L := by
    rw [X.L_eq]
    simp only [HidaSetting.crd, crdOf, RingEquiv.apply_symm_apply, Module.Basis.sum_repr]
    exact (mem_Mq wt x).1 hx
  exact Submodule.subset_span ⟨⟨_, hL⟩, rfl⟩

theorem link_unique (u : D.what₂.Word) (Fr Fr' : FrQ D wt) (h : FrLink X u wt ιA Fr) (h' : FrLink X u wt ιA Fr') :
    Fr.eps = Fr'.eps ∧ Fr.psi = Fr'.psi ∧
      (∀ i, embA X wt ιA (Fr.b i) - embA X wt ιA (Fr'.b i) ∈ mL X.B.I X.B.g) ∧
      ∀ i, embA X wt ιA (Fr.bd i) - embA X wt ιA (Fr'.bd i) ∈ mL X.B.I X.B.g := by
  refine ⟨h.1.trans h'.1.symm, funext fun a => (h.2.2.2 a).trans (h'.2.2.2 a).symm, fun i => ?_, fun i => ?_⟩
  · simpa using (mL X.B.I X.B.g).sub_mem (h.2.1 i) (h'.2.1 i)
  · simpa using (mL X.B.I X.B.g).sub_mem (h.2.2.1 i) (h'.2.2.1 i)

theorem level_rank : X.B.g = D.host.g 0 * D.host.g 1 ∧ D.R.N 0 = D.R.k :=
  ⟨X.g_eq, by simp [Ranks.N]⟩

end GlobalTheory.St.G.LinkCheck

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocOf
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ampQ {Cl Nu : Type} (Q : Prop → Prop) (L : PN.LocalNG Cl Nu) (d : ∀ p, L.D p) : ℂ :=
  haveI := L.fP
  ∑ A ∈ L.Om.powerset.filter (fun A => Q A.Nonempty), ∏ p, (if p ∈ A then L.aN p (d p) else L.aZ p (d p))

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)

def setQ (Q : Prop → Prop) : Set (TauC Y u u') := {t | (Y.tO u u').G t ≠ 0 ∧ Q (¬ (Y.tO u u').gener t)}

def FamQ {Cl : Type} (Q : Prop → Prop) (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) : Prop :=
  TS = setQ Y u u' Q ∧ GlobalTheory.Unfold.ClsRow TS cls ∧
    ∀ t ∈ TS, ∀ t' ∈ TS, cls t = cls t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t'

def HasPt (TS : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS) : Prop :=
  ∃ t ∈ TS, (Y.tO u u').vec t ≠ 0 ∧ ptPN t = γ

def grpF {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (c : Cl) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) :=
  ∑' t : TauC Y u u', (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = ν}).indicator (Y.tO u u').vec t

def a2F {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (c : Cl) (γ : PN.Pts D.host.E D.R.rS) (ν : NuC D) : ℝ :=
  ‖grpF Y u u' TS cls c γ ν‖ ^ 2 / J2of Y u u' νq γ

def gCls (t : TauC Y u u') : Set (TauC Y u u') :=
  {t' | t' ∈ (Y.tO u u').genSet ∧ (Y.tO u u').rowOf t' = (Y.tO u u').rowOf t ∧ (Y.tO u u').s0 t t' = 1 ∧
    (Y.tO u u').scal t t'}

def locOf (t : TauC Y u u') (p : PlF D) : Loc.Term (Vp D p) (Y.M p) D.R.rS :=
  GlobalTheory.LocOver.locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')

def Dfc (t : TauC Y u u') : Set (PlF D) :=
  {p | LocNG.BBne (H := locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) (locOf Y u u' t p)}

end GlobalTheory.SnFam
end
end

