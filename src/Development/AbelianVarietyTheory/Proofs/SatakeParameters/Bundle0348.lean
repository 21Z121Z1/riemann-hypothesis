import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0345
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0022
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0712
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepSucc
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 2000000 in

theorem Joint.pt_succ_isPt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), J.IsPt std (j + 1) hj La (J.pt std (j + 1) hj La) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) (J.pt std (j + 1) hj La).1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La
  have hG := (H.core j hj ((I.at' j hj).st.eC.symm La.1).1).good
  obtain ⟨x0, hx0⟩ := exists_unitary_pt hG ((I.at' j hj).st.eC.symm La.1).2
    (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2)
  have hspec := Classical.epsilon_spec (p := fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
    (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) x ∧
    x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ⟨x0, hx0⟩
  have hy : (J.cp std).y (j + 1) La = Formalism.L2.PairingIndexBounds.F.reGL (finCongr ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm)
      (Classical.epsilon fun x => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2
        (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om (j + 1) La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D (j + 1) hj) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    show (chAt _ _ _ _ _ _ _ _ _ I _ _ _ _ (j + 1) La).y = _
    simp only [chAt, dif_pos hj]
  have hre : ∀ {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (y : GL (Fin m) R), Formalism.L2.PairingIndexBounds.F.reGL (finCongr h.symm) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y) = y := by
    intro R _ m n h y
    subst h
    ext a b
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  have key : ∃ x, J.IsPt std (j + 1) hj La x :=
    ⟨⟨_, hspec.2⟩, ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk, by
      rw [hy]
      exact (hre ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk.symm _).symm⟩
  have hpt : J.IsPt std (j + 1) hj La (J.pt std (j + 1) hj La) := Classical.epsilon_spec key
  refine ⟨hpt, ?_⟩
  obtain ⟨hr, hx⟩ := hpt
  rw [hx, hy, hre]
  exact hspec.1

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleAdelicPointStepZero
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TwV.Joint.isPt_pt_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), J.IsPt std 0 (Nat.zero_le _) La (J.pt std 0 (Nat.zero_le _) La) ∧ (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) (J.pt std 0 (Nat.zero_le _) La).1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La
  have hr := (lev0At J.Gd u w hg).A.rk
  obtain ⟨x0, hx0⟩ := GlobalTheory.TwU.exists_unitary_pt J.one.good La.1
    (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
      (sysS H X std).dG_spec (sysS H X std).om 0 La.2)
  have hs := Classical.epsilon_spec (p := fun x => (lev0At J.Gd u w hg).A.IsPt La.1
      (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
        (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧ x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ⟨x0, hx0⟩
  have hex : ∃ x, J.IsPt std 0 (Nat.zero_le _) La x := by
    refine ⟨⟨_, hs.2⟩, hr, ?_⟩
    ext i j
    rfl
  have hp := Classical.epsilon_spec hex
  obtain ⟨hr', he⟩ := hp
  refine ⟨⟨hr', he⟩, ?_⟩
  have h1 : (J.pt std 0 (Nat.zero_le _) La).1 = Classical.epsilon (fun x => (lev0At J.Gd u w hg).A.IsPt La.1
      (basesAt (chainAt H hT) std (sysS H X std).vp (sysS H X std).unif (sysS H X std).eO (sysS H X std).eO_spec (sysS H X std).dG
        (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧ x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [show (J.pt std 0 (Nat.zero_le _) La).1 = _ from he]
    ext i j
    rfl
  rw [h1]
  exact hs.1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleBasesSpanAtPlaces
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TwV.Joint.basesAt_span : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → ∀ v, (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) ((basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om j La.2) v : Matrix _ _ ((sysS H X std).G.P.Qq v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j La hLa v
  obtain ⟨g, hdet, hg'⟩ := Formalism.L2.G.Pend.latAt_isLattice (sysS H X std) j La.2 hLa v
  have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 hdet
  unfold basesAt
  exact Classical.epsilon_spec (p := fun g' : GL (Fin (((sysS H X std).Pj j).m + 1)) ((sysS H X std).G.P.Qq v) =>
      (sysS H X std).latAt v j La.2 = colSpan ((sysS H X std).G.P.W v) (g' : Matrix _ _ _)) ⟨hu.unit, by rw [hu.unit_spec]; exact hg'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChart
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.TwV.ChartSucc

theorem castSt_ofStepIn_chart {D : D7} {u : D.what₂.Word} {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (h : C = C') {i : ℕ} {hi : i ≤ D.R.m}
    {A : ColumnsAtT D.R C} {P : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P}
    {p : ℕ} {G : GAtP p} (S : StepIn M i hi G) (St : GlobalTheory.TwU.StepCharts C' i hi) (hSt : St = castSt h (GlobalTheory.TwU.StepCharts.ofStepIn S))
    (c : C.cls i) (c' : C'.cls i) (hc' : c' = castCls h i c) (β : S.Ch) (hβ : S.chOf c = β) :
    St.T = S.T ∧ (St.K (St.chOf c')).lev.Lb = (S.K β).lev.Lb ∧ (St.K (St.chOf c')).lev.U = (S.K β).lev.U ∧
      (St.K (St.chOf c')).lev.Uloc = (S.K β).lev.Uloc ∧ ∀ hc : S.chOf c = β, St.y c' = (S.K β).y ⟨c, hc⟩ := by
  subst hSt hc' h hβ
  exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

end GlobalTheory.TwV.ChartSucc

theorem GlobalTheory.TwV.chart_succ_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → (I.at' j hj).st.T = (D.mem u).A.T ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Uloc = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Uloc ∧ ∀ hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1, (J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2) = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  have hc := clsOf_chart (S := (I.at' j hj).st) (H.core j hj) La.1 La.2 hLa
  obtain ⟨hT', hLb, hU, hUl, hy⟩ := GlobalTheory.TwV.ChartSucc.castSt_ofStepIn_chart (X.onCh j hj) (I.at' j hj).st (J.St (j + 1) hj) (J.st j hj)
    _ (clsAt X H (j + 1) La.1 La.2) (clsAt_succ X H j hj La.1 La.2) _ hc
  refine ⟨hT'.symm.trans (J.tie.T_eq (j + 1) hj), hLb, hU, hUl, hy⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleDetEqAdelicPointDet
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

set_option maxHeartbeats 2000000 in

theorem joint_dt_eq_det_of_isPt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) x, J.IsPt std j hj La x → (J.fd std).dt j La = Matrix.GeneralLinearGroup.det x.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La x hx
  obtain ⟨hr, hx⟩ := hx
  have h1 : (J.fd std).dt j La = Matrix.GeneralLinearGroup.det ((J.cp std).y j La) := rfl
  rw [h1, hx]
  exact ((reindex_rename_point_det_latK D.sp hr 0 0 ((J.cp std).y j La) ⊥).2.1).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LimWUOfSeeds
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL

theorem overPl_unique {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (τ : E →+* ℂ)
    {w u : HeightOneSpectrum (𝓞 E)} (hw : OverPl ι τ w) (hu : OverPl ι τ u) : u = w := by
  by_contra hne
  have hI : u.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have htop : u.asIdeal ⊔ w.asIdeal = ⊤ := Ideal.IsMaximal.coprime_of_ne u.isMaximal w.isMaximal hI
  have h1 : (1 : 𝓞 E) ∈ u.asIdeal ⊔ w.asIdeal := htop ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  have hx' := hu x hx
  have hy' := hw y hy
  have hsum : ι.symm (τ ((x : E))) + ι.symm (τ ((y : E))) = 1 := by
    rw [← map_add, ← map_add]
    have : ((x : E) + (y : E)) = 1 := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hxy
    rw [this, map_one, map_one]
  have hle := IsUltrametricDist.norm_add_le_max (ι.symm (τ ((x : E)))) (ι.symm (τ ((y : E))))
  rw [hsum, norm_one] at hle
  exact absurd hle (not_le.mpr (max_lt hx' hy'))

end GlobalTheory.CongL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocSpLatAdIsPt
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.SpanPt

theorem colSpan_map {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (M X : Matrix (Fin k) (Fin k) K) :
    (colSpan R X).map ((M.mulVecLin).restrictScalars R) = colSpan R (M * X) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1

set_option maxHeartbeats 400000 in

theorem locSp_latAd_isPt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)), LatAdLoc A Lb → LbAtB A Lb → ∀ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))), A.IsPt i g y → ∀ v, locSp (G.P.W v) (A.iw v) (latAd y Lb) = colSpan (G.P.W v) (((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin n) (Fin n) (G.P.Qq v))) := by
  intro F E _ _ _ _ _ n p G A Lb hA hB i g y hy v
  rw [hA y v, hB v, colSpan_map, GlobalTheory.TwV.FacQPt.facQ_isPt A i g y hy v]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Units.val_mul (bc (A.iw v) A.B)⁻¹, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end GlobalTheory.TwV.SpanPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelPartition_size_extension_firstLast_rows : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → NuIs X D pos j (extNu (D.R.N (j + 1)) ν) ∧ (∀ τ, szT X D pos j τ = ∑ r, (ν τ r : ℤ)) ∧ (∀ τ, szT X D pos j τ = ∑ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ)) ∧ (∀ τ r, (extNu (D.R.N (j + 1)) ν τ r : ℤ) ≤ cT1 X D pos j τ) ∧ ∀ τ, 0 ≤ X.nuv (pos.symm τ).1 (j + 1) (pos.symm τ).2 (NN X.G.P.m X.t j) := by
  first | exact @GlobalTheory.TwV.DelA.size_first_last_rows | exact GlobalTheory.TwV.DelA.size_first_last_rows | (intros; apply GlobalTheory.TwV.DelA.size_first_last_rows <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedPairDatumEqAdelicDatum
section
noncomputable section

namespace GlobalTheory.TwV

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inFr_symm_inFr_cancel {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a)
    (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (z : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' z) = z := by
  refine LinearMap.ext fun x => ?_
  simp [Formalism.L2.Col.inFr]

set_option maxHeartbeats 2000000 in

theorem moved_pair_datum_eq_adelic_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (Xi : AdDatum J.St) j (hj : j + 1 ≤ D.R.m) (h1 : ((sysS H X std).Pj j).m + 1 = D.R.N j) (h2 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, xiM (sysS H X std) (J.fd std) (J.xi0 std Xi) j La La' z = Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J Xi j hj h1 h2 La La' z
  unfold GlobalTheory.TwU.xiM Formalism.L2.PairingIndexBounds.F.movD Joint.xi0
  rw [dif_pos ⟨hj, h1, h2⟩, inFr_symm_inFr_cancel]

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NaturalActionInverseFrameUndoesMoveStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.naturalAction_inverseFrame_undoes_move : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (j : ℕ) (La : X.Lt j) (G : (X.Pj j).Xsp), (X.Pj j).natAct (glInv X j (BOf fd j La)) (gmOf fd j La G) = G := by
  first | exact @GlobalTheory.TwV.DelA.natAct_glInv_gmOf | exact GlobalTheory.TwV.DelA.natAct_glInv_gmOf | (intros; apply GlobalTheory.TwV.DelA.natAct_glInv_gmOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OddTwistedFrameDetFunctionMulDetPowPolynomial
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

open Formalism.L2.KerInert.SharpPolyP

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

def zA {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  if IsOddPos (pos.symm τ).2 then (f τ).adjugate.transpose.submatrix id Fin.rev else f τ

def adjPol {n : ℕ} (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) : MvPolynomial (GL3Theta.FrV D n) ℂ :=
  MvPolynomial.aeval (fun k : GL3Theta.FrV D n => if IsOddPos (pos.symm k.1).2 then
    (Matrix.of fun a b : Fin n => (MvPolynomial.X (k.1, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)).adjugate (Fin.rev k.2.2) k.2.1
    else MvPolynomial.X k) Q

theorem eval_adj {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (i j : Fin n) :
    MvPolynomial.eval (pt x) ((Matrix.of fun a b : Fin n => (MvPolynomial.X (τ, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)).adjugate i j)
      = (x τ).adjugate i j := by
  have h := congrArg (fun M => M i j) (RingHom.map_adjugate (MvPolynomial.eval (pt x))
    (Matrix.of fun a b : Fin n => (MvPolynomial.X (τ, a, b) : MvPolynomial (GL3Theta.FrV D n) ℂ)))
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h
  rw [h]
  congr 1
  ext a b
  simp

theorem eval_adjPol {n : ℕ} (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (pt x) (adjPol X D pos Q) = MvPolynomial.eval (pt (zA X D pos x)) Q := by
  unfold adjPol
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X q k hq =>
    rw [map_mul, map_mul, hq, map_mul]
    congr 1
    rw [MvPolynomial.aeval_X, MvPolynomial.eval_X]
    show _ = zA X D pos x k.1 k.2.1 k.2.2
    unfold zA
    split_ifs with h
    · rw [eval_adj]; rfl
    · rw [MvPolynomial.eval_X]

def dg {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun _ => if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1

theorem zT_eq_mul {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos x = fun τ => zA X D pos x τ * dg X D pos x τ := by
  funext τ
  unfold zT zA dg
  split_ifs with h
  · ext i j
    simp [Matrix.mul_diagonal, Matrix.inv_def, Ring.inverse_eq_inv', mul_comm]
  · simp

theorem dg_bor {n : ℕ} (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hx : ∀ τ, (x τ).det ≠ 0) :
    IsBor (dg X D pos x) := by
  intro τ
  refine ⟨fun r s hsr => ?_, fun r => ?_⟩
  · unfold dg
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hsr)
  · unfold dg
    rw [Matrix.diagonal_apply_eq]
    split_ifs
    · exact inv_ne_zero (hx τ)
    · exact one_ne_zero

theorem eval_zT {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (Q : MvPolynomial (GL3Theta.FrV D n) ℂ) (hQ : Q ∈ WtPol ℂ ν)
    (x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hx : ∀ τ, (x τ).det ≠ 0) :
    MvPolynomial.eval (pt (zT X D pos x)) Q =
      (∏ τ, ∏ r, (if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1) ^ ν τ r) *
        MvPolynomial.eval (pt x) (adjPol X D pos Q) := by
  rw [eval_adjPol, zT_eq_mul, ← sp_eval_colSub (dg X D pos x) (zA X D pos x) Q, hQ _ (dg_bor X D pos x hx),
    MvPolynomial.smul_eval]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun r _ => ?_
  unfold dg
  rw [Matrix.diagonal_apply_eq]

theorem twF_mul_det_poly : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ}, 0 < n → ∀ (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ (K : D.what₂.Tau → ℕ) (P : MvPolynomial (GL3Theta.FrV D n) ℂ), ∀ x : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (x τ).det ≠ 0) → MvPolynomial.eval (fun k : GL3Theta.FrV D n => x k.1 k.2.1 k.2.2) P = twF X D pos c Q x * ∏ τ, (x τ).det ^ K τ := by
  intro p _ X D pos n hn ν c hc Q hQ
  have hc0 : ∀ τ, 0 ≤ c τ := fun τ => le_trans (Int.natCast_nonneg _) (hc τ ⟨0, hn⟩)
  refine ⟨fun τ => if IsOddPos (pos.symm τ).2 then ∑ r, ν τ r else 0,
    (∏ τ, if IsOddPos (pos.symm τ).2 then
        MvPolynomial.C ((sgRev n ^ (c τ).toNat)⁻¹) * frDet ℂ n τ ^ (c τ).toNat else 1) * adjPol X D pos Q, ?_⟩
  intro x hx
  change MvPolynomial.eval (pt x) _ = _
  have key : ∀ τ, MvPolynomial.eval (pt x) (if IsOddPos (pos.symm τ).2 then
        MvPolynomial.C ((sgRev n ^ (c τ).toNat)⁻¹) * frDet ℂ n τ ^ (c τ).toNat else 1) =
      (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ).det ^ (-(c τ)) else 1) *
        (∏ r, (if IsOddPos (pos.symm τ).2 then ((x τ).det)⁻¹ else 1) ^ ν τ r) *
        (x τ).det ^ (if IsOddPos (pos.symm τ).2 then ∑ r, ν τ r else 0) := by
    intro τ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, c τ = m := ⟨(c τ).toNat, (Int.toNat_of_nonneg (hc0 τ)).symm⟩
    have hd := hx τ
    rw [det_zT]
    split_ifs with h
    · rw [map_mul, map_pow, MvPolynomial.eval_C, sp_eval_frDet, hm, Int.toNat_natCast, zpow_neg, zpow_natCast,
        Finset.prod_pow_eq_pow_sum, mul_assoc, ← mul_pow, inv_mul_cancel₀ hd, one_pow, mul_one, mul_pow, mul_inv,
        inv_pow, inv_inv]
    · simp
  unfold twF
  rw [map_mul, map_prod, Finset.prod_congr rfl (fun τ _ => key τ), Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  change _ = _ * MvPolynomial.eval (pt (zT X D pos x)) Q * _
  rw [eval_zT X D pos ν Q hQ x hx]
  ring

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OddTwistedFrameDetFunctionMulUpperTriangular
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem upper_inv_diag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hU : ∀ r s, s < r → M r s = 0) (hd : ∀ r, M r r ≠ 0) :
    (∀ r s, s < r → M⁻¹ r s = 0) ∧ ∀ r, M⁻¹ r r = (M r r)⁻¹ := by
  classical
  have hB : Matrix.BlockTriangular M id := fun i j h => hU i j h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular hB]
    exact Finset.prod_ne_zero_iff.2 fun r _ => hd r
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  letI := M.invertibleOfIsUnitDet hunit
  have hBi : Matrix.BlockTriangular M⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨fun r s h => hBi h, fun i => ?_⟩
  have h := congrFun (congrFun (Matrix.mul_nonsing_inv M hunit) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
  rw [Finset.sum_eq_single i] at h
  · exact eq_inv_of_mul_eq_one_right h
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hU i k hk, zero_mul]
    · rw [hBi hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem zT_mul {n : ℕ} (x β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    zT X D pos (fun τ => x τ * β τ) = fun τ => zT X D pos x τ *
      (if IsOddPos (pos.symm τ).2 then ((β τ)⁻¹).transpose.submatrix Fin.rev Fin.rev else β τ) := by
  funext τ
  unfold zT
  split_ifs with h
  · rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
    exact (Equiv.sum_comp Fin.revPerm (fun k => ((x τ)⁻¹).transpose i k * ((β τ)⁻¹).transpose k (Fin.rev j))).symm
  · rfl

theorem prod_inv_rev_zpow_mul_prod_pow_eq_odd_position {n : ℕ} (b : Fin n → ℂ) (hb : ∀ r, b r ≠ 0) (c : ℤ) (ν : Fin n → ℕ) (h : ∀ r, (ν r : ℤ) ≤ c) :
    (∏ r, (b (Fin.rev r))⁻¹) ^ (-c) * ∏ r, (b (Fin.rev r))⁻¹ ^ ν r = ∏ r, b r ^ (c - (ν (Fin.rev r) : ℤ)).toNat := by
  rw [← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  rw [← Equiv.prod_comp Fin.revPerm (fun r => b r ^ (c - (ν (Fin.rev r) : ℤ)).toNat)]
  refine Finset.prod_congr rfl fun r _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev]
  have e : b (Fin.rev r) ^ (c - (ν r : ℤ)).toNat = b (Fin.rev r) ^ (c - (ν r : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by linarith [h r])]
  rw [e, inv_zpow', neg_neg, inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (hb _)]
  congr 1

theorem twF_mul_bor : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) {n : ℕ} (ν : D.what₂.Tau → Fin n → ℕ) (c : D.what₂.Tau → ℤ), (∀ τ r, (ν τ r : ℤ) ≤ c τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∀ (x β : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (x τ).det ≠ 0) → IsBor β → twF X D pos c Q (fun τ => x τ * β τ) = (∏ τ, ∏ r, β τ r r ^ (if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)) * twF X D pos c Q x := by
  intro p _ X D pos n ν c hνc Q hQ x β _hx hβ
  classical
  have hbd : ∀ τ r, β τ r r ≠ 0 := fun τ r => (hβ τ).2 r
  have hinv : ∀ τ, (∀ r s, s < r → ((β τ)⁻¹) r s = 0) ∧ ∀ r, ((β τ)⁻¹) r r = (β τ r r)⁻¹ :=
    fun τ => upper_inv_diag (β τ) (hβ τ).1 (hbd τ)
  let β' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ =>
    if IsOddPos (pos.symm τ).2 then ((β τ)⁻¹).transpose.submatrix Fin.rev Fin.rev else β τ
  have hd' : ∀ τ r, β' τ r r = if IsOddPos (pos.symm τ).2 then (β τ (Fin.rev r) (Fin.rev r))⁻¹ else β τ r r := by
    intro τ r
    simp only [β']
    split_ifs
    · simp [(hinv τ).2]
    · rfl
  have hB' : IsBor β' := by
    intro τ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp only [β']
      split_ifs
      · simp only [Matrix.submatrix_apply, Matrix.transpose_apply]
        exact (hinv τ).1 _ _ (Fin.rev_lt_rev.2 hsr)
      · exact (hβ τ).1 r s hsr
    · rw [hd']
      split_ifs
      · exact inv_ne_zero (hbd τ _)
      · exact hbd τ r
  have hz : zT X D pos (fun τ => x τ * β τ) = fun τ => zT X D pos x τ * β' τ := zT_mul X D pos x β
  have hev : GL3Theta.evFr D Q (fun τ => zT X D pos x τ * β' τ) =
      (∏ τ, ∏ r, β' τ r r ^ ν τ r) * GL3Theta.evFr D Q (zT X D pos x) := by
    have h1 := Formalism.L2.KerInert.SharpPolyP.sp_eval_colSub β' (zT X D pos x) Q
    rw [hQ β' hB', MvPolynomial.smul_eval] at h1
    exact h1.symm
  have key : ∀ τ, (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) * ∏ r, β' τ r r ^ ν τ r
      = (∏ r, β τ r r ^ (if IsOddPos (pos.symm τ).2 then (c τ - (ν τ (Fin.rev r) : ℤ)).toNat else ν τ r)) *
        (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ).det ^ (-(c τ)) else 1) := by
    intro τ
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [if_pos ho]
      rw [Matrix.det_mul, Formalism.L2.KerInert.SharpPolyP.sp_det_bor hB', mul_zpow]
      simp only [hd', if_pos ho]
      rw [← prod_inv_rev_zpow_mul_prod_pow_eq_odd_position (fun r => β τ r r) (hbd τ) (c τ) (ν τ) (hνc τ)]
      ring
    · simp only [if_neg ho, one_mul, mul_one, hd']
  unfold twF
  rw [hz, hev]
  calc (∏ τ, if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) *
        ((∏ τ, ∏ r, β' τ r r ^ ν τ r) * GL3Theta.evFr D Q (zT X D pos x))
      = (∏ τ, (if IsOddPos (pos.symm τ).2 then (zT X D pos x τ * β' τ).det ^ (-(c τ)) else 1) * ∏ r, β' τ r r ^ ν τ r) *
          GL3Theta.evFr D Q (zT X D pos x) := by rw [Finset.prod_mul_distrib]; ring
    _ = _ := by simp_rw [key]; rw [Finset.prod_mul_distrib]; ring

end GlobalTheory.TwV.DelA
end
end

