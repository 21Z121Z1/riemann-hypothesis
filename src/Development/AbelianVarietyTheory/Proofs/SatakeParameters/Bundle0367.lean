import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0363
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0361
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0358
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0360
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0062
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0364
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTuplePointDetNormOneOrderEqNegLength
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.PtOrd

theorem det_reGL' {R : Type} [CommRing R] {a b : ℕ} (e : Fin a ≃ Fin b) (x : GL (Fin a) R) :
    Matrix.GeneralLinearGroup.det (reGL e x) = Matrix.GeneralLinearGroup.det x := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_reindex_self e _

theorem det_bc' {A B : Type} [CommRing A] [CommRing B] {m : Type} [Fintype m] [DecidableEq m] (φ : A →+* B) (x : GL m A) :
    ((Matrix.GeneralLinearGroup.det (Formalism.UG.bc φ x) : Bˣ) : B) = φ ((Matrix.GeneralLinearGroup.det x : Aˣ) : A) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

theorem det_castGL' {a b : ℕ} (h : a = b) (R : Type) [CommRing R] (g : GL (Fin a) R) :
    ((Matrix.GeneralLinearGroup.det (castGL h R g) : Rˣ) : R) = ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) := by
  subst h
  simp [castGL, Matrix.GeneralLinearGroup.val_det_apply]

theorem phiA_det_eps {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n k p : ℕ} {G : GAtP p}
    (A : LocAt F E n G) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (S : Set (GL (Fin n) (AfE F E)))
    (hex : ∃ x, A.IsPt i g x ∧ x ∈ S) (e : Fin n ≃ Fin k) (v : Fin G.P.nV) :
    phiA A v ((Matrix.GeneralLinearGroup.det (reGL e (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ S)) : (AfE F E)ˣ) : AfE F E) =
      (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)).det := by
  rw [det_reGL']
  have hx := (Classical.epsilon_spec hex).1
  have h := congrArg (fun y => ((Matrix.GeneralLinearGroup.det y : _ˣ) : (A.pl v).1.adicCompletion F)) (hx.2 v)
  have e : ∀ (a b : ((A.pl v).1.adicCompletion F)ˣ), a * b * a⁻¹ = b := fun a b => by
    rw [mul_comm a b, mul_inv_cancel_right]
  simp only [map_mul, map_inv] at h
  rw [det_bc', det_bc'] at h
  have h2 : A.ph v (prV (E := E) (A.pl v).1 ((Matrix.GeneralLinearGroup.det (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ S) : _ˣ) : _)) =
      A.eQ v ((Matrix.GeneralLinearGroup.det (g v) : _ˣ) : _) := by
    rw [h, e, det_bc', det_castGL']
    rfl
  show (A.eQ v).symm (A.ph v (prV (E := E) (A.pl v).1 _)) = _
  rw [h2, RingEquiv.symm_apply_apply, Matrix.GeneralLinearGroup.val_det_apply]

end GlobalTheory.TwV.Xc.PtOrd

noncomputable section
namespace GlobalTheory.TwV.Xc.PtOrd

open Formalism.L2.KerInert.SecondKernelInstances

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  {n0 : ℕ} (A0 : LocAt D.host.F D.host.E n0 (D.gat u w h)) (J0 : Matrix (Fin n0) (Fin n0) D.host.E)
  (Lb0 : Submodule (𝓞 D.host.E) (Fin n0 → D.host.E))
  (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n0) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))

theorem latAt_bases (j : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).Tup) (hL : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).IsLatTup Lt) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v j Lt = colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) ((basesAt Ch std vp unif eO eO_spec dG dG_spec om j Lt v : GL _ _) : Matrix _ _ _) := by
  have hx : ∃ g : GL (Fin (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).m + 1)) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v), (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v j Lt = colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (g : Matrix _ _ _) := by
    cases j with
    | zero =>
      obtain ⟨g, hg, hLg⟩ := hL v
      exact ⟨Matrix.nonsingInvUnit g hg, hLg⟩
    | succ i =>
      obtain ⟨g, hg, hLg⟩ := hL v
      exact ⟨Matrix.nonsingInvUnit g hg, hLg⟩
  exact Classical.epsilon_spec hx

theorem len_bases (j : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).Tup) (hL : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj j).IsLatTup Lt) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    len (sysAt Ch std vp unif eO eO_spec dG dG_spec om) v j Lt = -ordP ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w)
      ((Matrix.GeneralLinearGroup.det (basesAt Ch std vp unif eO eO_spec dG dG_spec om j Lt v) : _ˣ) : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v) := by
  have hS := (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.setting v
  have := hS.frac_alt
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  cases j with
  | zero =>
    unfold len
    show lenLat ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v 0 Lt) = _
    rw [latAt_bases Ch std vp unif eO eO_spec dG dG_spec om 0 Lt hL v,
      lenLat_colSpan hS.p_unif _ ((Matrix.isUnit_iff_isUnit_det _).1 (basesAt Ch std vp unif eO eO_spec dG dG_spec om 0 Lt v).isUnit)]
  | succ i =>
    unfold len
    show lenLat ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (D.what₂.places.resChar w) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) Lt) = _
    rw [latAt_bases Ch std vp unif eO eO_spec dG dG_spec om (i + 1) Lt hL v,
      lenLat_colSpan hS.p_unif _ ((Matrix.isUnit_iff_isUnit_det _).1 (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) Lt v).isUnit)]

theorem cpAt_y_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).y (i + 1) La =
      reGL (finCongr ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm)
        (Classical.epsilon fun x => ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2
          (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) x ∧
          x ∈ Formalism.UG.UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).y = _
  simp only [chAt, dif_pos hi]

end GlobalTheory.TwV.Xc.PtOrd
end
namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem latticeTuplePoint_det_normOne_order_eq_neg_length : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j), ((sysS H X std).Pj j).IsLatTup La.2 → (J.fd std).dt j La ∈ U1 (sigD D) ∧ ∀ v : (sysS H X std).Pl, ordA (A0 J) v ((J.fd std).dt j La) = -len (sysS H X std) v j La.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj La hLa
  obtain ⟨⟨hr, hpt⟩, -, -, hdt⟩ := hD j hj La hLa
  refine ⟨hdt ▸ Formalism.L2.DIV.det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D j hj) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) _ (J.pt std j hj La).2, fun v => ?_⟩
  rw [PtOrd.len_bases (chainAt H hT) std _ _ _ _ _ _ _ j La.2 hLa v, neg_neg, hdt]
  unfold ordA
  rw [hpt]
  erw [PtOrd.det_reGL']
  cases j with
  | zero =>
    exact congrArg _ (PtOrd.phiA_det_eps (A0 J) La.1 _ _ (let hG := J.one.good; ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩) _ v)
  | succ i =>
    have hP := (GlobalTheory.T.stepCharts_places_firstFactor_eq_stepZero S hD hS i hj ((I.at' i hj).st.eC.symm La.1).1 v).2
    rw [PtOrd.cpAt_y_succ (chainAt H hT) std _ _ _ _ _ _ _ I _ _ _ _ i hj La, ← hP]
    exact congrArg _ (PtOrd.phiA_det_eps _ _ _ _ (let hG := (H.core i hj ((I.at' i hj).st.eC.symm La.1).1).good; ⟨_, hG.isPt_sec _ _, Subgroup.mul_mem _ (hG.yG_mem _) (hG.sec _).2⟩) _ v)

end GlobalTheory.TwV.Xc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleSuccLevelPointIsComponentPointInCharStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTupleSuccLevel_point_isComponentPointInChart : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ g : ∀ v, GL (Fin ((gatJ Lv (j + 1)).P.m + 1)) ((gatJ Lv (j + 1)).P.Qq v), (∀ v, La.2 v = colSpan ((gatJ Lv (j + 1)).P.W v) (g v).1) ∧ ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g (J.pt std (j + 1) hj La).1) := by
  first | exact @GlobalTheory.TwV.DelA.ptS_isPt | exact GlobalTheory.TwV.DelA.ptS_isPt | (intros; apply GlobalTheory.TwV.DelA.ptS_isPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalSpaceGramTransform
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Matrix

namespace GlobalTheory.TwV.DelB.UnitB

theorem det_map_transpose {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (M : Matrix (Fin N) (Fin N) E) :
    ((M.map σ)ᵀ).det = σ M.det := by
  rw [Matrix.det_transpose, RingHom.map_det]
  rfl

theorem det_unitary_prod {E : Type} [CommRing E] (σ : E →+* E) {N : ℕ} (J c B : Matrix (Fin N) (Fin N) E)
    (hc : (c.map σ)ᵀ * c = J) (hB : (B.map σ)ᵀ * J * B = 1) :
    σ (c.det * B.det) * (c.det * B.det) = 1 := by
  have h : ((c * B).map σ)ᵀ * (c * B) = 1 := by
    rw [Matrix.map_mul, Matrix.transpose_mul]
    calc (B.map σ)ᵀ * (c.map σ)ᵀ * (c * B) = (B.map σ)ᵀ * ((c.map σ)ᵀ * c) * B := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc, hB]
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, det_map_transpose, Matrix.det_one, Matrix.det_mul] at hd
  exact hd

end GlobalTheory.TwV.DelB.UnitB

open GlobalTheory.TwV.DelB.UnitB in

theorem GlobalTheory.TwV.DelB.detCrdB_unit : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → ∀ j (hj : j ≤ D.R.m) (β : (J.St j hj).Ch) (B : GL (Fin (D.R.N j)) D.host.E), cT (sigD D : D.host.E →+* D.host.E) B.1 * gramN D j hj * B.1 = 1 → (∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.St j hj).K β).lev.Lb = colSpan ((sysS H X std).G.P.W v) (B.1.map (J.rho std v))) → ∀ τ, ‖ι (TaylorLogMetric.embT D τ ((J.A.crd j hj).1.det * B.1.det))‖ = 1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hPos ι hι j hj β B hB hL τ
  refine GlobalTheory.T.norm_cmEmbedding_normOne_localUnit_eq_one S hPos ι hι _ ?_ (fun v => GlobalTheory.T.det_orthonormalCoords_mul_basis_localUnit S j hj β B v (hL v)) τ
  have hc := J.pins.crd_orth j hj
  have h1 := det_unitary_prod (sigD D : D.host.E →+* D.host.E) (gramN D j hj) (J.A.crd j hj).1 B.1 hc hB
  have hconj : ∀ y : D.host.E, D.host.conj y = (sigD D : D.host.E →+* D.host.E) y := fun y => (bridge_star_holds D.R D.host y).symm
  rw [hconj, mul_comm]
  exact h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPolynomialOddDegreeOfRealisesFramePoly
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem blk_iff_posJ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ)
    (x : Var (X.Pj j)) (b : Σ v : X.Pl, Fin (X.G.P.n' v)) :
    ((⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v)) = (GlobalTheory.TwV.DelA.posJ X D pos j).symm (pos b)) ↔ blkJ X j x = b := by
  cases j
  · simp only [blkJ, idxJ]
    change _ = pos.symm (pos b) ↔ _
    rw [Equiv.symm_apply_apply]
    exact Iff.rfl
  · simp only [blkJ, idxJ]
    change _ = pos.symm (pos b) ↔ _
    rw [Equiv.symm_apply_apply]
    exact Iff.rfl

theorem oddDeg_of_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hmap m hm b hb
  have hs : G.support = Gc.support := by
    rw [← MvPolynomial.support_map_of_injective G (algebraMap X.G.Kf Kc).injective, hmap,
      MvPolynomial.support_map_of_injective Gc ι.injective]
  rw [hs] at hm
  have hh := GlobalTheory.T.realising_polynomial_blockwise_homogeneous X D pos j (rkS X D hN) (wT X D pos j) ν Q Gc hQ hR m hm (pos b)
  obtain ⟨he, -⟩ := GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j (pos b)
  obtain ⟨-, hsz, -, -, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  have hodd : IsOddPos (pos.symm (pos b)).2 := by rw [Equiv.symm_apply_apply]; exact hb
  rw [if_pos hodd] at he hh
  rw [he, ← hsz] at hh
  have hl : ((∑ x ∈ Finset.univ.filter (fun x => blkJ X j x = b), m x : ℕ) : ℤ) =
      ∑ x : Var (X.Pj j), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v)) = (GlobalTheory.TwV.DelA.posJ X D pos j).symm (pos b)
        then (m x : ℤ) else 0 := by
    rw [Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [blk_iff_posJ]
  have h1 : szT X D pos j (pos b) = szMu X j b.1 b.2 := by unfold szT; rw [Equiv.symm_apply_apply]
  have h2 : cT1 X D pos j (pos b) = cMu X j b.1 b.2 := by unfold cT1; rw [Equiv.symm_apply_apply]
  rw [hl, hh, h1, h2, hN.1]
  ring

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumEqOfLatticeTuplesAgreeAway
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.TwV.Xc.xiM_eq_of_sameAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j < D.R.m) (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j Lb Lb') := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v j hj La Lb La' Lb' hab hab'
  obtain ⟨-, -, hN, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  have hj1 : j + 1 ≤ D.R.m := hj
  funext z
  rw [GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj1 (hN j) (hN (j + 1)) La La' z, GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj1 (hN j) (hN (j + 1)) Lb Lb' z]
  have hc : J.chart std j (Nat.le_of_succ_le hj1) La = J.chart std j (Nat.le_of_succ_le hj1) Lb := by
    obtain ⟨h1, h2, h3, -⟩ := hab
    rcases La with ⟨c, a⟩
    rcases Lb with ⟨c', b⟩
    simp only at h3
    subst h3
    exact GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j _ c a b h1 h2
  have hc' : J.chart std (j + 1) hj1 La' = J.chart std (j + 1) hj1 Lb' := by
    obtain ⟨h1, h2, h3, -⟩ := hab'
    rcases La' with ⟨c, a⟩
    rcases Lb' with ⟨c', b⟩
    simp only at h3
    subst h3
    exact GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS (j + 1) _ c a b h1 h2
  rw [hc, hc']
  refine congrFun (S.law.away j hj1 _ _ (J.pt std j _ Lb) (J.pt std (j + 1) hj1 Lb') (J.pt std j _ La) (J.pt std (j + 1) hj1 La') ?_) _
  intro v' hv'
  have hne : v' ≠ ((A0 J).pl v).1 := fun h => (GlobalTheory.T.level_badPrimes_coprime_residueChar S hD hS).2.2.1 v' hv' (h ▸ ((A0 J).pl v).2)
  exact ⟨(GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v j _ La Lb hab).1 v' hne, (GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v (j + 1) hj1 La' Lb' hab').1 v' hne⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumMovedLatticeTuple
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

theorem stdG_one_apply {D : D7} {N : ℕ} (J : Matrix (Fin N) (Fin N) D.host.E) (v : Fin N → D.host.E) :
    stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J 1 v = v := by
  have h : ∀ w : Fin N → D.host.E, toLE (1 : GL (Fin N) D.host.E) w = w := by
    intro w
    simp [toLE, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin]
  show (stdCo _ J) (toLE 1 ((stdCo _ J).symm v)) = v
  rw [h, LinearEquiv.apply_symm_apply]

theorem inFr_stdG_homRe {D : D7} {a b N N' : ℕ} (hr : a = N) (hr' : b = N') (J : Matrix (Fin N) (Fin N) D.host.E)
    (J' : Matrix (Fin N') (Fin N') D.host.E) (g : GL (Fin N) D.host.E) (x : Formalism.L2.Col.HomE D.host.E a b) :
    Formalism.L2.Col.inFr (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J g) (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J' 1) (homRe hr hr' x) =
      homRe hr hr' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) J g)) := by
  subst hr hr'
  apply LinearMap.ext
  intro v
  have h1 : ∀ w, (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) J' 1).symm w = w := by
    intro w
    rw [LinearEquiv.symm_apply_eq, stdG_one_apply]
  simp only [Formalism.L2.Col.inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, h1, homRe, eMat]
  congr 2
  ext i
  simp [Matrix.toLin'_apply, LinearMap.toMatrix'_mulVec]

end GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.TwV.Xc.xiM_smul_moveBy : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → ∀ La' : (sysS H X std).Lt (j + 1), (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) ∈ TaylorLogMetric.Qbar ∧ ∀ x, GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, (((sysS H X std).Lv.lev j c).smul γ La)) La' x = (S.muT (j + 1) (Matrix.GeneralLinearGroup.det κ.1) * (((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ))⁻¹) * GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j (c, La) La' (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS j hj c La γ g κ hr hLa hM La'
  have hj' : j + 1 ≤ D.R.m := hj
  have hr' : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1) := (GlobalTheory.TwV.DelB.sysS_ranks S).2.2.1 (j + 1)
  obtain ⟨hg, hpt, -, r, hr0, -⟩ := hM
  have hκU := ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U_eq κ.1).1 κ.2).1

  have hdet : Matrix.GeneralLinearGroup.det κ.1 ∈ U1 (sigD D) := det_unitary_adelic_point_gram_step_norm_one D j hj.le ⟨κ.1, hκU⟩
  refine ⟨?_, fun x => ?_⟩
  · have hmu := S.law.mu_alg j hj _ hdet
    have hchi : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ∈ TaylorLogMetric.Qbar := by
      rw [← hr0]
      exact (mem_algebraicClosure_iff).2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) r).algHom (D.what₂.embLL.toRatAlgHom))
    exact mul_mem hmu (inv_mem hchi)
  · have e1 := GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj' hr hr' (c, ((sysS H X std).Lv.lev j c).smul γ La) La' x
    have e2 := GlobalTheory.T.movedDatum_pair_eq_adelicDatum_two_points S hD hS j hj' hr hr' (c, La) La'
      (x ∘ₗ Matrix.toLin' (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g))
    have hch := GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hS j hj.le c (((sysS H X std).Lv.lev j c).smul γ La) La
      (GlobalTheory.GO.CmpMem.isLatTup_smul _ γ hLa) hLa
    rw [e1, e2, hch]
    have hx0 : (J.pt std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La)).1 * κ.1⁻¹ ∈
        UPts (sigD D) (gramN D j hj.le) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      mul_mem (J.pt std j hj.le _).2 (inv_mem hκU)
    have hlev := S.law.lev j hj' (J.chart std j hj.le (c, La)) (J.chart std (j + 1) hj' La') ⟨_, hx0⟩ (J.pt std (j + 1) hj' La')
      (J.pt std j hj.le (c, ((sysS H X std).Lv.lev j c).smul γ La)) (J.pt std (j + 1) hj' La') κ 1
      (by show _ = _ * _ * _; group) (by simp) (homRe hr hr' x)
    have hrat := S.law.rat j hj' (J.chart std j hj.le (c, La)) (J.chart std (j + 1) hj' La') (J.pt std j hj.le (c, La))
      (J.pt std (j + 1) hj' La') ⟨_, hx0⟩ (J.pt std (j + 1) hj' La') g hg 1 (one_mem _)
      (by show _ * _ = _; rw [hpt]; group) (by simp) (homRe hr hr' x)
    rw [inFr_stdG_homRe] at hrat
    rw [hrat] at hlev
    simp only [OneMemClass.coe_one, map_one, (S.law.mu_mul j hj).1, one_mul, Units.val_one, mul_one] at hlev
    have hc : ((((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.chi κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
    linear_combination hlev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedPairDatumDependsOnlyOnReaderLevelStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedPairDatum_congr : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') := by
  first | exact @GlobalTheory.TwU.xiM_datLoc | exact GlobalTheory.TwU.xiM_datLoc | (intros; apply GlobalTheory.TwU.xiM_datLoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SeriesCoefficientsAtKernelSiteOfClassSeries
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem tieSerH_series_of_classes : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hN : RankTie (sysS H X std) D j), TieSerH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι (fun j La La' => resV (kapOf (sysS H X std) (hT.gat_pos u w hg) j) (d.gS S ι j La La')) (d.sH S ι) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d ι j hN La _ c' L' _ α _
  exact GlobalTheory.T.coeff_renamed_thetaClass_series t u μ _ (sysS H X std) (hT.gat_pos u w hg) (clsAt X H) ι j hN La (c', L') (d.sH S ι j La (c', L')) α

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteFramesAndChangedFramesInvertible
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem det_map_ringHom {n : Type*} [Fintype n] [DecidableEq n] {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix n n R) : (M.map f).det = f M.det := (RingHom.map_det f M).symm

theorem frInv_fdOfCharts {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7} (cp : ChartPts X D) (a : 𝓞 D.host.E)
    (bad : Finset (HeightOneSpectrum (𝓞 D.host.F))) : FrInv (fdOfCharts cp a bad) := by
  intro j La v
  simp only [fdOfCharts]
  rw [Matrix.det_submatrix_equiv_self, det_map_ringHom]
  apply IsUnit.map
  rw [Matrix.det_mul, LinearMap.det_toMatrix']
  exact IsUnit.mul (LinearEquiv.isUnit_det' _) (Matrix.isUnits_det_units _)

theorem frames_invertible : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    FrInv (J.fd std) ∧ ∀ d : Dec J std, FrInv d.fd2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S
  have h1 : FrInv (J.fd std) := frInv_fdOfCharts _ _ _
  refine ⟨h1, fun d j La v => ?_⟩
  show IsUnit (((star (d.eM j La)).map (J.rho std v)) * (J.fd std).frM j La v).det
  rw [Matrix.det_mul, det_map_ringHom]
  exact IsUnit.mul (IsUnit.map _ (Matrix.isUnit_det_of_left_inverse (GlobalTheory.T.decomposition_unitary_mul_star_eq_one S d j La))) (h1 j La v)

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCharacterDetRationalIsometry
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.muT_det_ratA : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m), ∃ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩) ∧ ∀ k (hk : k ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D k hk), S.muT (j + 1) (Matrix.GeneralLinearGroup.det (ratA D.host.F γ)) = ∏ τ, TaylorLogMetric.embT D τ γ.1.det ^ e τ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S j hj
  obtain ⟨e, he, hz⟩ := S.law.mu_rat j hj
  refine ⟨e, he, fun k hk γ hγ => ?_⟩
  have hu := ((GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S) k hk).2 γ hγ
  have key : Matrix.GeneralLinearGroup.det (ratA D.host.F γ) =
      Formalism.L2.DIV.ratId D.host.F D.host.E (Matrix.GeneralLinearGroup.det γ) := by
    ext
    simp [ratA, Formalism.UG.bc, Formalism.L2.DIV.ratId, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [key]
  have h2 := hz (Matrix.GeneralLinearGroup.det γ) (by simpa using hu.2)
  simpa using h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepCoordsConjUnitaryAndCarriesCompanionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepCoords_conj_unitary_and_carries_companion : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m) β (y : UA D i hi), ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹ ∈ Formalism.L2.Herm.UstdAf D.sp.cm (D.R.N i) ∧ Formalism.L2.Herm.Carries (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹) (latCo D.sp (gramN D i hi) (A.crd i hi) a 1 ((St i hi).K β).lev.Lb) (latCo D.sp (gramN D i hi) (A.crd i hi) a y.1 ((St i hi).K β).lev.Lb) ∧ ∃ d : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det d.1 = Matrix.GeneralLinearGroup.det y.1 ∧ Formalism.L2.Herm.IsDetOf D.sp.cm d (ratA D.host.F (A.crd i hi) * y.1 * (ratA D.host.F (A.crd i hi))⁻¹)) := by
  first | exact @GlobalTheory.TwV.conj_crd_unitary_carries | exact GlobalTheory.TwV.conj_crd_unitary_carries | (intros; apply GlobalTheory.TwV.conj_crd_unitary_carries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepTwistAtClassRepEqCharPowDetStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepTwist_at_classRep_eq_charPow_det : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j + 1 ≤ D.R.m) (β : (I.at' j hj).st.Ch) (c : {c // (I.at' j hj).st.chOf c = β}), ((I.at' j hj).st.tw β).ch (((I.at' j hj).st.K β).y c) = D.chiD ((t.O u μ).dt (j + 1) (castCls (X.onCh j hj) (j + 1) c.1)) ^ cTw D (j + 1)) := by
  first | exact @GlobalTheory.TwV.tw_at_rep | exact GlobalTheory.TwV.tw_at_rep | (intros; apply GlobalTheory.TwV.tw_at_rep <;> assumption)
end

