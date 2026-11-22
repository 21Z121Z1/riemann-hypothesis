import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0621
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Formalism.UnipotentAdelicQuotients.Bundle0003
import Formalism.PeriodIntegrals.Bundle0022
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotLv3MvFixH
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0391
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0137
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0439
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0128
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0341
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0675
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0657

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoDetAffDetOm
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.GrCl GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod
open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.HodgeCech

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Dual

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {g : ℕ}

theorem tanLin_bijective (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) :
    Function.Bijective (tanLin t h c.e) := by
  refine ⟨tanLin_injective t h c.e le_rfl h (c.isFrame.res le_rfl), fun a => ?_⟩
  obtain ⟨v, ⟨hv, e⟩, -⟩ := GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x c.U h g c.e c.isFrame a
  exact ⟨tanOf hv, funext e⟩

def dualBasis (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) :
    Module.Basis (Fin g) S (TanM x t.G) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (tanLin_bijective t c x h))

theorem dualBasis_repr (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (v : TanM x t.G)
    (i : Fin g) : (dualBasis t c x h).repr v i = tanLin t h c.e v i := rfl

theorem ev_detUnit (c c' : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U)) :
    ev x _ hh (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right).val =
      rdet ((dualBasis t c' x h').toMatrix (dualBasis t c x h)) := by
  show ev x _ hh ((c.isFrame.basis inf_le_left).det (c'.isFrame.basis inf_le_right)) = _
  rw [Module.Basis.det_apply, RingHom.map_det, rdet_self, ← Matrix.det_transpose]
  congr 1
  ext l i
  rw [Module.Basis.toMatrix_apply, dualBasis_repr, tanLin_apply, ← tanEv_resM t _ hh inf_le_right,
    sum_frMat c'.isFrame c.isFrame inf_le_right inf_le_left, tanEv_sum_smul]
  simp only [tanEv_resM t _ hh inf_le_left]
  have e : ∀ k, tanEv t (isTan_tv (dualBasis t c x h i)) h (c.e k) = if i = k then 1 else 0 := fun k => by
    rw [← tanLin_apply, ← dualBasis_repr, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [e, mul_ite, _root_.mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

def detAff (t : SAB H X) (g : ℕ) : LB X :=
  ⟨{c : VB.Chart (LieVB.omega t.G) g // IsAffineOpen c.U}, fun c => c.1.U,
    fun c c' => c.1.isFrame.detUnit c'.1.isFrame inf_le_left inf_le_right⟩

theorem isLB_detAff (h : VB.IsVB (LieVB.omega t.G) g) : (detAff t g).IsLB := by
  refine ⟨top_le_iff.1 fun x _ => ?_, fun c => h.isLB_det.g_self c.1, fun c c' c'' => h.isLB_det.cocycle c.1 c'.1 c''.1⟩
  obtain ⟨U, e, hx, he⟩ := h x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U) (x := x) hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, _, he.res hVU⟩, hV⟩, hxV⟩

theorem lbIso_detAff (h : VB.IsVB (LieVB.omega t.G) g) : LBIso (detAff t g) (VB.det (LieVB.omega t.G) g) :=
  (VB.lbIso_det_of_frames (isLB_detAff t h) (fun c => c.1.e) (fun c => c.1.isFrame) fun _ _ => rfl).2

end Dual

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) {g : ℕ} {S : Type} [CommRing S]

theorem isAffineOpen_inf' {U V : Y.X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by
    rw [← terminal.comp_from Y.s]
    infer_instance⟩
  exact hU.inf hV

variable {Y}

def pairDet (M : MChart Y) (a : (detAff Y.t g).ι) : Γ(Y.X, M.U ⊓ a.1.U)ˣ :=
  (isUnit_rdet_toMatrix (dualBasis Y.t a.1 (tau (isAffineOpen_inf' Y M.hU a.2)) (tau_le _ inf_le_right))
    (lieBasis M (tau (isAffineOpen_inf' Y M.hU a.2)) (tau_le _ inf_le_left))).unit

theorem ev_pairDet (M : MChart Y) (a : (detAff Y.t g).ι) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ a.1.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ a.1.U)) :
    ev x _ hh (pairDet M a).val = rdet ((dualBasis Y.t a.1 x h').toMatrix (lieBasis M x h)) := by
  have e : spMap (ev x _ hh) ≫ tau (isAffineOpen_inf' Y M.hU a.2) = x := spMap_ev x _ hh
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, dualBasis_repr, dualBasis_repr,
    ← tanPull_lieBasis M _ e (tau_le _ inf_le_left) h, tanLin_tanPull Y.t _ e (tau_le _ inf_le_right) h']
  rfl

variable (Y)

theorem lbIso_detAff_detOm : LBIso (detAff Y.t g) (detOm Y) := by
  refine ⟨⟨fun p => pairDet p.1 p.2⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq ?_
  refine Eq.trans ?_ (congrArg (· * _) (map_inv _ (detChg p.1 q.1)).symm)
  refine eq_inv_mul_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ (p.1 : MChart Y).U := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ (q.1 : MChart Y).U := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ p.2.1.U := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ q.2.1.U := le_preimage_mono inf_le_right hq
  refine (map_mul (ev z _ hz) _ _).trans ?_
  refine (congrArg₂ (· * ·) ((ev_res z _ hz (le_preimage_inf hp1 hq1) _).trans (ev_detChg _ _ z hp1 hq1 _))
    ((map_mul (ev z _ hz) _ _).trans (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans (ev_pairDet _ _ z hp1 hp2 hp))
      ((ev_res z _ hz (le_preimage_inf hp2 hq2) _).trans (ev_detUnit Y.t _ _ z hp2 hq2 _))))).trans
    (Eq.trans ?_ ((ev_res z _ hz hq _).trans (ev_pairDet _ _ z hq1 hq2 hq)).symm)
  rw [_root_.mul_comm, _root_.mul_comm (rdet _) (rdet _), rdet_toMatrix_mul, rdet_toMatrix_mul]

theorem lbIso_detOm_det (hO : (detOm Y).IsLB) (h : VB.IsVB (LieVB.omega Y.t.G) g) :
    LBIso (detOm Y) (VB.det (LieVB.omega Y.t.G) g) :=
  (lbIso_detAff_detOm Y).symm.trans hO (isLB_detAff Y.t h) h.isLB_det (lbIso_detAff Y.t h)

end GlobalTheory.HodgeCech
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelThreeToFour
section
noncomputable section

namespace GlobalTheory.Mem.SRe.UpS

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.DIV
  Formalism.L2.SG.RowDict Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms MeasureTheory NumberField IsDedekindDomain
  GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RowHyp {D : D7} (p : RowPk D) : Prop :=
  p.R.toLevCh.Is p.A.μ0 ∧ p.R.grp_levels p.F ∧ GrpPin p.R ∧ p.R.IsModels ∧
    LinearMap.range p.eE = (p.R.EEat (p.R.levR p.F true)).comap p.R.HE.e ∧
    (∀ x, ‖p.eE x‖ ^ 2 = RealDat.nP p.F true * ‖x‖ ^ 2) ∧ DallTie p.R p.F

set_option maxHeartbeats 4000000 in

theorem rowHyp_read {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : R3.Pins R F cG)
    (hH : R3.Holds R F) : RowHyp (⟨G, Pl0, T, A3.A, Ks, R.toRealDat, F.lv2, Y.eE⟩ : RowPk D) := by
  have hr := R3.RowsLvl.range_eE_and_norm D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  obtain ⟨plg, iso, h⟩ := hP.keep.grp
  exact ⟨hP.char.base.lev, hP.char.base.grp.levels, ⟨R.eG.trans cG, plg, iso, h⟩, hP.char.base.models, hr.1, hr.2, Y.dall⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

set_option maxHeartbeats 4000000 in

theorem rowHyp_pkOf {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (r : RowsT K w Z Wt p0) : RowHyp (pkOf r) :=
  (by with_unfolding_all exact ((rowHyp_read r.r.z.R r.r.z.F r.r.z.cG r.r.Y r.r.z.pins r.r.intersectionNumber_baseChange) :))

def reSt {C : Cols B} (a : Late B C) (Zs : SNew a.D) : SStage B C a.W := reStage a.st Zs

def SatNew : Prop :=
  ∀ (B : Base) (C : Cols B) (a : Late B C) (p : RowPk a.D) (F0 : ∀ u, Forms0 a.D u) (P : SPack a.D F0), GapHyp a.D →
    Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I) → Formalism.L2.SG.Pf.LocCP.LocTied a.D → RealTied a.D →
    a.D.what₂.Dstar = StandardLattice.DstarD a.D → IdempotentRealFixed a.D → RowHyp p →
    ∃ Zs : SNew a.D, ∀ (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ)
      (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ F0 F₁ → Nonempty (SAtL a ⟨Zs, N, hh⟩ p.R p.F p.eE F₁)

set_option maxHeartbeats 4000000 in
theorem satOfDiscreteSeries (h1 : GlobalTheory.Dec.DSInfChar) (h2 : GlobalTheory.Published.HarishChandraFinite) (h3 : GlobalTheory.Published.CuspRapidDecay)
    (h4 : GlobalTheory.Published.DiscreteSeriesUpqUnique) (h5 : Formalism.L2.SG.RowsDef.RowsFinDim) : SatNew :=
  fun B C a p F0 P g i l r d e ⟨a1, a2, a3, a4, a5, a6, a7⟩ =>
    GlobalTheory.T.exists_spectralObjects_over_replacedStages h1 h2 h3 h4 h5 B C a p.G' p.Pl0 p.T p.A p.Ks p.R p.F F0 p.eE P g i l r d a1 a2 a3 e a4 a5 a6 a7

set_option maxHeartbeats 8000000 in

theorem sat_col (a : w.Lt) (col : ColT w a) (p : RowPk (Late.D a)) (Zs : SNew (Late.D a))
    (H : ∀ (N : ∀ u, Submodule (𝓞 (Late.D a).what₂.LL) ((Late.D a).div.Nu u).V) (hh : (Late.D a).what₂.Word → ℝ)
      (F₁ : ∀ u, Forms0 (reL a ⟨Zs, N, hh⟩).D u), SameL a ⟨Zs, N, hh⟩ (fun u => (col.C.forms u).to0) F₁ →
        Nonempty (SAtL a ⟨Zs, N, hh⟩ p.R p.F p.eE F₁))
    (N : ∀ u, Submodule (𝓞 B.LL) (a.V.div.Nu u).V) (h : B.Word → ℝ) (col' : ColT w (upL a (reSt a Zs) N h)) :
    Nonempty ((p.up a (reSt a Zs) N h).SAt fun u => (col'.C.forms u).to0) := by
  let Zn : New (Late.D a) := ⟨Zs, (by with_unfolding_all exact (N :)), (by with_unfolding_all exact (h :))⟩
  obtain ⟨C', hC⟩ := ColRe.exists_colsTiedSym (Late.D a) Zn col.C
  let F₀ : ∀ u, Forms0 (reD (Late.D a) Zn) u := fun u => (C'.forms u).to0
  let F₁ : ∀ u, Forms0 (reL a Zn).D u := (by with_unfolding_all exact (F₀ :))
  have hF : SameL a Zn (fun u => (col.C.forms u).to0) F₁ := (by with_unfolding_all exact (hC :))
  obtain ⟨s⟩ := H Zn.N Zn.h F₁ hF
  have c := CarModel.sameStd B f T w a Zn col ((by with_unfolding_all exact (col' :))) F₁ hF
  exact ⟨CarModel.satCar (D := Late.D (upL a (reSt a Zs) N h)) (F := (by with_unfolding_all exact (F₁ :))) ((by with_unfolding_all exact (c :))) (p.up a (reSt a Zs) N h) ((by with_unfolding_all exact (s :)))⟩

def RealOf : Prop := ∀ D : D7, VolTieG D → D.s.cdScale = Vol.trueScale D.cd → (∀ τ, D.dsig τ = Vol.trueDsig D.R (D.hc τ)) → RealTied D

def PackEx : Prop := ∀ (D : D7) (F : ∀ u, Forms0 D u), GapHyp D → Formalism.L2.SG.Pf.LocCP.LocTied D →
  ∃ P : SPack D F, Integrable P.X.ph (Formalism.L2.SG.ProjRows.muInf P.X.B.I)

set_option maxHeartbeats 4000000 in

theorem real_of (hR : RealOf) (a : w.Lt) (g : GIs2 K w a.G) (hs : a.S.s.cdScale = Vol.trueScale a.G.cd)
    (hd : ∀ τ, a.S.dsig τ = Vol.trueDsig B.R (B.hc τ)) : RealTied (w.D a) :=
  hR (w.D a) (g a.W a.V a.S a.N).1 ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (hd :)))

set_option maxHeartbeats 8000000 in

theorem lv4_of {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (hS : p.S = SExt.none) (hM : LevelThreeCondition p.s) (hN : SatNew) (hR : RealOf)
    (hP : PackEx) (hV : ∀ D : D7, VolTieG D → StandardLattice.VolumeEqMass₂ D) (hE : ∀ D : D7, GlobalTheory.GLq.ESerTie D → IdempotentRealFixed D) (hO : K.Over B.toPre)
    (a : w.Lt) (l : Lv3 p.s K w a) (gap : GapHyp (Late.D a)) (hdel : a.S.s.Del = (Delv K.s K.cD : ℚ))
    (hs : a.S.s.cdScale = Vol.trueScale a.G.cd) (hd : ∀ τ, a.S.dsig τ = Vol.trueDsig B.R (B.hc τ))
    (loc : Formalism.L2.SG.Pf.LocCP.LocTied (Late.D a)) : ∃ b : w.Lt, Nonempty (Lv4 p.s K w b) := by
  obtain ⟨vt, -, ⟨col⟩⟩ := l.g a.W a.V a.S a.N
  have col₀ : ColT w a := col.toColT
  obtain ⟨P, hI⟩ := hP (Late.D a) (fun u => (col₀.C.forms u).to0) gap loc
  have real₀ : RealTied (Late.D a) := (by with_unfolding_all exact ((real_of hR a l.g hs hd) :))
  have dstar : (Late.D a).what₂.Dstar = StandardLattice.DstarD (Late.D a) := (sizes_eq_count K (Late.st a) hO (hV _ real₀.vol) hd).2
  have e0 : IdempotentRealFixed (Late.D a) := hE _ (l.what₂.grp.eSerTie a.V a.S a.G)
  obtain ⟨Zs, H⟩ := hN B w.C a (pkOf l.what₂) _ P gap hI loc real₀ dstar e0 (rowHyp_pkOf l.what₂)
  let b : w.Lt := upL a (reSt a Zs) (fun u => (a.V.div.Nu u).L) a.V.div.h
  obtain ⟨l', e⟩ := hM K B f T w a l (reSt a Zs) (fun u => (a.V.div.Nu u).L) a.V.div.h
  obtain ⟨-, -, ⟨col'⟩⟩ := l'.g b.W b.V b.S b.N
  have col₁ : ColumnDataSplitPrimes K w b := col'
  obtain ⟨s⟩ := sat_col a col₀ (pkOf l.what₂) Zs H _ _ col₁.toColT
  have s' : SX K B f T w b l'.Wt l'.p0 l'.what₂ col₁.toColT := by
    rw [sx_eq l'.what₂ col₁.toColT, e]
    exact s
  have x : p.S K B f T w b l'.Wt l'.p0 l'.what₂ col₁.toColT s' := by
    rw [hS]
    exact PUnit.unit
  exact ⟨b, ⟨⟨l', col₁, real_of hR b l'.g ((by with_unfolding_all exact (hs :))) ((by with_unfolding_all exact (hd :))), (by with_unfolding_all exact (hd :)), (by with_unfolding_all exact (hdel :)), ⟨s', x⟩⟩⟩⟩

set_option maxHeartbeats 8000000 in

theorem step_of {hL : GlobalTheory.Published.LocalLanglandsGL} (p : Prm hL) (hS : p.S = SExt.none) (hM : LevelThreeCondition p.s) (hN : SatNew) (hR : RealOf)
    (hP : PackEx) (hV : ∀ D : D7, VolTieG D → StandardLattice.VolumeEqMass₂ D) (hE : ∀ D : D7, GlobalTheory.GLq.ESerTie D → IdempotentRealFixed D) :
    StepW (pinAnd (Has3 p.s)) (Has4 p.s) := by
  refine Step.of_evG ((evG_of_ev GlobalTheory.Mem.Top.NodeGap.ev_gapHyp).imp fun K _ _ _ _ gap B f T hO _ _ _ w => ?_)
  rintro ⟨-, Z, ⟨l⟩⟩
  obtain ⟨S, hdel, hs, hd, loc⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C Z.W Z.G.cd hO (SpectralModel.colsPos_of Z.S) (SpectralModel.rows_le_of Z.S)
  obtain ⟨l₀, -⟩ := hM K B f T w Z l S (fun u => (Z.V.div.Nu u).L) Z.V.div.h
  exact lv4_of p hS hM hN hR hP hV hE hO _ l₀ (gap _ hO) hdel hs hd ((by with_unfolding_all exact ((loc (upL Z S (fun u => (Z.V.div.Nu u).L) Z.V.div.h).V Z.N Z.G) :)))

theorem realOf (h1 : Vol.DiscreteSeriesExist) (h2 : Vol.FormalDegreeFormula₂) : RealOf := by
  intro D hv hs hd
  refine ⟨?_, ?_, ?_, hv⟩
  · rw [Vol.cdScaleTie_iff, hs]
    exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd
  · intro τ
    unfold Formalism.L2.Theta.IsDsig
    rw [hs, hd τ]
    exact (GlobalTheory.T.exists_discreteSeries_formalDegree_product h1 h2 D.cd D.R (D.hc τ)).1
  · intro τ H _ _ σ d hσ hf
    rw [hs] at hf
    rw [hd τ]
    exact (GlobalTheory.T.exists_discreteSeries_formalDegree_product h1 h2 D.cd D.R (D.hc τ)).2 H σ d hσ hf

theorem goodIdempotent_real_of_harishChandra_series (D : D7) (h : GlobalTheory.GLq.ESerTie D) : IdempotentRealFixed D :=
  GlobalTheory.GoodIdemReal.star_coeff_of_reverse D fun k g hm h0 x => by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    obtain ⟨L, -, he⟩ := h k
    rw [he, he]
    exact DFunLike.congr_fun (GlobalTheory.GLq.GalSer.eSerC_map L _ D.R.r hm (GlobalTheory.SeriesSupport.rel_dual L hm h0)) x

theorem stepW_has4 : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.BesselMapUniq.BesselMapUniq → Vol.DiscreteSeriesExist → Vol.FormalDegreeFormula₂ → StandardLattice.SiegelMassRatioCM → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), p.S = SExt.none → LevelThreeCondition p.s → StepW (pinAnd (Has3 p.s)) (Has4 p.s) :=
  fun h1 h2 h3 h4 h5 hW hB hD hF _ _ p hS hM =>
    step_of p hS hM (satOfDiscreteSeries h1 h2 h3 h4 h5) (realOf hD hF) (GlobalTheory.Mem.SRe.exists_sPack_integrable hW hB h5)
      (GlobalTheory.Mem.VolMass.volumes_eq_masses_of_unfold (GlobalTheory.VolRatioFromSiegelWeil.volumeRatio hW)) goodIdempotent_real_of_harishChandra_series

end GlobalTheory.Mem.SRe.UpS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearFormFromFinsupp
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

variable {X : Type} [AddCommGroup X]

theorem linW_single_apply (p : X × X) (k : ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (Finsupp.single p k) β = k * β p.1 p.2 := by
  rw [linW_apply, Finsupp.sum_single_index (by simp)]

theorem linW_add_apply (w v : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (w + v) β = linW w β + linW v β := by
  simp only [linW_apply]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem linW_finset_sum_apply {ι : Type} (s : Finset ι) (g : ι → (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (∑ i ∈ s, g i) β = ∑ i ∈ s, linW (g i) β := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linW_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, linW_add_apply, ih]

theorem bilin_eq_zero_of_mem_torsion_left (β : LinearMap.BilinForm ℤ X) {t : X}
    (ht : t ∈ Submodule.torsion ℤ X) (y : X) : β t y = 0 := by
  obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff t).mp ht
  rw [Submonoid.smul_def] at hn
  have h := LinearMap.map_smul₂ β (n : ℤ) t y
  rw [hn, map_zero, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h
  exact h.resolve_left (nonZeroDivisors.coe_ne_zero n)

theorem bilin_eq_zero_of_mem_torsion_right (β : LinearMap.BilinForm ℤ X) (x : X) {t : X}
    (ht : t ∈ Submodule.torsion ℤ X) : β x t = 0 := by
  obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff t).mp ht
  rw [Submonoid.smul_def] at hn
  have h := (β x).map_smul (n : ℤ) t
  rw [hn, map_zero, eq_comm, smul_eq_zero] at h
  exact h.resolve_left (nonZeroDivisors.coe_ne_zero n)

theorem exists_linW_eq : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    ∃ w : (X × X) →₀ ℤ, linW w = ℓ := by
  intro X _ _ ℓ
  classical
  let T := Submodule.torsion ℤ X
  let b := Module.Free.chooseBasis ℤ (X ⧸ T)
  let e : Module.Free.ChooseBasisIndex ℤ (X ⧸ T) → X := fun i => (T.mkQ_surjective (b i)).choose
  have he : ∀ i, T.mkQ (e i) = b i := fun i => (T.mkQ_surjective (b i)).choose_spec
  let c : Module.Free.ChooseBasisIndex ℤ (X ⧸ T) → X →ₗ[ℤ] ℤ := fun i => (b.coord i).comp T.mkQ
  have hdec : ∀ x, x - ∑ i, c i x • e i ∈ T := by
    intro x
    refine (Submodule.Quotient.mk_eq_zero T).mp ?_
    change T.mkQ _ = 0
    rw [map_sub, map_sum]
    simp only [map_smul, he, c, LinearMap.comp_apply, Module.Basis.coord_apply]
    rw [b.sum_repr, sub_self]
  have hβ : ∀ β : LinearMap.BilinForm ℤ X,
      β = ∑ i, ∑ j, β (e i) (e j) • (c i).smulRight (c j) := by
    intro β
    ext x y
    have h1 : β x y = β (∑ i, c i x • e i) y := by
      have := bilin_eq_zero_of_mem_torsion_left β (hdec x) y
      rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    have h2 : ∀ x', β x' y = β x' (∑ j, c j y • e j) := by
      intro x'
      have := bilin_eq_zero_of_mem_torsion_right β x' (hdec y)
      rwa [map_sub, sub_eq_zero] at this
    rw [h1, h2]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨∑ i, ∑ j, Finsupp.single (e i, e j) (ℓ ((c i).smulRight (c j))), ?_⟩
  ext β
  rw [linW_finset_sum_apply]
  conv_rhs => rw [hβ β]
  simp only [map_sum, map_smul, smul_eq_mul, linW_finset_sum_apply, linW_single_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PolCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixW
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv GlobalTheory.RayHoriz
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayRosEx

section Weights

variable {S : Type} [CommRing S] {ρ : Type}

def mixW (M : Fin 2 → Fin 3 → S) (W : Fin 2 → ρ → S) : Fin 3 → ρ → S := fun i r => ∑ k, M k i * W k r

def rat3 {U : Type} [CommGroup U] (E : (Fin 3 → ρ → S) → U) (α β : ρ → S) (M : Fin 2 → Fin 3 → S) : U :=
  E (mixW M ![α, fun _ => 1]) * (E (mixW M ![α, fun _ => 0]))⁻¹ * (E (mixW M ![fun _ => 0, fun _ => 1]))⁻¹ *
    (E (mixW M ![fun _ => 1, β]))⁻¹ * E (mixW M ![fun _ => 1, fun _ => 0]) * E (mixW M ![fun _ => 0, β])

def th3 {U : Type} [CommGroup U] (E : (Fin 3 → ρ → S) → U) (s : Fin 3 → ρ → S) : U :=
  ∏ I : Finset (Fin 3), E (fun i r => if i ∈ I then s i r else 0) ^ ((-1 : ℤ) ^ (3 - I.card))

def subL (M : Fin 2 → Fin 3 → S) (m : ℕ) : Jet S (Fin 2 × ρ) m →ₐ[S] Jet S (Fin 3 × ρ) m :=
  jetMap (fun p => ∑ i, MvPolynomial.C (M p.1 i) * MvPolynomial.X (i, p.2)) fun p =>
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (X_mem_orig (i, p.2))

def sc3 (s : Fin 3 → ρ → S) (m : ℕ) : Jet S (Fin 3 × ρ) m →ₐ[S] Jet S (Fin 3 × ρ) m :=
  jetScale fun p => s p.1 p.2

end Weights

end GlobalTheory.RayRosEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NTiedAllAtWit
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem nTiedAll_atWit : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL) (K : Ctx) (q : WPt p.s K), ∃ (I : TwIn (q.w.D q.Z)) (n : Formalism.L2.NormalizedTwistCompatibility (q.w.D q.Z) q.O.ex.nch I), I.E = twEOf q.O.ex.xd ∧ DQ.GoodAllAt (q.w.D q.Z) q.O.ex.nch I ∧ (⟨n.cf, n.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = ⟨TC.cf q.w.I q.w.l q.Z, q.x.n.tp⟩ ∧ n.gal = q.core.a.all.gal ∧ n.n = q.core.a.all.n ∧ n.exp = q.core.a.all.exp ∧ n.chiD = q.core.a.all.chiD ∧ n.twF = q.core.a.all.twF ∧ HEq n.types q.core.a.all.types ∧ HEq n.cover q.core.a.all.cover ∧ n.plB = q.core.a.all.plB := by
  intro hL p K q
  obtain ⟨I, hE, hG, hC⟩ := q.x.good.tw
  have hch := q.core.a.chr_eq
  have hc : Formalism.L2.NChoiceTied (q.w.D q.Z) q.O.ex.nch I (Formalism.L2.avDesign (q.w.D q.Z)) := by
    have c := q.core.a.all.choice
    first
    | exact { twI_conj := c.twI_conj, sd_place := c.sd_place, emb_side := c.emb_side, sd_conj := c.sd_conj, one := c.one,
              good := fun w hw h => hC w hw h, conj := c.conj }
    | exact { twI_conj := c.twI_conj, sd_place := c.sd_place, emb_side := c.emb_side, sd_conj := c.sd_conj, one := c.one,
              conj := c.conj }
  refine ⟨I, { q.core.a.all with choice := hc }, hE, hG, hch, rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, rfl⟩

end GlobalTheory.Mem.Top.Bl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointDerivationAffineOpenEqFderivEtaleChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointDerivation_affineOpen_eq_fderiv_etaleChart : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ) (c : AlgChart p σ n) (x₀ : CxPts p σ), x₀ ∈ c.e.source → ∀ (U : Y.affineOpens), x₀ ∈ CxPts.ptsIn p σ U.1 → ∀ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) → (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) → ∃ v : ReciprocityTheory.L2DbarEstimates.V n, ∀ g : Γ(Y, U.1), δ g = fderiv ℂ (CxPts.ev p σ U.1 g ∘ c.e.symm) (c.e x₀) v := by
  first | exact @GlobalTheory.PointDer.exists_eq_fderiv | exact GlobalTheory.PointDer.exists_eq_fderiv | (intros; apply GlobalTheory.PointDer.exists_eq_fderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanCarrierDimensionBounded
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem genRank_le_sq (E : Type) [Field E] [NumberField E] (q : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) {m : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) : genRank γ ≤ (q * Module.finrank ℚ E) ^ 2 := by
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Free ℤ X := free_int_of_projective E
  have h1 : genRank γ ≤ Module.finrank ℤ (LinearMap.BilinForm ℤ X) :=
    Submodule.finrank_le _
  have h2 : Module.finrank ℤ (LinearMap.BilinForm ℤ X) = Module.finrank ℤ X * Module.finrank ℤ X := by
    unfold LinearMap.BilinForm
    rw [Module.finrank_linearMap, Module.finrank_linearMap_self]
  have h3 : Module.finrank ℤ X ≤ q * Module.finrank ℚ E := by
    rw [finrank_int_eq_finrank_mul E X, mul_comm]
    exact Nat.mul_le_mul_right _ hX
  calc genRank γ ≤ Module.finrank ℤ X * Module.finrank ℤ X := h2 ▸ h1
    _ ≤ (q * Module.finrank ℚ E) * (q * Module.finrank ℚ E) := Nat.mul_le_mul h3 h3
    _ = (q * Module.finrank ℚ E) ^ 2 := (sq _).symm

theorem carrierDim_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)), IsCarrierDim H.bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  intro E _ _ _ H q ψ lab hlab
  refine ⟨(q * Module.finrank ℚ E) ^ 2, fun X _ _ _ _ hX β hβ hpos => ?_⟩
  rw [hlab X hX β hβ hpos]
  exact_mod_cast (by
    rcases Set.eq_empty_or_nonempty {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
        InRCone γ β ∧ genRank γ = k} with he | hne
    · rw [he, Nat.sInf_empty]; exact Nat.zero_le _
    · obtain ⟨m, γ, -, -, hk⟩ := Nat.sInf_mem hne
      rw [← hk]; exact genRank_le_sq E q X hX γ :
    sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧ genRank γ = k} ≤
      (q * Module.finrank ℚ E) ^ 2)

end GlobalTheory.PolFan
end
end

