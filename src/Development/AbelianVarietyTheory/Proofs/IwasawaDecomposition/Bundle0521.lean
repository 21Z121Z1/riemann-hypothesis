import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0310
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0516
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideDefinitionBothLevels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped ComplexOrder
open Formalism.L2.Indef Formalism.IndefR.Cx

noncomputable section

namespace GlobalTheory.Mem.R3.IotaRd

open Formalism.IndefR.Cx.CxData

theorem theta_eq_proj {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A) (b : Bool)
    (eV : ∀ t, (Fin ((lv (fc X.zs) b).nV t) → K) →ₗ[K] A.FR t) (hJ : X.JIsoR cv)
    (hRL : X.RatLev cr cv b) (hDn : X.DnLev cv b) (hUp : X.UpLev cv b) (hC : X.CoordinatesInGoodPart cr cv b)
    (hV : ∀ t F, eV t F ∈ cv.v0R X.zs b t)
    (hO : ∀ t F (x : Fin ((lv (fc X.zs) b).dQ t) → K),
      cv.hR t (cr.toR X.zs b t x) (eV t F) = cv.hR t (cr.toR X.zs b t x) (cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F)))
    (t : Bs.Tup) (F : Fin ((lv (fc X.zs) b).nV t) → K) :
    X.Θ t (X.jR t (eV t F)) = X.Θ t (X.jR t (cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F))) := by
  set q : A.FR t := cr.toR X.zs b t (((lv (fc X.zs) b).Pq t).mulVec F) with hq
  have hdV : eV t F - q ∈ cv.v0R X.zs b t := sub_mem (hV t F) (hC t _)
  have hdo : ∀ x, cv.hR t (cr.toR X.zs b t x) (eV t F - q) = 0 := by
    intro x; rw [map_sub, hO t F x, sub_self]
  have hjV : X.jR t (eV t F - q) ∈ X.V0C cv b t := Submodule.subset_span ⟨_, hdV, rfl⟩
  have hΘE : X.Θ t (X.jR t (eV t F - q)) ∈ X.EEl b := hDn t ⟨_, hjV, rfl⟩
  have horth : ∀ e ∈ X.EEl b, ⟪e, X.Θ t (X.jR t (eV t F - q))⟫_ℂ = 0 := by
    intro e he
    rw [← LinearMap.adjoint_inner_left]
    have h1 : LinearMap.adjoint (X.Θ t) e ∈
        Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) := by
      rw [hRL t]
      exact Submodule.mem_inf.2 ⟨LinearMap.mem_range_self _ e, hUp t (Submodule.mem_map_of_mem he)⟩
    have h2 : Submodule.span ℂ (Set.range fun x : Fin ((lv (fc X.zs) b).dQ t) → K => X.jR t (cr.toR X.zs b t x)) ≤
        (Submodule.span ℂ {X.jR t (eV t F - q)})ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hJ, hdo x, map_zero]
    have h3 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (h2 h1)
    rwa [inner_eq_zero_symm] at h3
  have h0 : X.Θ t (X.jR t (eV t F - q)) = 0 := inner_self_eq_zero.1 (horth _ hΘE)
  rw [map_sub, map_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.Mem.R3.IotaRd

namespace GlobalTheory.Mem.R3.IotaRd

open Formalism.IndefR.Cx.CxData Formalism.IndefR.Links.EvTie

theorem sharp_downTo' (D : D7) (μ) (j : ℕ) : (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RowSide.sharp D).downTo μ j).comp (D.what₂.io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [ih]; rfl

theorem sharp_iota' (D : D7) (μ) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [sharp_downTo']; rfl

theorem rowSideDef3_both : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → RowSideDef3 D A3.A (RowSide.sharp D) F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s1Of R F)) Y.tup Z.eRR Y.jA ∧ RowSideDef3 D A3.A X0.s F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) (A3.indefDown (s0Of R F)) Y.tup Z.eRR0 Y.jA0 := by
  intro hCusp D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  obtain ⟨h1, h0⟩ := GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector hCusp D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  have hC := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have hOk := hH.ok
  have hout : ∀ t y, Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).Θ t ((R.toCx3 F).jR t y)) = R.Th t (R.jX t y) :=
    fun t y => rfl
  have hb : ∀ t (P : Subgroup G) (ψ : P →* D.what₂.LLˣ), BlockHyp (A3.A.fam.R t) (A3.A.fam.lvl P ψ) A3.A.fam.v0 1 :=
    fun t P ψ => ⟨hOk.ok2.conj, hOk.ok2.irr, hOk.ok2.what₂ t⟩
  have hrow : ∀ t (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) x, rowForm A3.A P ψ t ((rV0 D A3.A P ψ t) *ᵥ x) =
      (A3.A.fam.R t).S.basis.equivFun.symm ((A3.A.fam.R t).vE (A3.A.fam.lvl P ψ) *ᵥ x) := by
    intro t P ψ x
    unfold rowForm rV0
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, BlockDat.lf_lvl_vE (hb t P ψ)]
  have k1 : ∀ t x, R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t (rV0 D A3.A F.P1 F.ψ1 t *ᵥ x))) =
      Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding
        ((A3.indefDown (s1Of R F)).ι t *ᵥ ((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x)))) := by
    intro t x
    have e := theta_eq_proj (R.toCx3 F) F.cr F.cv true (F.eV (R.toCx3 F).zs) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1
      (hC.levs true).2.2 (definite_coordinates_in_good_part _ true) (evTie_of_ok hOk F _).1 (evTie_of_ok hOk F _).2 t x
    have k := ((R.toCx3 F).key_row F.cr true (hC.what₂ true).1 (hC.ratMu true) t
      (((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x))).trans ((R.toCx3 F).iC_cpt' F.cr true t _)
    exact (congrArg (fun y => R.Th t (R.jX t y)) (hrow t F.P1 F.ψ1 x)).trans
      ((hout t _).symm.trans (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)) (e.trans k.symm)))
  have k0 : ∀ t x, R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t (rV0 D A3.A F.P0 F.ψ0 t *ᵥ x))) =
      Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding
        ((A3.indefDown (s0Of R F)).ι t *ᵥ ((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x)))) := by
    intro t x
    let eV0 : ∀ t, (Fin ((lv (F.fc (R.toCx3 F).zs) false).nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A3.fam3.amb3.FR t := fun t =>
      ((A3.A.fam.R t).S.basis.equivFun.symm : (Fin (A3.A.fam.R t).S.dim → D.what₂.LL) →ₗ[D.what₂.LL] (A3.A.fam.R t).S.Forms) ∘ₗ
        ((A3.A.fam.R t).vE (A3.A.fam.lvl F.P0 F.ψ0)).mulVecLin
    have e := theta_eq_proj (R.toCx3 F) F.cr F.cv false eV0 hC.jIsoR (hC.levs false).1 (hC.levs false).2.1
      (hC.levs false).2.2 (definite_coordinates_in_good_part _ false) (fun t y => ⟨y, rfl⟩)
      (fun t y x => evTie_block (A3.A.fam.R t) (A3.A.fam.lvl F.P0 F.ψ0) ((R.toCx3 F).zs.Z t)
        (BlockDat.HZ_det hOk.ok2.conj (hOk.ok2.what₂ t) (fun χ hχ => hOk.ok2.irr χ hχ)) x y) t x
    have k := ((R.toCx3 F).key_row F.cr false (hC.what₂ false).1 (hC.ratMu false) t
      (((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t *ᵥ x))).trans ((R.toCx3 F).iC_cpt' F.cr false t _)
    exact (congrArg (fun y => R.Th t (R.jX t y)) (hrow t F.P0 F.ψ0 x)).trans
      ((hout t _).symm.trans (congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H)) (e.trans k.symm)))
  refine ⟨⟨Y.formsA, Y.latA, ?_⟩, ⟨Y.formsAtBottomLevel, Y.latA0, ?_⟩⟩
  · intro t x
    apply Y.Ish.jE.injective
    apply Subtype.val_injective
    have e1 := h1 t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec x)
    have e2 := Z.jEE (((A3.indefDown (s1Of R F)).ι t).mulVec (((A3.A.side F.P1 F.ψ1 (A3.fam3.toSub2 (zsOf R F))).Pq t).mulVec x))
    rw [k1] at e1
    rw [sharp_iota']
    exact e1.trans e2.symm
  · intro t x
    apply Y.Iz.jE.injective
    apply Subtype.val_injective
    have e1 := h0 t ((rV0 D A3.A F.P0 F.ψ0 t).mulVec x)
    have e2 := Z.jEE0 (((A3.indefDown (s0Of R F)).ι t).mulVec (((A3.A.side F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F))).Pq t).mulVec x))
    rw [k0] at e1
    exact e1.trans e2.symm

end GlobalTheory.Mem.R3.IotaRd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralComparisonTransportedDivisionLatticeChanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists Formalism.MainNotions Formalism.L2.Forms Formalism.L2.SG.PackageTie2 MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe GlobalTheory.Mem.Top.Bl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectralComparison_transported_divisionLatticeChange : ∀ (B : Base) (C : Cols B) (a : Late B C) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn a.D.what₂.LL G' Pl0 T a.D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] (R : RealDat a.D A Ks) (F : Face a.D A) (F0 : ∀ u, Forms0 a.D u) (eE : a.D.what₂.EE →ₗ[ℂ] R.HE.H) (s : SAt R F eE F0) (N : ∀ u, Submodule (𝓞 a.D.what₂.LL) (a.D.div.Nu u).V) (hh : a.D.what₂.Word → ℝ) (F₁ : ∀ u, Forms0 (reL a (New.ofDiv a.D N hh)).D u), SameL a (New.ofDiv a.D N hh) F0 F₁ → ∃ s' : SAtL a (New.ofDiv a.D N hh) R F eE F₁, SAtL.pt a (New.ofDiv a.D N hh) s' = tL a (New.ofDiv a.D N hh) s.t := by
  first | exact @GlobalTheory.Mem.SRe.sAtL_exists_ofDiv | exact GlobalTheory.Mem.SRe.sAtL_exists_ofDiv | (intros; apply GlobalTheory.Mem.SRe.sAtL_exists_ofDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdCopy
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StdTr

set_option maxHeartbeats 800000 in

theorem std_copy (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w.st Z') w.I hX T Wt) : z'.Xg = z.Xg → z'.tr = z.tr → HEq z'.R (real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ (iK := z.alg) z.R) → HEq z'.core (coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.core) → z.Std → z'.Std := by
  intro hXg htr hR hc hs
  cases z' with
  | @mk Xg' tr' core' alg' alg_eq' R' cG' geo' pins' lev' idG' good' mu' le' ks' =>
  dsimp only at hXg htr hR hc ⊢
  subst hXg htr
  obtain rfl := eq_of_heq hc
  change BrgStd (w.st Z') w.I hX (usedOf w.I T Wt) z.Xg z.tr R'.toRealDat
  change HEq R' _ at hR
  have e : alg' = alg (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) ⟨Z'.W, Z'.V, Z'.S, Z'.N, Z'.G⟩ z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.st Z').B.embLL.injective
    rw [alg_eq']
    exact (z.alg_eq y).symm
  clear cG' geo' pins' lev' idG' good' mu' le' ks' alg_eq' hc
  subst e
  obtain rfl := eq_of_heq hR
  exact (by with_unfolding_all exact (hs :))

end GlobalTheory.Mem.R3.Rw.StdTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepPinned
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.PinW

theorem valsRoots (K : Ctx) : large₂ K fun B f T => ∀ (px : PreX B.toPre) (I : ColIn B px), I.Ok →
    I.S = {p | p ∈ offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'} → Set.range I.xi = T.set f →
    (∀ a P, (I.xi a).UnrAt P → ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) ∧
    ∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal)) := by
  classical
  choose Z hZ gZ using fun (B : Pre) (Ξ : Set (HChar B.host.E)) => GlobalTheory.Mem.Col2.InEx.exists_holds 1 Ξ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ _ Ξ => Z B Ξ, by simp,
    fun B _ _ _ Ξ z hz => hZ B Ξ z hz, fun B f T _ hH _ _ => ?_⟩
  intro px I h hS hxi
  refine ⟨fun a P _ => ⟨_, (h.xi_reads a _).symm⟩, fun a P hP => ?_⟩
  have hm : I.xi a ∈ T.set f := hxi ▸ Set.mem_range_self a
  have ht := GlobalTheory.Mem.Col2.InEx.isTwist_of_mem_set B f T _ hm
  have hf := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
  have hold := gZ B.toPre _ hf B.LL B.embLL (fun z hz => B.mem_LLC.1 (hH.2 z hz)) _ hm ht.1
  have ht' : Chr.IsTwist B.host I.S (I.xi a) := by rw [hS]; exact ht
  obtain ⟨P', a1, a2⟩ := GlobalTheory.Mem.Col2.InEx.exists_ram_of_mem_QE B h.sel_ok (I.tup a) ht' (h.xi_reads a) hP
  obtain ⟨ζ, hζ⟩ := (hold.2 P' a1).2
  refine ⟨ζ, ?_⟩
  rw [pow_one] at hζ
  have e : Nat.card (𝓞 B.fields.E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [e, a2]
  exact hζ

theorem step_pinned (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ _ _ _ => True) (fun K B f T => ∃ w : ColW B f T, Pinned K B f T w) := by
  have e1 := evG_of_ev (ev_preX_frame h2b)
  have e2 := evG_of_ev GlobalTheory.Mem.Col2.TwIdxEx.evLg_canonical
  have e3 := evG_all fun K => (valsRoots K).inter (GlobalTheory.Mem.Col2.InEx.lg_colIn K)
  refine ((e1.inter e2).inter e3).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hfr, h41⟩, hv⟩ := H
  refine (h41.inter hv).imp fun B f T hO G hk _ _ => ?_
  obtain ⟨H, V, Lc⟩ := G
  obtain ⟨⟨δ, hδ⟩, hp⟩ := hk
  obtain ⟨Pv, d, hsel, habove, hhalf, hd1, hd2⟩ := GlobalTheory.T.exists_half_selection_split_places_base B
  obtain ⟨X, I, hok, hpins, htw, hjets, hsel', hC, hS, hxi, hval⟩ := H hp (hfr _ hO).1 Pv hsel
  obtain ⟨hv1, hv2⟩ := V X I hok hS hxi
  subst hsel'
  exact ⟨⟨X, I, hok, hC, hS, hxi, hpins, GlobalTheory.Mem.Col2.TC.laws_of_ok I hok, StepZero.law0 I hok _, δ, hδ, Lc.2.2,
      fun C W V S N G => (hval C W V S N G).1⟩,
    ⟨⟨htw, hjets, GlobalTheory.Mem.FieldsLaws.fields_ok B, habove, hhalf, d, ⟨hd1, hd2⟩, hv1, hv2⟩⟩⟩

end GlobalTheory.Mem.Top.Bl.PinW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtension
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.ChiTr

theorem coreCharacter_fieldInclusion_eq_columnHeckeChar {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {h : B.fields.Ok} {W : Set B.places.Pl}
    (z : Dat (w.st Z) w.I h T W) (j : Fin B.R.m) :
    ChrEq (z.core.chiW ((j : ℕ) + 1) z.core.toCore.σ₀) (w.I.C.mu0 j) := by
  have e := Formalism.IndefR.FWT.chiTie_of_chiR z.core z.R.toRealDat z.geo.fw.alg_eq z.geo.fw.laws.pins.2.2.1 z.geo.fw.chiR j
  rw [e]
  have h1 := z.lev.is.mu0 j
  rw [z.lev.C] at h1
  exact h1

theorem embLL_chi {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (j : Fin B.R.m)
    (p : {p // p ∈ (B.primes w.px).vGs}) (c : (𝓞 B.fields.E ⧸ p.1.asIdeal)ˣ) (y : 𝓞 B.fields.E) (x : B.fields.Eˣ)
    (hx : (x : B.fields.E) = y) (hc : (c : 𝓞 B.fields.E ⧸ p.1.asIdeal) = Ideal.Quotient.mk p.1.asIdeal y) :
    B.embLL ((w.I.Ch.chi j p c : B.fields.Kˣ) : B.fields.K) = (((w.I.C.mu0 j).locK p.1 x : ℂˣ) : ℂ)⁻¹ := by
  have h1 := (w.ok.ch_tied.mu0 j).atg p x y c hx hc
  rw [h1, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem app_chiW {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Type} [Monoid A]
    {H₁ H₂ : Host E} {l₁ : Level H₁} {l₂ : Level H₂} {c₁ : Coeff l₁} {c₂ : Coeff l₂}
    {χ₁ : ℕ → (c₁.F →+* ℂ) → A →* Circle} {χ₂ : ℕ → (c₂.F →+* ℂ) → A →* Circle}
    (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hc : HEq c₂ c₁) (hχ : HEq χ₂ χ₁) (n : ℕ) :
    χ₂ n c₂.F.val.toRingHom = χ₁ n c₁.F.val.toRingHom := by
  cases hH; cases hl; cases hc; cases hχ; rfl

end GlobalTheory.Mem.R3.Rw.ChiTr

namespace GlobalTheory.Mem.R3.Rw.ChiTr

theorem embLL_chi_ext : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (j₁ : Fin B₁.R.m) (j₂ : Fin B₂.R.m), (j₁ : ℕ) = j₂ → ∀ (p₁ : {p // p ∈ (B₁.primes w₁.px).vGs}) (p₂ : {p // p ∈ (B₂.primes w₂.px).vGs}), HEq p₂.1 p₁.1 → ∀ (c₁ : (𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)ˣ) (c₂ : (𝓞 B₂.fields.E ⧸ p₂.1.asIdeal)ˣ), HEq c₂ c₁ → B₂.embLL ((w₂.I.Ch.chi j₂ p₂ c₂ : B₂.fields.Kˣ) : B₂.fields.K) = B₁.embLL ((w₁.I.Ch.chi j₁ p₁ c₁ : B₁.fields.Kˣ) : B₁.fields.K) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ Z₁ Z₂ h₁ h₂ W₁ W₂ z₁ z₂ hE hX j₁ j₂ hj p₁ p₂ hp c₁ c₂ hc
  have A₁ := coreCharacter_fieldInclusion_eq_columnHeckeChar z₁ j₁
  have A₂ := coreCharacter_fieldInclusion_eq_columnHeckeChar z₂ j₂
  have eH := hX.H
  have el := hX.l
  have ec := hX.c
  have eχ := hX.chiW
  obtain ⟨hP, -⟩ := hE
  clear hX
  rcases B₂ with ⟨P₂⟩
  change P₂ = B₁.toPre at hP
  subst hP
  have ec₀ := app_chiW eH el ec eχ ((j₁ : ℕ) + 1)
  rw [← hj] at A₂
  have A₂' : ChrEq (D := (w₁.st Z₁).toD7) (z₁.core.chiW ((j₁ : ℕ) + 1) z₁.core.Q.c.F.val.toRingHom) (w₂.I.C.mu0 j₂) := by
    rw [← ec₀]
    exact A₂
  have hχ : w₁.I.C.mu0 j₁ = w₂.I.C.mu0 j₂ := (GlobalTheory.ChrEqUnique.chrEq_unique _).1 _ _ _ A₁ A₂'
  rcases p₂ with ⟨q₂, hq₂⟩
  have eq : q₂ = p₁.1 := eq_of_heq hp
  subst eq
  have ecc : c₂ = c₁ := eq_of_heq hc
  subst ecc
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c₂ : 𝓞 B₁.fields.E ⧸ p₁.1.asIdeal)
  have hy0 : ((y : 𝓞 B₁.fields.E) : B₁.fields.E) ≠ 0 := by
    intro h0
    have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
    rw [h0', map_zero] at hy
    exact c₂.ne_zero hy.symm
  rw [embLL_chi w₂ j₂ _ c₂ y (Units.mk0 _ hy0) rfl hy.symm, embLL_chi w₁ j₁ p₁ c₂ y (Units.mk0 _ hy0) rfl hy.symm, hχ]

end GlobalTheory.Mem.R3.Rw.ChiTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleChainsLevelStructureCompatibleAtLevelPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleChains_levelStructure_compatible_at_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → I.StdW l Z l0 W → (∃ Lv : SymmetricTwistedLevelData W, I.StdLv l Z l0 Lv) ∧ Nonempty (TwLvSameS W) := by
  first | exact @GlobalTheory.Mem.Col2.TC.tw_lv_tied_and_same | exact GlobalTheory.Mem.Col2.TC.tw_lv_tied_and_same | (intros; apply GlobalTheory.Mem.Col2.TC.tw_lv_tied_and_same <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleLayerCompatibilitiesOfXPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleLayerCompatibilities_of_X_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) (Lv : SymmetricTwistedLevelData W), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → I.StdW l Z l0 W → I.StdLv l Z l0 Lv → (∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m), ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) → ∃ (Pt : TwPTiedS Lv) (E : TwPEvzS Pt), TwPAtGS Pt ∧ I.StdP l Z l0 Pt E := by
  first | exact @GlobalTheory.Mem.Col2.TC.tupleLayer_compatibility | exact GlobalTheory.Mem.Col2.TC.tupleLayer_compatibility | (intros; apply GlobalTheory.Mem.Col2.TC.tupleLayer_compatibility <;> assumption)
end

