import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealLowestKTypeOfExtremalVectorCase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0406
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FamilyLinkDownward
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowDescent

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

abbrev xOf (W : RealPack ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL) : ((pk W).HX t).H :=
  (pk W).jX t (W.Q.F.eV (cxW W).zs t F)

theorem topOf_eq (W : RealPack ex) (t : W.P.T) (F : Fin ((W.Q.F.fc (cxW W).zs).Df1.nV t) → D.what₂.LL) :
    topOf W t F = (pk W).cX.toMap (pk W).prX (((pk W).HX t).e (xOf W t F)) := rfl

theorem dn_eq {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u) (t : W.P.T) (hr : (f.row t).Is) :
    ∀ k, k + 1 ≤ D.R.m → ∀ (F : (f.t t).CC k) (F' : (pk W).CC t k), F.1 = F'.1 →
      ((f.t t).dn k F).1 = (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) k F').1 := by
  intro k
  induction k with
  | zero => intro _ F F' e; exact e
  | succ k ih =>
    intro hk F F' e
    obtain ⟨h1, h2⟩ := hr.io k (by omega) F
    have e2 : (⟨F.1, h1⟩ : (pk W).CC t (k + 1)) = F' := Subtype.ext e
    show ((f.t t).dn k ((f.row t).io k F)).1 = (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) k ((pk W).ioY t k F')).1
    rw [← e2]
    exact ih (by omega) _ _ h2

theorem dnFrom_heq (W : RealPack ex) (t : W.P.T) {k : ℕ} (hk : D.R.m - 1 = k) (X : (pk W).CC t k) (X' : (pk W).CC t (D.R.m - 1))
    (e : HEq X X') : (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) k X).1 = (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) (D.R.m - 1) X').1 := by
  subst hk
  rw [eq_of_heq e]

theorem app_heq (W : RealPack ex) (t : W.P.T) {M : Type} [AddCommGroup M] [Module ℂ M] {k k' : ℕ} (p : k = k')
    (g : M →ₗ[ℂ] (pk W).CC t k) (z : M) :
    HEq ((Eq.rec (motive := fun n _ => M →ₗ[ℂ] (pk W).CC t n) g p) z) (g z) := by
  subst p
  rfl

set_option maxHeartbeats 1000000 in

theorem down_eq {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u) (t : W.P.T) (hr : (f.row t).Is) (n : ℕ)
    (h : 2 * n + 2 * 0 + 2 = D.R.m) (G : (f.t t).CT) (y : ((pk W).HX t).H)
    (hG : G.1 = (pk W).cX.toMap (pk W).prX (((pk W).HX t).e y)) : down f n h t G = (pk W).thDn t y := by
  have H := hr.ioT (2 * n) h G
  have h' := H.choose
  have e : (((f.row t).ioT (2 * n) h G).1 : SmT ((pk W).MY (2 * n + 1)) →ₗ[ℂ] (GA D (Yc D (2 * n + 1)) → ℂ)) =
      (ioXT (pk W) t (2 * n) h ⟨G.1, h'⟩).1 := H.choose_spec
  have e1 := dn_eq f t hr (2 * n + 1) (by omega) ((f.t t).ioT (2 * n) h G) (ioXT (pk W) t (2 * n) h ⟨G.1, h'⟩) e
  have hy : (⟨G.1, h'⟩ : LinearMap.range ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e)) =
      ((pk W).cX.toMap (pk W).prX ∘ₗ ((pk W).HX t).e).rangeRestrict y := Subtype.ext hG
  have e2 := dnFrom_heq W t (idx_top h) (ioXT (pk W) t (2 * n) h ⟨G.1, h'⟩) ((pk W).ioX t ⟨G.1, h'⟩)
    (app_heq W t (idx_top h) ((pk W).ioX t) _)
  have e3 : (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) (D.R.m - 1) ((pk W).ioX t ⟨G.1, h'⟩)).1 = (pk W).thDn t y :=
    (congrArg (fun z => (Lift.dnFrom ((pk W).CC t) ((pk W).ioY t) (D.R.m - 1) ((pk W).ioX t z)).1) hy).trans
      (GlobalTheory.ChainEquiv.thDn_eq t y).symm
  have key : ((f.t t).dn (2 * n + 1) ((f.t t).ioT (2 * n) h G)).1 = (pk W).thDn t y := e1.trans (e2.trans e3)
  unfold GlobalTheory.MiTop.down
  exact key

theorem lift_postOn_fixed (W : RealPack ex) (T : SmT ((pk W).MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ))
    (hT : ∀ v : ((pk W).MY 0).Vec, (pk W).e0 (T (PiTensorProduct.tprod ℂ v)) = T (PiTensorProduct.tprod ℂ v)) :
    PiTensorProduct.lift (postOn ((pk W).MY 0) (pk W).e0 (PiTensorProduct.lift.symm T)) = T := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod, postOn_apply]
  rw [show (PiTensorProduct.lift.symm T) v = T (PiTensorProduct.tprod ℂ v) from rfl, hT v]

end GlobalTheory.RowDescent

end

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.MiTop.linkDown_of_rowOK : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ f : FamCh W u, f.RowOK → LinkDown f := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f hR n h t F
  refine ⟨⟨topOf W t F, GlobalTheory.T.top_vector_mem_extra_projection W hP t F⟩, rfl, ?_⟩
  have e1 := GlobalTheory.RowDescent.down_eq f t (hR.row t) n h ⟨topOf W t F, GlobalTheory.T.top_vector_mem_extra_projection W hP t F⟩
    (GlobalTheory.RowDescent.xOf W t F) (GlobalTheory.RowDescent.topOf_eq W t F)
  have hC : (pk W).IsChain := RealDat.chain_of_weak W.Q.charW.base.chain hP.ex
  have e2 : rowAt W t F = PiTensorProduct.lift ((pk W).HE.e ((pk W).Th t (GlobalTheory.RowDescent.xOf W t F))) := rfl
  have e3 := congrArg PiTensorProduct.lift (hC.Th t (GlobalTheory.RowDescent.xOf W t F))
  have e4 := GlobalTheory.RowDescent.lift_postOn_fixed W _ (GlobalTheory.T.e0_thDn_tprod_eq W hP t F)
  exact e1.trans (e4.symm.trans (e3.symm.trans e2.symm))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientEqConstMulLowestKTypeCoefficient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

noncomputable section

namespace GlobalTheory.RawLift.FockPair

open GlobalTheory.DefLift GlobalTheory.RawLift GlobalTheory.RawLift.RealLowRed Formalism.IndefR.FWT

variable {D : D7} {V W : HSp D} {S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {χV χW : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {μ : Measure (WO V W)} {𝓕 : Set (WO V W)}

open Classical in
set_option maxHeartbeats 4000000 in

theorem pair_of_ext (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel W S') (hLS : LowSm M) (hLI : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M)
    (hω : IsWeilDatumO ψ V W χV χW ω) (hcv : IsCovolOne (ratL W V) μ 𝓕)
    (J : MultilinearMap ℂ (fun ρ => lowT M ρ) (WO V W → ℂ)) (hJ : ∀ v, IsThetaFunO ψ V W (J v))
    (hK : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) →
      J (Function.update v τ u) = ω (1, atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)) (J v))
    (hX : ∀ v : (∀ ρ, lowT M ρ), IsExtVec M (fun ρ => (v ρ : M.sm ρ)) → ∀ u ∈ GinfC W,
      thetaIP μ 𝓕 (J v) (ω (1, u) (J v)) = thetaIP μ 𝓕 (J v) (J v) *
        ∏ ρ, ⟪((v ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) u) ((v ρ : M.sm ρ) : M.H ρ)⟫_ℂ) :
    ∃ N : ℂ, ∀ (v v' : ∀ ρ, lowT M ρ), ∀ g ∈ GinfC W, thetaIP μ 𝓕 (J v) (ω (1, g) (J v')) = N *
      ∏ ρ, ⟪((v ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) ((v' ρ : M.sm ρ) : M.H ρ)⟫_ℂ := by
  have h1 : μ 𝓕 = 1 := hcv.2.2
  have hU : ∀ ρ, IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D W ρ)) (M.rep ρ) := fun ρ =>
    (GlobalTheory.HolDict.ModelRep.model_rep D W S' M ρ).2.1
  have hXU : ∀ g ρ, infMat D.sp.cm.sig W.gram (θ ρ) g ∈ Formalism.QuantumDeterminants.UH (gramAt D W ρ) :=
    fun g ρ => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W g ρ
  have hrep : ∀ ρ g h, M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) (g * h)) =
      (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g)).comp (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) h)) :=
    fun ρ g h => by
      rw [GlobalTheory.PointAtPlaceHom.infMat_mul]
      exact (hU ρ).1.2 _ (hXU g ρ) _ (hXU h ρ)
  have hrep1 : ∀ ρ, M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) 1) = 1 := fun ρ => by
    rw [GlobalTheory.PointAtPlaceHom.infMat_one]
    exact (hU ρ).1.1
  have hωmul : ∀ g h f, ω (1, g) (ω (1, h) f) = ω (1, g * h) f := fun g h f => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

  have hA : ∀ τ, ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ (v : ∀ ρ, lowT M ρ) (u : lowT M τ),
      ((u : M.sm τ) : M.H τ) = M.σ τ k ((v τ : M.sm τ) : M.H τ) → ∀ ρ,
      (((Function.update v τ u ρ : lowT M ρ) : M.sm ρ) : M.H ρ) =
        M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) (atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)))
          ((v ρ : M.sm ρ) : M.H ρ) := by
    intro τ k hk v u hu ρ
    have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
    have hg : (M.fr τ)⁻¹ * k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) := by
      have hk' : kᴴ * Formalism.REAL.Jm (M.ε τ) * k = Formalism.REAL.Jm (M.ε τ) := kset_uj hk
      have e1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
      change ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D W τ * ((M.fr τ)⁻¹ * k * M.fr τ) = gramAt D W τ
      calc ((M.fr τ)⁻¹ * k * M.fr τ)ᴴ * gramAt D W τ * ((M.fr τ)⁻¹ * k * M.fr τ)
          = (M.fr τ)ᴴ * (kᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * k) *
              M.fr τ := by
            rw [← M.fr_gram τ]; simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D W τ := by rw [e1, mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_one, hk', M.fr_gram]
    have e2 : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
        mul_nonsing_inv _ hd, Matrix.mul_one]
    have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ W τ hg
    by_cases c : ρ = τ
    · subst c
      rw [Function.update_self, hu, hs.2.1]
      unfold DSModel.rep
      rw [e2]
    · rw [Function.update_of_ne c, hs.2.2 ρ c, (hU ρ).1.1]
      rfl
  have hinv : ∀ ρ (a : GA D W) (y x : M.H ρ), ⟪M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a⁻¹) y, x⟫_ℂ =
      ⟪y, M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a) x⟫_ℂ := by
    intro ρ a y x
    let L : M.H ρ →ₗᵢ[ℂ] M.H ρ :=
      { toLinearMap := (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a)).toLinearMap,
        norm_map' := (hU ρ).2.1 _ (hXU a ρ) }
    have e : M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a) (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a⁻¹) y) = y := by
      rw [← ContinuousLinearMap.comp_apply, ← hrep, mul_inv_cancel, hrep1]
      rfl
    calc ⟪M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a⁻¹) y, x⟫_ℂ
        = ⟪L (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a⁻¹) y), L x⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪y, M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a) x⟫_ℂ := by
        rw [show L (M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) a⁻¹) y) = y from e]
        rfl

  obtain ⟨e0, he0⟩ := exists_isExtVec M hLS
  let e : ∀ ρ, lowT M ρ := fun ρ => ⟨e0 ρ, (he0 ρ).2.1⟩
  have hext : IsExtVec M (fun ρ => (e ρ : M.sm ρ)) := he0
  have hne : ∀ ρ, e ρ ≠ 0 := fun ρ h => by
    have h' := (he0 ρ).1
    have h0 : ((e0 ρ : M.sm ρ) : M.H ρ) = 0 := by
      have := congrArg (fun x : lowT M ρ => ((x : M.sm ρ) : M.H ρ)) h
      simpa [e] using this
    rw [h0, norm_zero] at h'
    exact zero_ne_one h'

  have st1 : ∀ v', ∀ g ∈ GinfC W, thetaIP μ 𝓕 (J e) (ω (1, g) (J v')) = thetaIP μ 𝓕 (J e) (J e) *
      ∏ ρ, ⟪((e ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) ((v' ρ : M.sm ρ) : M.H ρ)⟫_ℂ := by
    intro v'
    have key := GlobalTheory.DefLift.mem_of_translates hLS hLI
      (thR hω h1 J hJ (J e) (hJ e) - thetaIP μ 𝓕 (J e) (J e) • prodR θ M (fun ρ => ((e ρ : M.sm ρ) : M.H ρ)))
      (offReal W) e hne ?_ ?_ v'
    · intro g hg
      have := key g hg
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodR_apply, thR_apply] at this
      exact sub_eq_zero.1 this
    · intro g hg
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodR_apply, thR_apply]
      exact sub_eq_zero.2 (hX e hext g hg)
    · intro τ k hk v' u hu hv' g hg
      have := hv' (g * atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ)) (mul_mem hg (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _))
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodR_apply, thR_apply] at this ⊢
      rw [hK τ k hk v' u hu, hωmul]
      have hp : ∏ ρ, ⟪((e ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g)
            (((Function.update v' τ u ρ : lowT M ρ) : M.sm ρ) : M.H ρ)⟫_ℂ =
          ∏ ρ, ⟪((e ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ)
            (g * atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ))) ((v' ρ : M.sm ρ) : M.H ρ)⟫_ℂ :=
        Finset.prod_congr rfl fun ρ _ => by rw [hA τ k hk v' u hu ρ, hrep]; rfl
      rw [hp]
      exact this

  have hconj : ∀ (x y : ∀ ρ, M.H ρ), ∏ ρ, ⟪y ρ, x ρ⟫_ℂ = star (∏ ρ, ⟪x ρ, y ρ⟫_ℂ) := fun x y => by
    rw [star_prod]
    exact Finset.prod_congr rfl fun ρ _ => (inner_conj_symm _ _).symm
  have st2 : ∀ v v', ∀ g ∈ GinfC W, thetaIP μ 𝓕 (J v) (ω (1, g) (J v')) = thetaIP μ 𝓕 (J e) (J e) *
      ∏ ρ, ⟪((v ρ : M.sm ρ) : M.H ρ), M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) ((v' ρ : M.sm ρ) : M.H ρ)⟫_ℂ := by
    intro v v'
    have key := GlobalTheory.DefLift.mem_of_translates hLS hLI
      (thL hω h1 J hJ (J v') (hJ v') - star (thetaIP μ 𝓕 (J e) (J e)) •
        prodL θ M (fun ρ => ((v' ρ : M.sm ρ) : M.H ρ))) (offReal W) e hne ?_ ?_ v
    · intro g hg
      have := key g hg
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodL_apply, thL_apply] at this
      rw [sub_eq_zero, hconj, ← star_mul'] at this
      exact star_injective this
    · intro g hg
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodL_apply, thL_apply]
      rw [st1 v' g hg, star_mul', ← hconj, sub_self]
    · intro τ k hk v u hu hv g hg
      set a := atTau θ W τ ((M.fr τ)⁻¹ * k * M.fr τ) with ha
      have := hv (a⁻¹ * g) (mul_mem (inv_mem (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _)) hg)
      simp only [MultilinearMap.sub_apply, MultilinearMap.smul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        prodL_apply, thL_apply] at this ⊢
      have e1 : ω (1, g) (J v') = ω (1, a) (ω (1, a⁻¹ * g) (J v')) := by rw [hωmul, mul_inv_cancel_left]
      rw [hK τ k hk v u hu, e1, GlobalTheory.WeilPairing.thetaInner_weilRep D ψ V W χV χW ω μ 𝓕 hω hcv (1, a) _ _ (hJ v)
        (hω.om_pres _ _ (hJ v'))]
      have hp : ∏ ρ, ⟪M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) g) ((v' ρ : M.sm ρ) : M.H ρ),
            (((Function.update v τ u ρ : lowT M ρ) : M.sm ρ) : M.H ρ)⟫_ℂ =
          ∏ ρ, ⟪M.rep ρ (infMat D.sp.cm.sig W.gram (θ ρ) (a⁻¹ * g)) ((v' ρ : M.sm ρ) : M.H ρ),
            ((v ρ : M.sm ρ) : M.H ρ)⟫_ℂ :=
        Finset.prod_congr rfl fun ρ _ => by
          rw [hA τ k hk v u hu ρ, hrep, ContinuousLinearMap.comp_apply, hinv]
      rw [hp]
      exact this
  exact ⟨_, st2⟩

end GlobalTheory.RawLift.FockPair

namespace GlobalTheory.RawLift.FockPair

open GlobalTheory.DefLift GlobalTheory.RawLift Formalism.IndefR.FWT in

theorem coef_one_vector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), GlobalTheory.HolDict.HolShape M → (∃ wt, GlobalTheory.HolDict.WtIs M wt) → ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → GlobalTheory.RawLift.FockCoef.Killed om θ M (pt Δ) → ∀ w : c.W, ∃ N : ℂ, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w)) = N * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) := by
  intro D ψ θ S T χS χT om hθ hom Sp M hM hwt μ 𝓧 hcv c hc pt hpt Δ io hio hΔ w
  obtain ⟨wt, hw⟩ := hwt
  obtain ⟨hLS, hLI⟩ := GlobalTheory.HolLowOnce.lowSm_and_lowIrr D T Sp M hM
  let J : MultilinearMap ℂ (fun ρ => lowT M ρ) (WO S T → ℂ) :=
    (pt.comp (io.flip w)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hJv : ∀ v, J v = pt (io (PiTensorProduct.tprod ℂ v) w) := fun _ => rfl
  have hJ : ∀ v, IsThetaFunO ψ S T (J v) := fun v => hpt _
  obtain ⟨N, hN⟩ := pair_of_ext θ hθ M hLS hLI hom hcv J hJ
    (fun τ k hk v u hu => (hio.2.1 τ k hk v u hu w).symm)
    (fun v hv u hu => GlobalTheory.RawLift.FockCoef.coef_eq hom hcv hθ M hM hw hv (hpt _)
      (fun a ha => GlobalTheory.RawLift.FockCoef.holAd_coef hom hcv hθ M hM hw c hc pt hpt Δ io hio hΔ v hv w ha) u hu)
  refine ⟨N, fun g hg e e' => ?_⟩
  have hmem : realElt θ T g ∈ GinfC T := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hy
    exact GlobalTheory.PointAtPlaceHom.atTau_mem _ τ _
  have hinf : ∀ ρ, infMat D.sp.cm.sig T.gram (θ ρ) (realElt θ T g) = g ρ := fun ρ => by
    rw [realElt, GlobalTheory.RealTransSm.infMat_list_prod hθ g hg ρ _ (Finset.nodup_toList _),
      if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ))]
  have key := hN e' e _ hmem
  rw [hJv, hJv] at key
  simp only [hinf] at key
  rw [← key]
  show (∫ x in 𝓧, _ ∂μ) = ∫ x in 𝓧, _ ∂μ
  congr 1
  funext x
  rw [starRingEnd_apply, mul_comm]

end GlobalTheory.RawLift.FockPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormTranslateRealPointReadByPeriod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.TopTranslate

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift

theorem infM_eq_reindex {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn g τ = (infMat D.sp.cm.sig V.gram (θ τ) g).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

theorem infPt_eq_infM {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    ((infPt θ x τ : GL _ ℂ) : Matrix _ _ ℂ) = infM θ D.sp.X' (rankP D) x τ := by
  rw [infM_eq_reindex]
  exact GlobalTheory.Core.Rk.TopOnto.infN_eq (rankP D) x τ

theorem infPt_mul_inv {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    (infPt θ x τ).1 * (infPt θ x⁻¹ τ).1 = 1 := by
  rw [← Units.val_mul, ← Pi.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem top_translate : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ (f : CXP R P t) v c, ∀ x ∈ GinfC (I.rec7 l Z).sp.X', f.1 v (h c * x * g.bT) = (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) * (I.per l u a).period (eW.symm (Pi.single c fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩)) (G' f) := by
  intro B X I _ _ l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w _ UT ε _ bad K eW _ _ hbT _ _ h hh G' hG' f v c x hx
  obtain ⟨v', e1, e2⟩ := GlobalTheory.Core.Rk.TopOnto.real_translate (J := levS _ R.βX (datXP R P t))
    (χ := levChi _ R.βX (datXP R P t)) hX.inf hj x hx v
  have ex : h c * x * g.bT = h c * g.bT * x := by
    rw [mul_assoc, GlobalTheory.PointAtPlaceHom.comm_of_mem _ hx hbT, ← mul_assoc]
  have key : j v' = fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩ := by
    funext y
    have h1 : j v' y = j v (frL _ (infPt R.θ x⁻¹) y) := by
      rw [← e1, lT_apply]
      refine congrArg (j v') (Subtype.ext (funext fun τ => ?_))
      show y.1 τ = _ * (_ * y.1 τ)
      rw [← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
    rw [h1]
    refine (hJ v x hx ⟨(frL _ (infPt R.θ x⁻¹) y).1, (frL _ (infPt R.θ x⁻¹) y).2⟩ ⟨y.1, y.2⟩ fun τ => ?_).symm
    show y.1 τ = infM R.θ _ (rankP (I.rec7 l Z)) x τ * (_ * y.1 τ)
    rw [← infPt_eq_infM, ← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
  rw [ex, ← e2 f.1 f.2 (h c * g.bT), hG' f c v' (h c) (hh c), key]

end GlobalTheory.AdForm.TopTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GeneratorMemSplitPrimeLevelPrimeMemPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.GenOver

open GlobalTheory.AdForm.PlacesDistinct in

theorem mem_place_of_mem_prime {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hI : Formalism.L2.NTheta.IsIdemAt p.e w)
    (x : 𝓞 D.host.F) (y : 𝓞 D.host.E) (hxy : (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F))
    (hy : y ∈ w.asIdeal) : x ∈ p.v.asIdeal := by
  by_contra hxv
  have hx0 : x ≠ 0 := fun h => hxv (h ▸ p.v.asIdeal.zero_mem)
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    have : algebraMap D.host.F D.host.E (x : D.host.F) = 0 := by rw [← hxy, h]; rfl
    rw [map_eq_zero_iff _ (algebraMap D.host.F D.host.E).injective] at this
    exact RingOfIntegers.coe_eq_zero_iff.mp this
  apply (hI.2 y hy0).1 hy
  obtain ⟨ε, hε, hsum⟩ := p.above
  have he : p.e = p.e * algebraMap (AF D.host.F) (AE D) ε := by
    rw [← hsum, mul_add, p.split.1, p.split.2.1, add_zero]
  set c : AF D.host.F := algebraMap D.host.F (AF D.host.F) ((x : D.host.F)⁻¹) with hc
  have hinc : incA D ((y : D.host.E)⁻¹) = algebraMap (AF D.host.F) (AE D) c := by
    rw [hxy, ← map_inv₀, hc]
    show Algebra.TensorProduct.includeRight _ = _
    exact (Algebra.TensorProduct.includeRight.commutes _).trans (IsScalarTower.algebraMap_apply _ _ _ _)
  have h2 : finPart D (algebraMap (AF D.host.F) (AE D) (ε * c)) ∈ intAE D := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have hf : finPart D ((ε * c) ⊗ₜ[D.host.F] (1 : D.host.E)) = sndA D.host.F (ε * c) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hf]
    refine AddSubgroup.subset_closure ⟨sndA D.host.F (ε * c), ?_, 1, by simp⟩
    intro v'
    obtain ⟨α, rfl, h1, h0⟩ := hε
    have hs : sndA D.host.F (pairA D.host.F 0 α * c) = α * algebraMap D.host.F (Af D.host.F) ((x : D.host.F)⁻¹) := by
      rw [map_mul, hc, AlgHom.commutes]; rfl
    rw [hs, map_mul, AlgHom.commutes]
    by_cases hv : v' = p.v
    · subst hv
      rw [h1, one_mul, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀]
      have hv1 : Valued.v (algebraMap D.host.F (Fv D.host.F p.v) (x : D.host.F)) = 1 := by
        have := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := D.host.F) p.v x
        refine this.trans ?_
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        exact IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hxv
      rw [hv1, inv_one]
    · rw [h0 v' hv, zero_mul]
      exact zero_mem _
  rw [hinc, he, mul_assoc, ← map_mul, map_mul]
  exact FrameLat.mul_mem_intAE (finPart_idem_int hI) h2

theorem natCast_mem_place {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hI : Formalism.L2.NTheta.IsIdemAt p.e w) (n : ℕ)
    (hn : (n : 𝓞 D.host.E) ∈ w.asIdeal) : (n : 𝓞 D.host.F) ∈ p.v.asIdeal :=
  mem_place_of_mem_prime p hI (n : 𝓞 D.host.F) (n : 𝓞 D.host.E) (by simp) hn

end GlobalTheory.AdForm.GenOver

open GlobalTheory.AdForm.GenOver in

theorem GlobalTheory.AdForm.piT_mem_and_T_mem_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt (I.rec7 l Z) k) (P : (B.primes X).vT u), Formalism.L2.NTheta.IsIdemAt p.e P.1 → X.piT u ∈ P.1.asIdeal ∧ ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ p.v.asIdeal := by
  intro B X I _ l Z u k _ _ _ _ p P hI
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have h1 : X.piT u ∈ P.1.asIdeal := (Formalism.L2.Col.mem_divs (hPr.piT_ne_zero u) _).1 P.2
  have hT : ((B.T u : ℕ) : 𝓞 B.fields.E) ∈ P.1.asIdeal := by
    have : X.piT u * B.fields.conjO (X.piT u) = ((B.T u : ℕ) : 𝓞 B.fields.E) := hPr.piT_norm u
    rw [← this]
    exact Ideal.mul_mem_right _ _ h1
  exact ⟨h1, natCast_mem_place p hI (B.T u) hT⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAIdempotentComponentCocycleTrivialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfA_idempotent_component_cocycle_trivial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplOH S T ((LinearMap.toMatrix' x').map fun r => e * incA D r) ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r))) = 1 := by
  first | exact @GlobalTheory.AdForm.CocycleSS.cocycle_trivial | exact GlobalTheory.AdForm.CocycleSS.cocycle_trivial | (intros; apply GlobalTheory.AdForm.CocycleSS.cocycle_trivial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorHomSelfDualComponentsSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem isLattice_of_isLat_selfDual {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p S n) (L : Lat S) (hL : IsSelfDualC S L) (Λ : Submodule 𝒪[k] (n → k)) (h : β.IsLat L Λ) :
    Λ.IsLattice k := by
  obtain ⟨Λ₀, h₀, hI, -⟩ := (GlobalTheory.T.splitPlaceHermitianFrame_properties D k p S n β).2.2.2.1 L hL
  have e : Λ = Λ₀ := Submodule.ext fun x => (h x).trans (hI x).symm
  exact e ▸ h₀

theorem latInd_mem_SB_of_selfDual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat LS ΛS → β.IsLat LT ΛT → latInd ΛS ΛT ∈ SB (Matrix n n' k) := by
  intro D k _ _ _ _ p n n' _ _ _ _ S T α β LS LT hS hT ΛS ΛT hα hβ
  haveI := isLattice_of_isLat_selfDual α LS hS ΛS hα
  haveI := isLattice_of_isLat_selfDual β LT hT ΛT hβ
  exact GlobalTheory.LatPair.latInd_mem_SB ΛS ΛT

end GlobalTheory.FinPl
end

