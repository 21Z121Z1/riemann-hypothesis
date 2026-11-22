import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0114
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKerPD
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

variable {D : D7}

def kerPD (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A₁ : Fr W₁) (B : Fr X)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) {Pi : ModuleCat.{0} ℂ}
    (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) :
    Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :=
  Submodule.span ℂ {Φ₀D | Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧
    ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0}

theorem mem_kerPD {ψ : AddChar (AF D.host.F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (θ : InfFam D) {W W₁ X : HSp D}
    (A₁ : Fr W₁) (B : Fr X) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) {Pi : ModuleCat.{0} ℂ}
    (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi) (Φ₀D : (Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ) :
    Φ₀D ∈ kerPD ψ θ A₁ B Bs Γ cB p' ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧
      ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0 := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  have hl := isDatum_linear Γ.M' ψ hψ (⇑cB)
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, hl.1, map_zero p'⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx1, Φx, hΦx, hDx, hpx⟩ := hx
    obtain ⟨hy1, Φy, hΦy, hDy, hpy⟩ := hy
    refine ⟨Submodule.add_mem _ hx1 hy1, Φx + Φy, Submodule.add_mem _ hΦx hΦy, ?_, by rw [map_add, hpx, hpy, add_zero]⟩
    have := hl.2 x y Φx Φy 1 hDx hDy
    simpa using this
  | smul c x _ hx =>
    obtain ⟨hx1, Φx, hΦx, hDx, hpx⟩ := hx
    refine ⟨Submodule.smul_mem _ c hx1, c • Φx, Submodule.smul_mem _ c hΦx, ?_, by rw [map_smul, hpx, smul_zero]⟩
    have := hl.2 0 x 0 Φx c hl.1 hDx
    simpa using this

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSixth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DnLiftAut

theorem isAutFunSm_lift_dn : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.dn i).ω g h Φ * φ g) (G.mP (i + 1)).fd (G.mP (i + 1)).ν) → IsAutFunSm R.θ (G.P i).V (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i hi Φ hΦ φ hφ hint
  have hθ : IsInfFam R.θ := hR.inf
  have hW := (hG.arrows.dn i hi).weil
  have hκ := GlobalTheory.Mem.Lift.isKerSys_thKer hθ hW.std (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont
  have hm := hG.meas.P (i + 1) hi
  have hq0 : (G.mP (i + 1)).ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.P (i + 1)).V) (G.mP (i + 1)).fd (G.mP (i + 1)).ν := by
    by_cases hd : i + 1 = D.R.m
    · exact ⟨(hm.1 hd).1.1, (hm.1 hd).2⟩
    · exact ⟨(hm.2 hd).1.1, (hm.2 hd).2⟩
  obtain ⟨ν₁, hH, hF, hI⟩ := (GlobalTheory.SgnIdent.sgnLaw_holds D R.θ hθ true (G.P (i + 1)).V).meas _ _ hq0.1 hq0.2
  have hL' := GlobalTheory.SgnIdent.sgnLaw_holds D R.θ hθ true (G.P (i + 1)).V
  have hc : GlobalTheory.Mem.Th.IsCuspForm R.θ (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (fun g => φ (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V g)) :=
    ⟨(GlobalTheory.SgnFun.isAutFunSm_sgn_true hL' φ).2 hφ.1, (GlobalTheory.SgnFun.isCuspFun_sgn_true hL' φ).2 hφ.2.1⟩
  have key := hκ.lift hP.cuspRapidDecay hθ ⟨hH, hF⟩ hc ⟨Φ, hΦ⟩
  have e : (fun h => ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h Φ * φ g ∂(G.mP (i + 1)).ν) =
      fun h => ∫ g in GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V ⁻¹' (G.mP (i + 1)).fd,
        GlobalTheory.Mem.Lift.thKer R.ψ (GlobalTheory.Grid.sgn true (G.P (i + 1)).V) (G.P i).V ((G.dn i).ω.toSgn true) ⟨Φ, hΦ⟩ g h *
          φ (GlobalTheory.Grid.ofSgn true (G.P (i + 1)).V g) ∂ν₁ :=
    funext fun h => ((hI fun g => thetaKO (G.dn i).ω g h Φ * φ g).2).symm
  rw [e]
  exact key.2

end GlobalTheory.DnLiftAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspThetaConvX

theorem integrableOn_thetaKO_mul_cusp : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) := by
  intro _hL hP D _hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ h
  have hM := GlobalTheory.PairLift.haar_vert hRB hG t hi.le hj
  have : BorelSpace (GA D (G.V i j).V) := ⟨rfl⟩
  have hw := (hG.arrows.X i j hi hj).weil
  have hr : GlobalTheory.Grow.RapidDec (G.V i j).V φ :=
    GlobalTheory.Grow.rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf hφ.1 hφ.2.1
  have key := GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec (GlobalTheory.KernelSeminorm.thetaGrowth D) hRB.inf hw hΦ hM.1
    hM.2 hr ((GlobalTheory.Grid.ofSgn true _).symm h)
  convert key using 3 with g
  simp only [thetaKO, GlobalTheory.Grid.WRep.toSgn, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
    MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MonoidHom.id_apply]

end GlobalTheory.CuspThetaConvX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ArrowLiftAut

theorem isQuot_of_is {D : D7} {N : GlobalTheory.Grid.Node D} (m : N.MeasDat) (df : Prop)
    (K : Subgroup (GL (Fin N.V.rank) (Lev.EAf D))) (h : m.Is df K) :
    GlobalTheory.Mem.Th.IsQuot N.V m.ν m.fd := by
  by_cases hd : df
  · obtain ⟨⟨hH, -⟩, hF⟩ := h.1 hd
    exact And.intro hH hF
  · obtain ⟨⟨hH, -⟩, hF⟩ := h.2 hd
    exact And.intro hH hF

theorem isQuot_cast {D : D7} {S S' : GlobalTheory.Grid.Node D} (e : S = S') (m : S.MeasDat)
    (h : GlobalTheory.Mem.Th.IsQuot S.V m.ν m.fd) :
    GlobalTheory.Mem.Th.IsQuot S'.V (m.cast e).ν (m.cast e).fd := by
  subst e
  exact h

theorem lift_isAutFunSm (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {θ : InfFam D} (hθ : IsInfFam θ)
    {ψ : AddChar (AF ↥D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep S T}
    (hω : IsWeilDatumO ψ (GlobalTheory.Grid.sgn true S) T χS χT (GlobalTheory.Grid.WRep.toSgn true ω))
    {ν : Measure (GA D T)} {𝓕 : Set (GA D T)} (hq : GlobalTheory.Mem.Th.IsQuot T ν 𝓕)
    {Φ : WO (GlobalTheory.Grid.sgn true S) T → ℂ} (hΦ : IsThetaFunO ψ (GlobalTheory.Grid.sgn true S) T Φ)
    {φ : GA D T → ℂ} (hφ : IsAutFunSm θ T φ) (hφc : IsCuspFun T φ) :
    IsAutFunSm θ S (fun h => ∫ g in 𝓕, thetaKO ω h g Φ * φ g ∂ν) := by
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  have hK := (GlobalTheory.Mem.Lift.isKerSys_thKer hθ hω.std hW hω.om_cont).swap
  have hL := (GlobalTheory.Mem.Lift.IsKerSys.lift hCRD hθ hK hq ⟨hφ, hφc⟩ ⟨Φ, hΦ⟩).2
  exact ((GlobalTheory.sgn_fun_cusp D θ hθ true S (fun h => ∫ g in 𝓕, thetaKO ω h g Φ * φ g ∂ν)).1).1 hL

private theorem isQuot_Yc_nuY_fdY_of_base {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R) (t : T) (k : ℕ) (hk : k < D.R.m) :
    GlobalTheory.Mem.Th.IsQuot (Yc D k) (R.νY t k) (R.fdY t k) := by
  rcases Nat.lt_or_ge (k + 1) D.R.m with h | h
  · obtain ⟨⟨hH, -⟩, hF⟩ := hR.measY t k h
    exact And.intro hH hF
  · obtain rfl : k = D.R.m - 1 := by omega
    obtain ⟨⟨hH, -⟩, hF⟩ := hR.measY' t
    exact And.intro hH hF

theorem isQuot_meas {D : D7} {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {R : RealDat D A Ks} (G : GlobalTheory.Grid.GridPre R) (hR : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R) (hG : G.Is)
    (t : T) (i j : ℕ) (hi : i < D.R.m) (hj : j ≤ D.R.m) :
    GlobalTheory.Mem.Th.IsQuot (G.V i j).V (G.meas t i j).ν (G.meas t i j).fd := by
  have hM := hG.meas
  rcases i with _ | i
  · rcases j with _ | j
    · exact isQuot_of_is _ _ _ (hM.col 0 (Nat.zero_le _))
    · dsimp only [GlobalTheory.Grid.GridPre.meas, GlobalTheory.Grid.meas0]
      split_ifs with h1
      · exact isQuot_cast _ _ (isQuot_Yc_nuY_fdY_of_base R hR t (j + 1) h1)
      · refine isQuot_cast _ _ ?_
        obtain ⟨⟨hH, -⟩, hF⟩ := hR.measX t
        exact And.intro hH hF
  · rcases j with _ | j
    · exact isQuot_of_is _ _ _ (hM.col (i + 1) hi.le)
    · exact isQuot_of_is _ _ _ (hM.vert i j hi.le hj)

end GlobalTheory.ArrowLiftAut

namespace GlobalTheory.ArrowLiftAut

theorem liftX_isAutFunSm : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsAutFunSm R.θ (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj Φ hΦ φ hφ _
  exact lift_isAutFunSm hP.cuspRapidDecay hR.inf (hG.arrows.X i j hi hj).weil
    (isQuot_meas G hR hG t i j hi hj) hΦ hφ.1 hφ.2.1

end GlobalTheory.ArrowLiftAut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSqUnitaryEmbeddingOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

theorem norm_sq_unitaryEmbedding_add : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (Y V : HSp D) (d : HermitianOrthogonalExtensionData Y V 1 1) (A : Fr Y) (B : Fr V), Adapted d A B → ∀ (x : GA D Y) (τ : D.what₂.Tau) (y : Fin Y.rank → D.host.E) (u : D.host.E), nrm θ B (stabilizerEmbedding d x) τ (frameMat V Y d.ι *ᵥ y + u • zv d) ^ 2 = nrm θ A x τ y ^ 2 + ‖tauE D τ u‖ ^ 2 := by
  intro D θ hθ Y V d A B hAd x τ y u
  let φ : AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ :=
    (θ τ).comp (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hinc : ∀ e, φ (incA D e) = tauE D τ e := by
    intro e
    have := (hθ τ).1 e
    simpa [φ, incA, inclR] using this
  have hcmp : ∀ {W : HSp D} (g : GA D W), cmp θ τ g = (matHom W g).1.map φ := by
    intro W g; rfl
  have hinv : (stabilizerEmbedding d x)⁻¹ = stabilizerEmbedding d x⁻¹ :=
    (map_inv (MonoidHom.mk' (stabilizerEmbedding d) (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d)) x).symm
  set P := (frameMat V Y d.ι).map (tauE D τ) with hP
  set Q := (GlobalTheory.UnitaryEmbeddingProperties.qM d).map (tauE D τ) with hQ
  have key : cmp θ τ (stabilizerEmbedding d x)⁻¹ = GlobalTheory.UnitaryEmbeddingProperties.ex P Q (cmp θ τ x⁻¹) := by
    rw [hinv, hcmp, hcmp, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_matrix_formula, GlobalTheory.UnitaryEmbeddingProperties.ex_map, Matrix.map_map, Matrix.map_map]
    have hf : (⇑φ ∘ ⇑(incA D)) = ⇑(tauE D τ) := funext hinc
    rw [hf]
  have hQP : Q * P = 1 := GlobalTheory.UnitaryEmbeddingProperties.qM_mul_map (tauE D τ) d
  have hQz0 : GlobalTheory.UnitaryEmbeddingProperties.qM d *ᵥ zv d = 0 := by
    have hp := d.perp
    have h0 : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat V Y d.ι) * V.gram) *ᵥ zv d = 0 := by
      funext i
      have := congr_fun (congr_fun hp i) 0
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, zv] using this
    rw [GlobalTheory.UnitaryEmbeddingProperties.qM, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have hQz : Q *ᵥ (fun i => tauE D τ (zv d i)) = 0 := by
    funext i
    have := congr_fun hQz0 i
    rw [hQ]
    change ((GlobalTheory.UnitaryEmbeddingProperties.qM d).map (tauE D τ) *ᵥ (⇑(tauE D τ) ∘ zv d)) i = 0
    rw [← RingHom.map_mulVec, this]
    exact map_zero _
  have hvec : (fun i => tauE D τ ((frameMat V Y d.ι *ᵥ y + u • zv d) i)) =
      P *ᵥ (fun i => tauE D τ (y i)) + tauE D τ u • fun i => tauE D τ (zv d i) := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hP, RingHom.map_mulVec]
    rfl
  have hex : ∀ (h : Matrix (Fin Y.rank) (Fin Y.rank) ℂ) (w : Fin Y.rank → ℂ) (a : ℂ),
      GlobalTheory.UnitaryEmbeddingProperties.ex P Q h *ᵥ (P *ᵥ w + a • fun i => tauE D τ (zv d i)) =
        P *ᵥ (h *ᵥ w) + a • fun i => tauE D τ (zv d i) := by
    intro h w a
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, GlobalTheory.UnitaryEmbeddingProperties.ex_mul_P P Q hQP,
      ← Matrix.mulVec_mulVec]
    congr 2
    rw [GlobalTheory.UnitaryEmbeddingProperties.ex, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hQz,
      Matrix.mulVec_zero, add_zero]
  unfold nrm
  rw [key, hvec, hex]
  exact hAd τ _ _

end GlobalTheory.SepPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedDefiniteKernelEntriesIsAlgebraic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj
open Formalism.L2.Ker MvPolynomial

noncomputable section

namespace GlobalTheory.KernelAlg

open GlobalTheory.ThetaAlgebraic in

theorem coefIn_dict (D : D7) (hI : GlobalTheory.NormSum.Inp D) {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : StandardLatticesGL3.Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t0) {N N' : ℕ} (e0 : TaylorLogMetric.VC D N N' → ℂ)
    (he : StandardLatticesGL3.ThetaVectorUpToUnits D (TaylorLogMetric.tor0 D cc δ) t0 (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') e0)
    (Ls : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (κ : ℂ) (hκ : κ ∈ TaylorLogMetric.Qbar) {n : ℕ} (r : Fin n → TaylorLogMetric.Qbar) (s : Fin n → TaylorLogMetric.VC D N N') (k : ℕ) (hk : 0 < k)
    (hs : ∀ i, k • s i ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt) :
    TaylorLogMetric.CoefIn D (fun z => κ * ∑ i, (r i : ℂ) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt) e0) z) TaylorLogMetric.Qbar := by
  obtain ⟨b, κ0, hb, hκ0, rfl⟩ := he
  have hG := hI.g1
  have hU := hI.use1
  have hg := ((good_theta hG hU hC hb ht).iop hG hC hb (StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) b) _
    (la_le cc δ hG hb (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).const_mul hκ0.1
  have hg2 := hg.iop hG hC hb (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') _ (la_le cc δ hG hb Ls Lt)
  have hT : ∀ i, Good cc δ b (TaylorLogMetric.U D (TaylorLogMetric.tor0 D cc δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D cc δ) N N') (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Ls Lt)
        fun z => κ0 * TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.LaB D (TaylorLogMetric.tor0 D cc δ) b) (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
          (StandardLatticesGL3.pullB D (TaylorLogMetric.tor0 D cc δ) b (GL3Theta.th0 (TaylorLogMetric.lamOf D cc δ) t0)) z)) := fun i =>
    hg2.transl hG hC hb (sat_of_nsmul hk (la_le cc δ hG hb Ls Lt (hs i)))
  exact ((Good.sum Finset.univ _ fun i _ => (hT i).const_mul (r i).2).const_mul hκ).coefIn

theorem applyAt0_monomial_mem (D : D7) {N N' : ℕ} (m : GL3Theta.Idx D N N' →₀ ℕ) {G : TaylorLogMetric.VC D N N' → ℂ}
    (hG : TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar) : GL3Theta.applyAt0 D (MvPolynomial.monomial m 1) G ∈ TaylorLogMetric.Qbar := by
  classical
  unfold GL3Theta.applyAt0
  refine sum_mem fun α _ => mul_mem (mul_mem ?_ (prod_mem fun _ _ => natCast_mem _ _)) (hG α)
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem opp_isAlgebraic {T : Type} (p : GlobalTheory.ChiGrid.Pair T) {z : ℂ} (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ (opp p z) :=
  IsAlgebraic.algHom (opp p).toRatAlgHom hz

theorem fvar_fst {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : ChiGrid.GridData L sc) (p : GlobalTheory.ChiGrid.Pair T)
    (k : DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank) : (fvar G p k).1 = k.1 := by
  cases p <;> rfl

theorem kk_isAlgebraic : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ∀ (ch : Choice R), ch.Is → GlobalTheory.NormSum.Inp D → GlobalTheory.SumSize.DictAt ch → ∀ (t : T) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → WtOK ch.G p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl ch.G t → ch.S.Z.HasVec d → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (a : VVIdx (wt ch.G p.big)) (b : VVIdx (wt ch.G p.small)), IsAlgebraic ℚ (ch.S.Z.kk d x y a b) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R large₂ F hS ch hch hInp hDict t p hp hW k d hk hcos hz hP hV x y a b
  obtain ⟨Ls, Lt, κ, n, r, s, hLs, hLt, hκ, hs, -, -, -, hJ⟩ := hDict t p hp k d hk hcos hz hP x y
  set Z := ch.S.Z
  have hF := coefIn_dict D hInp Z.crv Z.pt0 (Z.e0 p) (Z.e0_is p hp).2.2.2.1 Ls Lt κ hκ.1 r s k hk hs
  set FF := (fun z => κ * ∑ i, ((r i : TaylorLogMetric.Qbar) : ℂ) * TaylorLogMetric.U D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) (s i)
      (TaylorLogMetric.Iop D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) (StandardLatticesGL3.La0 D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) _ _)
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D D.host.ccK Z.δ) Ls Lt) (Z.e0 p)) z) with hFF
  set J2 : (DVar D.what₂.Tau (ch.G.V p.small).rank (ch.G.V p.big).rank →₀ ℕ) → ℂ := fun m =>
    opp p (GL3Theta.applyAt0 D (MvPolynomial.monomial (m.mapDomain (fvar ch.G p)) 1) FF) with hJ2
  have hA : ∀ m, IsAlgebraic ℚ (J2 m) := fun m =>
    opp_isAlgebraic p (mem_algebraicClosure_iff.1 (applyAt0_monomial_mem D _ hF))
  set c : D.what₂.Tau → ℂ := fun τ => opp p (period Z.δ τ) with hc
  have hJf : jetTab ch.W ch.S.N.frC p (Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _) =
      fun m => (Z.c0 p : ℂ) * ((m.prod fun k e => c k.1 ^ e) * J2 m) := by
    funext m
    rw [hJ m, map_mul]
    congr 2
    rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), map_finsuppProd]
    simp only [map_pow, fvar_fst, hc]
  have hop : ∀ P : Formalism.L2.DIV.VV ℂ (wt ch.G p.small),
      jetOp (wt ch.G p.small) (wt ch.G p.big) (jetTab ch.W ch.S.N.frC p (Z.vec d) (x * ch.S.N.u _) (y * ch.S.N.u _))
        (nuEnd ch.G p) P = ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) • jetOp _ _ J2 (nuEnd ch.G p) P := by
    intro P
    rw [hJf]
    simp only [jetOp, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [GlobalTheory.T.thetaJetMap_weighted_table_scale, GlobalTheory.T.blockAction_diagonal_coefficientSpace_smul _ _ _ (hW.2 J2 P.1 P.2), smul_smul, map_smul]
    rfl
  simp only [Normal.kk, Normal.kkIn, Normal.kkMap, LinearMap.toMatrix_apply, LinearMap.smul_apply, fockComp]
  rw [hop, map_smul, map_smul]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  have hR := GlobalTheory.T.jetOperator_bideterminantBasis_repr_isAlgebraic _ _ J2 (nuEnd ch.G p) hA hW.2 a b
  have e : Z.scal 1 p * ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) =
      ∏ τ, opp p ((1 / period Z.δ τ) * period Z.δ τ) ^ fockDeg ch.G p τ := by
    simp only [Normal.scal, Pi.one_apply, hc, map_mul, mul_pow, Finset.prod_mul_distrib]
    rw [mul_mul_mul_comm, Units.inv_mul, one_mul]
  have hK : Z.scal 1 p * ((Z.c0 p : ℂ) * ∏ τ, c τ ^ fockDeg ch.G p τ) ∈ TaylorLogMetric.Qbar := by
    rw [e]
    refine prod_mem fun τ _ => pow_mem ?_ _
    rw [mem_algebraicClosure_iff]
    apply opp_isAlgebraic
    by_cases h : period Z.δ τ = 0
    · simp [h, isAlgebraic_zero]
    · simp [h, isAlgebraic_one]
  rw [← mul_assoc, ← mem_algebraicClosure_iff]
  exact mul_mem hK (mem_algebraicClosure_iff.2 hR)

end GlobalTheory.KernelAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

abbrev Arr (D : D7) : Type := Fin D.R.m ⊕ Fin D.R.m

def arrP (t : T) : Arr D → Pair T
  | .inl j => .top t j
  | .inr i => .chi i D.R.m

variable (G) in

abbrev Vecs (t : T) : Type := ∀ a : Arr D, WO (G.pS (arrP t a)) (G.pT (arrP t a)) → ℂ

def vecsOf (S : GridChoice W U) {t : T} (d : PureDat G t) : Vecs G t
  | .inl j => S.Z.vec (d.1 j)
  | .inr i => S.Z.vec (d.2 i)

def kkVec (S : GridChoice W U) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  S.Z.scal 1 p • fockComp W S.N.frC p f (x * S.N.u _) (y * S.N.u _)

def colV (S : GridChoice W U) {t : T} (fs : Vecs G t) (x : ∀ j, FinPt G (.top j)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then kkVec S (.top t j) (fs (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowV (S : GridChoice W U) {t : T} (fs : Vecs G t) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then kkVec S (.chi i D.R.m) (fs (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairVec (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (fs : Vecs G t) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂ (colV S fs x) (rowV S fs y)

theorem pairPts_eq (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) (v w) :
    pairPts S τ x y v w = τ.sum fun d a => a * pairVec S x y (vecsOf S d) v w := by
  unfold pairPts Finsupp.sum
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

def first : Arr D := .inl ⟨0, by have := D.R.two_le_m; omega⟩

def moveFirst (W : G.Weil) {t : T} (g : FinPt G (.top 0)) (fs : Vecs G t) : Vecs G t :=
  Function.update fs first (W.om (.top t 0) (G.toPair (.top t 0) g.1 1) (fs first))

end GlobalTheory.TopZeroInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodsOnLineOfInvLine
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def InvLine (ch : Choice R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (S : Sizes) (P : ι → Entries S), (∀ τ, (P τ).Good) ∧
    ∃ e : PolCol ch.G × PolRow ch.G → OM P, ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support, ∀ y,
        ∃ l ∈ invFun (omRep P), ∀ Q, defPer t ch.S.toGridChoice M Q d (colFn ch a) (formTop ch t y) = l (e Q)

theorem periodsOnLine_of_invLine (hL : OneLine) (ch : Choice R) (h : InvLine ch) : PeriodsOnLine ch := by
  obtain ⟨ι, _, _, S, P, hP, e, he⟩ := h
  haveI : Module.Free ℂ (invFun (omRep P)) := Module.Free.of_divisionRing ℂ _
  obtain ⟨L0, -, hL0⟩ := finrank_eq_one_iff'.1 (hL ι S P hP)
  refine ⟨fun Q => L0.1 (e Q), fun t a hS β hβ M hM τ hτ d hd y => ?_⟩
  obtain ⟨l, hl, hle⟩ := he t a hS β hβ M hM τ hτ d hd y
  obtain ⟨c, hc⟩ := hL0 ⟨l, hl⟩
  refine ⟨c, fun Q => ?_⟩
  have hc' : c • L0.1 = l := congrArg Subtype.val hc
  rw [hle Q, ← hc']
  rfl

end GlobalTheory.RowReal

end
end

