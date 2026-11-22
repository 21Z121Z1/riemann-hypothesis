import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0966
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0967
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0968
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0943
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0842
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterisationTransferMovedReadings
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def rhoEquiv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) : M ≃ₗ[K] M :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_rho {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g g' : G) (x : M) :
    ρ g (ρ g' x) = ρ (g * g') x := by rw [map_mul]; rfl

theorem rho_inv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) (x : M) :
    ρ g (ρ g⁻¹ x) = x := by rw [rho_rho, mul_inv_cancel, map_one]; rfl

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ)

abbrev realDatMovedReadingsKeepScalars : RealDat3 D A3 Ks := ⟨moveR Rl.toRealDat w, Rl.plI, Rl.SF, Rl.phs, Rl.lam3⟩

variable (kap : ℝ) (lam : type_of% Rl.lam3)

abbrev fullHeckeRealDatMovedReadings : RealDat3 D A3 Ks := (realDatMovedReadingsKeepScalars Rl w).updS kap lam

variable {Rl w kap lam}

set_option maxHeartbeats 4000000 in

theorem heckeCharacterisation_transfer_movedReadings {F : Face3 D A3} (h : Rl.Char3 F) (hs : (fullHeckeRealDatMovedReadings Rl w kap lam).IsScal F) : (fullHeckeRealDatMovedReadings Rl w kap lam).Char3 F := by
  obtain ⟨h1, h2, h5, hi, h6, h7, h8, f1, f2, f3, -, ht, hp, ha⟩ := h
  refine ⟨h1, ⟨h2.1, h2.2, h2.3, h2.4, h2.5⟩, ?_, ⟨hi.1, hi.2, hi.3, hi.4, hi.5⟩, ?_, ?_, ?_, f1, f2, f3, hs,
    ⟨ht.1, ht.2, ht.3, ht.4, ht.5⟩, fun i => ⟨(hp i).1, fun hc x => ?_⟩, ha⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩
  · obtain ⟨c, hc1, hc2⟩ := hc
    obtain ⟨y, hy⟩ := (hp i).2 ⟨c, hc1, fun x => (hc2 x).elim fun y hy => ⟨(Rl.FW i).ρ (w i (sg0 D A3.A)) y, hy⟩⟩ x
    exact ⟨(Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ y, (congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ y)).trans hy⟩

variable {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (w)

abbrev moveS : NX.RatDat D.ntw :=
  { S with
    A := fun n => moveForms (S.A n) fun σ =>
      (YS.fi (NX.idxOf D n)).eG.symm (w (NX.idxOf D n) σ * (w (NX.idxOf D n) (sg0 D A3.A))⁻¹) }

variable {w} (kap lam) (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)

def moveIso (i : Fin D.R.m) : NX.FormsIso ((moveS w YS).A ((i : ℕ) + 1)) ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i) where
  eK := (YS.fi i).eK
  eK_LL := (YS.fi i).eK_LL
  e := (YS.fi i).e.trans (rhoEquiv (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹)
  eG := (YS.fi i).eG
  eW := (YS.fi i).eW
  wk x := ((YS.fi i).wk x).trans ⟨(hst i _ _).1, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).1 h⟩
  mkK x := ((YS.fi i).mkK x).trans ⟨(hst i _ _).2, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).2 h⟩
  rho g x := by
    change (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e ((S.A _).ρ g x)) =
      (Rl.FW i).ρ ((YS.fi i).eG g) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))
    rw [(YS.fi i).rho, rho_rho, rho_rho, Subgroup.mem_center_iff.1 (inv_mem (hw i _))]
  chi := (YS.fi i).chi
  j σ x := by
    change (Rl.FW i).j σ ((Rl.FW i).ρ (w i σ) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))) =
      (YS.fi i).eW σ ((S.A _).j σ ((S.A _).ρ ((YS.fi (NX.idxOf D ((i : ℕ) + 1))).eG.symm
        (w (NX.idxOf D ((i : ℕ) + 1)) σ * (w (NX.idxOf D ((i : ℕ) + 1)) (sg0 D A3.A))⁻¹)) x))
    rw [NX.idxOf_succ, ← (YS.fi i).j, (YS.fi i).rho, MulEquiv.apply_symm_apply, rho_rho]

def moveYS : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) where
  fi := moveIso kap lam YS hw hst
  geq := YS.geq
  rho := YS.rho
  chi := YS.chi
  eF := YS.eF
  bsup := YS.bsup
  act := YS.act

theorem j_moveYS (i : Fin D.R.m) (x : S.WL ((i : ℕ) + 1)) :
    ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i).j (sg0 D A3.A) (((moveYS kap lam YS hw hst).fi i).e x) =
      (Rl.FW i).j (sg0 D A3.A) ((YS.fi i).e x) :=
  congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ _)

def moveH (H : NX.NExpRealH Rl cG S YS) : NX.NExpRealH (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) where
  hL := H.hL
  hs := H.hs
  cHk := H.cHk
  cHk_zero := H.cHk_zero
  cHk_unit := H.cHk_unit
  cHk_pow := H.cHk_pow
  hkEq := H.hkEq

theorem reads_move {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} (h : GlobalTheory.ExportPin.Reads Rl cG S YS hL) :
    GlobalTheory.ExportPin.Reads (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) hL := by
  intro i k P h1 h2 h3 α R h4 h5 x
  rw [j_moveYS, j_moveYS]
  exact h i k P h1 h2 h3 α R h4 h5 x

variable (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem realRd_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ) :
    realRd (moveYS kap lam YS hw hst) v₀ hρ i j b ν = realRd YS v₀ hρ i j b ν := by
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      evK (moveYS kap lam YS hw hst) v₀ hρ i j b x = evK YS v₀ hρ i j b x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
    | tmul a f =>
      exact congrArg (fun y => ρ.e i b a • (Rl.HW j (sg0 D A3.A)).e y (v₀ j _)) (j_moveYS kap lam YS hw hst j (Subtype.val f))
  exact LinearMap.ext fun f => congrArg (ν⁻¹ • ·) (key _)

theorem ratRow_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    RatRow (moveYS kap lam YS hw hst) v₀ hρ i j b ↔ RatRow YS v₀ hρ i j b :=
  exists_congr fun ν => and_congr Iff.rfl (by rw [realRd_move])

variable {YS v₀}

theorem rd_move (Z : ExportTie YS v₀) :
    (fun i j b => realRd (moveYS kap lam YS hw hst) v₀ Z.good i j b (Z.ν i j b) : Rds D.nexp Z.ρ) = Z.rd :=
  funext fun i => funext fun j => funext fun b => realRd_move kap lam YS hw hst v₀ Z.good i j b _

end GlobalTheory.Unframe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockScalarLinearSubstitutionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_act_fock_scalar_linear_substitution : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (t : T), ∀ u ∈ GinfC (Vc D i), ∃ (c : ℂ) (g : GLR D (Vc D i).rank), ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = c • R.ptP i t (fockSubst (pS D i) g P) := by
  first | exact @GlobalTheory.RealFockSubst.om_ptP_subst | exact GlobalTheory.RealFockSubst.om_ptP_subst | (intros; apply GlobalTheory.RealFockSubst.om_ptP_subst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockScalarUnitarySubstitutionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_act_fock_scalar_unitary_substitution : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := by
  first | exact @GlobalTheory.RealFockActionFree.om_ptP_inf | exact GlobalTheory.RealFockActionFree.om_ptP_inf | (intros; apply GlobalTheory.RealFockActionFree.om_ptP_inf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReferenceTupleLiftsEquivariantRootOfUnity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option autoImplicit false

namespace GlobalTheory.ConjRefLift

section Scale

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

theorem conjFun_scale (O : OMDat T.toCore R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (τ : ℂ ≃+* ℂ) {c : ℂ} (hc : c ≠ 0)
    {Ψ Ψ' Φ Φ' : GA D (Wc D i) → ℂ} (h : ConjFun O κ τ 1 Ψ Ψ') (e : ∀ g, Φ g = c⁻¹ * Ψ g)
    (e' : ∀ g, Φ' g = (τ c)⁻¹ * Ψ' g) : ConjFun O κ τ 1 Φ Φ' := by
  obtain ⟨⟨n, a, f, ha⟩, hall⟩ := h
  have hτc : τ c ≠ 0 := (map_ne_zero τ).2 hc
  refine ⟨⟨n, fun k => c⁻¹ * a k, f, fun g => ?_⟩, fun m b f' hb g => ?_⟩
  · rw [e g, ha g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · have hb' : Expands O κ Ψ (fun k => c * b k) f' := fun g => by
      have h1 := hb g
      rw [e g] at h1
      have h2 : Ψ g = c * (c⁻¹ * Ψ g) := by field_simp
      rw [h2, h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e' g, hall m _ f' hb' g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_mul, one_mul]
    field_simp

theorem conjFun_congr {Tp' : Type} {tup' : Tp' → T0} (O : OMDat T.toCore R i Tp tup) (O' : OMDat T.toCore R i Tp' tup')
    {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {τ : ℂ ≃+* ℂ} {ζ : ℂ} {Φ Φ' : GA D (Wc D i) → ℂ}
    (hphi : O.phi (T.cE ((i : ℕ) + 1) O.s0) = O'.phi (T.cE ((i : ℕ) + 1) O'.s0)) (h : ConjFun O κ τ ζ Φ Φ') :
    ConjFun O' κ τ ζ Φ Φ' := by
  unfold ConjFun Expands at h ⊢
  rw [← hphi]
  exact h

end Scale

set_option maxHeartbeats 2000000 in

theorem conjFun_lifts_root : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → M.lev = (O i).lev → (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) → Normal ℚ M.c'.F → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) → (∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e) → ∀ c₀ : M.c'.F, IsRoot1 ((c₀ : M.c'.F) : ℂ) → (∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (x x' : M.Cl' A.μ0 → VsV D i M.c'.F), (∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k))) → ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank, GlobalTheory.OneMapAll.IsSum M A.μ0 x f → (ta c₀ * c₀⁻¹)⁻¹ • galRul hf f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank ∧ GlobalTheory.OneMapAll.IsSum M A.μ0 x' ((ta c₀ * c₀⁻¹)⁻¹ • galRul hf f)) → ∃ ζ₁ : ℂ, IsRoot1 ζ₁ ∧ ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (y y' : (R.HV i A.μ0).H), (∀ h : GA D (Vc D i), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i A.μ0).e y (fin _ h) = M.c0' x ∧ (R.HV i A.μ0).e y' (fin _ h) = M.c0' x') → ConjFun (O i) (κ i) τ 1 (fun g => ζ₁ * ph i * R.thF i A.μ0 y (v₀ i (sg0 D A)) g) (fun g => ζ₁ * ph i * R.thF i A.μ0 y' (v₀ i (sg0 D A)) g) := by
  intro hC D G _ _ Pl0 T0 A T _ R F κ v₀ O ph hnV hcore hfin hfw hio hQ i hpins hphase M hMp hMl hMe hMn hMc hMx hMs c₀ hc₀ hc₀P
  obtain ⟨fw⟩ := hfw
  have hT : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hrow0 := GlobalTheory.T.thetaOneMap_baseTuple_of_characterisation_extremal hC D G Pl0 T0 A T R F κ v₀ hcore hT hio O i hpins
  have hEqO := (hphase hrow0).1
  have elev : M.lev2 = (O i).lev2 := by funext g; simp only [OMDat.lev2, hMl]
  have hEq : M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) := by
    unfold OMDat.EquivAt
    rw [GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1)), elev]
    exact hEqO
  obtain ⟨ζ, z, hζ, -, hser⟩ :=
    GlobalTheory.T.oneMap_every_normalisedFamily_at_coreConstants hC D G Pl0 T0 A T R F κ v₀ O ph hnV hcore hfin ⟨fw⟩ hio hQ i hpins hphase T0 id M hMp hMl hMe
  obtain ⟨nζ, hnζ, hζn⟩ := hζ
  obtain ⟨nc, hnc, hcn⟩ := hc₀
  have hζ0 : ζ ≠ 0 := fun h0 => by simp [h0, hnζ.ne'] at hζn
  have hc0 : ((c₀ : M.c'.F) : ℂ) ≠ 0 := fun h0 => by simp [h0, hnc.ne'] at hcn
  refine ⟨(ζ * (c₀ : ℂ))⁻¹, ⟨nζ * nc, Nat.mul_pos hnζ hnc, ?_⟩, fun τ ta hta hB y y' hyy => ?_⟩
  · rw [inv_pow, mul_pow, pow_mul, hζn, one_pow, mul_comm nζ nc, pow_mul, hcn, one_pow, mul_one, inv_one]
  have hf : Fixes M.c' ta :=
    fixes_of_le (c := T.Q.c) ta fun x hx => Subtype.ext ((hta x).trans (hB.core ⟨x, hx⟩))
  obtain ⟨h, J', hR, -⟩ := (hMp.tuple A.μ0).reps
  choose x x' hxx hx hx' using fun k => hyy (h k)
  have hio' : ∀ k, M.io (x' k) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (M.io (x k)) := fun k =>
    GlobalTheory.T.coefficientMap_commutes_fieldAutomorphism D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hMp τ ta hta hB (x k) (x' k) (hxx k)
  have hex := GlobalTheory.ClassSumRule.exists_cusp_isThClsD_core hC D G Pl0 T0 A T R F κ v₀ hcore hT i T0 id M hMp A.μ0 x
  obtain ⟨f, hf2⟩ := hex
  have hfc := hf2.1
  have hfs := hf2.2
  have hfsec : f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) M.c' (wtA (κ i)) (Vc D i).rank := ((mem_cusp _ _ _ _ _ _).1 hfc).1
  have hP' := hc₀P τ ta hta hB hf x x' hio' f hfsec hfs
  have e1 := hser A.μ0 h J' hR y x hx f hfsec hfs
  have e2 := hser A.μ0 h J' hR y' x' hx' _ hP'.1 hP'.2
  dsimp only [id_eq] at e1 e2
  have hCM := GlobalTheory.T.cuspFormReading_galoisConj_expansion D G Pl0 T0 A T R F κ v₀ hcore ⟨fw⟩ i T0 id M hMp τ ta hta hB hf z f hfc hEq
  have hsm : ∀ (s : M.c'.F) (Fr : Rul (T.Q.Xo ((i : ℕ) + 1)) M.c') a b,
      rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (s • Fr)) a b =
        inC M.c' s * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z Fr) a b := by
    intro s Fr a b
    rw [map_smul, map_smulₛₗ]
    rfl
  have hcv : inC M.c' c₀ = (c₀ : ℂ) := rfl
  have htv : inC M.c' (ta c₀) = τ (c₀ : ℂ) := hta c₀
  have hτ0 : τ (c₀ : ℂ) ≠ 0 := (map_ne_zero τ).2 hc0
  refine conjFun_scale (O i) (κ i) τ hc0 (conjFun_congr M (O i) (GlobalTheory.OneMapAll.phi_eq M (O i) (T.cE ((i : ℕ) + 1))) hCM)
    (fun g => ?_) (fun g => ?_)
  · beta_reduce
    rw [mul_assoc, e1 g]
    field_simp
  · beta_reduce
    have hs := hsm ((ta c₀ * c₀⁻¹)⁻¹) (galRul hf f) (M.dict g).1 (M.dict g).2
    rw [mul_assoc, e2 g]
    erw [hs]
    rw [map_inv₀, map_mul, map_inv₀, hcv, htv]
    field_simp

end GlobalTheory.ConjRefLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceIdempotentEqCompletionEmbeddingOneStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_idempotent_eq_completionEmbedding_one : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ι : P.adicCompletion D.host.E →+ AE D, GlobalTheory.DivPtLocal.IsIotaAt (rfl : P.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) ι → e = ι 1 := by
  first | exact @GlobalTheory.IdemIota.idemAt_eq_iota_one | exact GlobalTheory.IdemIota.idemAt_eq_iota_one | (intros; apply GlobalTheory.IdemIota.idemAt_eq_iota_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLawsOfSides
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem supLaws_of_sides (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E)
    (h : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) :
    SupG D ∧ SupFull D ∧ SupHk D ∧ CommG D ∧ HkComm D := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.twistedFormSupLattice_full_groupStable_of_eq_rational D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS Y.sup X.integral
  obtain ⟨h3, h4⟩ := GlobalTheory.T.hecke_preserves_supLattice_and_commutes_typeGroup D X E Y h
  exact ⟨h1, h2, h3, h4, GlobalTheory.T.splitPlaceHeckeCommute_of_twistSeriesSideData D X E Y⟩

end GlobalTheory.TwInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceIntegralOfSmallAtOtherPlaces
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero

namespace GlobalTheory.TraceSmall

theorem valV_le_one_of_ext {T T' : CDVR} (i : T.Fr →+* T'.Fr) {e' : ℕ} (he' : 0 < e')
    (hv : ∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) (z : T.Fr) :
    valV T'.V (i z) ≤ 1 ↔ valV T.V z ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have h1 : valV T'.V (i z) ≠ 0 := valV_ne_zero ((map_ne_zero i).2 hz)
  have h2 : valV T.V z ≠ 0 := valV_ne_zero hz
  have h := hv z hz
  have he : (0 : ℤ) < e' := by exact_mod_cast he'
  rw [← WithZero.log_le_log h1 one_ne_zero, ← WithZero.log_le_log h2 one_ne_zero, WithZero.log_one]
  unfold vV at h
  constructor <;> intro h' <;> nlinarith

theorem exists_bound {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (p : HeightOneSpectrum (𝓞 K)) {m : ℕ} (y : Fin m → L) :
    ∃ N : ℕ, ∀ la' : HeightOneSpectrum (𝓞 L), la'.asIdeal.under (𝓞 K) = p.asIdeal → ∀ k,
      la'.valuation L (y k) ≤ WithZero.exp (N : ℤ) := by
  have hS : {la' : HeightOneSpectrum (𝓞 L) | la'.asIdeal.under (𝓞 K) = p.asIdeal}.Finite := by
    refine (Set.Finite.preimage (f := fun la' : HeightOneSpectrum (𝓞 L) => la'.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)
      (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 L))).subset fun la' h => ?_
    exact ⟨la'.isPrime, ⟨h.symm⟩⟩
  obtain ⟨B, hB⟩ := ((hS.prod (Set.finite_univ (α := Fin m))).image
    fun q : HeightOneSpectrum (𝓞 L) × Fin m => WithZero.log (q.1.valuation L (y q.2))).bddAbove
  refine ⟨B.toNat, fun la' h k => ?_⟩
  by_cases hy : y k = 0
  · simp [hy]
  have h0 : la'.valuation L (y k) ≠ 0 := by simpa using hy
  have := hB ⟨(la', k), ⟨h, Set.mem_univ _⟩, rfl⟩
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
  simp only at this
  omega

theorem valuation_le_of_mem {L : Type} [Field L] [NumberField L] (la' : HeightOneSpectrum (𝓞 L)) {N : ℕ}
    {b : 𝓞 L} (hb : b ∈ la'.asIdeal ^ N) : la'.valuation L (b : L) ≤ WithZero.exp (-(N : ℤ)) :=
  (la'.valuation_of_algebraMap b).trans_le ((la'.intValuation_le_pow_iff_mem b N).2 hb)

theorem trace_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (p : HeightOneSpectrum (𝓞 K)) (la : HeightOneSpectrum (𝓞 L)), la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ (m : ℕ) (y : Fin m → L), ∃ N : ℕ, ∀ b : 𝓞 L, (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal → b ∈ la'.asIdeal ^ N) → ∀ (T : CDVR), T.FinRes → ∀ (io : K →+* T.Fr) (e : ℕ), OverLa p T.V io e → ∀ x : Fin m → T.Fr, (∀ k, valV T.V (x k) ≤ 1) → (∀ (T' : CDVR) (i : T.Fr →+* T'.Fr) (e' : ℕ) (τ : L →+* T'.Fr) (e'' : ℕ), 0 < e' → (∀ z : T.Fr, z ≠ 0 → vV T'.V (i z) = (e' : ℤ) * vV T.V z) → T'.FinRes → (∀ z : K, τ (algebraMap K L z) = i (io z)) → OverLa la T'.V τ e'' → valV T'.V (∑ k, τ (y k) * i (x k)) ≤ 1) → valV T.V (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) ≤ 1 := by
  intro K L _ _ _ _ _ p la hla m y
  obtain ⟨N, hN⟩ := exists_bound p y
  refine ⟨N, fun b hb T hT io e ho x hx H => ?_⟩
  let Ω := AlgebraicClosure L
  let F := IntermediateField.normalClosure K L Ω
  obtain ⟨T', i, e', σ₀, he', hv, hT', hσ₀⟩ := GlobalTheory.SupDescent.exists_ext (L := F) T hT io
  have hv' : ∀ a : T.Fr, vV T'.V (i a) = (e' : ℤ) * vV T.V a := fun a => by
    by_cases h : a = 0
    · subst h; simp [vV]
    · exact hv a h
  have ho' := ho.bc i he' hv'
  have hF : ∀ (ρ : L →ₐ[K] Ω) (z : L), ρ z ∈ F := fun ρ z =>
    AlgHom.fieldRange_le_normalClosure ρ ⟨z, rfl⟩
  let τ : (L →ₐ[K] Ω) → L →+* T'.Fr := fun ρ =>
    σ₀.comp ((ρ.codRestrict F.toSubalgebra (hF ρ)).toRingHom)
  have hτ : ∀ ρ z, τ ρ z = σ₀ ⟨ρ z, hF ρ z⟩ := fun _ _ => rfl
  have hτK : ∀ ρ (a : K), τ ρ (algebraMap K L a) = i (io a) := fun ρ a => by
    rw [hτ, ← hσ₀ a]
    congr 1
    exact Subtype.ext (ρ.commutes a)
  have htr : ∀ z : L, i (io (Algebra.trace K L z)) = ∑ ρ : L →ₐ[K] Ω, τ ρ z := fun z => by
    have h1 := trace_eq_sum_embeddings Ω (K := K) (L := L) (x := z)
    have h2 : algebraMap K F (Algebra.trace K L z) = ∑ ρ : L →ₐ[K] Ω, (⟨ρ z, hF ρ z⟩ : F) := by
      apply Subtype.val_injective
      rw [IntermediateField.coe_sum]
      exact h1
    rw [← hσ₀, h2, map_sum]
    exact Finset.sum_congr rfl fun ρ _ => (hτ ρ z).symm
  rw [← valV_le_one_of_ext i he' hv]
  have hsum : i (∑ k, io (Algebra.trace K L ((b : L) * y k)) * x k) =
      ∑ ρ : L →ₐ[K] Ω, ∑ k, τ ρ (b : L) * (τ ρ (y k) * i (x k)) := by
    simp only [map_sum, map_mul (f := i), htr, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, mul_assoc]
  rw [hsum]
  refine Valuation.map_sum_le _ fun ρ _ => ?_
  obtain ⟨la', e'', hol⟩ := GlobalTheory.AlgLawsCompare.exists_overLa T' (τ ρ) hT'
  have hunder : la'.asIdeal.under (𝓞 K) = p.asIdeal := Ideal.ext fun a => by
    rw [Ideal.under_def, Ideal.mem_comap, ← GlobalTheory.SupDescent.val_lt_one_iff_mem hol,
      ← GlobalTheory.SupDescent.val_lt_one_iff_mem ho']
    exact Iff.of_eq (congrArg (fun t => valV T'.V t < 1) (hτK ρ a))
  rcases eq_or_ne la' la with rfl | hne
  · rw [← Finset.mul_sum, map_mul]
    exact mul_le_one' ((GlobalTheory.SupDescent.val_le_one_iff hol _).2 (la'.valuation_le_one b))
      (H T' i e' (τ ρ) e'' he' hv hT' (hτK ρ) hol)
  · refine Valuation.map_sum_le _ fun k _ => ?_
    rw [← mul_assoc, ← map_mul, map_mul]
    refine mul_le_one' ((GlobalTheory.SupDescent.val_le_one_iff hol _).2 ?_) ((valV_le_one_of_ext i he' hv _).2 (hx k))
    rw [map_mul]
    calc la'.valuation L (b : L) * la'.valuation L (y k)
        ≤ WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) :=
          mul_le_mul' (valuation_le_of_mem la' (hb la' hne hunder)) (hN la' hunder k)
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

end GlobalTheory.TraceSmall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialTwistBaseLevelEqTupleParahoricStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivialTwist_baseLevel_eq_tuple_parahoric : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q →
    ∀ x : GL (Fin (Vc D j).rank) (Lev.EAf D),
      (x ∈ lev D.sp.cm (Vc D j).gram (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) ↔
        x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t) ∧
          X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U) ∧
      ∀ (hx : x ∈ parLev D.sp.cm (Vc D j).gram (X.R.βV j) (X.R.datVt j t))
        (hu : X.cG (rTup (X.R.βV j) (X.R.datVt j t) x) ∈ D.nexp.U),
        ((levFn (Y.Z.ρ.B i j b).F.βS ((Y.Z.ρ.B i j b).levS (Y.Z.ρ.tw i b 0 ∅ 1)) x : ℂˣ) : ℂ) =
          ((levFn (X.R.βV j) (Lev.flagL (X.R.datVt j t)) x : ℂˣ) : ℂ) *
            Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨_, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) := by
  first | exact @GlobalTheory.TrivTwistLevel.levS_triv_iff_and_levFn | exact GlobalTheory.TrivTwistLevel.levS_triv_iff_and_levFn | (intros; apply GlobalTheory.TrivTwistLevel.levS_triv_iff_and_levFn <;> assumption)
end

