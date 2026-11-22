import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastTwoStepsDoubleLiftPeriodEqIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0642
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0641
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0640
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumAnisotropicKernelPair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

def lam (σ : ℕ) : Fin σ → D.host.E := fun a => D.host.xi0 ^ (a : ℕ)

theorem lam_ne (σ : ℕ) (a : Fin σ) : lam (D := D) σ a ≠ 0 := pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)

def besDecAt (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) :
    HypDec (G.V (.grid D.R.m j)) (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ :=
  diagDec (rowBes G j (by omega) σ (by omega)) (lam σ) (lam_ne σ)

variable {G t M} in

def volAt (hM : M.Is t) (X : Node) (hX : X.InRange D.R.m) : GlobalTheory.Unf.Vol (G.V X) :=
  ⟨M.ν X, M.fd X, (hM.vtx X hX).haar_fund.1, (hM.vtx X hX).haar_fund.2⟩

variable {t M} in

def besAt (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)) : BesLev D σ where
  V := G.V (.grid D.R.m j)
  V₀ := GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)
  A := G.V (.top j)
  L := GlobalTheory.SeeSaw.Model.nLine D
  d := besDecAt G j σ hj
  o := GlobalTheory.OrthSumExists.orthDecHsum D _ _
  ζ := fun _ => D.host.xi0 ^ σ
  line := GlobalTheory.SeeSaw.Model.isLineVec_nLine (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D))
  cpt := cocpt_top G (by omega)
  vA := volAt hM (.top j) (by show j ≤ D.R.m; omega)
  vN := vN

variable {t M} in

def jacAt (hM : M.Is t) (n σ : ℕ) (hn : n + 2 * σ + 1 = D.R.m) : JacLev D σ where
  W := G.V (.grid D.R.m n)
  W₀ := G.V (.top n)
  d := rowJac G n (by omega) σ (by omega)
  cpt := cocpt_top G (by omega)
  v0 := volAt hM (.top n) (by show n ≤ D.R.m; omega)
  vN := (GlobalTheory.Unf.Inhab.nonempty_volN _).some

theorem exists_weilDatum_anisotropicKernelPair {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) :
    ∃ om₀ : Om V₀ W₀, IsWeilDatumO ψ V₀ W₀ χV χW om₀ := by
  obtain ⟨om₁, h₁⟩ := (GlobalTheory.Desc.weil_data_descend D ψ V W χV χW om h).1 V₀ ρ dV
  exact (GlobalTheory.Desc.weil_data_descend D ψ V₀ W χV χW om₁ h₁).2 W₀ σ dW

variable {M} in

def stepAt (hM : M.Is t) (j : ℕ) (hj : j + 1 ≤ D.R.m) {V₀ W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec (G.V (.grid D.R.m j)) V₀ ρ)
    (dW : HypDec (G.V (.grid D.R.m (j + 1))) W₀ σ) :
    Step Wl.ψ (G.V (.grid D.R.m j)) V₀ (G.V (.grid D.R.m (j + 1))) W₀ ρ σ where
  χV := G.chrS (.mu t D.R.m j)
  χW := G.chrT (.mu t D.R.m j)
  om := Wl.om (.mu t D.R.m j)
  om₀ := (exists_weilDatum_anisotropicKernelPair dV dW (Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩)).choose
  weil := Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩
  weil₀ := (exists_weilDatum_anisotropicKernelPair dV dW (Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩)).choose_spec
  vW := volAt hM (.grid D.R.m (j + 1)) ⟨le_rfl, hj⟩
  vS := (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some
  vT := (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some
  vU := (GlobalTheory.Unf.Inhab.nonempty_volU D _).some

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

theorem link_map {n : ℕ} (σ : ℕ) :
    (-(D.host.xi0 • (1 : Matrix (Fin n) (Fin n) D.host.E))) *ᵥ (fun _ => D.host.xi0 ^ σ) = -fun _ => D.host.xi0 ^ (σ + 1) := by
  rw [neg_mulVec, smul_mulVec, one_mulVec]
  funext i
  simp [pow_succ, mul_comm]

theorem link_norm (L : HSp D) (σ : ℕ) :
    star (fun _ : Fin L.rank => D.host.xi0 ^ (σ + 1)) ⬝ᵥ L.gram *ᵥ (fun _ => D.host.xi0 ^ (σ + 1)) =
      D.host.xi0 * star D.host.xi0 * (star (fun _ : Fin L.rank => D.host.xi0 ^ σ) ⬝ᵥ L.gram *ᵥ (fun _ => D.host.xi0 ^ σ)) := by
  have e : (fun _ : Fin L.rank => D.host.xi0 ^ (σ + 1)) = D.host.xi0 • fun _ => D.host.xi0 ^ σ := by
    funext i
    simp [pow_succ, mul_comm]
  rw [e, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

variable {G t M} in

def linkAt (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (vN : VolN (besDecAt G j (σ + 1) hj))
    (hj' : j + 1 + 1 + 2 * σ + 2 = D.R.m) (vN' : VolN (besDecAt G (j + 1 + 1) σ hj')) :
    Link (besAt G hM j (σ + 1) hj vN) (besAt G hM (j + 1 + 1) σ hj' vN').L (besAt G hM (j + 1 + 1) σ hj' vN').ζ where
  τ := -(D.host.xi0 • (1 : Matrix (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) D.host.E))
  map := link_map σ
  norm := link_norm _ σ

theorem cocpt_last : CoCpt (G.V (.grid D.R.m D.R.m)) := by
  have hm := D.R.two_le_m
  have h := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
    injection e with e1
    omega
  refine GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite h.sigOK fun τ => Or.inl ?_
  rw [h.sig τ, h.rank]
  simp [Node.neg]

def castOm {V : HSp D} {n n' : ℕ} (h : n = n') (om : Om V (G.V (.grid D.R.m n))) : Om V (G.V (.grid D.R.m n')) :=
  Eq.rec (motive := fun k _ => Om V (G.V (.grid D.R.m k))) om h

theorem castOm_weil {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {n n' : ℕ} (h : n = n') {χV χW : (AE D)ˣ →* Circle}
    {om : Om V (G.V (.grid D.R.m n))} (hom : IsWeilDatumO ψ V _ χV χW om) :
    IsWeilDatumO ψ V (G.V (.grid D.R.m n')) χV χW (castOm G h om) := by
  subst h
  exact hom

def castSch {V : HSp D} {n n' : ℕ} (h : n = n') (f : WO V (G.V (.grid D.R.m n)) → ℂ) : WO V (G.V (.grid D.R.m n')) → ℂ :=
  Eq.rec (motive := fun k _ => WO V (G.V (.grid D.R.m k)) → ℂ) f h

theorem castSch_theta {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {n n' : ℕ} (h : n = n') {f : WO V (G.V (.grid D.R.m n)) → ℂ}
    (hf : IsThetaFunO ψ V _ f) : IsThetaFunO ψ V (G.V (.grid D.R.m n')) (castSch G h f) := by
  subst h
  exact hf

variable {M} in

def lastAt (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) :
    Last Wl.ψ (G.V (.grid D.R.m D.R.m)) (besAt G hM j 0 hj vN) where
  J := jacAt G hM (j + 1) 0 (by omega)
  s := stepAt G Wl t hM j (by omega) (besDecAt G j 0 hj) (rowJac G (j + 1) (by omega) 0 (by omega))
  cptS := GlobalTheory.LastRed.cocpt_zero (rowJac G (j + 1) (by omega) 0 (by omega)) (cocpt_top G (j := j + 1) (by omega))
  cptT := cocpt_last G
  χS := G.chrS (.mu t D.R.m (j + 1))
  χT := G.chrT (.mu t D.R.m (j + 1))
  om := castOm G (show j + 1 + 1 = D.R.m by omega) (Wl.om (.mu t D.R.m (j + 1)))
  weil := castOm_weil G (show j + 1 + 1 = D.R.m by omega) (Wl.om_is (.mu t D.R.m (j + 1)) ⟨le_rfl, by omega⟩)
  vT := volAt hM (.grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩

variable {M} in

noncomputable def chainFrom (hM : M.Is t) : (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) →
    Chain Wl.ψ (G.V (.grid D.R.m D.R.m)) σ (besAt G hM j σ hj vN)
  | 0, j, hj, vN => .last (lastAt G Wl t hM j hj vN)
  | σ + 1, j, hj, vN =>
    .step (jacAt G hM (j + 1) (σ + 1) (by omega)) (besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
      (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
        (besDecAt G (j + 1 + 1) σ (by omega)))
      (linkAt hM j σ hj vN (by omega) _) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
      (chainFrom hM σ (j + 1 + 1) (by omega) _)

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

theorem top_idx : 0 + 2 * ((D.R.m - 2) / 2) + 2 = D.R.m := by
  have := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  omega

variable {G t M} in

def topVN (hM : M.Is t) : VolN (besDecAt G 0 ((D.R.m - 2) / 2) top_idx) :=
  volNOf (d := rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2) (by have := top_idx (D := D); omega))
    (nFlag_diag _ (lam _) (lam_ne _)).symm
    (topVolN G M hM.isRow (by have := D.R.two_le_m; omega) (by have := top_idx (D := D); omega))

variable {t M} in

def topLev (hM : M.Is t) : BesLev D ((D.R.m - 2) / 2) := besAt G hM 0 ((D.R.m - 2) / 2) top_idx (topVN hM)

variable {M} in

noncomputable def chain (hM : M.Is t) : Chain Wl.ψ (G.V (.grid D.R.m D.R.m)) ((D.R.m - 2) / 2) (topLev G hM) :=
  chainFrom G Wl t hM _ 0 top_idx (topVN hM)

variable {M} in

noncomputable def dataFrom (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) :
    (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) → (chainFrom G Wl t hM σ j hj vN).Data
  | 0, j, hj, _ => (getD t D.R.m D.R.m d j (by omega),
      castSch G (show j + 1 + 1 = D.R.m by omega) (getD t D.R.m D.R.m d (j + 1) (by omega)))
  | σ + 1, j, hj, _ => (getD t D.R.m D.R.m d j (by omega), getD t D.R.m D.R.m d (j + 1) (by omega),
      dataFrom hM d σ (j + 1 + 1) (by omega) _)

def AllTheta (d : PureT G (downPath t D.R.m D.R.m)) : Prop :=
  Path.Fam.All (fun a (f : Sch G a) => IsThetaFunO Wl.ψ (G.pS a.pair) (G.pT a.pair) f) d

variable {M} in
theorem dataFrom_isTheta (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)),
      (chainFrom G Wl t hM σ j hj vN).IsTheta (dataFrom G Wl t hM d σ j hj vN)
  | 0, j, hj, _ => ⟨getD_all _ t D.R.m D.R.m d hd j (by omega),
      castSch_theta G _ (getD_all _ t D.R.m D.R.m d hd (j + 1) (by omega))⟩
  | σ + 1, j, hj, _ => ⟨getD_all _ t D.R.m D.R.m d hd j (by omega), getD_all _ t D.R.m D.R.m d hd (j + 1) (by omega),
      dataFrom_isTheta hM d hd σ (j + 1 + 1) (by omega) _⟩

variable {M} in

noncomputable def chainData (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) : (chain G Wl t hM).Data :=
  dataFrom G Wl t hM d _ 0 top_idx (topVN hM)

variable {M} in

theorem chainData_isTheta (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) :
    (chain G Wl t hM).IsTheta (chainData G Wl t hM d) :=
  dataFrom_isTheta G Wl t hM d hd _ 0 top_idx (topVN hM)

end GlobalTheory.RowChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedCongruenceElementMemPrincipalCongruence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

open scoped Pointwise

namespace GlobalTheory.LevFrame

theorem gl_smul_pi_one {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] (k₀ : GL n 𝒪[k]) :
    Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ • (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) =
      Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k) := by
  have A : ∀ h : GL n 𝒪[k], ∀ y ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)),
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h • y ∈ (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) := by
    intro h y hy
    have hy' : ∀ j, ∃ c : 𝒪[k], algebraMap 𝒪[k] k c = y j := fun j => Submodule.mem_one.1 (hy j (Set.mem_univ j))
    choose c hc using hy'
    intro i _
    refine Submodule.mem_one.2 ⟨∑ j, h.1 i j * c j, ?_⟩
    show _ = ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) h).1 *ᵥ y) i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← hc]
    rfl
  refine Submodule.ext fun x => (Submodule.mem_smul_pointwise_iff_exists x _ _).trans ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    exact A k₀ y hy
  · intro hx
    refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀⁻¹ • x, A _ x hx, ?_⟩
    rw [map_inv, smul_inv_smul]

set_option maxHeartbeats 2000000 in

theorem gl_mem_lev : All fun {D} _ _ {sc} {G} _ _ => ∀ (X : Node), IsSelfDualC (G.V X) (G.Λ X) → ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) → ∀ (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p (G.V X) n),
  β.IsLat (G.Λ X) (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ k₀ : GL n 𝒪[k],
  (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v) →
  β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀) ∈ lev G X := by
  intro D hQ T L μ0 hL sc G W M hM X hsd v hv k _ _ _ _ p hpv hid n _ _ β hlat k₀ hk₀
  set g := β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀) with hg
  have hff := GlobalTheory.FrameAt.frame_facts D k p (G.V X) n β
  have hgrp : g ∈ grpAt (G.V X) (· = p.v) := (hff.1 g).2 ⟨_, rfl⟩
  have hinK : InK (G.V X) (G.Λ X) (· = p.v) g := by
    obtain ⟨Λ₀, -, hΛ₀, hK⟩ := hff.2.2.2.1 (G.Λ X) hsd
    have hΛeq : Λ₀ = Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k) :=
      Submodule.ext fun x => (hΛ₀ x).trans (hlat x).symm
    rw [hg, hK, hΛeq]
    exact gl_smul_pi_one k₀
  have hsupp : ∀ y, y ∈ latV (G.V X) (G.Λ X) (· = p.v) → ∀ i, y i ∈ idAt D (· = p.v) := fun y hy =>
    (((GlobalTheory.FinPl.localComponents D (· = p.v)).2 (G.V X)).2.2.2 (G.Λ X) y hsd.1).1 hy |>.1
  have hmov : ∀ κ, InK (G.V X) (G.Λ X) (· = p.v) κ → ∀ y, y ∈ latV (G.V X) (G.Λ X) (· = p.v) →
      (mt (G.V X) κ - 1) *ᵥ y ∈ latV (G.V X) (G.Λ X) (· = p.v) := by
    intro κ hκ y hy
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem ((hκ.2 y (hsupp y hy)).1 hy) hy
  show g ∈ Lev.levA (G.V X) (G.levCong X)
  refine Lev.mem_levA.2 ⟨GlobalTheory.SplitHecke.Stab.mem_GfC p.split (β.gl_supp _), ?_⟩
  show Lev.finE (G.V X) g ∈ congLev D.sp.cm (G.V X).gram (G.Λ X) G.modul
  refine mem_congLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x hx => ?_⟩
  · have h1 := add_mem (GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.Λ X) g hgrp (hmov g hinK) x hx) hx
    rwa [sub_add_cancel] at h1
  · have h1 := add_mem (GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.Λ X) g⁻¹ (inv_mem hgrp) (hmov g⁻¹ (inK_inv hinK)) _ hx) hx
    rwa [sub_add_cancel, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at h1
  · obtain ⟨⟨m, hm, hm'⟩, m₂, hm₂, hm₂'⟩ := GlobalTheory.T.gridModulus_exact_order_witness G v hv
    refine GlobalTheory.T.sub_mem_lattice_completion_of_supported_places D (G.V X) _ (G.Λ X) (G.modul • G.Λ X) g hgrp (fun y hy => ?_) x hx
    have hz := hmov g hinK y hy
    obtain ⟨ε, hε, hsum⟩ := p.above
    have hsplit : (mt (G.V X) g - 1) *ᵥ y = (fun i => p.e * ((mt (G.V X) g - 1) *ᵥ y) i) +
        (fun i => cA D p.e * ((mt (G.V X) g - 1) *ᵥ y) i) := by
      funext i
      rw [Pi.add_apply, ← add_mul, hsum]
      exact (((GlobalTheory.T.placeIdempotent_acts_on_supportedAndOff D p.v ε hε).1 _).1 (hsupp _ hz i)).symm
    rw [hsplit]
    exact add_mem (GlobalTheory.T.frameCongruent_sub_one_mulVec_mem_idealLatticeCompletion D k p (G.V X) (G.Λ X) n β hlat G.modul (G.pl.depth sc v)
      ⟨m, hm, GlobalTheory.T.integer_outside_prime_pow_dvd_maximal_ideal_pow D k p (G.pl.w v) hid _ m hm'⟩ k₀ hk₀ y hy) (GlobalTheory.T.cA_smul_mem_latV_ideal_smul_of_conj_place D k p (G.pl.w v) hid (G.V X) (G.Λ X) G.modul ⟨m₂, hm₂, hm₂'⟩ _ hz)

end GlobalTheory.LevFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPerMove
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section Outer

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem outer_move (M : Vol G) {K : Subgroup (GL (Fin (G.V (.grid D.R.m D.R.m)).rank) (Lev.EAf D))}
    (hK : M.IsAt (.grid D.R.m D.R.m) K) (k : GA D (G.V (.grid D.R.m D.R.m))) (k' : GA D (G.V (.top D.R.m)))
    (hk : MeasurePreserving (fun h : GA D (G.V (.grid D.R.m D.R.m)) => h * k) (M.ν (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)))
    (hk' : Measurable (fun h : GA D (G.V (.grid D.R.m D.R.m)) => h * k⁻¹))
    (ι : GA D (G.V (.grid D.R.m D.R.m)) → GA D (G.V (.top D.R.m)))
    (hι : ∀ h, ι h * k' = ι (h * k))
    (P P' : Fn G (.top D.R.m)) (S S' : Fn G (.grid D.R.m D.R.m))
    (hP : ∀ h, P (h * k') = P' h) (hS : ∀ h, S (h * k) = S' h)
    (hPl : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ h, P (ι (γ * h)) = P (ι h))
    (hSl : ∀ γ ∈ GQ (G.V (.grid D.R.m D.R.m)), ∀ h, S (γ * h) = S h) :
    ∫ h in M.fd (.grid D.R.m D.R.m), P' (ι h) * S' h ∂M.ν (.grid D.R.m D.R.m) =
      ∫ h in M.fd (.grid D.R.m D.R.m), P (ι h) * S h ∂M.ν (.grid D.R.m D.R.m) := by
  rw [← setIntegral_fd_mul_right M hK k hk hk' (fun h => P (ι h) * S h) ?_]
  · congr 1
    funext h
    rw [← hP, ← hS, hι]
  · intro γ hγ h
    simp only [hPl γ hγ h, hSl γ hγ h]

end Outer

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section Main

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem genPer_move (ch : Choice R)
    {μ0 : T} (hL : R.toLevCh.Is μ0) (t : T) (a : Fin ch.n) (M : Vol ch.G) (d : PureDat ch.G t) (y : (R.HX t).H)
    (hMr : ∀ j : Fin D.R.m, ∃ K, M.IsAt (.top j) K) (hMc : ∀ i : Fin (D.R.m + 1), ∃ K, M.IsAt (.grid i D.R.m) K)
    (hd1 : ∀ j, ch.S.toGridChoice.Z.HasVec (d.1 j)) (hd2 : ∀ i, ch.S.toGridChoice.Z.HasVec (d.2 i))
    (hξ : ∀ ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g)
    (hη : ∀ η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g)
    (g : Gc D.what₂.Tau (rowSizes D)) (Q Q' : PolCol ch.G × PolRow ch.G)
    (h1 : ∀ j : Fin D.R.m, ch.W.om (.top t j) (ch.G.toPair (.top t j) (ptTop ch.W g j) (ptTop ch.W g (j + 1)))
        (ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q.1 j)) =
      ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (Q'.1 j))
    (h2 : ∀ i : Fin D.R.m, ch.W.om (.chi i D.R.m) (ch.G.toPair (.chi i D.R.m) (ptGrid ch.W g i) (ptGrid ch.W g (i + 1)))
        (ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q.2 i)) =
      ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (Q'.2 i))
    (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W) (η : Module.Dual ℂ R.cX.W) :
    genPer ch t a M d y Q' (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹)
      (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹) =
      genPer ch t a M d y Q ξ η := by

  have hfc : ∀ (P : PolCol ch.G) (j : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.top t j)) (ch.G.pT (.top t j))
      (ch.W.fock (.top t j) (movedVec t ch.S.toGridChoice (d.1 j)) (P j)) := fun P j =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _
      (movedVec_theta_fockVac ch.W ch.S.toGridChoice t (.top t j) j.2 (d.1 j) (hd1 j)).1 (P j)
  have hfr : ∀ (P : PolRow ch.G) (i : Fin D.R.m), IsThetaFunO ch.W.ψ (ch.G.pS (.chi i D.R.m)) (ch.G.pT (.chi i D.R.m))
      (ch.W.fock (.chi i D.R.m) (movedVec t ch.S.toGridChoice (d.2 i)) (P i)) := fun P i =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _
      (movedVec_theta_fockVac ch.W ch.S.toGridChoice t (.chi i D.R.m) ⟨i.2, rfl⟩ (d.2 i) (hd2 i)).1 (P i)

  have hφ' : pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹) (ch.col a) = fun x => (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (x * ptTop ch.W g 0) :=
    funext (pairVec_mul_real (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (ptTop_mem ch.W g 0))
  have hF' : formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹) =
      fun x => (formGen ch t y η) (x * ptGrid ch.W g 0) :=
    funext (formGen_mul_real ch t y η (ptGrid_mem ch.W g 0))

  have hcol := pathLift_column_translate ch.W M t (ptTop ch.W g) D.R.m le_rfl
    (fun j hj => by
      obtain ⟨K, hK⟩ := hMr ⟨j, hj⟩
      refine ⟨⟨K, hK⟩, ?_⟩
      rw [ptTop_lt ch.W g hj]
      exact kappa_fst_move ch.W g ⟨j, hj⟩ hK)
    _ _ (hfc Q.1) h1 (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (hξ ξ)
  have hrow := pathLift_row_translate ch.W M (ptGrid ch.W g) D.R.m le_rfl
    (fun i hi => by
      obtain ⟨K, hK⟩ := hMc ⟨i, by omega⟩
      refine ⟨⟨K, hK⟩, ?_⟩
      rw [ptGrid_le ch.W g (by omega : i < D.R.m + 1)]
      exact kappa_snd_move ch.W g ⟨i, by omega⟩ hK)
    _ _ (hfr Q.2) h2 (formGen ch t y η) (hη η)

  have htop : ∀ h, stabilizerEmbedding ch.G.sp.topDec h * ptTop ch.W g D.R.m = stabilizerEmbedding ch.G.sp.topDec (h * ptGrid ch.W g D.R.m) := by
    intro h
    rw [ptTop_m, kappaTop_apply, ptGrid_le ch.W g (Nat.lt_succ_self D.R.m), GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
    rfl

  obtain ⟨K, hK⟩ : ∃ K, M.IsAt (.grid D.R.m D.R.m) K := hMc (Fin.last D.R.m)
  have hmv : MeasurePreserving (fun h : GA D (ch.G.V (.grid D.R.m D.R.m)) => h * ptGrid ch.W g D.R.m)
        (M.ν (.grid D.R.m D.R.m)) (M.ν (.grid D.R.m D.R.m)) ∧
      Measurable (fun h : GA D (ch.G.V (.grid D.R.m D.R.m)) => h * (ptGrid ch.W g D.R.m)⁻¹) := by
    rw [ptGrid_le ch.W g (Nat.lt_succ_self D.R.m)]
    exact kappa_snd_move ch.W g (Fin.last D.R.m) hK
  show defPer t ch.S.toGridChoice M Q' d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) (ξ ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ (ptTop ch.W g 0)⁻¹) (ch.col a))
      (formGen ch t y (η ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) (ptGrid ch.W g 0))⁻¹)) =
    defPer t ch.S.toGridChoice M Q d (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (formGen ch t y η)
  rw [hφ', hF']
  have hPl := fun (γ : GA D (ch.G.V (.grid D.R.m D.R.m))) (hγ : γ ∈ GQ (ch.G.V (.grid D.R.m D.R.m)))
      (h : GA D (ch.G.V (.grid D.R.m D.R.m))) =>
    (congrArg _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul ch.G.sp.topDec γ h)).trans
      (pathLift_column_leftInvariant ch.W M t D.R.m le_rfl _ (hfc Q.1) (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a)) (hξ ξ) _
        (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational ch.G.sp.topDec γ hγ) (stabilizerEmbedding ch.G.sp.topDec h))
  have hSl := pathLift_row_leftInvariant ch.W M D.R.m le_rfl _ (hfr Q.2) (formGen ch t y η) (hη η)
  exact outer_move M hK (ptGrid ch.W g D.R.m) (ptTop ch.W g D.R.m) hmv.1 hmv.2 (stabilizerEmbedding ch.G.sp.topDec) htop _ _ _ _
    hcol hrow hPl hSl

end Main

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentPartFinitePointMemShiftedTensorLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentPart_finitePoint_mem_shiftedTensorLattice : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e (Pg ∪ Q) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → ∀ y ∈ tens (stdL D.host.E S.rank) (conjI Lv.𝔪 • C.X.Λ), GlobalTheory.LiftLevel.partAt e (finW S T y) ∈ hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ)) := by
  first | exact @GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh | exact GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh | (intros; apply GlobalTheory.LiftLevel.partAt_finW_mem_hatA_sh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinersAndLiftsExistAtChoicesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwinersAndLifts_exist_at_choices : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.grp_record → HostHyp D → R.IsChainW → R.IsThPW → R.ExAt := by
  first | exact @GlobalTheory.ExAtAssembly.exAt_holds | exact GlobalTheory.ExAtAssembly.exAt_holds | (intros; apply GlobalTheory.ExAtAssembly.exAt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVectorAdjointRowIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeVector_adjointRow_integral : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ v ∈ C.X.Λ, IsIntM (GlobalTheory.LiftDat.rowAdj T βT a e v) := by
  first | exact @GlobalTheory.LiftDat.rowAdj_isIntM_of_mem | exact GlobalTheory.LiftDat.rowAdj_isIntM_of_mem | (intros; apply GlobalTheory.LiftDat.rowAdj_isIntM_of_mem <;> assumption)
end

