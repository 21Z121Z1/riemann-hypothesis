import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0658
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittRankZeroEmbeddingMemLatticeCongruenceIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0666
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0510
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0574
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0637
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0664
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal

noncomputable section

open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowShape

variable {D : D7}

def latPi (S : HSp D) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : GlobalTheory.FinPl.Lat S :=
  Submodule.pi Set.univ fun _ => (I : Submodule (𝓞 D.host.E) D.host.E)

variable (D) in

def tiltSc (j : ℕ) (p : Fin (D.R.m - 1 - j)) : D.host.E :=
  if Odd j then
    (if 2 * p.1 < D.R.m - 1 - j then (D.host.xi0 ^ p.1)⁻¹ else star (D.host.xi0 ^ (D.R.m - 1 - j - 1 - p.1)))
  else 1

variable (D) in

def rowId (j : ℕ) (p : Fin (D.R.m - 1 - j)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  FractionalIdeal.spanSingleton _ (tiltSc D j p) * stairId D.host.AA D.host.AAbar (D.R.m - 1 - j) p

variable {T : Type} {L : LevCh D T} {sc : Consts}

def rowN (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (G.V (.grid D.R.m j)) :=
  if h : j < D.R.m then (G.rowDec j h).lat (G.Λ (.top j)) (rowId D j) else G.Λ (.grid D.R.m j)

variable (D) in

def lineId (j : ℕ) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  D.host.AA ^ ((D.R.m - 2 - j) / 2 + 1) * (D.host.AAbar ^ ((D.R.m - 2 - j) / 2 + 1))⁻¹

variable (D) in

def lineL (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.SeeSaw.Model.nLine D) := latPi _ (lineId D j)

variable (D) in

def topL : GlobalTheory.FinPl.Lat (GlobalTheory.RowChain.pLine D) := latPi _ 1

def coreL (G : GridData L sc) (j : ℕ) : GlobalTheory.FinPl.Lat (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) :=
  (G.Λ (.top j)).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iA).restrictScalars
        (𝓞 D.host.E)) ⊔
    (lineL D j).map
      ((Matrix.mulVecLin (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)).iB).restrictScalars
        (𝓞 D.host.E))

end GlobalTheory.RowShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TopOrthAtEmb
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf GlobalTheory.FunObj GlobalTheory.RowUnf GlobalTheory.RowChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowChain.LastSeeSawStep

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem topOrthAt_emb (G : GridData L sc) {n : ℕ} (h : D.R.m = n) (h' : GA D (G.V (.grid D.R.m D.R.m))) :
    (topOrthAt G h).emb (h', 1) = topEmb G h h' := by
  subst h
  exact topOrth_emb G h'

theorem lastTau_gram :
    (lastTau (D := D))ᴴ * ((GlobalTheory.SeeSaw.Model.nLine D).gram * lastTau) =
      (-(D.host.xi0 * star D.host.xi0)) • (pLine D).gram := by
  refine Matrix.ext fun i j => ?_
  rw [pLine_gram]
  have h1 : ∀ a b : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank, (GlobalTheory.SeeSaw.Model.nLine D).gram a b = -1 := nLine_gram
  simp only [Matrix.mul_apply, conjTranspose_apply, lastTau, Matrix.of_apply, Matrix.smul_apply, h1]
  change ∑ x : Fin 1, star (-D.host.xi0) * ∑ y : Fin 1, (-1) * (-D.host.xi0) = (-(D.host.xi0 * star D.host.xi0)) * antiDiagonalSignGramMatrix (R := D.host.E) 1 1 i j
  have hij : i = j := Subsingleton.elim (α := Fin 1) _ _
  subst hij
  have hi : (i : ℕ) = 0 := by have := i.2; change (i : ℕ) < 1 at this; omega
  simp [antiDiagonalSignGramMatrix, hi]
  ring

end GlobalTheory.RowChain.LastSeeSawStep

namespace GlobalTheory.RowChain.LastSeeSawStep

set_option maxHeartbeats 2000000 in

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) {M : GlobalTheory.FunObj.Vol G}
    (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ) (F : Fn G (.grid D.R.m D.R.m))
    (φ : GA D (G.V (.top j)) → ℂ),
    IsThetaFunO Wl.ψ _ _ Φ₁ → IsThetaFunO Wl.ψ _ _ Φ₂ → IsContAut (G.V (.grid D.R.m D.R.m)) F → IsContAut (G.V (.top j)) φ →
    ∀ g : GA D (G.V (.grid D.R.m j)),
      (lastAt G Wl t hM j hj vN).Q φ ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) Φ₂ F =
        ∫ h' in M.fd (.grid D.R.m D.R.m), F h' * GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
          (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
          (lastDat Wl hM j hj vN g Φ₁ Φ₂) (topEmb G (show D.R.m = j + 1 + 1 by omega) h') ∂M.ν (.grid D.R.m D.R.m) := by
  intro D T L sc G Wl t M hM j hj vN Φ₁ Φ₂ F φ hΦ₁ hΦ₂ hF hφ g
  have hψ : IsStdChar D Wl.ψ (-1) := Wl.ψ_std
  obtain ⟨χz, hzH, hzE, -, hev, hodd⟩ := GlobalTheory.RowChars.rowChars G Wl t
  obtain ⟨hS0, hT0⟩ := hodd j (by omega) (by omega)
  obtain ⟨hS1, hT1⟩ := hev (j + 1) (by omega) (by omega)
  have homa : IsWeilDatumO Wl.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.chrS (.top t j)) (G.chrT (.top t j))
      (Wl.om (.top t j)) := Wl.om_is (.top t j) (by show j + 1 ≤ D.R.m; omega)
  have homX0 : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.chrS (.top t (j + 1)))
      (G.chrT (.top t (j + 1))) (Wl.om (.top t (j + 1))) := Wl.om_is (.top t (j + 1)) (by show j + 1 + 1 ≤ D.R.m; omega)
  have homX : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.chrS (.top t (j + 1)))
      (G.chrT (.top t (j + 1)) * χz * χz⁻¹) (Wl.om (.top t (j + 1))) := by
    rw [mul_inv_cancel_right]; exact homX0
  have hom₁ : IsWeilDatumO Wl.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top (j + 1))) (G.chrS (.top t j) * χz) (G.chrT (.top t j)) (lastAt G Wl t hM j hj vN).s.om₀ := by
    rw [← hS0, ← hT0]; exact (lastAt G Wl t hM j hj vN).s.weil₀
  obtain ⟨omT, homT⟩ := (GlobalTheory.Desc.weil_data_descend D Wl.ψ _ _ _ _ _ (lastAt G Wl t hM j hj vN).weil).1 (G.V (.top (j + 1))) 0 (rowJac G (j + 1) (by omega) 0 (by omega))
  have homT' : IsWeilDatumO Wl.ψ (G.V (.top (j + 1))) (G.V (.grid D.R.m D.R.m)) (G.chrS (.top t (j + 1)))
      (G.chrT (.top t (j + 1)) * χz) omT := by
    rw [← hS1, ← hT1]; exact homT
  obtain ⟨omz, homz⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1))) Wl.ψ χz
    (G.chrT (.top t j)) hψ hzH homa.hecT hzE homa.resT
  obtain ⟨hzH', hzE'⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χz 1 hzH hzE
  obtain ⟨omz'', homz''⟩ := GlobalTheory.WeilDatumExistence.weilDatumExists D (G.V (.top (j + 1))) (pLine D) Wl.ψ
    (G.chrS (.top t (j + 1))) χz⁻¹ hψ homX0.hecS hzH' homX0.resS hzE'
  have hΨ : IsThetaFunO Wl.ψ _ _ ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) := (lastAt G Wl t hM j hj vN).s.weil.om_pres _ _ hΦ₁
  have hΞ : IsThetaFunO Wl.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top (j + 1))) (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁)) :=
    (GlobalTheory.LastRed.val_zero (lastAt G Wl t hM j hj vN).s hΨ).1
  have hΦ₂' : IsThetaFunO Wl.ψ (G.V (.top (j + 1))) (G.V (.grid D.R.m D.R.m))
      (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) := GlobalTheory.RankZeroVac.isThetaFunction_comp_wittExtendByZero _ _ hΦ₂
  obtain ⟨-, key⟩ := GlobalTheory.SeeLastPf.seeLast D Wl.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D) (G.V (.top (j + 1)))
    (G.V (.top (j + 1 + 1))) (G.V (.grid D.R.m D.R.m)) (pLine D) (besAt G hM j 0 hj vN).o (topOrthAt G (show D.R.m = j + 1 + 1 by omega))
    lastTau rfl rfl lastTau_gram (G.chrS (.top t j)) χz (G.chrT (.top t j)) (G.chrS (.top t (j + 1)))
    (G.chrT (.top t (j + 1)) * χz) (lastAt G Wl t hM j hj vN).s.om₀ (Wl.om (.top t j)) omz (Wl.om (.top t (j + 1))) omT omz''
    hom₁ homa homz homX homT' homz'' _ _ hΞ hΦ₂'
  have hC := GlobalTheory.LastBiTheta.isBiTheta_lastBi D Wl.ψ hψ (besAt G hM j 0 hj vN).V₀ (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)
    (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.V (.grid D.R.m D.R.m)) (pLine D) (besAt G hM j 0 hj vN).o
    (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau lastTau_gram _ _ hΞ hΦ₂'
  obtain ⟨-, -, hcomm, -⟩ := GlobalTheory.SeeSaw.biAct_all D Wl.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))
    _ _ _ _ (Wl.om (.top t j)) (Wl.om (.top t (j + 1))) homa homX0 _ hC
  have pt : ∀ h' g₀ h₀, omT (g₀, h') (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) 0 *
      (φ h₀ * (lastAt G Wl t hM j hj vN).s.om₀ ((besAt G hM j 0 hj vN).o.emb (h₀, 1), g₀) (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁)) 0) =
      φ h₀ * Wl.om (.top t (j + 1)) (g₀, topEmb G (show D.R.m = j + 1 + 1 by omega) h')
        (fun v => Wl.om (.top t j) (h₀, g₀) (fun u => lastDat Wl hM j hj vN g Φ₁ Φ₂ u v) 0) 0 := by
    intro h' g₀ h₀
    rw [mul_left_comm]
    congr 1
    refine (key h₀ g₀ h').trans ?_
    rw [← topOrthAt_emb]
    exact (hcomm (h₀, g₀) (g₀, _) 0 0).symm
  have inner : ∀ h', (∫ h in (lastAt G Wl t hM j hj vN).s.vW.𝓕, (lastAt G Wl t hM j hj vN).om (h, h') Φ₂ 0 *
      (∫ h₀ in (besAt G hM j 0 hj vN).vA.𝓕, φ h₀ * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, h) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 ∂(besAt G hM j 0 hj vN).vA.μ) ∂(lastAt G Wl t hM j hj vN).s.vW.μ) =
      GlobalTheory.SeeSaw.biLift (Wl.om (.top t j)) (Wl.om (.top t (j + 1)))
        (volAt hM (.top j) (by show j ≤ D.R.m; omega)) (volAt hM (.top (j + 1)) (by show j + 1 ≤ D.R.m; omega)) φ
        (lastDat Wl hM j hj vN g Φ₁ Φ₂) (topEmb G (show D.R.m = j + 1 + 1 by omega) h') := by
    intro h'
    refine (GlobalTheory.RowVolZero.vol_rankZero G t hM (j + 1) (by omega) (fun h => (lastAt G Wl t hM j hj vN).om (h, h') Φ₂ 0 *
      (∫ h₀ in (besAt G hM j 0 hj vN).vA.𝓕, φ h₀ * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, h) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 ∂(besAt G hM j 0 hj vN).vA.μ)) ?_).trans ?_
    · intro γ hγ x
      have a1 : (lastAt G Wl t hM j hj vN).om (γ * x, h') Φ₂ 0 = (lastAt G Wl t hM j hj vN).om (x, h') Φ₂ 0 := by
        have hm : (lastAt G Wl t hM j hj vN).om (γ * x, h') = (lastAt G Wl t hM j hj vN).om (γ, 1) * (lastAt G Wl t hM j hj vN).om (x, h') := by
          rw [← map_mul]; exact congrArg _ (Prod.ext rfl (one_mul h').symm)
        rw [hm]
        exact (lastAt G Wl t hM j hj vN).weil.om_aut γ hγ 1 (one_mem _) _ ((lastAt G Wl t hM j hj vN).weil.om_pres _ _ hΦ₂)
      have a2 : ∀ h₀, (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, γ * x) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 =
          (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, x) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 := by
        intro h₀
        have hm : (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, γ * x) = (lastAt G Wl t hM j hj vN).s.om (1, γ) * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, x) := by
          rw [← map_mul]; exact congrArg _ (Prod.ext (one_mul _).symm rfl)
        rw [hm]
        exact (lastAt G Wl t hM j hj vN).s.weil.om_aut 1 (one_mem _) γ hγ _ ((lastAt G Wl t hM j hj vN).s.weil.om_pres _ _ hΨ)
      simp only [a1, a2]
    · unfold GlobalTheory.SeeSaw.biLift
      refine integral_congr_ae (Filter.Eventually.of_forall fun g₀ => ?_)
      have e1 : (lastAt G Wl t hM j hj vN).om ((rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀, h') Φ₂ 0 = omT (g₀, h') (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) 0 :=
        GlobalTheory.FinPl.VLast.Transport.weilRep_rankZeroWittEmbedding_valueAtZero D Wl.ψ _ _ _ (rowJac G (j + 1) (by omega) 0 (by omega)) _ _ _ omT (lastAt G Wl t hM j hj vN).weil homT Φ₂ hΦ₂ g₀ h'
      have e2 : ∀ h₀, (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, (rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 =
          (lastAt G Wl t hM j hj vN).s.om₀ ((besAt G hM j 0 hj vN).o.emb (h₀, 1), g₀) (flatBF (lastAt G Wl t hM j hj vN).s ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁)) 0 := fun h₀ =>
        GlobalTheory.FinPl.VLast.Transport.om_flatBF_rankZero D Wl.ψ (besAt G hM j 0 hj vN) (lastAt G Wl t hM j hj vN).J (lastAt G Wl t hM j hj vN).s _ hΨ h₀ g₀
      show (lastAt G Wl t hM j hj vN).om ((rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀, h') Φ₂ 0 * (∫ h₀ in (besAt G hM j 0 hj vN).vA.𝓕,
        φ h₀ * (lastAt G Wl t hM j hj vN).s.om (embA (besAt G hM j 0 hj vN).d (besAt G hM j 0 hj vN).o h₀, (rowJac G (j + 1) (by omega) 0 (by omega)).emb0 g₀) ((lastAt G Wl t hM j hj vN).s.om (g, 1) Φ₁) 0 ∂(besAt G hM j 0 hj vN).vA.μ) = _
      rw [e1]
      simp only [e2]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_)
      exact pt h' g₀ h₀
  unfold Last.Q
  refine integral_congr_ae (Filter.Eventually.of_forall fun h' => ?_)
  exact congrArg (F h' * ·) (inner h')

end GlobalTheory.RowChain.LastSeeSawStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelFourth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ColTypeLift

theorem colLift_isTypeAt : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.Xp j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * φ g) (G.measX j).fd (G.measX j).ν) → ∀ τ, IsTypeAt R.θ (G.Xp (j + 1)).V τ ((G.Xp (j + 1)).S τ) (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * φ g ∂(G.measX j).ν) := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t j hj Φ hΦ φ hφ hI τ
  have h0 := xp_definite hG j hj.le
  have h1 := xp_definite hG (j + 1) hj
  obtain ⟨n, F, w, rfl⟩ := GlobalTheory.T.cusp_form_of_type_eq_finite_sum hP R.θ (G.Xp j) hR.inf h0.1 h0.2 φ hφ
  obtain ⟨k, F', z, e⟩ := GlobalTheory.T.theta_lift_vertical_cuspidal_sum hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ n F w hI
  rw [e]
  exact isTypeAt_sum R.θ (G.Xp (j + 1)) h1.1 h1.2 τ F' z

end GlobalTheory.ColTypeLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_line_good_model : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Y, ∀ (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (r : (Fin n × Fin d → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) f f₁ →
    ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r))))
      (GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r))) 0 := by
  first | exact @GlobalTheory.ThetaLineDerY.hasDerivAt_thetaSum_lineY | exact GlobalTheory.ThetaLineDerY.hasDerivAt_thetaSum_lineY | (intros; apply GlobalTheory.ThetaLineDerY.hasDerivAt_thetaSum_lineY <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelGoodLineActionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Filter Topology
open GlobalTheory.AdelicU
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_model_good_line_action : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Wd, ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
    (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
    ∃ (c : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      (∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c t) φ) ∧
      Tendsto (fun t : ℝ => t⁻¹ • (c t - c 0)) (𝓝[≠] 0) (𝓝 g) := by
  first | exact @GlobalTheory.Twist.smoothLine_pure | exact GlobalTheory.Twist.smoothLine_pure | (intros; apply GlobalTheory.Twist.smoothLine_pure <;> assumption)
end

