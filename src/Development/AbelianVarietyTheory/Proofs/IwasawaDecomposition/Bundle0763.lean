import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0745
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0836
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0746
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0853
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0843
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0845
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtremalVectorMemLowestKType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0431
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0722
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0735
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0608
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0733
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0743
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0706
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitReductionStandardFrameConj
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameRedSplit

theorem conj_red_core {R K k ι : Type} [CommRing R] [Field K] [CommRing k] {m : ℕ} (S : Subring R) (O : ValuationSubring K)
    (pr : R →+* K) (φ : O →+* k) (res : S →+* k) (hres : ∀ z : S, ∃ h : pr z ∈ O, res z = φ ⟨_, h⟩)
    (β : GL (Fin m) R) (B B' : Matrix (Fin m) (Fin m) R) (hBB : B * B' = 1)
    (U : Set ι) (Km : ι → Matrix (Fin m) (Fin m) R) (Z : ∀ κ ∈ U, GL (Fin m) S)
    (hZ : ∀ κ (hκ : κ ∈ U), β.1 * (Z κ hκ).1.map S.subtype * (β⁻¹).1 = B * Km κ * B')
    (hsurj : ∀ u : GL (Fin m) O, ∃ κ, ∃ hκ : κ ∈ U, (Km κ).map pr = u.1.map O.subtype) :
    ∃ b : GL (Fin m) k, ∀ κ (hκ : κ ∈ U) (y : GL (Fin m) O), (Km κ).map pr = y.1.map O.subtype →
      (Z κ hκ).1.map res = (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).1 := by
  classical
  obtain ⟨γ, hγ⟩ : ∃ γ : Matrix (Fin m) (Fin m) R, γ = (β⁻¹).1 * B := ⟨_, rfl⟩
  obtain ⟨γ', hγ'⟩ : ∃ γ' : Matrix (Fin m) (Fin m) R, γ' = B' * β.1 := ⟨_, rfl⟩
  have g1 : γ * γ' = 1 := by
    rw [hγ, hγ', Matrix.mul_assoc, ← Matrix.mul_assoc B, hBB, Matrix.one_mul, Units.inv_mul]
  have g2 : γ' * γ = 1 := mul_eq_one_comm.mp g1
  have hZ' : ∀ κ (hκ : κ ∈ U), (Z κ hκ).1.map S.subtype = γ * Km κ * γ' := by
    intro κ hκ
    have e : γ * Km κ * γ' = (β⁻¹).1 * (B * Km κ * B') * β.1 := by
      rw [hγ, hγ']; simp only [Matrix.mul_assoc]
    rw [e, ← hZ κ hκ]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  let c : GL (Fin m) K := ⟨γ.map pr, γ'.map pr, by rw [← Matrix.map_mul, g1, Matrix.map_one _ (map_zero _) (map_one _)],
    by rw [← Matrix.map_mul, g2, Matrix.map_one _ (map_zero _) (map_one _)]⟩
  have hc : ∀ κ (hκ : κ ∈ U), (c.1 * (Km κ).map pr * (c⁻¹).1) = ((Z κ hκ).1.map S.subtype).map pr := by
    intro κ hκ
    rw [hZ' κ hκ, Matrix.map_mul, Matrix.map_mul]
    rfl
  have hent : ∀ u : GL (Fin m) O, ∀ a b, (c * Matrix.GeneralLinearGroup.map O.subtype u * c⁻¹).1 a b ∈ O := by
    intro u a b
    obtain ⟨κ, hκ, hK⟩ := hsurj u
    have e : (c * Matrix.GeneralLinearGroup.map O.subtype u * c⁻¹).1 = c.1 * (Km κ).map pr * (c⁻¹).1 := by
      rw [hK]; rfl
    rw [e, hc κ hκ, Matrix.map_apply, Matrix.map_apply]
    exact (hres _).1
  have hnorm : ∀ u ∈ Formalism.UG.GLint (Fin m) O.toSubring, c * u * c⁻¹ ∈ Formalism.UG.GLint (Fin m) O.toSubring := by
    rintro _ ⟨u, rfl⟩
    refine GlobalTheory.HeckeStdFacts.mem_GLint_iff.2 ⟨fun a b => hent u a b, fun a b => ?_⟩
    have e : (c * Formalism.UG.bc O.toSubring.subtype u * c⁻¹)⁻¹ = c * Matrix.GeneralLinearGroup.map O.subtype u⁻¹ * c⁻¹ := by
      rw [map_inv]
      group
      rfl
    rw [e]
    exact hent u⁻¹ a b
  obtain ⟨h, ⟨h₀, rfl⟩, hconj⟩ := GlobalTheory.HeckeStdFacts.exists_int_of_normalizes O.valuation O.toSubring
    (fun x => (O.valuation_le_one_iff x).symm) c hnorm
  suffices H : ∀ h₁ : GL (Fin m) O, (∀ x, c * x * c⁻¹ = Matrix.GeneralLinearGroup.map O.subtype h₁ * x *
      (Matrix.GeneralLinearGroup.map O.subtype h₁)⁻¹) → ∃ b : GL (Fin m) k, ∀ κ (hκ : κ ∈ U) (y : GL (Fin m) O),
      (Km κ).map pr = y.1.map O.subtype → (Z κ hκ).1.map res = (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).1 from H h₀ hconj
  intro h₁ hconj'
  refine ⟨Matrix.GeneralLinearGroup.map φ h₁, fun κ hκ y hy => ?_⟩
  ext a b
  obtain ⟨hm, hr⟩ := hres ((Z κ hκ).1 a b)
  have e1 : pr ((Z κ hκ).1 a b : R) = (c * Matrix.GeneralLinearGroup.map O.subtype y * c⁻¹).1 a b := by
    have := congrFun (congrFun (hc κ hκ) a) b
    rw [hy] at this
    exact this.symm
  have e2 : (c * Matrix.GeneralLinearGroup.map O.subtype y * c⁻¹) =
      Matrix.GeneralLinearGroup.map O.subtype (h₁ * y * h₁⁻¹) := by
    rw [hconj']
    simp only [map_mul, map_inv]
  have e3 : (⟨_, hm⟩ : O) = (h₁ * y * h₁⁻¹).1 a b := by
    apply Subtype.ext
    show pr _ = _
    rw [e1, e2]
    rfl
  have e4 : Matrix.GeneralLinearGroup.map φ h₁ * Matrix.GeneralLinearGroup.map φ y * (Matrix.GeneralLinearGroup.map φ h₁)⁻¹ =
      Matrix.GeneralLinearGroup.map φ (h₁ * y * h₁⁻¹) := by
    simp only [map_mul, map_inv]
  rw [Matrix.map_apply, hr, e3, e4]
  rfl

theorem resS_eq_phiR (D : D7) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (y : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ h : s.proj (y : EAf D) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      resS D.host.F s.w y = GlobalTheory.MtRed.phiR s ⟨_, h⟩ := by
  have hmem : s.proj (y : EAf D) ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (GlobalTheory.RowGood.proj_le_one s y.2)
  refine ⟨hmem, ?_⟩
  obtain ⟨a, ha, hφ⟩ := GlobalTheory.MtRed.exists_approx s ⟨_, hmem⟩
  rw [hφ]
  exact GlobalTheory.RowGood.res_eq (rfl : maximalRealSubfield D.host.E = _) s (y : EAf D) y (GlobalTheory.RowGood.tr_rfl _).symm a ha

set_option maxHeartbeats 1600000 in

theorem frameRed_exists : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), R3.StdFrame hF P → IsBaseFrame V β Λ 1 → ∀ s : ReciprocityTheory.Aut.SplitPlace D.host.E, ∃ (φ : Os s →+* kP s.w) (b : GL (Fin n) (kP s.w)), IsResidue s φ ∧ FrameRed hn P β s φ b := by
  intro D V n hn hF P β Λ hP hβ s
  subst hn
  obtain ⟨⟨β₀, β₀', h01, h10, hmat⟩, hK⟩ := hP
  have hSt : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank, finE V (P.ψ κ) ∈ St β := fun κ hκ =>
    (GlobalTheory.FinZeta.LevelOff.finE_mem_St_iff hβ (P.into κ)).2 ((hK κ).1 hκ)
  have hfin : ∀ κ : Formalism.AUTREP.GAf D.host.E V.rank, (finE V (P.ψ κ)).1 =
      β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * (κ.1.1.map (GlobalTheory.RowGood.tr hF)) *
        β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
    intro κ
    have e := congrArg (fun M => Matrix.map M (GlobalTheory.LevSplit.swp D.host.F D.host.E)) (hmat κ)
    refine e.trans ?_
    simp only [Matrix.map_mul]
    rfl
  have hBB : β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) = 1 := by
    rw [← Matrix.map_mul, h01, Matrix.map_one _ (map_zero _) (map_one _)]
  have hZ : ∀ (κ : Formalism.AUTREP.GAf D.host.E V.rank) (hκ : κ ∈ {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank}),
      β.1 * (pullFr β ⟨_, hSt κ hκ⟩).1.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (β⁻¹).1 =
        β₀.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) * (κ.1.1.map (GlobalTheory.RowGood.tr hF)) *
          β₀'.map (GlobalTheory.LevSplit.swp D.host.F D.host.E) := by
    intro κ hκ
    exact (congrArg (fun g : GL (Fin V.rank) (EAf D) => g.1) (frGL_pullFr β ⟨_, hSt κ hκ⟩)).trans (hfin κ)
  have hpr : ∀ κ : Formalism.AUTREP.GAf D.host.E V.rank, (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj = (s.loc V.rank κ).1 := by
    intro κ
    ext i j
    simp only [Matrix.map_apply]
    rw [GlobalTheory.RowGood.tr_rfl]
    rfl
  have hsurj : ∀ u : GL (Fin V.rank) (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)),
      ∃ κ : Formalism.AUTREP.GAf D.host.E V.rank, ∃ _ : κ ∈ {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank},
        (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj =
          u.1.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype := by
    intro u
    obtain ⟨x, hx, hloc⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc D.host.E V.rank s
      (Matrix.GeneralLinearGroup.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype u)
    refine ⟨x, (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s hx).1 ⟨u, ?_⟩, ?_⟩
    · rw [hloc]; rfl
    · rw [hpr, hloc]; rfl
  obtain ⟨b, hb⟩ := conj_red_core (R := EAf D) (K := s.v.adicCompletion (maximalRealSubfield D.host.E)) (k := kP s.w)
    (ι := Formalism.AUTREP.GAf D.host.E V.rank) (m := V.rank) (S := Formalism.L2.Herm.intAf D.host.F D.host.E)
    (O := s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (pr := s.proj) (φ := GlobalTheory.MtRed.phiR s)
    (res := resS D.host.F s.w) (hres := resS_eq_phiR D s) (β := β) (hBB := hBB)
    (U := {κ | κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank})
    (Km := fun κ => κ.1.1.map (GlobalTheory.RowGood.tr hF))
    (Z := fun κ hκ => pullFr β ⟨_, hSt κ hκ⟩) (hZ := hZ) (hsurj := hsurj)
  refine ⟨GlobalTheory.MtRed.phiR s, b, ⟨GlobalTheory.MtRed.phiR_surj s, GlobalTheory.MtRed.phiR_eq_zero s⟩, fun κ hκ y hy a c => ?_⟩
  have hy' : (κ.1.1.map (GlobalTheory.RowGood.tr hF)).map s.proj =
      y.1.map (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype := by
    rw [hpr]
    exact Matrix.ext fun i j => (hy i j).symm
  have e := congrFun (congrFun (hb κ hκ y hy') a) c
  have hr : redFn β s.w (finE V (P.ψ κ)) = Formalism.UG.bc (resS D.host.F s.w) (pullFr β ⟨_, hSt κ hκ⟩) := by
    have h1 := redFn_frGL β s.w (pullFr β ⟨_, hSt κ hκ⟩)
    rwa [frGL_pullFr] at h1
  rw [← e, hr]
  rfl

end GlobalTheory.FrameRedSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

theorem exportTie_move (h : CopyTw D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
    (YS : NX.NExpRealS X.R X.cG S)
    (hsup : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b)
    (Z : ExportTie YS X.geo.v₀) :
    ∃ Z' : ExportTie (Forms.tie h m YS hsup) X'.geo.v₀, SameSetup Z.ρ Z'.ρ ∧
      ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b,
        Z'.ν i' (h.cm j) b = Z.ν i j b ∧ HEq (Z.tie i j b).rdV (Z'.tie i' (h.cm j) b).rdV := by
  obtain ⟨ρ', hs, hg, hp⟩ := setup_move h m Z.ρ Z.good Z.pin
  have hrd := Forms.rdRel_move h m YS hsup Z.ρ ρ' hs Z.good hg
  have hm : D'.R.m = D.R.m := (congrArg Ranks.m h.gal.R).symm
  let ν' : D'.ntw.Tw → Fin D'.R.m → Bool → ℂ := fun i' j' b => Z.ν (cast h.Tw_eq.symm i') (Fin.cast hm j') b
  have hν : ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : Fin D.R.m) b, ν' i' (h.cm j) b = Z.ν i j b := by
    intro i i' hi j b
    have e1 : cast h.Tw_eq.symm i' = i := eq_of_heq ((cast_heq _ _).trans hi.symm)
    have e2 : Fin.cast hm (h.cm j) = j := Fin.ext rfl
    change Z.ν (cast h.Tw_eq.symm i') (Fin.cast hm (h.cm j)) b = _
    rw [e1, e2]
  have back : ∀ (i' : D'.ntw.Tw) (j' : Fin D'.R.m), ∃ i : D.ntw.Tw, ∃ j : Fin D.R.m, HEq i i' ∧ h.cm j = j' :=
    fun i' j' => ⟨cast h.Tw_eq.symm i', Fin.cast hm j', cast_heq _ _, Fin.ext rfl⟩
  have hrdZ : RdRel h (fun i j b => realRd YS X.geo.v₀ Z.good i j b (Z.ν i j b))
      (fun i j b => realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i j b (ν' i j b)) := by
    intro i i' hi j b f
    have := hrd (Z.ν i j b) i i' hi j b f
    change HEq (realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i' (h.cm j) b (ν' i' (h.cm j) b) _) _
    rw [hν i i' hi j b]
    exact this
  obtain ⟨T', hT'⟩ := TieUp.tie_move h hs Z.good hg _ _ hrdZ Z.tie
  have hv := isExtremalVector_of_realSideBaseChange h m Z.vec
  have hsc : ∀ i' j' b, IsScalar (Forms.tie h m YS hsup) X'.geo.v₀ hg i' j' b (ν' i' j' b) := by
    intro i' j' b
    obtain ⟨i, j, hi, rfl⟩ := back i' j'
    rw [hν i i' hi j b]
    exact scalar_move h m hs Z.good hg Z.pin hp Z.vec hv hrd i i' hi j b _ (Z.scalar i j b)
  have hhk : ∀ i' j' b, HeckeTie (realRd (Forms.tie h m YS hsup) X'.geo.v₀ hg i' j' b (ν' i' j' b)) := by
    intro i' j' b
    obtain ⟨i, j, hi, rfl⟩ := back i' j'
    exact heckeTie_move h hs _ _ hrdZ i i' hi j b (Z.hecke i j b)
  exact ⟨ExportTie.mk ρ' hg hp hv ν' hsc T' hhk (GlobalTheory.UnivCharCopy.isUnivChar_copy h Z.univ), hs,
    fun i i' hi j b => ⟨hν i i' hi j b, hT' i i' hi j b⟩⟩

theorem serAt_move (h : CopyAll D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι) {S : NX.RatDat D.ntw}
    (YS : NX.NExpRealS X.R X.cG S) {Xe : NExpTied D} {Xe' : NExpTied D'} (hX : ExpMove Xe Xe')
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {PV' : ∀ i : Fin D'.R.m, principalLevelFrame.RowPsi (Vc D' i) D'.R.nV}
    (hp : KeepsMat fun i => (PV i).ψ) (hp' : KeepsMat fun i => (PV' i).ψ) {cf : CharFrame D} {cf' : CharFrame D'}
    (hcf : SameFrame cf cf') {Pq Pq'} (hPq : HEq Pq Pq') (Z : SerAt YS X.geo.v₀ Xe PV cf Pq) :
    Nonempty (SerAt (Forms.tie h.cp m YS Z.sup) X'.geo.v₀ Xe' PV' cf' Pq') := by
  obtain ⟨Z', hs, hr⟩ := exportTie_move h.cp m YS Z.sup Z.ex
  obtain ⟨lam, l1, l2, l3, l4, l5⟩ := LamCopy.lam_copy h hcf ⟨Z.lam, Z.lam_ok, Z.lam_teich, Z.lam_C, Z.lam_q, Z.lam_tie⟩
  refine ⟨{ ex := Z'
            bad := (low_copy h.cp).2.1 _ _ hs.bad Z.bad
            ch := (pq_copy h.cp Pq Pq' hPq).1 _ _ hs.ch Z.ch
            join := fun i' j' b k Q' ψ' hA' hT' => ?_
            sup := sup_move h.cp m YS Z.sup
            off := (low_copy h.cp).2.2 Z.off
            lam := lam
            lam_ok := l1
            lam_teich := l2
            lam_C := l3
            lam_q := l4
            lam_tie := l5 }⟩
  obtain ⟨j, rfl⟩ : ∃ j, h.cp.cm j = j' := ⟨⟨j', lt_m h.cp j'.2⟩, rfl⟩
  obtain ⟨i, Q, ψ, hi, hQ, hψ, hT, e1, e2, e3, e4⟩ := join_copy h.cp i' j (h.cp.cm j) rfl b k Q' ψ' hT'
  obtain ⟨e5, e6⟩ := e4 _ _ hs.ek
  obtain ⟨hA, -, -, hR⟩ := hX i i' hi ((j : ℕ) + 1) b k Q Q' hQ ψ ψ' hψ (Nat.le_add_left _ _) j.2 (h.cp.cm j).2 hA'
  exact hR _ _ e5 _ _ e1 e2 e3 _ _ (e6 _ _ (hr i i' hi j b).2 _ _ (keepsMat_heq h.cp _ _ hp hp' j (h.cp.cm j) rfl))
    (Z.join i j b k Q ψ hA hT)

theorem series_move (h : CopyAll D D' ι e) {X : RealSide D} {X' : RealSide D'} (m : RealMove X X' ι)
    (g₀ : GlobalTheory.RealGeo.GeoHalf X.core X.R.toRealDat fun _ => 1) (g₁ : GlobalTheory.RealGeo.GeoHalf X'.core X'.R.toRealDat fun _ => 1)
    {kKs hk} (kKs' hk') (YS : NX.NExpRealS X.R X.cG (NX.ratDatR X.R X.cG kKs hk)) (hfi : ∀ i x, HEq ((YS.fi i).e x) x)
    (hl : LowIn D) {Sb Sb'} (hSb : OverSet D Sb (lowAll D)) (hSb' : OverSet D' Sb' (lowAll D'))
    {hL hL'} (H : HkAd X Sb hL) (H' : HkAd X' Sb' hL') {hs c} (hs') {c'} (hc : SameUnits c c') (L : HkLaw D _ YS.eF hL hs c)
    {cf : CharFrame D} {cf' : CharFrame D'} (hcf : SameFrame cf cf') (s : CharSide D cf) (s' : CharSide D' cf')
    {PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV} {PV' : ∀ i : Fin D'.R.m, principalLevelFrame.RowPsi (Vc D' i) D'.R.nV}
    (hp : KeepsMat fun i => (PV i).ψ) (hp' : KeepsMat fun i => (PV' i).ψ) {Pq Pq'} (hPq : HEq Pq Pq')
    {Xe : NExpTied D} (hq : PqLaw Xe Pq) (hτ : TauTrue Xe) (Z : SerAt YS g₀.v₀ Xe PV cf Pq) :
    ∃ (YS' : NX.NExpRealS X'.R X'.cG (NX.ratDatR X'.R X'.cG kKs' hk')) (Xe' : NExpTied D'), PqLaw Xe' Pq' ∧
      HkLaw D' (NX.ratDatR X'.R X'.cG kKs' hk') YS'.eF hL' hs' c' ∧ (∀ i x, HEq ((YS'.fi i).e x) x) ∧
      Nonempty (SerAt YS' g₁.v₀ Xe' PV' cf' Pq') ∧ TauTrue Xe' := by
  obtain rfl : kKs' = m.kKsOf (e := e) YS (NX.idxOf D 0) :=
    RingHom.ext fun x => Subtype.ext ((hk' x).trans (m.kKsOf_spec h.cp YS _ x).symm)
  obtain ⟨Xe', ht, hX⟩ := GlobalTheory.HeightCounting.ExpCopy.expTied_copy h hcf s s' Xe
  obtain ⟨Z₁⟩ := GlobalTheory.SerVec.serAt_vec X g₀ X.geo YS _ _ _ _ Z
  obtain ⟨Z₂⟩ := serAt_move h m YS hX hp hp' hcf hPq Z₁
  exact ⟨Forms.tie h.cp m YS Z₁.sup, Xe', pqLaw_move h.cp hX hPq hq,
    hkLaw_move h.cp m YS hfi hl ((low_copy h.cp).1 hl) hSb hSb' H H' Z₁.sup hs' hc L, fun i x => fiOfEq_heq X' _ x,
    GlobalTheory.SerVec.serAt_vec X' X'.geo g₁ _ _ _ _ _ Z₂, ht hτ⟩

end GlobalTheory.HeightCounting.SerCarry

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteBalancedCmIntegersActionsSiegelReduced
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem finite_balanced_actions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ),
    {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧
      (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u *
        (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)}.Finite := by
  intro E _ _ _ H n
  classical
  set S := {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧
      (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u *
        (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)} with hSdef

  have hK : ∀ c : 𝓞 E, ∃ K : ℝ, ∀ ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ,
      (((ρ (H.bar c) * ρ c).trace : ℤ) : ℝ) ≤ K := by
    intro c
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) (H.bar c * c)
    obtain ⟨K, hK⟩ := GlobalTheory.T.trace_bounded_of_aeval_monic_eq_zero p hpm n
    refine ⟨K, fun ρ => ?_⟩
    apply hK
    have h0 : Polynomial.aeval (ρ.toIntAlgHom (H.bar c * c)) p = 0 := by
      rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hp, map_zero]
    simpa using h0
  choose K hK using hK

  have hC : ∀ c : 𝓞 E, ∃ N : ℤ, ∀ ρ ∈ S, ∀ i j, ρ c i j ∈ Set.Icc (-N) N := by
    intro c
    obtain ⟨C, hC⟩ := GlobalTheory.T.balanced_entries_bounded_siegelReduced n (K c)
    refine ⟨⌈C⌉, fun ρ hρ i j => ?_⟩
    obtain ⟨d, u, hs, hpos, hrel⟩ := hρ
    have h1 := hC (ρ c) (ρ (H.bar c)) d u hs hpos (hrel c) (hK c ρ) i j
    have h2 : ((|ρ c i j| : ℤ) : ℝ) ≤ ((⌈C⌉ : ℤ) : ℝ) := h1.trans (Int.le_ceil C)
    have h3 : |ρ c i j| ≤ ⌈C⌉ := by exact_mod_cast h2
    exact abs_le.mp h3
  choose N hN using hC
  let b := RingOfIntegers.basis E
  let F : (𝓞 E →+* Matrix (Fin n) (Fin n) ℤ) → (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fin n → Fin n → ℤ) :=
    fun ρ l => ρ (b l)
  let T : Set (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fin n → Fin n → ℤ) :=
    Set.pi Set.univ fun l => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-N (b l)) (N (b l))
  have hT : T.Finite :=
    Set.Finite.pi fun l => Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine Set.Finite.of_injOn (f := F) (t := T) ?_ ?_ hT
  · intro ρ hρ l _ i _ j _
    exact hN (b l) ρ hρ i j
  · intro ρ₁ _ ρ₂ _ h
    have hl : ∀ l, ρ₁ (b l) = ρ₂ (b l) := fun l => congrFun h l
    have hlin : ρ₁.toAddMonoidHom.toIntLinearMap = ρ₂.toAddMonoidHom.toIntLinearMap :=
      b.ext fun l => by simpa using hl l
    ext1 x
    simpa using LinearMap.congr_fun hlin x

end GlobalTheory.RedTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharacterEqProductResidualCharactersE
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.ChiWExt

section Move

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt}

theorem m_eq (hP : B'.toPre = B.toPre) : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  exact (by with_unfolding_all exact ((Eq.refl (w.st Z).toD7.R.m) :))

theorem gc_eq (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px) : Gc B' px' = Gc B px := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  exact (by with_unfolding_all exact ((Eq.refl (Gc B px)) :))

theorem prod_move (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px)
    {Pg : Finset (Pl (w.st Z).toD7.host.E)} {Pg' : Finset (Pl (w'.st Z').toD7.host.E)} (hPg : HEq Pg' Pg)
    {eG : Gc B px ≃* G0 Pg (w.st Z).toD7.R.r} {eG' : Gc B' px' ≃* G0 Pg' (w'.st Z').toD7.R.r} (heG : HEq eG' eG)
    {χ : ∀ PP : Pl (w.st Z).toD7.host.E, (kP PP)ˣ →* ℂˣ} {χ' : ∀ PP : Pl (w'.st Z').toD7.host.E, (kP PP)ˣ →* ℂˣ}
    (hχ : ∀ PP' PP, HEq PP' PP → PP ∈ Pg → HEq (χ' PP') (χ PP)) {g : Gc B px} {g' : Gc B' px'} (hg : HEq g' g) :
    ∏ PP : Pg', ((χ' PP (Matrix.GeneralLinearGroup.det (eG' g' PP)) : ℂˣ) : ℂ) =
      ∏ PP : Pg, ((χ PP (Matrix.GeneralLinearGroup.det (eG g PP)) : ℂˣ) : ℂ) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  ( (
  have e : @Eq (type_of% (Pg')) ((by with_unfolding_all exact ((Pg) :))) (Pg') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Pg')) (Pg') (((Pg))) (((hPg)))).symm : _))
  clear (hPg)
  subst e))
  ( (
  have e : @Eq (type_of% (eG')) ((by with_unfolding_all exact ((eG) :))) (eG') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (eG')) (eG') (((eG))) (((heG)))).symm : _))
  clear (heG)
  subst e))
  ( (
  have e : @Eq (type_of% (g')) ((by with_unfolding_all exact ((g) :))) (g') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (g')) (g') (((g))) (((hg)))).symm : _))
  clear (hg)
  subst e))
  have e : ∀ PP : Pl (w.st Z).toD7.host.E, PP ∈ Pg → HEq (χ' ((by with_unfolding_all exact (PP :)))) (χ PP) :=
    fun PP hm => hχ ((by with_unfolding_all exact (PP :))) PP ((by with_unfolding_all exact ((HEq.refl PP) :))) hm
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact congrArg (fun c : ℂˣ => (c : ℂ)) (DFunLike.congr_fun (eq_of_heq (e PP.1 PP.2)) _)

end Move

set_option maxHeartbeats 1000000 in

theorem grp_chiW_ext : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq w'.px w.px → RSideW z Wt' R' → LevSame z Wt' R' → R'.toRealDat.grp_chiW := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hpx hS hL
  have hc := z.pins.char.base.grp.chiW
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL :=
    (B'.embLL.rangeRestrictFieldEquiv.symm : B'.embLL.fieldRange →+* B'.LL).comp
      (B.embLL.codRestrict B'.embLL.fieldRange fun x => hE.2.2.2 ⟨x, rfl⟩)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := fun x =>
    congrArg Subtype.val (B'.embLL.rangeRestrictFieldEquiv.apply_symm_apply ⟨B.embLL x, hE.2.2.2 ⟨x, rfl⟩⟩)
  intro i' g'
  have hm := m_eq (w := w) (w' := w') (Z := Z) (Z' := Z') hE.1
  let i : Fin (w.st Z).toD7.R.m := ⟨i', by have := i'.2; omega⟩
  have hi : (i : ℕ) = i' := rfl
  let g : Gc B w.px := cast (gc_eq hE.1 hpx) g'
  have hg : HEq g' g := (cast_heq _ _).symm
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hPg, heG, -, hW, -⟩ := hS'
  have hWi := hW i i' hi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hWι⟩ := hWi
  have hch := (hWι ι hι).2.2.1 g' g hg
  rw [hch, hι, hc i g]
  exact (prod_move hE.1 hpx hPg heG (fun PP' PP h hm => (hL.1 i i' hi).2 PP' PP h hm) hg).symm

end GlobalTheory.Mem.R3.Rw.ChiWExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernIsHomogeneousCmTypeStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_isHomogeneous_cmType : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), (rootDiscr Dw.mult).IsHomogeneous (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2)) := by
  first | exact @GlobalTheory.GrassTop.rootDiscr_isHomogeneous | exact GlobalTheory.GrassTop.rootDiscr_isHomogeneous | (intros; apply GlobalTheory.GrassTop.rootDiscr_isHomogeneous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceUniqueLiftAnyFieldStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpace_unique_lift_any_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → ∀ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn), Tied e C.Y C.π C.f0 E' A₁ → f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → (∀ z', ∀ A' ∈ E'.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf C.Y).O z').toSubring (A' * (A.map φ)⁻¹)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), ∀ A ∈ Eb.S (x (IsLocalRing.closedPoint K)), ∀ h : Mat Dw.mult K, Par 0 ⊤ h → ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ Bears E' φ A h p := by
  first | exact @GlobalTheory.ShFam.FieldLift.lifts_of_closed | exact GlobalTheory.ShFam.FieldLift.lifts_of_closed | (intros; apply GlobalTheory.ShFam.FieldLift.lifts_of_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapRAllSt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Up.GapAllStates

theorem gapR_allSt : AllSt fun _ _ _ _ _ _ x => ∀ (τ : (Dof x).what₂.Tau) (n : ℕ), n + 1 < (Dof x).R.r →
    100 * ((Dof x).R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt ((Dof x).hc τ) n - Formalism.L2.NTheta.lamAt ((Dof x).hc τ) (n + 1) :=
  Step.of_evG (EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
    fun _ _ _ _ _ hK _ _ _ hO _ _ _ w _ _ x => (hK (w.st x.o.Z) hO).1.gapR)

end GlobalTheory.HeightCounting.Up.GapAllStates
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLineIffEigenSpanStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_line_iff_eigen_span : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x → ∀ θ : (∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ), (∀ kk, θ kk ≠ 1) → LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → ∀ j, 1 ≤ j → j ≤ (Dof x).R.m → ∀ v : (SOf x).WL j, (v ∈ goodL (Dof x) (SOf x) θ j ↔ GlobalTheory.EigSpanDesc.iotaR x.m.z.R (idxOf (Dof x) j) v ∈ GlobalTheory.EigRows.goodW x.m.z.R.toRealDat x.m.z.F.lv2 (idxOf (Dof x) j)) := by
  first | exact @GlobalTheory.EigSpanTie.mem_goodL_iff_of_state | exact GlobalTheory.EigSpanTie.mem_goodL_iff_of_state | (intros; apply GlobalTheory.EigSpanTie.mem_goodL_iff_of_state <;> assumption)
end

