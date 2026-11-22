import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0728
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HeckePin
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerHyperplaneAveragesVanish
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.HypAvg

theorem residueEquiv : ∀ (D : D7) (v : FinPl D) (PP : Pl D.host.E) (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ∃ ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP, ∀ a : OI v, ρk (IsLocalRing.residue (OI v) a) = red a := by
  intro D v PP red hs hk
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal (OI v) := by
    ext a
    rw [RingHom.mem_ker, hk]
    exact (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (Fv D.host.F v) _))).symm
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hs), fun a => rfl⟩

theorem exists_blockGL : ∀ (O : Type) [CommRing O] [IsLocalRing O] (r t n : ℕ) (hn : r + t = n) (M : Matrix (Fin r) (Fin r) O) (g₀ : GL (Fin r) (IsLocalRing.ResidueField O)), M.map (IsLocalRing.residue O) = (g₀ : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∃ h : GL (Fin n) O, (h : Matrix (Fin n) (Fin n) O) = (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin t) (Fin t) O)).submatrix (rowIx hn).symm (rowIx hn).symm := by
  intro O _ _ r t n hn M g₀ hM
  have hd : IsLocalRing.residue O M.det = (g₀ : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det := by
    rw [← hM, RingHom.map_det]; rfl
  have hdet : IsUnit ((Matrix.fromBlocks M 0 0 (1 : Matrix (Fin t) (Fin t) O)).submatrix (rowIx hn).symm
      (rowIx hn).symm).det := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
      ← IsLocalRing.residue_ne_zero_iff_isUnit, hd, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  exact ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩

theorem ell_heisO_omegaInv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ) (κ : GA D (Vc D i)) (c : ℂ), c ≠ 0 → (∀ φ', IsThetaFunO R.ψ (Vc D i) (Wc D i) φ' → ℓ (R.ωP i t (κ, 1) φ') = c * ℓ φ') → ∀ (u : WO (Vc D i) (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ℓ (heisO R.ψ (Vc D i) (Wc D i) u (R.ωP i t (κ⁻¹, 1) f)) = c⁻¹ * ℓ (heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) κ 1 u) f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t ℓ κ c hc hsc u f hf
  have hW := hω i t
  have e1 : actO (Vc D i) (Wc D i) κ⁻¹ 1 (actO (Vc D i) (Wc D i) κ 1 u) = u := by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO (S := Vc D i) (T := Wc D i) κ 1 u
  have e2 := hW.om_heis κ⁻¹ 1 (actO (Vc D i) (Wc D i) κ 1 u) f hf
  rw [e1] at e2
  rw [← e2]
  have hth := hW.om_pres (κ⁻¹, 1) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf (actO (Vc D i) (Wc D i) κ 1 u))
  have e3 := hsc _ hth
  have e4 : R.ωP i t (κ, 1) (R.ωP i t (κ⁻¹, 1) (heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) κ 1 u) f)) =
      heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) κ 1 u) f := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one]
    show R.ωP i t 1 _ = _
    rw [map_one]; rfl
  rw [e4] at e3
  rw [e3, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem actO_sigma : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (κ : GA D (Vc D i)) (M : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (Fv D.host.F v)), ((grpCo φ (Vc D i) (frCo φ (R.βV i)) κ : GL (Fin (Vc D i).rank) (Fv D.host.F v)) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (Fv D.host.F v)) = M.submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm → ∀ X, actO (Vc D i) (Wc D i) κ 1 (σ X) = σ (M * X) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i v φ e he σ hσ κ M hM X
  have sdV := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βV i)
  have sdW := GlobalTheory.T.isSelfDualCoordLattice_of_selfDualFrame D _ _ _ _ (hL.βW i)
  obtain ⟨hco, hact⟩ := GlobalTheory.PlaceTensor.adjCo_isCoord D (Vc D i) (Wc D i) _ _ sdV sdW v φ e he (frCo φ (R.βV i))
    (frCo φ (R.βW i))
  have hhalf : IsHalf (cA D e) (actO (Vc D i) (Wc D i) κ 1 (σ X)) := GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσ X).1
  apply hco.2.1.injOn hhalf (hσ (M * X)).1
  have h1 := hact κ⁻¹ 1 (σ X)
  simp only [inv_inv, inv_one] at h1
  have hg1 : grpCo φ (Wc D i) (frCo φ (R.βW i)) 1 = 1 := by
    unfold grpCo; simp
  have key : ∀ y, adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) y =
      (coR R i φ y).submatrix (rowIx (rank_V i)).symm (finCongr (rank_weight_component_eq i)).symm := by
    intro y
    unfold coR co
    rw [Matrix.submatrix_submatrix]
    ext j k
    simp
  rw [h1, GlobalTheory.PlaceTensor.AdjCoord.grpCo_inv, inv_inv, hg1, Units.val_one, Matrix.mul_one, key (σ (M * X)),
    (hσ _).2, key (σ X), (hσ X).2, hM, Matrix.submatrix_mul_equiv]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem liftsV (R : RealDat D A Ks) (h : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (t : T) :
    LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := by
  obtain ⟨c, hc⟩ := h.βV i
  refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_)
    (GlobalTheory.LevelRamif.ramif_at_levels D T R.toLevCh A.μ0 h t i).1
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (h.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

theorem termAt (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hω : R.thP_ωP) (i : Fin D.R.m) (t : T)
    (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) {v : FinPl D} (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D) (he : IsIdemOf φ e)
    (red : OI v →+* kP PP) (ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP)
    (hρ : ∀ a : OI v, ρk (IsLocalRing.residue (OI v) a) = red a) (hAct : ActAt R i t PP φ e red)
    {Sb : Finset (FinPl D)} (hv : v ∈ Sb)
    (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i))
    (hσ : ∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X)
    (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ) (hℓ : InvForm R.ψ (Vc D i) (Wc D i) e ℓ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) (a' : Fin D.R.r → kP PP)
    (lift : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → Matrix (Fin D.R.r) (Fin D.R.r) (OI v))
    (hlift : ∀ g, (lift g).map (IsLocalRing.residue (OI v)) =
      (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))))
    (g : G) (hg : mirC R i ⟨PP, hPP⟩ a' false 1 g ≠ 0) :
    ∃ κ : GA D (Vc D i), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ SuppIn Sb (Vc D i) κ ∧
      ∀ X, mirC R i ⟨PP, hPP⟩ a' false 1 g * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ *
          ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) (R.ωP i t (κ⁻¹, 1) f)) =
        ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((Matrix.fromBlocks
          (lift (Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩))) 0 0
          (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) := by
  classical
  have hc : (∀ PP' : R.Pg, PP' ≠ ⟨PP, hPP⟩ → R.eG g PP' = 1) ∧
      ∀ x, a' ⬝ᵥ x = 0 → ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).mulVec x = x := by
    by_contra hc
    exact hg (by unfold mirC; rw [if_neg (by simpa using hc)])
  have hm : mirC R i ⟨PP, hPP⟩ a' false 1 g =
      ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (R.eG g ⟨PP, hPP⟩)) : ℂˣ) : ℂ) := by
    unfold mirC; rw [if_pos (by simpa using hc), zpow_one]
  set g₀ := Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩) with hg₀
  obtain ⟨hh, hhv⟩ := exists_blockGL (OI v) D.R.r D.R.t _ (rank_V i) (lift g₀) g₀ (hlift g₀)
  obtain ⟨κ, hSupp, hGf, hSt, hgrp, hred, hoth, hsc⟩ := hAct hh
  have hlr : (lift g₀).map red = ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) := by
    ext j k
    have e1 := congrFun (congrFun (hlift g₀) j) k
    simp only [Matrix.map_apply] at e1 ⊢
    rw [← hρ, e1, hg₀]
    simp [Matrix.GeneralLinearGroup.map]
  have hredM : ((redFn (R.βV i) PP (finE (Vc D i) κ) : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) =
      (Matrix.fromBlocks ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) 0 0
        (1 : Matrix (Fin D.R.t) (Fin D.R.t) (kP PP))).submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm := by
    rw [hred]
    show (hh : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)).map red = _
    rw [hhv, ← Matrix.submatrix_map, Matrix.fromBlocks_map, hlr, Matrix.map_zero _ (map_zero red),
      Matrix.map_zero _ (map_zero red), Matrix.map_one _ (map_zero red) (map_one red)]
  obtain ⟨hLift, hchi⟩ := GlobalTheory.T.lift_blockDiag_reduction_to_flagGroup D G Pl0 T A Ks R i t PP hPP g hc.1 κ hGf hSt hredM hoth
  refine ⟨κ, hLift, suppIn_of_suppAt he hv hSupp, fun X => ?_⟩
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map red hh) =
      Matrix.GeneralLinearGroup.det (R.eG g ⟨PP, hPP⟩) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ← hred, hredM,
      Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  set c : ℂ := ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (R.eG g ⟨PP, hPP⟩)) : ℂˣ) : ℂ) with hcdef
  have hc0 : c ≠ 0 := Units.ne_zero _
  have key := ell_heisO_omegaInv D G Pl0 T A Ks R hω i t ℓ κ c hc0
    (fun φ' hφ' => by rw [hsc ℓ hℓ φ' hφ', hdet]) (σ X) f hf
  have hco := actO_sigma D G Pl0 T A Ks R hL i v φ e he σ hσ κ
    ((Matrix.fromBlocks (lift g₀) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map
      (algebraMap (OI v) (Fv D.host.F v))) (by
        rw [hgrp]
        show (hh : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) = _
        rw [hhv, Matrix.submatrix_map]) X
  rw [key, hco, hchi, hm, inv_one, mul_one, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

theorem avg_schrodinger_hyperplane : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ActAt R i t PP φ e red → ∀ (Sb : Finset (FinPl D)), v ∈ Sb → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ), InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → CleanIn R i t Sb f → ∀ a : Fin D.R.r → IsLocalRing.ResidueField (OI v), a ≠ 0 → ∀ (lift : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → Matrix (Fin D.R.r) (Fin D.R.r) (OI v)), (∀ g, (lift g).map (IsLocalRing.residue (OI v)) = (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v)))) → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ∑ᶠ g ∈ {g : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) | ∀ w, a ⬝ᵥ w = 0 → (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))).mulVec w = w}, ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω i t PP hPP v φ e hproj he red hsurj hker hAct Sb hv σ hσ ℓ hℓ f hf hclean a ha
    lift hlift X
  classical
  obtain ⟨ρk, hρ⟩ := residueEquiv D v PP red hsurj hker
  have ha' : (fun j => ρk (a j)) ≠ 0 := fun h => ha (funext fun j => ρk.injective (by simpa using congrFun h j))
  have hOver : Over PP v := ((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hproj).1
  choose κ₀ hκ₀ using fun g : G => liftsV R hL i t (R.eG g)
  have hG := fun (g : G) (hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0) =>
    termAt R hL hω i t PP hPP φ e he red ρk hρ hAct hv σ hσ ℓ hℓ f hf (fun j => ρk (a j)) lift hlift g hg
  let κ : G → GA D (Vc D i) := fun g =>
    if hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0 then (hG g hg).choose else κ₀ g
  have hκ : ∀ g (hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0), κ g = (hG g hg).choose :=
    fun g hg => dif_pos hg
  have hLifts : IsLifts R i t κ := fun g => by
    by_cases hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0
    · rw [hκ g hg]; exact (hG g hg).choose_spec.1
    · have : κ g = κ₀ g := dif_neg hg
      rw [this]; exact hκ₀ g
  have hSupp : ∀ g, mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0 → SuppIn Sb (Vc D i) (κ g) :=
    fun g hg => by rw [hκ g hg]; exact (hG g hg).choose_spec.2.1
  have h0 := hclean ⟨PP, hPP⟩ (fun j => ρk (a j)) ha' false 1 (Or.inl rfl) ⟨v, hv, hOver⟩ κ hLifts hSupp
  have h1 := congrArg (fun φ' => ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) φ')) h0
  simp only [avgW, GlobalTheory.SplitScalar.heisO_sum, GlobalTheory.SplitScalar.heisO_smul, map_sum, map_smul, smul_eq_mul] at h1
  set Fn : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → ℂ := fun g =>
    ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map
      (algebraMap (OI v) (Fv D.host.F v)) * X)) f) with hFn
  rw [← GlobalTheory.T.mirabolicHyperplaneAverage_support_residueGL D G Pl0 T A Ks R i PP hPP v ρk a Fn, finsum_mem_def, finsum_eq_sum_of_fintype]
  have hz : heisO R.ψ (Vc D i) (Wc D i) (σ X) (0 : WO (Vc D i) (Wc D i) → ℂ) = 0 := by
    funext w; simp [heisO]
  rw [hz, map_zero] at h1
  refine (Finset.sum_congr rfl fun g _ => ?_).trans h1
  by_cases hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0
  · rw [Set.indicator_of_mem (show g ∈ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0} from hg), hκ g hg]
    exact ((hG g hg).choose_spec.2.2 X).symm
  · rw [Set.indicator_of_notMem (show g ∉ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0} from hg)]
    rw [not_not.1 hg, zero_mul, zero_mul]

end GlobalTheory.DownLift.HypAvg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOffOutsideS0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SplitOffS0

theorem main : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {ρ : Setup X}, ρ.Good → ∀ (i : X.Tw) (Q : Finset (Pl D.host.E)), (∀ P' ∈ Q, P' ∈ X.S0 i) → ∀ (P : Pl D.host.E), IsSplitPl D.host P → P ∉ X.S0 i → Bridge.SplitOff P (Q : Set (Pl D.host.E)) := by
  intro D N X ρ hρ i Q hQ P hsplit hP
  have hinv : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := fun z => Formalism.L2.Host.conj_conj (D := D) D.host z
  let c : 𝓞 D.host.E → 𝓞 D.host.E := fun x => RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x
  have hc : ∀ x : 𝓞 D.host.E, ((c x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := fun x => rfl
  have key : ∀ x y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) →
      (x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ↔ y ∈ P.asIdeal) :=
    fun x y h => GlobalTheory.Mem.Col2.HAt.mem_conjIdeal_Pv P.asIdeal x y h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx, hy⟩ := hsplit
    intro heq
    have h1 : c x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal :=
      (key (c x) x (by rw [hc, hinv])).2 hx
    exact hy (c x) (hc x) (heq ▸ h1)
  · intro hPQ
    exact hP (hQ P (by simpa using hPQ))
  · intro Q' hQ' heq
    apply hP
    refine hρ.goodSetup_badPlaces_conj i Q' (hQ Q' (by simpa using hQ')) P ?_
    intro x y hxy
    rw [heq]
    exact key x y hxy

end GlobalTheory.SplitOffS0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitSep

open GlobalTheory.SplitScalar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplO_nsmul_left (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = k • symplO S T x y := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, symplO_zero_left]
  | succ n ih => rw [succ_nsmul, succ_nsmul, GlobalTheory.LatVac.symplO_add_left, ih]

theorem symplO_nsmul_swap (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  rw [symplO_nsmul_left, symplO_skew S T (k • y) x, symplO_nsmul_left, symplO_skew S T x y, neg_nsmul, neg_neg]

theorem symplO_neg_left (x y : WO S T) : symplO S T (-x) y = -symplO S T x y := by
  have h := symplO_sub_left S T 0 x y
  rwa [zero_sub, symplO_zero_left, zero_sub] at h

theorem nsmul_smul_comm (k : ℕ) (a : AE D) (v : WO S T) : k • (a • v) = a • (k • v) := by
  induction k with
  | zero => rw [zero_nsmul, zero_nsmul, smul_zero]
  | succ n ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]

theorem isHalf_neg' {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) : IsHalf e (-u) := by
  rw [isHalf_iff] at *
  rw [smul_neg, hu]

theorem smul_eq_zero_of_half_conj {a : AE D} (ha : IsSplitIdem D a) {u : WO S T} (hu : IsHalf (cA D a) u) :
    a • u = 0 := by
  rw [← (isHalf_iff _ _).1 hu, smul_smul, ha.2.1, zero_smul]

theorem conj_smul_eq_zero_of_half {a : AE D} (ha : IsSplitIdem D a) {u : WO S T} (hu : IsHalf a u) :
    cA D a • u = 0 := by
  rw [← (isHalf_iff _ _).1 hu, smul_smul, mul_comm, ha.2.1, zero_smul]

theorem exists_nsmul_subgroup (Λ : AddSubgroup (WO S T)) (k : ℕ) :
    ∃ K : AddSubgroup (WO S T), ∀ d, d ∈ K ↔ ∃ v ∈ Λ, d = k • v := by
  refine ⟨{ carrier := {d | ∃ v ∈ Λ, d = k • v}
            add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun d => Iff.rfl⟩
  · rintro u w ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
    exact ⟨v + v', add_mem hv hv', by rw [nsmul_add]⟩
  · exact ⟨0, zero_mem _, by rw [nsmul_zero]⟩
  · rintro u ⟨v, hv, rfl⟩
    exact ⟨-v, neg_mem hv, by rw [neg_nsmul]⟩

theorem exists_mixed_subgroup {a : AE D} (ha : IsSplitIdem D a) (Λ : AddSubgroup (WO S T)) (k : ℕ) :
    ∃ Λ' : AddSubgroup (WO S T), (∀ u, IsHalf a u → (u ∈ Λ' ↔ ∃ v ∈ Λ, u = k • v)) ∧
      ∀ u, IsHalf (cA D a) u → (u ∈ Λ' ↔ k • u ∈ Λ) := by
  obtain ⟨Λ', hΛ'⟩ : ∃ Λ' : AddSubgroup (WO S T),
      ∀ u, u ∈ Λ' ↔ (∃ v ∈ Λ, a • u = k • v) ∧ k • (cA D a • u) ∈ Λ := by
    refine ⟨{ carrier := {u | (∃ v ∈ Λ, a • u = k • v) ∧ k • (cA D a • u) ∈ Λ}
              add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun u => Iff.rfl⟩
    · rintro u w ⟨⟨v, hv, huv⟩, hu⟩ ⟨⟨v', hv', hwv⟩, hw⟩
      refine ⟨⟨v + v', add_mem hv hv', by rw [smul_add, huv, hwv, nsmul_add]⟩, ?_⟩
      rw [smul_add, nsmul_add]
      exact add_mem hu hw
    · refine ⟨⟨0, zero_mem _, by rw [smul_zero, nsmul_zero]⟩, ?_⟩
      rw [smul_zero, nsmul_zero]
      exact zero_mem _
    · rintro u ⟨⟨v, hv, huv⟩, hu⟩
      refine ⟨⟨-v, neg_mem hv, by rw [smul_neg, huv, neg_nsmul]⟩, ?_⟩
      rw [smul_neg, neg_nsmul]
      exact neg_mem hu
  refine ⟨Λ', fun u hu => ?_, fun u hu => ?_⟩
  · rw [hΛ', (isHalf_iff _ _).1 hu, conj_smul_eq_zero_of_half ha hu, nsmul_zero]
    exact ⟨fun h => h.1, fun h => ⟨h, zero_mem _⟩⟩
  · have h0 : a • u = 0 := smul_eq_zero_of_half_conj ha hu
    have h1 : cA D a • u = u := (isHalf_iff _ _).1 hu
    rw [hΛ']
    constructor
    · rintro ⟨-, h⟩
      rwa [h1] at h
    · intro h
      exact ⟨⟨0, zero_mem _, by rw [h0, nsmul_zero]⟩, by rwa [h1]⟩

theorem rep_half {e : AE D} (he : e * e = e) {Λ : AddSubgroup (WO S T)} (hstab : ∀ u ∈ Λ, e • u ∈ Λ) {k : ℕ}
    {d : WO S T} (hd : IsHalf e d) (h : ∃ v ∈ Λ, d = k • v) : ∃ v ∈ Λ, IsHalf e v ∧ d = k • v := by
  obtain ⟨v, hv, h⟩ := h
  exact ⟨e • v, hstab v hv, isHalf_smul he v, by rw [nsmul_smul_comm, ← h, (isHalf_iff _ _).1 hd]⟩

theorem sum_average {a : AE D} (ha : IsSplitIdem D a) {Λ : AddSubgroup (WO S T)} {k : ℕ} {f : WO S T → ℂ}
    (hfix : ∀ u ∈ Λ, IsHalf (cA D a) u → heisO ψ S T (k • u) f = f)
    {Y X : Finset (WO S T)}
    (hY : ∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ Λ)
    (hYu : ∀ y', IsHalf (cA D a) y' → k • y' ∈ Λ →
      ∃! y, y ∈ Y ∧ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y' - y = k • u)
    (hX : ∀ x ∈ X, IsHalf a x)
    (hXo : ∀ y, IsHalf (cA D a) y → k • y ∈ Λ →
      ((∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u) → ∀ x ∈ X, ψ (symplO S T y x) = 1) ∧
      ((¬ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u) → ∑ x ∈ X, ψ (symplO S T y x) = 0)) :
    ∑ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = (X.card : ℂ) • f := by
  have e1 : ∀ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) =
      ∑ y ∈ Y, ψ (symplO S T y x) • heisO ψ S T y f := by
    intro x hx
    rw [heisO_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [heisO_comm, ← heisO_add_of_orth ψ S T (half_orth ha (isHalf_neg' (hX x hx)) (hX x hx)),
      neg_add_cancel, heisO_zero, symplO_neg_left, ← symplO_skew]
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  obtain ⟨y₀, ⟨hy₀Y, u₀, hu₀, hu₀h, hy₀⟩, huniq⟩ :=
    hYu 0 (isHalf_zero _) (by rw [nsmul_zero]; exact zero_mem _)
  rw [Finset.sum_eq_single_of_mem y₀ hy₀Y]
  · have hy₀' : y₀ = k • (-u₀) := by rw [neg_nsmul, ← hy₀, zero_sub, neg_neg]
    have hyy : ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y₀ = k • u := ⟨-u₀, neg_mem hu₀, isHalf_neg' hu₀h, hy₀'⟩
    rw [Finset.sum_congr rfl ((hXo y₀ (hY y₀ hy₀Y).1 (hY y₀ hy₀Y).2).1 hyy), Finset.sum_const, nsmul_eq_mul,
      mul_one, hy₀', hfix _ (neg_mem hu₀) (isHalf_neg' hu₀h)]
  · intro y hy hne
    have hnot : ¬ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y = k • u := by
      rintro ⟨u, hu, huh, rfl⟩
      exact hne (huniq _ ⟨hy, -u, neg_mem hu, isHalf_neg' huh, by rw [zero_sub, neg_nsmul]⟩)
    rw [(hXo y (hY y hy).1 (hY y hy).2).2 hnot, zero_smul]

theorem sum_translates_eq_zero {a : AE D} (ha : IsSplitIdem D a) (hψ : IsStdChar D ψ (-1)) {Λ : AddSubgroup (WO S T)}
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hpair : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1)
    (hstab : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ)
    {k : ℕ} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hfix : ∀ u ∈ Λ, IsHalf a u ∨ IsHalf (cA D a) u → heisO ψ S T (k • u) f = f)
    {Y : Finset (WO S T)}
    (hY : ∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ Λ)
    (hYu : ∀ y', IsHalf (cA D a) y' → k • y' ∈ Λ →
      ∃! y, y ∈ Y ∧ ∃ u ∈ Λ, IsHalf (cA D a) u ∧ y' - y = k • u)
    (hℓ : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0)
    {x : WO S T} (hxa : IsHalf a x) (hkx : k • x ∈ Λ) :
    ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) = 0 := by
  have ha' := isSplitIdem_conj ha
  have hcc : cA D (cA D a) = a := GlobalTheory.DualPairCheck.cA_cA a
  obtain ⟨K, hK⟩ := exists_nsmul_subgroup Λ k
  obtain ⟨Λ', memA, memC⟩ := exists_mixed_subgroup ha Λ k
  have hYK : ∀ u', IsHalf (cA D a) u' → k • u' ∈ Λ → ∃! v, v ∈ Y ∧ u' - v ∈ K := by
    intro u' hu' hku'
    obtain ⟨y, ⟨hyY, w, hw, -, hyw⟩, huniq⟩ := hYu u' hu' hku'
    refine ⟨y, ⟨hyY, (hK _).2 ⟨w, hw, hyw⟩⟩, fun y' hy' => huniq y' ⟨hy'.1, ?_⟩⟩
    exact rep_half ha'.1 (hstab _ ha'.1) (isHalf_sub hu' (hY y' hy'.1).1) ((hK _).1 hy'.2)
  by_contra hn
  have hfx : IsThetaFunO ψ S T (heisO ψ S T x f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf x
  have hGx : ∀ d, IsHalf (cA D a) d → d ∈ K → heisO ψ S T d (heisO ψ S T x f) = heisO ψ S T x f := by
    intro d hdh hdK
    obtain ⟨v, hv, hvh, rfl⟩ := rep_half ha'.1 (hstab _ ha'.1) hdh ((hK d).1 hdK)
    rw [heisO_comm, symplO_nsmul_swap, hpair v hv _ hkx, one_smul, hfix v hv (Or.inr hvh)]
  have hd : ∀ y, IsHalf (cA D a) y → y ∉ Λ' → ∃ l ∈ Λ', IsHalf (cA D (cA D a)) l ∧ ψ (symplO S T l y) ≠ 1 := by
    intro y hy hyΛ'
    have hky : k • y ∉ Λ := fun h => hyΛ' ((memC y hy).2 h)
    obtain ⟨l, hl, hlh, hne⟩ := exists_dual_half ha' hdual (hstab _ (by rw [hcc]; exact ha.1))
      (isHalf_nsmul hy k) hky
    refine ⟨k • l, ?_, isHalf_nsmul hlh k, by rwa [symplO_nsmul_swap]⟩
    rw [hcc] at hlh
    exact (memA _ (isHalf_nsmul hlh k)).2 ⟨l, hl, rfl⟩
  have h1 : ∀ u ∈ Λ', IsHalf (cA D a) u →
      heisO ψ S T u (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) :=
    fun u hu huh => sum_reps_invariant (ψ := ψ) (Λ := K) (Λ' := Λ') ha'
      (fun y hy => ⟨(memC y (hY y hy).1).2 (hY y hy).2, (hY y hy).1⟩)
      (fun u' hu' hu'h => hYK u' hu'h ((memC u' hu'h).1 hu')) (fun d hdK _ hdh => hGx d hdh hdK) hu huh
  have h2 : ∀ u ∈ Λ', IsHalf (cA D (cA D a)) u →
      heisO ψ S T u (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) := by
    intro u hu huh
    rw [hcc] at huh
    obtain ⟨v, hv, hvh, rfl⟩ := rep_half ha.1 (hstab _ ha.1) huh ((memA u huh).1 hu)
    rw [heisO_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [heisO_comm, symplO_nsmul_swap, hpair v hv _ (hY y hy).2, one_smul, heisO_comm ψ S T (k • v) x,
      half_orth ha (isHalf_nsmul hvh k) hxa, AddChar.map_zero_eq_one, one_smul, hfix v hv (Or.inl hvh)]
  obtain ⟨ℓ, hℓ0, hℓinv⟩ := GlobalTheory.SplitHecke.exists_invariant_form' (Λ := Λ') (ψ := ψ) ha' hd hn h1 h2
  apply hℓ0
  rw [map_sum, Finset.sum_congr rfl fun y hy => hℓinv y (hY y hy).1 _ hfx, hℓ ℓ hℓinv x hxa,
    Finset.sum_const_zero]

theorem invForms_separate (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (hψ : IsStdChar D ψ (-1)) (a : AE D)
    (ha : IsSplitIdem D a) (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f)
    (hℓ : ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0) : f = 0 := by
  have hS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  have ha' := isSplitIdem_conj ha
  obtain ⟨k, hk, hfix, -⟩ := (GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split D ψ S T hψ _ _ hS hT a ha f hf).1
  obtain ⟨Y, -, hY, hYu, -⟩ := GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ _ _ hS hT a ha.1 (infPart_splitIdem ha) k hk
  obtain ⟨X, hXne, hX, -, hXo⟩ := GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ _ _ hS hT (cA D a) ha'.1 (infPart_splitIdem ha') k hk
  rw [GlobalTheory.DualPairCheck.cA_cA] at hX
  have hdual : ∀ u : WO S T, u.map (infPart D) = 0 →
      (u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) ↔
        ∀ u' ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), ψ (symplO S T u u') = 1) :=
    (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfinΛ : ∀ u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T), u.map (infPart D) = 0 :=
    fun u hu => latO_fin hu
  have hstab : ∀ e : AE D, e * e = e → ∀ u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T),
      e • u ∈ latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) :=
    fun e he => idem_smul_mem he
  generalize latH S T (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T) = Λ at *
  have hpair : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u u') = 1 := fun u hu => (hdual u (hfinΛ u hu)).1 hu
  have hB : ∀ x ∈ X, ∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f) = 0 := fun x hx =>
    sum_translates_eq_zero ha hψ hdual hpair hstab hf hfix hY hYu hℓ (hX x hx).1 (hX x hx).2
  have hA := sum_average (ψ := ψ) ha (fun u hu huh => hfix u hu (Or.inr huh)) hY hYu (fun x hx => (hX x hx).1) hXo
  have h0 : ∑ x ∈ X, heisO ψ S T (-x) (∑ y ∈ Y, heisO ψ S T y (heisO ψ S T x f)) = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hB x hx]
    exact (heisL ψ S T (-x)).map_zero
  rw [h0] at hA
  have hc : (X.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hXne)
  exact (smul_eq_zero.1 hA.symm).resolve_left hc

end GlobalTheory.DownLift.SplitSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumVector_drop_auxiliary_places : ∀ (D : D7) (S T : HSp D) (B : Base S T) (Q Q' : Finset (Pl D.host.E)) [DecidablePred (· ∈ Q')] (φ : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ), B.Good → B.admitted Q → Q' ⊆ Q → B.vecAt Q (fun PP y => if PP.1 ∈ Q' then φ PP.1 y else 1) = B.vecAt Q' fun PP => φ PP.1 := by
  first | exact @GlobalTheory.ExportSeries.vecAt_drop | exact GlobalTheory.ExportSeries.vecAt_drop | (intros; apply GlobalTheory.ExportSeries.vecAt_drop <;> assumption)
end

