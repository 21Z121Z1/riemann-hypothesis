import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0749
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0774
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootsMinpolyPhi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelAveragesThetaPairZeroWithoutCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem representation_inv_mul_apply_cancel_left {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (γ h : H)
    (v : W) : ρ (γ * h)⁻¹ (ρ γ v) = ρ h⁻¹ v := by
  rw [← Module.End.mul_apply, ← map_mul]; congr 2; group

theorem representation_inv_mul_smul_one_of_trivial_right {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : H →* Module.End ℂ W) (h κ : H)
    (hκ : ρ κ⁻¹ = 1) (c : ℂ) (v : W) : ρ (h * κ)⁻¹ (c • ρ 1 v) = c • ρ h⁻¹ v := by
  rw [map_one, Module.End.one_apply, map_smul, _root_.mul_inv_rev, map_mul, hκ, one_mul]

theorem extV_law (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (γ : GQ (Vc D i)) (x : Formalism.IndefR.Bridge.Gf (Vc D i)) (k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) :
    (R.HV i t).e y (Formalism.IndefR.Bridge.ratF (Vc D i) γ * x * k) =
      ((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂ) • (R.cV i).ρ γ ((R.HV i t).e y x) := by
  have h1 : (R.HV i t).e y ∈ LinearMap.range (R.HV i t).e := LinearMap.mem_range_self _ _
  exact (SetLike.ext_iff.mp (hM.HV i t).2.1 ((R.HV i t).e y)).mp h1 γ x k

theorem extV_left (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    R.extV i t y (γ * h) = R.extV i t y h := by
  have hx : (finHom (Vc D i)).rangeRestrict (γ * h) = Formalism.IndefR.Bridge.ratF (Vc D i) ⟨γ, hγ⟩ *
      (finHom (Vc D i)).rangeRestrict h * ((1 : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J) : Formalism.IndefR.Bridge.Gf (Vc D i)) := by
    apply Subtype.ext
    simp [Formalism.IndefR.Bridge.ratF]
  have e : (R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (γ * h)) = (R.cV i).ρ γ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)) := by
    calc _ = _ := congrArg _ hx
      _ = _ := extV_law R hM i t y ⟨γ, hγ⟩ ((finHom (Vc D i)).rangeRestrict h) 1
      _ = _ := by simp only [map_one, Units.val_one, one_smul]
  show (R.cV i).ρ (γ * h)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (γ * h))) =
    (R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))
  refine (congrArg _ e).trans ?_
  exact representation_inv_mul_apply_cancel_left _ γ h _

theorem extV_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (κ : GA D (Vc D i)) (hκ : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t))) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ • R.extV i t y h := by
  let k : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J := ⟨(finHom (Vc D i)).rangeRestrict κ, hκ.2⟩
  have hx : (finHom (Vc D i)).rangeRestrict (h * κ) = Formalism.IndefR.Bridge.ratF (Vc D i) 1 *
      (finHom (Vc D i)).rangeRestrict h * (k : Formalism.IndefR.Bridge.Gf (Vc D i)) := by
    apply Subtype.ext
    simp [k]
  have hχ : (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ k : ℂˣ) : ℂ) =
      levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ := rfl
  have e : (R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ)) =
      levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ • (R.cV i).ρ 1 ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h)) := by
    calc _ = _ := congrArg _ hx
      _ = _ := extV_law R hM i t y 1 ((finHom (Vc D i)).rangeRestrict h) k
      _ = _ := congrArg (· • _) hχ
  show (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict (h * κ))) =
    _ • (R.cV i).ρ h⁻¹ ((R.HV i t).e y ((finHom (Vc D i)).rangeRestrict h))
  refine (congrArg _ e).trans ?_
  exact representation_inv_mul_smul_one_of_trivial_right _ h κ ((hM.cV i).1 _ ((GfC (Vc D i)).inv_mem hκ.1)) _ _

def compF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ) :
    GA D (Vc D i) → ℂ :=
  fun h => l (R.extV i t y h)

theorem compF_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) : HasType (Vc D i) (R.βV i) (flag1L (R.datVt i t)) (compF R i t y l) := by
  intro k hk h
  exact (congrArg l (extV_type R hM i t y k hk h)).trans (by rw [map_smul, smul_eq_mul]; rfl)

theorem compF_left (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    compF R i t y l (γ * h) = compF R i t y l h :=
  congrArg l (extV_left R hM i t y γ hγ h)

theorem theta_left (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
    (hP : R.FullP)
    (φ : WO (Vc D i) (Wc D i) → ℂ) (hφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ) (g : GA D (Wc D i))
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) (γ * h) g φ = thetaKO (R.ωP i t) h g φ := by
  have hm : ((γ * h, g) : GA D (Vc D i) × GA D (Wc D i)) = (γ, 1) * (h, g) := by rw [Prod.mk_mul_mk, one_mul]
  show R.ωP i t (γ * h, g) φ 0 = R.ωP i t (h, g) φ 0
  rw [hm, map_mul, Module.End.mul_apply]
  exact (hP i t).datum.om_aut γ hγ 1 (GQ (Wc D i)).one_mem _ ((hP i t).datum.om_pres _ φ hφ)

theorem theta_transl (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (φ : WO (Vc D i) (Wc D i) → ℂ)
    (g : GA D (Wc D i)) (κ h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) φ) = thetaKO (R.ωP i t) (h * κ) g φ := by
  show R.ωP i t (h, g) (R.ωP i t (κ, 1) φ) 0 = R.ωP i t (h * κ, g) φ 0
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem theta_avgW (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (tr : Bool)
    (ε : ℤ) (κ : G → GA D (Vc D i)) (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (h : GA D (Vc D i)) :
    thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) =
      ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
        thetaKO (R.ωP i t) (h * (κ j)⁻¹) g f := by
  rw [← Finset.sum_congr rfl fun j _ => congrArg (_ * ·) (theta_transl R i t f g (κ j)⁻¹ h)]
  show R.ωP i t (h, g) (avgW R i t PP a tr ε κ f) 0 = _
  simp only [avgW, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

theorem sum_compF_eq_zero (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (hNC : NoChi R i t y) (PP : R.Pg) (a : Fin D.R.r → kP PP.1) (ha : a ≠ 0) (tr : Bool) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (κ : G → GA D (Vc D i)) (hκ : IsLifts R i t κ) (l : (R.cV i).W →ₗ[ℂ] ℂ) (h : GA D (Vc D i)) :
    ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
      compF R i t y l (h * κ j) = 0 := by
  have h0 := congrFun (hNC PP a ha tr ε hε l) h
  refine Eq.trans ?_ h0
  simp only [gaL, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  show _ = mirC R i PP a tr ε j * actG0 (Vc D i) (R.βV i) (R.datVt i t) (R.eG j) (compF R i t y l) h
  rw [level_action_spec (compF_type R hM i t y l) ⟨κ j, hκ j⟩ (κ j) (hκ j) h]
  ring

def termF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (κ : GA D (Vc D i)) : GA D (Vc D i) → ℂ :=
  fun h => thetaKO (R.ωP i t) (h * κ⁻¹) g f * compF R i t y l h

theorem termF_eq (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (l : (R.cV i).W →ₗ[ℂ] ℂ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (g : GA D (Wc D i)) (κ : GA D (Vc D i)) :
    (fun h => thetaKO (R.ωP i t) h g (R.ωP i t (κ⁻¹, 1) f) * l (R.extV i t y h)) = termF R i t y l f g κ := by
  funext h
  exact congrArg (· * l (R.extV i t y h)) (theta_transl R i t f g κ⁻¹ h)

theorem termF_left (R : RealDat D A Ks) (hM : R.IsModels) (hP : R.FullP) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f)
    (g : GA D (Wc D i)) (κ : GA D (Vc D i)) (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) :
    termF R i t y l f g κ (γ * h) = termF R i t y l f g κ h := by
  show thetaKO (R.ωP i t) (γ * h * κ⁻¹) g f * compF R i t y l (γ * h) =
    thetaKO (R.ωP i t) (h * κ⁻¹) g f * compF R i t y l h
  rw [mul_assoc, theta_left R i t hP f hf g γ hγ, compF_left R hM i t y l γ hγ h]

theorem avgLaw : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H), NoChi R i t y → ∀ (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 → ∀ (tr : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ κ : G → GA D (Vc D i), GlobalTheory.DownLift.GenFinite.IsLifts R i t κ → ∀ f : WO (Vc D i) (Wc D i) → ℂ, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (GlobalTheory.DownLift.GenFinite.avgW R i t PP a tr ε κ f) l g = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hNC PP a ha tr ε hε κ hκ f hf l g
  have hM := hG.core.models
  obtain ⟨hmeas, hfd⟩ := hM.νV i t
  haveI : (R.νV i t).IsHaarMeasure := hmeas.1
  haveI : IsTopologicalGroup (GA D (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Vc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Vc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  haveI : (R.νV i t).IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds _ _ hmeas.1
  have hu_int : ∀ j, IntegrableOn (termF R i t y l f g (κ j)) (R.fdV i t) (R.νV i t) := by
    intro j
    have h1 := GlobalTheory.T.integrableOn_downwardThetaLift_integrand D G Pl0 T A Ks R F hG hP i t y (R.ωP i t ((κ j)⁻¹, 1) f) l g
      ((hP i t).datum.om_pres _ f hf)
    exact (congrArg (fun φ => IntegrableOn φ (R.fdV i t) (R.νV i t)) (termF_eq R i t y l f g (κ j))).mp h1
  have hv_int : ∀ j, IntegrableOn (fun h => termF R i t y l f g (κ j) (h * κ j)) (R.fdV i t) (R.νV i t) :=
    fun j => GlobalTheory.integrableOn_fundamentalDomain_mul_right hfd (κ j) _
      (fun γ hγ h => termF_left R hM hP i t y l f hf g (κ j) γ hγ h) (hu_int j)
  have hsub : ∀ j, ∫ h in R.fdV i t, termF R i t y l f g (κ j) h ∂(R.νV i t) =
      ∫ h in R.fdV i t, termF R i t y l f g (κ j) (h * κ j) ∂(R.νV i t) :=
    fun j => (GlobalTheory.setIntegral_fundamentalDomain_mul_right hfd (κ j) _
      (fun γ hγ h => termF_left R hM hP i t y l f hf g (κ j) γ hγ h)).symm
  have hpt1 : ∀ h, thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) * compF R i t y l h =
      ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
        termF R i t y l f g (κ j) h := by
    intro h
    rw [theta_avgW, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  have hpt2 : ∀ h, ∑ j, (mirC R i PP a tr ε j * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ j))⁻¹) *
      termF R i t y l f g (κ j) (h * κ j) = 0 := by
    intro h
    have e : ∀ j, termF R i t y l f g (κ j) (h * κ j) = thetaKO (R.ωP i t) h g f * compF R i t y l (h * κ j) := by
      intro j
      show thetaKO (R.ωP i t) (h * κ j * (κ j)⁻¹) g f * _ = _
      rw [mul_inv_cancel_right]
    simp only [e]
    rw [← mul_zero (thetaKO (R.ωP i t) h g f), ← sum_compF_eq_zero R hM i t y hNC PP a ha tr ε hε κ hκ l h,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g (avgW R i t PP a tr ε κ f) * compF R i t y l h ∂(R.νV i t) = 0
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt1),
    integral_finset_sum _ fun j _ => (hu_int j).const_mul _]
  simp only [integral_const_mul]
  simp only [hsub]
  simp only [← integral_const_mul]
  rw [← integral_finset_sum _ fun j _ => (hv_int j).const_mul _]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt2)]
  exact integral_zero _ _

end GlobalTheory.DownLift.GenFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogIdealSupportFinite
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.AdBridge

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m r : ℕ}

theorem Aof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Aof (M.map f) = (Aof M).map f := rfl
theorem Bof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Bof (M.map f) = (Bof M).map f := rfl
theorem Cof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Cof (M.map f) = (Cof M).map f := rfl
theorem Dof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Dof (M.map f) = (Dof M).map f := rfl

theorem inv_map_of_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (h : IsUnit A.det) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one f (map_zero f) (map_one f)]

theorem Yof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Yof (M.map f) = (Yof M).map f := by
  rw [Yof, Yof, Matrix.map_mul, Dof_map, Cof_map, inv_map_of_isUnit f _ h]

theorem Xof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Xof (M.map f) = (Xof M).map f := by
  rw [Xof, Xof, Matrix.map_mul, Dof_map, Bof_map, inv_map_of_isUnit f _ h]

theorem Scof_map (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    Scof (M.map f) = (Scof M).map f := by
  rw [Scof, Scof, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, Aof_map, Dof_map, Bof_map, Cof_map,
    inv_map_of_isUnit f _ h]

theorem lowUni_map (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) :
    (lowUni Y).map f = lowUni (Y.map f) := by
  ext i j
  simp only [lowUni, unblk, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (eqv m r i) with a | a <;> rcases (eqv m r j) with b | b <;>
    simp [Matrix.one_apply, apply_ite f]

theorem conjLowUni_map (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (conjLowUni Y k).map f = conjLowUni (Y.map f) (k.map f) := by
  rw [conjLowUni, conjLowUni, Matrix.map_mul, Matrix.map_mul, lowUni_map, lowUni_map, Matrix.map_neg _ (map_neg f)]

end Maps

section Ones

variable {R : Type} [CommRing R] {m r : ℕ}

theorem blk_one : blk (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  simp [blk]

theorem Aof_one : Aof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Aof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
theorem Bof_one : Bof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Bof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂]
theorem Cof_one : Cof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Cof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]
theorem Dof_one : Dof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Dof, blk_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]
theorem Yof_one : Yof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Yof, Cof_one, Matrix.mul_zero]
theorem Xof_one : Xof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 0 := by
  rw [Xof, Bof_one, Matrix.zero_mul]
theorem Scof_one : Scof (1 : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) = 1 := by
  rw [Scof, Aof_one, Bof_one, Cof_one]; simp

theorem unblk_mul (P Q : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    unblk P * unblk Q = unblk (P * Q) := Matrix.submatrix_mul_equiv _ _ _ _ _

theorem unblk_one : unblk (1 : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) = 1 := by
  simp [unblk]

theorem lowUni_mul_neg (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : lowUni Y * lowUni (-Y) = 1 := by
  rw [lowUni, lowUni, unblk_mul, Matrix.fromBlocks_multiply]
  simp [unblk_one]

theorem conjLowUni_one (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : conjLowUni Y 1 = 1 := by
  rw [conjLowUni, Matrix.mul_one, lowUni_mul_neg]

theorem det_lowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) : (lowUni (m := m) Y).det = 1 := by
  rw [lowUni, unblk, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]; simp

theorem det_conjLowUni (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) R) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (conjLowUni Y k).det = k.det := by
  rw [conjLowUni, Matrix.det_mul, Matrix.det_mul, det_lowUni, det_lowUni]; ring

theorem det_eq_det_Dof_mul (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    M.det = (Dof M).det * (Scof M).det := by
  letI := Matrix.invertibleOfIsUnitDet _ h
  have e : Matrix.fromBlocks (Aof M) (Bof M) (Cof M) (Dof M) = blk M := Matrix.fromBlocks_toBlocks _
  have h1 : M.det = (blk M).det := by rw [blk, Matrix.det_submatrix_equiv_self]
  rw [h1, ← e, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]; rfl

theorem isUnit_det_Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hM : IsUnit M.det)
    (h : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  rw [det_eq_det_Dof_mul M h] at hM
  exact isUnit_of_mul_isUnit_right hM

end Ones

section Adeles

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem pInf_sFin_eq_zero (b : Af E) : pInf E (sFin E b) = 0 := map_zero (infEq E).symm

omit [IsTotallyComplex E] in
theorem pFin_sFin_eq (b : Af E) : pFin E (sFin E b) = b := rfl

theorem isUnit_of_parts {x : Ad E} (h1 : IsUnit (pInf E x)) (h2 : IsUnit (pFin E x)) : IsUnit x := by
  refine Prod.isUnit_iff.2 ⟨?_, h2⟩
  have e : (infEq E) (pInf E x) = x.1 := (infEq E).apply_symm_apply x.1
  rw [← e]; exact h1.map _

theorem map_pInf_finGL {n : ℕ} (k : GL (Fin n) (Af E)) :
    (finGL E n k : Matrix (Fin n) (Fin n) (Ad E)).map (pInf E) = 1 :=
  congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E))) (pInf_finGL k)

omit [IsTotallyComplex E] in
theorem map_pFin_finGL {n : ℕ} (k : GL (Fin n) (Af E)) :
    (finGL E n k : Matrix (Fin n) (Fin n) (Ad E)).map (pFin E) = (k : Matrix (Fin n) (Fin n) (Af E)) :=
  congrArg (fun g : GL (Fin n) (Af E) => (g : Matrix (Fin n) (Fin n) (Af E))) (pFin_finGL k)

theorem coe_finGL_mkGL {n : ℕ} (M : Matrix (Fin n) (Fin n) (Ad E)) (hi : M.map (pInf E) = 1) (hu : IsUnit M.det) :
    (finGL E n (mkGL (M.map (pFin E))) : Matrix (Fin n) (Fin n) (Ad E)) = M := by
  have hu' : IsUnit (M.map (pFin E)).det := by
    have h := hu.map (pFin E)
    rwa [RingHom.map_det] at h
  ext i j
  refine ad_ext ?_ ?_
  · exact congrFun (congrFun ((map_pInf_finGL _).trans hi.symm) i) j
  · exact congrFun (congrFun ((map_pFin_finGL _).trans (coe_mkGL hu')) i) j

end Adeles

theorem schur_data_mul_finGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := by
  intro E _ _ _ m r x k hD hD'
  rw [Units.val_mul]
  have hx : IsUnit (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
  have hK : IsUnit (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (finGL E (m + r + 1 + 1) k).isUnit
  have hKi := map_pInf_finGL (E := E) k
  have hKf := map_pFin_finGL (E := E) k
  generalize (finGL E (m + r + 1 + 1) k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = K at *
  generalize (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) = g at *
  have hf : conjLowUni ((Yof g).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)) =
      (conjLowUni (Yof g) K).map (pFin E) := by rw [conjLowUni_map, hKf]
  have hi : (conjLowUni (Yof g) K).map (pInf E) = 1 := by rw [conjLowUni_map, hKi, conjLowUni_one]
  have hdet : IsUnit (conjLowUni (Yof g) K).det := by rwa [det_conjLowUni]
  rw [hf] at hD' ⊢
  have alg := GlobalTheory.T.lower_unipotent_conj_block_formulas (Ad E) m r g K hD
  generalize conjLowUni (Yof g) K = L at *
  have hDi : (Dof L).map (pInf E) = 1 := by rw [← Dof_map, hi, Dof_one]
  have hDL : IsUnit (Dof L).det := by
    refine isUnit_of_parts ?_ ?_
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, hDi, Matrix.det_one]; exact isUnit_one
    · rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Dof_map]; exact hD'
  obtain ⟨a1, a2, a3, a4, a5⟩ := alg hDL
  have hS := isUnit_det_Scof g hx hD
  have hSL := isUnit_det_Scof L hdet hDL
  have hSi : (Scof L).map (pInf E) = 1 := by rw [← Scof_map _ _ hDL, hi, Scof_one]
  have hYi : (Yof L).map (pInf E) = 0 := by rw [← Yof_map _ _ hDL, hi, Yof_one]
  have hXi : (Xof L).map (pInf E) = 0 := by rw [← Xof_map _ _ hDL, hi, Xof_one]
  have hXi' : ∀ j l, pInf E (Xof L j l) = 0 := fun j l => congrFun (congrFun hXi j) l
  refine ⟨hS, a1, Units.ext ?_, Units.ext ?_, fun i j => ?_, fun i j => ?_, ?_⟩
  · rw [coe_mkGL a1, Units.val_mul, coe_mkGL hD, Dof_map, coe_finGL_mkGL _ hDi hDL, a2]
  · have hSgK : IsUnit (Scof (g * K)).det := by rw [a4, Matrix.det_mul]; exact hS.mul hSL
    rw [coe_mkGL hSgK, Units.val_mul, coe_mkGL hS, Scof_map _ _ hDL, coe_finGL_mkGL _ hSi hSL, a4]
  · have h0 : pInf E (Yof L i j) = 0 := congrFun (congrFun hYi i) j
    rw [a3, Matrix.add_apply, map_add, h0, add_zero]
  · rw [a3, Matrix.add_apply, map_add, Yof_map _ _ hDL, Matrix.map_apply]
  · rw [a5, Matrix.add_apply, Xof_map _ _ hDL]
    congr 1
    refine ad_ext ?_ ?_
    · rw [pInf_sFin_eq_zero]
      simp only [Matrix.mul_apply, map_sum, map_mul, hXi', mul_zero, Finset.sum_const_zero, zero_mul]
    · rw [pFin_sFin_eq, Finset.sum_comm]
      simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Matrix.map_apply]

end GlobalTheory.SchurExt.AdBridge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeterssonIntegralFormula
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

noncomputable section

namespace GlobalTheory.AdjUp

theorem ip_eq_mul_integral_val : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ),
    IsUnitVec R i v → ∃ P : ℝ, 0 ≤ P ∧ ∀ y z : (R.HW i (sg0 D A)).H,
      ⟪y, z⟫_ℂ = (P : ℂ) * ∫ g in R.fdW i, star (val R i v y g) * val R i v z g ∂(R.νW i) := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL i v hv
  obtain ⟨-, hr, hip⟩ := hL.models.HW i (sg0 D A)
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hS := (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hC R).2.2 i

  set Q : ℝ := ∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℝ) with hQ
  have hQc : (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) = (Q : ℂ) := by
    rw [hQ, Complex.ofReal_prod]; rfl

  have key : ∀ y z : (R.HW i (sg0 D A)).H,
      ⟪y, z⟫_ℂ = (Q : ℂ) * ∫ g in R.fdW i, star (val R i v y g) * val R i v z g ∂(R.νW i) := by
    intro y z
    obtain ⟨c, hc⟩ := hS hL.models.inf (hL.models.νW i).1.1 (hL.models.νW i).2 _ (hmem y) _ (hmem z)
    have hex : ∃ c, IsMultIP (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e y)
        ((R.HW i (sg0 D A)).e z) c := ⟨c, hc⟩
    have hv1 := (hex.choose_spec (fun ρ => v ρ) (fun ρ => v ρ)).2
    have hprod : (∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) = 1 := by
      refine Finset.prod_eq_one fun ρ _ => ?_
      rw [inner_self_eq_norm_sq_to_K, hv ρ]
      norm_num
    rw [hip, ipAt, hQc, ipM, dif_pos hex]
    unfold val
    rw [hv1, hprod, mul_one]
  by_cases h0 : 0 ≤ Q
  · exact ⟨Q, h0, key⟩
  ·
    refine ⟨0, le_rfl, fun y z => ?_⟩
    have hy : y = 0 := by
      have e1 := key y y
      have hnn : 0 ≤ ∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) :=
        MeasureTheory.setIntegral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => by positivity)
      have hI : (∫ g in R.fdW i, star (val R i v y g) * val R i v y g ∂(R.νW i)) =
          ((∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only
        rw [Complex.ofReal_pow, ← Complex.conj_mul']
        rfl
      rw [hI] at e1
      have e2 : ‖y‖ ^ 2 = Q * ∫ g in R.fdW i, ‖val R i v y g‖ ^ 2 ∂(R.νW i) := by
        have := congrArg Complex.re e1
        rw [inner_self_eq_norm_sq_to_K] at this
        simpa [← Complex.ofReal_pow, Complex.re_ofReal_mul] using this
      have hle : ‖y‖ ^ 2 ≤ 0 := by
        rw [e2]; exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 h0)) hnn
      have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
      exact norm_eq_zero.1 this
    rw [hy, inner_zero_left, Complex.ofReal_zero, zero_mul]

end GlobalTheory.AdjUp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentStarCompatibleOfLabellingAgree
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodTypes

theorem seriesConj_of_labTie : Green → ∀ (D : D7) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L →
    GlobalTheory.GoodTypes.SeriesConj D :=
  fun hG D L hL k f hf =>
    GlobalTheory.GLq.GalSer.eSer_galois hG D ((eSerTie_iff D).2 ⟨L, hL⟩) starRingAut k f hf

end GlobalTheory.GoodTypes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilDoublingProductRationalTranslateEqFramStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeilDoublingProduct_rational_translate_eq_frame : ∀ (D : D7) (V W : HSp D) (f₁ f₂ : WO V W → ℂ) (γ : GA D (GlobalTheory.Doubling.dblSp W)) (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E), Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) → ∀ (y : Mx D V.rank W.rank), GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V γ⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) = f₁ (ratMul (frameOf W g₀).1 (GlobalTheory.PairLift.adjO V W y)) * star (f₂ (ratMul (frameOf W g₀).2 (GlobalTheory.PairLift.adjO V W y))) := by
  first | exact @GlobalTheory.SWLagTerms.dbl_actO_lagr | exact GlobalTheory.SWLagTerms.dbl_actO_lagr | (intros; apply GlobalTheory.SWLagTerms.dbl_actO_lagr <;> assumption)
end

