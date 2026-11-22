import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0730
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0504
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0525
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0577
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0487
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0135
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0100
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0104
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0091
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0728
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0729
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0731
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicMeasureEulerProductDecomposition
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0393
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHolds
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}

theorem mcast_spec {a b : ℕ} (h : a = b) (Y : MRep k a) :
    ∃ e : Y.V ≃ₗ[ℂ] (mcast h Y).V, ∀ x v, e (Y.ρ x v) = (mcast h Y).ρ (castM k h x) (e v) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem dpowM_castM {a b : ℕ} (h : a = b) (s : ℝ) (x : Mir k a) : dpowM b s (castM k h x) = dpowM a s x := by
  subst h
  rfl

theorem mExt_mcast {a b : ℕ} (h : a = b) {A B C : MRep k a} (H : MExt A B C) :
    MExt (mcast h A) (mcast h B) (mcast h C) := by
  subst h
  exact H

theorem phiN_mcast (ψ : AddChar k Circle) {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1) (X : MRep k (a + 1)) :
    phiN ψ (mcast h' X) = mcast h (phiN ψ X) := by
  subst h
  rfl

theorem mcast_mcast {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c) (X : MRep k a) :
    mcast h₂ (mcast h₁ X) = mcast h₃ X := by
  subst h₁
  subst h₂
  rfl

theorem evX_cInd {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (g p : Mir k ((i + 1) + t + 1)) :
    evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) p = evX f (p * g) := rfl

theorem intC_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g y : Mir k ((i + 1) + t + 1)) :
    intC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y = intC ψ f (y * g) := by
  simp only [intC, evX_cInd, mul_assoc]

theorem intO_translate {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g y : Mir k ((i + 1) + t + 1)) :
    intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y = intO f (y * g) := by
  simp only [intO, evX_cInd, mul_assoc]

abbrev XR (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t + 1) := prodPGn (i := i + 1) (t := t + 1) τ σ

theorem eC_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (x m : Mir k ((i + 1) + t)) :
    eC ψ f (x * m) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) x := by
  simp only [eC, map_mul, Units.val_mul, intC_translate, smul_smul, mul_comm]

theorem eO_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (x m : Mir k (i + (t + 1))) :
    eO ψ f (x * m) = ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) •
      eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) (castM k (by omega : i + (t + 1) = (i + 1) + t) m)) f) x := by
  simp only [eO, map_mul, Units.val_mul, intO_translate, smul_smul, mul_comm, mul_assoc]

def XR' (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t + 1) :=
  ⟨XS τ σ, cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)⟩

def RC (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t) :=
  ⟨cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ), cInd (MirabolicParabolic k (i + 1) t) (sigC τ σ)⟩

def RO (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k (i + (t + 1)) :=
  ⟨cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), cInd (HPG k i (t + 1)) (sigO τ σ ψ)⟩

set_option maxHeartbeats 1000000 in
theorem xr_eq (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : XR τ σ = XR' τ σ := rfl

set_option maxHeartbeats 1000000 in
theorem rc_eq (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : prodGPn (psiN τ) (gres σ) = RC τ σ := rfl

set_option maxHeartbeats 1000000 in
theorem ro_eq (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) :
    prodPGn (phiN ψ τ) σ = RO ψ τ σ := rfl

theorem rho_eq (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    (phiN ψ (n := (i + 1) + t) (XR' τ σ)).ρ m (Submodule.Quotient.mk f) =
      ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
        (Submodule.Quotient.mk (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) :
          TwJacquet (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t))) := rfl

def jC (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) :
    (RC τ σ).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (psiN τ).V ⊗[ℂ] σ.V) :=
  (indSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)).subtype ∘ₗ (smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ))).subtype ∘ₗ
    (cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)).subtype

def mirabolicRestriction (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hh : i + (t + 1) = (i + 1) + t) :
    (RO ψ τ σ).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) :=
  (LinearMap.funLeft ℂ _ (fun m => (castM k hh).symm m)) ∘ₗ
    (indSpace (HPG k i (t + 1)) (sigO τ σ ψ)).subtype ∘ₗ (smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).subtype ∘ₗ
      (cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).subtype

theorem jC_inj (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : Function.Injective (jC τ σ) :=
  fun _ _ hab => Subtype.ext (Subtype.ext (Subtype.ext hab))

theorem jO0_inj (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hh : i + (t + 1) = (i + 1) + t) :
    Function.Injective (mirabolicRestriction ψ τ σ hh) := fun a b hab => by
  refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
  funext m
  have h2 : (a : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (castM k hh m)) =
      (b : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (castM k hh m)) := congrFun hab (castM k hh m)
  rw [MulEquiv.symm_apply_apply] at h2
  exact h2

def eCl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) : XS τ σ →ₗ[ℂ] (Mir k ((i + 1) + t) → (psiN τ).V ⊗[ℂ] σ.V) where
  toFun f := eC ψ f
  map_add' f g := (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f g 0).1
  map_smul' c f := (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f f c).2.1

def eOl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) :
    XS τ σ →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) where
  toFun f m := eO ψ f ((castM k hh).symm m)
  map_add' f g := by
    funext m
    exact congrFun (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f g 0).2.2.1 _
  map_smul' c f := by
    funext m
    exact congrFun (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f f c).2.2.2 _

theorem eOl_apply (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) (f : XS τ σ) (m : Mir k ((i + 1) + t)) :
    eOl ψ hψ τ σ hτ hσ hh f m = eO ψ f ((castM k hh).symm m) := rfl

theorem aO_eOl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    rightReg ℂ _ _ m (eOl ψ hψ τ σ hτ hσ hh f) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eOl ψ hψ τ σ hτ hσ hh (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) := by
  funext x
  show eO ψ f ((castM k hh).symm (x * m)) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) ((castM k hh).symm x)
  have e1 := map_mul (castM k hh).symm x m
  have e2 := eO_translate ψ f ((castM k hh).symm x) ((castM k hh).symm m)
  have e3 : castM k hh ((castM k hh).symm m) = m := MulEquiv.apply_symm_apply _ _
  have e4 : dpowM (i + (t + 1)) (-1 / 2) ((castM k hh).symm m) = dpowM ((i + 1) + t) (-1 / 2) m := by
    have := dpowM_castM (k := k) hh (-1 / 2) ((castM k hh).symm m)
    rw [e3] at this
    exact this.symm
  have e6 := congrArg (fun g => eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) g) f)
    ((castM k hh).symm x)) e3
  have e7 : ((dpowM (i + (t + 1)) (-1 / 2) ((castM k hh).symm m) : ℂˣ) : ℂ) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) :=
    congrArg _ e4
  exact (congrArg (eO ψ f) e1).trans (e2.trans (congrArg₂ (· • ·) e7 e6))

theorem aC_eCl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    rightReg ℂ _ _ m (eCl ψ hψ τ σ hτ hσ f) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eCl ψ hψ τ σ hτ hσ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) := by
  funext x
  exact eC_translate ψ f x m

set_option maxHeartbeats 1000000 in
theorem phiPG_core (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) :
    MExt (mcast (by omega : i + (t + 1) = (i + 1) + t) (RO ψ τ σ)) (phiN ψ (n := (i + 1) + t) (XR' τ σ)) (RC τ σ) := by
  have hh : i + (t + 1) = (i + 1) + t := by omega
  obtain ⟨hUn, hθ, hCc, hHC, hCU, hdir⟩ := GlobalTheory.T.mirabolic_cell_structure_data k ψ hψ i t
  obtain ⟨e, he⟩ := mcast_spec hh (RO ψ τ σ)
  let jOl : (mcast hh (RO ψ τ σ)).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) :=
    mirabolicRestriction ψ τ σ hh ∘ₗ e.symm.toLinearMap
  have hjOl : Function.Injective jOl := (jO0_inj ψ τ σ hh).comp e.symm.injective
  have hes : ∀ (m : Mir k ((i + 1) + t)) v, e.symm ((mcast hh (RO ψ τ σ)).ρ m v) =
      (RO ψ τ σ).ρ ((castM k hh).symm m) (e.symm v) := by
    intro m v
    rw [LinearEquiv.symm_apply_eq, he, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hjOe : ∀ m v, jOl ((mcast hh (RO ψ τ σ)).ρ m v) = rightReg ℂ _ _ m (jOl v) := by
    intro m v
    show mirabolicRestriction ψ τ σ hh (e.symm _) = _
    rw [hes]
    funext x
    show (e.symm v : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm x * (castM k hh).symm m) =
      (e.symm v : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (x * m))
    rw [map_mul]
  exact GlobalTheory.T.twisted_jacquet_closed_open_sequence (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) hUn (mirChar k ψ ((i + 1) + t)) hθ hdir
    (sEmb k ((i + 1) + t)) (dpowM ((i + 1) + t) (-1 / 2)) (phiN ψ (n := (i + 1) + t) (XR' τ σ)).ρ (fun m f => rho_eq ψ τ σ m f)
    (Cl k i t) hCc hHC hCU
    (RC τ σ).ρ (mcast hh (RO ψ τ σ)).ρ
    (rightReg ℂ _ _) (rightReg ℂ _ _) (jC τ σ) jOl (jC_inj τ σ) hjOl (fun m v => rfl) hjOe
    (eCl ψ hψ τ σ hτ hσ) (eOl ψ hψ τ σ hτ hσ hh)
    (fun u f => GlobalTheory.T.closed_evaluation_equivariant k i t ψ hψ τ σ hτ hσ u f)
    (fun u f => by
      funext m
      exact congrFun (GlobalTheory.T.open_evaluation_equivariant k i t ψ hψ τ σ hτ hσ u f) _)
    (fun m f => aC_eCl ψ hψ τ σ hτ hσ m f)
    (fun m f => aO_eOl ψ hψ τ σ hτ hσ hh m f)
    (fun f => by
      obtain ⟨y, hy⟩ := GlobalTheory.T.closed_evaluation_induced k i t ψ hψ τ σ hτ hσ f
      exact ⟨y, hy⟩)
    (fun f hf => by
      obtain ⟨y, hy⟩ := GlobalTheory.T.open_evaluation_induced k i t ψ hψ τ σ hτ hσ f hf
      refine ⟨e y, ?_⟩
      funext m
      have e1 : e.symm (e y) = y := e.symm_apply_apply y
      exact (congrArg (fun z => mirabolicRestriction ψ τ σ hh z m) e1).trans (congrFun hy _))
    (fun v => GlobalTheory.T.closed_evaluation_surjective k i t ψ hψ τ σ hτ hσ v)
    (fun v => by
      obtain ⟨f, hf, hy⟩ := GlobalTheory.T.open_evaluation_surjective k i t ψ hψ τ σ hτ hσ (e.symm v)
      refine ⟨f, hf, ?_⟩
      funext m
      exact congrFun hy _)
    (fun f hf => GlobalTheory.T.closed_evaluation_vanishing_on_open k i t ψ τ σ hτ hσ f hf)
    (fun f h0 p hp => GlobalTheory.T.average_vanishes_closed_cell k i t ψ hψ τ σ hτ hσ f h0 p hp)
    (fun f h0 p hp => GlobalTheory.T.average_vanishes_open_cell k i t ψ hψ τ σ hτ hσ f (by
      funext m
      have := congrFun h0 (castM k hh m)
      rw [eOl_apply, MulEquiv.symm_apply_apply] at this
      exact this) p hp)

theorem phiPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG k := by
  intro k _ _ _ _ ψ hψ _ i t τ σ hτ hσ
  have h0 : (i + 1) + t = i + t + 1 := by omega
  have H := mExt_mcast h0 (phiPG_core ψ hψ i t τ σ hτ hσ)
  rw [mcast_mcast _ _ (by omega : i + (t + 1) = i + t + 1), ← ro_eq, ← xr_eq, ← rc_eq] at H
  rw [phiN_mcast ψ h0 (by omega)]
  exact H

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchInt
section
namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem paramChartInt : GroundTheory.Heights₂.Heights.ParamChartInt.Statement :=
  GroundTheory.Heights₂.Heights.ParamChartInt.proof
    (GroundTheory.Heights₂.Heights.ChartIntCountAdd.proof GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.ChartMassCompact)
    GroundTheory.Heights₂.Heights.ParamPieceInt.proof GroundTheory.Heights₂.Heights.ParamCritNull.proof
    GroundTheory.Heights₂.Heights.ParamOffRegularZero.proof GroundTheory.Heights₂.Heights.RegularInjectivePieces.proof
    GroundTheory.Heights₂.Heights.ParamDensIntegrable.proof

theorem sliceBranchInt : GroundTheory.Heights₂.Heights.SliceBranchInt.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranchInt.proof GlobalTheory.T.branch_proper_at_point_holds paramChartInt

end GlobalTheory.CompanionTheory.Ar.SliceBranch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlotEmbeddingsExistStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.position_embeddings_exist : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) {S : Set (Pl E)} (hS : IsSection S),
    ∃ e : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b,
      (∀ i, Continuous (e i)) ∧ (∀ (i : Slot S) m, i.cp a b (e i m) = m) ∧ (∀ (i j : Slot S) m, i ≠ j → j.cp a b (e i m) = 1) ∧
      (∀ (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inl w) m) = (embW a w.1 m.1, embW b w.1 m.2)) ∧
      ∀ (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1),
        finH (e (.inr w) m) = (embT a w.1 m.1, embT b w.1 m.2) := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.exists_factorEmb | exact GlobalTheory.CompanionTheory.FinActS.exists_factorEmb | (intros; apply GlobalTheory.CompanionTheory.FinActS.exists_factorEmb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlotLevelSubgroupsExistStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.position_level_subgroups_exist : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂),
    ∃ L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl),
      (∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl))) ∧ (∀ᶠ i in cofinite, L i = K2 a b i.pl) ∧
      (∀ i, ∀ k ∈ L i, ∀ x, sf φ₁ φ₂ i (x * k) = sf φ₁ φ₂ i x) ∧
      (∀ i : Slot S, HasCompactSupport (sf φ₁ φ₂ i)) ∧
      ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1 := by
  first | exact @GlobalTheory.CompanionTheory.PositionTest.exists_factor_level₂ | exact GlobalTheory.CompanionTheory.PositionTest.exists_factor_level₂ | (intros; apply GlobalTheory.CompanionTheory.PositionTest.exists_factor_level₂ <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableDenominatorPowerOfLtStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_denominator_power_of_lt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (s : ℝ), (n : ℝ) < s →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.summable_delta_rpow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleSpaceCovolumeFormula
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.TupCovolume

open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SiegelND.DxN PositivityTheory.SiegelWeilFormula.KWhit.MeasP
open scoped TensorProduct

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def ratCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (Y : Fin n → Fin M → E) : Fin n × (Fin M × Fin d) → F :=
  fun p => b.repr (Y p.1 p.2.1) p.2.2

def ofCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (c : Fin n × (Fin M × Fin d) → F) : Fin n → Fin M → E :=
  fun a i => ∑ l, c (a, (i, l)) • b l

theorem ratCoord_ofCoord {d M n : ℕ} (b : Module.Basis (Fin d) F E) (c : Fin n × (Fin M × Fin d) → F) :
    ratCoord b (ofCoord b c) = c := by
  funext p
  obtain ⟨a, i, l⟩ := p
  simp [ratCoord, ofCoord, Finsupp.single_apply]

theorem ratCoord_injective {d M n : ℕ} (b : Module.Basis (Fin d) F E) :
    Function.Injective (ratCoord (M := M) (n := n) b) := by
  intro Y Y' h
  funext a i
  refine b.repr.injective (Finsupp.ext fun l => ?_)
  exact congrFun h (a, (i, l))

theorem cvN_incl_add (R : Type) [CommRing R] [Algebra F R] {d M n : ℕ} (b : Module.Basis (Fin d) F E)
    (Y : Fin n → Fin M → E) (X : Fin n → Fin M → R ⊗[F] E) (p : Fin n × (Fin M × Fin d)) :
    cvN R b ((fun a i => inclR R (Y a i)) + X) p = algebraMap F R (ratCoord b Y p) + cvN R b X p := by
  simp [cvN, GlobalTheory.CompanionTheory.SW.BB.cv, ratCoord, inclR, Algebra.TensorProduct.basis_repr_tmul,
    Algebra.algebraMap_eq_smul_one]

end Coord

section Main

open GroundTheory.Global

attribute [local instance 100000] GroundTheory.Global.measurableSpace_adeleRing

theorem tupCovol : TupCovol := by
  intro F E _ _ _ _ _ σ hCM M J hJ ψ hψ n μ hμ
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  let b := Module.finBasis F E
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    obtain ⟨x, hx⟩ := hψ.2.2.2
    apply hx
    rw [hξ x]
    simp
  obtain ⟨e, he, hB⟩ := exists_coordHomeoN σ hCM n M b
  have hdxc := dx_coordN σ hCM J hJ b ψ ξ hξ0 hξ μ hμ e he hB
  have := hB
  have : BorelSpace (AF F) := GroundTheory.Global.borelSpace_adeleRing F
  have : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have hD : MeasurableSet (Set.univ.pi fun _ : Fin n × (Fin M × Fin (Module.finrank F E)) => fundamentalSet F) :=
    MeasurableSet.univ_pi fun _ => measurableSet_fundamentalSet F
  have hem : Measurable e := e.continuous.measurable
  have hmem : ∀ (Y : Fin n → Fin M → E) X,
      e ((fun a i => inclR (AF F) (Y a i)) + X) ∈
          (Set.univ.pi fun _ : Fin n × (Fin M × Fin (Module.finrank F E)) => fundamentalSet F) ↔
        ∀ p, algebraMap F (AF F) (ratCoord b Y p) + e X p ∈ fundamentalSet F := by
    intro Y X
    simp only [Set.mem_univ_pi, he, cvN_incl_add]
  refine ⟨e ⁻¹' (Set.univ.pi fun _ => fundamentalSet F), IsAddFundamentalDomain.mk' (hem hD).nullMeasurableSet fun X => ?_, ?_⟩
  · choose k hk huniq using fun p => existsUnique_sub_mem_fundamentalSet F (e X p)
    refine ⟨⟨_, ofCoord b (-k), rfl⟩, ?_, ?_⟩
    · refine (hmem _ X).2 fun p => ?_
      rw [ratCoord_ofCoord]
      have := hk p
      rwa [Pi.neg_apply, map_neg, neg_add_eq_sub]
    · rintro ⟨_, Y, rfl⟩ h
      have h' := (hmem Y X).1 h
      have hY : ratCoord b Y = -k := by
        funext p
        have e1 := huniq p (-(ratCoord b Y p)) (by
          change e X p - algebraMap F (AF F) (-(ratCoord b Y p)) ∈ fundamentalSet F
          rw [map_neg, sub_neg_eq_add, add_comm]; exact h' p)
        rw [Pi.neg_apply, ← e1, neg_neg]
      have : Y = ofCoord b (-k) := ratCoord_injective b (by rw [hY, ratCoord_ofCoord])
      subst this
      rfl
  · rw [← Measure.map_apply hem hD, hdxc, GroundTheory.Automorphic.GJMatrix.adeleMeasurePi, Measure.pi_pi]
    simp [adeleMeasure_fundamentalSet]

end Main

end GlobalTheory.CompanionTheory.SiegelND.TupCovolume

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Rodier

theorem whitHeredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    WhitHeredity k := by
  intro k _ _ _ _ ψ hψ hψ1 h N d hd X _ _ π hπ
  obtain ⟨J, hJs, hJ⟩ := GlobalTheory.T.open_cell_jacquet_map_surjective_whittaker k ψ hψ h N d hd (piTensor π) (isSmooth_piTensor hπ)
  obtain ⟨E⟩ := GlobalTheory.T.twisted_jacquet_tensor_product_equiv π (fun a => unipB k (Fin (d a))) (fun a => whitChar ψ (d a))
  set T := twKer (multiProd (stdBlocks d hd) π) (unipB k (Fin N)) (whitChar ψ N) with hT
  set S := twKer (piTensor π) (unipM k d) (whitM d ψ) with hS
  let a : openFns d hd (piTensor π) →ₗ[ℂ] (IndSp (stdBlocks d hd) (piTensor π)) ⧸ T :=
    T.mkQ ∘ₗ (openFns d hd (piTensor π)).subtype
  let b : openFns d hd (piTensor π) →ₗ[ℂ] (⨂[ℂ] a, X a) ⧸ S := S.mkQ ∘ₗ J
  have ha : Function.Surjective a := by
    intro y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f₀, h0, h1⟩ := GlobalTheory.T.induced_function_open_cell_modulo_whittaker k ψ hψ hψ1 h N d hd (piTensor π) f
    refine ⟨⟨f₀, h0⟩, ?_⟩
    exact ((Submodule.Quotient.eq T).2 (by simpa [neg_sub] using T.neg_mem h1))
  have hb : Function.Surjective b := by
    intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f, rfl⟩ := hJs w
    exact ⟨f, rfl⟩
  have hker : LinearMap.ker a = LinearMap.ker b := by
    ext f
    simp only [a, b, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.subtype_apply]
    exact (hJ f).symm
  exact ⟨(a.quotKerEquivOfSurjective ha).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans ((b.quotKerEquivOfSurjective hb).trans E))⟩

end GlobalTheory.CompanionTheory.Rodier
end

