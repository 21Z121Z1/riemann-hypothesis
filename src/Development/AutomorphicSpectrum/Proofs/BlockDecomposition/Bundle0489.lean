import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0450
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0417
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeTwistedIso
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd.DerivTw

section gen

variable {G M V W : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem equiv_of_eq {ρ σ : Representation ℂ G V} (h : ρ = σ) : Nonempty (ρ.Equiv σ) :=
  h ▸ ⟨Representation.Equiv.refl _⟩

theorem twAct_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (e : ρ.Equiv σ) :
    Nonempty ((twAct ρ N θ s hs).Equiv (twAct σ N θ s hs)) := by
  let f := twMap ρ σ N θ e.toLinearEquiv.toLinearMap (fun g v => eint e g v)
  let f' := twMap σ ρ N θ e.symm.toLinearEquiv.toLinearMap (fun g v => eint e.symm g v)
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofLinear f f' ?_ ?_) fun x => ?_⟩
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e (e.symm v)) = Submodule.Quotient.mk v
    simp
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e.symm (e v)) = Submodule.Quotient.mk v
    simp
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.Quotient.mk (e (ρ (s x) v)) = Submodule.Quotient.mk (σ (s x) (e v))
    rw [eint e]

theorem twKer_twist (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (χ : G →* ℂˣ) (hN : ∀ n : N, χ n = 1) :
    twKer (twist ρ χ) N θ = twKer ρ N θ := by
  unfold twKer
  congr 1
  ext w
  simp only [twist_apply, hN, Units.val_one, one_smul, Set.mem_setOf_eq]

theorem twAct_twist (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n) (χ : G →* ℂˣ) (χ' : M →* ℂˣ)
    (hN : ∀ n : N, χ n = 1) (hχ : ∀ m, χ (s m) = χ' m) :
    Nonempty ((twAct (twist ρ χ) N θ s hs).Equiv (twist (twAct ρ N θ s hs) χ')) := by
  refine ⟨Representation.Equiv.mk (Submodule.quotEquivOfEq (twKer (twist ρ χ) N θ) (twKer ρ N θ) (twKer_twist ρ N θ χ hN)) fun x => ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show Submodule.Quotient.mk (p := twKer ρ N θ) ((χ (s x) : ℂ) • ρ (s x) v) =
    (χ' x : ℂ) • Submodule.Quotient.mk (p := twKer ρ N θ) (ρ (s x) v)
  rw [hχ]
  rfl

end gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_of_last {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (h : A (Fin.last n) = eLast k n) :
    A.det = (blockMat k n A).det := by
  have h0 : ∀ j : Fin n, A (Fin.last n) (Fin.castSucc j) = 0 := fun j => by
    rw [h]; simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
  have h1 : A (Fin.last n) (Fin.last n) = 1 := by
    rw [h]; simp [eLast]
  rw [Matrix.det_succ_row A (Fin.last n), Fin.sum_univ_castSucc]
  simp only [h0, h1, Fin.succAbove_last]
  simp [blockMat, ← two_mul, Matrix.submatrix]
  rfl

theorem det_uin {n : ℕ} (u : MirUin k n) :
    Matrix.GeneralLinearGroup.det ((u : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
  obtain ⟨v, hv⟩ := (u.2 : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  have hb : blockMat k n (((u : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 := by
    rw [show ((u : Mir k n) : GL (Fin (n + 1)) k) = unip k n v from hv.symm]
    ext i j
    show (1 + colMat k n v.toAdd) (Fin.castSucc i) (Fin.castSucc j) = _
    simp [colMat, one_apply, Fin.castSucc_ne_last]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, det_of_last _ ((mem_Mir_iff k _).1 (u : Mir k n).2), hb]
  simp

theorem det_levi {n : ℕ} (m : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det ((levi k n m : Mir k n) : GL (Fin (n + 1)) k) = Matrix.GeneralLinearGroup.det m := by
  have hb : blockMat k n (((levi k n m : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      (m : Matrix (Fin n) (Fin n) k) := by
    ext i j
    show glEmbMat k n (m : Matrix (Fin n) (Fin n) k) (Fin.castSucc i) (Fin.castSucc j) = _
    simp [glEmbMat]
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    det_of_last _ ((mem_Mir_iff k _).1 (levi k n m : Mir k n).2), hb]

theorem dpow_add (n : ℕ) (s t : ℝ) : dpow (k := k) n (s + t) = dpow n t * dpow n s := by
  ext g
  simp only [dpow, detChar_apply, MonoidHom.mul_apply, Complex.ofReal_add, absPow_add, Units.val_mul]
  exact mul_comm _ _

theorem dpow_zero (n : ℕ) : dpow (k := k) n 0 = 1 := by
  ext g
  simp [dpow]

theorem dpowM_add (n : ℕ) (s t : ℝ) : dpowM (k := k) n (s + t) = dpowM n t * dpowM n s := by
  ext g
  simp [dpowM, dpow_add]

theorem dpowM_zero (n : ℕ) : dpowM (k := k) n 0 = 1 := by
  ext g
  simp [dpowM, dpow_zero]

theorem dpowM_uin {n : ℕ} (s : ℝ) (u : MirUin k n) : dpowM n s (u : Mir k n) = 1 := by
  show detChar (Fin (n + 1)) (absPow k (s : ℂ)) ((u : Mir k n) : GL (Fin (n + 1)) k) = 1
  rw [detChar_apply, det_uin, map_one]

theorem dpowM_levi {n : ℕ} (s : ℝ) (m : GL (Fin n) k) : dpowM n s (levi k n m) = dpow n s m := by
  show detChar (Fin (n + 1)) (absPow k (s : ℂ)) ((levi k n m : Mir k n) : GL (Fin (n + 1)) k) = _
  rw [detChar_apply, det_levi]
  rfl

theorem tw_tw {n : ℕ} (π : GRep k n) (s t : ℝ) : GIso ((π.tw s).tw t) (π.tw (s + t)) := by
  show Nonempty ((twist (twist π.ρ (dpow n s)) (dpow n t)).Equiv (twist π.ρ (dpow n (s + t))))
  exact equiv_of_eq (by rw [twist_twist, dpow_add])

theorem tw_zero {n : ℕ} (π : GRep k n) : GIso (π.tw 0) π := by
  show Nonempty ((twist π.ρ (dpow n 0)).Equiv π.ρ)
  exact equiv_of_eq (by rw [dpow_zero, twist_one])

theorem mtw_mtw {n : ℕ} (τ : MRep k n) (s t : ℝ) : MIso (mtw (mtw τ s) t) (mtw τ (s + t)) := by
  show Nonempty ((twist (twist τ.ρ (dpowM n s)) (dpowM n t)).Equiv (twist τ.ρ (dpowM n (s + t))))
  exact equiv_of_eq (by rw [twist_twist, dpowM_add])

theorem mtw_zero {n : ℕ} (τ : MRep k n) : MIso (mtw τ 0) τ := by
  show Nonempty ((twist τ.ρ (dpowM n 0)).Equiv τ.ρ)
  exact equiv_of_eq (by rw [dpowM_zero, twist_one])

theorem miso_mtw {n : ℕ} {A B : MRep k n} (s : ℝ) (h : MIso A B) : MIso (mtw A s) (mtw B s) := by
  obtain ⟨e⟩ := h
  exact ⟨Representation.Equiv.mk e.toLinearEquiv fun x => by
    ext v
    show e (((dpowM n s x : ℂˣ) : ℂ) • A.ρ x v) = ((dpowM n s x : ℂˣ) : ℂ) • B.ρ x (e v)
    rw [map_smul]
    exact congrArg _ (eint e x v)⟩

def psiG {n : ℕ} (τ : MRep k n) : GRep k n := ⟨_, psiMinus k τ.ρ⟩

theorem miso_phiM (ψ : AddChar k Circle) {n : ℕ} {A B : MRep k (n + 1)} (h : MIso A B) :
    MIso (MRep.phiM k ψ A) (MRep.phiM k ψ B) := by
  obtain ⟨e⟩ := h
  exact twAct_equiv _ _ _ (levi_stab ψ n) e

theorem giso_psiG {n : ℕ} {A B : MRep k n} (h : MIso A B) : GIso (psiG A) (psiG B) := by
  obtain ⟨e⟩ := h
  exact twAct_equiv _ _ _ (levi_normalises n) e

theorem phiM_mtw (ψ : AddChar k Circle) {n : ℕ} (τ : MRep k (n + 1)) (s : ℝ) :
    MIso (MRep.phiM k ψ (mtw τ s)) (mtw (MRep.phiM k ψ τ) s) :=
  twAct_twist τ.ρ _ _ _ (levi_stab ψ n) (dpowM (n + 1) s) (dpowM n s) (dpowM_uin s) fun m => by
    show dpowM (n + 1) s (levi k (n + 1) (m : GL (Fin (n + 1)) k)) = _
    rw [dpowM_levi]
    rfl

theorem psiG_mtw {n : ℕ} (τ : MRep k n) (s : ℝ) : GIso (psiG (mtw τ s)) ((psiG τ).tw s) :=
  twAct_twist τ.ρ _ _ _ (levi_normalises n) (dpowM n s) (dpow n s) (dpowM_uin s) (dpowM_levi s)

theorem miso_iterPhi (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) {A B : MRep k (n + j)}, MIso A B →
    MIso (iterPhi k ψ j A) (iterPhi k ψ j B)
  | 0, _, _, h => h
  | j + 1, _, _, h => miso_iterPhi ψ j (miso_phiM ψ h)

theorem iterPhi_mtw (ψ : AddChar k Circle) {n : ℕ} (s : ℝ) : ∀ (j : ℕ) (X : MRep k (n + j)),
    MIso (iterPhi k ψ j (mtw X s)) (mtw (iterPhi k ψ j X) s)
  | 0, _ => miso_refl _
  | j + 1, X => miso_trans (miso_iterPhi ψ j (phiM_mtw ψ X s)) (iterPhi_mtw ψ s j (MRep.phiM k ψ X))

theorem iterN_iso (ψ : AddChar k Circle) {n : ℕ} : ∀ (j : ℕ) (τ : MRep k (n + j)),
    MIso (iterN ψ j τ) (mtw (iterPhi k ψ j τ) (-(j : ℝ) / 2))
  | 0, τ => by
    rw [show -((0 : ℕ) : ℝ) / 2 = 0 by simp]
    exact miso_symm (mtw_zero τ)
  | j + 1, τ => by
    have h1 := iterN_iso ψ j (phiN ψ τ)
    have h2 := iterPhi_mtw ψ (-1 / 2) j (MRep.phiM k ψ τ)
    have h3 := mtw_mtw (iterPhi k ψ j (MRep.phiM k ψ τ)) (-1 / 2) (-(j : ℝ) / 2)
    rw [show (-1 / 2 : ℝ) + -(j : ℝ) / 2 = -((j + 1 : ℕ) : ℝ) / 2 by push_cast; ring] at h3
    exact miso_trans h1 (miso_trans (miso_mtw _ h2) h3)

theorem derivB_iso_tw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (j n : ℕ) (π : GRep k (n + j)), GIso (derivB ψ j π) ((dG ψ j π).tw ((j : ℝ) / 2)) := by
  intro k _ _ _ _ ψ j n π
  cases j with
  | zero =>
    rw [show ((0 : ℕ) : ℝ) / 2 = 0 by simp]
    exact giso_symm (tw_zero π)
  | succ j =>
    have h1 : MIso (iterN ψ j (gres π)) (mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2)) := iterN_iso ψ j (gres π)
    have h2 : GIso (psiN (iterN ψ j (gres π))) ((psiG (mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2))).tw (-1 / 2)) :=
      giso_tw _ (giso_psiG h1)
    have h3 := giso_tw (-1 / 2) (psiG_mtw (iterPhi k ψ j (resM k π.ρ)) (-(j : ℝ) / 2))
    have h4 := tw_tw (psiG (iterPhi k ψ j (resM k π.ρ))) (-(j : ℝ) / 2) (-1 / 2)
    have h5 : GIso ((dG ψ (j + 1) π).tw (((j + 1 : ℕ) : ℝ) / 2))
        (((psiG (iterPhi k ψ j (resM k π.ρ))).tw (-(j : ℝ) / 2 + -1 / 2)).tw (((j + 1 : ℕ) : ℝ) / 2)) :=
      giso_tw _ (giso_trans h2 (giso_trans h3 h4))
    have h6 := tw_tw (psiG (iterPhi k ψ j (resM k π.ρ))) (-(j : ℝ) / 2 + -1 / 2) (((j + 1 : ℕ) : ℝ) / 2)
    rw [show -(j : ℝ) / 2 + -1 / 2 + ((j + 1 : ℕ) : ℝ) / 2 = 0 by push_cast; ring] at h6
    exact giso_symm (giso_trans h5 (giso_trans h6 (tw_zero _)))

end GlobalTheory.CompanionTheory.LeibOrd.DerivTw

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeckeFunctionalStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_hecke_functional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → IsHecke F E χ → ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → ∀ s : ℂ, t < s.re → ∀ γ ∈ rat2 σ Y, ∀ x, Ê s (γ * x) = Ê s x := by
  first | exact @GlobalTheory.CompanionTheory.EisRat.eis_left_rat | exact GlobalTheory.CompanionTheory.EisRat.eis_left_rat | (intros; apply GlobalTheory.CompanionTheory.EisRat.eis_left_rat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfEigOfMemTwKer
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.LocO

open MeasureTheory GlobalTheory.CompanionTheory.TwistedAverage GlobalTheory.CompanionTheory.Rodier

theorem eq_zero_of_eig_of_mem_twKer {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) {x : V}
    (hx : x ∈ twKer ρ L θ) (he : ∀ l : L, ρ (l : G) x = (θ l : ℂ) • x) : x = 0 := by
  classical
  obtain ⟨M, hM, hs⟩ := exists_sum_eq_zero hρ hL θ hθ hx
  haveI : M.FiniteIndex := hM
  haveI : M.normalCore.FiniteIndex := inferInstance
  haveI : M.normalCore.Normal := Subgroup.normalCore_normal _
  haveI : Finite (L ⧸ M.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (L ⧸ M.normalCore) := Fintype.ofFinite _
  have h0 := hs M.normalCore (Subgroup.normalCore_le M)
  have h1 : ∀ t : L, twOrbit ρ L θ x t = x := fun t => by
    rw [twOrbit, he t, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  simp only [h1, Finset.sum_const, Finset.card_univ] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · exact h0

theorem isSmooth_cInd {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] (H : Subgroup G) (σ : Representation ℂ H Z) : IsSmooth (cInd H σ) := by
  intro f
  have h : {g : G | cInd H σ g f = f} = {g : G | ind H σ g f.1.1 = f.1.1} := by
    ext g
    exact ⟨fun h => congrArg (fun x : cIndSpace H σ => x.1.1) h, fun h => Subtype.ext (Subtype.ext h)⟩
  rw [h]
  exact f.1.2

def evL {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] (H : Subgroup G) (σ : Representation ℂ H Z) (x : G) : cIndSpace H σ →ₗ[ℂ] Z :=
  (LinearMap.proj x) ∘ₗ (indSpace H σ).subtype ∘ₗ (smoothPart (ind H σ)).subtype ∘ₗ (cIndSpace H σ).subtype

theorem avgVanish_of_fibre {G Z Γ A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ)
    (ρ₁ : Representation ℂ Γ Z) (hρ₁ : IsSmooth ρ₁)
    (C : Subgroup Γ) (hC : IsCompact (C : Set Γ)) (χ : C →* ℂˣ) (hχ : IsOpen (χ.ker : Set C))
    (c : C → H) (hc : ∀ (b : C) (w : Z), σ (c b) w = ρ₁ (b : Γ) w)
    (e : A → G) (he : ∀ a a', e (a + a') = e a * e a')
    (hce : ∀ (b : C) (a : A), ((c b : H) : G) * e a = e a * ((c b : H) : G))
    (y : G) (D : Set A) (hD0 : (0 : A) ∈ D) (hDs : ∀ a a', a ∈ D → a' ∈ D → a - a' ∈ D)
    (hDc : IsCompact D) (hDo : IsOpen D)
    (L : Subgroup G) (hLU : L ≤ U) (hLc : IsCompact (L : Set G))
    (hθ : IsOpen ((θ.comp (Subgroup.inclusion hLU)).ker : Set L))
    (hL1 : ∀ l : L, ∃ (b : C) (a : A), a ∈ D ∧ y * (l : G) * y⁻¹ = ((c b : H) : G) * e a ∧
      θ (Subgroup.inclusion hLU l) = χ b)
    (hL2 : ∀ b : C, ∃ l : L, y * (l : G) * y⁻¹ = ((c b : H) : G) ∧ θ (Subgroup.inclusion hLU l) = χ b)
    (hL3 : ∀ a ∈ D, ∃ l : L, y * (l : G) * y⁻¹ = e a ∧ θ (Subgroup.inclusion hLU l) = 1)
    (hU : ∀ u ∈ U, ∃ h ∈ H, ∃ a : A, y * u * y⁻¹ = h * e a)
    (hfib : ∀ f' : cIndSpace H σ, IsLocallyConstant (fun a => evL H σ (e a * y) f') ∧
      HasCompactSupport (fun a => evL H σ (e a * y) f'))
    (f : cIndSpace H σ) (hsupp : ∀ a, evL H σ (e a * y) f ≠ 0 → a ∈ D)
    (hz : smInt μ (fun a => evL H σ (e a * y) f) ∈ twKer ρ₁ C χ) :
    AvgVanish H σ U θ f y := by
  classical
  have hev : ∀ (x l : G) (f' : cIndSpace H σ), evL H σ x (cInd H σ l f') = evL H σ (x * l) f' := fun _ _ _ => rfl
  have hleft : ∀ (h : H) (x : G) (f' : cIndSpace H σ), evL H σ ((h : G) * x) f' = σ h (evL H σ x f') :=
    fun h x f' => f'.1.1.2 h x
  have he0 : e 0 = 1 := by
    have := he 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  set θL : L →* ℂˣ := θ.comp (Subgroup.inclusion hLU) with hθL
  obtain ⟨ι, _, r, c₀, h1, h2⟩ := GlobalTheory.CompanionTheory.TwAvgInd.exists_finite_average (cInd H σ) (isSmooth_cInd H σ) hLc θL hθ f
  obtain ⟨g, hg⟩ : ∃ g : cIndSpace H σ, g = c₀ • ∑ i, twOrbit (cInd H σ) L θL f (r i) := ⟨_, rfl⟩
  rw [← hg] at h1
  simp only [← hg] at h2

  let T : cIndSpace H σ →ₗ[ℂ] Z :=
    { toFun := fun f' => smInt μ (fun a => evL H σ (e a * y) f')
      map_add' := fun f₁ f₂ => by
        have := SmIntEl.smInt_add μ (hfib f₁).1 (hfib f₁).2 (hfib f₂).1 (hfib f₂).2
        rw [← this]
        congr 1
      map_smul' := fun s f' => by
        have := SmIntEl.smInt_linear μ (s • (LinearMap.id : Z →ₗ[ℂ] Z)) (hfib f').1 (hfib f').2
        simp only [LinearMap.smul_apply, LinearMap.id_apply, RingHom.id_apply] at this ⊢
        rw [← this]
        congr 1 }
  have hTdef : ∀ f', T f' = smInt μ (fun a => evL H σ (e a * y) f') := fun _ => rfl
  have hpoint : ∀ (l : G) (b : C) (a₁ a : A), y * l * y⁻¹ = ((c b : H) : G) * e a₁ →
      e a * y * l = ((c b : H) : G) * (e (a₁ + a) * y) := by
    intro l b a₁ a h
    have h' : y * l = ((c b : H) : G) * e a₁ * y := by rw [← h]; group
    have h2 : e (a₁ + a) = e a * e a₁ := by rw [add_comm, he]
    rw [mul_assoc, h', h2]
    simp only [← mul_assoc]
    rw [← hce b a]
  have hTl : ∀ (l : G) (b : C) (a₁ : A), y * l * y⁻¹ = ((c b : H) : G) * e a₁ → ∀ f',
      T (cInd H σ l f') = ρ₁ (b : Γ) (T f') := by
    intro l b a₁ hl f'
    set φ : A → Z := fun a => evL H σ (e a * y) f' with hφ
    have hfun : (fun a => evL H σ (e a * y) (cInd H σ l f')) = (ρ₁ (b : Γ)) ∘ (φ ∘ (fun a => a₁ + a)) := by
      funext a
      rw [hev, hpoint l b a₁ a hl, hleft, hc]
      rfl
    have hl₂ : IsLocallyConstant (φ ∘ fun a => a₁ + a) := (hfib f').1.comp_continuous (by fun_prop)
    have hc₂ : HasCompactSupport (φ ∘ fun a => a₁ + a) := (hfib f').2.comp_homeomorph (Homeomorph.addLeft a₁)
    rw [hTdef, hfun, SmIntEl.smInt_linear μ _ hl₂ hc₂,
      SmIntEl.smInt_comp_measurePreserving μ (measurePreserving_add_left μ a₁) (hfib f').1]
    rfl
  have hker : ∀ x ∈ twKer (cInd H σ) L θL, T x ∈ twKer ρ₁ C χ := by
    intro x hx
    have hle : twKer (cInd H σ) L θL ≤ (twKer ρ₁ C χ).comap T := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨l, v, rfl⟩
      obtain ⟨b, a, -, h3, h4⟩ := hL1 l
      show T (_ - _) ∈ twKer ρ₁ C χ
      rw [map_sub, map_smul, hTl _ b a h3]
      have : θL l = χ b := h4
      rw [this]
      exact Submodule.subset_span ⟨b, T v, rfl⟩
    exact hle hx
  have hTg : T g ∈ twKer ρ₁ C χ := by
    have : T g = T f - T (f - g) := by rw [map_sub]; abel
    rw [this]
    exact Submodule.sub_mem _ hz (hker _ h1)
  have heig : ∀ b : C, ρ₁ (b : Γ) (T g) = (χ b : ℂ) • T g := by
    intro b
    obtain ⟨l, h3, h4⟩ := hL2 b
    have h5 : y * (l : G) * y⁻¹ = ((c b : H) : G) * e 0 := by rw [he0, mul_one, h3]
    rw [← hTl _ b 0 h5 g, h2 l, map_smul]
    have : θL l = χ b := h4
    rw [this]
  have hTg0 : T g = 0 := eq_zero_of_eig_of_mem_twKer hρ₁ hC χ hχ hTg heig

  have hsg : ∀ a, evL H σ (e a * y) g ≠ 0 → a ∈ D := by
    intro a ha
    by_contra hn
    apply ha
    have hz0 : ∀ i, evL H σ (e a * y) (twOrbit (cInd H σ) L θL f (r i)) = 0 := by
      intro i
      obtain ⟨b, a₁, ha₁, h3, -⟩ := hL1 (r i)
      rw [twOrbit, map_smul, hev, hpoint _ b a₁ a h3, hleft]
      have : evL H σ (e (a₁ + a) * y) f = 0 := by
        by_contra h
        have h6 := hsupp _ h
        apply hn
        have := hDs _ _ h6 ha₁
        rwa [add_sub_cancel_left] at this
      rw [this, map_zero, smul_zero]
    rw [hg, map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz0 i, smul_zero]

  have hper : ∀ a ∈ D, evL H σ (e a * y) g = evL H σ (e 0 * y) g := by
    intro a ha
    obtain ⟨l, h3, h4⟩ := hL3 a ha
    have h5 := congrArg (evL H σ (e 0 * y)) (h2 l)
    rw [hev, map_smul] at h5
    have h6 : e 0 * y * (l : G) = e a * y := by
      rw [he0, one_mul]
      have : y * (l : G) = e a * y := by rw [← h3]; group
      exact this
    rw [h6] at h5
    have h7 : θL l = 1 := h4
    rw [h5, h7]
    simp
  have hφ : (fun a => evL H σ (e a * y) g) = D.indicator fun _ => evL H σ (e 0 * y) g := by
    funext a
    by_cases ha : a ∈ D
    · rw [Set.indicator_of_mem ha, hper a ha]
    · rw [Set.indicator_of_notMem ha]
      by_contra h
      exact ha (hsg a h)
  have hv0 : evL H σ (e 0 * y) g = 0 := by
    have h3 : T g = (((μ D).toReal : ℝ) : ℂ) • evL H σ (e 0 * y) g := by
      rw [hTdef, hφ, SmIntEl.smInt_indicator]
    rw [hTg0] at h3
    have hpos : (μ D).toReal ≠ 0 :=
      (ENNReal.toReal_pos (hDo.measure_pos μ ⟨0, hD0⟩).ne' hDc.measure_lt_top.ne).ne'
    rcases smul_eq_zero.1 h3.symm with h4 | h4
    · exact absurd (Complex.ofReal_eq_zero.1 h4) hpos
    · exact h4
  refine ⟨L, hLU, hLc, g, h1, fun l => h2 l, fun u hu => ?_⟩
  obtain ⟨h, hh, a, hua⟩ := hU u hu
  have h3 : y * u = (h : G) * (e a * y) := by
    have : y * u = (y * u * y⁻¹) * y := by group
    rw [this, hua, mul_assoc]
  show evL H σ (y * u) g = 0
  rw [h3]
  have h4 : evL H σ ((h : G) * (e a * y)) g = σ ⟨h, hh⟩ (evL H σ (e a * y) g) := hleft ⟨h, hh⟩ _ g
  rw [h4]
  have h5 : evL H σ (e a * y) g = 0 := by
    rw [show evL H σ (e a * y) g = _ from congrFun hφ a, hv0]
    simp
  rw [h5, map_zero]

end GlobalTheory.CompanionTheory.BZPhiPG.LocO

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactConjugacyTransversal
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.OrbitalCount

theorem exists_compact_reps_of_finite_doubleCosets :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K : Subgroup H) (N : H),
      IsCompact (K : Set H) →
      (∀ C : Set H, IsCompact C →
        {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
          ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C}.Finite) →
      ∀ C : Set H, IsCompact C →
        ∃ D : Set H, IsCompact D ∧ ∀ x : H, x⁻¹ * N * x ∈ C →
          ∃ t ∈ twCent (MonoidHom.id H) N, ∃ d ∈ D, x = t * d := by
  intro H _ _ _ K N hK hfin C hC
  refine ⟨⋃ q ∈ {q : DoubleCoset.Quotient (twCent (MonoidHom.id H) N : Set H) (K : Set H) |
      ∃ k ∈ K, (Quotient.out q * k)⁻¹ * N * MonoidHom.id H (Quotient.out q * k) ∈ C},
      (fun k => Quotient.out q * k) '' (K : Set H), ?_, ?_⟩
  · exact (hfin C hC).isCompact_biUnion fun q _ =>
      hK.image (continuous_const.mul continuous_id)
  · intro x hx
    obtain ⟨h, k, hh, hk, hout⟩ :=
      DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id H) N) K x
    have hcomm : h * N = N * h := hh
    have hconj : (h * x)⁻¹ * N * (h * x) = x⁻¹ * N * x := by
      have : h⁻¹ * N * h = N := by
        rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
      calc (h * x)⁻¹ * N * (h * x) = x⁻¹ * (h⁻¹ * N * h) * x := by group
        _ = x⁻¹ * N * x := by rw [this]
    set q := DoubleCoset.mk (twCent (MonoidHom.id H) N) K x with hq
    have hd : Quotient.out q * k⁻¹ = h * x := by
      rw [hout]; group
    refine ⟨h⁻¹, inv_mem hh, Quotient.out q * k⁻¹, ?_, ?_⟩
    · refine Set.mem_biUnion (x := q) ?_ ⟨k⁻¹, inv_mem hk, rfl⟩
      refine ⟨k⁻¹, inv_mem hk, ?_⟩
      rw [MonoidHom.id_apply, hd, hconj]
      exact hx
    · rw [hd, inv_mul_cancel_left]

end GlobalTheory.CompanionTheory.OrbitalCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteLeviStableChainsStatement
section
open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_levi_stable_chains : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (d : ℕ) (y : Cq n V),
    (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kA E1 E2 a b w ∈ S) →
    SuppL (inUU lev) y → DegL d y →
    ∃ T : Submodule ℂ (Cq n V), FiniteDimensional ℂ T ∧ y ∈ T ∧ (∀ x ∈ T, SuppL (inUU lev) x ∧ DegL d x) ∧
      ∀ p q : Fin n, lev p = lev q → ∀ x ∈ T, Lv lev E1 E2 p q x ∈ T := by
  first | exact @GlobalTheory.CompanionTheory.LvStableChains.exists_stable | exact GlobalTheory.CompanionTheory.LvStableChains.exists_stable | (intros; apply GlobalTheory.CompanionTheory.LvStableChains.exists_stable <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLargePrimeInRayClassStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_prime_in_ray_class : ∀ (F : Type) [Field F] [NumberField F] (𝔣 𝔞 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ → CoprimeTo F 𝔣 𝔞 → ∀ (W : Finset (𝓞 F)) (B : ℕ), (∀ x ∈ W, x ≠ 0) → ∃ 𝔠 : Ideal (𝓞 F), 𝔠.IsPrime ∧ (Ideal.absNorm 𝔠).Prime ∧ B < Ideal.absNorm 𝔠 ∧ CoprimeTo F 𝔣 𝔠 ∧ RayRel F 𝔣 𝔠 𝔞 ∧ ∀ x ∈ W, x ∉ 𝔠 := by
  first | exact @GlobalTheory.CompanionTheory.DegOneRay.exists_degOne_prime_in_rayClass | exact GlobalTheory.CompanionTheory.DegOneRay.exists_degOne_prime_in_rayClass | (intros; apply GlobalTheory.CompanionTheory.DegOneRay.exists_degOne_prime_in_rayClass <;> assumption)
end

