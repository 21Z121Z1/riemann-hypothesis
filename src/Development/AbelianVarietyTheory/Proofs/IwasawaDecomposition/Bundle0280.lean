import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMtTieCoord

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.CompactHowe Matrix Complex
open scoped TensorProduct Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockBaseChange

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockIndep

theorem cplxO_one {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℂ) : cplxO 1 1 z = I • z := by
  rw [cplxO, Matrix.one_mul, Matrix.mul_one]

theorem unitMap_mul {m n : ℕ} (B g : Matrix (Fin n) (Fin n) ℂ) (B' h : Matrix (Fin m) (Fin m) ℂ) (i : Fin m)
    (j : Fin n) : unitMap (B * g) (B' * h) i j = ∑ k, ∑ l, (h k i * g⁻¹ j l) • unitMap B B' k l := by
  have e : h * Matrix.single i j (1 : ℂ) * g⁻¹ = ∑ k, ∑ l, (h k i * g⁻¹ j l) • Matrix.single k l (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (h * Matrix.single i j (1 : ℂ) * g⁻¹)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j (fun b _ hb => by rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul])
      (by simp), Matrix.mul_single_apply_same, mul_one]
  unfold unitMap
  rw [Matrix.mul_inv_rev]
  calc B' * h * Matrix.single i j (1 : ℂ) * (g⁻¹ * B⁻¹) = B' * (h * Matrix.single i j (1 : ℂ) * g⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by simp only [e, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem omDir_I (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ' : D.what₂.Tau)
    (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omDir S T τ (cplxO 1 1 z) τ' (cplxO 1 1 z') = omDir S T τ z τ' z' ∧
    omDir S T τ z τ' (cplxO 1 1 z') = -omDir S T τ (cplxO 1 1 z) τ' z' := by
  unfold omDir
  split_ifs with h
  · simp only [cplxO_one, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      RCLike.star_def, conj_I]
    constructor
    · congr 3
      rw [← mul_assoc]; simp
    · simp only [neg_mul, mul_neg, Complex.neg_re]
  · simp

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
include hψ hθ

theorem dRho_dir_add (τ : D.what₂.Tau) (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dRho (heisO ψ S T) θ τ (z + z') f = dRho (heisO ψ S T) θ τ z f + dRho (heisO ψ S T) θ τ z' f := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ z g, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun z g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have hs := theta_sm h hf
  have e : piW θ T S (lineAt θ τ (z + z') 1) = piW θ T S (lineAt θ τ z 1) + piW θ T S (lineAt θ τ z' 1) := by
    rw [piW_lineAt hθ, piW_lineAt hθ, piW_lineAt hθ, Pi.single_add]
    rfl
  funext w
  rw [Pi.add_apply, hE, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
    LinearMap.map_add, ContinuousLinearMap.map_add]
  push_cast
  ring

theorem dRho_dir_smul (τ : D.what₂.Tau) (t : ℝ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    dRho (heisO ψ S T) θ τ ((t : ℂ) • z) f = (t : ℂ) • dRho (heisO ψ S T) θ τ z f := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hE : ∀ z g, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g =
      FockCompare.hD (iotaW σ T S) (piW θ T S) (omO S T) (piW θ T S (lineAt θ τ z 1)) g := fun z g =>
    dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  have hs := theta_sm h hf
  have e : piW θ T S (lineAt θ τ ((t : ℂ) • z) 1) = t • piW θ T S (lineAt θ τ z 1) := by
    rw [piW_lineAt hθ, piW_lineAt hθ, Pi.single_smul]
    rfl
  funext w
  rw [Pi.smul_apply, hE, hE, e, hD_eq_fderiv _ _ _ _ hs, hD_eq_fderiv _ _ _ _ hs,
    LinearMap.map_smul, ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem aPlus_dir_add (τ : D.what₂.Tau) (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO 1 1) (z + z') f =
      aPlus (heisO ψ S T) θ τ (cplxO 1 1) z f + aPlus (heisO ψ S T) θ τ (cplxO 1 1) z' f := by
  simp only [aPlus_eq, cplxO_one, smul_add, fun z z' => dRho_dir_add hψ hθ τ z z' hf]
  module

theorem aPlus_dir_smul (τ : D.what₂.Tau) (c : ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO 1 1) (c • z) f = c • aPlus (heisO ψ S T) θ τ (cplxO 1 1) z f := by
  have e1 : c • z = (c.re : ℂ) • z + (c.im : ℂ) • (I • z) := by
    rw [smul_smul, ← add_smul, re_add_im]
  have e2 : I • c • z = ((-c.im : ℝ) : ℂ) • z + (c.re : ℂ) • (I • z) := by
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    apply Complex.ext <;> simp
  simp only [aPlus_eq, cplxO_one]
  rw [e2, e1, dRho_dir_add hψ hθ τ _ _ hf, dRho_dir_add hψ hθ τ _ _ hf, dRho_dir_smul hψ hθ τ _ _ hf,
    dRho_dir_smul hψ hθ τ _ _ hf, dRho_dir_smul hψ hθ τ _ _ hf, dRho_dir_smul hψ hθ τ _ _ hf]
  generalize ((fockScale D τ : ℂ)⁻¹) = a
  match_scalars
  · linear_combination a * re_add_im c
  · linear_combination (-I) * a * re_add_im c + a * (c.im : ℂ) * I_mul_I

theorem aPlus_dir_sum {ι : Type} (τ : D.what₂.Tau) (s : Finset ι) (z : ι → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO 1 1) (∑ i ∈ s, z i) f = ∑ i ∈ s, aPlus (heisO ψ S T) θ τ (cplxO 1 1) (z i) f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := aPlus_dir_smul hψ hθ τ 0 0 hf
    rwa [zero_smul, zero_smul] at this
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, aPlus_dir_add hψ hθ τ _ _ hf, ih]

theorem aPlus_comm_one (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (τ' : D.what₂.Tau)
    (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ (cplxO 1 1) z (aPlus (heisO ψ S T) θ τ' (cplxO 1 1) z' f) =
    aPlus (heisO ψ S T) θ τ' (cplxO 1 1) z' (aPlus (heisO ψ S T) θ τ (cplxO 1 1) z f) := by
  have ht := fun τ z => theta_dRho hθ hψ τ z hf
  have hc := fun τ z τ' z' => dRho_comm hψ hθ τ z τ' z' hf
  obtain ⟨h1, h2⟩ := omDir_I τ z τ' z'
  rw [aPlus_eq τ' _ z' f, aPlus_eq τ _ z f, aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)), aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    aPlus_smul hψ hθ _ _ _ _ (ht _ _), aPlus_smul hψ hθ _ _ _ _ (ht _ _)]
  simp only [aPlus_eq]
  rw [hc τ z τ' z', hc τ z τ' (cplxO 1 1 z'), hc τ (cplxO 1 1 z) τ' z', hc τ (cplxO 1 1 z) τ' (cplxO 1 1 z')]
  rw [h1, h2]
  match_scalars
  all_goals first | ring1 | (ring_nf; simp only [I_pow_three]; ring1)

theorem pureTensorO_X_mul (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) (v : FVar D T.rank S.rank) :
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (MvPolynomial.X v * Q) =
      aPlus (heisO ψ S T) θ v.1 (cplxO 1 1) (unitMap (BS v.1) (BT v.1) v.2.1 v.2.2)
        (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f Q) := by
  unfold pureTensorO
  exact pure_X_mul (A := aPlusAll (heisO ψ S T) θ (fun _ => cplxO 1 1) BS BT) (P := IsThetaFunO ψ S T)
    (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) (fun i j _ h => aPlus_comm_one hψ hθ i.1 _ j.1 _ h)
    (fun i _ _ h h' => aPlus_add hψ hθ i.1 _ _ h h') (fun i a _ h => aPlus_smul hψ hθ i.1 _ _ a h) hf Q v

omit hψ hθ in

theorem pureTensorO_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS g : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT h : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun τ => BS τ * g τ) (fun τ => BT τ * h τ) f P = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (substF h (fun τ => ((g τ)⁻¹)ᵀ) P) := by
  intro D ψ θ S T hψ hθ BS g BT h f hf P
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [← mul_one (MvPolynomial.C a), MvPolynomial.C_mul', map_smul, map_smul, map_smul, map_one (substF _ _)]
    unfold pureTensorO
    rw [pure_one, pure_one]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    have hm : IsThetaFunO ψ S T
        (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f (substF h (fun τ => ((g τ)⁻¹)ᵀ) p)) :=
      pure_mem (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
        (fun _ _ h => aPlus_theta hψ hθ _ _ _ h) hf _
    rw [mul_comm, pureTensorO_X_mul hψ hθ _ _ hf, hp, map_mul, substF_X, unitMap_mul, aPlus_dir_sum hψ hθ _ _ _ hm,
      Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [aPlus_dir_sum hψ hθ _ _ _ hm, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [aPlus_dir_smul hψ hθ _ _ _ hm, mul_assoc, MvPolynomial.C_mul', map_smul, pureTensorO_X_mul hψ hθ _ _ hf]
    rfl

end GlobalTheory.FockBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorMaximalCompactBasisSubstitut
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubst

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex GlobalTheory.Ker.FockAlg

section Generic

variable {ι X : Type} {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem pure_subst {κ : Type} [Fintype κ] (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (hA : ∀ i f, P f → P (A i f)) (hc : ∀ i j f, P f → A i (A j f) = A j (A i f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f')
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f)
    (hA' : ∀ i f, P f → P (A' i f)) (hc' : ∀ i j f, P f → A' i (A' j f) = A' j (A' i f))
    (Aadd' : ∀ i f f', P f → P f' → A' i (f + f') = A' i f + A' i f')
    (Asm' : ∀ i (a : ℂ) f, P f → A' i (a • f) = a • A' i f)
    (c : ι → κ → ℂ) (r : ι → κ → ι) (h : ∀ i f, P f → A' i f = ∑ b, c i b • A (r i b) f)
    {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) :
    pureTensorL A' f Q = pureTensorL A f
      (MvPolynomial.aeval (fun v : ι => ∑ b, c v b • (MvPolynomial.X (r v b) : MvPolynomial ι ℂ)) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a), MvPolynomial.C_mul',
      map_smul, map_smul, pure_one, pure_one]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, pure_X_mul hadd hsm hA' hc' Aadd' Asm' hf, hp, h _ _ (pure_mem hadd hsm hA hf _), map_mul,
      MvPolynomial.aeval_X, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_mul_assoc, map_smul, pure_X_mul hadd hsm hA hc Aadd Asm hf]

end Generic

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (τ : D.what₂.Tau)
  (s : Matrix (Fin S.rank) (Fin S.rank) ℂ) (t : Matrix (Fin T.rank) (Fin T.rank) ℂ)
  {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)

include hψ hθ hf

theorem dRho_csmul (w : ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    Datum.dRho (heisO ψ S T) θ τ (w • u) f =
      (w.re : ℂ) • Datum.dRho (heisO ψ S T) θ τ u f + (w.im : ℂ) • Datum.dRho (heisO ψ S T) θ τ (I • u) f := by
  have e : w • u = (w.re : ℂ) • u + (w.im : ℂ) • (I • u) := by
    rw [smul_smul, ← add_smul, Complex.re_add_im]
  rw [e, (dRho_laws hψ hθ hf τ _).2.2.1, (dRho_laws hψ hθ hf τ _).2.2.2.1, (dRho_laws hψ hθ hf τ _).2.2.2.1]

theorem aPlus_dir_add (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (z + z') f =
      aPlus (heisO ψ S T) θ τ (cplxO s t) z f + aPlus (heisO ψ S T) θ τ (cplxO s t) z' f := by
  simp only [aPlus_eq, GlobalTheory.OrientedRealForm.cplxO_add, fun z => (dRho_laws hψ hθ hf τ z).2.2.1]
  module

theorem aPlus_dir_zero : aPlus (heisO ψ S T) θ τ (cplxO s t) 0 f = 0 := by
  have := aPlus_dir_add hψ hθ τ s t hf 0 0
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem aPlus_dir_sum {κ : Type} (F : Finset κ) (z : κ → Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (∑ b ∈ F, z b) f = ∑ b ∈ F, aPlus (heisO ψ S T) θ τ (cplxO s t) (z b) f := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using aPlus_dir_zero hψ hθ τ s t hf
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, aPlus_dir_add hψ hθ τ s t hf, ih]

theorem aPlus_dir_smul (e : Bool) (w : ℂ) {u : Matrix (Fin T.rank) (Fin S.rank) ℂ}
    (hu : cplxO s t u = ((if e then 1 else -1 : ℂ) * I) • u) :
    aPlus (heisO ψ S T) θ τ (cplxO s t) (w • u) f =
      (if e then w else starRingEnd ℂ w) • aPlus (heisO ψ S T) θ τ (cplxO s t) u f := by
  have h1 : cplxO s t (w • u) = (w * ((if e then 1 else -1 : ℂ) * I)) • u := by
    rw [← smul_smul, ← hu]
    unfold cplxO
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  rw [aPlus_eq, aPlus_eq, h1, hu, dRho_csmul hψ hθ τ hf w, dRho_csmul hψ hθ τ hf (w * _),
    dRho_csmul hψ hθ τ hf (_ * I)]
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, w = x + y * I := ⟨w.re, w.im, (Complex.re_add_im w).symm⟩
  cases e
  · simp only [Bool.false_eq_true, if_false, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    match_scalars <;> simp <;> ring_nf <;> simp
  · simp only [if_true]
    match_scalars <;> simp <;> ring_nf <;> simp

omit hψ hθ hf

theorem unitMap_mul {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' k : Matrix (Fin m) (Fin m) ℂ) (a : Fin m)
    (j : Fin n) : unitMap B (B' * k) a j = ∑ b, k b a • unitMap B B' b j := by
  have e : k * single a j (1 : ℂ) = ∑ b, k b a • single b j (1 : ℂ) := by
    ext p q
    by_cases h : j = q
    · subst h
      simp [Matrix.sum_apply, Matrix.single_apply]
    · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, h]
  unfold unitMap
  rw [Matrix.mul_assoc B', e, Matrix.mul_sum, Matrix.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul]

theorem cplxO_unitMap {S' : D.what₂.Tau → SPar} (M : DSModel T S') {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin T.rank) (j : Fin n) : cplxO 1 (cart M τ) (unitMap B (onb M τ) b j) =
      ((if M.ε τ b then 1 else -1 : ℂ) * I) • unitMap B (onb M τ) b j := by
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have e : Formalism.REAL.Jm (M.ε τ) * single b j (1 : ℂ) = (if M.ε τ b then 1 else -1 : ℂ) • single b j (1 : ℂ) := by
    ext p q
    rw [Formalism.REAL.Jm, diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases h : b = p
    · rw [h]
    · simp [h]
  unfold cplxO unitMap cart onb
  rw [Matrix.mul_one, mul_comm _ I, ← smul_smul]
  congr 1
  calc _ = (M.fr τ)⁻¹ * (Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * single b j (1 : ℂ)) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_one, e, Matrix.mul_smul, Matrix.smul_mul]

theorem kset_zero {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) {a b : Fin n}
    (h : ε b ≠ ε a) : k b a = 0 := by
  have e := congrFun (congrFun hk.2 b) a
  rw [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at e
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, ne_eq, not_true_eq_false] at h e <;> simp at e <;>
    first | linear_combination (1 / 2 : ℂ) * e | linear_combination (-1 / 2 : ℂ) * e

theorem pureTensorO_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (S' : D.what₂.Tau → SPar) (M : DSModel T S') (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) (k c : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) 1) → IsThetaFunO ψ S T f → (∀ τ, k τ ∈ Formalism.REAL.Kset (M.ε τ)) → (∀ τ a b, c τ b a = if M.ε τ a then k τ b a else starRingEnd ℂ (k τ b a)) → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (fun τ => onb M τ * k τ) f P = pureTensorO ψ θ S T (fun _ => 1) (cart M) BS (onb M) f (MvPolynomial.aeval (fun v : FVar D T.rank S.rank => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P) := by
  intro D ψ θ S T S' M BS f k c hψ hθ hS hf hk hc P
  have hT := GlobalTheory.Chain.VacVec.cart_isCartanInv M
  have hA : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f) :=
    fun _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i f f', IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T f' → aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i (f + f') =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f +
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f' :=
    fun _ _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f :=
    fun _ _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ (B : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) i j f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B j f) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B j
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS B i f) :=
    fun _ i j _ h => aPlus_comm (sS := fun _ => 1) (sT := cart M) hψ hθ i.1 _ hS hT j.1 _ h
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (fun τ => onb M τ * k τ) i g =
      ∑ b, c i.1 b i.2.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (cart M τ)) BS (onb M) (i.1, b, i.2.2) g := by
    rintro ⟨τ, a, j⟩ g hg
    simp only [aPlusAll]
    rw [unitMap_mul, aPlus_dir_sum hψ hθ τ _ _ hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [aPlus_dir_smul hψ hθ τ _ _ hg _ _ (cplxO_unitMap τ M _ b j), hc]
    by_cases h : M.ε τ b = M.ε τ a
    · rw [h]
    · rw [kset_zero (hk τ) h]
      simp
  unfold pureTensorO
  exact pure_subst (P := IsThetaFunO ψ S T) (fun _ _ => theta_add) (fun a _ => theta_smul a)
    (hA _) (Ac _) (Aadd _) (Asm _) (hA _) (Ac _) (Aadd _) (Asm _)
    (fun v b => c v.1 b v.2.1) (fun v b => (v.1, b, v.2.2)) key hf P

end GlobalTheory.FockSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsModelHolomorphicIntegralExtremalWeight
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLift

theorem holShape_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_order → ∀ i, HolShape (R.MW i (sg0 D A)) ∧ ∃ w, WtIs (R.MW i (sg0 D A)) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R ho i
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i (sg0 D A)).lam ρ) := fun ρ => by
    have he := (R.MW i (sg0 D A)).enum ρ
    refine ⟨he.1, fun a => ?_⟩
    obtain ⟨-, f, hf, hS⟩ := he
    have hp : Links.parAt (Wc D i) (sg0 D A) ρ = Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) ρ) := by
      rw [hs]; exact GlobalTheory.ThetaFiresProbe.parAt_fixed _ ρ
    rw [hp] at hS
    have hm : (f a, (R.MW i (sg0 D A)).ε ρ a) ∈ Formalism.L2.NTheta.holPar _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) ρ) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hm
    have hx1 := congrArg Prod.fst hx
    have hn : (((Wc D i).rank : ℕ) : ℝ) = (((Wc D i).sig (tauE D ρ)).1 : ℝ) + ((Wc D i).sig (tauE D ρ)).2 := by
      rw [← hpq ρ]; push_cast; rfl
    dsimp only at hx1
    rw [hf a, ← hx1, hn]
    rcases x with c | c
    · refine ⟨Formalism.L2.NTheta.wtOf D (Wc D i) ρ (Sum.inl c) - ((Wc D i).sig (tauE D ρ)).2 - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inl]
      push_cast
      ring
    · refine ⟨Formalism.L2.NTheta.wtOf D (Wc D i) ρ (Sum.inr c) - (c : ℕ), ?_⟩
      simp only [Formalism.L2.NTheta.holEnt, Sum.elim_inr]
      push_cast
      ring
  refine ⟨fun ρ => ⟨hc ρ, _, (Nat.le_add_right _ _).trans (hpq ρ).le, fun a => ho i ρ a⟩, ?_⟩
  choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i (sg0 D A)).ε ρ) _ (hc ρ).2 a
  exact ⟨fun ρ c => w ρ (revNeg ((R.MW i (sg0 D A)).ε ρ) (arr (nNeg ((R.MW i (sg0 D A)).ε ρ)) c)),
    fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.DefLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalR
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G GlobalTheory.Points
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def constHom (M : RatModel o Ω) (U : M.Z.Opens) : o →+* Γ(M.Z, U) :=
  (M.s.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom

theorem finiteType_constHom (M : RatModel o Ω) {U : M.Z.Opens} (hU : IsAffineOpen U) :
    (M.constHom U).FiniteType := by
  have := M.lft
  have h1 : (M.s.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
    M.s.finiteType_appLE (isAffineOpen_top _) hU _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

variable {Ω' : Type} [Field Ω'] [Algebra o Ω']

theorem exists_nbhd_of_map_O (M : RatModel o Ω) (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω') {z' : M'.Z} {z : M.Z}
    (hz : ∀ a ∈ M.O z, φ a ∈ M'.O z') :
    ∃ (V : M'.Z.Opens) (U : M.Z.Opens), z' ∈ V ∧ IsAffineOpen U ∧ (U : Set M.Z).Nonempty ∧
      ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M.Z.Opens)) (x := z) trivial
  have hUne : (U : Set M.Z).Nonempty := ⟨z, hzU⟩
  letI := (M.constHom U).toAlgebra
  obtain ⟨s, hs⟩ := (M.finiteType_constHom hU).out
  let V : M'.Z.Opens := ⟨⋂ f ∈ s, {w | φ (valF M.pt U f) ∈ M'.O w},
    isOpen_biInter_finset fun f _ => M'.isOpen_setOf_mem_O _⟩
  have hzV : z' ∈ V := Set.mem_iInter₂.2 fun f _ => hz _ (valF_mem_O hzU f)
  have hsV : ∀ f ∈ s, φ (valF M.pt U f) ∈ M'.ringOn V := fun f hf =>
    mem_ringOn.2 fun w hw => Set.mem_iInter₂.1 hw f hf
  have key : ∀ f : Γ(M.Z, U), φ (valF M.pt U f) ∈ M'.ringOn V := by
    intro f
    have hf : f ∈ Algebra.adjoin o (s : Set Γ(M.Z, U)) := hs ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact hsV x hx
    | algebraMap r =>
      have e : valF M.pt U (algebraMap o Γ(M.Z, U) r) = algebraMap o Ω r := M.valF_constFn hUne r
      rw [e, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy =>
      rw [← M.res_apply U hUne, map_add, map_add, res_apply, res_apply]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [← M.res_apply U hUne, map_mul, map_mul, res_apply, res_apply]
      exact mul_mem hx hy
  refine ⟨V, U, hzV, hU, hUne, fun x hx => ?_⟩
  obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hUne).1 hx
  exact key f

theorem exists_isHom_of_map_O :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω']
      (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') →
        ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  intro o Ω _ _ _ M Ω' _ _ M' φ h
  refine exists_isHom_of_local fun z' => ?_
  obtain ⟨z, hz⟩ := h z'
  exact exists_nbhd_of_map_O M M' φ hz

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertInnerLiftFormsEqBaseLevelHermitian
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
noncomputable section
namespace GlobalTheory.Mem.R3

theorem liftForm_inner_eq_hform : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (i : Fin D.R.m) (t : T) (x y : Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL), (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB i t x y
  have h1 : ∀ f g : (A.MtCSD i t).Forms, ⟪R.jV i t f, R.jV i t g⟫_ℂ = D.what₂.embLL ((A.MtCSD i t).csum f g) := by
    intro f g
    refine ((hB.models.HV i t).2.2 _ _).trans ?_
    refine (congrArg₂ _ (hB.models.jV i t f) (hB.models.jV i t g)).trans ?_
    exact (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.2 f g
  have h2 := GlobalTheory.Mem.LiftForms.csum_lvlForm (A.fam.L i t).S (A.fam.L i t).r (A.fam.lvlA F.P0 F.ψ0).P (A.fam.lvlA F.P0 F.ψ0).ψ x y
  have h3 : ⟪R.jV i t (liftForm A F.P0 F.ψ0 i t x), R.jV i t (liftForm A F.P0 F.ψ0 i t y)⟫_ℂ =
      D.what₂.embLL ((Nat.card (A.fam.lvlA F.P0 F.ψ0).P : D.what₂.LL) * Formalism.DivisionValues.hform (lH D A F.P0 F.ψ0 i t) x y) :=
    (h1 (liftForm A F.P0 F.ψ0 i t x) (liftForm A F.P0 F.ψ0 i t y)).trans (congrArg D.what₂.embLL h2)
  have hP : RealDat.nP F false = (Nat.card F.P0 : ℝ) := rfl
  have hc : (Nat.card F.P0 : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := F.P0)).ne'
  rw [h3, map_mul, map_natCast, hP, ← mul_assoc]
  change ((((Nat.card F.P0 : ℝ))⁻¹ : ℝ) : ℂ) * (Nat.card F.P0 : ℂ) * _ = _
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀ hc, one_mul]

end GlobalTheory.Mem.R3
end
end

