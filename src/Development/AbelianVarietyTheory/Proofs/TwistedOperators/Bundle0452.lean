import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVectorDatumEqSumLevelClassIndicators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0413
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0441

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorFrameChangeSameCartan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.FrameChange

variable {D : D7}

theorem sign_eq_of_ne_zero {n : ℕ} {ε ε' : Fin n → Bool} {x : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.Jm ε * x = x * Formalism.REAL.Jm ε') {a i : Fin n} (hx : x a i ≠ 0) : ε a = ε' i := by
  have hc := congrFun (congrFun h a) i
  rw [Formalism.REAL.Jm, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at hc
  by_contra hne
  apply hx
  cases h1 : ε a <;> cases h2 : ε' i <;> simp only [h1, h2] at hc hne
  · exact (hne trivial).elim
  · simp at hc; linear_combination -hc / 2
  · simp at hc; linear_combination hc / 2
  · exact (hne trivial).elim

theorem Jm_mul_fr {V : HSp D} (X Y : Fr V) (τ : D.what₂.Tau) (h : Y.cart τ = X.cart τ) :
    Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹) = X.fr τ * (Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) := by
  unfold Fr.cart at h
  calc Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹)
      = (X.fr τ * (X.fr τ)⁻¹) * Formalism.REAL.Jm (X.ε τ) * (X.fr τ * (Y.fr τ)⁻¹) := by
        rw [GlobalTheory.CompactFockAction.fr_mul_inv, Matrix.one_mul]
    _ = X.fr τ * ((X.fr τ)⁻¹ * Formalism.REAL.Jm (X.ε τ) * X.fr τ) * (Y.fr τ)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = X.fr τ * ((Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) * Y.fr τ) * (Y.fr τ)⁻¹ := by rw [h]
    _ = X.fr τ * (Y.fr τ)⁻¹ * Formalism.REAL.Jm (Y.ε τ) * (Y.fr τ * (Y.fr τ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [GlobalTheory.CompactFockAction.fr_mul_inv, Matrix.mul_one]

theorem fr_mul_inv_mul {V : HSp D} (X Y : Fr V) (τ : D.what₂.Tau) :
    X.fr τ * (Y.fr τ)⁻¹ * (Y.fr τ * (X.fr τ)⁻¹) = 1 := by
  calc X.fr τ * (Y.fr τ)⁻¹ * (Y.fr τ * (X.fr τ)⁻¹) = X.fr τ * ((Y.fr τ)⁻¹ * Y.fr τ) * (X.fr τ)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [GlobalTheory.CompactFockAction.inv_mul_fr, Matrix.mul_one, GlobalTheory.CompactFockAction.fr_mul_inv]

section Coef

variable {V W : HSp D}

def coef (A A' : Fr V) (B B' : Fr W) (v : FVar D W.rank V.rank) (p : Fin W.rank × Fin V.rank) : ℂ :=
  if B'.ε v.1 v.2.1 = A'.ε v.1 v.2.2 then
    (B.fr v.1 * (B'.fr v.1)⁻¹) p.1 v.2.1 * (A'.fr v.1 * (A.fr v.1)⁻¹) v.2.2 p.2
  else starRingEnd ℂ ((B.fr v.1 * (B'.fr v.1)⁻¹) p.1 v.2.1 * (A'.fr v.1 * (A.fr v.1)⁻¹) v.2.2 p.2)

def sub (A A' : Fr V) (B B' : Fr W) : PolF D W.rank V.rank →ₐ[ℂ] PolF D W.rank V.rank :=
  MvPolynomial.aeval fun v => ∑ p, coef A A' B B' v p • (MvPolynomial.X (v.1, p.1, p.2) : PolF D W.rank V.rank)

end Coef

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}

theorem onb_eq (X Y : Fr V) (τ : D.what₂.Tau) : Y.onb τ = X.onb τ * (X.fr τ * (Y.fr τ)⁻¹) := by
  unfold Fr.onb
  rw [← Matrix.mul_assoc, GlobalTheory.CompactFockAction.inv_mul_fr, Matrix.one_mul]

theorem inv_fr_mul (X Y : Fr V) (τ : D.what₂.Tau) : (X.fr τ * (Y.fr τ)⁻¹)⁻¹ = Y.fr τ * (X.fr τ)⁻¹ :=
  Matrix.inv_eq_left_inv (fr_mul_inv_mul Y X τ)

theorem aPlusAll_change (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A A' : Fr V) (B B' : Fr W)
    (hA : ∀ τ, A'.cart τ = A.cart τ) (hB : ∀ τ, B'.cart τ = B.cart τ) (v : FVar D W.rank V.rank)
    (g : WO V W → ℂ) (hg : IsThetaFunO ψ V W g) :
    aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) A'.onb B'.onb v g =
      ∑ p, coef A A' B B' v p •
        aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) A.onb B.onb (v.1, p.1, p.2) g := by
  obtain ⟨ρ, i, j⟩ := v
  simp only [aPlusAll]
  rw [onb_eq A A' ρ, onb_eq B B' ρ, GlobalTheory.FockBasis.unitMap_mul, inv_fr_mul,
    GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ ρ _ _ hg, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ ρ _ _ hg]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (GlobalTheory.CompactFockAction.Jm_single A B ρ a b)]
  congr 1
  simp only [coef]
  by_cases hx : (B.fr ρ * (B'.fr ρ)⁻¹) a i * (A'.fr ρ * (A.fr ρ)⁻¹) j b = 0
  · simp [hx]
  · have h1 := sign_eq_of_ne_zero (Jm_mul_fr B B' ρ (hB ρ)) (left_ne_zero_of_mul hx)
    have h2 := sign_eq_of_ne_zero (Jm_mul_fr A' A ρ (hA ρ).symm) (right_ne_zero_of_mul hx)
    rw [h1, ← h2]
    simp only [decide_eq_true_eq]

theorem ptF_sub (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A A' : Fr V) (B B' : Fr W)
    (hA : ∀ τ, A'.cart τ = A.cart τ) (hB : ∀ τ, B'.cart τ = B.cart τ) {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (Q : PolF D W.rank V.rank) :
    ptF ψ θ A' B' f Q = ptF ψ θ A B f (sub A A' B B' Q) := by
  have e1 : A'.cart = A.cart := funext hA
  have e2 : B'.cart = B.cart := funext hB
  have hS := GlobalTheory.CompactFockAction.cart_isCartanInv A
  have hT := GlobalTheory.CompactFockAction.cart_isCartanInv B
  unfold ptF pureTensorO sub
  rw [e1, e2]
  have hAt : ∀ X Y i f, IsThetaFunO ψ V W f →
      IsThetaFunO ψ V W (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f) :=
    fun _ _ _ _ h => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h
  have Aadd : ∀ X Y i f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i (f + f') =
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f +
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f' :=
    fun _ _ _ _ _ h h' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ h h'
  have Asm : ∀ X Y i (a : ℂ) f, IsThetaFunO ψ V W f →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i (a • f) =
      a • aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f :=
    fun _ _ _ a _ h => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a h
  have Ac : ∀ X Y i j f, IsThetaFunO ψ V W f →
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i
        (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y j f) =
      aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y j
        (aPlusAll (heisO ψ V W) θ (fun ρ => cplxO (A.cart ρ) (B.cart ρ)) X Y i f) :=
    fun _ _ i j _ h => GlobalTheory.FockSubst.aPlus_comm (sS := A.cart) (sT := B.cart) hψ hθ i.1 _ hS hT j.1 _ h
  exact GlobalTheory.FockSubst.pure_subst (P := IsThetaFunO ψ V W) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (hAt _ _) (Ac _ _) (Aadd _ _) (Asm _ _) (hAt _ _) (Ac _ _)
    (Aadd _ _) (Asm _ _) (coef A A' B B') (fun v p => (v.1, p.1, p.2))
    (aPlusAll_change hψ hθ A A' B B' hA hB) hf Q

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

variable {D : D7} {V W : HSp D}

theorem coef_comp (X X' : Fr V) (Y Y' : Fr W) (hX : ∀ τ, X'.cart τ = X.cart τ) (hY : ∀ τ, Y'.cart τ = Y.cart τ)
    (v : FVar D W.rank V.rank) (q : Fin W.rank × Fin V.rank) :
    ∑ p, coef X' X Y' Y v p * coef X X' Y Y' (v.1, p.1, p.2) q = if q = (v.2.1, v.2.2) then 1 else 0 := by
  obtain ⟨ρ, i, j⟩ := v

  have hK : ∀ c d, (∑ a, (Y'.fr ρ * (Y.fr ρ)⁻¹) a d * (Y.fr ρ * (Y'.fr ρ)⁻¹) c a) = if c = d then 1 else 0 := by
    intro c d
    have := congrFun (congrFun (fr_mul_inv_mul Y Y' ρ) c) d
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hU : ∀ c d, (∑ b, (X.fr ρ * (X'.fr ρ)⁻¹) c b * (X'.fr ρ * (X.fr ρ)⁻¹) b d) = if c = d then 1 else 0 := by
    intro c d
    have := congrFun (congrFun (fr_mul_inv_mul X X' ρ) c) d
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    exact this
  have hprod : (∑ p : Fin W.rank × Fin V.rank, ((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
      ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)) = if q = (i, j) then 1 else 0 := by
    rw [Fintype.sum_prod_type]
    have e : ∀ a b, ((Y'.fr ρ * (Y.fr ρ)⁻¹) a i * (X.fr ρ * (X'.fr ρ)⁻¹) j b) *
        ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 a * (X'.fr ρ * (X.fr ρ)⁻¹) b q.2) =
        ((Y'.fr ρ * (Y.fr ρ)⁻¹) a i * (Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 a) *
        ((X.fr ρ * (X'.fr ρ)⁻¹) j b * (X'.fr ρ * (X.fr ρ)⁻¹) b q.2) := fun a b => by ring
    simp only [e, ← Finset.mul_sum, ← Finset.sum_mul, hU, hK]
    obtain ⟨q1, q2⟩ := q
    by_cases h1 : q1 = i <;> by_cases h2 : j = q2 <;> (try simp [h1, h2]) <;> (try exact fun h => h1 h.symm) <;>
      (try exact fun h => h2 h.symm)

  have hterm : ∀ p : Fin W.rank × Fin V.rank, coef X' X Y' Y (ρ, i, j) p * coef X X' Y Y' (ρ, p.1, p.2) q =
      if Y.ε ρ i = X.ε ρ j then
        ((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
          ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)
      else starRingEnd ℂ (((Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2) *
          ((Y.fr ρ * (Y'.fr ρ)⁻¹) q.1 p.1 * (X'.fr ρ * (X.fr ρ)⁻¹) p.2 q.2)) := by
    intro p
    simp only [coef]
    by_cases hx : (Y'.fr ρ * (Y.fr ρ)⁻¹) p.1 i * (X.fr ρ * (X'.fr ρ)⁻¹) j p.2 = 0
    · simp [hx]
    · have h1 := sign_eq_of_ne_zero (Jm_mul_fr Y' Y ρ (hY ρ).symm) (left_ne_zero_of_mul hx)
      have h2 := sign_eq_of_ne_zero (Jm_mul_fr X X' ρ (hX ρ)) (right_ne_zero_of_mul hx)
      rw [h1, ← h2]
      split_ifs <;> simp [map_mul]
  by_cases hs : Y.ε ρ i = X.ε ρ j
  · simp only [hterm, hs, if_true]
    exact hprod
  · simp only [hterm, hs, if_false]
    rw [← map_sum, hprod]
    split_ifs <;> simp

theorem sub_comp (X X' : Fr V) (Y Y' : Fr W) (hX : ∀ τ, X'.cart τ = X.cart τ) (hY : ∀ τ, Y'.cart τ = Y.cart τ) :
    (sub X X' Y Y').comp (sub X' X Y' Y) = AlgHom.id ℂ (PolF D W.rank V.rank) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [AlgHom.comp_apply, AlgHom.id_apply]
  obtain ⟨ρ, i, j⟩ := v
  calc sub X X' Y Y' (sub X' X Y' Y (MvPolynomial.X (ρ, i, j)))
      = ∑ p : Fin W.rank × Fin V.rank, coef X' X Y' Y (ρ, i, j) p •
          ∑ q : Fin W.rank × Fin V.rank, coef X X' Y Y' (ρ, p.1, p.2) q •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        simp only [sub, MvPolynomial.aeval_X, map_sum, map_smul]
    _ = ∑ q : Fin W.rank × Fin V.rank, (∑ p : Fin W.rank × Fin V.rank,
          coef X' X Y' Y (ρ, i, j) p * coef X X' Y Y' (ρ, p.1, p.2) q) •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        exact Finset.sum_comm
    _ = ∑ q : Fin W.rank × Fin V.rank, (if q = (i, j) then (1 : ℂ) else 0) •
            (MvPolynomial.X (ρ, q.1, q.2) : PolF D W.rank V.rank) := by
        simp only [coef_comp X X' Y Y' hX hY (ρ, i, j)]
    _ = MvPolynomial.X (ρ, i, j) := by
        rw [Finset.sum_eq_single (i, j)]
        · simp
        · intro q _ hq
          simp [hq]
        · simp

end GlobalTheory.FrameChange

namespace GlobalTheory.FrameChange

theorem ptF_frame_change : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (V W : HSp D) (A A' : Fr V) (B B' : Fr W), (∀ τ, A'.cart τ = A.cart τ) → (∀ τ, B'.cart τ = B.cart τ) → ∃ j : PolF D W.rank V.rank ≃ₗ[ℂ] PolF D W.rank V.rank, ∀ f, IsThetaFunO ψ V W f → ∀ P, ptF ψ θ A' B' f (j P) = ptF ψ θ A B f P := by
  intro D ψ θ hψ hθ V W A A' B B' hA hB
  let e : PolF D W.rank V.rank ≃ₐ[ℂ] PolF D W.rank V.rank :=
    AlgEquiv.ofAlgHom (sub A' A B' B) (sub A A' B B') (sub_comp A' A B' B (fun τ => (hA τ).symm) fun τ => (hB τ).symm)
      (sub_comp A A' B B' hA hB)
  refine ⟨e.toLinearEquiv, fun f hf P => ?_⟩
  exact (ptF_sub hψ hθ A' A B' B (fun τ => (hA τ).symm) (fun τ => (hB τ).symm) hf P).symm

end GlobalTheory.FrameChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyAppellHumbertFramePullEqTransitionMu
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)

noncomputable section

namespace GlobalTheory.HeckeEx

theorem frame_pull_eq_transition_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (yx zx : Sp ℂ ⟶ Xo.X) (p : ℕ)
  (ψp : (Over.mk yx ⟶ Xo.univ.t.G) →* (Over.mk zx ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk yx ⟶ Xo.univ.t.G) → ℂ)
  (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (e : (Fin g → ℂ) → (Over.mk yx ⟶ Xo.univ.t.G)) (e' : (Fin g → ℂ) → (Over.mk zx ⟶ Xo.univ.t.G))
  (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
  Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
  IsHolTo Set.univ (fun w => (e w).left) → IsHolTo Set.univ (fun w => (e' w).left) →
  (∀ w w', e (w + w') = e w * e w') → (∀ a ∈ Λ, e a = 1) → (∀ w, e' (h w) = ψp (e w)) →
  (∀ a ∈ Λ, h a ∈ Λ') →
  (∀ i j (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) →
  (∀ i j i' j' (a : Over.mk yx ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
    ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
    b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
      valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) →
  (∀ i j, ⊤ ≤ (1 : Over.mk zx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
    ⊤ ≤ (1 : Over.mk yx ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
      b i j 1 * valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
  (∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
    {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
  ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    Hm.IsHermitian →
    (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → fr j z ≠ 0) →
    (∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr j z = valAt' (e z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr j' z) →
    (∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j 0 = valAt' yx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ, ∀ j z, ‖χl a‖ = 1 ∧ (⊤ ≤ (e z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr j z = χl a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a))) →
  ∀ (Hm' : Matrix (Fin g) (Fin g) ℂ) (χl' : (Fin g → ℂ) → ℂ) (fr' : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ),
    (∀ z w, hermForm Hm' (h z) (h w) = ((p : ℂ) ^ 2) * hermForm Hm z w) →
    (∀ j, DifferentiableOn ℂ (fr' j) {z | ⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) →
    (∀ j j' z, ⊤ ≤ (e' z).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      fr' j z = valAt' (e' z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val * fr' j' z) →
    (∀ j, ⊤ ≤ (e' 0).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j 0 = valAt' zx ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) →
    (∀ a ∈ Λ', ∀ j z, ‖χl' a‖ = 1 ∧ (⊤ ≤ (e' z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      fr' j z = χl' a * Complex.exp (Real.pi * hermForm Hm' z a + Real.pi / 2 * hermForm Hm' a a) * fr' j (z + a))) →
  ∀ w i j, ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
    fr' i (h w) = b i j (e w) * fr j ((p : ℂ) • w) := by
  intro E _ _ _ H Dw l Xo yx zx p ψp b g Λ Λ' e e' h hΛ hhe hhe' hadd hker hψ hΛΛ' hbn hbc hb0 hbd
    Hm χl fr hH hd hn hc h0 ha Hm' χl' fr' hHH hd' hc' h0' ha' w i j hi hj
  have e0 : e 0 = 1 := hker 0 (zero_mem Λ)
  have hpow : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n := by
    intro n z
    induction n with
    | zero => rw [Nat.cast_zero, zero_smul, e0, pow_zero]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, hadd, ih, pow_succ]
  have e'0 : e' 0 = 1 := by rw [← map_zero h, hψ, e0, map_one]
  have hpa : ∀ a ∈ Λ, (p : ℂ) • a ∈ Λ := fun a haa => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem haa p
  have per : ∀ a ∈ Λ, ∀ z, e (z + a) = e z := fun a haa z => by rw [hadd, hker a haa]; exact @_root_.mul_one _ (CategoryTheory.Hom.monoid).toMulOneClass _
  have hsm : ∀ z a, hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a) = (p : ℂ) ^ 2 * hermForm Hm z a := fun z a => by
    rw [GlobalTheory.UnitFrameGen.hermForm_smul_left, GlobalTheory.UnitFrameGen.hermForm_smul_right, star_natCast]; ring
  have ho1 : ∀ V, IsOpen {z | ⊤ ≤ (e z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe V 0).1
  have ho1' : ∀ V, IsOpen {z | ⊤ ≤ (e' z).left ⁻¹ᵁ V} := fun V => by simpa using (hhe' V 0).1
  have hch : Continuous h := h.toLinearMap.continuous_of_finiteDimensional
  have dh : Differentiable ℂ (fun z => h z) := (LinearMap.toContinuousLinearMap h.toLinearMap).differentiable
  have dsm : Differentiable ℂ (fun z : Fin g → ℂ => (p : ℂ) • z) := differentiable_id.const_smul (p : ℂ)
  have key := GlobalTheory.UnitFrameGen.frames_eq Λ hΛ
    (fun q : Xo.univ.t.PP.L.ι × Xo.univ.t.PP.L.ι =>
      {w | ⊤ ≤ (e' (h w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.1 ∧ ⊤ ≤ (e ((p : ℂ) • w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U q.2})
    (fun q => ((ho1' _).preimage hch).inter ((ho1 _).preimage (continuous_const_smul (p : ℂ))))
    (fun z => by
      obtain ⟨i', hi'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e' (h z)).left
      obtain ⟨j', hj'⟩ := GlobalTheory.ThetaPtChg.exists_chart_point Xo.univ.t.PP.isLB (e ((p : ℂ) • z)).left
      exact ⟨(i', j'), hi', hj'⟩)
    (fun q a haa z hz => by
      refine ⟨?_, ?_⟩
      · rw [hψ, per a haa, ← hψ]; exact hz.1
      · rw [smul_add, per _ (hpa a haa)]; exact hz.2)
    (fun q z => b q.1 q.2 (e z) * fr q.2 ((p : ℂ) • z)) (fun q z => fr' q.1 (h z))
    (fun q q' z => valAt' (e' (h z)).left (Xo.univ.t.PP.L.U q.1 ⊓ Xo.univ.t.PP.L.U q'.1)
      (Xo.univ.t.PP.L.g q.1 q'.1).val)
    (fun a z => Real.exp (Real.pi * (hermForm Hm ((p : ℂ) • z) ((p : ℂ) • a)).re +
      Real.pi / 2 * (hermForm Hm ((p : ℂ) • a) ((p : ℂ) • a)).re))
    (fun q => ((hbd q.1 q.2).mono fun z hz => ⟨by rw [← hψ]; exact hz.1, by rw [← hpow]; exact hz.2⟩).mul
      ((hd q.2).comp dsm.differentiableOn fun z hz => hz.2))
    (fun q => (hd' q.1).comp dh.differentiableOn fun z hz => hz.1)
    (fun q z hz => mul_ne_zero (hbn q.1 q.2 (e z) (by rw [← hψ]; exact hz.1) (by rw [← hpow]; exact hz.2))
      (hn q.2 _ hz.2))
    (fun q q' z h1 h2 => by
      have e1 := hc q.2 q'.2 ((p : ℂ) • z) ((top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      have e2 := hbc q.1 q.2 q'.1 q'.2 (e z)
        (by rw [← hψ]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩)
        (by rw [← hpow]; exact (top_le_preimage_inf _ _ _).2 ⟨h1.2, h2.2⟩)
      rw [hpow] at e1
      rw [hψ, e1]
      linear_combination e2 * fr q'.2 ((p : ℂ) • z))
    (fun q q' z h1 h2 => hc' q.1 q'.1 (h z) ((top_le_preimage_inf _ _ _).2 ⟨h1.1, h2.1⟩))
    (fun q hz => by
      have z1 := hz.1
      have z2 := hz.2
      rw [map_zero] at z1
      rw [smul_zero] at z2
      rw [map_zero, smul_zero, h0' _ z1, h0 _ z2, e0]
      rw [e'0] at z1
      rw [e0] at z2
      exact hb0 q.1 q.2 z1 z2)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm _ _ _ _ _ (ha _ (hpa a haa) q.2 ((p : ℂ) • z)).1
        ((ha _ (hpa a haa) q.2 _).2 hz.2)
      rw [per a haa, smul_add, norm_mul, norm_mul, this]; ring)
    (fun q a haa z hz => by
      have := GlobalTheory.UnitFrameGen.norm_factor Hm' _ _ _ _ _ (ha' _ (hΛΛ' a haa) q.1 (h z)).1
        ((ha' _ (hΛΛ' a haa) q.1 (h z)).2 hz.1)
      rw [hHH, hHH] at this
      rw [map_add, this, hsm, hsm])
  exact key (i, j) w ⟨hi, hj⟩

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InertPlaceStabilizersFixWeilLatticeVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_stabilizers_fix_weil_lattice_vacuum : ∀ D : D7, InertVacuumFixed D := by
  first | exact @GlobalTheory.PlaceTensor.inertVacuumFixed | exact GlobalTheory.PlaceTensor.inertVacuumFixed | (intros; apply GlobalTheory.PlaceTensor.inertVacuumFixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralValuesAlgebraicPointsIffValueNonnegStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.NX (ExpSet CoefLat)
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.Tow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_values_algebraic_points_iff_value_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (la : HeightOneSpectrum (𝓞 c.F)) (f : Rul Xo c), GlobalTheory.GoodPts.BddAll Xo c la 1 f ↔ ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f := by
  first | exact @GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg | exact GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg | (intros; apply GlobalTheory.TowVal.bddAll_one_iff_valSet_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviElementScalesRestrictionNormSqAbsDetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviElement_scales_restrictionNormSq_absDet : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ (h : GA D W) (f : WO V W → ℂ), IsThetaFunO ψ V W f → ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, h) f) x‖ₑ ^ 2 ∂μ' = (GlobalTheory.Doubling.absE D.host.F D.host.E (Matrix.GeneralLinearGroup.det a) : ENNReal) ^ W.rank * ∫⁻ x in 𝓕', ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f x‖ₑ ^ 2 ∂μ' := by
  first | exact @GlobalTheory.LeviNorm.norm_levi | exact GlobalTheory.LeviNorm.norm_levi | (intros; apply GlobalTheory.LeviNorm.norm_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftVectorDatumEqSumLevelClassIndicatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftVectorDatum_eq_sum_levelClassIndicators : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S) (Λ' : Lt D.host.E S.rank), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → IsMov (fmtC S k₀⁻¹) Λ' (stdL D.host.E S.rank) → ∀ Lv : GlobalTheory.SW.Level C.X, Lv.𝔪 = GlobalTheory.LiftLevel.liftI Pg Q → Finite (GlobalTheory.LiftLevel.LvCls C Lv) → (∀ y ∈ tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ), Lv.dat hn y = omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))))) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)))))) → ∀ x, GlobalTheory.LiftLevel.thPDatum S T βS βT Pg Q ξ e x = ∑ᶠ c : GlobalTheory.LiftLevel.LvCls C Lv, Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) * GlobalTheory.LiftLevel.indL (GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e) (x + GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)))) := by
  first | exact @GlobalTheory.LiftLevel.DatSum.thPDatum_eq_levelSum | exact GlobalTheory.LiftLevel.DatSum.thPDatum_eq_levelSum | (intros; apply GlobalTheory.LiftLevel.DatSum.thPDatum_eq_levelSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalIwasawaDecompositionStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_iwasawa_decomposition : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ v (g : GLoc D.sp.cm.sig V.gram v), ∃ p ∈ PLoc Φ.flag0 v, ∃ k ∈ stabLoc D.sp.cm.sig V.gram L v, g = p * k := by
  first | exact @GlobalTheory.IwFinFlag.iwasawa_minPar_fin | exact GlobalTheory.IwFinFlag.iwasawa_minPar_fin | (intros; apply GlobalTheory.IwFinFlag.iwasawa_minPar_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedMulPullbackCommutesBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_mul_pullback_commutes_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} {p : ℕ} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)} {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))}, IsCan χ pm → (∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J) → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∃ s₁' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x₁)), IsMulPull Xo.univ.t.G Xo.univ.t.PP p s' s₁' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s₁' r z J = sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ pm) z J := by
  first | exact @GlobalTheory.HeckeExBC.isMulPull_baseChange | exact GlobalTheory.HeckeExBC.isMulPull_baseChange | (intros; apply GlobalTheory.HeckeExBC.isMulPull_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneSubIdempotentSmulMemCompletionPrimeMulStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_sub_idempotent_smul_mem_completion_prime_mul : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)),
      (1 - finPart D e) • y ∈ GlobalTheory.AdLat.hat D.host.F ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  first | exact @GlobalTheory.ComplOffPlace.one_sub_smul_mem | exact GlobalTheory.ComplOffPlace.one_sub_smul_mem | (intros; apply GlobalTheory.ComplOffPlace.one_sub_smul_mem <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceDiagonalStabilizerGeneratedHermitianDo
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.DblVac

theorem gen_diag_anti_split_herm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ H : Subgroup (GlobalTheory.DblVac.UD σ V),
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PDiag σ V → p ∈ H) →
      (∀ p ∈ GlobalTheory.DblVac.KD σ V v, p ∈ GlobalTheory.DblVac.PAnti σ V → p ∈ H) → ∀ g ∈ GlobalTheory.DblVac.KD σ V v, g ∈ H := by
  intro F E _ _ _ _ _ σ B d V r s hB hV v hv hψ h2 H hD hA g hg
  obtain ⟨Y, hYat, hYlat, hYadm, M, hM, hMlat⟩ := GlobalTheory.T.exists_admissible_unipotent_at_split_place GlobalTheory.T.exists_isUnit_det_add_mul_of_fromBlocks_localRing σ B V r s hB hV v hv hψ h2 g hg
  obtain ⟨p, hpK, hpD, hp⟩ := GlobalTheory.T.exists_unipotent_doubledStabilizer_adds_diagonalBlock σ V v h2 Y hYat hYlat hYadm
  obtain ⟨hpgK, hpg⟩ := hp g hg
  have hbig : GlobalTheory.DblVac.BigCell V v (p * g) := ⟨M, by rw [hpg]; exact hM, hMlat⟩
  obtain ⟨q, hqK, hqA, p', hp'K, hp'D, he⟩ := GlobalTheory.T.doubledVacuumStabilizer_gaussDecomposition_bigCell σ V v h2 (p * g) hpgK hbig
  have hg' : g = p⁻¹ * (q * p') := by rw [← he]; group
  rw [hg']
  exact H.mul_mem (H.inv_mem (hD p hpK hpD)) (H.mul_mem (hA q hqK hqA) (hD p' hp'K hp'D))

end GlobalTheory.DblVac
end
end

