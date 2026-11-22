import Formalism.HermitianCurvature.StatementB
import Formalism.PeriodIntegrals.UpqRep
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0031

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

namespace B2

theorem AB_nonneg (k r : ℕ) : (0 : ℝ) ≤ AB k r := by
  unfold AB
  positivity

theorem aDil_inv (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (aDil k r t)⁻¹ = aDil k r t⁻¹ := by
  have hp : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht
  apply Matrix.inv_eq_left_inv
  unfold aDil
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs with h1 h2
  · rw [← Complex.ofReal_mul, inv_pow, inv_mul_cancel₀ (hp _), Complex.ofReal_one]
  · exact mul_one 1
  · rw [← Complex.ofReal_mul, inv_pow, inv_inv, mul_inv_cancel₀ (hp _), Complex.ofReal_one]

end B2

theorem bessel_lemma_from_reductions : Formalism.FourierDecayAlt.B.LemmaBFromSteps := by
  intro hFC hAe hFat hCC hDil hJ hRB hRA hU hJC hDB hPA hRP hEq hAdj
  unfold StepRegBound StepRegAverage StepUnfold StepJCont StepDilBeta at *
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A hA hInt hConj hDJ hCCI hCoef hXi
  have h0A : 0 ≤ A := (B2.AB_nonneg k r).trans hA
  have h12 := hEq hFC hAe hFat hCC hDil hJ k r Wp Wq D A h0A
    (by apply hRB <;> assumption) (by apply hRA <;> assumption) (by apply hU <;> assumption)
    (by apply hJC <;> assumption) (by apply hDB <;> assumption)
  exact ⟨h12.1, h12.2, hAdj hPA hRP k r Wp Wq D A h12.2⟩

theorem adjointness_of_bessel_transform : Formalism.FourierDecayAlt.B.AssembleAdj := by
  intro hPA hRP k r Wp Wq _ _ _ _ _ _ D A hB2 UU Θ hStab hSm hCom F F' hCk hCk' hS hS' h1 h2 h3 h4 hIC
  have hT : ∀ τ, betaInfTau D τ (opApply Θ F) F' = betaInfTau D τ F (opAdj Θ F') := fun τ =>
    hRP k r Wp Wq D τ _ _ _ _ (hPA k r Wp Wq D UU Θ hStab hSm hCom F F' hCk hCk' hS hS' hIC)
  rw [hB2 _ _ h3 h2, hB2 _ _ h1 h4]
  first
  | (unfold betaInf; simp only [hT])
  | (simp only [betaInf, hT])
  | (unfold betaInf; rw [hT])

theorem adjointness_polynomially_bounded : Formalism.FourierDecayAlt.B.AssemblePoly := by
  intro hSC k r Wp Wq _ _ _ _ _ _ D A hA hCC hB3 Θ ε d hε hd hSm hCom hPoly F F' hF hF' hsF hsF'
  obtain ⟨hStab, hcl⟩ := hSC k r Wp Wq D A hA hCC
  obtain ⟨hs1, hs2, h1, h2, h3, h4, hIC⟩ := hcl Θ ε d hε hd hSm hPoly F F' hF hF' hsF hsF'
  have hCk : ∀ G : Mat k r → (Wq →L[ℂ] Wp), InCC (A + d) (opOrder Θ + 5) G →
      CkOn ((opOrder Θ + 5 : ℕ) : ℕ∞) (GV k r) G := by
    intro G hG
    obtain ⟨c, hc⟩ := hG
    unfold CCle at hc
    first
    | exact hc.1
    | exact hc.2.1
    | exact hc.2.2.1
    | exact hc.1.1
    | exact hc
  exact hB3 (GPos D) Θ hStab hSm hCom F F' (hCk F hF) (hCk F' hF') hs1 hs2 h1 h2 h3 h4 hIC

theorem bessel_function_trivial_index : Formalism.FourierDecayAlt.B.JtauOne := by
  unfold Formalism.FourierDecayAlt.B.JtauOne
  intro k r Wp Wq _ _ _ _ D F g
  unfold Jtau JF xiTau besselJ RealPlaceData.μSS
  unfold rho sgs
  congr 1
  funext p
  congr 1
  unfold psi cStd
  have hs : ∀ z : ℂ, star (Complex.exp z) = Complex.exp ((starRingEnd ℂ) z) :=
    fun z => (Complex.exp_conj z).symm
  rw [hs, ← Complex.exp_add]
  congr 1
  try unfold lam
  dsimp only
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, one_mul]
  try unfold cStd
  ring_nf
  push_cast
  ring

private lemma star_ofReal_eq (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x

theorem dilation_big_cell_formula : Formalism.FourierDecayAlt.B.DilBigCell := by
  unfold Formalism.FourierDecayAlt.B.DilBigCell
  intro k r c μ t₁ t₂ h1 h2
  rw [B2.aDil_inv k r t₁ h1]
  unfold aDil
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  unfold bigCell esI
  beta_reduce
  split_ifs
  all_goals try first
    | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega)
    | rfl
    | (rw [one_mul, mul_one])
    | exact (congrArg (· * (1 : ℂ)) (one_mul _)).trans (mul_one _)
    | (simp; done)
    | (have e : (i : ℕ) - (r + k) = r - (j : ℕ) := by
          (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega
       rw [e]
       try simp only [Fin.val_mk]
       push_cast
       simp only [inv_pow, inv_inv]
       ring)
    | (have e1 : r - (i : ℕ) = (j : ℕ) - (r + k) := by
          (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega
       have e2 : r - (2 * r + k - (j : ℕ)) = (j : ℕ) - (r + k) := by omega
       simp only [Fin.val_mk, e1, e2, star_mul', star_ofReal_eq]
       push_cast
       ring)

private lemma star_ofReal_eq_self (x : ℝ) : star (x : ℂ) = x := Complex.conj_ofReal x

theorem dilation_mem_group : Formalism.FourierDecayAlt.B.DilMem := by
  unfold Formalism.FourierDecayAlt.B.DilMem
  intro k r t ht
  have hp : ∀ n : ℕ, t ^ n ≠ 0 := fun n => pow_ne_zero n ht
  unfold GV UH aDil
  rw [Set.mem_setOf_eq, Matrix.diagonal_conjTranspose]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  unfold Hpk
  beta_reduce
  split_ifs
  all_goals (try simp only [star_ofReal_eq_self, star_one, mul_one, one_mul, mul_zero, zero_mul, mul_neg])
  all_goals try first
    | rfl
    | (exfalso; (try simp only [Fin.ext_iff, Fin.val_mk] at *); omega)
    | (rw [show (j : ℕ) - (r + k) = r - (i : ℕ) by omega, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (hp _), Complex.ofReal_one])
    | (rw [show (i : ℕ) - (r + k) = r - (j : ℕ) by omega, ← Complex.ofReal_mul,
          inv_mul_cancel₀ (hp _), Complex.ofReal_one])

theorem bessel_lemma_closed_form : Formalism.FourierDecayAlt.B.LemmaBClosedFromParts := by
  intro hXi hLB hSC hAP k r Wp Wq _ _ _ _ _ _ D A hA hInt hConj hDJ hCCI
  obtain ⟨Ξ, hCB, hXI⟩ := hXi k r Wp Wq D A hA
  have h0A : 0 ≤ A := (B2.AB_nonneg k r).trans hA
  obtain ⟨h1, h2, h3⟩ := hLB k r Wp Wq D Ξ A hA hInt hConj hDJ hCCI hCB hXI
  exact ⟨h1, h2, h3, hAP hSC k r Wp Wq D A h0A hCCI h3⟩

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimBdPfKFin
section
namespace Formalism.FourierDecayAlt.P.CutBP

noncomputable section

def KFinDSCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ : B.Mat k r → (H →L[ℂ] H)) (Pm : H →L[ℂ] Wp) (Qm : Wq →L[ℂ] H),
    PI.UpqRep.IsHCParam lam ∧ PI.UpqRep.IsDSHpk k r ε lam σ ∧
    (∀ w, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (Qm w)) ∧
    (∀ x, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (ContinuousLinearMap.adjoint Pm x)) ∧
    ∀ g ∈ B.GV k r, F g = Pm.comp ((σ g).comp Qm)

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsSmoothExt
section
open Matrix Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem isClosed_GVt (k r : ℕ) : IsClosed {x : Mt k r | Matrix.of x ∈ B.GV k r} := by
  have h0 : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have hc : Continuous (fun x : Mt k r => (Matrix.of x)ᴴ * Hpk k r * Matrix.of x) :=
    ((h0.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul h0
  exact isClosed_eq hc continuous_const

theorem exists_smoothExt {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : B.Mat k r → E) (hF : B.CkOn (⊤ : ℕ∞) (B.GV k r) F) :
    ∃ Ft : Mt k r → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ft ∧
      ∀ x : Mt k r, Matrix.of x ∈ B.GV k r → Ft x = F (Matrix.of x) := by
  set s : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ B.GV k r} with hs
  have hloc : ∀ i : s, ∃ (U : Set (Mt k r)) (f' : Mt k r → E), IsOpen U ∧ (i : Mt k r) ∈ U ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f' U ∧ ∀ x ∈ U, Matrix.of x ∈ B.GV k r → F (Matrix.of x) = f' x := by
    intro i
    obtain ⟨U, f', hU, hiU, hf', hfe⟩ := hF (Matrix.of (i : Mt k r)) i.2
    exact ⟨U, f', hU, hiU, hf', fun x hx hxG => hfe (Matrix.of x) hx hxG⟩
  choose U f' hU hiU hf' hfe using hloc
  have hcov : s ⊆ ⋃ i : s, U i := fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hiU ⟨x, hx⟩⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Mt k r) (isClosed_GVt k r) U hU hcov
  refine ⟨fun x => ∑ᶠ i, ρ i x • f' i x, ?_, ?_⟩
  · have h := ρ.contMDiff_finsum_smul (n := (⊤ : ℕ∞)) (g := f') fun i x hx => by
      have hxU : x ∈ U i := hρ i hx
      exact ((hf' i).contDiffAt ((hU i).mem_nhds hxU)).contMDiffAt
    exact contMDiff_iff_contDiff.1 h
  · intro x hx
    have hsum : ∑ᶠ i, ρ i x = 1 := ρ.sum_eq_one hx
    have heq : ∀ i, ρ i x • f' i x = ρ i x • F (Matrix.of x) := by
      intro i
      by_cases h0 : ρ i x = 0
      · simp [h0]
      · have hxU : x ∈ U i := hρ i (subset_tsupport _ h0)
        rw [hfe i x hxU hx]
    simp only [heq]
    rw [← finsum_smul, hsum, one_smul]

end Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FreeActionExpansion
section
namespace Formalism.FourierDecayAlt.P.FreeActionExpansion

open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.CoordinateFlipUpdateSums
open scoped Matrix

section Ops

variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]

theorem J_lift : (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A)) = lift0 (Formalism.YangianSpanCharacter.T.J A) := by
  have h0 : (io (0 : A) : SlopeTestRemainingChoices S A) = 0 := map_zero (Matrix.scalar (Ix S))
  have h1 : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := map_one (Matrix.scalar (Ix S))
  have hn : (io (-1 : A) : SlopeTestRemainingChoices S A) = -1 := by
    rw [show (io (-1 : A) : SlopeTestRemainingChoices S A) = Matrix.scalar (Ix S) (-1 : A) from rfl, map_neg, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, lift0, h0, h1, hn]

theorem comm_io_alg (C : SlopeTestRemainingChoices S A) (c : ℂ) : Commute C (io (algebraMap ℂ A c)) := by
  refine Matrix.ext fun z z' => ?_
  simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact (Algebra.commutes c (C z z')).symm

theorem uinv_alg (s : ℂ) (i j : Fin 2) :
    ∃ c : ℂ, (Formalism.YangianSpanCharacter.T.Uinv (A := A) s) i j = algebraMap ℂ A c := by
  fin_cases i <;> fin_cases j
  · exact ⟨1, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩
  · exact ⟨0, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩
  · exact ⟨s, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩
  · exact ⟨1, by simp [Formalism.YangianSpanCharacter.T.Uinv]⟩

theorem comm_ins_uinv {a : S} {C : SlopeTestRemainingChoices S A} (hC : FreeOf a C) (s : ℂ) :
    Commute C (ins a (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A := A) s))) := by
  refine Formalism.FourierDecayAlt.P.Wd1.ins_comm a _ C hC fun i j => ?_
  obtain ⟨c, hc⟩ := uinv_alg (A := A) s i j
  simp only [lift0, Matrix.map_apply, hc]
  exact comm_io_alg C c

theorem freeOf_one (a : S) : FreeOf a (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

theorem freeOf_JL (a : S) : ∀ L : List (Letter ℂ S), (∀ l ∈ L, l.plus = true) →
    a ∉ L.map Letter.intersection_update_fsHerm_neg_one → FreeOf a (JL L : SlopeTestRemainingChoices S A) := by
  intro L
  induction L with
  | nil => intro _ _; exact freeOf_one a
  | cons l L ih =>
    intro hL ha
    rw [List.map_cons, List.mem_cons, not_or] at ha
    have hpl : l.plus = true := hL l (by simp)
    simp only [JL, hpl, if_true, J_lift]
    refine freeOf_mul (Formalism.FourierDecayAlt.P.Wd1.ins_free ha.1 _ fun i j => freeOf_io a _) (ih ?_ ha.2)
    exact fun l' h => hL l' (by simp [h])

theorem freeOf_UUiw (a : S) (s : ℂ) : ∀ L : List (Letter ℂ S),
    a ∉ L.map Letter.intersection_update_fsHerm_neg_one → FreeOf a (UUiw s L : SlopeTestRemainingChoices S A) := by
  intro L
  induction L with
  | nil => intro _; exact freeOf_one a
  | cons l L ih =>
    intro ha
    rw [List.map_cons, List.mem_cons, not_or] at ha
    simp only [UUiw]
    exact freeOf_mul (Formalism.FourierDecayAlt.P.Wd1.ins_free ha.1 _ fun i j => freeOf_io a _) (ih ha.2)

end Ops

section Vec

variable {A S V : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S] [AddCommGroup V]
  [Module A V]

theorem act_ins (a : S) (M : M2 A) (Ψ : Ix S → V) (z : Ix S) :
    act (ins a (lift0 M)) Ψ z = ∑ j, M (z a) j • Ψ (Function.update z a j) := by
  have h : ∀ z', (ins a (lift0 M) : SlopeTestRemainingChoices S A) z z' =
      ∑ j, if z' = Function.update z a j then M (z a) j else 0 := by
    intro z'
    unfold ins lift0
    simp only [Matrix.sum_apply, Matrix.map_apply]
    have hm : ∀ i j, (((eU a i j : SlopeTestRemainingChoices S A) * (io (M i j) : SlopeTestRemainingChoices S A) : SlopeTestRemainingChoices S A)) z z' =
        if z a = i ∧ z' = Function.update z a j then M i j else 0 := by
      intro i j
      simp only [io, Matrix.scalar_apply, Matrix.mul_diagonal, Formalism.FourierDecayAlt.P.Wd1.eU_apply, ite_mul,
        one_mul, zero_mul]
    simp only [hm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (z a)]
    · simp
    · intro i _ hi; simp [Ne.symm hi]
    · simp
  unfold act
  simp only [h, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem letters_zero (P Q : A[X]) (a : S) (x : Ix S → V) (hx : ∀ u, u a ≠ 0 → x u = 0) :
    ∀ L : List (Letter ℂ S), a ∉ L.map Letter.intersection_update_fsHerm_neg_one → ∀ u, u a ≠ 0 → letters P Q L x u = 0 := by
  intro L
  induction L with
  | nil => intro _ u hu; exact hx u hu
  | cons l L ih =>
    intro ha u hu
    rw [List.map_cons, List.mem_cons, not_or] at ha
    simp only [letters, placeV]
    rw [ih ha.2 _ (by rw [Function.update_of_ne ha.1]; exact hu), smul_zero]

end Vec

section Main

variable {A S V : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S]
  [DecidableEq S] [AddCommGroup V] [Module ℂ V] [Module A V] [IsScalarTower ℂ A V]

theorem pair_eq_sum_split_coord (a : S) (ρ : Rep A V) (Ψ Ψ' : Ix S → V) :
    pair ρ Ψ Ψ' = ∑ u, if u a = 0 then ρ.β (Ψ u) (Ψ' u) +
      ρ.β (Ψ (Function.update u a 1)) (Ψ' (Function.update u a 1)) else 0 :=
  sum_position a (fun u => ρ.β (Ψ u) (Ψ' u))

theorem act_lin (G : SlopeTestRemainingChoices S A) (X : Ix S → V) (P b c : A) (s : ℂ) :
    act G ((P * (b + algebraMap ℂ A s * c)) • X) = act G ((P * b) • X) + s • act G ((P * c) • X) := by
  have e : (P * (b + algebraMap ℂ A s * c)) • X = (P * b) • X + s • ((P * c) • X) := by
    rw [mul_add, add_smul, ← mul_assoc P (algebraMap ℂ A s) c, ← Algebra.commutes s P, mul_assoc,
      mul_smul (algebraMap ℂ A s) (P * c) X, algebraMap_smul]
  rw [e, act_add, act_smul]

theorem expand (ρ : Rep A V) (QQ : ℂ → M2 A) (f : A) (s : ℂ) (w : List (Letter ℂ S))
    (vA vB vAv vBv : A[X]) (x : Ix S → V) (Ξ : F7.Sesq (Ix S → V))
    (hΞ : ∀ X X', Ξ X X' = frm ρ (RRw QQ w * Vw f s w) X X') (hx : SupportedOnUsedSlots w x) :
    ∀ L : List (Letter ℂ S), (∀ l ∈ L, l.plus = true ∧ l.pt.im = 0) → (L.map Letter.intersection_update_fsHerm_neg_one).Nodup →
      (∀ l ∈ L, l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one) → ∀ P P' : A,
      pair ρ (act (JL L * RRw QQ w * Vw f s (L ++ w)) (P • letters vA vB L x))
          (P' • letters vAv vBv (L.map dl) x) =
        F7.Fw Ξ x x (L.map fun l => ((⟨vA, vB, vAv, vBv, s⟩ : F7.Dat A), l.pt.re)) P P' := by
  intro L
  induction L with
  | nil =>
    intro _ _ _ P P'
    simp only [JL, one_mul, List.nil_append, letters, List.map_nil, F7.Fw, hΞ, frm]
  | cons l L ih =>
    intro hL hnd hw P P'
    obtain ⟨hpl, him⟩ := hL l (by simp)
    have hL' : ∀ l' ∈ L, l'.plus = true ∧ l'.pt.im = 0 := fun l' h => hL l' (by simp [h])
    rw [List.map_cons, List.nodup_cons] at hnd
    have hw' : ∀ l' ∈ L, l'.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one := fun l' h => hw l' (by simp [h])
    have haw : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one := hw l (by simp)
    have haL : l.intersection_update_fsHerm_neg_one ∉ L.map Letter.intersection_update_fsHerm_neg_one := hnd.1
    have hpt : l.pt = (l.pt.re : ℂ) := Complex.ext (by simp) (by simp [him])

    have hJL := freeOf_JL (A := A) l.intersection_update_fsHerm_neg_one L (fun l' h => (hL' l' h).1) haL
    have hRR := (Formalism.FourierDecayAlt.P.word_free_of_unused_positions ℂ A S QQ w l.intersection_update_fsHerm_neg_one haw).1
    have hUU := freeOf_UUiw (A := A) l.intersection_update_fsHerm_neg_one s (L ++ w) (by
      rw [List.map_append, List.mem_append, not_or]; exact ⟨haL, haw⟩)
    have hC : FreeOf l.intersection_update_fsHerm_neg_one (JL L * RRw QQ w * io f : SlopeTestRemainingChoices S A) :=
      freeOf_mul (freeOf_mul hJL hRR) (freeOf_io l.intersection_update_fsHerm_neg_one f)
    have hG : FreeOf l.intersection_update_fsHerm_neg_one (JL L * RRw QQ w * Vw f s (L ++ w) : SlopeTestRemainingChoices S A) := by
      unfold Vw; exact freeOf_mul (freeOf_mul hJL hRR) (freeOf_mul (freeOf_io l.intersection_update_fsHerm_neg_one f) hUU)
    have hop : JL (l :: L) * RRw QQ w * Vw f s ((l :: L) ++ w) =
        ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A)) * (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A := A) s)) *
          (JL L * RRw QQ w * Vw f s (L ++ w))) := by
      have hc := (comm_ins_uinv hC s).eq
      simp only [JL, hpl, if_true, J_lift, Vw, List.cons_append, UUiw]
      calc ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A)) * JL L * RRw QQ w *
            (io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv s)) * UUiw s (L ++ w)))
          = ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A)) * ((JL L * RRw QQ w * io f) *
              ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv s)) * UUiw s (L ++ w)) := by simp only [mul_assoc]
        _ = ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A)) * (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv s)) *
              (JL L * RRw QQ w * io f) * UUiw s (L ++ w)) := by rw [hc]
        _ = _ := by simp only [mul_assoc]
    rw [hop, act_mul, act_mul]

    have hx0 : ∀ u, u l.intersection_update_fsHerm_neg_one ≠ 0 → x u = 0 := fun u hu => hx u ⟨l.intersection_update_fsHerm_neg_one, haw, hu⟩
    have hX := letters_zero vA vB l.intersection_update_fsHerm_neg_one x hx0 L haL
    have hX' := letters_zero vAv vBv l.intersection_update_fsHerm_neg_one x hx0 (L.map dl) (by
      rwa [List.map_map, show (Letter.intersection_update_fsHerm_neg_one ∘ dl : Letter ℂ S → S) = Letter.intersection_update_fsHerm_neg_one from
        funext fun l' => by by_cases h : l'.plus <;> simp [dl, h]])
    have hdl : dl l = ⟨false, l.intersection_update_fsHerm_neg_one, l.pt + 1⟩ := by simp [dl, hpl]
    have hΦ : P • letters vA vB (l :: L) x = fun u =>
        (fun i : Fin 2 => P * (if i = 0 then evC vA l.pt else evC vB l.pt)) (u l.intersection_update_fsHerm_neg_one) •
          letters vA vB L x (Function.update u l.intersection_update_fsHerm_neg_one 0) := by
      funext u
      simp only [letters, placeV, Pi.smul_apply, mul_smul]
    have hΦ' : P' • letters vAv vBv ((l :: L).map dl) x = fun u =>
        (P' * (if u l.intersection_update_fsHerm_neg_one = 0 then evC vAv (l.pt + 1) else evC vBv (l.pt + 1))) •
          letters vAv vBv (L.map dl) x (Function.update u l.intersection_update_fsHerm_neg_one 0) := by
      funext u
      simp only [List.map_cons, letters, hdl, placeV, Pi.smul_apply, mul_smul]
    rw [hΦ, hΦ']
    set X := letters vA vB L x with hXdef
    set X' := letters vAv vBv (L.map dl) x with hX'def
    set G := JL L * RRw QQ w * Vw f s (L ++ w) with hGdef
    set C : Fin 2 → A := fun i => P * (if i = 0 then evC vA l.pt else evC vB l.pt) with hCdef
    have h1 : act G (fun u => C (u l.intersection_update_fsHerm_neg_one) • X (Function.update u l.intersection_update_fsHerm_neg_one 0)) =
        fun z => act G (C (z l.intersection_update_fsHerm_neg_one) • X) (Function.update z l.intersection_update_fsHerm_neg_one 0) := funext (act_place hG X hX C)
    rw [h1]
    have hv0 : ∀ u, u l.intersection_update_fsHerm_neg_one = 0 →
        act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A))) (act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A := A) s)))
          (fun z => act G (C (z l.intersection_update_fsHerm_neg_one) • X) (Function.update z l.intersection_update_fsHerm_neg_one 0))) u =
        s • act G (C 0 • X) u + act G (C 1 • X) u := by
      intro u hu
      rw [act_ins, Fin.sum_univ_two, act_ins, act_ins]
      simp [hu, Formalism.YangianSpanCharacter.T.J, Formalism.YangianSpanCharacter.T.Uinv, Fin.sum_univ_two, update_zero_of _ u hu, algebraMap_smul]
    have hv1 : ∀ u, u l.intersection_update_fsHerm_neg_one = 0 →
        act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.J A))) (act (ins l.intersection_update_fsHerm_neg_one (lift0 (Formalism.YangianSpanCharacter.T.Uinv (A := A) s)))
          (fun z => act G (C (z l.intersection_update_fsHerm_neg_one) • X) (Function.update z l.intersection_update_fsHerm_neg_one 0))) (Function.update u l.intersection_update_fsHerm_neg_one 1) =
        -act G (C 0 • X) u := by
      intro u hu
      rw [act_ins, Fin.sum_univ_two, act_ins, act_ins]
      simp [hu, Formalism.YangianSpanCharacter.T.J, Formalism.YangianSpanCharacter.T.Uinv, Fin.sum_univ_two, update_zero_of _ u hu]
    have eA : F7.evR vA l.pt.re = evC vA l.pt := by unfold F7.evR evC; rw [← hpt]
    have eB : F7.evR vB l.pt.re = evC vB l.pt := by unfold F7.evR evC; rw [← hpt]
    have eAv : F7.evR vAv (l.pt.re + 1) = evC vAv (l.pt + 1) := by
      unfold F7.evR evC; rw [Complex.ofReal_add, Complex.ofReal_one, ← hpt]
    have eBv : F7.evR vBv (l.pt.re + 1) = evC vBv (l.pt + 1) := by
      unfold F7.evR evC; rw [Complex.ofReal_add, Complex.ofReal_one, ← hpt]
    simp only [List.map_cons, F7.Fw]
    rw [← ih hL' hnd.2 hw', ← ih hL' hnd.2 hw', eA, eB, eAv, eBv, act_lin]
    rw [pair_eq_sum_split_coord l.intersection_update_fsHerm_neg_one, pair_eq_sum_split_coord l.intersection_update_fsHerm_neg_one, pair_eq_sum_split_coord l.intersection_update_fsHerm_neg_one, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u l.intersection_update_fsHerm_neg_one = 0
    · rw [if_pos hu, if_pos hu, if_pos hu, hv0 u hu, hv1 u hu]
      have hX'1 : X' (Function.update u l.intersection_update_fsHerm_neg_one 1) = 0 := hX' _ (by simp)
      simp only [Pi.smul_apply, hX'1, smul_zero, map_zero, add_zero, Function.update_self,
        Function.update_idem, update_zero_of _ u hu, hu, if_true, hCdef]
      simp only [show ((1 : Fin 2) = 0) = False from by decide, if_false, Pi.add_apply, Pi.smul_apply, map_add, map_neg,
        map_smul, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    · rw [if_neg hu, if_neg hu, if_neg hu, sub_zero]

end Main

end Formalism.FourierDecayAlt.P.FreeActionExpansion
end

