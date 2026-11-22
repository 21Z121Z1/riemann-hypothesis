import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0179
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
section
noncomputable section

namespace GlobalTheory.Core.Rk.FockBox

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (resL resR)
open GlobalTheory.OrientedHeis

theorem killed_of_leibniz {P Q U V : Type} [Zero U] [AddCommGroup V] (a : P → U → U) (b : Q → V → V) (TU : U → Prop)
    (TV : V → Prop) (δ : U → U → V) (c₁ c₂ : Q → P) (ha : ∀ p f, TU f → TU (a p f)) (hb : ∀ q f, TV f → TV (b q f))
    (hadd : ∀ q f g, TV f → TV g → b q (f + g) = b q f + b q g) (hb0 : ∀ q, b q 0 = 0)
    (hδ : ∀ f g, TU f → TU g → TV (δ f g)) (h1 : ∀ g, δ 0 g = 0) (h2 : ∀ f, δ f 0 = 0)
    (hL : ∀ q f g, TU f → TU g → b q (δ f g) = δ (a (c₁ q) f) g + δ f (a (c₂ q) g)) (N : ℕ) :
    ∀ (N₁ N₂ : ℕ) (f g : U), N₁ + N₂ ≤ N → TU f → TU g →
      (∀ l : List P, l.length = N₁ → l.foldr a f = 0) → (∀ l : List P, l.length = N₂ → l.foldr a g = 0) →
      ∀ l : List Q, l.length = N → l.foldr b (δ f g) = 0 := by
  have w0 : ∀ l : List Q, l.foldr b 0 = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hb0]
  have wT : ∀ (l : List Q) f, TV f → TV (l.foldr b f) := fun l f hf => by
    induction l with
    | nil => exact hf
    | cons q l ih => exact hb _ _ ih
  have wadd : ∀ (l : List Q) f g, TV f → TV g → l.foldr b (f + g) = l.foldr b f + l.foldr b g := fun l f g hf hg => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hadd _ _ _ (wT l f hf) (wT l g hg)]; rfl
  have step : ∀ (M : ℕ) (f : U) (p : P), (∀ l : List P, l.length = M + 1 → l.foldr a f = 0) →
      ∀ l : List P, l.length = M → l.foldr a (a p f) = 0 := fun M f p h l hl => by
    have := h (l ++ [p]) (by simp [hl])
    rwa [List.foldr_append] at this
  induction N with
  | zero =>
    intro N₁ N₂ f g hN _ _ k₁ _ l _
    have : f = 0 := k₁ [] (by simp; omega)
    rw [this, h1, w0]
  | succ N ih =>
    intro N₁ N₂ f g hN hf hg k₁ k₂ l hl
    rcases N₁ with _ | M₁
    · have : f = 0 := k₁ [] rfl
      rw [this, h1, w0]
    rcases N₂ with _ | M₂
    · have : g = 0 := k₂ [] rfl
      rw [this, h2, w0]
    obtain rfl | ⟨l', q, rfl⟩ := l.eq_nil_or_concat'
    · simp at hl
    have hl' : l'.length = N := by simpa using hl
    rw [List.foldr_append, List.foldr_cons, List.foldr_nil, hL q f g hf hg,
      wadd _ _ _ (hδ _ _ (ha _ _ hf) hg) (hδ _ _ hf (ha _ _ hg)),
      ih M₁ (M₂ + 1) _ _ (by omega) (ha _ _ hf) hg (step _ _ _ k₁) k₂ l' hl',
      ih (M₁ + 1) M₂ _ _ (by omega) hf (ha _ _ hg) k₁ (step _ _ _ k₂) l' hl', add_zero]

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}

theorem lineAt_neg (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ) :
    lineAt θ τ (-z) = -lineAt θ τ z := by
  have hL := isLineAt_lineAt hθ τ z
  refine GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) ⟨?_, fun t => ?_, fun t τ' => ?_⟩
  · have e : ⇑(-lineAt θ τ z) = fun t => lineAt θ τ z (-t) := by
      funext t; rw [AddMonoidHom.neg_apply, map_neg]
    rw [e]
    exact hL.1.comp continuous_neg
  · rw [AddMonoidHom.neg_apply, ← map_neg]
    exact hL.2.1 _
  · rw [AddMonoidHom.neg_apply, ← map_neg, hL.2.2]
    simp

theorem lineAt_col (hθ : IsInfFam θ) {m n k : ℕ} (c : Fin k → Fin n) (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) : lineAt θ τ (z.submatrix id c) t = (lineAt θ τ z t).submatrix id c := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ Mx D m k :=
    { toFun := fun t => (lineAt θ τ z t).submatrix id c
      map_zero' := by rw [map_zero]; rfl
      map_add' := fun s t => by rw [map_add]; rfl }
  have hL' : IsLineAt θ τ (z.submatrix id c) L := by
    refine ⟨continuous_matrix fun i j => hL.1.matrix_elem i (c j), fun t => ?_, fun t τ' => ?_⟩
    · exact congrArg (fun x => Matrix.submatrix x id c) (hL.2.1 t)
    · refine (congrArg (fun x => Matrix.submatrix x id c) (hL.2.2 t τ')).trans ?_
      split_ifs <;> rfl
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

section One

variable {S T : HSp D}

theorem hasDerivAt_dRho (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S T) :
    HasDerivAt (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) f w) (dRho (heisO ψ S T) θ τ z f w) 0 :=
  (hasDerivAt_heisO hθ hψ (isRealDir_lineAt hθ τ z) hf w 0).differentiableAt.hasDerivAt

theorem dRho_add (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
    dRho (heisO ψ S T) θ τ z (f + g) = dRho (heisO ψ S T) θ τ z f + dRho (heisO ψ S T) θ τ z g := by
  funext w
  have := (hasDerivAt_dRho hθ hψ τ z hf w).add (hasDerivAt_dRho hθ hψ τ z hg w)
  refine Eq.trans ?_ this.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  simp only [heisO, Pi.add_apply, mul_add]

theorem dRho_neg (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ S T) θ τ (-z) f = -dRho (heisO ψ S T) θ τ z f := by
  funext w
  have := deriv_comp_neg (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) f w) 0
  rw [neg_zero] at this
  refine Eq.trans ?_ this
  unfold Formalism.IndefR.Datum.dRho
  simp only [lineAt_neg hθ, AddMonoidHom.neg_apply, map_neg]

end One

variable {A B : HSp D}

theorem symplOH_dbl (x y : WO (dblSp A) B) : symplOH (dblSp A) B x y =
    symplOH A B (resL A B x) (resL A B y) - symplOH A B (-resR A B x) (-resR A B y) := by
  have hu : IsUnit A.gram.det := (isHermND_gram A).2.isUnit
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_right_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.mul_nonsing_inv _ hu, blkMat_one])
  have h : hO (dblSp A) B x y = hO A B (resL A B x) (resL A B y) - hO A B (-resR A B x) (-resR A B y) := by
    simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, resL, resR, Matrix.of_apply,
      blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
      map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [symplOH, symplO, h, mul_sub, map_sub]

theorem heisO_delta (hψ : IsStdChar D ψ (-1)) (u : WO (dblSp A) B) (f₁ f₂ : WO A B → ℂ) :
    heisO ψ (dblSp A) B u (delta A B f₁ f₂) =
      delta A B (heisO ψ A B (resL A B u) f₁) (heisO ψ A B (-resR A B u) f₂) := by
  funext x
  have e₁ : resL A B (x + u) = resL A B x + resL A B u := rfl
  have e₂ : -resR A B (x + u) = -resR A B x + -resR A B u := by
    rw [← neg_add]; rfl
  have e₃ : ∀ a, ψ (-a) = conj (ψ a) := fun a => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.1.2.1 a)]
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, symplOH_dbl, e₁, e₂, sub_eq_add_neg, AddChar.map_add_eq_mul, e₃, map_mul]
  ring

abbrev colL (A : HSp D) : Fin A.rank → Fin (dblSp A).rank := fun j => finSumFinEquiv (Sum.inl j)

abbrev colR (A : HSp D) : Fin A.rank → Fin (dblSp A).rank := fun j => finSumFinEquiv (Sum.inr j)

theorem dRho_delta (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) {f₁ f₂ : WO A B → ℂ} (h₁ : IsThetaFunO ψ A B f₁)
    (h₂ : IsThetaFunO ψ A B f₂) :
    dRho (heisO ψ (dblSp A) B) θ τ z (delta A B f₁ f₂) =
      delta A B (dRho (heisO ψ A B) θ τ (z.submatrix id (colL A)) f₁) f₂ +
        delta A B f₁ (dRho (heisO ψ A B) θ τ (-z.submatrix id (colR A)) f₂) := by
  funext x
  have d := (hasDerivAt_dRho hθ hψ τ (z.submatrix id (colL A)) h₁ (resL A B x)).mul
    (hasDerivAt_dRho hθ hψ τ (-z.submatrix id (colR A)) h₂ (-resR A B x)).star
  simp only [map_zero, heisO_zero] at d
  refine Eq.trans ?_ d.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [heisO_delta hψ]
  simp only [Pi.mul_apply, lineAt_neg hθ, AddMonoidHom.neg_apply, lineAt_col hθ]
  rfl

theorem cplxO_colL (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (s' : Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) :
    (cplxO (n := (dblSp A).rank) ((Matrix.fromBlocks s 0 0 (-s)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) s' z).submatrix
      id (colL A) = cplxO s s' (z.submatrix id (colL A)) := by
  ext i j
  simp only [cplxO, Matrix.submatrix_apply, Matrix.smul_apply, id]
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  erw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.mul_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem cplxO_colR (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (s' : Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) :
    (cplxO (n := (dblSp A).rank) ((Matrix.fromBlocks s 0 0 (-s)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) s' z).submatrix
      id (colR A) = cplxO s s' (-z.submatrix id (colR A)) := by
  ext i j
  simp only [cplxO, Matrix.submatrix_apply, Matrix.smul_apply, id]
  congr 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  erw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.mul_apply, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]

theorem annih_delta (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (s' : Matrix (Fin B.rank) (Fin B.rank) ℂ)
    (z : Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ) {f₁ f₂ : WO A B → ℂ} (h₁ : IsThetaFunO ψ A B f₁)
    (h₂ : IsThetaFunO ψ A B f₂) :
    annih (heisO ψ (dblSp A) B) θ τ (cplxO (n := (dblSp A).rank)
        ((Matrix.fromBlocks s 0 0 (-s)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) s') z (delta A B f₁ f₂) =
      delta A B (annih (heisO ψ A B) θ τ (cplxO s s') (z.submatrix id (colL A)) f₁) f₂ +
        delta A B f₁ (annih (heisO ψ A B) θ τ (cplxO s s') (-z.submatrix id (colR A)) f₂) := by
  unfold annih
  rw [dRho_delta hθ hψ τ _ h₁ h₂, dRho_delta hθ hψ τ _ h₁ h₂, cplxO_colL, cplxO_colR, dRho_neg hθ τ (cplxO _ _ _)]
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, map_add, map_mul, map_neg, Complex.conj_I]
  ring

theorem isFockVec_delta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (sA : RealMat A) (sB : RealMat B), IsStdChar D ψ (-1) → IsInfFam θ → ∀ Φ₁ Φ₂, IsFockVec ψ θ A B sA sB Φ₁ → IsFockVec ψ θ A B sA sB Φ₂ → IsFockVec ψ θ (dblSp A) B (fun τ => (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) sB (delta A B Φ₁ Φ₂) := by
  intro D ψ θ A B sA sB hψ hθ Φ₁ Φ₂ ⟨t₁, N₁, k₁⟩ ⟨t₂, N₂, k₂⟩
  have hT : ∀ (S : HSp D) τ J z f, IsThetaFunO ψ S B f → IsThetaFunO ψ S B (annih (heisO ψ S B) θ τ J z f) :=
    fun S τ J z f hf => theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ _ hf))
  refine ⟨GlobalTheory.T.isThetaFunction_doublingSeesaw_of_standard_char D ψ A B hψ _ _ t₁ t₂, N₁ + N₂, ?_⟩
  refine killed_of_leibniz (P := D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (Q := D.what₂.Tau × Matrix (Fin B.rank) (Fin (dblSp A).rank) ℂ)
    (fun p f => annih (heisO ψ A B) θ p.1 (cplxO (sA p.1) (sB p.1)) p.2 f)
    (fun p f => annih (heisO ψ (dblSp A) B) θ p.1 (cplxO (n := (dblSp A).rank)
      ((Matrix.fromBlocks (sA p.1) 0 0 (-sA p.1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) (sB p.1)) p.2 f)
    (IsThetaFunO ψ A B) (IsThetaFunO ψ (dblSp A) B) (delta A B)
    (fun q => (q.1, q.2.submatrix id (colL A))) (fun q => (q.1, -q.2.submatrix id (colR A)))
    (fun p f hf => hT A _ _ _ f hf) (fun p f hf => hT _ _ _ _ f hf) (fun q f g hf hg => ?_) (fun q => ?_)
    (GlobalTheory.T.isThetaFunction_doublingSeesaw_of_standard_char D ψ A B hψ) (fun g => ?_) (fun f => ?_) (fun q f g hf hg => annih_delta hθ hψ q.1 (sA q.1) (sB q.1) q.2 hf hg)
    _ N₁ N₂ Φ₁ Φ₂ le_rfl t₁ t₂ k₁ k₂
  · simp only [annih]
    rw [dRho_add hθ hψ _ _ hf hg, dRho_add hθ hψ _ _ hf hg, smul_add]
    abel
  · funext x
    simp [annih, Formalism.IndefR.Datum.dRho, heisO]
  · funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta]
  · funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta]

end GlobalTheory.Core.Rk.FockBox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartsAtTwistPlacesChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.TwistChart

variable {D : D7}

theorem isIdemOf_idem {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) :
    IsIdemOf φ (GlobalTheory.EmbChart.idem (GlobalTheory.SplitProjChart.emb φ)) := by
  refine ⟨GlobalTheory.EmbChart.isSplitIdem_idem _, ?_, GlobalTheory.SplitProjChart.rdA_idem φ⟩
  rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add, add_sub_cancel]
  rfl

theorem exists_unif (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ ϖ : (Fv D.host.F v)ˣ, ValuativeRel.valuation (Fv D.host.F v) (ϖ : Fv D.host.F v) =
      ValuativeRel.uniformizer (Fv D.host.F v) := by
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (Fv D.host.F v))
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at hx
    exact ValuativeRel.uniformizer_ne_zero hx.symm
  exact ⟨Units.mk0 x hx0, hx⟩

theorem unit_section {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) :
    ∃ U : (Fv D.host.F v)ˣ →* (AE D)ˣ, (∀ y, (1 - e) * (U y : AE D) = 1 - e ∧ rdA φ (U y : AE D) = y) ∧
      ∀ (x : AE D) (y : (Fv D.host.F v)ˣ), (1 - e) * x = 1 - e → rdA φ x = y → x = U y := by
  have hπ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hee : e * e = e := he.1.1
  obtain ⟨sec, hsec⟩ : ∃ sec : Fv D.host.F v → AE D, ∀ y, rdA φ (sec y) = y :=
    ⟨fun y => (hπ.1 y).choose, fun y => (hπ.1 y).choose_spec⟩
  have hf1 : ∀ y, (1 - e) * ((1 - e) + e * sec y) = 1 - e := fun y => by
    linear_combination (1 - sec y) * hee
  have hf2 : ∀ y, rdA φ ((1 - e) + e * sec y) = y := fun y => by
    rw [map_add, map_sub, map_mul, map_one, he.2.2, hsec]; ring
  have key : ∀ x y, (1 - e) * x = 1 - e → rdA φ x = y → x = (1 - e) + e * sec y := by
    intro x y h1 h2
    have h3 : e * (x - sec y) = 0 := (hπ.2.1 _).1 (by rw [map_sub, h2, hsec, sub_self])
    have h4 : e * x = e * sec y := by rw [mul_sub] at h3; exact sub_eq_zero.1 h3
    calc x = (1 - e) * x + e * x := by ring
      _ = (1 - e) + e * sec y := by rw [h1, h4]
  have hmul : ∀ y z, (1 - e) + e * sec (y * z) = ((1 - e) + e * sec y) * ((1 - e) + e * sec z) := fun y z =>
    (key _ _ (by rw [← mul_assoc, hf1, hf1]) (by rw [map_mul, hf2, hf2])).symm
  have hone : (1 - e) + e * sec 1 = 1 := (key 1 1 (mul_one _) (map_one _)).symm
  let f : (Fv D.host.F v)ˣ → (AE D)ˣ := fun y =>
    ⟨(1 - e) + e * sec y, (1 - e) + e * sec ((y⁻¹ : (Fv D.host.F v)ˣ) : Fv D.host.F v),
      by rw [← hmul, Units.mul_inv, hone], by rw [← hmul, Units.inv_mul, hone]⟩
  exact ⟨MonoidHom.mk' f fun y z => Units.ext (by simp only [f, Units.val_mul]; exact hmul y z),
    fun y => ⟨hf1 y, hf2 y⟩, fun x y h1 h2 => key x y h1 h2⟩

end GlobalTheory.TwistChart

namespace GlobalTheory.TwistChart

variable {D : D7}

def blockEquiv (n r k t : ℕ) (h : n = r + k * t) : Fin r ⊕ Blocks k t ≃ Fin n :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sigmaEquivProd _ _).trans finProdFinEquiv)).trans
    (finSumFinEquiv.trans (finCongr h.symm))

theorem blockEquiv_inl (n r k t : ℕ) (h : n = r + k * t) (i : Fin r) : ((blockEquiv n r k t h (.inl i) : Fin n) : ℕ) = i := by
  simp [blockEquiv]

theorem exists_isChart (s : PiLocalization₂ D) (k : ℕ) (hrank : s.V.rank = D.R.r + k * D.R.t) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (φ : SplitProj D v) {e : AE D} (he : IsIdemOf φ e) : ∃ ι, IsChart s k φ ι := by
  have hπ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  have hJ := GlobalTheory.NoExcl.isHermND_gram s.V
  let ε := blockEquiv s.V.rank D.R.r k D.R.t hrank
  let re : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃* GL (Fin s.V.rank) (Fv D.host.F v) :=
    Units.mapEquiv (Matrix.reindexAlgEquiv (Fv D.host.F v) (Fv D.host.F v) ε).toRingEquiv.toMulEquiv
  let L := GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (GlobalTheory.AdelicU.chartEmb hπ) (frCo φ s.β)
  let ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V :=
    (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v).comp (L.symm.toMulEquiv.toMonoidHom.comp re.toMonoidHom)
  refine ⟨ι, ε, blockEquiv_inl _ _ _ _ hrank, fun y => ⟨?_, ?_⟩⟩
  · change GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v (ι y)) = ι y
    simp only [ι, MonoidHom.comp_apply, GlobalTheory.AdelicU.proj_emb_self]
  · have h1 : grpCo φ s.V (frCo φ s.β) (ι y) = GlobalTheory.SplitHecke.rho s.V (rdA φ) (frCo φ s.β) (ι y) := by
      refine Units.ext ?_
      rw [GlobalTheory.SplitHecke.rho_val]
      rfl
    rw [h1, GlobalTheory.AdelicU.rho_eq_splitEquivIn hπ s.V hJ]
    simp only [ι, L, MonoidHom.comp_apply, GlobalTheory.AdelicU.proj_emb_self]
    have h2 : L (L.symm (re y)) = re y := L.apply_symm_apply _
    change (L (L.symm (re y))).1.submatrix ε ε = y.1
    rw [h2]
    ext i j
    simp [re]

end GlobalTheory.TwistChart

namespace GlobalTheory.TwistChart

open GlobalTheory.ChainOnto GlobalTheory.ChainTw

theorem charts_at_twist : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, (∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP) ∧ ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → (∃ e, IsIdemOf φ e) ∧ (∃ x ϖ, IsLocUnif φ x ϖ) ∧ (∃ ι, IsChart s j φ ι) ∧ ∀ χ : (AE D)ˣ →* Circle, ∃ μ : (Fv D.host.F v)ˣ →* ℂˣ, GlobalTheory.SmGL.IsUnitaryChar μ ∧ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (χ x)) := by
  intro D c w hw j _ s hs PP hPP
  classical
  have hPg : PP ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_right _ hPP
  obtain ⟨-, ⟨es, hes, -⟩, -⟩ := hw.com.split
  refine ⟨?_, fun v φ _ => ?_⟩
  · obtain ⟨v, φ, -, h⟩ := (GlobalTheory.SplitIdemDict.idem_dictionary D).1 _ _ (hes PP hPg)
    exact ⟨v, φ, h⟩
  have he := isIdemOf_idem φ
  obtain ⟨U, hU1, hU2⟩ := unit_section φ he
  have huniq := (GlobalTheory.SplitProjChart.chart_rdA D v φ _ he).2.2.2.2
  obtain ⟨hr, -, hst⟩ := hs
  refine ⟨⟨_, he⟩, ?_, exists_isChart s j hst.rank φ he, fun χ => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_unif (D := D) v
    exact ⟨U ϖ, ϖ, _, he, (hU1 ϖ).1, (hU1 ϖ).2, hϖ⟩
  · refine ⟨(Circle.toUnits.comp χ).comp U, fun y => ?_, fun x y ⟨e', he', h1, h2⟩ => ?_⟩
    · exact Circle.norm_coe _
    · obtain rfl := huniq e' he'
      have hx : x = U y := Units.ext (hU2 _ _ h1 h2)
      rw [hx]
      rfl

end GlobalTheory.TwistChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConjVec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Core.Mi

theorem exists_conjVec : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → ∃ v₀ : M.Vec, ConjVec X h θ M v₀ := by
  intro hcl D X h θ S M hS hθ _hgap hιE
  subst hS
  obtain ⟨-, -, hreal, -⟩ := GlobalTheory.T.modelIdentification_respects_real_and_finite D X h θ hθ hιE
  obtain ⟨-, -, -, -, hmult, -, hstrict⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hcl
  have hU := GlobalTheory.Published.discreteSeriesHermitianUnique_of_classification hcl
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.SeeInt.exists_conj_intertwiner hU hmult hstrict X.B.I h X.pl X.n_eq X.eps_eq X.B.H X.B.σ
    X.B.w X.B.lam X.lam_eq X.ds X.low M
  refine ⟨fun τ => ⟨(c τ).symm (X.B.w (X.pl.symm τ)), hc2 τ⟩, c, fun τ g hg x => hc1 τ g hg _ (hreal τ g hg).2.2 x,
    fun τ => ?_⟩
  exact LinearIsometryEquiv.apply_symm_apply _ _

end GlobalTheory.Core.Mi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlaceStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_doubled_unitary_chart_split_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E), IsSplitChart σ J L h e → ∃ f : GLoc σ Q v ≃* GL (Fin (n + n)) (w.adicCompletion E), (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ KGL w (n + n)) ∧ (∀ y y', f (ioH _ σ hQ (y, y')) = blkGL finSumFinEquiv (e y, e y')) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ KeepsDiag finSumFinEquiv (f g).1) ∧ ∀ p : siegelH (Fv F v) σ Q, toCompl h (aH _ σ Q p).1 = (leviMat finSumFinEquiv (f p).1).det ∧ ∀ (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v), w ≠ w' → ordL (toCompl h' (aH _ σ Q p).1) = -ordL (quotMat finSumFinEquiv (f p).1).det := by
  first | exact @GlobalTheory.LFun.DblSplit.exists_dbl_chart | exact GlobalTheory.LFun.DblSplit.exists_dbl_chart | (intros; apply GlobalTheory.LFun.DblSplit.exists_dbl_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixUpImageCompletedHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfIntUp

theorem sec_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (a b : k) : q.sec (a * b) = q.sec a * q.sec b := by

  have he : ∀ c : k, q.sec c = q.e * q.sec c := fun c => by rw [← q.sec_pr, q.pr_sec]
  have h1 : q.sec (a * b) = q.e * (q.sec a * q.sec b) := by
    rw [← q.sec_pr, map_mul q.pr, q.pr_sec, q.pr_sec]
  rw [h1, ← mul_assoc, ← he]

private lemma mulVec_sec_eq_sec_mulVec {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {m n : Type} [Fintype n]
    (u : Matrix m n (AE D)) (z : n → k) :
    u *ᵥ (fun j => q.sec (z j)) = fun i => q.sec ((u.map q.pr *ᵥ z) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have he : q.sec (z j) = q.e * q.sec (z j) := by rw [← q.sec_pr, q.pr_sec]
  rw [sec_mul', q.sec_pr]
  conv_lhs => rw [he]
  ring

theorem exists_int_up : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ u : WO S T, u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → IsHalf q.e u → ∃ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) ∧ u = (ofSplit q).up FS FT x := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hSd _ hS hT u hu hh
  refine ⟨(ofSplit q).down FS FT u, ?_, (GlobalTheory.LocMod.Witness.up_down (ofSplit q) FS FT hh).symm⟩
  intro r s

  have hz : (fun i => q.sec ((FS.β *ᵥ Pi.single s 1) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v) := by
    refine (hS (Pi.single s 1)).1 fun i => ?_
    rcases eq_or_ne i s with rfl | h
    · rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _

  have hmem := GlobalTheory.FinPl.LatMem.latO_maps hSd hu hz
  rw [hU.2 T LT, mulVec_sec_eq_sec_mulVec q u (FS.β *ᵥ Pi.single s 1)] at hmem

  have hcol : FT.β *ᵥ (fun r => (ofSplit q).down FS FT u r s) =
      (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map q.pr *ᵥ (FS.β *ᵥ Pi.single s 1) := by
    have e1 : (fun r => (ofSplit q).down FS FT u r s) = (ofSplit q).down FS FT u *ᵥ Pi.single s 1 := by
      funext r; simp [Matrix.mulVec_single]
    rw [e1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp only [GlobalTheory.LocMod.Place.down, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul]
    rfl
  have hin : (fun i => q.sec ((FT.β *ᵥ (fun r => (ofSplit q).down FS FT u r s)) i)) ∈
      GlobalTheory.FinPl.latV T LT (· = q.v) := by
    rw [hcol]; exact hmem
  exact (hT _).2 hin r

end GlobalTheory.HalfIntUp
end
end

