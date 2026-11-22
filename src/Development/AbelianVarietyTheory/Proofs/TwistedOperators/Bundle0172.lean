import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0034
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorsReframeSource
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.Refock

variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem frameMatrix_mul_frameMatrixInv : frP S b * frPinv S b = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _

theorem gram_reS : (reS S b).gram = (frP S b)ᴴ * S.gram * frP S b := by
  refine Matrix.ext fun (i j : Fin S.rank) => ?_
  have hb : ∀ k, b k = ∑ l, frP S b l k • S.frame l := fun k =>
    (Module.Basis.sum_toMatrix_smul_self S.frame b k).symm
  show S.hT (b i) (b j) = ∑ k, (∑ l, star (frP S b l i) * S.gram l k) * frP S b k j
  rw [hb i, hb j]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    HSpace.gram, Finset.sum_mul, Finset.mul_sum, RingHom.id_apply, starRingEnd_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem hO_trace (S T : HSp D) (x y : WO S T) : hO S T x y =
    trace ((S.gram⁻¹).map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Matrix.map_apply, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem inv_eq_of_gram_conjTranspose_change {n : ℕ} {G' G P Pinv : Matrix (Fin n) (Fin n) D.host.E} (h : G' = Pᴴ * G * P)
    (hP : P * Pinv = 1) : G'⁻¹ = Pinv * G⁻¹ * Pinvᴴ := by
  rw [h, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv,
    Matrix.inv_eq_right_inv hP, Matrix.mul_assoc]

theorem gram_reS_inv : (reS S b).gram⁻¹ = frPinv S b * S.gram⁻¹ * (frPinv S b)ᴴ :=
  inv_eq_of_gram_conjTranspose_change (gram_reS b) (frameMatrix_mul_frameMatrixInv b)

theorem map_conjTranspose_incA {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    Mᴴ.map (incA D) = ((M.map (incA D)).map (cA D))ᵀ := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, conjTranspose_apply, Matrix.transpose_apply]
  rfl

theorem adelicMap_inv_conjTranspose_congruence {n : ℕ} {G' G Pinv : Matrix (Fin n) (Fin n) D.host.E} (h : G'⁻¹ = Pinv * G⁻¹ * Pinvᴴ) :
    G'⁻¹.map (incA D) = Pinv.map (incA D) * G⁻¹.map (incA D) * ((Pinv.map (incA D)).map (cA D))ᵀ := by
  rw [h, Matrix.map_mul, Matrix.map_mul, map_conjTranspose_incA]

theorem trace_inverseGram_conj_smul_eq {R : Type} [CommRing R] (c : R →+* R) {n m : ℕ} (A Q : Matrix (Fin n) (Fin n) R)
    (Y X : Matrix (Fin m) (Fin n) R) (C : Matrix (Fin m) (Fin m) R) :
    trace (Q * A * (Q.map c)ᵀ * (Y.map c)ᵀ * C * X) = trace (A * ((Y * Q).map c)ᵀ * C * (X * Q)) := by
  rw [Matrix.map_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Q]
  simp only [Matrix.mul_assoc]

theorem hO_reW (x y : WO (reS S b) T) : hO (reS S b) T x y = hO S T (reW S T b x) (reW S T b y) := by
  rw [hO_trace, hO_trace, adelicMap_inv_conjTranspose_congruence (gram_reS_inv b)]
  exact trace_inverseGram_conj_smul_eq (R := AE D) (cA D) (n := S.rank) (m := T.rank) _ _ _ _ _
end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem reW_add (x y : WO (reS S b) T) : reW S T b (x + y) = reW S T b x + reW S T b y :=
  Matrix.add_mul _ _ _

def reWHom : WO (reS S b) T →+ WO S T where
  toFun := reW S T b
  map_zero' := Matrix.zero_mul _
  map_add' := reW_add b

theorem heisO_reF (ψ : AddChar (AF D.host.F) ℂ) (w₀ : WO (reS S b) T) (f : WO S T → ℂ) :
    heisO ψ (reS S b) T w₀ (reF S T b f) = reF S T b (heisO ψ S T (reW S T b w₀) f) := by
  funext w
  simp only [heisO, reF_apply, symplOH, symplO, hO_reW, reW_add]

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : D.host.E) :
    θ τ (infPart D (incA D e)) = tauE D τ e := by
  show θ τ ((Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) ((1 : AF D.host.F) ⊗ₜ e)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  exact (hθ τ).1 e

theorem compAt_reW {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : Mx D T.rank S.rank) :
    compAt θ τ (reW S T b x) = compAt θ τ x * (frPinv S b).map (tauE D τ) := by
  have e1 : ∀ {m n : ℕ} (w : Mx D m n), compAt θ τ w = w.map ((θ τ).comp (infPart D)) := fun _ => rfl
  show compAt θ τ (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))) = _
  rw [e1, e1, Matrix.map_mul, Matrix.map_map]
  congr 2
  funext e
  exact theta_incA hθ τ e

theorem finPart_reW (x : Mx D T.rank S.rank) (hx : x.map (finPart D) = 0) :
    (reW S T b x).map (finPart D) = 0 := by
  show (HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))).map (finPart D) = 0
  rw [Matrix.map_mul, hx, Matrix.zero_mul]

end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem tauFrame_mul_tauFrameInv (τ : D.what₂.Tau) :
    (frP S b).map (tauE D τ) * (frPinv S b).map (tauE D τ) = 1 := by
  rw [← Matrix.map_mul, frameMatrix_mul_frameMatrixInv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cplxO_mul {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (z : Matrix (Fin m) (Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) : cplxO 1 s (z * M) = cplxO 1 s z * M := by
  simp only [cplxO, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_assoc]

theorem continuous_reW : Continuous (reW S T b) :=
  continuous_id.matrix_mul continuous_const

theorem lineAt_reW {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    reW S T b (lineAt θ τ (z * (frP S b).map (tauE D τ)) t) = lineAt θ τ z t := by
  have hL := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ (z * (frP S b).map (tauE D τ))
  have key := GlobalTheory.RealLineAt.lineAt_unique D θ hθ T.rank S.rank τ z
    ((reWHom (T := T) b).comp (lineAt θ τ (z * (frP S b).map (tauE D τ)))) (lineAt θ τ z)
    ⟨(continuous_reW b).comp hL.1, fun s => finPart_reW b _ (hL.2.1 s), fun s τ' => ?_⟩
    (GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z)
  · exact DFunLike.congr_fun key t
  · refine (compAt_reW b hθ τ' (lineAt θ τ (z * (frP S b).map (tauE D τ)) s)).trans ?_
    rw [hL.2.2 s τ']
    split_ifs
    · subst τ'
      rw [Matrix.smul_mul, Matrix.mul_assoc, tauFrame_mul_tauFrameInv, Matrix.mul_one]
    · exact Matrix.zero_mul _

end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)
variable (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ)
include hθ

theorem dRho_reF (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (f : WO S T → ℂ) :
    dRho (heisO ψ (reS S b) T) θ τ (z * (frP S b).map (tauE D τ)) (reF S T b f) =
      reF S T b (dRho (heisO ψ S T) θ τ z f) := by
  funext x
  have h : ∀ t : ℝ, heisO ψ (reS S b) T (lineAt θ τ (z * (frP S b).map (tauE D τ)) t) (reF S T b f) x =
      heisO ψ S T (lineAt θ τ z t) f (reW S T b x) := fun t => by
    exact (congrFun (heisO_reF b ψ _ f) x).trans
      (congrArg (fun w => heisO ψ S T w f (reW S T b x)) (lineAt_reW b hθ τ z t))
  show deriv (fun t : ℝ => heisO ψ (reS S b) T (lineAt θ τ (z * (frP S b).map (tauE D τ)) t) (reF S T b f) x) 0 =
    deriv (fun t : ℝ => heisO ψ S T (lineAt θ τ z t) f (reW S T b x)) 0
  simp only [h]

theorem aPlus_reF (τ : D.what₂.Tau) (s : Matrix (Fin T.rank) (Fin T.rank) ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (f : WO S T → ℂ) :
    aPlus (heisO ψ (reS S b) T) θ τ (cplxO 1 s) (z * (frP S b).map (tauE D τ)) (reF S T b f) =
      reF S T b (aPlus (heisO ψ S T) θ τ (cplxO 1 s) z f) := by
  have h1 := dRho_reF b ψ hθ τ z f
  have h2 : dRho (heisO ψ (reS S b) T) θ τ (cplxO 1 s (z * (frP S b).map (tauE D τ))) (reF S T b f) =
      reF S T b (dRho (heisO ψ S T) θ τ (cplxO 1 s z) f) :=
    (congrArg (fun w => dRho (heisO ψ (reS S b) T) θ τ w (reF S T b f)) (cplxO_mul s z _)).trans
      (dRho_reF b ψ hθ τ (cplxO 1 s z) f)
  simp only [aPlus, crea]
  rw [h1, h2, LinearMap.map_smul, LinearMap.map_sub, LinearMap.map_smul]

end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan.Refock
variable {D : D7} {S T : HSp D} (b : Module.Basis (Fin S.rank) D.host.E S.V)

theorem unitMap_re {m : ℕ} (τ : D.what₂.Tau) (B : Matrix (Fin S.rank) (Fin S.rank) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ)
    (i : Fin m) (j : Fin S.rank) :
    unitMap ((frPinv S b).map (tauE D τ) * B) B' i j = unitMap B B' i j * (frP S b).map (tauE D τ) := by
  unfold unitMap
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv (tauFrame_mul_tauFrameInv b τ)]
  simp only [Matrix.mul_assoc]

theorem gramAt_reS (τ : D.what₂.Tau) :
    gramAt D (reS S b) τ = ((frP S b).map (tauE D τ))ᴴ * gramAt D S τ * (frP S b).map (tauE D τ) := by
  have e : ((frP S b).map (tauE D τ))ᴴ = (frP S b)ᴴ.map (tauE D τ) :=
    Matrix.ext fun i j => by simp [conjTranspose_apply, Formalism.IndefR.Eqv.tauE_star]
  refine (congrArg (fun M : Matrix (Fin S.rank) (Fin S.rank) D.host.E => M.map (tauE D τ)) (gram_reS b)).trans ?_
  show _ = _ * (S.gram).map (tauE D τ) * _
  rw [Matrix.map_mul, Matrix.map_mul, e]

theorem conjTranspose_gram_congruence_cancel {n : ℕ} (B P Pinv G : Matrix (Fin n) (Fin n) ℂ) (h : P * Pinv = 1) :
    (Pinv * B)ᴴ * (Pᴴ * G * P) * (Pinv * B) = Bᴴ * G * B := by
  have h' : Pinvᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h, conjTranspose_one]
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Pinv, h, Matrix.one_mul, ← Matrix.mul_assoc Pinvᴴ, h', Matrix.one_mul]

theorem opPow_comm {ι X Y : Type} (A : ι → (X → ℂ) → (X → ℂ)) (A' : ι → (Y → ℂ) → (Y → ℂ))
    (H : (X → ℂ) → (Y → ℂ)) (hA : ∀ i g, A' i (H g) = H (A i g)) (k : ι →₀ ℕ) (f : X → ℂ) :
    opPow A' k (H f) = H (opPow A k f) := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, ih, hA]

theorem pureTensorL_comm' {ι X Y : Type} (A : ι → (X → ℂ) → (X → ℂ)) (A' : ι → (Y → ℂ) → (Y → ℂ))
    (H : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (hA : ∀ i g, A' i (H g) = H (A i g)) (f : X → ℂ) (P : MvPolynomial ι ℂ) :
    pureTensorL A' (H f) P = H (pureTensorL A f P) := by
  have e : pureTensorL A' (H f) = H ∘ₗ pureTensorL A f := (MvPolynomial.basisMonomials ι ℂ).ext fun k => by
    rw [LinearMap.comp_apply, pureTensorL, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis]
    exact opPow_comm A A' H hA k f
  rw [e, LinearMap.comp_apply]

theorem aPlusAll_reF (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (k : FVar D T.rank S.rank) (g : WO S T → ℂ) :
    aPlusAll (heisO ψ (reS S b) T) θ (fun τ => cplxO 1 (sT τ)) (fun τ => (frPinv S b).map (tauE D τ) * BS τ) BT k
        (reF S T b g) = reF S T b (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (sT τ)) BS BT k g) :=
  (congrArg (fun w => aPlus (heisO ψ (reS S b) T) θ k.1 (cplxO 1 (sT k.1)) w (reF S T b g))
    (unitMap_re b k.1 (BS k.1) (BT k.1) k.2.1 k.2.2)).trans
    (aPlus_reF b ψ hθ k.1 (sT k.1) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2) g)

end GlobalTheory.AdSpan.Refock

namespace GlobalTheory.AdSpan

open Refock in

theorem pureTensorO_reF : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ, ∃ BS' : D.what₂.Tau → Matrix (Fin (reS S b).rank) (Fin (reS S b).rank) ℂ, (∀ τ, (BS' τ)ᴴ * gramAt D (reS S b) τ * BS' τ = (BS τ)ᴴ * gramAt D S τ * BS τ) ∧ ∀ (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ), pureTensorO ψ θ (reS S b) T (fun _ => 1) sT BS' BT (reF S T b f) P = reF S T b (pureTensorO ψ θ S T (fun _ => 1) sT BS BT f P) := by
  intro D S T b ψ θ hθ BS
  refine ⟨fun τ => (frPinv S b).map (tauE D τ) * BS τ, fun τ => ?_, fun sT BT f P => ?_⟩
  · rw [gramAt_reS b τ]
    exact conjTranspose_gram_congruence_cancel _ _ _ _ (tauFrame_mul_tauFrameInv b τ)
  · exact pureTensorL_comm' _ _ (reF S T b) (fun k g => aPlusAll_reF b ψ hθ sT BT BS k g) f P

end GlobalTheory.AdSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FreeMonoidAlgebraOfCharacterVanishesOffOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FreeOfCharacter

noncomputable def freeRep (P : Type) [Group P] (N : ℕ) :
    Representation ℂ P (Fin N → MonoidAlgebra ℂ P) where
  toFun g :=
    { toFun := fun x => (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ P) • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => smul_comm _ c x }
  map_one' := by
    refine LinearMap.ext fun x => ?_
    simp [← MonoidAlgebra.one_def]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [smul_smul, MonoidAlgebra.single_mul_single]

theorem freeRep_apply {P : Type} [Group P] {N : ℕ} (g : P) (x : Fin N → MonoidAlgebra ℂ P) :
    freeRep P N g x = (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ P) • x := rfl

theorem trace_freeRep {P : Type} [Group P] [Finite P] (N : ℕ) {g : P} (hg : g ≠ 1) :
    LinearMap.trace ℂ _ (freeRep P N g) = 0 := by
  classical
  haveI := Fintype.ofFinite P
  let b := Pi.basis fun _ : Fin N => MonoidAlgebra.basis P ℂ
  have hb : ∀ (j : Fin N) (q : P), b ⟨j, q⟩ = Pi.single j (MonoidAlgebra.single q 1) := by
    intro j q
    simp [b, Pi.basis_apply]
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨j, p⟩ := i
  have hmove : freeRep P N g (b ⟨j, p⟩) = b ⟨j, g * p⟩ := by
    rw [hb, hb, freeRep_apply]
    funext k
    by_cases hk : k = j
    · subst hk
      simp [MonoidAlgebra.single_mul_single]
    · simp [hk]
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hmove, b.repr_self, Finsupp.single_apply, if_neg]
  intro h
  rw [Sigma.mk.inj_iff, heq_iff_eq] at h
  exact hg (mul_right_cancel (h.2.trans (one_mul p).symm))

theorem finrank_free (P : Type) [Group P] [Finite P] (N : ℕ) :
    Module.finrank ℂ (Fin N → MonoidAlgebra ℂ P) = Nat.card P * N := by
  haveI := Fintype.ofFinite P
  rw [Module.finrank_eq_card_basis (Pi.basis fun _ : Fin N => MonoidAlgebra.basis P ℂ),
    Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.card_eq_fintype_card, mul_comm]

theorem free_of_trace_eq_zero : ∀ (P M : Type) [Group P] [Finite P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ P M), (∀ g : P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) → ∃ N : ℕ, Nat.card P * N = Module.finrank ℂ M ∧ Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra ℂ P] (Fin N → MonoidAlgebra ℂ P)) := by
  intro P M _ _ _ _ _ ρ hρ
  classical
  haveI := Fintype.ofFinite P
  have hcard : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  haveI : Invertible (Nat.card P : ℂ) := invertibleOfNonzero hcard

  have hz : ∀ g : P, g ≠ 1 → ρ.character g = 0 := hρ
  have havg := Representation.card_inv_mul_sum_char_eq_finrank ρ
  rw [Finset.sum_eq_single (1 : P) (fun g _ hg => hz g hg) (by simp),
    Representation.char_one] at havg
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Nat.card P * N = Module.finrank ℂ M := by
    refine ⟨Module.finrank ℂ (Representation.invariants ρ), ?_⟩
    have hc : ((Nat.card P * Module.finrank ℂ (Representation.invariants ρ) : ℕ) : ℂ) =
        (Module.finrank ℂ M : ℂ) := by
      push_cast
      rw [← havg, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    exact_mod_cast hc
  refine ⟨N, hN, ?_⟩
  haveI : FiniteDimensional ℂ (MonoidAlgebra ℂ P) :=
    Module.Finite.of_basis (MonoidAlgebra.basis P ℂ)

  have hχ : ρ.character = (freeRep P N).character := by
    funext g
    by_cases hg : g = 1
    · subst hg
      rw [Representation.char_one, Representation.char_one, finrank_free, hN]
    · exact (hz g hg).trans (trace_freeRep N hg).symm
  obtain ⟨e⟩ := GlobalTheory.CharacterDetermines.nonempty_equiv_of_character_eq P M
    (Fin N → MonoidAlgebra ℂ P) ρ (freeRep P N) hχ

  have hlin : ∀ (r : MonoidAlgebra ℂ P) (x : M),
      e.toLinearEquiv (ρ.asAlgebraHom r x) = (freeRep P N).asAlgebraHom r (e.toLinearEquiv x) := by
    intro r x
    induction r using MonoidAlgebra.induction_on with
    | of g =>
      simp only [Representation.asAlgebraHom_of]
      exact e.toIntertwiningMap.isIntertwining _ _ g x
    | add f f' hf hf' => simp only [map_add, LinearMap.add_apply, hf, hf']
    | smul c f hf => simp only [map_smul, LinearMap.smul_apply, hf]

  have hact : ∀ (r : MonoidAlgebra ℂ P) (y : Fin N → MonoidAlgebra ℂ P),
      (freeRep P N).asAlgebraHom r y = r • y := by
    intro r y
    induction r using MonoidAlgebra.induction_on with
    | of g => rw [Representation.asAlgebraHom_of, freeRep_apply, MonoidAlgebra.of_apply]
    | add f f' hf hf' => rw [map_add, LinearMap.add_apply, hf, hf', add_smul]
    | smul c f hf => rw [map_smul, LinearMap.smul_apply, hf, smul_assoc]
  exact ⟨{ (ρ.asModuleEquiv.trans e.toLinearEquiv).toAddEquiv with
    map_smul' := fun r x => by
      change e.toLinearEquiv (ρ.asModuleEquiv (r • x)) = r • e.toLinearEquiv (ρ.asModuleEquiv x)
      rw [Representation.asModuleEquiv_map_smul, hlin, hact] }⟩

end GlobalTheory.FreeOfCharacter
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodProjectorCoeffEqProdAtTwoTypePrimes
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodProjProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem monicOf_injective {g N : ℕ} [Fact g.Prime] :
    Function.Injective fun c : Fin N → ZMod g => (Formalism.CyclotomicNorms.monicOf c : (ZMod g)[X]) := by
  intro c c' h
  funext i
  have key := congrArg (fun p : (ZMod g)[X] => p.coeff (i : ℕ)) h
  simp only [Formalism.CyclotomicNorms.monicOf, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul_X_pow, Nat.ne_of_lt i.isLt, if_false, zero_add] at key
  rwa [Finset.sum_eq_single i (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (by simp), if_pos rfl,
    Finset.sum_eq_single i (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm))) (by simp), if_pos rfl] at key

open Classical in

theorem sum_good {g N m : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] [Fintype (ι → Fin N → ZMod g)]
    (ch : ι → Fin m → (ZMod g)ˣ) (h : (ι → (ZMod g)[X]) → ℂ) :
    (∑ a : ι → Fin N → ZMod g, if GlobalTheory.BadShare.Good g N ch (fun v => Formalism.CyclotomicNorms.monicOf (a v)) then
      h (fun v => Formalism.CyclotomicNorms.monicOf (a v)) else 0) = ∑ F ∈ GlobalTheory.BadShare.goodSet g N ch, h F := by
  have hinj : Function.Injective fun (a : ι → Fin N → ZMod g) (v : ι) => (Formalism.CyclotomicNorms.monicOf (a v) : (ZMod g)[X]) :=
    by
      intro a b hab
      funext v
      have hv : Formalism.CyclotomicNorms.monicOf (a v) = (Formalism.CyclotomicNorms.monicOf (b v) : (ZMod g)[X]) := congrFun hab v
      exact monicOf_injective (g := g) (N := N) hv
  have hset : GlobalTheory.BadShare.goodSet g N ch =
      (Finset.univ.filter fun a : ι → Fin N → ZMod g => GlobalTheory.BadShare.Good g N ch fun v => Formalism.CyclotomicNorms.monicOf (a v)).image
        fun (a : ι → Fin N → ZMod g) (v : ι) => (Formalism.CyclotomicNorms.monicOf (a v) : (ZMod g)[X]) := by
    ext F
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hF
      have hG := GlobalTheory.BadShare.mem_goodSet_iff_good.1 hF
      have hsq := (GlobalTheory.BadShare.good_iff.1 hG).1
      have hc : ∀ v, ∃ c : Fin N → ZMod g, Formalism.CyclotomicNorms.monicOf c = F v := by
        intro v
        have hv := hsq v
        rw [GlobalTheory.BadShare.sqSet_eq_monicOf, Finset.mem_filter, Finset.mem_image] at hv
        obtain ⟨c, -, hc⟩ := hv.1
        exact ⟨c, hc⟩
      choose a ha using hc
      have hMa : (fun v => Formalism.CyclotomicNorms.monicOf (a v)) = F := funext ha
      refine ⟨a, ?_, hMa⟩
      rw [hMa]
      exact hG
    · rintro ⟨a, hG, rfl⟩
      exact GlobalTheory.BadShare.mem_goodSet_iff_good.2 hG
  rw [hset, Finset.sum_image (fun a _ b _ e => hinj e), Finset.sum_filter]

theorem sum_sigma_two {P : Fin 2 → Type} {A : Fin 2 → Type} [Fintype (∀ kv : (Σ k : Fin 2, P k), A kv.1)]
    [Fintype (P 0 → A 0)] [Fintype (P 1 → A 1)] (f0 : (P 0 → A 0) → ℂ) (f1 : (P 1 → A 1) → ℂ) :
    (∑ a : (∀ kv : (Σ k : Fin 2, P k), A kv.1), f0 (fun v => a ⟨0, v⟩) * f1 (fun v => a ⟨1, v⟩)) =
      (∑ a, f0 a) * ∑ b, f1 b := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv ((Equiv.piCurry fun (k : Fin 2) (_ : P k) => A k).trans
    (piFinTwoEquiv fun k => P k → A k)) _ _ (fun a => rfl)

theorem goodProjector_coeff_eq_prod_at_two_typePrimes : ∀ (D : D7) (τ : ∀ k : Fin 2, (ZMod (D.host.g k))[X] → GlobalTheory.BadShare.GG (D.host.g k) D.R.r → ℂ), (∀ k, ∀ f ∈ GlobalTheory.BadShare.sqSet (D.host.g k) D.R.r, ∀ x, (D.ntypes.eSer k f).coeff x = GlobalTheory.BadShare.zc (τ k f) x) → ∀ γ : G0g D.nd, D.ntypes.e0.coeff γ = GlobalTheory.BadShare.eGood (fun _ => τ 0) (D.nd.chiT 0) (fun v => γ ⟨0, v⟩) * GlobalTheory.BadShare.eGood (fun _ => τ 1) (D.nd.chiT 1) (fun v => γ ⟨1, v⟩) := by
  intro D τ hτ γ
  classical
  have he : D.ntypes.e0.coeff γ = ∑ᶠ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0 := by
    unfold NTypes.e0
    rfl
  let f : ∀ k : Fin 2, (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k)) → ℂ := fun k b =>
    if GlobalTheory.BadShare.Good (D.host.g k) D.R.r (D.nd.chiT k) (fun v => Formalism.CyclotomicNorms.monicOf (b v)) then
      ∏ v, (D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf (b v))).coeff (γ ⟨k, v⟩) else 0
  have hsplit : ∀ a : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      (if D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv, (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv) else 0) =
        f 0 (fun v => a ⟨0, v⟩) * f 1 (fun v => a ⟨1, v⟩) := by
    intro a
    have hg : D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) ↔
        ∀ k : Fin 2, GlobalTheory.BadShare.Good (D.host.g k) D.R.r (D.nd.chiT k) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) := by
      unfold NTypes.goodTuple GlobalTheory.BadShare.Good
      exact Iff.rfl
    rw [Fintype.prod_sigma, Fin.prod_univ_two]
    by_cases h0 : GlobalTheory.BadShare.Good (D.host.g 0) D.R.r (D.nd.chiT 0) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨0, v⟩)) <;>
      by_cases h1 : GlobalTheory.BadShare.Good (D.host.g 1) D.R.r (D.nd.chiT 1) (fun v => Formalism.CyclotomicNorms.monicOf (a ⟨1, v⟩)) <;>
      simp [f, hg, Fin.forall_fin_two, h0, h1]
  have hk : ∀ k : Fin 2, ∑ b, f k b = GlobalTheory.BadShare.eGood (fun _ => τ k) (D.nd.chiT k) (fun v => γ ⟨k, v⟩) := by
    intro k
    refine (Eq.trans ?_ (sum_good (g := D.host.g k) (N := D.R.r) (D.nd.chiT k)
      (fun F => ∏ v, (D.ntypes.eSer k (F v)).coeff (γ ⟨k, v⟩)))).trans ?_
    · rfl
    · unfold GlobalTheory.BadShare.eGood
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl (fun F hF => ?_)
      have hsq := (GlobalTheory.BadShare.good_iff.1 (GlobalTheory.BadShare.mem_goodSet_iff_good.1 hF)).1
      unfold GlobalTheory.BadShare.tens
      exact Finset.prod_congr rfl fun v _ => hτ k (F v) (hsq v) (γ ⟨k, v⟩)
  rw [he, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ hsplit,
    sum_sigma_two (P := fun k => D.nd.PlG k) (A := fun k => Fin D.R.r → ZMod (D.host.g k)) (f 0) (f 1), hk 0, hk 1]

end GlobalTheory.GoodProjProd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeVecSatakeSumUnitaryBorelRepresentativesStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeVec_satake_sum_unitaryBorel_representatives : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ), ∀ h ∈ Hecke ℂ (KU σ n), ∃ (ι : Type) (_ : Fintype ι) (b : ι → GU σ n), (∀ i, IsBorelU (b i)) ∧ (∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (s : M), (∀ k ∈ KU σ n, π k s = s) → heckeVec π (KU σ n) h s = ∑ i, h (b i) • π (b i) s) ∧ ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = ∑ i, h (b i) * ∏ k : Fin (n / 2), ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((b i).1.1 (lo n k) (lo n k)) := by
  first | exact @GlobalTheory.SatBorel.heckeVec_satU_borel | exact GlobalTheory.SatBorel.heckeVec_satU_borel | (intros; apply GlobalTheory.SatBorel.heckeVec_satU_borel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergVacuumUniqueOfSelfDualStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergVacuum_unique_of_selfDual : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ v, Fixes W Λ v → ∃ c : ℂ, v = c • s := by
  first | exact @GlobalTheory.SphTheta.vacuum_unique_of_selfDual | exact GlobalTheory.SphTheta.vacuum_unique_of_selfDual | (intros; apply GlobalTheory.SphTheta.vacuum_unique_of_selfDual <;> assumption)
end

