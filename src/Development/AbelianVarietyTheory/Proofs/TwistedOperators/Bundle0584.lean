import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0564
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0567
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchrodingerThetaDatumHeisenbergOriented
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  calc _ = ∑ j, ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, ∑ l, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ l, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j, ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (HMul.hMul (HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D))
      ((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ) (T.gram.map (incA D)))
      (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by
  simp only [hO, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c', ∑ d, incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a
      = ∑ b, ∑ d, ∑ c', incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c', incA D (S.gram⁻¹ a b) * cA D (y c' b) * incA D (T.gram c' d) * x d a := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem trace_mul_submatrix {A : Type} [CommRing A] {m d : ℕ} (e : Fin m ≃ Fin d) (P : Matrix (Fin d) (Fin d) A)
    (K : Matrix (Fin m) (Fin m) A) : (P * K.submatrix e.symm e.symm).trace = (P.submatrix e e * K).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e]
  simp

theorem cA_inc (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, CMData.sig, inclR]; rfl

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun _ _ => S.herm.eq _ _

theorem gram_map_herm (S : HSp D) : ((S.gram.map (incA D)).map (cA D))ᵀ = S.gram.map (incA D) := by
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun (gram_herm S) i) j))

theorem gram_inv_mul (T : HSp D) : T.gram⁻¹.map (incA D) * T.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne _))]; simp

theorem hTens_eq_trace' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) (c' : A →+* A)
    (hc : ∀ a, c a = c' a) {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A)
    (x y : Matrix α β A) : GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c' * JBᵀ).trace := by
  rw [hTens_eq_trace]
  congr 3
  ext i j
  exact hc _

end GlobalTheory.SquareAgree.HeisCov

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem sgn_gram (ε : Bool) (S : HSp D) : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
  cases ε <;> ext i j <;> simp [Formalism.BasicNotions.HSpace.gram]

set_option maxHeartbeats 1000000 in

theorem symp_eq (ε : Bool) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (JV : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (JW : Matrix (Fin d) (Fin d) D.host.E)
    (hJ : JV = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : JW = D.host.xi0 • reindex e e X.gramᵀ)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) → WO S X)
    (hcS : ∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D)))
    (u w : Matrix (Fin S.rank) (Fin d) (AE D)) :
    GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JV)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JW) u w = symplO (sgn ε S) X (cS u) (cS w) := by
  have hGs : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram) = (sgn ε S).gram.map (incA D) := by
    rw [← sgn_gram]; rfl
  have hJA : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JV = -(sgn ε S).gram.map (incA D) := by
    rw [hJ, sgn_gram]
    cases ε <;> ext i j <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hJB : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JW)ᵀ =
      incA D D.host.xi0 • (X.gram.map (incA D)).submatrix e.symm e.symm := by
    rw [hJW]; ext i j; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  unfold GlobalTheory.WeilM.symp symplO
  rw [hTens_eq_trace' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (cA D) (fun _ => rfl), hO_eq_trace, hcS, hcS, hGs, hJA, hJB]
  have hinv := gram_inv_mul (sgn ε S)
  have hh := gram_map_herm (sgn ε S)
  have hW : ((wᵀ.submatrix e id).map (cA D))ᵀ = (w.map (cA D)).submatrix id e := rfl
  congr 1
  rw [Matrix.map_mul, Matrix.transpose_mul, hh, ← Matrix.mul_assoc _ _ (((wᵀ.submatrix e id).map (cA D))ᵀ), hinv,
    Matrix.one_mul, hW]
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.trace_neg,
    smul_eq_mul, trace_mul_submatrix, Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
  rw [Matrix.mul_assoc (uᵀ.submatrix e id * _), Matrix.trace_mul_comm (uᵀ.submatrix e id * _)]
  ring

end GlobalTheory.SquareAgree.HeisCov

namespace GlobalTheory.SquareAgree.HeisCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem invOf_two' {D : D7} : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul, mul_one_div_cancel two_ne_zero, map_one]

theorem isDatum_rho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ), IsDatum M ψ cS Φ f →
        ∀ w : Matrix (Fin S.rank) (Fin d) (AE D), IsDatum M ψ cS (M.co.rho ψ w Φ) (heisO ψ (sgn ε S) X (cS w) f) := by
  intro D ψ θ _ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW _ _ _ M _ cS hcS Φ f hD w
  refine ⟨?_, fun u => ?_⟩
  · have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hBs.std
    exact GlobalTheory.HeisSchA.rho_mem_schA M ψ hstd w Φ hD.1
  · rw [GlobalTheory.BigDat.rho_rho M.co ψ u w Φ, GlobalTheory.WeilM.thetaSum_smul, hD.2 (u + w)]
    unfold heisO symplOH
    rw [symp_eq ε S X e Vs.J Ws.J hJ hJW cS hcS u w, map_add, invOf_two']

end GlobalTheory.SquareAgree.HeisCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfAdjointFactorIdempotentOrthogonalSplittingRa
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {γ : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem factorIdem_mul (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) (p : plusAlg σ J γ) :
    factorIdem e i * ((p : genAlg γ) : Matrix (Fin n) (Fin n) E) =
      ((e.symm (Pi.single i (e p i)) : plusAlg σ J γ) : genAlg γ) := by
  have h : e.symm (Pi.single i 1) * p = e.symm (Pi.single i (e p i)) := by
    apply e.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [← h]; rfl

theorem factorIdem_mul_self (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    factorIdem e i * factorIdem e i = factorIdem e i := by
  have := factorIdem_mul e i (e.symm (Pi.single i 1))
  rw [AlgEquiv.apply_symm_apply, Pi.single_eq_same] at this
  exact this

theorem factorIdem_ne_zero (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) : factorIdem e i ≠ 0 := by
  intro h
  have h1 : e.symm (Pi.single i 1) = 0 := Subtype.ext (Subtype.ext h)
  have h2 := congrFun (e.symm_apply_eq.1 h1) i
  simp at h2

theorem factorIdem_selfAdj (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    cT (σ : E →+* E) (factorIdem e i) * J = J * factorIdem e i :=
  (e.symm (Pi.single i 1)).2

theorem factorIdem_orth (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    cT (σ : E →+* E) (1 - factorIdem e i) * J * factorIdem e i = 0 := by
  have hq : cT (σ : E →+* E) (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) * J =
      J * (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) :=
    (1 - e.symm (Pi.single i 1)).2
  have hc : (((1 - e.symm (Pi.single i 1) : plusAlg σ J γ) : genAlg γ) : Matrix (Fin n) (Fin n) E) =
      1 - factorIdem e i := rfl
  rw [hc] at hq
  rw [hq, Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, factorIdem_mul_self, sub_self, Matrix.mul_zero]

theorem factorIdem_comm (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    ∀ l ∈ genAlg γ, l * factorIdem e i = factorIdem e i * l := by
  intro l hl
  exact congrArg Subtype.val (mul_comm (⟨l, hl⟩ : genAlg γ) (e.symm (Pi.single i 1) : plusAlg σ J γ))

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem rank_factorIdem {γ : GL (Fin n) E} (hA : ClauseAlg σ J γ) (hP : ClausePlus σ J γ)
    (e : plusAlg σ J (γ : Matrix (Fin n) (Fin n) E) ≃ₐ[F] ∀ i, K i) (i : Fin k) :
    (factorIdem e i).rank = Module.finrank E (E ⊗[F] K i) := by
  obtain ⟨-, -, -, ⟨v, hv⟩, -⟩ := hA
  obtain ⟨-, -, hbij⟩ := hP
  let L := genAlg (γ : Matrix (Fin n) (Fin n) E)
  let P := plusAlg σ J (γ : Matrix (Fin n) (Fin n) E)
  let φ : L →ₗ[E] (Fin n → E) :=
    { toFun := fun l => (l : Matrix (Fin n) (Fin n) E) *ᵥ v
      map_add' := fun a b => Matrix.add_mulVec _ _ _
      map_smul' := fun c a => Matrix.smul_mulVec _ _ _ }
  let incl : P →ₗ[F] L := P.val.toLinearMap
  let ψ : E ⊗[F] P →ₗ[E] L := LinearMap.liftBaseChange E incl
  let ι : K i →ₗ[F] P := e.symm.toLinearMap ∘ₗ LinearMap.single F K i
  let Φ : E ⊗[F] K i →ₗ[E] (Fin n → E) := φ ∘ₗ ψ ∘ₗ ι.baseChange E
  have hψ : ∀ t, ψ t = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) (TensorProduct.comm F E P t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a p =>
      simp [ψ, incl, plusTensor, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def, mul_comm]; rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hψb : Function.Bijective ψ := by
    have : (ψ : E ⊗[F] P → L) = plusTensor σ J (γ : Matrix (Fin n) (Fin n) E) ∘ TensorProduct.comm F E P :=
      funext hψ
    rw [this]; exact hbij.comp (TensorProduct.comm F E P).bijective
  have hι : Function.Injective (ι.baseChange E) := by
    have h0 : Function.Injective ι := e.symm.injective.comp (Pi.single_injective i)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap ι h0
  have hΦ : Function.Injective Φ := hv.1.comp (hψb.1.comp hι)
  have hΦt : ∀ (a : E) (x : K i), Φ (a ⊗ₜ x) =
      a • ((((e.symm (Pi.single i x) : P) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v) := by
    intro a x
    simp [Φ, φ, ψ, ι, incl, LinearMap.liftBaseChange_tmul, Matrix.smul_mulVec]
  have hrange : LinearMap.range Φ = LinearMap.range (factorIdem e i).mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        refine ⟨a • ((((e.symm (Pi.single i x) : P) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v), ?_⟩
        rw [hΦt, Matrix.mulVecLin_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, factorIdem_mul]
        simp
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · rintro _ ⟨w, rfl⟩
      obtain ⟨l, rfl⟩ := hv.2 w
      obtain ⟨s, rfl⟩ := hψb.2 l
      change (factorIdem e i).mulVecLin (φ (ψ s)) ∈ LinearMap.range Φ
      induction s using TensorProduct.induction_on with
      | zero => simp [φ]
      | tmul a p =>
        refine ⟨a ⊗ₜ (e p i), ?_⟩
        rw [hΦt]
        simp only [ψ, incl, LinearMap.liftBaseChange_tmul, Matrix.mulVecLin_apply]
        have hc : (((a • (p : L)) : L) : Matrix (Fin n) (Fin n) E) = a • ((p : L) : Matrix (Fin n) (Fin n) E) := rfl
        change _ = factorIdem e i *ᵥ ((((a • (p : L)) : L) : Matrix (Fin n) (Fin n) E) *ᵥ v)
        rw [hc, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec, factorIdem_mul]
      | add x y hx hy =>
        rw [map_add, map_add, map_add]; exact add_mem hx hy
  rw [Matrix.rank, ← hrange, LinearMap.finrank_range_of_inj hΦ]

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt Formalism.UG Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}
  {J : Matrix (Fin n) (Fin n) E} {γ : Matrix (Fin n) (Fin n) E} {k : ℕ} {K : Fin k → Type}
  [∀ i, Field (K i)] [∀ i, Algebra F (K i)]

theorem eq_zero_of_mulVec {M : Matrix (Fin n) (Fin n) E} (h : ∀ w, M *ᵥ w = 0) : M = 0 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [Matrix.mulVec_single_one] using this

theorem rank_pos_of_ne_zero {M : Matrix (Fin n) (Fin n) E} (hM : M ≠ 0) : 0 < M.rank := by
  refine Nat.pos_of_ne_zero fun h => hM (eq_zero_of_mulVec fun w => ?_)
  rw [Matrix.rank, Submodule.finrank_eq_zero] at h
  have : M.mulVecLin w ∈ LinearMap.range M.mulVecLin := ⟨w, rfl⟩
  rw [h] at this
  exact (Submodule.mem_bot E).1 this

theorem eq_one_of_idem_rank {M : Matrix (Fin n) (Fin n) E} (hM : M * M = M) (hr : M.rank = n) : M = 1 := by
  have htop : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hr, Module.finrank_fin_fun]
  have hu : ∀ u, M *ᵥ u = u := by
    intro u
    obtain ⟨w, hw⟩ : u ∈ LinearMap.range M.mulVecLin := htop ▸ Submodule.mem_top
    rw [← hw, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hM]
  have h0 := eq_zero_of_mulVec (M := M - 1) fun w => by rw [Matrix.sub_mulVec, hu, Matrix.one_mulVec, sub_self]
  exact sub_eq_zero.1 h0

theorem two_le_of_decomp {P : Type} [CommRing P] [Algebra F P] {k' : ℕ} {K' : Fin k' → Type}
    [∀ i, Field (K' i)] [∀ i, Algebra F (K' i)] (e' : P ≃ₐ[F] ∀ i, K' i) (hk' : 2 ≤ k')
    (e : P ≃ₐ[F] ∀ i, K i) (i : Fin k) : ∃ j, j ≠ i := by
  by_contra hne
  simp only [not_exists, ne_eq, not_not] at hne
  let a : Fin k' := ⟨0, by omega⟩
  let b : Fin k' := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  let q : P := e'.symm (Pi.single a 1)
  have hqq : q * q = q := by
    apply e'.injective
    rw [map_mul, AlgEquiv.apply_symm_apply, ← Pi.single_mul, one_mul]
  have hq : IsIdempotentElem (e q i) := by
    show e q i * e q i = e q i
    rw [← Pi.mul_apply, ← map_mul, hqq]
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 hq with h | h
  · have : e q = 0 := funext fun j => by rw [hne j]; exact h
    have h2 := congrFun (e'.symm_apply_eq.1 (e.map_eq_zero_iff.1 this)) a
    simp at h2
  · have : e q = 1 := funext fun j => by rw [hne j]; exact h
    have h1 : q = 1 := by rw [← map_one e] at this; exact e.injective this
    have h2 := congrFun (e'.symm_apply_eq.1 h1) b
    simp [Pi.single_apply, hab.symm] at h2

theorem factorIdem_ne_one (e : plusAlg σ J γ ≃ₐ[F] ∀ i, K i) (i : Fin k) (hj : ∃ j, j ≠ i) :
    factorIdem e i ≠ 1 := by
  intro h
  obtain ⟨j, hj⟩ := hj
  have h1 : e.symm (Pi.single i 1) = 1 := Subtype.ext (Subtype.ext h)
  have h2 := congrFun (e.symm_apply_eq.1 h1) j
  simp [Pi.single_apply, hj] at h2

end GlobalTheory.FactorSplit

namespace GlobalTheory.FactorSplit
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt

theorem factorIdem_orthSplit_rank : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple → ∀ (D : D7) (V : HSp D) (γ : GF V), IsRegSS γ.1.1 → ∀ (k : ℕ) (Kf : Fin k → Type) [∀ i, Field (Kf i)] [∀ i, Algebra D.host.F (Kf i)] (e : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.plusAlg D.sp.cm.sig V.gram γ.1.1 ≃ₐ[D.host.F] ∀ i, Kf i) (i : Fin k), GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 → GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsOrthSplit D.sp.cm.sig V.gram γ.1.1 (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i) ∧ (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.factorIdem e i).rank = Module.finrank D.host.E (TensorProduct D.host.F D.host.E (Kf i)) := by
  intro hRS D V γ hss k Kf _ _ e i hnf
  have hreg := GlobalTheory.ConjLevi.RegularData.isRegular_of_isRegSS γ hss
  obtain ⟨hA, hP, -⟩ := hRS.1 D.host.F D.host.E (Fin V.rank) D.sp.cm.sig V.gram γ.1 hreg
  obtain ⟨-, k', K', _, _, ⟨e'⟩, hk', -⟩ := hnf
  have hj := two_le_of_decomp e' hk' e i
  refine ⟨⟨factorIdem_mul_self e i, factorIdem_selfAdj e i, factorIdem_orth e i, factorIdem_comm e i,
    rank_pos_of_ne_zero (factorIdem_ne_zero e i), lt_of_le_of_ne (Matrix.rank_le_width _) fun h =>
      factorIdem_ne_one e i hj (eq_one_of_idem_rank (factorIdem_mul_self e i) h)⟩,
    rank_factorIdem hA hP e i⟩

end GlobalTheory.FactorSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeriesAverageOtherPlaceTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_average_other_place_type : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ' (N.S τ') ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @GlobalTheory.AvgTypeOther.isTypeAt_avg_other | exact GlobalTheory.AvgTypeOther.isTypeAt_avg_other | (intros; apply GlobalTheory.AvgTypeOther.isTypeAt_avg_other <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeriesAveragePreservesTypeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_average_preserves_type : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (ψ : GA D N.V → ℂ), IsAutFunSm θ N.V ψ → IsTypeAt θ N.V τ (N.S τ) ψ → ∀ (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → IsTypeAt θ N.V τ (N.S τ) (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @GlobalTheory.AvgSamePlace.isTypeAt_avg | exact GlobalTheory.AvgSamePlace.isTypeAt_avg | (intros; apply GlobalTheory.AvgSamePlace.isTypeAt_avg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SetIntegralFdMulRight
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

theorem setIntegral_fd_mul_right : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {X : Node} (M : Vol G)
    {K : Subgroup (GL (Fin (G.V X).rank) (Formalism.IndefR.Lev.EAf D))}, M.IsAt X K → ∀ (k : GA D (G.V X)),
    MeasurePreserving (fun g : GA D (G.V X) => g * k) (M.ν X) (M.ν X) → Measurable (fun g : GA D (G.V X) => g * k⁻¹) →
    ∀ φ : GA D (G.V X) → ℂ, (∀ γ ∈ GQ (G.V X), ∀ g, φ (γ * g) = φ g) →
    ∫ g in M.fd X, φ (g * k) ∂M.ν X = ∫ g in M.fd X, φ g ∂M.ν X := by
  intro D T L sc G X M K hM k hk hk' φ hφ
  obtain ⟨hH, hF⟩ := hM.haar_fund
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (G.V X).gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig (G.V X).gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig (G.V X).gram
  haveI : Countable (GQ (G.V X)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (G.V X).gram
  haveI := hH
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ (G.V X))
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ (G.V X)) (M.ν X)

  let e : GA D (G.V X) ≃ᵐ GA D (G.V X) :=
    { toFun := fun g => g * k, invFun := fun g => g * k⁻¹,
      left_inv := fun g => by simp, right_inv := fun g => by simp,
      measurable_toFun := hk.measurable, measurable_invFun := hk' }

  have hF' : IsFundamentalDomain (GQ (G.V X)) ((fun g : GA D (G.V X) => g * k) ⁻¹' M.fd X) (M.ν X) :=
    hF.preimage_of_equiv hk.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc])
  rw [hF.setIntegral_eq hF' (f := fun g => φ (g * k)) (fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]; exact hφ γ γ.2 _)]
  exact hk.setIntegral_preimage_emb e.measurableEmbedding φ (M.fd X)

end GlobalTheory.RowReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRowGridBottomSelfDualLatticesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRowGrid_bottom_selfDual_lattices : All fun {D} _ {L} _ {G} _ _ => IsSelfDualC (Yc D 0) (L.ΛY 0) ∧ IsSelfDualC (G.V (.core 0)) (G.Λ (.core 0)) ∧ G.Λ (.core 0) = G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) ∧ zv G.sp.dec0 ∈ G.Λ (.core 0) ∧ (∀ k ∈ GfC (Yc D 0), Lev.finE (G.V (.core 0)) (stabilizerEmbedding G.sp.dec0 k) ∈ G.levCong (.core 0) → k ∈ levRow L) ∧ (Yc D 0).rank = D.R.r ∧ (G.V (.core 0)).rank = D.R.r + 1 ∧ ∀ (A : Fr (Yc D 0)) τ, (Finset.univ.filter fun a => A.ε τ a = false).card ≤ D.R.m := by
  first | exact @GlobalTheory.BottomGrid.bottom | exact GlobalTheory.BottomGrid.bottom | (intros; apply GlobalTheory.BottomGrid.bottom <;> assumption)
end

