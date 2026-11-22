import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0543
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0574
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0571
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockFrameChangeLastColumnDefinitePair
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open GlobalTheory.FockReal MvPolynomial
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FockFrameChange

private theorem sum4_lemma {α β γ δ R : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid R]
    (f : α → β → γ → δ → R) :
    ∑ k, ∑ l, ∑ k', ∑ l', f k l k' l' = ∑ k', ∑ l', ∑ k, ∑ l, f k l k' l' := by
  calc ∑ k, ∑ l, ∑ k', ∑ l', f k l k' l' = ∑ k, ∑ k', ∑ l, ∑ l', f k l k' l' :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k', ∑ k, ∑ l, ∑ l', f k l k' l' := Finset.sum_comm
    _ = ∑ k', ∑ k, ∑ l', ∑ l, f k l k' l' :=
        Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k', ∑ l', ∑ k, ∑ l, f k l k' l' := Finset.sum_congr rfl fun k' _ => Finset.sum_comm

theorem substF_mul {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) =
      GlobalTheory.CompactHowe.substF (fun τ => h τ * h' τ) (fun τ => g τ * g' τ) P := by
  unfold GlobalTheory.CompactHowe.substF
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  refine congrArg (fun F => (MvPolynomial.aeval F) P) (funext fun p => ?_)
  obtain ⟨τ, a, b⟩ := p
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.sum_mul_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine (sum4_lemma _).trans ?_
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun l' _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem change_mul {n : ℕ} {A F : Matrix (Fin n) (Fin n) ℂ} (hA : A * A⁻¹ = 1) (hF : F * F⁻¹ = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) : F⁻¹ * A * (A⁻¹ * M * A) = F⁻¹ * M * F * (F⁻¹ * A) := by
  calc F⁻¹ * A * (A⁻¹ * M * A) = F⁻¹ * (A * A⁻¹) * M * A := by simp only [Matrix.mul_assoc]
    _ = F⁻¹ * M * A := by rw [hA, Matrix.mul_one]
    _ = F⁻¹ * M * (F * F⁻¹) * A := by rw [hF, Matrix.mul_one]
    _ = F⁻¹ * M * F * (F⁻¹ * A) := by simp only [Matrix.mul_assoc]

theorem change_mul_invT {n : ℕ} {A F : Matrix (Fin n) (Fin n) ℂ} (hA : A * A⁻¹ = 1) (hF : F * F⁻¹ = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ((F⁻¹ * A)⁻¹).transpose * ((A⁻¹ * M * A)⁻¹).transpose = ((F⁻¹ * M * F)⁻¹).transpose * ((F⁻¹ * A)⁻¹).transpose := by
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.mul_inv_rev (F⁻¹ * A) (A⁻¹ * M * A),
    ← Matrix.mul_inv_rev (F⁻¹ * M * F) (F⁻¹ * A), change_mul hA hF M]

theorem subst_change {ι : Type} {N n : ℕ} {A F : ι → Matrix (Fin N) (Fin N) ℂ} {A' F' : ι → Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ τ, A τ * (A τ)⁻¹ = 1) (hF : ∀ τ, F τ * (F τ)⁻¹ = 1) (hA' : ∀ τ, A' τ * (A' τ)⁻¹ = 1)
    (hF' : ∀ τ, F' τ * (F' τ)⁻¹ = 1) (M : ι → Matrix (Fin N) (Fin N) ℂ) (M' : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * A τ).map (starRingEnd ℂ))
                 (fun τ => ((((F' τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ))
                 (GlobalTheory.CompactHowe.substF (fun τ => ((A τ)⁻¹ * M τ * A τ).map (starRingEnd ℂ))
                   (fun τ => ((((A' τ)⁻¹ * M' τ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) =
      GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * M τ * F τ).map (starRingEnd ℂ))
        (fun τ => ((((F' τ)⁻¹ * M' τ * F' τ)⁻¹).transpose).map (starRingEnd ℂ))
        (GlobalTheory.CompactHowe.substF (fun τ => ((F τ)⁻¹ * A τ).map (starRingEnd ℂ))
          (fun τ => ((((F' τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) := by
  rw [substF_mul, substF_mul]
  exact congrArg₂ (fun h g => GlobalTheory.CompactHowe.substF h g P)
    (funext fun τ => by
      simp only [← Matrix.map_mul]
      rw [change_mul (hA τ) (hF τ)])
    (funext fun τ => by
      simp only [← Matrix.map_mul]
      rw [change_mul_invT (hA' τ) (hF' τ)])

theorem map_mul_inv {n : ℕ} {E : Type} [Field E] (φ : E →+* ℂ) (g : GL (Fin n) E) :
    g.1.map φ * (g.1.map φ)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  have h := (Matrix.isUnits_det_units g).map φ
  rw [RingHom.map_det] at h
  exact h

private theorem fock_frame_lemma {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BS A' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT A : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hBS : ∀ τ, BS τ * (BS τ)⁻¹ = 1) (hBT : ∀ τ, BT τ * (BT τ)⁻¹ = 1)
    (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ) (hf : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) A' A f P =
      pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f
        (GlobalTheory.CompactHowe.substF (fun τ => ((BT τ)⁻¹ * A τ).map (starRingEnd ℂ))
          (fun τ => ((((BS τ)⁻¹ * A' τ)⁻¹).transpose).map (starRingEnd ℂ)) P) := by
  have e1 : A' = fun τ => BS τ * ((BS τ)⁻¹ * A' τ) := by
    funext τ
    rw [← Matrix.mul_assoc, hBS τ, Matrix.one_mul]
  have e2 : A = fun τ => BT τ * ((BT τ)⁻¹ * A τ) := by
    funext τ
    rw [← Matrix.mul_assoc, hBT τ, Matrix.one_mul]
  conv_lhs => rw [e1, e2]
  exact GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D ψ θ S T hψ hθ BS (fun τ => (BS τ)⁻¹ * A' τ) BT
    (fun τ => (BT τ)⁻¹ * A τ) f hf P

theorem exists_frame_change : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {μ0 : T},
    L.Is μ0 → ∀ (i : ℕ), i < D.R.m →
    ∃ σ₀ : PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank →ₗ[ℂ] PolF D (G.pT (.chi i D.R.m : Pair T)).rank (G.pS (.chi i D.R.m : Pair T)).rank,
      (∀ t ∈ U, ∀ d : FinDatum G t (.chi i D.R.m), S.Z.HasVec d → ∀ P,
        W.fock (.chi i D.R.m) (S.Z.vec d) P = fockIn W S.N.frC (.chi i D.R.m) (S.Z.vec d) (σ₀ P)) ∧
      ∀ k : GA D (G.V (.grid i D.R.m)), k ∈ GinfC (G.V (.grid i D.R.m)) →
        ∀ k' : GA D (G.V (.grid (i + 1) D.R.m)), k' ∈ GinfC (G.V (.grid (i + 1) D.R.m)) → ∀ P,
          σ₀ (realSubst W W.onb (.chi i D.R.m) k k' P) = realSubst W S.N.frC (.chi i D.R.m) k k' (σ₀ P) := by
  intro D T L sc G W U S μ0 hL i hi
  have hdT : DefNode D.R.m (Node.grid i D.R.m) := by
    unfold DefNode
    exact ⟨hi.le, rfl⟩
  have hdS : DefNode D.R.m (Node.grid (i + 1) D.R.m) := by
    unfold DefNode
    exact ⟨hi, rfl⟩
  have hdP : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := by
    unfold DefPair
    exact ⟨hi, rfl⟩
  have honb : ∀ X, DefNode D.R.m X → ∀ τ, W.onb X τ * (W.onb X τ)⁻¹ = 1 := fun X hX τ =>
    Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse (GlobalTheory.FockReal.onb_def hL W hX τ))
  have hfr : ∀ X τ, S.N.frC X τ * (S.N.frC X τ)⁻¹ = 1 := fun X τ => map_mul_inv (tauE D τ) (S.N.fr X)
  refine ⟨(GlobalTheory.CompactHowe.substF
      (fun τ => ((S.N.frC (Node.grid i D.R.m) τ)⁻¹ * W.onb (Node.grid i D.R.m) τ).map (starRingEnd ℂ))
      (fun τ => ((((S.N.frC (Node.grid (i + 1) D.R.m) τ)⁻¹ * W.onb (Node.grid (i + 1) D.R.m) τ)⁻¹).transpose).map
        (starRingEnd ℂ))).toLinearMap, ?_, ?_⟩
  · intro t _ d hd P
    have hf := (GlobalTheory.FockRealVec.vec_theta_fock W S.Z hdP d hd).1
    have hcS : G.cartS W.cart (Pair.chi i D.R.m : Pair T) = fun _ => -1 := by
      funext τ
      show -W.cart (Node.grid (i + 1) D.R.m) τ = -1
      rw [GlobalTheory.FockReal.cart_def hL W hdS τ]
    have hcT : G.onT W.cart (Pair.chi i D.R.m : Pair T) = fun _ => 1 := by
      funext τ
      exact GlobalTheory.FockReal.cart_def hL W hdT τ
    unfold GlobalTheory.ChiGrid.GridData.Weil.fock GlobalTheory.FunObj.fockIn
    rw [hcS, hcT, AlgHom.toLinearMap_apply]
    exact fock_frame_lemma W.ψ W.θ (G.V (Node.grid (i + 1) D.R.m)) (G.V (Node.grid i D.R.m)) W.ψ_std W.θ_is
      (S.N.frC (Node.grid (i + 1) D.R.m)) (W.onb (Node.grid (i + 1) D.R.m))
      (S.N.frC (Node.grid i D.R.m)) (W.onb (Node.grid i D.R.m))
      (hfr _) (hfr _) (S.Z.vec d) hf P
  · intro k _ k' _ P
    unfold GlobalTheory.FockReal.realSubst
    rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply]
    exact subst_change (A := W.onb (Node.grid i D.R.m)) (F := S.N.frC (Node.grid i D.R.m))
      (A' := W.onb (Node.grid (i + 1) D.R.m)) (F' := S.N.frC (Node.grid (i + 1) D.R.m))
      (fun τ => honb _ hdT τ) (hfr _) (fun τ => honb _ hdS τ) (hfr _) _ _ P

end GlobalTheory.FockFrameChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieWordExpansion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.PlaceDecomp

theorem exists_expn_model : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (f : GA D N.V → ℂ), IsAutFunSm θ N.V f → IsTypeAt θ N.V τ (N.S τ) f → ∀ x : GA D N.V, ∃ (S : List (List (Mx N.V.rank))) (v : ℕ → N.M.H τ) (ℓ : ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : ℕ → ℝ), Words (lieSet (N.M.ε τ)) S ∧ Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) S ∧ Expn (N.M.ε τ) (N.M.σ τ) S v ℓ C (res θ N.V τ (N.M.fr τ) f x) := by
  intro D θ hθ hPr N τ f hf hty x
  obtain ⟨H', i1, i2, σ', lam', ε', P', hE', hD', hP', hJ', hx⟩ := hty
  obtain ⟨hl, he⟩ := GlobalTheory.SignedParTest.isEnum_unique (N.M.enum τ) hE'
  subst hl he
  obtain ⟨U, hU⟩ := hPr.discreteSeriesHermitianUnique _ (N.M.ε τ) (N.M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (N.M.enum τ).1 (N.M.ds τ)) _ (N.M.fr τ) P'
    (N.M.fr_unit τ) hP' (N.M.fr_gram τ) hJ' _ _ (N.M.σ τ) σ' (N.M.ds τ) hD'
  have t := GlobalTheory.TypeSum.hasTypeAll_transport _ H' (N.M.H τ) (fun g => σ' (P' * g * P'⁻¹)) (N.M.σ τ)
    (gramAt D N.V τ) (Formalism.REAL.Jm (N.M.ε τ)) (N.M.fr τ) (isUnit_gram (N.M.fr_unit τ) (N.M.fr_gram τ))
    (N.M.fr_unit τ) (N.M.fr_gram τ) U hU (fun g => f (x * atTau θ N.V τ g))
    (GlobalTheory.TypeSum.hasTypeAll_iff.2 (hx x))
  obtain ⟨S, hS, hc, v, ℓ, C, h⟩ := t
  exact ⟨S, v, ℓ, C, hS, hc, h⟩

end GlobalTheory.PlaceDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalProjectionPosDefSesquilinearFini
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem exists_proj_sesq_posDef_finiteDim : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (F : Submodule ℂ M), FiniteDimensional ℂ F →
    (∀ x ∈ F, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ F, ∀ y ∈ F, star (b x y) = b y x) →
    ∃ e : M →ₗ[ℂ] M, (∀ x, e x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (e x) f = b x f := by
  intro M _ _ b F hF hpos hherm
  classical
  set n := Module.finrank ℂ F
  let v : Module.Basis (Fin n) ℂ F := Module.finBasis ℂ F
  let A : F →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => (b (v i : M)).comp F.subtype)
  let B : M →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x i => star (b x (v i : M))
      map_add' := by intro x y; funext i; simp [map_add]
      map_smul' := by intro c x; funext i; simp [mul_comm] }
  have key : ∀ (y : F) (x : M), (∀ i, b (v i : M) (y : M) = star (b x (v i : M))) →
      ∀ f ∈ F, b (y : M) f = b x f := by
    intro y x h f hf
    have hc : (b (y : M)).comp F.subtype = (b x).comp F.subtype := by
      refine v.ext (fun i => ?_)
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [← hherm _ (v i).2 _ y.2, h i, star_star]
    have := LinearMap.congr_fun hc ⟨f, hf⟩
    simpa using this
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∀ i, b (v i : M) (y : M) = star (b (0 : M) (v i : M)) := by
      intro i
      have := congrFun hy i
      simpa [A] using this
    have hyy := key y 0 h0 y y.2
    by_contra hne
    have hne' : (y : M) ≠ 0 := by simpa using hne
    have := hpos y y.2 hne'
    rw [hyy] at this
    simp at this
  have hdim : Module.finrank ℂ F = Module.finrank ℂ (Fin n → ℂ) := by simp [n]
  let Aeq := LinearMap.linearEquivOfInjective A hinj hdim
  refine ⟨F.subtype.comp (Aeq.symm.toLinearMap.comp B), fun x => (Aeq.symm (B x)).2, ?_⟩
  intro x f hf
  show b ((Aeq.symm (B x) : F) : M) f = b x f
  refine key (Aeq.symm (B x)) x ?_ f hf
  intro i
  have h1 : A (Aeq.symm (B x)) = B x := by
    exact Aeq.apply_symm_apply (B x)
  have := congrFun h1 i
  simpa [A, B] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPartialFourierColumnBlockSchwartzBruhat
section
namespace GlobalTheory.ColFourier
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {A C : Type} [Fintype A] [DecidableEq C]

theorem fourierInt_add (ψ : AddChar k Circle) (m : Measure k) (hψ : HasConductor ψ 1) (hm : IsUnitVol m)
    (P : Finset C) {Ξ₁ Ξ₂ : Matrix A C k → ℂ} (h₁ : Ξ₁ ∈ SB (Matrix A C k)) (h₂ : Ξ₂ ∈ SB (Matrix A C k)) :
    fourierInt ψ m P (Ξ₁ + Ξ₂) = fourierInt ψ m P Ξ₁ + fourierInt ψ m P Ξ₂ := by
  haveI := hm.1
  haveI := secondCountable k
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : BorelSpace (Matrix A P k) := inferInstanceAs (BorelSpace (A → P → k))
  have hi : ∀ Ξ ∈ SB (Matrix A C k), ∀ Y : Matrix A C k,
      Integrable (fun U => Ξ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ)) (volM m A P) := by
    intro Ξ hΞ Y
    have hg := comp_setCols_mem_SB hΞ P Y
    have hc : Continuous fun U : Matrix A P k => pairCols P Y U := by unfold pairCols; fun_prop
    exact (hg.1.continuous.integrable_of_hasCompactSupport hg.2).mul_bdd (c := 1)
      ((continuous_subtype_val.comp (hψ.continuous.comp hc)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun U => (Circle.norm_coe _).le)
  funext Y
  simp only [fourierInt, Pi.add_apply, add_mul]
  exact integral_add (hi _ h₁ Y) (hi _ h₂ Y)

theorem fourierInt_shift [Fintype C] (ψ : AddChar k Circle) (m : Measure k) (hm : IsUnitVol m) (P : Finset C)
    (Ξ : Matrix A C k → ℂ) (T R : Matrix A C k) (hT : ∀ r, ∀ s ∉ P, T r s = 0) (hR : ∀ r, ∀ s ∈ P, R r s = 0) :
    fourierInt ψ m P (fun S => (ψ (GlobalTheory.FlipMatch.pairM S R) : ℂ) * Ξ (S + T)) =
      fun Z => (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) * fourierInt ψ m P Ξ Z := by
  haveI := hm.1
  haveI := isAddHaarMeasure_volM m (A := A) P
  haveI : MeasurableAdd (Matrix A P k) := inferInstanceAs (MeasurableAdd (A → P → k))
  funext Z
  unfold fourierInt
  set Tp := restrictCols P T
  rw [← integral_add_right_eq_self (μ := volM m A P)
    (fun U => Ξ (setCols P Z U) * (ψ (pairCols P Z U) : ℂ)) Tp, ← integral_const_mul]
  congr 1
  funext U
  have ea : GlobalTheory.FlipMatch.pairM (setCols P Z U) R = GlobalTheory.FlipMatch.pairM Z R := by
    simp only [GlobalTheory.FlipMatch.pairM]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j ∈ P
    · simp [setCols, h, hR i j h]
    · simp [setCols, h]
  have eb : setCols P Z U + T = setCols P Z (U + Tp) := by
    ext i j
    by_cases h : j ∈ P
    · simp [setCols, h, Tp, restrictCols]
    · simp [setCols, h, hT i j h]
  have ec : pairCols P Z (U + Tp) = pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T := by
    simp only [pairCols, GlobalTheory.FlipMatch.pairM, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [hT i j hj]),
      ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Tp, restrictCols]
    ring
  have key : (ψ (GlobalTheory.FlipMatch.pairM Z R - GlobalTheory.FlipMatch.pairM Z T) : ℂ) *
      ψ (pairCols P Z U + GlobalTheory.FlipMatch.pairM Z T) = ψ (GlobalTheory.FlipMatch.pairM Z R) * ψ (pairCols P Z U) := by
    rw [← Circle.coe_mul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2; ring
  dsimp only
  rw [ea, eb, ec]
  linear_combination (Ξ (setCols P Z (U + Tp))) * key.symm

end GlobalTheory.ColFourier

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

theorem GlobalTheory.ColFourier.exists_blockFourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∃ 𝓕 : (Matrix A C k → ℂ) →ₗ[ℂ] (Matrix A C k → ℂ), Set.BijOn 𝓕 (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∈ P, T r s = 0) → (∀ r, ∀ s ∉ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => 𝓕 Ξ (Z + (T + R))) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∉ P, T r s = 0) → (∀ r, ∀ s ∈ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => (ψ (pairM Z R - pairM Z T) : ℂ) * 𝓕 Ξ Z) ∧
      ∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ n, IsNatDatum ϖ n (𝓕 Ξ) → fourierSum ψ⁻¹ ϖ n P (𝓕 Ξ) = Ξ := by
  intro k _ _ _ _ A _ _ C _ _ ψ ϖ P hϖ hψ
  borelize k
  obtain ⟨m, hm⟩ := exists_isUnitVol k
  haveI := hm.1
  have hψ' : HasConductor ψ⁻¹ 1 := GlobalTheory.ColFourier.hasConductor_inv hψ
  have hSB := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => GlobalTheory.T.partialColumnFourier_mem_schwartzBruhat k A C χ m hχ hm P Ξ h
  have hInv := fun (χ : AddChar k Circle) (hχ : HasConductor χ 1) (Ξ : Matrix A C k → ℂ)
    (h : Ξ ∈ SB (Matrix A C k)) => GlobalTheory.T.partialColumnFourier_inversion_schwartzBruhat k A C χ m hχ hm P Ξ h
  let L : SB (Matrix A C k) →ₗ[ℂ] (Matrix A C k → ℂ) :=
    { toFun := fun Ξ => fourierInt ψ m P Ξ
      map_add' := fun a b => GlobalTheory.ColFourier.fourierInt_add ψ m hψ hm P a.2 b.2
      map_smul' := fun c a => by
        funext Y
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, fourierInt]
        rw [← integral_const_mul]
        congr 1; funext U; ring }
  obtain ⟨F, hF⟩ := LinearMap.exists_extend L
  have hFe : ∀ Ξ ∈ SB (Matrix A C k), F Ξ = fourierInt ψ m P Ξ := fun Ξ h => LinearMap.congr_fun hF ⟨Ξ, h⟩
  have hmod : ∀ Ξ ∈ SB (Matrix A C k), ∀ T R : Matrix A C k,
      (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) ∈ SB (Matrix A C k) := by
    intro Ξ hΞ T R
    have hc : Continuous fun S : Matrix A C k => pairM S R := by unfold pairM; fun_prop
    refine ⟨((hψ.isLocallyConstant.comp_continuous hc).comp (fun z : Circle => (z : ℂ))).mul
      (hΞ.1.comp_continuous (continuous_add_right T)), ?_⟩
    exact (hΞ.2.comp_homeomorph (Homeomorph.addRight T)).mul_left
  refine ⟨F, ⟨fun Ξ h => ?_, fun Ξ₁ h₁ Ξ₂ h₂ he => ?_, fun Ψ hΨ => ?_⟩, fun Ξ hΞ T R hT hR => ?_,
    fun Ξ hΞ T R hT hR => ?_, fun Ξ hΞ n hn => ?_⟩
  · show F Ξ ∈ SB (Matrix A C k)
    rw [hFe Ξ h]; exact hSB ψ hψ Ξ h
  · rw [hFe _ h₁, hFe _ h₂] at he
    rw [← hInv ψ hψ Ξ₁ h₁, ← hInv ψ hψ Ξ₂ h₂, he]
  · have h1 := hSB ψ⁻¹ hψ' Ψ hΨ
    refine ⟨_, h1, ?_⟩
    rw [hFe _ h1]
    simpa only [inv_inv] using hInv ψ⁻¹ hψ' Ψ hΨ
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    funext Z
    unfold fourierInt
    congr 1
    funext U
    have e1 : setCols P Z U + T = setCols P (Z + (T + R)) U := by
      ext i j
      by_cases h : j ∈ P
      · simp [setCols, h, hT i j h]
      · simp [setCols, h, hR i j h]
    have e2 : pairM (setCols P Z U) R + pairCols P Z U = pairCols P (Z + (T + R)) U := by
      simp only [pairM, pairCols, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ P) (fun j _ hj => by simp [setCols, hj, hR i j hj]),
        ← Finset.sum_coe_sort P, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [setCols, j.2, hT i j j.2]
      ring
    dsimp only
    rw [e1, ← e2, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  · rw [hFe _ (hmod Ξ hΞ T R), hFe _ hΞ]
    exact GlobalTheory.ColFourier.fourierInt_shift ψ m hm P Ξ T R hT hR
  · rw [hFe _ hΞ] at hn ⊢
    rw [← GlobalTheory.T.partialColumnFourier_eq_finiteFourierSum_depth k A C ψ⁻¹ m ϖ hϖ hψ' hm P n _ hn]
    exact hInv ψ hψ Ξ hΞ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalSplitStabilizerDecompositionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_split_stabilizer_decomposition : ∀ {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E) (N : ℕ), 0 < N → ∀ g : GfC V,
    ∃ r s k : GfC V, GlobalTheory.MovedKappaEx.RatFin V r ∧ GlobalTheory.UnRep.SuppSplit (GlobalTheory.Member.cF D) N (finHom V s.1).1 ∧
      (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE V k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat B)) ∧ g = r * s * k := by
  first | exact @GlobalTheory.RatSplitLat.exists_rat_split_lat | exact GlobalTheory.RatSplitLat.exists_rat_split_lat | (intros; apply GlobalTheory.RatSplitLat.exists_rat_split_lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumIsAlgebraicCombinationDefiniteBottomStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_isAlgebraicCombination_definiteBottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X →
    ∀ t : T, GlobalTheory.MovedAlg.IsAlgComb W.ψ A' WW X.vac' (X.f' t) := by
  first | exact @GlobalTheory.BotFourierSnd.finDatum'_isAlgComb | exact GlobalTheory.BotFourierSnd.finDatum'_isAlgComb | (intros; apply GlobalTheory.BotFourierSnd.finDatum'_isAlgComb <;> assumption)
end

