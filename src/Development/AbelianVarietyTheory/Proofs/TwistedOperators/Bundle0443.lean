import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaTraceBaseChangeIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulNonsingInvCancelRightGram
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0310
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalDarbouxOrientedPairTransport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem hTens_eq_trace {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    GlobalTheory.WeilM.hTens c JA JB x y = (xᵀ * JA * y.map c * JBᵀ).trace := by
  simp only [GlobalTheory.WeilM.hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ i, ∑ k, ∑ l, x i j * JA i k * JB j l * c (y k l)
      = ∑ i, ∑ l, ∑ k, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k, x i j * JA i k * JB j l * c (y k l) := Finset.sum_comm
    _ = ∑ l, ∑ k, ∑ i, x i j * JA i k * JB j l * c (y k l) :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun i _ => ?_
        ring

theorem hTens_transpose_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β γ : Type}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] (e : α ≃ γ) (K : Matrix α α A) {G H : Matrix β β A} (x : A)
    (hGH : H * G = 1) (hG : G.map c = Gᵀ) (u u' : Matrix β γ A) :
    GlobalTheory.WeilM.hTens c Kᵀ (x • H) (uᵀ.submatrix e id * G) (u'ᵀ.submatrix e id * G) =
      -GlobalTheory.WeilM.hTens c (-G) (x • reindex e e Kᵀ) u u' := by
  have hHG : Gᵀ * Hᵀ = 1 := by rw [← Matrix.transpose_mul, hGH, Matrix.transpose_one]
  have hmap : (u'ᵀ.submatrix e id * G).map c = (u'ᵀ.submatrix e id).map c * Gᵀ := by
    rw [← hG]
    exact Matrix.map_mul (f := (c : A →+* A))
  have hM : ((u'ᵀ.submatrix e id).map c)ᵀ * K * uᵀ.submatrix e id = u'.map c * reindex e e K * uᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
      Matrix.reindex_apply]
    refine Fintype.sum_equiv e _ _ fun a => ?_
    congr 1
    exact Fintype.sum_equiv e _ _ fun b => by simp
  rw [hTens_eq_trace, hTens_eq_trace, hmap, Matrix.transpose_mul, Matrix.transpose_smul]
  calc (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * ((u'ᵀ.submatrix e id).map c * Gᵀ) * (x • Hᵀ)).trace
      = x * (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * (u'ᵀ.submatrix e id).map c * (Gᵀ * Hᵀ)).trace := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        simp only [Matrix.mul_assoc]
    _ = x * (Gᵀ * (uᵀ.submatrix e id)ᵀ * Kᵀ * (u'ᵀ.submatrix e id).map c).trace := by
        rw [hHG, Matrix.mul_one]
    _ = x * (((u'ᵀ.submatrix e id).map c)ᵀ * K * uᵀ.submatrix e id * G).trace := by
        congr 1
        rw [← Matrix.trace_transpose]
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    _ = x * (u'.map c * reindex e e K * uᵀ * G).trace := by rw [hM]
    _ = x * (uᵀ * G * u'.map c * reindex e e K).trace := by
        rw [Matrix.mul_assoc (u'.map c * reindex e e K), Matrix.trace_mul_comm]
        simp only [Matrix.mul_assoc]
    _ = -((uᵀ * -G * u'.map c * (x • reindex e e Kᵀ)ᵀ).trace) := by
        rw [Matrix.transpose_smul, Matrix.transpose_reindex, Matrix.transpose_transpose, Matrix.mul_neg,
          Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_smul, Matrix.trace_neg, Matrix.trace_smul, neg_neg,
          smul_eq_mul]

theorem exists_darboux_transpose_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β γ κ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype κ] [DecidableEq β] (e : α ≃ γ) (K : Matrix α α A)
    {G H : Matrix β β A} (x : A) (hGH : H * G = 1) (hG : G.map c = Gᵀ) {JV JB : Matrix β β A} {JW : Matrix γ γ A}
    {JA : Matrix α α A} (hV : JV = -G) (hW : JW = x • reindex e e Kᵀ) (hA : JA = Kᵀ) (hB : JB = x • H)
    (M : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c (-1) JV JW) κ) (T : Matrix β γ A ≃+ Matrix α β A)
    (hT : ∀ u, T u = uᵀ.submatrix e id * G) :
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp c 1 JA JB) κ, ∀ u, co.e (T u) = M.e u := by
  subst hV hW hA hB
  have hsmul : ∀ (r : R) (u : Matrix β γ A), T (r • u) = r • T u := by
    intro r u
    rw [hT, hT, Matrix.transpose_smul]
    exact Matrix.smul_mul r (uᵀ.submatrix e id) G
  have h1 : ∀ v, (T.toLinearEquiv hsmul).symm (T v) = v := fun v => (T.toLinearEquiv hsmul).symm_apply_apply v
  refine ⟨{ e := (T.toLinearEquiv hsmul).symm.trans M.e, form := ?_ }, ?_⟩
  · intro w w'
    obtain ⟨u, rfl⟩ := T.surjective w
    obtain ⟨u', rfl⟩ := T.surjective w'
    simp only [LinearEquiv.trans_apply]
    rw [h1, h1, ← M.form]
    simp only [GlobalTheory.WeilM.symp]
    rw [hT, hT, hTens_transpose_mul c e K x hGH hG, one_mul, neg_one_mul]
  · intro u
    simp only [LinearEquiv.trans_apply]
    rw [h1]

theorem map_transpose_inv_mul {E A : Type} [CommRing E] [CommRing A] (f : E →+* A) {α β γ : Type} [Fintype β]
    [DecidableEq β] (e : α ≃ γ) (x : Matrix α β E) {G : Matrix β β E} (hG : IsUnit G.det) :
    (((x * G⁻¹)ᵀ.submatrix id e.symm).map f)ᵀ.submatrix e id * G.map f = x.map f := by
  have h1 : (((x * G⁻¹)ᵀ.submatrix id e.symm).map f)ᵀ.submatrix e id = (x * G⁻¹).map f := by
    ext a b
    simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, Equiv.symm_apply_apply]
  rw [h1, ← Matrix.map_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.mul_one]

private theorem symp_smul_eq_symp_one_smul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type}
    [Fintype α] [Fintype β] (ξ : A) (JA : Matrix α α A) (JB : Matrix β β A) (w w' : Matrix α β A) :
    GlobalTheory.WeilM.symp c ξ JA JB w w' = GlobalTheory.WeilM.symp c 1 JA (ξ • JB) w w' := by
  simp only [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens, one_mul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

set_option maxHeartbeats 800000 in

theorem exists_darboux_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
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
      ∃ (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) (Fin S.rank × Fin d)),
        ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) ∧
        (∀ x : Matrix (Fin X.rank) (Fin S.rank) D.host.E, ∃ y z : Fin S.rank × Fin d → D.host.F,
          co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
            (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) ∧
        ∀ (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ) (f : WO S X → ℂ),
          IsDatum M ψ cS Φ f ↔
            Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin S.rank × Fin d) ∧ GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ = f := by
  intro D ψ θ _ ε S X A B d e Bs _ _ Vs Ws r s r' s' hJ hJW hV _ _ M hM cS hcS
  have hsgn : (sgn ε S).gram = (if ε then -1 else 1 : D.host.E) • S.gram := by
    cases ε <;> ext i j <;> simp [Formalism.BasicNotions.HSpace.gram]
  have hdet : IsUnit (sgn ε S).gram.det := isUnit_iff_ne_zero.mpr (Formalism.L2.Theta.gram_det_ne _)
  have hG0 : (sgn ε S).gram = -Vs.J := by
    rw [hsgn, hJ]
    cases ε <;> simp
  have hmapc : ∀ {m n : Type} (J : Matrix m n D.host.E),
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (J.map D.sp.cm.sig) := by
    intro m n J
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]
  have hGJ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram := by
    rw [hG0]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  have hG : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram)ᵀ := by
    rw [hmapc, hG0]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hV.herm]
  have hGH : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((sgn ε S).gram)⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram = 1 := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0 •
      reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram)ᵀ := by
    rw [hJW]
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.reindex_apply, map_mul]
  have hT : ∀ u, cS u = uᵀ.submatrix e id * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (sgn ε S).gram := by
    intro u
    rw [hcS u, hsgn]
  obtain ⟨co0, hco0⟩ := exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gram) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0)
    hGH hG hGJ hW rfl rfl M.co cS hT
  obtain ⟨co, hco⟩ : ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((sgn ε S).gram)⁻¹))
      (Fin S.rank × Fin d), (∀ u, co.e (cS u) = M.co.e u) ∧ ∀ w, co.e w = co0.e w := by
    refine ⟨⟨co0.e, fun w w' => ?_⟩, hco0, fun _ => rfl⟩
    rw [← co0.form, symp_smul_eq_symp_one_smul]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]
  refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (AF D.host.F) D.host.xi0, ((sgn ε S).gram)⁻¹, co, ?_, ?_, ?_⟩
  · ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, map_mul]
  · intro y
    obtain ⟨a, b, hab⟩ := hM.rat ((y * ((sgn ε S).gram)⁻¹)ᵀ.submatrix id e.symm)
    refine ⟨a, b, ?_⟩
    have hu : cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F ((y * ((sgn ε S).gram)⁻¹)ᵀ.submatrix id e.symm)) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F y := by
      rw [hT]
      exact map_transpose_inv_mul _ e y hdet
    rw [← hu, hco.1]
    exact hab
  · intro Φ f
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, funext fun w => ?_⟩
      obtain ⟨u, rfl⟩ := cS.surjective w
      rw [← h2 u]
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco.1 u]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun u => ?_⟩
      rw [← h2]
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco.1 u]

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalIsometryOfTraceSimilitudeSqStatement
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_isometry_of_trace_similitude_sq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) → ∀ (gam : X.Λ →ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * herm X'.Gm (gam u : Fin r → E) (gam v : Fin r → E)) = (N : ℚ) ^ 2 * Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (u : Fin r → E) (v : Fin r → E))) → (∀ w : X'.Λ, ∃ v, gam v = (N ^ 2) • w) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E)) = (gam v : Fin r → E)) ∧ (∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ) ∧ ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * herm X.Gm u v := by
  first | exact @GlobalTheory.TraceSimilitude.exists_gl_of_trace_similitude | exact GlobalTheory.TraceSimilitude.exists_gl_of_trace_similitude | (intros; apply GlobalTheory.TraceSimilitude.exists_gl_of_trace_similitude <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalPointThetaGeneratorNeZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalPoint_thetaGenerator_ne_zero : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x₁ : Sp Ω ⟶ Xo.X} {s : LB.Sec (PPx x₁)}, IsThGen x₁ s → ∃ w : Sp Ω ⟶ Gx x₁, w ≫ (fst (Over.mk x₁) Xo.univ.t.G).left = 𝟙 _ ∧ ∀ (z : Sp Ω) (J : (Sp Ω ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s w z J ≠ 0 := by
  first | exact @GlobalTheory.ThetaNZ.exists_ratPt_sv_ne_zero | exact GlobalTheory.ThetaNZ.exists_ratPt_sv_ne_zero | (intros; apply GlobalTheory.ThetaNZ.exists_ratPt_sv_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRigidifiedThetaIsoBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaTraceBC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

theorem exists_isRigIso_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} {pm : Gx x₁ ⟶ Gx x} {pm' : Gx x₁' ⟶ Gx x'} {k : ℤ} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ k)}, IsCan χ pm → IsCan χ pm' → Ψ₁ ≫ pm' = pm ≫ Ψ → Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ k β → ∃ β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k), IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ₁ k β₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → val β₁ r z J = val β (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x' x₁ x₁' Ψ Ψ₁ pm pm' k β hc hc' hΨ h0 hβ
  let σ : (Over.mk x₁ : Over Xo.X) ⟶ Over.mk x := Over.homMk (spMap χ) hc.1.symm
  let σ' : (Over.mk x₁' : Over Xo.X) ⟶ Over.mk x' := Over.homMk (spMap χ) hc'.1.symm
  have epm : pm = (σ ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [hc.2.2, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [hc.2.1, ← Over.comp_left, whiskerRight_snd])
  have epm' : pm' = (σ' ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [hc'.2.2, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [hc'.2.1, ← Over.comp_left, whiskerRight_snd])
  obtain ⟨β₁, h₁, hv⟩ := isRigIso_pull (σ := σ) (σ' := σ') rfl (by rw [← epm, ← epm']; exact hΨ) h0 hβ
  exact ⟨β₁, h₁, fun Z r z J hJ => by rw [hv r z hJ, ← epm]⟩

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaLineGeneratorZariskiLocallyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaLine_generator_zariski_locally : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : Type) [CommRing T] [Algebra c.F T] (x : Sp T ⟶ Xo.X), x ≫ Xo.s = sOf c T → ∀ q : PrimeSpectrum T, ∃ g : T, g ∉ q.asIdeal ∧ ∃ s : LB.Sec (PPx (spMap (algebraMap T (Localization.Away g)) ≫ x)), SecGen _ s := by
  first | exact @GlobalTheory.HeckeEx.exists_secGen_away | exact GlobalTheory.HeckeEx.exists_secGen_away | (intros; apply GlobalTheory.HeckeEx.exists_secGen_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTraceEqFinsumGeometricPointsEtaleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trace_eq_finsum_geometric_points_etale : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], Module.Finite R B → Algebra.Etale R B → ∀ b : B, ∃ v : R, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), φ v = ∑ᶠ χ : {χ : B →+* Ω // χ.comp (algebraMap R B) = φ}, χ.1 b := by
  first | exact @GlobalTheory.EtaleTraceGeom.exists_trace_eq_finsum | exact GlobalTheory.EtaleTraceGeom.exists_trace_eq_finsum | (intros; apply GlobalTheory.EtaleTraceGeom.exists_trace_eq_finsum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilDatumOneParameterGeneratorCommutatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilDatum_oneParameter_generator_commutators : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : OmT S T), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (τ : D.what₂.Tau), ∀ X ∈ lieAt S τ, ∀ Y ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u f) - Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (Y * u - u * X) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u f) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ (∀ w, HasDerivAt (fun t : ℝ => om (oneP θ S τ X t, oneP θ T τ Y t) f w) (Gn f w) 0) ∧ ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ g, IsThetaFunO ψ S T g → HasDerivAt (fun t : ℝ => ipO μ 𝓕 (om (oneP θ S τ X t, oneP θ T τ Y t) f) g) (ipO μ 𝓕 (Gn f) g) 0 := by
  first | exact @GlobalTheory.PlaceTensor.GenPair.exists_generator | exact GlobalTheory.PlaceTensor.GenPair.exists_generator | (intros; apply GlobalTheory.PlaceTensor.GenPair.exists_generator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FibreIsogenyPairDefinedOverFiniteSubextensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreIsogenyPair_defined_over_finite_subextension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (g : Fib Xo w ⟶ Fib Xo w') (g' : Fib Xo w' ⟶ Fib Xo w), φ.IsIntegral → w = spMap φ ≫ x → w' = spMap φ ≫ x' → IsMonHom g → IsMonHom g' → ∃ (M : Type) (_ : Field M) (i : K →+* M) (j : M →+* L), j.comp i = φ ∧ i.Finite ∧ ∀ v v' : Sp M ⟶ Xo.X, v = spMap i ≫ x → v' = spMap i ≫ x' → ∃ (f : Fib Xo v ⟶ Fib Xo v') (f' : Fib Xo v' ⟶ Fib Xo v), IsBC j f g ∧ IsBC j f' g' := by
  first | exact @GlobalTheory.HkIntegral.pair_defined_over_finite | exact GlobalTheory.HkIntegral.pair_defined_over_finite | (intros; apply GlobalTheory.HkIntegral.pair_defined_over_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteClassesRationalIsometriesBoundedDenominatoStatement
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_classes_rational_isometries_bounded_denominator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (N : ℕ), 0 < N → ∃ S : Finset (GL (Fin r) E), (∀ s ∈ S, QMatch X X' N s) ∧ ∀ a, QMatch X X' N a → ∃ s ∈ S, ∃ b ∈ X'.Γ, a = b * s := by
  first | exact @GlobalTheory.HeckeEx.QFin.finite_reps | exact GlobalTheory.HeckeEx.QFin.finite_reps | (intros; apply GlobalTheory.HeckeEx.QFin.finite_reps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLie
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.AlgStable

theorem isStable_span {D : D7} (θ : InfFam D) (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ))
    (s : Set (Z → ℂ)) (h1 : ∀ g ∈ GfC X, ∀ Φ ∈ s, ρ g Φ ∈ Submodule.span ℂ s)
    (h2 : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ s, ∃ Φ' ∈ Submodule.span ℂ s, GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsDer θ X ρ τ Y Φ Φ') :
    GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints.IsStable θ X ρ (Submodule.span ℂ s) := by
  refine ⟨fun g hg Φ hΦ => ?_, fun τ Y hY Φ hΦ => ?_⟩
  · have hle : Submodule.span ℂ s ≤ (Submodule.span ℂ s).comap (ρ g) := Submodule.span_le.2 (h1 g hg)
    exact hle hΦ
  · induction hΦ using Submodule.span_induction with
    | mem x hx => exact h2 τ Y hY x hx
    | zero =>
      refine ⟨0, zero_mem _, fun z => ?_⟩
      simp only [map_zero]
      exact hasDerivAt_const _ _
    | add x y _ _ hx hy =>
      obtain ⟨x', hx', dx⟩ := hx
      obtain ⟨y', hy', dy⟩ := hy
      refine ⟨x' + y', add_mem hx' hy', fun z => ?_⟩
      simp only [map_add]
      exact (dx z).add (dy z)
    | smul a x _ hx =>
      obtain ⟨x', hx', dx⟩ := hx
      refine ⟨a • x', Submodule.smul_mem _ a hx', fun z => ?_⟩
      simp only [map_smul]
      exact (dx z).const_mul a

theorem isVacF_om {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} (A : Fr S)
    (B : Fr T) {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) {g : GA D S} (hg : g ∈ GfC S) {h : GA D T} (hh : h ∈ GfC T) {f : WO S T → ℂ}
    (hf : IsVacF ψ θ A B f) : IsVacF ψ θ A B (om (g, h) f) := by
  have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
    intro τ z
    rw [GlobalTheory.OrientedHeis.om_dRho hW hθ g h τ z hf.1, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S (inv_mem hg), Matrix.one_mul, Matrix.mul_one]
  refine ⟨hW.om_pres _ f hf.1, fun τ z => ?_⟩
  have h0 := hf.2 τ z
  unfold annih at h0 ⊢
  rw [e, e, ← map_smul, ← map_add, h0, map_zero]

theorem algF_isStable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (ε : Bool) (M X : HSp D) (Am : Fr M) (Bx : Fr X) (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X), IsWeil ψ ε M X χ χ' ω →
      IsStable θ M (fun g => ω (g, 1)) (algF ψ θ ε Am Bx) ∧ IsStable θ X (fun h => ω (1, h)) (algF ψ θ ε Am Bx) := by
  intro D ψ θ _ hθ ε M X A B χ χ' ω hW
  have hW' : IsWeilDatumO ψ (sgn ε M) X χ χ' (ω.toSgn ε) := hW
  have hmem : ∀ f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B f P ∈ algF ψ θ ε A B :=
    fun f P hf => Submodule.subset_span ⟨f, P, hf, rfl⟩
  have e0 : ∀ (g : GA D (sgn ε M)) (h : GA D X), (ω.toSgn ε) (g, h) = ω (ofSgn ε M g, h) := fun _ _ => rfl
  have hfin : ∀ g ∈ GfC M, ∀ h ∈ GfC X, ∀ f P, IsFinF ψ θ ε A B f →
      ω (g, h) (fockF ψ θ ε A B f P) ∈ algF ψ θ ε A B := by
    intro g hg h hh f P hf
    have hg' : (ofSgn ε M).symm g ∈ GfC (sgn ε M) := by
      rw [GlobalTheory.SgnIdent.mem_GfC_sgn, MulEquiv.apply_symm_apply]; exact hg
    have ht := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ (sgn ε M) X χ χ' (ω.toSgn ε) hW' θ hθ _ hg' h hh
      (frSgn ε A).cart B.cart A.onb B.onb f P hf.1
    have hv := isVacF_om hθ (frSgn ε A) B hW' hg' hh hf
    rw [e0, MulEquiv.apply_symm_apply] at ht hv
    have : ω (g, h) (fockF ψ θ ε A B f P) = fockF ψ θ ε A B (ω (g, h) f) P := ht
    rw [this]
    exact hmem _ _ hv
  have hL := fun τ => GlobalTheory.LieFock.lieFockUpTo D (sgn ε M) X (frSgn ε A) B θ ψ χ χ' (ω.toSgn ε) τ hθ hW'
  refine ⟨isStable_span θ M _ _ ?_ ?_, isStable_span θ X _ _ ?_ ?_⟩
  · rintro g hg _ ⟨f, P, hf, rfl⟩
    exact hfin g hg 1 (one_mem _) f P hf
  · rintro τ Z hZ _ ⟨f, P, hf, rfl⟩
    obtain ⟨κS, κT, hκ⟩ := hL τ
    have hZ' : Z ∈ lieAt (sgn ε M) τ := by rw [GlobalTheory.SgnIdent.lieAt_sgn]; exact hZ
    have e : ∀ t : ℝ, (ω.toSgn ε) (oneP θ (sgn ε M) τ Z t, 1) = ω (oneP θ M τ Z t, 1) := by
      intro t
      rw [e0]
      unfold oneP
      rw [GlobalTheory.SgnIdent.atTau_sgn θ hθ]
    have h := (hκ f hf).1 Z hZ' P
    simp only [e] at h
    exact ⟨_, hmem f _ hf, h⟩
  · rintro h hh _ ⟨f, P, hf, rfl⟩
    exact hfin 1 (one_mem _) h hh f P hf
  · rintro τ Y hY _ ⟨f, P, hf, rfl⟩
    obtain ⟨κS, κT, hκ⟩ := hL τ
    have e1 : ∀ h : GA D X, (ω.toSgn ε) (1, h) = ω (1, h) := fun h => by rw [e0, map_one]
    have h := (hκ f hf).2 Y hY P
    simp only [e1] at h
    exact ⟨_, hmem f _ hf, h⟩

end GlobalTheory.AlgStable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedPointDescendsFiniteSubextension
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

theorem exists_finite_factor {F R K L : Type} [Field F] [CommRing R] [Field K] [Field L] [Algebra F R]
    [Algebra F K] [Algebra F L] [Algebra.FiniteType F R] (φ : K →ₐ[F] L) (hφ : φ.toRingHom.IsIntegral)
    (ψ : R →ₐ[F] L) :
    ∃ (M : Type) (_ : Field M) (_ : Algebra F M) (i : K →ₐ[F] M) (j : M →ₐ[F] L) (χ : R →ₐ[F] M),
      j.comp i = φ ∧ i.toRingHom.Finite ∧ j.comp χ = ψ := by
  classical
  letI : Algebra K L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F R).out
  let M : IntermediateField K L := IntermediateField.adjoin K ((s.image ψ : Finset L) : Set L)
  haveI hM : FiniteDimensional K M :=
    IntermediateField.finiteDimensional_adjoin fun x _ => hφ x
  have hmem : ∀ r : R, ψ r ∈ M.toSubalgebra.restrictScalars F := by
    intro r
    have hr : r ∈ Algebra.adjoin F (s : Set R) := hs ▸ Algebra.mem_top
    have : Algebra.adjoin F (s : Set R) ≤ (M.toSubalgebra.restrictScalars F).comap ψ := by
      refine Algebra.adjoin_le fun x hx => ?_
      exact IntermediateField.subset_adjoin K _ (by simpa using ⟨x, hx, rfl⟩)
    exact this hr
  refine ⟨M, inferInstance, inferInstance, IsScalarTower.toAlgHom F K M, M.val.restrictScalars F,
    ψ.codRestrict (M.toSubalgebra.restrictScalars F) hmem, ?_, ?_, ?_⟩
  · ext a; rfl
  · exact RingHom.finite_algebraMap.2 hM
  · ext a; rfl

theorem frPt_descends_finite :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K L : Type) [Field K] [Field L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) (z : FrPt Xo c L), φ.toRingHom.IsIntegral → ∃ (M : Type) (_ : Field M) (_ : Algebra c.F M) (i : K →ₐ[c.F] M) (j : M →ₐ[c.F] L) (z₁ : FrPt Xo c M), j.comp i = φ ∧ i.toRingHom.Finite ∧ FrMap j z₁ z := by
  intro E _ _ _ H Dw l Xo c K L _ _ _ _ φ z hφ
  obtain ⟨p, ψ, u, hu⟩ := GlobalTheory.FlagTan.fromTest_of_isLocalRing z
  haveI : Algebra.FiniteType c.F p.R := inferInstance
  obtain ⟨M, _, _, i, j, χ, h1, h2, h3⟩ := exists_finite_factor φ hφ ψ
  obtain ⟨z₁, hz⟩ := GlobalTheory.FlagTan.exists_frMap χ u
  exact ⟨M, inferInstance, inferInstance, i, j, z₁, h1, h2,
    GlobalTheory.FlagTan.frMap_of_comp hz hu fun a => DFunLike.congr_fun h3 a⟩

end GlobalTheory.HkIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltrationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricLemma_of_bzFiniteness_of_filtration : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.Published.GeometricLemma := by
  first | exact @GlobalTheory.geometricLemma_of_filtration | exact GlobalTheory.geometricLemma_of_filtration | (intros; apply GlobalTheory.geometricLemma_of_filtration <;> assumption)
end

