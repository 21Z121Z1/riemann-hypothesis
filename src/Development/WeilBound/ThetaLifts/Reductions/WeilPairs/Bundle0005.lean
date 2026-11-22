import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHalfAbstract
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.CAFInvol
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

section Alg

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem levi_alg (c : R →+* R) (hcc : ∀ x, c (c x) = x) (r : R) (hr : 2 * r = 1) (J : Matrix ι ι R)
    (hJ : (J.map c)ᵀ = J) (hJu : IsUnit J.det) (a : R) (ha : c a = a) (t t' : Matrix ι ι R)
    (h1 : t * t' = 1) (h2 : t' * t = 1) (hs : a • (t - 1) = t - 1) :
    ∃ H H' : Matrix (ι ⊕ ι) (ι ⊕ ι) R, H * H' = 1 ∧ H' * H = 1 ∧
      (H.map c)ᵀ * Matrix.fromBlocks J 0 0 (-J) * H = Matrix.fromBlocks J 0 0 (-J) ∧
      H * Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) * t ∧
      a • (H - 1) = H - 1 ∧
      (∃ M : Matrix ι ι R, IsUnit M.det ∧
        H' * Matrix.fromRows (1 : Matrix ι ι R) (-1 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (-1 : Matrix ι ι R) * M) ∧
      H.det * c t.det = t.det := by
  have hcr : c r = r := by
    have := congrArg c hr
    rw [map_mul, map_ofNat, map_one] at this
    linear_combination r * this - c r * hr
  have hT : ∀ {κ : Type} [Fintype κ] (x y : Matrix κ κ R), ((x * y).map c)ᵀ = (y.map c)ᵀ * (x.map c)ᵀ := by
    intro κ _ x y
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hT1 : ((1 : Matrix ι ι R).map c)ᵀ = 1 := by
    rw [Matrix.map_one _ c.map_zero c.map_one, Matrix.transpose_one]
  have hTT : ∀ x : Matrix ι ι R, (((x.map c)ᵀ).map c)ᵀ = x := by
    intro x; ext i j; exact hcc _
  have j1 : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hJu
  have j2 : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJu
  obtain ⟨u, hu⟩ : ∃ u, u = (t.map c)ᵀ := ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u', u' = (t'.map c)ᵀ := ⟨_, rfl⟩
  have u1 : u * u' = 1 := by rw [hu, hu', ← hT, h2, hT1]
  have u2 : u' * u = 1 := by rw [hu, hu', ← hT, h1, hT1]
  obtain ⟨s, hs1⟩ : ∃ s, s = J⁻¹ * u' * J := ⟨_, rfl⟩
  obtain ⟨s', hs2⟩ : ∃ s', s' = J⁻¹ * u * J := ⟨_, rfl⟩
  have s1 : s * s' = 1 := by
    rw [hs1, hs2]
    calc J⁻¹ * u' * J * (J⁻¹ * u * J) = J⁻¹ * (u' * (J * J⁻¹) * u) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [j1, Matrix.mul_one, u2, Matrix.mul_one, j2]
  have s2 : s' * s = 1 := mul_eq_one_comm.1 s1
  have k1 : u * J * s = J := by
    rw [hs1]
    calc u * J * (J⁻¹ * u' * J) = u * (J * J⁻¹) * u' * J := by simp only [Matrix.mul_assoc]
      _ = J := by rw [j1, Matrix.mul_one, u1, Matrix.one_mul]
  have k2 : (s.map c)ᵀ * J * t = J := by
    have := congrArg (fun x : Matrix ι ι R => (x.map c)ᵀ) k1
    simp only [hT, hJ] at this
    rw [hu, hTT] at this
    rw [Matrix.mul_assoc, this]
  have a1 : a • (t' - 1) = t' - 1 := by
    have e : t' - 1 = -t' * (t - 1) := by rw [Matrix.mul_sub, Matrix.neg_mul, h2]; simp [sub_eq_add_neg, add_comm]
    rw [e, ← Matrix.mul_smul, hs]
  have a2 : a • (u' - 1) = u' - 1 := by
    ext i j
    have := congrArg c (congrFun (congrFun a1 j) i)
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, map_mul, map_sub, ha] at this ⊢
    have e : c ((1 : Matrix ι ι R) j i) = (1 : Matrix ι ι R) i j := congrFun (congrFun hT1 i) j
    rw [e] at this
    rw [hu']
    exact this
  have a3 : a • (s - 1) = s - 1 := by
    have e : s - 1 = J⁻¹ * (u' - 1) * J := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, j2, hs1]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, a2]
  have d1 : s.det * c t.det = 1 := by
    have e : c t.det = u.det := by
      rw [hu, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
    have := congrArg Matrix.det k1
    rw [Matrix.det_mul, Matrix.det_mul] at this
    refine hJu.mul_left_cancel ?_
    rw [e]
    linear_combination this
  obtain ⟨P, hP⟩ : ∃ P : Matrix (ι ⊕ ι) (ι ⊕ ι) R, P = Matrix.fromBlocks 1 1 1 (-1) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (ι ⊕ ι) (ι ⊕ ι) R, Q = r • P := ⟨_, rfl⟩
  have hrr : r • (1 : Matrix ι ι R) + r • 1 = 1 := by
    rw [← add_smul, ← two_mul, hr, one_smul]
  have p1 : P * Q = 1 := by
    rw [hQ, Matrix.mul_smul, hP, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_one]
    simp [hrr]
  have p2 : Q * P = 1 := mul_eq_one_comm.1 p1
  have pT : (P.map c)ᵀ = P := by
    rw [hP]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, apply_ite c, eq_comm]
  have qT : (Q.map c)ᵀ = Q := by
    ext i j
    have := congrFun (congrFun pT i) j
    simp only [hQ, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hcr] at this ⊢
    rw [this]
  have c1 : P * Matrix.fromRows (1 : Matrix ι ι R) (0 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (1 : Matrix ι ι R) := by
    rw [hP, Matrix.fromBlocks_mul_fromRows]; simp
  have c2 : P * Matrix.fromRows (0 : Matrix ι ι R) (1 : Matrix ι ι R) = Matrix.fromRows (1 : Matrix ι ι R) (-1 : Matrix ι ι R) := by
    rw [hP, Matrix.fromBlocks_mul_fromRows]; simp
  have conj : ∀ X Y : Matrix (ι ⊕ ι) (ι ⊕ ι) R, X * Y = 1 → P * X * Q * (P * Y * Q) = 1 := by
    intro X Y h
    calc P * X * Q * (P * Y * Q) = P * (X * (Q * P) * Y) * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [p2, Matrix.mul_one, h, Matrix.mul_one, p1]
  refine ⟨P * Matrix.fromBlocks t 0 0 s * Q, P * Matrix.fromBlocks t' 0 0 s' * Q, conj _ _ ?_, conj _ _ ?_, ?_, ?_, ?_,
    ⟨s', ?_, ?_⟩, ?_⟩
  · rw [Matrix.fromBlocks_multiply, h1, s1]; simp
  · rw [Matrix.fromBlocks_multiply, h2, s2]; simp
  · have e1 : P * Matrix.fromBlocks J 0 0 (-J) * P = Matrix.fromBlocks 0 (J + J) (J + J) 0 := by
      rw [hP, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]; simp
    have e2 : ((Matrix.fromBlocks t 0 0 s).map c)ᵀ = Matrix.fromBlocks u 0 0 (s.map c)ᵀ := by
      rw [hu, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]; simp
    have e3 : Matrix.fromBlocks u 0 0 (s.map c)ᵀ * Matrix.fromBlocks 0 (J + J) (J + J) 0 * Matrix.fromBlocks t 0 0 s =
        Matrix.fromBlocks 0 (J + J) (J + J) 0 := by
      rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [Matrix.mul_add, Matrix.add_mul, k1, k2]
    rw [hT, hT, pT, qT, e2]
    calc Q * (Matrix.fromBlocks u 0 0 (s.map c)ᵀ * P) * Matrix.fromBlocks J 0 0 (-J) *
          (P * Matrix.fromBlocks t 0 0 s * Q)
        = Q * (Matrix.fromBlocks u 0 0 (s.map c)ᵀ * (P * Matrix.fromBlocks J 0 0 (-J) * P) *
            Matrix.fromBlocks t 0 0 s) * Q := by simp only [Matrix.mul_assoc]
      _ = (Q * P) * Matrix.fromBlocks J 0 0 (-J) * (P * Q) := by
          rw [e1, e3, ← e1]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [p1, p2, Matrix.one_mul, Matrix.mul_one]
  · rw [← c1]
    calc P * Matrix.fromBlocks t 0 0 s * Q * (P * Matrix.fromRows (1 : Matrix ι ι R) (0 : Matrix ι ι R))
        = P * (Matrix.fromBlocks t 0 0 s * ((Q * P) * Matrix.fromRows (1 : Matrix ι ι R) (0 : Matrix ι ι R))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [p2, Matrix.one_mul, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]; simp
  · have e : P * Matrix.fromBlocks t 0 0 s * Q - 1 = P * Matrix.fromBlocks (t - 1) 0 0 (s - 1) * Q := by
      have e0 : Matrix.fromBlocks (t - 1) 0 0 (s - 1) = Matrix.fromBlocks t 0 0 s - 1 := by
        rw [← Matrix.fromBlocks_one, sub_eq_add_neg (Matrix.fromBlocks t 0 0 s), Matrix.fromBlocks_neg,
          Matrix.fromBlocks_add]
        simp [sub_eq_add_neg]
      rw [e0, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, p1]
    rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.fromBlocks_smul, hs, a3, smul_zero]
  · exact Matrix.isUnit_det_of_left_inverse s1
  · rw [← c2]
    calc P * Matrix.fromBlocks t' 0 0 s' * Q * (P * Matrix.fromRows (0 : Matrix ι ι R) (1 : Matrix ι ι R))
        = P * (Matrix.fromBlocks t' 0 0 s' * ((Q * P) * Matrix.fromRows (0 : Matrix ι ι R) (1 : Matrix ι ι R))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [p2, Matrix.one_mul, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]; simp
  · have e := congrArg Matrix.det p1
    rw [Matrix.det_mul, Matrix.det_one] at e
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
    linear_combination t.det * s.det * c t.det * e + t.det * d1

end Alg

theorem cAF_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (z : AEF F E) : cAF σ (cAF σ z) = z := by
  have hs : ∀ (a : AF F) (x : E), cAF σ (a ⊗ₜ[F] x) = a ⊗ₜ[F] σ x := fun _ _ => rfl
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rw [hs, hs, GlobalTheory.SplitDetCharF.sig_invol h]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]

theorem exists_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) →
      ∃ h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC F E nT = dC F E nT * t.1 ∧
        SuppAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h ∧
        (∃ M : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), IsUnit M.det ∧ ∀ (nS : ℕ) (y : WOF F E nS nT),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h⁻¹ * (aC F E nT * y) = aC F E nT * (M * y)) ∧
        ∃ x : (AF F ⊗[F] E)ˣ, IsDetAtF σ e (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h x ∧
          ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (m : ℕ), ResEtaF χ m → χ x = χ (Matrix.GeneralLinearGroup.det t) := by
  intro F E _ _ _ _ _ σ B hB n JT hT e he t ht
  have hc : IsCMExt F E σ := hB.cm
  have hcc := cAF_invol hc
  obtain ⟨r, hr⟩ : ∃ r : AEF F E, 2 * r = 1 := by
    have h := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (AF F ⊗[F] E))
    rw [map_ofNat] at h
    exact h.exists_right_inv
  have hJ : ((JR (F := F) (AF F) JT).map (cAF σ))ᵀ = JR (F := F) (AF F) JT := by
    ext i j
    show (1 : AF F) ⊗ₜ[F] σ (JT j i) = (1 : AF F) ⊗ₜ[F] JT i j
    rw [hT.1]
  have hu : IsUnit (JR (F := F) (AF F) JT).det := by
    have := ((Ne.isUnit hT.2).map (inclR (F := F) (AF F)))
    rwa [RingHom.map_det] at this
  have ha : cAF σ (e + cAF σ e) = e + cAF σ e := by rw [RingHom.map_add, hcc, add_comm]
  obtain ⟨H, H', g1, g2, g3, g4, g5, ⟨M, hM, g6⟩, g7⟩ := levi_alg (cAF σ) hcc r hr _ hJ hu _ ha t.1 (t⁻¹).1
    t.mul_inv t.inv_mul (by ext i j; exact ht i j)
  have eJ : JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) =
      (Matrix.fromBlocks (JR (F := F) (AF F) JT) 0 0 (-JR (F := F) (AF F) JT)).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, JR, Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Matrix.map_apply] <;> simp [dbl]
  let G : GL (Fin (n + n)) (AF F ⊗[F] E) :=
    ⟨H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm, H'.submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
      by rw [Matrix.submatrix_mul_equiv, g1, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, g2, Matrix.submatrix_one_equiv]⟩
  have hG : G ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := by
    show ((H.map (cAF σ))ᵀ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm *
      JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) *
      H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm = JR (F := F) (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
    rw [eJ, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, g3]
  obtain ⟨h, m1, m2⟩ : ∃ h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT),
      mtF σ _ h = H.submatrix finSumFinEquiv.symm finSumFinEquiv.symm ∧
      mtF σ _ h⁻¹ = H'.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := ⟨⟨G, hG⟩, rfl, rfl⟩
  have sub : ∀ (X : Matrix (Fin n ⊕ Fin n) (Fin n) (AEF F E)) (Y : Matrix (Fin n) (Fin n) (AEF F E)),
      (X * Y).submatrix (finSumFinEquiv (m := n) (n := n)).symm id = X.submatrix finSumFinEquiv.symm id * Y :=
    fun X Y => rfl
  have e1 : e * e = e := he.1
  have e2 : e * cAF σ e = 0 := he.2.1
  have e3 : cAF σ e * cAF σ e = cAF σ e := by rw [← RingHom.map_mul, e1]
  have hd : (1 - (e + cAF σ e)) * (t.1.det - 1) = 0 :=
    GlobalTheory.SplitDetCharF.mul_det_sub_one _ _ fun i j => by rw [sub_mul, one_mul, ht i j, sub_self]
  refine ⟨h, ?_, ?_, ⟨M, hM, fun nS y => ?_⟩,
    GlobalTheory.SplitDetCharF.cutDet σ _ e e1 h, ?_, fun χ m hχ => ?_⟩
  · rw [m1, dC, Matrix.submatrix_mul_equiv, ← sub]
    exact congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm id) g4
  · intro i j
    rw [m1, ← Matrix.submatrix_one_equiv (finSumFinEquiv (m := n) (n := n)).symm]
    exact congrFun (congrFun g5 (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  · rw [m2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, aC, Matrix.submatrix_mul_equiv, ← sub]
    exact congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm id * y) g6
  · exact add_comm _ _
  · let w : (AEF F E)ˣ := Units.map (GlobalTheory.SplitDetCharF.cut (cAF σ e) e3) (Matrix.GeneralLinearGroup.det t)
    let u : (AEF F E)ˣ := Units.map (GlobalTheory.SplitDetCharF.cut e e1) (Matrix.GeneralLinearGroup.det t)
    have hw : (w : AEF F E) = (1 - cAF σ e) + cAF σ e * t.1.det := rfl
    have hu' : (u : AEF F E) = (1 - e) + e * t.1.det := rfl
    have huw : Matrix.GeneralLinearGroup.det t = u * w := by
      refine Units.ext ?_
      rw [Units.val_mul, hw, hu', Matrix.GeneralLinearGroup.val_det_apply]
      linear_combination hd - (t.1.det - 1) ^ 2 * e2
    obtain ⟨w', hw'⟩ : IsUnit (cAF σ (w : AEF F E)) := w.isUnit.map (cAF σ)
    have hx : GlobalTheory.SplitDetCharF.cutDet σ _ e e1 h * w' = u := by
      refine Units.ext ?_
      rw [Units.val_mul, hw', hw, hu', GlobalTheory.SplitDetCharF.cutDet_val, m1, Matrix.det_submatrix_equiv_self,
        RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, hcc]
      linear_combination (H.det - 1) * (cAF σ t.1.det - 1) * e1 + e * g7
    have hy := GlobalTheory.SplitDetCharF.char_eq_of_mul_conj hc hχ w'⁻¹ w (by rw [← hw', Units.inv_mul])
    rw [huw, map_mul, ← hy, ← map_mul, ← hx, mul_inv_cancel_right]

end GlobalTheory.SplitLagrF

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
section
open scoped TensorProduct Matrix Kronecker
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT : ℕ}

theorem hOF_eq_trace {m : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin m) (Fin m) E) (x y : WOF F E nS m) :
    hOF σ JS J x y = (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * J.map (incAF F E) * x)).trace := by
  simp only [hOF, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem dC_dual (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) :
    (dC E nT)ᵀ * GlobalTheory.WeilSchrodinger.DblTargetF.dblG J * dCdE J = 1 := by
  have e : GlobalTheory.WeilSchrodinger.DblTargetF.dblG J = (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
  rw [e, dCdE, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id,
    diagCols, dbl, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_zero, add_zero, zero_add, neg_mul_neg, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, Matrix.mul_smul, Matrix.mul_nonsing_inv _ (Ne.isUnit hJ), ← add_smul]
  norm_num

theorem dC_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) : (dC R n).map φ = dC S n := by
  ext i j
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  simp only [dC, diagCols, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases k with k | k <;> simp [Matrix.one_apply, apply_ite φ]

theorem hOF_dual (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) (v y : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (dCd F J * v) (dC (AF F ⊗[F] E) nT * y) =
      (JS⁻¹.map (incAF F E) * ((y.map (cAF σ))ᵀ * v)).trace := by
  have h := congrArg (fun M : Matrix (Fin nT) (Fin nT) E => M.map (incAF F E)) (dC_dual J hJ)
  simp only [Matrix.map_mul, Matrix.transpose_map, dC_map] at h
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
  rw [hOF_eq_trace, Matrix.map_mul, dC_map, Matrix.transpose_mul]
  congr 2
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (dCd F J), ← Matrix.mul_assoc (dC _ nT)ᵀ, ← Matrix.mul_assoc (dC _ nT)ᵀ]
  rw [show (dC (AF F ⊗[F] E) nT)ᵀ * (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J).map (incAF F E) * dCd F J = 1 from h,
    Matrix.one_mul]

theorem phase_move (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) (ξ₀ : E)
    (ψ : AddChar (AF F) ℂ) (s : GL (Fin nT) (AF F ⊗[F] E)) (y w : WOF F E nS nT) :
    phase σ JS J ξ₀ ψ ((s⁻¹).1 * y) ((s.1.map (cAF σ))ᵀ * w) = phase σ JS J ξ₀ ψ y w := by
  unfold phase symplOF
  rw [hOF_dual JS J hJ, hOF_dual JS J hJ, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (s.1.map (cAF σ))ᵀ, ← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul]

variable (F E nS nT) in

def vecE : WOF F E nS nT ≃+ (Fin (nT * nS) → AF F ⊗[F] E) where
  toFun w k := w (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun u i j := u (finProdFinEquiv (i, j))
  left_inv w := by ext i j; simp only [Equiv.symm_apply_apply]
  right_inv u := by ext k; simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  map_add' _ _ := rfl

theorem integral_mul (ν : Measure (WOF F E nS nT)) (hν : ν.IsAddHaarMeasure) (A : GL (Fin nT) (AF F ⊗[F] E))
    (g : WOF F E nS nT → ℂ) : ∫ w, g (A.1 * w) ∂ν =
      ((((distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
        (Matrix.GeneralLinearGroup.det A)) : ℝ) ^ nS)⁻¹ : ℝ) : ℂ) * ∫ w, g w ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  letI : MeasurableSpace (Fin (nT * nS) → AF F ⊗[F] E) := borel _
  have : BorelSpace (Fin (nT * nS) → AF F ⊗[F] E) := ⟨rfl⟩
  have c1 : Continuous (vecE F E nS nT) :=
    continuous_pi fun k => (continuous_apply (finProdFinEquiv.symm k).2).comp (continuous_apply (finProdFinEquiv.symm k).1)
  have c2 : Continuous (vecE F E nS nT).symm := continuous_pi fun i => continuous_pi fun j => continuous_apply _
  let eh : WOF F E nS nT ≃ₜ (Fin (nT * nS) → AF F ⊗[F] E) := .mk (vecE F E nS nT).toEquiv c1 c2
  let em := eh.toMeasurableEquiv
  let K : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) → Matrix (Fin (nT * nS)) (Fin (nT * nS)) (AF F ⊗[F] E) :=
    fun M => (M ⊗ₖ (1 : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E))).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
  have hK : ∀ M M', M * M' = 1 → K M * K M' = 1 := fun M M' h => by
    simp only [K]
    rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, h, Matrix.mul_one, Matrix.one_kronecker_one,
      Matrix.submatrix_one_equiv]
  let t : GL (Fin (nT * nS)) (AF F ⊗[F] E) := ⟨K A.1, K (A⁻¹).1, hK _ _ A.mul_inv, hK _ _ A.inv_mul⟩
  have hd : Matrix.GeneralLinearGroup.det t = Matrix.GeneralLinearGroup.det A ^ nS := by
    ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    show (K A.1).det = _
    simp only [K]
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one, Fintype.card_fin]
  have hv : ∀ w : WOF F E nS nT, (vecE F E nS nT).symm (t.1 *ᵥ vecE F E nS nT w) = A.1 * w := fun w => by
    ext i j
    show ∑ k, K A.1 (finProdFinEquiv (i, j)) k * vecE F E nS nT w k = ∑ k, A.1 i k * w k j
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    show ∑ b, K A.1 (finProdFinEquiv (i, j)) (finProdFinEquiv (a, b)) *
      w (finProdFinEquiv.symm (finProdFinEquiv (a, b))).1 (finProdFinEquiv.symm (finProdFinEquiv (a, b))).2 = _
    simp only [K, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
    simp
  have h := GlobalTheory.T.integral_adelicGL_mulVec_haar_eq_modulus_det F E _ t (ν.map em) ((vecE F E nS nT).isAddHaarMeasure_map ν c1 c2)
    (fun u => g ((vecE F E nS nT).symm u))
  rw [integral_map_equiv, integral_map_equiv, hd, map_pow, map_pow, NNReal.coe_pow] at h
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    funext w
    exact congrArg g (hv w).symm
  · congr 2
    funext w
    exact congrArg g ((vecE F E nS nT).symm_apply_apply w)

end

theorem change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∀ (s : GL (Fin nT) (AF F ⊗[F] E)) (N : WOF F E nS nT → ℂ), Continuous N → Integrable N ν →
      Continuous (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ∧
      Integrable (fun w : WOF F E nS nT => N ((s.1.map (cAF σ))ᵀ * w)) ν ∧
      ∀ y : WOF F E nS nT, ∫ v, phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v ∂ν =
        ((mfac F E nS s : ℝ) : ℂ) ^ 2 * ∫ w, phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕 s N hN hI
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have hA : ∀ M M' : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), M * M' = 1 → (M'.map (cAF σ))ᵀ * (M.map (cAF σ))ᵀ = 1 :=
    fun M M' h => by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  let A : GL (Fin nT) (AF F ⊗[F] E) := ⟨(s.1.map (cAF σ))ᵀ, ((s⁻¹).1.map (cAF σ))ᵀ, hA _ _ s.inv_mul, hA _ _ s.mul_inv⟩
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => A.1 * w
      invFun := fun w => (A⁻¹).1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  have c1 : Continuous e := continuous_const.matrix_mul continuous_id
  have c2 : Continuous e.symm := continuous_const.matrix_mul continuous_id
  refine ⟨hN.comp c1, ?_, fun y => ?_⟩
  · have : (ν.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map ν c1 c2
    obtain ⟨c, hc⟩ : ∃ c : NNReal, ν.map e = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ ν⟩
    have h1 : Integrable N (ν.map e) := by
      rw [hc]
      exact hI.smul_measure_nnreal
    exact (integrable_map_measure hN.aestronglyMeasurable c1.measurable.aemeasurable).1 h1
  · have h := integral_mul ν hν A (fun v => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) v * N v)
    have hn : Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det A) =
        Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det s) := by
      refine Units.ext (GlobalTheory.SplitDetCharF.tensor_inj (F := F) (E := E) ?_)
      have hcc : ∀ z : AF F ⊗[F] E, cAF σ (cAF σ z) = z := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (GlobalTheory.SplitDetCharF.sig_invol hB.cm x)
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      have hd : A.1.det = cAF σ s.1.det := by
        show ((s.1.map (cAF σ))ᵀ).det = _
        rw [Matrix.det_transpose, RingHom.map_det]; rfl
      show algebraMap _ _ (Algebra.norm (AF F) A.1.det) = algebraMap _ _ (Algebra.norm (AF F) s.1.det)
      rw [GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, GlobalTheory.SplitDetCharF.algebraMap_norm hB.cm, hd, hcc, mul_comm]
    rw [hn] at h
    set m : ℝ := (distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
      (Matrix.GeneralLinearGroup.det s)) : ℝ) with hm
    have hm0 : 0 < m := NNReal.coe_pos.2 distribHaarChar_pos
    have hf : mfac F E nS s ^ 2 = m ^ nS := by
      show (m ^ ((Fintype.card (Fin nS) : ℝ) / 2)) ^ 2 = _
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le, Fintype.card_fin, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    have h2 : (fun w : WOF F E nS nT => phase σ JS JT ξ₀ B.ψ ((s⁻¹).1 * y) (A.1 * w) * N (A.1 * w)) =
        fun w => phase σ JS JT ξ₀ B.ψ y w * N ((s.1.map (cAF σ))ᵀ * w) := funext fun w => by
      rw [← phase_move JS JT hT.2 ξ₀ B.ψ s y w]
    rw [h2] at h
    rw [h, ← Complex.ofReal_pow, hf, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hm0 _).ne',
      Complex.ofReal_one, one_mul]

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end

