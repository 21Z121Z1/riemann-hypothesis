import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveHermitianPolynomial
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder ComplexConjugate
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.PosDefNorm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_value_pos {r : ℕ} (Q : SelfRecip E r) (ρ : Fld Q →+* ℂ) (hn : ‖ρ (alpha Q)‖ = 1) (y : Fld Q)
    (hz : ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[maximalRealSubfield E] Fld Q)ˣ,
      (z : u.Completion ⊗[maximalRealSubfield E] Fld Q) *
        involBase Q u.Completion (z : u.Completion ⊗[maximalRealSubfield E] Fld Q) = 1 ⊗ₜ y) :
    0 < ρ y := by
  have hinv : ∀ x, ρ (invol Q x) = conj (ρ x) := by
    have h : (ρ.comp (invol Q : Fld Q →+* Fld Q)) = (starRingEnd ℂ).comp ρ := by
      refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
      · change ρ (invol Q (algebraMap E (Fld Q) e)) = conj (ρ (algebraMap E (Fld Q) e))
        rw [invol_algebraMap]
        exact IsCMField.complexEmbedding_complexConj E (ρ.comp (algebraMap E (Fld Q))) e
      · change ρ (invol Q (alpha Q)) = conj (ρ (alpha Q))
        rw [invol_alpha, map_inv₀]
        exact Complex.inv_eq_conj hn
    exact fun x => DFunLike.congr_fun h x
  let ρF : maximalRealSubfield E →+* ℂ := ρ.comp (algebraMap (maximalRealSubfield E) (Fld Q))
  let w := InfinitePlace.mk ρF
  have hw : w.IsReal := IsTotallyReal.isReal w
  letI : Algebra (maximalRealSubfield E) ℂ := ρF.toAlgebra
  let g : w.Completion →ₐ[maximalRealSubfield E] ℂ :=
    ⟨InfinitePlace.Completion.extensionEmbedding w, fun a =>
      (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ a)).trans
        (DFunLike.congr_fun (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)) a)⟩
  have hg : ∀ a, conj (g a) = g a := fun a => by
    have : g a = (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw a : ℂ) :=
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a).symm
    rw [this, Complex.conj_ofReal]
  let f := (Algebra.TensorProduct.productMap g
    (⟨ρ, fun _ => rfl⟩ : Fld Q →ₐ[maximalRealSubfield E] ℂ)).toRingHom
  have hf : ∀ a e, f (a ⊗ₜ e) = g a * ρ e := fun _ _ => rfl
  have hfi : ∀ t, f (involBase Q w.Completion t) = conj (f t) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [involBase, Algebra.TensorProduct.map_tmul, hf, hf, map_mul, hg]
      exact congrArg _ (hinv e)
    | add a b ha hb => simp only [map_add, ha, hb]
  obtain ⟨z, hz⟩ := hz w
  have h1 := congrArg f hz
  rw [map_mul, hfi, hf, map_one, one_mul, Complex.mul_conj] at h1
  have h2 : f (z : w.Completion ⊗[maximalRealSubfield E] Fld Q) ≠ 0 := (z.isUnit.map f).ne_zero
  rw [← h1]
  exact_mod_cast Complex.normSq_pos.2 h2

theorem exists_irreducible_factor (P : E[X]) (hP : P.Monic) (τ : E →+* ℂ) (μ : ℂ) (h : eval₂ τ μ P = 0) :
    ∃ R : E[X], R.Monic ∧ Irreducible R ∧ R ∣ P ∧ eval₂ τ μ R = 0 := by
  letI : Algebra E ℂ := τ.toAlgebra
  have hi : IsIntegral E μ := ⟨P, hP, h⟩
  exact ⟨minpoly E μ, minpoly.monic hi, minpoly.irreducible hi, minpoly.dvd E μ h, minpoly.aeval E μ⟩

theorem aeval_units_conj {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ[X]) :
    aeval ((u : Matrix (Fin n) (Fin n) ℂ) * A * ((u⁻¹ : _ˣ) : Matrix (Fin n) (Fin n) ℂ)) p =
      (u : Matrix (Fin n) (Fin n) ℂ) * aeval A p * ((u⁻¹ : _ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]

theorem posDef_aeval {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (hs : U.charpoly.Separable)
    (hn : ∀ μ : ℂ, U.charpoly.IsRoot μ → ‖μ‖ = 1) (p : ℂ[X])
    (hp : ∀ μ : ℂ, U.charpoly.IsRoot μ → 0 < p.eval μ) : (aeval U p).PosDef := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  obtain ⟨r, hr⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm U Uᴴ hs (hU'.trans hU.symm)
  have hdiv : U.charpoly ∣ X * r - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval U hs _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr, hU', map_one, sub_self]
  have hrv : ∀ μ : ℂ, U.charpoly.IsRoot μ → r.eval μ = conj μ := fun μ hμ => by
    obtain ⟨t, ht⟩ := hdiv
    have h1 := congrArg (eval μ) ht
    have h0 : eval μ U.charpoly = 0 := hμ
    rw [eval_mul, h0, zero_mul, eval_sub, eval_mul, eval_X, eval_one, sub_eq_zero] at h1
    rw [← Complex.inv_eq_conj (hn μ hμ)]
    exact eq_inv_of_mul_eq_one_right h1
  have hcT : (aeval U p)ᴴ = aeval U ((p.map (starRingEnd ℂ)).comp r) := by
    have h1 := GlobalTheory.NormInert.cT_aeval (starRingEnd ℂ) U p
    have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, cT (starRingEnd ℂ) M = Mᴴ := fun M => rfl
    rw [h2, h2, hr, ← aeval_comp] at h1
    exact h1
  have hzero : aeval U (p - (p.map (starRingEnd ℂ)).comp r) = 0 := by
    by_cases h0 : p - (p.map (starRingEnd ℂ)).comp r = 0
    · rw [h0, map_zero]
    have hd : U.charpoly ∣ p - (p.map (starRingEnd ℂ)).comp r := by
      refine (IsAlgClosed.splits _).dvd_of_roots_le_roots U.charpoly_monic.ne_zero ?_
      rw [Multiset.le_iff_subset (nodup_roots hs)]
      intro μ hμ
      have hμ' := isRoot_of_mem_roots hμ
      rw [mem_roots h0, IsRoot.def, eval_sub, eval_comp, hrv μ hμ', sub_eq_zero, eval_map]
      have h3 : eval₂ (starRingEnd ℂ) (conj μ) p = conj (eval μ p) := by
        rw [eval, Polynomial.hom_eval₂, RingHom.comp_id]
      rw [h3]
      exact (Complex.conj_eq_iff_im.2 (Complex.pos_iff.1 (hp μ hμ')).2.symm).symm
    obtain ⟨t, ht⟩ := hd
    rw [ht, map_mul, Matrix.aeval_self_charpoly, zero_mul]
  have hH : (aeval U p).IsHermitian := by
    rw [Matrix.IsHermitian, hcT]
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  rw [hH.posDef_iff_eigenvalues_pos]
  intro i
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h1 : ((hH.eigenvalues i : ℝ) : ℂ) ∈ spectrum ℂ (aeval U p) := by
    have := hH.eigenvalues_mem_spectrum_real i
    rw [← spectrum.preimage_algebraMap ℂ] at this
    exact this
  rw [spectrum.map_polynomial_aeval_of_nonempty _ _ (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ U)] at h1
  obtain ⟨μ, hμ, e⟩ := h1
  have h2 := hp μ (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hμ)
  rw [show eval μ p = ((hH.eigenvalues i : ℝ) : ℂ) from e] at h2
  exact_mod_cast h2

open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem exists_factor {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.PosSemidef) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, T = Sᴴ * S := by
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT.nonneg
  exact ⟨y, rfl⟩

theorem map_aeval {n : ℕ} (τ : E →+* ℂ) (A : Matrix (Fin n) (Fin n) E) (p : E[X]) :
    (aeval A p).map τ = aeval (A.map τ) (p.map τ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Polynomial.map_add, map_add, ← hp, ← hq]
    ext i j
    simp
  | monomial k a =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial]
    have e : (A.map τ) ^ k = (A ^ k).map τ := by rw [Matrix.map_pow]
    rw [e]
    ext i j
    simp [Algebra.algebraMap_eq_smul_one]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[(maximalRealSubfield E)] Fld Q)ˣ, (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q u.Completion (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : Fld Q)) → ∀ τ : E →+* ℂ, ∃ Q' : Matrix (Fin n) (Fin n) ℂ, Q'.det ≠ 0 ∧ (H₀ * aeval γ₀.val m).map τ = cT (starRingEnd ℂ) Q' * Q' := by
  intro E _ _ _ n γ₀ hell H₀ _ _ hiso hdef m _ hz τ
  obtain ⟨Q, hQ, hHQ⟩ := hdef τ
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, cT (starRingEnd ℂ) M = Mᴴ := fun M => rfl
  rw [h2] at hHQ
  set A := γ₀.val.map τ with hA
  have hiso' : Aᴴ * (Qᴴ * Q) * A = Qᴴ * Q := by
    have h := congrArg (fun M => M.map τ) hiso
    simp only [Matrix.map_mul] at h
    have e : (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val).map τ = Aᴴ := by
      ext i j
      exact IsCMField.complexEmbedding_complexConj E τ (γ₀.val j i)
    rw [e, hHQ] at h
    exact h
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((Matrix.isUnit_iff_isUnit_det Q).2 (isUnit_iff_ne_zero.2 hQ)).unit
  have hu : (u : Matrix (Fin n) (Fin n) ℂ) = Q := rfl
  obtain ⟨Qi, hQi⟩ : ∃ Qi : Matrix (Fin n) (Fin n) ℂ, Qi = ((u⁻¹ : _ˣ) : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have e1 : Q * Qi = 1 := by rw [hQi, ← hu]; exact u.mul_inv
  have e2 : Qi * Q = 1 := by rw [hQi, ← hu]; exact u.inv_mul
  have hconj := aeval_units_conj u A (m.map τ)
  have hchar := Matrix.charpoly_units_conj u A
  rw [← Matrix.coe_units_inv] at hchar
  rw [hu, ← hQi] at hconj hchar
  have hAc : A.charpoly = γ₀.val.charpoly.map τ := Matrix.charpoly_map _ _
  obtain ⟨U, hUd⟩ : ∃ U, U = Q * A * Qi := ⟨_, rfl⟩
  rw [← hUd] at hconj hchar
  have hU : Uᴴ * U = 1 := by
    have e3 : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, e1, conjTranspose_one]
    calc Uᴴ * U = Qiᴴ * (Aᴴ * (Qᴴ * Q) * A) * Qi := by
          simp only [hUd, conjTranspose_mul, Matrix.mul_assoc]
      _ = (Qiᴴ * Qᴴ) * (Q * Qi) := by rw [hiso']; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, e3, Matrix.mul_one]
  have hroot : ∀ μ : ℂ, U.charpoly.IsRoot μ → (γ₀.val.charpoly.map τ).IsRoot μ := fun μ h => by
    rwa [hchar, hAc] at h
  have hnorm : ∀ μ : ℂ, U.charpoly.IsRoot μ → ‖μ‖ = 1 := fun μ h =>
    hell.2.2.2 τ μ ((mem_roots (Polynomial.map_ne_zero hell.1.ne_zero)).2 (hroot μ h))
  have hsep : U.charpoly.Separable := by
    rw [hchar, hAc]
    exact hell.2.2.1.map
  have hp : ∀ μ : ℂ, U.charpoly.IsRoot μ → 0 < (m.map τ).eval μ := fun μ h => by
    have h0 : eval₂ τ μ γ₀.val.charpoly = 0 := by
      rw [← eval_map]
      exact hroot μ h
    obtain ⟨R, Rm, Ri, Rd, Re⟩ := exists_irreducible_factor _ hell.1 τ μ h0
    let S : SelfRecip E R.natDegree := ⟨R, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell R Rm Ri Rd⟩
    let ρ : Fld S →+* ℂ := AdjoinRoot.lift τ μ Re
    have hα : ρ (alpha S) = μ := AdjoinRoot.lift_root Re
    have hm : ρ (AdjoinRoot.mk S.1 m : Fld S) = eval₂ τ μ m := AdjoinRoot.lift_mk Re m
    have := norm_value_pos S ρ (by rw [hα]; exact hnorm μ h) _ (hz _ S Rd)
    rwa [hm, ← eval_map] at this
  have hT := posDef_aeval U hU hsep hnorm (m.map τ) hp
  obtain ⟨S, hS⟩ := exists_factor hT.posSemidef
  have hdetS : S.det ≠ 0 := fun h => by
    have := hT.det_pos
    rw [hS, Matrix.det_mul, h, mul_zero] at this
    exact lt_irrefl _ this
  refine ⟨S * Q, by rw [Matrix.det_mul]; exact mul_ne_zero hdetS hQ, ?_⟩
  have e4 : Q * aeval A (m.map τ) = (Sᴴ * S) * Q := by
    rw [← hS, hconj, Matrix.mul_assoc, e2, Matrix.mul_one]
  rw [Matrix.map_mul, hHQ, map_aeval, h2, conjTranspose_mul, Matrix.mul_assoc, e4]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.PosDefNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatDoubleCosetEqOfRowDet
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.GAMajInj

theorem exists_nx_mul (g g' : GL (Fin 2) ℚ)
    (h0 : (g : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (g' : Matrix (Fin 2) (Fin 2) ℚ) 1 0)
    (h1 : (g : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = (g' : Matrix (Fin 2) (Fin 2) ℚ) 1 1)
    (hd : (g : Matrix (Fin 2) (Fin 2) ℚ).det = (g' : Matrix (Fin 2) (Fin 2) ℚ).det) :
    ∃ x : ℚ, nx (Multiplicative.ofAdd x) * g = g' := by
  have hne : (g : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  rw [Matrix.det_fin_two] at hne
  rw [Matrix.det_fin_two, Matrix.det_fin_two] at hd
  obtain ⟨x, hx0, hx1⟩ : ∃ x : ℚ,
      (g' : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = (g : Matrix (Fin 2) (Fin 2) ℚ) 0 0 +
        x * (g : Matrix (Fin 2) (Fin 2) ℚ) 1 0 ∧
      (g' : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = (g : Matrix (Fin 2) (Fin 2) ℚ) 0 1 +
        x * (g : Matrix (Fin 2) (Fin 2) ℚ) 1 1 := by
    rw [← h0, ← h1] at hd
    generalize (g : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = a at *
    generalize (g : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = b at *
    generalize (g : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = c at *
    generalize (g : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = d at *
    generalize (g' : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = a' at *
    generalize (g' : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = b' at *
    by_cases hdz : d = 0
    · subst hdz
      have hc : c ≠ 0 := by
        rintro rfl
        simp at hne
      refine ⟨(a' - a) / c, by field_simp; ring, ?_⟩
      have : (b' - b) * c = 0 := by linear_combination hd
      have hb : b' - b = 0 := (mul_eq_zero.1 this).resolve_right hc
      linear_combination hb
    · refine ⟨(b' - b) / d, ?_, by field_simp; ring⟩
      field_simp
      linear_combination -hd
  refine ⟨x, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nx, Matrix.mul_apply, Fin.sum_univ_two, hx0, hx1, h0, h1]

theorem maj_inj : ∀ q q' : Ad3.GA.NQ,
    (q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = (q'.out : Matrix (Fin 2) (Fin 2) ℚ) 1 0 →
    (q.out : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = (q'.out : Matrix (Fin 2) (Fin 2) ℚ) 1 1 →
    (q.out : Matrix (Fin 2) (Fin 2) ℚ).det = (q'.out : Matrix (Fin 2) (Fin 2) ℚ).det → q = q' := by
  intro q q' h0 h1 hd
  obtain ⟨x, hx⟩ := exists_nx_mul q.out q'.out h0 h1 hd
  have hr : (QuotientGroup.rightRel nU) q.out q'.out :=
    QuotientGroup.rightRel_apply.2 ⟨Multiplicative.ofAdd x, eq_mul_inv_of_mul_eq hx⟩
  rw [← Quotient.out_eq q, ← Quotient.out_eq q']
  exact Quotient.sound hr

end GlobalTheory.CompanionTheory.GAMajInj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SW.Core
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def InNOh {d : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) (x : Af F ⊗[F] E) : Prop :=
  ∀ k, ∃ y ∈ Oh F, (Algebra.TensorProduct.basis (Af F) b).repr x k = (N : Af F) * y

def latN {d : ℕ} (b : Module.Basis (Fin d) F E) (n M N : ℕ) :
    AddSubgroup (Fin n → Fin M → Af F ⊗[F] E) where
  carrier := {X | ∀ a i, InNOh b N (X a i)}
  zero_mem' := fun a i k => ⟨0, fun v => zero_mem _, by simp⟩
  add_mem' := by
    intro X Y hX hY a i k
    obtain ⟨x, hx, ex⟩ := hX a i k
    obtain ⟨y, hy, ey⟩ := hY a i k
    refine ⟨x + y, fun v => add_mem (hx v) (hy v), ?_⟩
    simp only [Pi.add_apply, map_add, Finsupp.add_apply, ex, ey, mul_add]
  neg_mem' := by
    intro X hX a i k
    obtain ⟨x, hx, ex⟩ := hX a i k
    refine ⟨-x, fun v => neg_mem (hx v), ?_⟩
    simp only [Pi.neg_apply, map_neg, Finsupp.neg_apply, ex, mul_neg]

def gram2 (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin n → Fin M → Af F ⊗[F] E) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
  fun a c => hR (Af F) σ J (X a) (Y c)

def phaseB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψf : Af F → ℂ)
    (b : HermR (Af F) σ n) (X : Fin n → Fin M → Af F ⊗[F] E) : ℂ :=
  ψf (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gramR (Af F) σ J X)))

def pairB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψf : Af F → ℂ)
    (b : HermR (Af F) σ n) (X Y : Fin n → Fin M → Af F ⊗[F] E) : ℂ :=
  ψf (Algebra.trace (Af F) (Af F ⊗[F] E)
    (Matrix.trace ((b : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gram2 σ J X Y)))

def ratTuple [NumberField E] {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : ℕ) (ρ : Fin M → Fin n → 𝓞 E) :
    Fin n → Fin M → Af F ⊗[F] E :=
  fun a j => inclR (Af F) ((s : E) * (J⁻¹ *ᵥ fun i => algebraMap (𝓞 E) E (ρ i a)) j)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalSectionFiniteOpenCover
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchRep

theorem exists_local_quot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L) (r : L.ι → X.functionFieldˣ) (y : GlobalTheory.CxPts q σ) :
    ∃ (W : X.Opens) (b : L.ι) (a d : Γ(X, W)) (h : genericPoint X ∈ W),
      y ∈ ptsIn q σ W ∧ W ≤ L.U b ∧ fnOf W h d ≠ 0 ∧
        (r b : X.functionField) * fnOf W h d = fnOf W h a := by
  have hb := mem_pick ψ.isLB y
  obtain ⟨W, hW, hyW, hWb⟩ := exists_isAffineOpen_mem_and_subset (mem_ptsIn.1 hb)
  have hg : genericPoint X ∈ W := gen_mem hyW
  haveI : Nonempty W := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  obtain ⟨a, d, hd, e⟩ := IsFractionRing.div_surjective (A := Γ(X, W)) (r (pick ψ.isLB y) : X.functionField)
  have hd0 : fnOf W hg d ≠ 0 := by
    have : algebraMap Γ(X, W) X.functionField d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    exact this
  refine ⟨W, pick ψ.isLB y, a, d, hg, mem_ptsIn.2 hyW, hWb, hd0, ?_⟩
  rw [← e]
  change algebraMap Γ(X, W) X.functionField a / algebraMap Γ(X, W) X.functionField d * fnOf W hg d = _
  have e' : algebraMap Γ(X, W) X.functionField d = fnOf W hg d := rfl
  have e'' : algebraMap Γ(X, W) X.functionField a = fnOf W hg a := rfl
  rw [e', e'', div_mul_cancel₀ _ hd0]

theorem logNorm_of_quot {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r)
    {W : X.Opens} {b : L.ι} {a d : Γ(X, W)} {h : genericPoint X ∈ W} (hWb : W ≤ L.U b)
    (e : (r b : X.functionField) * fnOf W h d = fnOf W h a) {y : GlobalTheory.CxPts q σ} (hy : y ∈ ptsIn q σ W)
    (ho : y ∈ offSupp q σ (divOfRatSec ψ.isLB hr)) (hd : ev q σ W d y ≠ 0) :
    GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ W a y‖ - Real.log ‖ev q σ W d y‖ - ψ.φ b y / 2 := by
  have hb : y ∈ ptsIn q σ (L.U b) := mem_ptsIn.2 (hWb (mem_ptsIn.1 hy))
  have hu := IsRatSec.unitAt ψ.isLB hr ho hb
  have hv : ratVal (r b : X.functionField) y ≠ 0 := ratVal_ne_zero hu
  have ev' : ratVal (r b : X.functionField) y * ev q σ W d y = ev q σ W a y := by
    rw [← ratVal_fnOf hy h d, ← ratVal_mul hu.regAt (regAt_fnOf (mem_ptsIn.1 hy) h d), e, ratVal_fnOf hy]
  rw [logNorm_eq ψ hr ho hb, ← ev', norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 hv) (norm_ne_zero_iff.2 hd)]
  ring

theorem logNorm_finite_rep {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ : k →+* ℂ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {L : LB X} (ψ : GlobalTheory.Weight q σ L) {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ∃ (N : ℕ) (W : Fin N → X.Opens) (b : Fin N → L.ι) (a d : ∀ l, Γ(X, W l)),
      (∀ y : GlobalTheory.CxPts q σ, ∃ l, y ∈ ptsIn q σ (W l)) ∧ (∀ l, W l ≤ L.U (b l)) ∧
      (∀ l, ∃ h : genericPoint X ∈ W l, fnOf (W l) h (d l) ≠ 0) ∧
      ∀ l, ∀ y ∈ ptsIn q σ (W l), y ∈ offSupp q σ (divOfRatSec ψ.isLB hr) → ev q σ (W l) (d l) y ≠ 0 →
        GlobalTheory.Cartier.logNorm ψ r y = Real.log ‖ev q σ (W l) (a l) y‖ - Real.log ‖ev q σ (W l) (d l) y‖ - ψ.φ (b l) y / 2 := by
  choose W₀ b₀ a₀ d₀ h₀ hy₀ hWb₀ hd₀ e₀ using exists_local_quot ψ r
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => ptsIn q σ (W₀ y))
    (fun y => isOpen_ptsIn _) fun y _ => Set.mem_iUnion.2 ⟨y, hy₀ y⟩
  let c : Fin t.card → GlobalTheory.CxPts q σ := fun l => (t.equivFin.symm l).1
  refine ⟨t.card, fun l => W₀ (c l), fun l => b₀ (c l), fun l => a₀ (c l), fun l => d₀ (c l), fun y => ?_,
    fun l => hWb₀ _, fun l => ⟨h₀ _, hd₀ _⟩, fun l y hy ho hd => logNorm_of_quot ψ hr (hWb₀ _) (e₀ _) hy ho hd⟩
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨z, hz⟩, ?_⟩
  simpa [c] using hyz

end GlobalTheory.CompanionTheory.MixZ.ArchRep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

abbrev Over {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)
    (z : (Σ k, Bk n k) → ℂ) : Prop :=
  IsUnder (PtsOver.map i rfl _ y) z

abbrev LinProj (n : Fin (m + 1) → ℕ) (D : ℕ) := (((k : Fin (m + 1)) → Bk n k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)

def ratios (Ψ : LinProj n D) (z : (Σ k, Bk n k) → ℂ) : Fin D → ℂ :=
  fun a => Ψ (segre z) a.succ / Ψ (segre z) 0

open Classical in

def liftOf {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : (Σ k, Bk n k) → ℂ :=
  if h : ∃ z, Over i y z then h.choose else 0

def projCoord {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    Fin D → ℂ :=
  ratios Ψ (liftOf i y)

def IsRegAt {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D)
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : Prop :=
  LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
    (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0

def IsPiece {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n)
    (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ))
    (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) : Prop :=
  (∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, e.source ⊆ c.e.source) ∧ DifferentiableOn ℂ Γ e.target ∧
    ∀ v ∈ e.target, Over i (e.symm v) (Γ v) ∧ Γ v ∈ mcPts (ptIdeal (i (genericPoint X))) ∧
      Ψ (segre (Γ v)) = Fin.cons 1 v ∧ eval (Γ v) (map (Int.castRingHom ℂ) N) ≠ 0

def pieceSet {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n) :
    Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :=
  {y | ∃ e Γ, IsPiece i Ψ N e Γ ∧ y ∈ e.source}

theorem isOpen_pieceSet {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) (Ψ : LinProj n D) (N : Pol n) :
    IsOpen (pieceSet i Ψ N) := isOpen_iff_forall_mem_open.mpr fun _ ⟨e, Γ, hp, hy⟩ =>
  ⟨e.source, fun _ hy' => ⟨e, Γ, hp, hy'⟩, e.open_source, hy⟩

theorem segre_orbit {z z' : (Σ k, Bk n k) → ℂ} {c : Fin (m + 1) → ℂ} (h : z = fun p => c p.1 * z' p) :
    segre z = (∏ k, c k) • segre z' := by
  subst h
  funext a
  simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, Finset.prod_mul_distrib]

theorem ratios_eq_of_sameOrbit (Ψ : LinProj n D) {z z' : (Σ k, Bk n k) → ℂ} (h : SameOrbit z z')
    (h0 : Ψ (segre z') 0 ≠ 0) : ratios Ψ z = ratios Ψ z' := by
  obtain ⟨c, hc, rfl⟩ := h
  have hprod : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  funext a
  simp only [ratios, segre_orbit (c := c) rfl, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hprod

theorem ratios_of_proj (Ψ : LinProj n D) {z : (Σ k, Bk n k) → ℂ} {v : Fin D → ℂ}
    (h : Ψ (segre z) = Fin.cons 1 v) : ratios Ψ z = v := by
  funext a
  simp [ratios, h]

theorem homog_mul {f g : Pol n} {a b : Fin (m + 1) → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro d hd k
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hd)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf x hx k, hg y hy k, Pi.add_apply]

end GlobalTheory.CompanionTheory.MixZ.ArchEq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinUnfoldingIdentityStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_eisenstein_unfolding_identity : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E), Filter.Tendsto (fun S => coefSN σ b J ψ dx db Φ T S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.coefSN_tendsto | exact GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.coefSN_tendsto | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.coefSN_tendsto <;> assumption)
end

