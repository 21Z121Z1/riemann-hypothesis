import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.SqChar
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ContraChar

open ReciprocityTheory.ChartRestriction.TR.Weyl

theorem map_gtChar (σ : ℂ →+* ℂ) : ∀ (n : ℕ) (l : Fin n → ℤ) (t : Fin n → ℂ),
    σ (gtChar n l t) = gtChar n l (fun i => σ (t i))
  | 0, l, t => by simp [gtChar]
  | n + 1, l, t => by
    simp only [gtChar, map_sum, map_mul, map_zpow₀]
    refine Finset.sum_congr rfl fun mu _ => ?_
    rw [map_gtChar σ n mu]

theorem trace_sqRep_diag {n : ℕ} (lam : DomWeight n) (g : GL (Fin n) ℂ) (t : Fin n → ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = diagonal t) :
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) = gtChar n lam.w t := by
  obtain ⟨f, hf, htr⟩ := sqChar n lam g t hg
  have e : f = GlobalTheory.Branching.sqRep ℂ n lam g :=
    LinearMap.ext fun x => Subtype.ext (by rw [hf, GlobalTheory.Branching.sqRep_coe])
  rw [← e, htr]

theorem trace_sqRep_conj {n : ℕ} (lam : DomWeight n) (P g : GL (Fin n) ℂ) :
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam (P * g * P⁻¹)) =
      LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) := by
  have e2 : GlobalTheory.Branching.sqRep ℂ n lam P⁻¹ * GlobalTheory.Branching.sqRep ℂ n lam P = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  rw [map_mul (GlobalTheory.Branching.sqRep ℂ n lam), map_mul (GlobalTheory.Branching.sqRep ℂ n lam), mul_assoc,
    LinearMap.trace_mul_comm, mul_assoc, e2, mul_one]

theorem exists_poly_trace {n : ℕ} (lam : DomWeight n) :
    ∃ Q : MvPolynomial (Fin n × Fin n) ℂ, ∀ g : GL (Fin n) ℂ,
      LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) =
        detPow ℂ n g lam.detShift * MvPolynomial.eval (fun x => (g : Matrix (Fin n) (Fin n) ℂ) x.2 x.1) Q := by
  let B := Module.finBasis ℂ (nablaSq ℂ n lam)
  have hL : ∀ i, ∃ L : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      L ∘ₗ (nablaSq ℂ n lam).subtype = B.coord i := fun i => LinearMap.exists_extend (B.coord i)
  choose L hL using hL
  have hP : ∀ i, ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ A : Matrix (Fin n) (Fin n) ℂ,
      L i (Formalism.GradedWeylDivisibility.rowAct ℂ A (B i : MvPolynomial (Fin n × Fin n) ℂ)) =
        MvPolynomial.eval (fun x => A x.1 x.2) P :=
    fun i => GlobalTheory.Branching.exists_poly_rowAct_coef n n _ (L i)
  choose P hP using hP
  refine ⟨∑ i, P i, fun g => ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℂ B, Matrix.trace, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  have h1 := LinearMap.congr_fun (hL i) (GlobalTheory.Branching.sqRep ℂ n lam g (B i))
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at h1
  rw [← h1, GlobalTheory.Branching.sqRep_coe, sqAct, map_smul, hP, smul_eq_mul]
  rfl

theorem detPow_conj {n : ℕ} (P g : GL (Fin n) ℂ) (c : ℤ) :
    detPow ℂ n (P * g * P⁻¹) c = detPow ℂ n g c := by
  unfold detPow
  rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det P), mul_inv_cancel_right]

theorem trace_sqRep_of_upper {n : ℕ} (lam : DomWeight n) (T D : GL (Fin n) ℂ)
    (hT : (T : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id)
    (hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal fun i => (T : Matrix (Fin n) (Fin n) ℂ) i i) :
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam T) =
      LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam D) := by
  obtain ⟨Q, hQ⟩ := exists_poly_trace lam
  set A : Matrix (Fin n) (Fin n) ℂ := (T : Matrix (Fin n) (Fin n) ℂ) with hA
  let φ : ℂ → ℂ := fun u => MvPolynomial.eval (fun x : Fin n × Fin n => A x.2 x.1 * u ^ ((x.1 : ℕ) - (x.2 : ℕ))) Q
  have hdetT : detPow ℂ n D lam.detShift = detPow ℂ n T lam.detShift := by
    unfold detPow
    congr 2
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, hD, det_diagonal,
      ← hA, Matrix.det_of_isUpperTriangular hT]
  have hne : detPow ℂ n T lam.detShift ≠ 0 := Units.ne_zero _
  have hconj : ∀ u : ℂ, u ≠ 0 →
      LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam T) = detPow ℂ n T lam.detShift * φ u := by
    intro u hu
    let U : ℂˣ := Units.mk0 u hu
    let Du : GL (Fin n) ℂ := diagGL ℂ n fun i : Fin n => U⁻¹ ^ (i : ℕ)
    have hM : ∀ i j, ((Du * T * Du⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j =
        A i j * u ^ ((j : ℕ) - (i : ℕ)) := by
      intro i j
      change (diagonal (fun a : Fin n => ((U⁻¹ ^ (a : ℕ) : ℂˣ) : ℂ)) * A *
        diagonal (fun a : Fin n => (((U⁻¹ ^ (a : ℕ))⁻¹ : ℂˣ) : ℂ))) i j = _
      rw [mul_diagonal, diagonal_mul]
      simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, U, inv_pow, inv_inv]
      by_cases hji : j < i
      · rw [hT hji]; ring
      · have hij : (i : ℕ) ≤ j := by rw [not_lt, Fin.le_iff_val_le_val] at hji; exact hji
        have e : u ^ (j : ℕ) = u ^ (i : ℕ) * u ^ ((j : ℕ) - (i : ℕ)) := by
          rw [← pow_add, Nat.add_sub_cancel' hij]
        rw [e]
        field_simp
    rw [← trace_sqRep_conj lam Du T, hQ, detPow_conj]
    congr 1
    exact congrArg (fun f => MvPolynomial.eval f Q) (funext fun x => hM x.2 x.1)
  have hφc : Continuous φ :=
    (MvPolynomial.continuous_eval Q).comp (continuous_pi fun x => continuous_const.mul (continuous_pow _))
  have hφ : φ = fun _ => φ 1 := by
    refine Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hφc continuous_const fun u hu => ?_
    have h1 := hconj u hu
    rw [hconj 1 one_ne_zero] at h1
    exact (mul_left_cancel₀ hne h1).symm
  have h0 : φ 0 = MvPolynomial.eval (fun x => (D : Matrix (Fin n) (Fin n) ℂ) x.2 x.1) Q := by
    refine congrArg (fun f => MvPolynomial.eval f Q) (funext fun x => ?_)
    rw [hD, diagonal_apply]
    by_cases h : x.2 = x.1
    · rw [if_pos h, h, Nat.sub_self, pow_zero, mul_one]
    · rw [if_neg h]
      rcases lt_or_gt_of_ne h with h' | h'
      · rw [zero_pow (by rw [Fin.lt_def] at h'; omega), mul_zero]
      · rw [hT h', zero_mul]
  rw [hQ D, hdetT, ← h0, congrFun hφ 0, hconj 1 one_ne_zero]

theorem exists_eig {n : ℕ} (lam : DomWeight n) (g : GL (Fin n) ℂ) :
    ∃ d : Fin n → ℂ, (∀ i, d i ≠ 0) ∧ (g : Matrix (Fin n) (Fin n) ℂ).charpoly = ∏ i, (X - C (d i)) ∧
      LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) = gtChar n lam.w d := by
  obtain ⟨P, hP, hT, -⟩ :=
    GlobalTheory.CommTriang.exists_triangular ℂ Unit n (fun _ => (g : Matrix (Fin n) (Fin n) ℂ)) (fun _ _ => rfl)
  let Pu : GL (Fin n) ℂ := hP.unit
  let T : GL (Fin n) ℂ := Pu⁻¹ * g * Pu
  have hTv : (T : Matrix (Fin n) (Fin n) ℂ) = P⁻¹ * g * P := by
    simp only [T, Units.val_mul, Matrix.coe_units_inv, Pu, IsUnit.unit_spec]
  have hTt : (T : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id := by rw [hTv]; exact hT ()
  have hdet : ∀ i, (T : Matrix (Fin n) (Fin n) ℂ) i i ≠ 0 := by
    intro i h
    have hd : (T : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
    rw [Matrix.det_of_isUpperTriangular hTt] at hd
    exact hd (Finset.prod_eq_zero (Finset.mem_univ i) h)
  let D : GL (Fin n) ℂ := diagGL ℂ n fun i => Units.mk0 _ (hdet i)
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal fun i => (T : Matrix (Fin n) (Fin n) ℂ) i i := by
    change diagonal (fun a => ((Units.mk0 _ (hdet a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  refine ⟨fun i => (T : Matrix (Fin n) (Fin n) ℂ) i i, hdet, ?_, ?_⟩
  · have h := Matrix.charpoly_units_conj (Pu⁻¹) (g : Matrix (Fin n) (Fin n) ℂ)
    rw [← Matrix.coe_units_inv, inv_inv, ← Units.val_mul, ← Units.val_mul] at h
    rw [← h]
    exact Matrix.charpoly_of_isUpperTriangular _ hTt
  · have hg : g = Pu * T * Pu⁻¹ := by simp only [T, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
    rw [hg, trace_sqRep_conj, trace_sqRep_of_upper lam T D hTt hD, trace_sqRep_diag lam D _ hD]

theorem exists_perm_of_map_eq {ι β : Type} [Fintype ι] (g g' : ι → β)
    (h : Finset.univ.val.map g = Finset.univ.val.map g') :
    ∃ π : Equiv.Perm ι, ∀ i, g (π i) = g' i := by
  classical
  have hc : ∀ c, Fintype.card {i // g' i = c} = Fintype.card {i // g i = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simp only [Finset.card, Finset.filter_val]
    simpa only [eq_comm] using this.symm
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

def permGL {n : ℕ} (π : Equiv.Perm (Fin n)) : GL (Fin n) ℂ where
  val := π.toPEquiv.toMatrix
  inv := π.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]

theorem gtChar_perm {n : ℕ} (lam : DomWeight n) (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) (π : Equiv.Perm (Fin n)) :
    gtChar n lam.w (fun i => d (π i)) = gtChar n lam.w d := by
  let D : GL (Fin n) ℂ := diagGL ℂ n fun i => Units.mk0 _ (hd i)
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal d := by
    change diagonal (fun a => ((Units.mk0 _ (hd a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  have hDπ : ((permGL π * D * (permGL π)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      diagonal fun i => d (π i) := by
    rw [Units.val_mul, Units.val_mul, hD]
    change π.toPEquiv.toMatrix * diagonal d * π.symm.toPEquiv.toMatrix = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Equiv.symm_symm, submatrix_submatrix]
    exact submatrix_diagonal_equiv d π
  rw [← trace_sqRep_diag lam D d hD, ← trace_sqRep_diag lam _ _ hDπ, trace_sqRep_conj]

theorem trace_sqRep_eq_of_charpoly_eq {n : ℕ} (lam : DomWeight n) (g h : GL (Fin n) ℂ)
    (hc : (g : Matrix (Fin n) (Fin n) ℂ).charpoly = (h : Matrix (Fin n) (Fin n) ℂ).charpoly) :
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam g) = LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam h) := by
  obtain ⟨d, hd0, hdc, hdt⟩ := exists_eig lam g
  obtain ⟨d', -, hdc', hdt'⟩ := exists_eig lam h
  have hr : ∀ e : Fin n → ℂ, (∏ i, (X - C (e i))).roots = Finset.univ.val.map e := fun e => by
    rw [← roots_multiset_prod_X_sub_C (Finset.univ.val.map e), Multiset.map_map]
    rfl
  have hm : Finset.univ.val.map d = Finset.univ.val.map d' := by rw [← hr, ← hr, ← hdc, ← hdc', hc]
  obtain ⟨π, hπ⟩ := exists_perm_of_map_eq d d' hm
  rw [hdt, hdt', ← funext hπ, gtChar_perm lam d hd0 π]

theorem trace_sqRep_inv_eq_conj_chAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (lam : DomWeight n) (γ : UE E n) (v : InfinitePlace E),
    LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map v.embedding (γ⁻¹).1)) =
      starRingEnd ℂ (chAt lam (γ.1.val.charpoly.map v.embedding)) := by
  intro E _ _ _ n lam γ v
  set τ : E →+* ℂ := v.embedding with hτ
  set g : GL (Fin n) ℂ := GeneralLinearGroup.map τ γ.1 with hg
  have hinv : GeneralLinearGroup.map τ (γ⁻¹).1 = g⁻¹ := by rw [Subgroup.coe_inv, map_inv]
  have hgv : (g : Matrix (Fin n) (Fin n) ℂ) = (γ.1 : Matrix (Fin n) (Fin n) E).map τ := rfl
  have hcp : γ.1.val.charpoly.map τ = (g : Matrix (Fin n) (Fin n) ℂ).charpoly := by rw [hgv, charpoly_map]
  have hu : ((g : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ * (g : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    have h : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (γ.1 : Matrix (Fin n) (Fin n) E) * 1 *
        (γ.1 : Matrix (Fin n) (Fin n) E) = 1 := γ.2
    rw [Matrix.mul_one] at h
    have h2 := congrArg (fun M => M.map τ) h
    simp only [Matrix.map_mul, Matrix.map_one τ (map_zero τ) (map_one τ)] at h2
    rw [← h2, hgv]
    congr 1
    ext i j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
    exact (IsCMField.complexEmbedding_complexConj E τ _).symm
  have hginv : ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      ((g : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hu
  obtain ⟨d, hd0, hdc, -⟩ := exists_eig lam g
  have hcd : ∀ i, starRingEnd ℂ (d i) ≠ 0 := fun i => by simpa using hd0 i
  let Dc : GL (Fin n) ℂ := diagGL ℂ n fun i => Units.mk0 _ (hcd i)
  let D : GL (Fin n) ℂ := diagGL ℂ n fun i => Units.mk0 _ (hd0 i)
  have hDc : (Dc : Matrix (Fin n) (Fin n) ℂ) = diagonal fun i => starRingEnd ℂ (d i) := by
    change diagonal (fun a => ((Units.mk0 _ (hcd a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  have hD : (D : Matrix (Fin n) (Fin n) ℂ) = diagonal d := by
    change diagonal (fun a => ((Units.mk0 _ (hd0 a) : ℂˣ) : ℂ)) = _
    simp only [Units.val_mk0]
  have cpD : (D : Matrix (Fin n) (Fin n) ℂ).charpoly = (g : Matrix (Fin n) (Fin n) ℂ).charpoly := by
    rw [hD, charpoly_diagonal, hdc]
  have cpDc : ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly = (Dc : Matrix (Fin n) (Fin n) ℂ).charpoly := by
    rw [hginv, charpoly_transpose, charpoly_map, hdc, hDc, charpoly_diagonal, Polynomial.map_prod]
    simp
  rw [hinv, hcp, trace_sqRep_eq_of_charpoly_eq lam _ Dc cpDc, trace_sqRep_diag lam Dc _ hDc]
  have hex : ∃ h : GL (Fin n) ℂ, (h : Matrix (Fin n) (Fin n) ℂ).charpoly = (g : Matrix (Fin n) (Fin n) ℂ).charpoly :=
    ⟨g, rfl⟩
  unfold chAt
  rw [dif_pos hex, trace_sqRep_eq_of_charpoly_eq lam _ D (hex.choose_spec.trans cpD.symm),
    trace_sqRep_diag lam D _ hD, map_gtChar]

end GlobalTheory.ContraChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralEqSumSmallerLevelStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegral_eq_sum_smallerLevel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → (∀ k ∈ K, θ k ∈ K) → ∀ K' : Subgroup G, IsLevel θ K K' → ∀ (δ : G) (f : G → ℂ), IsHecke K' f → (∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0) → {q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G) | f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) ≠ 0}.Finite → twOrb θ K δ f = ((K'.relIndex K : ℕ) : ℂ)⁻¹ * twOrb θ K' δ f ∧ twOrb θ K' δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K' : Set G), (((twCent θ δ ⊓ K'.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) * f ((Quotient.out q)⁻¹ * δ * θ (Quotient.out q)) := by
  first | exact @GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel | exact GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel | (intros; apply GlobalTheory.BCT.OrbLev.twOrb_eq_sum_smallerLevel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermDoubleCosetInvari
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

variable {G : Type} [Group G]

theorem twCent_mul_inv_conj (θ : G →* G) (δ : G) {t : G} (ht : t ∈ twCent θ δ) (z : G) :
    (t * z)⁻¹ * δ * θ (t * z) = z⁻¹ * δ * θ z := by
  have htd : t * δ = δ * θ t := ht
  rw [map_mul, _root_.mul_inv_rev]
  calc z⁻¹ * t⁻¹ * δ * (θ t * θ z) = z⁻¹ * (t⁻¹ * (δ * θ t)) * θ z := by simp only [mul_assoc]
    _ = z⁻¹ * δ * θ z := by rw [← htd, inv_mul_cancel_left]

theorem twCent_inf_map_conj (θ : G →* G) (K : Subgroup G) (δ : G)
    (hcomm : ∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) {t : G} (ht : t ∈ twCent θ δ) (y : G) {k : G}
    (hk : k ∈ K) :
    twCent θ δ ⊓ K.map (MulAut.conj (t * y * k)).toMonoidHom = twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hxT, z, hz, rfl⟩
    refine ⟨hxT, k * z * k⁻¹, K.mul_mem (K.mul_mem hk hz) (K.inv_mem hk), ?_⟩
    have hx : t * y * k * z * (t * y * k)⁻¹ = t * (y * (k * z * k⁻¹) * y⁻¹) * t⁻¹ := by group
    rw [hx] at hxT ⊢
    have hlT : y * (k * z * k⁻¹) * y⁻¹ ∈ twCent θ δ := by
      have h := (twCent θ δ).mul_mem ((twCent θ δ).mul_mem ((twCent θ δ).inv_mem ht) hxT) ht
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
    rw [hcomm t ht _ hlT, mul_inv_cancel_right]
  · rintro ⟨hxT, z, hz, rfl⟩
    refine ⟨hxT, k⁻¹ * z * k, K.mul_mem (K.mul_mem (K.inv_mem hk) hz) hk, ?_⟩
    have hx : t * y * k * (k⁻¹ * z * k) * (t * y * k)⁻¹ = t * (y * z * y⁻¹) * t⁻¹ := by group
    rw [hx, hcomm t ht _ hxT, mul_inv_cancel_right]

theorem twTerm_mul_mul [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (hcomm : ∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a)
    (hidx : ∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))).index ≠ 0) :
    ∀ t ∈ twCent θ δ, ∀ y, ∀ k ∈ K, twTerm θ K δ f (t * y * k) = twTerm θ K δ f y := by
  intro t ht y k hk
  unfold twTerm
  rw [twCent_inf_map_conj θ K δ hcomm ht y hk]
  congr 1
  have key := (GlobalTheory.AvgLin.avg_linear_translate_const K (fun k' : K => f ((y * k')⁻¹ * δ * θ (y * k'))) (fun k' : K => f ((y * k')⁻¹ * δ * θ (y * k')))
    0 ⟨k, hk⟩ (hidx y) (hidx y)).2.2.1
  rw [← key]
  congr 1
  funext k'
  congr 1
  rw [Subgroup.coe_mul, Subgroup.coe_mk, mul_assoc t y, mul_assoc t (y * k), ← mul_assoc y k]
  exact twCent_mul_inv_conj θ δ ht _

theorem twTerm_inv : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ),
    (∀ a ∈ twCent θ δ, ∀ b ∈ twCent θ δ, a * b = b * a) →
    (∀ y : G, (rStab fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))).index ≠ 0) →
    ∀ t ∈ twCent θ δ, ∀ y, ∀ k ∈ K, GlobalTheory.EulerAbs.twTerm θ K δ f (t * y * k) = GlobalTheory.EulerAbs.twTerm θ K δ f y :=
  fun θ K δ f hcomm hidx => twTerm_mul_mul θ K δ f hcomm hidx

end GlobalTheory.EulerAbs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralPointTermOneUnramified
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerAbs

theorem avg_const_one {H : Type} [Group H] : avg (fun _ : H => (1 : ℂ)) = 1 := by
  have hs : rStab (fun _ : H => (1 : ℂ)) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (QuotientGroup.mk 1)
  rw [finsum_unique]
  simp

theorem twTerm_one_eq_one {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G)
    (hθ : ∀ k ∈ K, θ k ∈ K) (hδ : δ ∈ K) (hc : cptPart (twCent θ δ) ≤ K) :
    twTerm θ K δ ((K : Set G).indicator 1) 1 = 1 := by
  have hT : cptPart (twCent θ δ) ≤ twCent θ δ := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro t ht; exact ht.1
  have hmap : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
    ext x; simp
  have hidx : ((twCent θ δ ⊓ K.map (MulAut.conj (1 : G)).toMonoidHom).relIndex (cptPart (twCent θ δ))) = 1 := by
    rw [hmap, Subgroup.relIndex_eq_one]
    exact le_inf hT hc
  have hf : (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((1 * (k : G))⁻¹ * δ * θ (1 * k))) = fun _ => 1 := by
    funext k
    rw [Set.indicator_of_mem]
    · rfl
    · simp only [one_mul, SetLike.mem_coe]
      exact K.mul_mem (K.mul_mem (K.inv_mem k.2) hδ) (hθ _ k.2)
  unfold twTerm
  rw [hidx, hf, avg_const_one]
  simp

end GlobalTheory.EulerAbs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentConjLeviEqBlockUpperTwistedSylvesterStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_conj_levi_eq_blockUpperTwistedSylvester : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), (blk h w 1 X)⁻¹ * blk h w m 0 * blk h w 1 X = blk h w m (GlobalTheory.LeviDesc.adL m.1 m.2.val X) := by
  first | exact @GlobalTheory.LeviDesc.LeviBlockConjugation.conj_blk | exact GlobalTheory.LeviDesc.LeviBlockConjugation.conj_blk | (intros; apply GlobalTheory.LeviDesc.LeviBlockConjugation.conj_blk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBorelEqDiagonalMulUnipotentStatement
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryBorel_eq_diagonal_mul_unipotent : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (β : GU σ n), IsBorelU β →
    ∃ t ν : GU σ n, β = t * ν ∧ IsUnipU ν ∧
      (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) ∧
      ∀ i, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((β : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  first | exact @GlobalTheory.UnitaryBorel.borel_eq_diag_mul_unip_sameDiag | exact GlobalTheory.UnitaryBorel.borel_eq_diag_mul_unip_sameDiag | (intros; apply GlobalTheory.UnitaryBorel.borel_eq_diag_mul_unip_sameDiag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCommutingEqMulNormOneTorusStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_commuting_eq_mul_normOneTorus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (Q : (w.adicCompletion E)[X]) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), Fits w e B Q u → IsModelMap w e B u x γ ψ → ∀ h : GLw n w, h ∈ UL n w → h * γ = γ * h → torusOf w B ψ h ∈ B.T ∧ ∀ y, ψ ((torusOf w B ψ h : B.A) * y) = h.val *ᵥ ψ y := by
  first | exact @GlobalTheory.KapTorus.torusOf_mem_of_mem_UL_commute | exact GlobalTheory.KapTorus.torusOf_mem_of_mem_UL_commute | (intros; apply GlobalTheory.KapTorus.torusOf_mem_of_mem_UL_commute <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOneStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeCharCM_splitPlace_mul_conjPlace_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w u : Pl E, u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ k : Eˣ, μ.locK u k * μ.locK w (Units.map (MonoidHomClass.toMonoidHom (IsCMField.complexConj E)) k) = 1 := by
  first | exact @GlobalTheory.BCT.SplitChar.locK_mul_locK_conj | exact GlobalTheory.BCT.SplitChar.locK_mul_locK_conj | (intros; apply GlobalTheory.BCT.SplitChar.locK_mul_locK_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorLevelIndicatorEqInvIndexStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeOperator_levelIndicator_eq_inv_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ φ ∈ fixed (RF E n) (globLev S K'), hop S K' (fun w => (K' w : Set (UL n w)).indicator 1) φ = (∏ᶠ w ∈ S, (((K' w).relIndex (KL n w) : ℕ) : ℂ))⁻¹ • φ := by
  first | exact @GlobalTheory.BCT.hop_indicator_level | exact GlobalTheory.BCT.hop_indicator_level | (intros; apply GlobalTheory.BCT.hop_indicator_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeEqIffInvMulIntegralStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLattice_eq_iff_inv_mul_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ q q' : UL n w, unitLat e B ψ q = unitLat e B ψ q' ↔ q⁻¹ * q' ∈ KL n w := by
  first | exact @GlobalTheory.InertUnitLat.unitLat_eq_iff | exact GlobalTheory.InertUnitLat.unitLat_eq_iff | (intros; apply GlobalTheory.InertUnitLat.unitLat_eq_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeIsLatticeSelfDualHermitianModelStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLattice_isLattice_selfDual_hermitianModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  first | exact @GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual | exact GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual | (intros; apply GlobalTheory.InertUnitOrb.SelfDualLat.unitLat_isLat_selfDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToTransposeGramGroupMapSurjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Matrix Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryToTransposeGramGroupMap_surjective : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • Matrix.reindex e e X.gramᵀ), Function.Surjective (GlobalTheory.SquareAgree.kapX X e hJ) := by
  first | exact @GlobalTheory.SquareAgree.kapX_surjective | exact GlobalTheory.SquareAgree.kapX_surjective | (intros; apply GlobalTheory.SquareAgree.kapX_surjective <;> assumption)
end

