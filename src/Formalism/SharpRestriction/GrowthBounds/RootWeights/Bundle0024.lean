import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0023
import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0022

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.LaurentDegreesSubstitutionSubset
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section inv

variable {A : Type*} [CommRing A] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)

theorem laurentExpand_C (σ : Type*) (b : LaurentPolynomial A) :
    mul_Phi σ A (C b) = AddMonoidAlgebra.mapRingHom ℤ (C : A →+* MvPolynomial σ A) b := by
  simp [mul_Phi]

theorem laurentExpand_X (σ : Type*) (v : σ) :
    mul_Phi σ A (X v) = LaurentPolynomial.C (X v) := by
  simp [mul_Phi]

theorem mapRingHom_laurent_C {A' : Type*} [CommRing A'] (f : A →+* A') (a : A) :
    AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  ext k
  rw [AddMonoidAlgebra.coeff_mapRingHom, LaurentPolynomial.C_apply, LaurentPolynomial.C_apply]
  split_ifs <;> simp

private theorem mapRingHom_laurent_comp {A₁ B₁ D₁ : Type*} [CommRing A₁] [CommRing B₁] [CommRing D₁]
    (f : B₁ →+* D₁) (g : A₁ →+* B₁) (x : LaurentPolynomial A₁) :
    AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.mapRingHom ℤ g x) =
      AddMonoidAlgebra.mapRingHom ℤ (f.comp g) x := by
  ext k
  simp only [AddMonoidAlgebra.coeff_mapRingHom, RingHom.comp_apply]

theorem laurentExpand_substitution (M M' : Matrix (Fin n) (Fin n) A) (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_Phi (ι × Fin n) A (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) =
      AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M') (mul_Phi (ι × Fin n) A Q) := by
  have key : (mul_Phi (ι × Fin n) A).comp
      (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C)) =
      (AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M')).comp (mul_Phi (ι × Fin n) A) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      have hC : (matrixSubst LL S (RingHom.id A) M M').comp (C : A →+* MvPolynomial (ι × Fin n) A) = C :=
        RingHom.ext fun a => by simp only [RingHom.comp_apply, matrixSubst_C, RingHom.id_apply]
      simp only [RingHom.comp_apply, matrixSubst_C, RingHom.id_apply, laurentExpand_C, mapRingHom_laurent_comp, hC]
    · intro v
      simp only [RingHom.comp_apply, matrixSubst_X, laurentExpand_X, mapRingHom_laurent_C]
      split_ifs <;> simp [map_sum, laurentExpand_C, laurentExpand_X, mapRingHom_laurent_C, Matrix.map_apply]
  exact congrArg (fun f => f Q) key

theorem laurent_degrees_substitution_subset (M M' : Matrix (Fin n) (Fin n) A) (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_degs (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) ⊆
      mul_degs Q := by
  rw [mul_degs_eq (matrixSubst LL S (RingHom.id _) _ _ Q), laurentExpand_substitution]
  have key : (AddMonoidAlgebra.mapRingHom ℤ (matrixSubst LL S (RingHom.id A) M M')).comp (mul_Phi (ι × Fin n) A) =
      eval₂Hom (AddMonoidAlgebra.mapRingHom ℤ ((matrixSubst LL S (RingHom.id A) M M').comp C))
        (fun v => LaurentPolynomial.C (matrixSubst LL S (RingHom.id A) M M' (X v))) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp only [RingHom.comp_apply, laurentExpand_C, mapRingHom_laurent_comp, MvPolynomial.eval₂Hom_C]
    · intro v
      simp only [RingHom.comp_apply, laurentExpand_X, mapRingHom_laurent_C, MvPolynomial.eval₂Hom_X']
  have e := congrArg (fun f => f Q) key
  simp only [RingHom.comp_apply] at e
  rw [e]
  exact mul_Psi_support _ _ Q

theorem laurent_degrees_substitution_eq (M M' : Matrix (Fin n) (Fin n) A) (h : M * M' = 1)
    (Q : MvPolynomial (ι × Fin n) (LaurentPolynomial A)) :
    mul_degs (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) =
      mul_degs Q := by
  apply Finset.Subset.antisymm (laurent_degrees_substitution_subset LL S M M' Q)
  have h' : M' * M = 1 := by
    first
    | exact Matrix.mul_eq_one_comm.1 h
    | exact mul_eq_one_comm.1 h
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) h
    | exact Matrix.nonsing_inv_mul_cancel_of_mul_eq_one h
  have hQ : matrixSubst LL S (RingHom.id _) (M'.map LaurentPolynomial.C) (M.map LaurentPolynomial.C)
      (matrixSubst LL S (RingHom.id _) (M.map LaurentPolynomial.C) (M'.map LaurentPolynomial.C) Q) = Q := by
    rw [matrixSubst_comp, ← Matrix.map_mul, h', Matrix.map_one _ (map_zero _) (map_one _), matrixSubst_one,
      MvPolynomial.map_id]
  conv_lhs => rw [← hQ]
  exact laurent_degrees_substitution_subset LL S M' M _

end inv

private theorem genericMatrixBis_mul_genericMatrixInverse (R : Type) [Field R] (n : ℕ) : genericMatrixRootWeights R n * genericMatrixInverse R n = 1 := by
  have e : genericMatrixInverse R n = IsLocalization.Away.invSelf (S := GLCoord R n) (genMat R n).det •
      (genMat R n).adjugate.map (algebraMap (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)) := by
    ext a b
    simp [genericMatrixInverse, Matrix.smul_apply]
  rw [e, genericMatrixRootWeights, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  ext a b
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  · simp [Matrix.smul_apply, Matrix.one_apply, hab]

private theorem map_C_genericMatrixBis_and_inverse_eq_gL_gLinv (R : Type) [Field R] (n : ℕ) :
    (genericMatrixRootWeights R n).map LaurentPolynomial.C = gL R n ∧ (genericMatrixInverse R n).map LaurentPolynomial.C = gLinv R n := by
  constructor <;> (ext a b; simp [genericMatrixRootWeights, genericMatrixInverse, gL, gLinv])

private theorem support_laurent_C_mul_T_of_ne_zero {B : Type*} [CommRing B] (h : B) (hh : h ≠ 0) (w : ℤ) :
    (LaurentPolynomial.C h * LaurentPolynomial.T w).coeff.support = {w} := by
  rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
  exact Finsupp.support_single_ne_zero _ hh

private theorem laurent_C_mul_T_eq_zero_iff {B : Type*} [CommRing B] (h : B) (w : ℤ) :
    LaurentPolynomial.C h * LaurentPolynomial.T w = 0 ↔ h = 0 := by
  constructor
  · intro e
    have := congrArg (fun p : LaurentPolynomial B => p.coeff w) e
    rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single] at this
    simpa using this
  · rintro rfl
    simp

theorem twist_exponents_are_weight_entries : TwistExponentsAreWeightEntries := by
  intro R _ ι _ LL n S j G
  classical
  let u : (GLLaurent R n)ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  let D : Fin n → (GLLaurent R n)ˣ := fun a => if a = j then u else 1
  have hD : (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n)) =
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T 1 else 1) := by
    congr 1; funext a; by_cases h : a = j <;> simp [D, h, u]
  have hD' : (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n)) =
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T (-1) else 1) := by
    congr 1; funext a; by_cases h : a = j <;> simp [D, h, u]
  obtain ⟨hgL, hgLinv⟩ := map_C_genericMatrixBis_and_inverse_eq_gL_gLinv R n
  have hcoefL : (LaurentPolynomial.C).comp (coefficientMap R n) = coefL R n := rfl
  have hH : MvPolynomial.map LaurentPolynomial.C (genericTranslate LL S G) =
      matrixSubst LL S (coefL R n) (gLinv R n) (gL R n) G := by
    rw [genericTranslate, map_matrixSubst, hgL, hgLinv, hcoefL]
  have hT : twistSub LL S j G = matrixSubst LL S (RingHom.id _) (gL R n) (gLinv R n)
      (matrixSubst LL S (RingHom.id _) (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n))
        (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n))
        (MvPolynomial.map LaurentPolynomial.C (genericTranslate LL S G))) := by
    rw [hH, hD, hD', matrixSubst_comp, matrixSubst_comp, twistSub_eq_matrixSubst]
    simp only [twistMat, Matrix.mul_assoc]
  have hprod : ∀ w : Fin n → ℤ, (((∏ a, D a ^ w a) : (GLLaurent R n)ˣ) : GLLaurent R n) =
      LaurentPolynomial.T (w j) := by
    intro w
    rw [Finset.prod_eq_single j (fun a _ ha => by simp [D, ha]) (fun h => absurd (Finset.mem_univ j) h)]
    simp only [D, if_pos rfl]
    rcases w j with k | k
    · rw [Int.ofNat_eq_coe, zpow_natCast, Units.val_pow_eq_pow_val]
      simp only [u, LaurentPolynomial.T_pow, mul_one]
    · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      simp only [u, Units.inv_mk, LaurentPolynomial.T_pow]
      congr 1
      rw [Int.negSucc_eq]
      push_cast
      ring
  set H := genericTranslate LL S G with hHdef
  set P := matrixSubst LL S (RingHom.id _) (Matrix.diagonal fun a => ((D a : (GLLaurent R n)ˣ) : GLLaurent R n))
        (Matrix.diagonal fun a => (((D a)⁻¹ : (GLLaurent R n)ˣ) : GLLaurent R n))
        (MvPolynomial.map LaurentPolynomial.C H) with hPdef
  have hcoef : ∀ m, P.coeff m = LaurentPolynomial.C (H.coeff m) * LaurentPolynomial.T (wtS LL S m j) := by
    intro m
    rw [hPdef]
    conv_lhs => rw [H.as_sum]
    simp only [map_sum, MvPolynomial.map_monomial,
      torus_acts_through_weight (GLLaurent R n) (GLLaurent R n) ι LL n S (RingHom.id _) D, RingHom.id_apply, hprod,
      MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hm
    · rfl
    · rw [MvPolynomial.notMem_support_iff.mp hm]
      simp
  have hsupp : P.support = H.support := by
    ext m
    rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, hcoef, Ne, laurent_C_mul_T_eq_zero_iff]
  show mul_degs (twistSub LL S j G) = _
  rw [hT, ← hgL, ← hgLinv, laurent_degrees_substitution_eq LL S (genericMatrixRootWeights R n) (genericMatrixInverse R n) (genericMatrixBis_mul_genericMatrixInverse R n)]
  rw [mul_degs, hsupp, ← Finset.biUnion_singleton]
  apply Finset.biUnion_congr rfl
  intro m hm
  rw [hcoef]
  exact support_laurent_C_mul_T_of_ne_zero _ (MvPolynomial.mem_support_iff.mp hm) _

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.RestAOfHighestVectorIntegrality
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def HighestWeightVectorIntegrality : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (lam : Fin n → ℤ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] (E : GLOps n (KK O) V) (v : V), IsIrrHW E lam v →
      v ∈ Nabla (O := O) E lam v

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightConditionFromIntegralForm
section
noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_Hs (E : GLOps n K V) (lam : Fin n → ℤ) : Submodule K V :=
  weightSp E lam ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

theorem cr_mem_Hs (E : GLOps n K V) (lam : Fin n → ℤ) (x : V) :
    x ∈ cr_Hs E lam ↔ x ∈ weightSp E lam ∧ ∀ a b : Fin n, a < b → E a b x = 0 := by
  simp only [cr_Hs, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem cr_compl [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) (hR : SatisfiesGLRelations E)
    (hT : (⨆ ν, weightSp E ν) = ⊤) (W : Submodule K V) (hW : IsStableUnderOperators E W) :
    ∃ W' : Submodule K V, IsCompl W W' ∧ IsStableUnderOperators E W' := by
  classical
  choose Q hQ using fun lam : Fin n → ℤ => Submodule.exists_isCompl (cr_Hs E lam ⊓ W)
  set H' : (Fin n → ℤ) → Submodule K V := fun lam => cr_Hs E lam ⊓ Q lam with hH'
  set W' : Submodule K V := ⨆ lam, isotypicPartIn E (H' lam) lam with hW'
  have hW'st : IsStableUnderOperators E W' := v2rep_iSup_stable E _ fun mu => v2rep_isoIn_stable E (H' mu) mu
  refine ⟨W', ⟨?_, ?_⟩, hW'st⟩
  ·
    rw [disjoint_iff]
    by_contra hne
    have hst : IsStableUnderOperators E (W ⊓ W') := fun a b x hx => ⟨hW a b x hx.1, hW'st a b x hx.2⟩
    obtain ⟨lam, w, hwm, hw⟩ := v2rep_exists_hwv E hR (W ⊓ W') hst (le_top.trans hT.ge) hne
    have hdl : Dominant lam := cr_hwv_dom E hR hw
    obtain ⟨r, hr1, hr2⟩ := casimir_polynomial_isolates_level E hR H' w hwm.2 (cr_c lam)
    rw [cr_aeval_eig (cr_C E) _ w (cr_C_hwv E hR lam w hw) r, hr1, one_smul] at hr2
    have hle : (⨆ ν ∈ {ν : Fin n → ℤ | cr_c ν = cr_c lam}, isotypicPartIn E (H' ν) ν) ≤
        H' lam ⊔ cr_WS E {τ | τ ≠ lam} := by
      refine iSup₂_le fun ν hν x hx => ?_
      by_cases hνl : ν = lam
      · subst hνl
        have hsub : cr_Low ν ⊆ {τ | τ ≠ ν} := by
          intro τ hτ h
          have h2 := hτ.2
          rw [h, sub_self, cr_ht_zero] at h2
          exact lt_irrefl _ h2
        exact (sup_le_sup inf_le_left (cr_WS_mono E hsub)) (cr_isoIn_le E hR (H' ν) ν hx)
      · by_cases hx0 : x = 0
        · rw [hx0]; exact zero_mem _
        · have hd := cr_isoIn_dom E hR (H' ν) hx hx0
          have hsub : weightsBelow ν ⊆ {τ | τ ≠ lam} := by
            intro τ hτ h
            have hτ' : ν - τ ∈ cr_Pos n := hτ
            rw [h] at hτ'
            rcases cr_Pos_zero_or hτ' with h0 | h0
            · exact hνl (sub_eq_zero.1 h0)
            · have := cr_c_lt hd hdl hτ' h0
              have hν' : cr_c ν = cr_c lam := hν
              omega
          exact Submodule.mem_sup_right (cr_WS_mono E hsub (isotypic_component_le_lower_weights E hR (H' ν) ν hx))
    obtain ⟨h, hh, l, hl, hsum⟩ := Submodule.mem_sup.1 (hle hr2)
    have hhw : h ∈ weightSp E lam := ((cr_mem_Hs E lam h).1 hh.1).1
    have hl0 : l = 0 := by
      by_contra hl0
      have hlw : l ∈ weightSp E lam := by
        have : l = w - h := by rw [← hsum]; abel
        rw [this]; exact Submodule.sub_mem _ hw.2.1 hhw
      exact (cr_WS_mem E hl hlw hl0) rfl
    rw [hl0, add_zero] at hsum
    rw [hsum] at hh
    have hwHs : w ∈ cr_Hs E lam ⊓ W := ⟨hh.1, hwm.1⟩
    have := (hQ lam).disjoint.le_bot ⟨hwHs, hh.2⟩
    exact hw.1 ((Submodule.mem_bot K).1 this)
  ·
    rw [codisjoint_iff, eq_top_iff]
    refine (cr_CR E hR hT ⊤ (fun _ _ _ _ => trivial)).trans (iSup_le fun mu => ?_)
    refine Submodule.span_le.2 ?_
    rintro x ⟨u, hu, v, _, hv, rfl⟩
    have hvHs : v ∈ cr_Hs E mu := (cr_mem_Hs E mu v).2 ⟨hv.2.1, hv.2.2⟩
    have hvt : v ∈ (cr_Hs E mu ⊓ W) ⊔ Q mu := by rw [(hQ mu).sup_eq_top]; trivial
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Submodule.mem_sup.1 hvt
    have hv2Hs : v2 ∈ cr_Hs E mu := by
      have : v2 = (v1 + v2) - v1 := by abel
      rw [this]; exact Submodule.sub_mem _ hvHs hv1.1
    show u (v1 + v2) ∈ W ⊔ W'
    rw [map_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (v2rep_Umon_stable E W hW u hu v1 hv1.2))
      (Submodule.mem_sup_right ?_)
    by_cases h0 : v2 = 0
    · rw [h0, map_zero]; exact zero_mem _
    · have h2 := (cr_mem_Hs E mu v2).1 hv2Hs
      exact Submodule.mem_iSup_of_mem mu (Submodule.subset_span ⟨u, hu, v2, ⟨hv2Hs, hv2⟩, ⟨h0, h2.1, h2.2⟩, rfl⟩)

theorem weight_condition_from_integral_form (D : Formalism.BasicNotions.D7) : adm2 D := by
  intro K V _ _ _ _ _ n E hE W hW
  exact cr_compl E hE.1 hE.2.2 W hW

end Formalism.MainNotions.G.GLWeightTheory
end
end

