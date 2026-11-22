import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTwinFdegNeZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine

open MvPolynomial Matrix Equiv

namespace FdegNeZero

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def colExp (j N : ℕ) (l : Fin N) : ℕ := if (l : ℕ) < j then j - 1 - l else N - 1 - l

def blkMat (j : ℕ) (τ : Ψ) : Matrix (Fin N) (Fin N) (Rts Ψ N) :=
  Matrix.of fun i l => if ((i : ℕ) < j ↔ (l : ℕ) < j) then X (τ, i) ^ colExp j N l else 0

def bigMat (j : ℕ) : Matrix (Ψ × Fin N) (Ψ × Fin N) (Rts Ψ N) :=
  Matrix.of fun x l => if x.1 = l.1 ∧ ((x.2 : ℕ) < j ↔ (l.2 : ℕ) < j) then X x ^ colExp j N l.2 else 0

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem det_blkMat (j : ℕ) (hj : j ≤ N) (τ : Ψ) :
    (blkMat (Ψ := Ψ) (N := N) j τ).det = altRho j (yv j hj τ) * altRho (N - j) (zv j τ) := by
  let e : Fin j ⊕ Fin (N - j) ≃ Fin N := finSumFinEquiv.trans (finCongr (by omega))
  rw [← det_submatrix_equiv_self e, ← Matrix.fromBlocks_toBlocks ((blkMat j τ).submatrix e e)]
  have h21 : ((blkMat (Ψ := Ψ) (N := N) j τ).submatrix e e).toBlocks₂₁ = 0 := by
    ext a b
    simp [toBlocks₂₁, blkMat, e]
  rw [h21, det_fromBlocks_zero₂₁]
  congr 1
  · unfold altRho
    congr 1
    refine Matrix.ext fun a b => ?_
    simp [toBlocks₁₁, blkMat, e, yv, colExp]
    rfl
  · unfold altRho
    congr 1
    refine Matrix.ext fun a b => ?_
    simp [toBlocks₂₂, blkMat, e, zv, colExp]
    rw [show N - 1 - (j + (b : ℕ)) = N - j - 1 - b by omega]
    rfl

theorem det_bigMat (j : ℕ) (hj : j ≤ N) : (bigMat (Ψ := Ψ) (N := N) j).det = fibV j hj := by
  have h : bigMat (Ψ := Ψ) (N := N) j =
      (blockDiagonal fun τ => blkMat (Ψ := Ψ) (N := N) j τ).submatrix (Equiv.prodComm Ψ (Fin N))
        (Equiv.prodComm Ψ (Fin N)) := by
    refine Matrix.ext fun x l => ?_
    obtain ⟨x1, x2⟩ := x
    obtain ⟨l1, l2⟩ := l
    simp only [bigMat, blkMat, of_apply, submatrix_apply, Equiv.prodComm_apply, blockDiagonal_apply, Prod.fst_swap,
      Prod.snd_swap]
    by_cases h1 : x1 = l1
    · subst h1
      simp
    · simp [h1]
  rw [h, det_submatrix_equiv_self, det_blockDiagonal, fibV]
  exact Finset.prod_congr rfl fun τ _ => det_blkMat j hj τ

theorem rename_det_bigMat (j : ℕ) (w : Perm (Ψ × Fin N)) (hw : w ∈ G0 j) :
    rename w (bigMat (Ψ := Ψ) (N := N) j).det = ((Perm.sign w : ℤ) : ℚ) • (bigMat j).det := by
  have hw' : ∀ x, (w x).1 = x.1 ∧ (((w x).2 : ℕ) < j ↔ (x.2 : ℕ) < j) := (Finset.mem_filter.mp hw).2
  rw [AlgHom.map_det]
  have h : (rename w : Rts Ψ N →ₐ[ℚ] Rts Ψ N).mapMatrix (bigMat j) = (bigMat j).submatrix w id := by
    refine Matrix.ext fun x l => ?_
    have e : ((w x).1 = l.1 ∧ (((w x).2 : ℕ) < j ↔ (l.2 : ℕ) < j)) ↔
        (x.1 = l.1 ∧ ((x.2 : ℕ) < j ↔ (l.2 : ℕ) < j)) := by rw [(hw' x).1, (hw' x).2]
    simp only [AlgHom.mapMatrix_apply, map_apply, bigMat, of_apply, submatrix_apply, id, e]
    split_ifs <;> simp
  rw [h, det_permute, MvPolynomial.smul_eq_C_mul]
  congr 1

theorem antisym_fibV (j : ℕ) (hj : j ≤ N) :
    antisym (G0 j) (fibV (Ψ := Ψ) j hj) = ((G0 (Ψ := Ψ) (N := N) j).card : ℚ) • fibV j hj := by
  rw [antisym, ← det_bigMat j hj, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [rename_det_bigMat j w hw, smul_smul, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

def rev (j : ℕ) (hj : j ≤ N) (i : Fin N) : Fin N :=
  ⟨if (i : ℕ) < j then j - 1 - i else N - 1 + j - i, by split_ifs <;> omega⟩

theorem rev_rev (j : ℕ) (hj : j ≤ N) (i : Fin N) : rev j hj (rev j hj i) = i := by
  apply Fin.ext
  simp only [rev]
  split_ifs <;> omega

def rho (j : ℕ) (hj : j ≤ N) : Perm (Ψ × Fin N) :=
  Function.Involutive.toPerm (fun x => (x.1, rev j hj x.2)) fun x => by simp [rev_rev]

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem rho_apply (j : ℕ) (hj : j ≤ N) (x : Ψ × Fin N) : rho j hj x = (x.1, rev j hj x.2) := rfl

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem rho_mem (j : ℕ) (hj : j ≤ N) (l : Ψ × Fin N) :
    (rho j hj l).1 = l.1 ∧ ((((rho j hj l).2 : Fin N) : ℕ) < j ↔ (l.2 : ℕ) < j) := by
  simp only [rho_apply, rev, true_and]
  split_ifs <;> omega

theorem prod_bigMat_of (j : ℕ) (σ : Perm (Ψ × Fin N))
    (hσ : ∀ l, (σ l).1 = l.1 ∧ (((σ l).2 : ℕ) < j ↔ (l.2 : ℕ) < j)) :
    ∏ l, bigMat (Ψ := Ψ) (N := N) j (σ l) l = monomial (∑ l, Finsupp.single (σ l) (colExp j N l.2)) 1 := by
  rw [monomial_sum_one]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [bigMat, (hσ l).1, (hσ l).2, X_pow_eq_monomial]

theorem sum_single_apply (j : ℕ) (σ : Perm (Ψ × Fin N)) (l : Ψ × Fin N) :
    (∑ l', Finsupp.single (σ l') (colExp j N l'.2)) (σ l) = colExp j N l.2 := by
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, σ.injective.eq_iff]

theorem sum_single_rho (j : ℕ) (hj : j ≤ N) :
    (∑ l, Finsupp.single (rho (Ψ := Ψ) j hj l) (colExp j N l.2)) = delta0 j := by
  refine Finsupp.ext fun x => ?_
  obtain ⟨l, rfl⟩ := (rho (Ψ := Ψ) j hj).surjective x
  rw [sum_single_apply]
  simp only [delta0, Finsupp.coe_equivFunOnFinite_symm, rho_apply, rev, colExp]
  split_ifs <;> omega

theorem coeff_det_bigMat (j : ℕ) (hj : j ≤ N) :
    coeff (delta0 j) (bigMat (Ψ := Ψ) (N := N) j).det = ((Perm.sign (rho (Ψ := Ψ) j hj) : ℤ) : ℚ) := by
  rw [det_apply, coeff_sum, Finset.sum_eq_single (rho j hj)]
  · rw [Units.smul_def, coeff_smul, prod_bigMat_of j _ (rho_mem j hj), coeff_monomial,
      if_pos (sum_single_rho j hj)]
    simp
  · intro σ _ hne
    rw [Units.smul_def, coeff_smul]
    by_cases hσ : ∀ l, (σ l).1 = l.1 ∧ (((σ l).2 : ℕ) < j ↔ (l.2 : ℕ) < j)
    · rw [prod_bigMat_of j σ hσ, coeff_monomial, if_neg, smul_zero]
      intro hm
      apply hne
      refine Equiv.ext fun l => Prod.ext ?_ (Fin.ext ?_)
      · rw [(hσ l).1, rho_apply]
      · have h1 := congrArg (fun m : Ψ × Fin N →₀ ℕ => m (σ l)) hm
        have h2 := (hσ l).2
        rw [sum_single_apply] at h1
        simp only [delta0, Finsupp.coe_equivFunOnFinite_symm, colExp] at h1
        simp only [rho_apply, rev]
        have h3 := (σ l).2.2
        have h4 := l.2.2
        split_ifs at h1 ⊢ <;> omega
    · obtain ⟨l, hl⟩ := not_forall.mp hσ
      rw [Finset.prod_eq_zero (Finset.mem_univ l) (by simp only [bigMat, of_apply, if_neg hl]), coeff_zero,
        smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem proof : FdegNeZero.Statement := by
  intro Ψ _ _ N j hj
  rw [fdeg, antisym_fibV j hj, coeff_smul, ← det_bigMat j hj, coeff_det_bigMat j hj, smul_eq_mul]
  refine mul_ne_zero ?_ ?_
  · exact Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, by simp [G0]⟩)
  · exact Int.cast_ne_zero.mpr (Units.ne_zero _)

end FdegNeZero

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PWedgeTransition
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open GroundTheory.Heights₂.Heights.LowerBoundFree Submodule Module

namespace WedgeTransition

theorem alternating_sum_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (f : M [⋀^Fin n]→ₗ[R] R) (v : Fin n → M) (A : Matrix (Fin n) (Fin n) R) :
    f (fun q => ∑ a, A a q • v a) = A.det * f v := by
  let T : (Fin n → R) →ₗ[R] M := (Pi.basisFun R (Fin n)).constr R v
  have h := congrArg (fun g => g (fun q a => A a q))
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun R (Fin n)) (f.compLinearMap T))
  have hT : ∀ x, T x = ∑ a, x a • v a := fun x => by
    simp [T, Basis.constr_apply_fintype]
  have hTe : (fun i => T (Pi.basisFun R (Fin n) i)) = v := funext fun i => by simp [T]
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, Pi.basisFun_det_apply,
    smul_eq_mul] at h
  have e1 : (fun i => T fun a => A a i) = fun q => ∑ a, A a q • v a := funext fun q => hT _
  rw [e1, hTe] at h
  rw [h, mul_comm]
  congr 1
  exact Matrix.det_transpose A

theorem castLE_ne_tailIdx {j N : ℕ} (hj : j ≤ N) (a : Fin j) (a' : Fin (N - j)) :
    Fin.castLE hj a ≠ tailIdx hj a' := by
  intro h
  have := congrArg Fin.val h
  simp [tailIdx] at this
  omega

def splitEquiv {j N : ℕ} (hj : j ≤ N) : Fin j ⊕ Fin (N - j) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hj))

theorem splitEquiv_inl {j N : ℕ} (hj : j ≤ N) (a : Fin j) : splitEquiv hj (Sum.inl a) = Fin.castLE hj a :=
  Fin.ext (by simp [splitEquiv])

theorem splitEquiv_inr {j N : ℕ} (hj : j ≤ N) (a : Fin (N - j)) : splitEquiv hj (Sum.inr a) = tailIdx hj a :=
  Fin.ext (by simp [splitEquiv, tailIdx])

theorem sum_split {M : Type*} [AddCommMonoid M] {j N : ℕ} (hj : j ≤ N) (g : Fin N → M) :
    ∑ p, g p = ∑ a, g (Fin.castLE hj a) + ∑ a, g (tailIdx hj a) := by
  rw [← (splitEquiv hj).sum_comp, Fintype.sum_sum_type]
  simp [splitEquiv_inl, splitEquiv_inr]

theorem det_split_of_zero {R : Type*} [CommRing R] {j N : ℕ} (hj : j ≤ N) (G : Matrix (Fin N) (Fin N) R)
    (h0 : ∀ a a', G (tailIdx hj a) (Fin.castLE hj a') = 0) :
    G.det = (G.submatrix (Fin.castLE hj) (Fin.castLE hj)).det *
      (G.submatrix (tailIdx hj) (tailIdx hj)).det := by
  rw [← Matrix.det_submatrix_equiv_self (splitEquiv hj) G,
    ← Matrix.fromBlocks_toBlocks (G.submatrix (splitEquiv hj) (splitEquiv hj))]
  have h21 : (G.submatrix (splitEquiv hj) (splitEquiv hj)).toBlocks₂₁ = 0 := by
    ext a a'
    simp [Matrix.toBlocks₂₁, splitEquiv_inl, splitEquiv_inr, h0]
  rw [h21, Matrix.det_fromBlocks_zero₂₁]
  congr 2

variable {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] (F : Submodule Ω V) {N j : ℕ} (hj : j ≤ N)

theorem exists_form_quotWedge_eq_one {b' : Fin N → V} (hli : LinearIndependent Ω b')
    (hsp : span Ω (Set.range b') = ⊤) (hF : span Ω (Set.range (b' ∘ Fin.castLE hj)) = F) :
    ∃ ℓ : ⋀[Ω]^(N - j) (V ⧸ F) →ₗ[Ω] Ω, ℓ (quotWedge F hj b') = 1 := by
  let B := Basis.mk hli hsp.ge
  have : Module.Finite Ω V := Module.Finite.of_basis B
  have hV : Module.finrank Ω V = N := by simpa using Module.finrank_eq_card_basis B
  have hFr : Module.finrank Ω F = j := by
    rw [← hF, finrank_span_eq_card (hli.comp _ (Fin.castLE_injective hj))]
    simp
  have hQ := Submodule.finrank_quotient_add_finrank F
  let w : Fin (N - j) → V ⧸ F := fun a => F.mkQ (b' (tailIdx hj a))
  have hspan : ⊤ ≤ span Ω (Set.range w) := by
    intro x _
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective F x
    have h1 : F.mkQ v ∈ span Ω (F.mkQ '' Set.range b') := by
      rw [← Submodule.map_span, hsp]
      exact ⟨v, trivial, rfl⟩
    refine (Submodule.span_le.mpr ?_) h1
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i.val < j
    · have hmem : b' i ∈ F := hF ▸ subset_span ⟨⟨i, hi⟩, rfl⟩
      have : F.mkQ (b' i) = 0 := by simpa using hmem
      rw [SetLike.mem_coe, this]
      exact zero_mem _
    · have : i = tailIdx hj ⟨i - j, by omega⟩ := Fin.ext (by simp [tailIdx]; omega)
      rw [this]
      exact subset_span ⟨_, rfl⟩
  have hli' : LinearIndependent Ω w :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp; omega)
  let Q := Basis.mk hli' hspan
  refine ⟨exteriorPower.alternatingMapLinearEquiv Q.det, ?_⟩
  rw [quotWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  have : (fun a => F.mkQ (b' (tailIdx hj a))) = ⇑Q := funext fun a => (Basis.mk_apply hli' hspan a).symm
  rw [this, Basis.det_self]

theorem one_factor {b b' : Fin N → V}
    (hb : LinearIndependent Ω b ∧ span Ω (Set.range b) = ⊤ ∧ span Ω (Set.range (b ∘ Fin.castLE hj)) = F)
    (hb' : LinearIndependent Ω b' ∧ span Ω (Set.range b') = ⊤ ∧ span Ω (Set.range (b' ∘ Fin.castLE hj)) = F)
    (φ : V [⋀^Fin N]→ₗ[Ω] Ω) (ψ : V [⋀^Fin j]→ₗ[Ω] Ω) (ℓ : ⋀[Ω]^(N - j) (V ⧸ F) →ₗ[Ω] Ω)
    (hℓ : ℓ (quotWedge F hj b') = 1) :
    φ b * ψ (b' ∘ Fin.castLE hj) = φ b' * ψ (b ∘ Fin.castLE hj) * ℓ (quotWedge F hj b) := by
  let B := Basis.mk hb'.1 hb'.2.1.ge
  have hB : ∀ i, B i = b' i := fun i => Basis.mk_apply _ _ i
  let S := B.toMatrix b
  have hexp : ∀ q, b q = ∑ p, S p q • b' p := by
    intro q
    simp only [S, Basis.toMatrix_apply, ← hB]
    exact (B.sum_repr (b q)).symm
  have hzero : ∀ a a', S (tailIdx hj a) (Fin.castLE hj a') = 0 := by
    intro a a'
    have hm : b (Fin.castLE hj a') ∈ span Ω (Set.range (b' ∘ Fin.castLE hj)) :=
      hb'.2.2 ▸ hb.2.2 ▸ subset_span ⟨a', rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).mp hm
    simp only [S, Basis.toMatrix_apply, ← hc, Function.comp_apply, ← hB, map_sum, map_smul,
      Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      Finsupp.single_apply, castLE_ne_tailIdx, if_false, smul_zero, Finset.sum_const_zero]
  have hF' : ∀ a, b' (Fin.castLE hj a) ∈ F := fun a => hb'.2.2 ▸ subset_span ⟨a, rfl⟩
  have hφ : φ b = S.det * φ b' := by
    rw [← alternating_sum_smul φ b' S]
    exact congrArg φ (funext hexp)
  have hψ : ψ (b ∘ Fin.castLE hj) = (S.submatrix (Fin.castLE hj) (Fin.castLE hj)).det * ψ (b' ∘ Fin.castLE hj) := by
    rw [← alternating_sum_smul ψ (b' ∘ Fin.castLE hj)]
    refine congrArg ψ (funext fun q => ?_)
    rw [Function.comp_apply, hexp, sum_split hj]
    simp [hzero]
  have hq : ∀ ℓ' : ⋀[Ω]^(N - j) (V ⧸ F) →ₗ[Ω] Ω,
      ℓ' (quotWedge F hj b) = (S.submatrix (tailIdx hj) (tailIdx hj)).det * ℓ' (quotWedge F hj b') := by
    intro ℓ'
    have := alternating_sum_smul (ℓ'.compAlternatingMap (exteriorPower.ιMulti Ω (N - j)))
      (fun a => F.mkQ (b' (tailIdx hj a))) (S.submatrix (tailIdx hj) (tailIdx hj))
    simp only [LinearMap.compAlternatingMap_apply, Matrix.submatrix_apply] at this
    rw [quotWedge, quotWedge, ← this]
    congr 2
    funext q
    rw [hexp, map_sum, sum_split hj]
    have h0 : ∀ a, F.mkQ (S (Fin.castLE hj a) (tailIdx hj q) • b' (Fin.castLE hj a)) = 0 := fun a => by
      simpa using Or.inr (hF' a)
    simp only [h0, Finset.sum_const_zero, zero_add, map_smul]
  have hdet := det_split_of_zero hj S hzero
  rw [hφ, hψ, hq ℓ, hℓ, hdet]
  ring

end WedgeTransition

theorem WedgeTransition.proof : WedgeTransition.Statement := by
  rintro Ψ _ Ω _ E _ _ F N j r s hj hr hs rfl rfl b b' hb hb' φ ψ κ κ' h
  classical
  choose ℓ hℓ using fun τ => WedgeTransition.exists_form_quotWedge_eq_one (F τ) hj (hb' τ).1 (hb' τ).2.1
    (hb' τ).2.2
  have key := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra Ω Ψ Ω).compLinearMap ℓ)) h
  simp only [map_smul, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, hℓ, Finset.prod_const_one, smul_eq_mul, mul_one] at key
  have hτ : ∀ τ, φ τ (b τ ∘ Fin.castLE hs) * ψ τ (b' τ ∘ Fin.castLE hr) =
      φ τ (b' τ ∘ Fin.castLE hs) * ψ τ (b τ ∘ Fin.castLE hr) * ℓ τ (quotWedge (F τ) hj (b τ)) :=
    fun τ => WedgeTransition.one_factor (F τ) hj (hb τ) (hb' τ) (φ τ) (ψ τ) (ℓ τ) (hℓ τ)
  rw [Finset.prod_congr rfl fun τ _ => hτ τ, Finset.prod_mul_distrib, ← key]
  ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ProjLineChart
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace LineChart

def lineLift (w : ((k : Unit) → PBlk 2 k) → ℂ) : (Σ k : Unit, PBlk 2 k) → ℂ := fun p => w fun _ => p.2

theorem segre_line (z : (Σ k : Unit, PBlk 2 k) → ℂ) (i : (k : Unit) → PBlk 2 k) :
    segre z i = z ⟨(), i ()⟩ := by
  simp [segre]

theorem segre_lineLift (w : ((k : Unit) → PBlk 2 k) → ℂ) : segre (lineLift w) = w := by
  funext i
  rw [segre_line]
  rfl

theorem lineLift_segre (z : (Σ k : Unit, PBlk 2 k) → ℂ) : lineLift (segre z) = z := by
  funext p
  obtain ⟨⟨⟩, i⟩ := p
  simp only [lineLift, segre_line]

theorem mem_mcPts_bot (z : (Σ k : Unit, PBlk 2 k) → ℂ) :
    z ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) ↔ ∃ i, z ⟨(), i⟩ ≠ 0 := by
  constructor
  · rintro ⟨h, -⟩
    exact h ()
  · intro h
    refine ⟨fun k => ?_, fun f hf => ?_⟩
    · cases k
      exact h
    · rw [Ideal.mem_bot] at hf
      subst hf
      simp

theorem lineLift_mem {w : ((k : Unit) → PBlk 2 k) → ℂ} (hw : w ≠ 0) :
    lineLift w ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine (mem_mcPts_bot _).2 ⟨i (), ?_⟩
  simpa [lineLift] using hi

theorem injective_of_good {Ψ : (((k : Unit) → PBlk 2 k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ)}
    (hΨ : IsGoodProj (⊥ : Ideal (MRing (PBlk 2))) Ψ) : Function.Injective Ψ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  by_contra hne
  exact hΨ _ (lineLift_mem hne) (by rw [segre_lineLift]; exact hw)

theorem exists_good :
    ∃ Ψ : (((k : Unit) → PBlk 2 k) → ℂ) →ₗ[ℂ] (Fin (1 + 1) → ℂ), IsGoodProj (⊥ : Ideal (MRing (PBlk 2))) Ψ := by
  let Ψ0 := LinearEquiv.funCongrLeft ℂ ℂ (Equiv.funUnique Unit (Fin 2)).symm
  refine ⟨Ψ0.toLinearMap, fun z hz h0 => ?_⟩
  obtain ⟨i, hi⟩ := (mem_mcPts_bot z).1 hz
  have hs : segre z = 0 := Ψ0.map_eq_zero_iff.mp h0
  exact hi (by rw [← segre_line z (fun _ => i), hs]; rfl)

theorem geomDeg_eq_integral (A : HermLine (PBlk 2)) :
    ∃ L : (Fin (1 + 1) → ℂ) ≃ₗ[ℂ] (((k : Unit) → PBlk 2 k) → ℂ),
      geomDeg (⊥ : Ideal (MRing (PBlk 2))) A 1 =
        ∫ y : Fin 1 → ℂ, maDensity (fun _ y' => Real.log (A.h (lineLift (L (Fin.cons 1 y'))))) y := by
  have hex := exists_good
  set Ψ := hex.choose with hΨdef
  have hΨ : IsGoodProj (⊥ : Ideal (MRing (PBlk 2))) Ψ := hex.choose_spec
  have hinj := injective_of_good hΨ
  have hrank : Module.finrank ℂ (((k : Unit) → PBlk 2 k) → ℂ) = Module.finrank ℂ (Fin (1 + 1) → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  set E := LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩ with hE
  set L := E.symm with hL
  have hΨL : ∀ v, Ψ (L v) = v := E.apply_symm_apply
  have hLΨ : ∀ w, L (Ψ w) = w := E.symm_apply_apply
  refine ⟨L, ?_⟩
  have hLdiff : Differentiable ℂ fun v => L v := (LinearMap.toContinuousLinearMap L.toLinearMap).differentiable
  have hcons : Differentiable ℂ fun y' : Fin 1 → ℂ => (Fin.cons 1 y' : Fin (1 + 1) → ℂ) := by
    rw [differentiable_pi]
    intro c
    refine Fin.cases ?_ (fun i => ?_) c
    · simp only [Fin.cons_zero]
      exact differentiable_const _
    · simp only [Fin.cons_succ]
      exact differentiable_apply i
  set γ0 : (Fin 1 → ℂ) → (Σ k : Unit, PBlk 2 k) → ℂ := fun y' => lineLift (L (Fin.cons 1 y')) with hγ0
  have hγ0d : ∀ y', DifferentiableAt ℂ γ0 y' := by
    intro y'
    rw [differentiableAt_pi]
    intro p
    exact ((differentiable_apply (fun _ => p.2)).comp (hLdiff.comp hcons)) y'
  have hγ0mem : ∀ y', γ0 y' ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))) := by
    intro y'
    have hv : (Fin.cons 1 y' : Fin (1 + 1) → ℂ) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
    exact lineLift_mem ((L.map_ne_zero_iff).mpr hv)
  unfold geomDeg ptsIntegral
  rw [dif_pos hex]
  unfold ptsIntegralAt
  congr 1
  funext y
  have hfib : fibre (⊥ : Ideal (MRing (PBlk 2))) Ψ y = {L (Fin.cons 1 y)} := by
    ext w
    simp only [fibre, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, -, -, hw⟩
      rw [← hw, hLΨ]
    · rintro rfl
      exact ⟨γ0 y, hγ0mem y, segre_lineLift _, hΨL _⟩
  have hsheet : IsSheet (⊥ : Ideal (MRing (PBlk 2))) Ψ y (L (Fin.cons 1 y)) γ0 :=
    ⟨segre_lineLift _, Eventually.of_forall fun y' => ⟨hγ0d y', hγ0mem y', by rw [segre_lineLift, hΨL]⟩⟩
  rw [hfib, finsum_mem_singleton]
  unfold sheetDensity
  split_ifs with hγ
  · have hev : (fun y' => Real.log (A.h (hγ.choose y'))) =ᶠ[𝓝 y]
        fun y' => Real.log (A.h (lineLift (L (Fin.cons 1 y')))) := by
      filter_upwards [hγ.choose_spec.2] with y' hy'
      have hs : segre (hγ.choose y') = L (Fin.cons 1 y') := by
        rw [← hLΨ (segre (hγ.choose y')), hy'.2.2]
      rw [← hs, lineLift_segre]
    rw [one_mul]
    exact maDensity_congr_of_eventuallyEq fun _ => hev
  · exact absurd ⟨γ0, hsheet⟩ hγ

end LineChart

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

