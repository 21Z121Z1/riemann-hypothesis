import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.Bundle0019

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlgWittAlt
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.IntWittAlg

open Matrix Formalism.UG

theorem algWitt : Formalism.L2.SG.Pf.NcX.IntWittPf.AlgWitt := by
  intro S _ s O hs hsO n J J' hJ hJJ hJO hJ'O a β β' hβ hβ' hββ hch x y hx hy hxx hyy
  have hconj := hform_conj s J hs hJ

  have mkGL : ∀ M : Matrix (Fin n) (Fin n) S, cT s M * J * M = J → (∀ i j, M i j ∈ O) →
      ∃ g : GL (Fin n) S, (g : Matrix (Fin n) (Fin n) S) = M ∧ g ∈ UJ s J ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O := by
    intro M hM hMO
    have hL : (J' * cT s M * J) * M = 1 := by
      calc (J' * cT s M * J) * M = J' * (cT s M * J * M) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hM, hJJ]
    have hR : M * (J' * cT s M * J) = 1 := mul_eq_one_comm.mp hL
    refine ⟨⟨M, J' * cT s M * J, hR, hL⟩, rfl, hM, ?_⟩
    intro i j
    show (J' * cT s M * J) i j ∈ O
    exact mul_mem' O _ _ (mul_mem' O _ _ hJ'O (cT_mem O s hsO M hMO)) hJO i j
  have hsβ : ∀ i, s (β i) = β i := by
    intro i
    have := hconj (y i) (y i)
    rw [hyy i i, if_pos rfl] at this
    exact this
  have hsβ' : ∀ i, s (β' i) = β' i := by
    intro i
    calc s (β' i) = s (β' i) * (β i * β' i) := by rw [hββ, mul_one]
      _ = s (β i * β' i) * β' i := by rw [map_mul, hsβ]; ring
      _ = β' i := by rw [hββ, map_one, one_mul]
  have main : ∀ m ≤ a, ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (∀ i j, (g : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      ∀ i : Fin a, i.val < m → (g : Matrix (Fin n) (Fin n) S) *ᵥ y i = x i := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨1, (UJ s J).one_mem, ?_, ?_, fun i h => absurd h (Nat.not_lt_zero _)⟩
      · intro i j; rw [Units.val_one]; exact one_mem' O i j
      · intro i j; rw [inv_one, Units.val_one]; exact one_mem' O i j
    | succ m ih =>
      intro hm
      obtain ⟨g, hg, hgO, hgiO, hgy⟩ := ih (by omega)
      let i0 : Fin a := ⟨m, by omega⟩
      set G := (g : Matrix (Fin n) (Fin n) S) with hG
      set Gi := ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) with hGi
      have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hgi : g⁻¹ ∈ UJ s J := (UJ s J).inv_mem hg
      have hGiU : ∀ z w, hform s J (Gi *ᵥ z) (Gi *ᵥ w) = hform s J z w := by
        intro z w
        rw [PI.VolStabW.TopoGram.hform_mulVec]
        exact congrArg (fun K => hform s K z w) hgi
      have hyGi : ∀ i : Fin a, i.val < m → Gi *ᵥ x i = y i := by
        intro i hi
        rw [← hgy i hi, mulVec_mulVec, hGiG, one_mulVec]
      set xp := Gi *ᵥ x i0 with hxpdef
      have hxpO : ∀ k, xp k ∈ O := mulVec_mem O _ hgiO _ (hx i0)
      have hxpy : ∀ i : Fin a, i.val < m → hform s J xp (y i) = 0 := by
        intro i hi
        rw [hxpdef, ← hyGi i hi, hGiU, hxx, if_neg]
        intro h; rw [← h] at hi; exact lt_irrefl _ hi
      have hxpxp : hform s J xp xp = hform s J (y i0) (y i0) := by
        rw [hxpdef, hGiU, hxx, hyy, if_pos rfl]
      have htO : hform s J xp (y i0) ∈ O := hform_mem O s hsO J hJO _ _ hxpO (hy i0)
      obtain ⟨lam, hlamO, hlam, ci, hciO, hci⟩ := hch i0 _ htO
      have hβ0 : β i0 = hform s J (y i0) (y i0) := by rw [hyy, if_pos rfl]
      set c := hform s J (y i0) (y i0) - s lam * hform s J xp (y i0) with hcdef
      have e2 : ci * c = 1 := by rw [mul_comm, hcdef, ← hβ0]; exact hci
      set u := y i0 - lam • xp with hudef
      have huO : ∀ k, u k ∈ O := by
        intro k
        simp only [hudef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        exact O.sub_mem (hy i0 k) (O.mul_mem hlamO (hxpO k))
      have hux : hform s J u (y i0) = c := by
        rw [hudef, hform_sub_left, hform_smul_left]
      have huu : hform s J u u = c + s c := by
        rw [hudef, hcdef]
        simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_sub, map_mul, hs,
          hconj]
        linear_combination (s lam * lam) * hxpxp + hform s J (y i0) (y i0) * hlam
      have huy : ∀ i : Fin a, i.val < m → hform s J u (y i) = 0 := by
        intro i hi
        rw [hudef, hform_sub_left, hform_smul_left, hxpy i hi, hyy, if_neg, mul_zero, sub_zero]
        intro h; rw [← h] at hi; exact lt_irrefl _ hi

      set T := rT s J u ci lam with hTdef
      have hTy0 : T *ᵥ y i0 = xp := by
        rw [hTdef, rT_mulVec, hux, e2, one_smul, hudef, sub_sub_cancel, smul_smul, mul_comm, hlam, one_smul]
      have hTy : ∀ i : Fin a, i.val < m → T *ᵥ y i = s lam • y i := by
        intro i hi
        rw [hTdef, rT_mulVec, huy i hi, mul_zero, zero_smul, sub_zero]
      have hTU := rT_preserves s J hs hJ u c ci lam hlam huu e2

      let t : Finset (Fin a) := Finset.univ.filter (fun i => i.val < m)
      have hmt : ∀ i, i ∈ t ↔ i.val < m := fun i => by simp [t]
      set Pm := pM s J t y β' with hPm
      set Dm := (1 : Matrix (Fin n) (Fin n) S) + (lam - 1) • Pm with hDm
      have hPy : ∀ i : Fin a, i.val < m → Pm *ᵥ y i = y i := by
        intro i hi
        rw [hPm, pM_mulVec, Finset.sum_eq_single i]
        · rw [hyy, if_pos rfl, mul_comm, hββ, one_smul]
        · intro j _ hji
          rw [hyy, if_neg hji, mul_zero, zero_smul]
        · intro h; exact absurd ((hmt i).2 hi) h
      have hPy0 : Pm *ᵥ y i0 = 0 := by
        rw [hPm, pM_mulVec]
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [hyy, if_neg, mul_zero, zero_smul]
        intro h; have := (hmt j).1 hj; rw [h] at this; exact lt_irrefl _ this
      have hDy : ∀ i : Fin a, i.val < m → Dm *ᵥ y i = lam • y i := by
        intro i hi
        rw [hDm, add_mulVec, one_mulVec, smul_mulVec, hPy i hi, sub_smul, one_smul]
        abel
      have hDy0 : Dm *ᵥ y i0 = y i0 := by
        rw [hDm, add_mulVec, one_mulVec, smul_mulVec, hPy0, smul_zero, add_zero]
      have hDU : ∀ z w, hform s J (Dm *ᵥ z) (Dm *ᵥ w) = hform s J z w := by
        intro z w
        set p := ∑ j ∈ t, β' j * hform s J (y j) w * hform s J z (y j) with hp
        have h1 : hform s J z (Pm *ᵥ w) = p := by
          rw [hPm, pM_mulVec, hform_sum_right]
        have h2 : hform s J (Pm *ᵥ z) w = p := by
          rw [hPm, pM_mulVec, hform_sum_left, hp]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul, hsβ', hconj]
          ring
        have h3 : hform s J (Pm *ᵥ z) (Pm *ᵥ w) = p := by
          rw [hPm, pM_mulVec, hform_sum_left, hp]
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [← hPm, pM_mulVec, hform_sum_right, Finset.sum_eq_single j]
          · rw [hyy, if_pos rfl, map_mul, hsβ', hconj]
            linear_combination (β' j * hform s J (y j) w * hform s J z (y j)) * hββ j
          · intro l _ hlj
            rw [hyy, if_neg (Ne.symm hlj), mul_zero]
          · intro h; exact absurd hj h
        rw [hDm, add_mulVec, add_mulVec, one_mulVec, one_mulVec, smul_mulVec, smul_mulVec, hform_add_left,
          hform_add_right, hform_add_right, hform_smul_left, hform_smul_left, hform_smul_right, hform_smul_right,
          h1, h2, h3, map_sub, map_one]
        linear_combination p * hlam

      set M := T * Dm with hM
      have hMU : cT s M * J * M = J := by
        refine unitary_of s J M fun z w => ?_
        rw [hM, ← mulVec_mulVec, ← mulVec_mulVec, hTU, hDU]
      have hMO : ∀ i j, M i j ∈ O := by
        intro i j
        refine mul_mem' O _ _ (rT_mem O s hsO J hJO u huO ci lam hciO hlamO) ?_ i j
        intro i j
        simp only [hDm, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        exact O.add_mem (one_mem' O i j) (O.mul_mem (O.sub_mem hlamO O.one_mem)
          (pM_mem O s hsO J hJO t y hy β' hβ' i j))
      obtain ⟨g', hg'M, hg'U, hg'iO⟩ := mkGL M hMU hMO
      refine ⟨g * g', (UJ s J).mul_mem hg hg'U, ?_, ?_, ?_⟩
      · intro i j
        rw [Units.val_mul, hg'M]
        exact mul_mem' O _ _ hgO hMO i j
      · intro i j
        rw [_root_.mul_inv_rev, Units.val_mul]
        exact mul_mem' O _ _ hg'iO hgiO i j
      · intro i hi
        rw [Units.val_mul, hg'M, ← mulVec_mulVec, hM, ← mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · rw [hDy i hi, mulVec_smul, hTy i hi, smul_smul, hlam, one_smul]
          exact hgy i hi
        · have : i = i0 := Fin.ext hi
          rw [this, hDy0, hTy0, hxpdef, mulVec_mulVec, ← hG, hGGi, one_mulVec]
  obtain ⟨g, hg, hgO, hgiO, hgy⟩ := main a le_rfl
  exact ⟨g, hg, hgO, hgiO, fun i => hgy i i.2⟩

end Formalism.L2.SG.Pf.NcX.IntWittAlg
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LamAEAlt
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter
  Formalism.L2.SG.Pf.NcX.KfOrbPf
open scoped TensorProduct

theorem lamAE : LamAE := by
  intro F E _ _ _ _ _ σ hCM δ hδ hδ0
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hσ : ∀ z, σ (σ z) = z := PI.VolStabW.sigma_invol σ hCM.2.2.2
  obtain ⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by
    by_contra H
    push Not at H
    let w : InfinitePlace E := Classical.arbitrary _
    have hreal : ComplexEmbedding.IsReal w.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext z
      rw [ComplexEmbedding.conjugate_coe_eq, ← Complex.star_def, ← hCM.2.2.2, H z]
    exact (InfinitePlace.not_isReal_iff_isComplex.2 (hCM.2.1.isComplex w)) (InfinitePlace.isReal_iff.2 hreal)
  set θ : E := x - σ x with hθdef
  have hσθ : σ θ = -θ := by rw [hθdef, map_sub, hσ]; ring
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
  have hind : ∀ p q : F, algebraMap F E p + algebraMap F E q * θ = 0 → p = 0 ∧ q = 0 := by
    intro p q h
    have h' := congrArg σ h
    rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ, map_zero] at h'
    have hq : (2 : E) * (algebraMap F E q * θ) = 0 := by linear_combination h - h'
    have hq0 : q = 0 := by
      rcases mul_eq_zero.1 ((mul_eq_zero.1 hq).resolve_left two_ne_zero) with h1 | h1
      · exact (algebraMap F E).injective (by rw [h1, map_zero])
      · exact absurd h1 hθ0
    subst hq0
    rw [map_zero, zero_mul, add_zero] at h
    exact ⟨(algebraMap F E).injective (by rw [h, map_zero]), rfl⟩
  let v2 : Fin 2 → E := ![1, θ]
  have hli : LinearIndependent F v2 := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    have e : algebraMap F E (g 0) + algebraMap F E (g 1) * θ = 0 := by
      rw [← hg]; simp [v2, Algebra.smul_def]
    obtain ⟨h0, h1⟩ := hind _ _ e
    intro i
    fin_cases i
    · exact h0
    · exact h1
  let b2 : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hCM.2.2.1])
  have hb2 : ∀ i, b2 i = v2 i := fun i => by
    simp only [b2, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hdec : ∀ e : E, e = algebraMap F E (b2.repr e 0) + algebraMap F E (b2.repr e 1) * θ := by
    intro e
    conv_lhs => rw [← b2.sum_repr e]
    rw [Fin.sum_univ_two, hb2, hb2]
    simp [v2, Algebra.smul_def]

  have hfixF : ∀ e : E, σ e = e → e = algebraMap F E (b2.repr e 0) := by
    intro e he
    have h1 := hdec e
    have h2 := congrArg σ h1
    rw [he, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσθ] at h2
    have h3 : algebraMap F E 0 + algebraMap F E (2 * b2.repr e 1) * θ = 0 := by
      rw [map_zero, map_mul, map_ofNat]; linear_combination h2 - h1
    have hq := (hind _ _ h3).2
    have hq' : b2.repr e 1 = 0 := (mul_eq_zero.1 hq).resolve_left two_ne_zero
    rw [hq', map_zero (algebraMap F E), zero_mul, add_zero] at h1
    exact h1
  have hθ2σ : σ (θ ^ 2) = θ ^ 2 := by rw [map_pow, hσθ, neg_sq]
  set d := b2.repr (θ ^ 2) 0 with hd_def
  have hd : θ ^ 2 = algebraMap F E d := hfixF _ hθ2σ
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at hd
    exact hθ0 ((pow_eq_zero_iff two_ne_zero).1 hd)
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, map_one] at hd
    have h1 : (θ - 1) * (θ + 1) = 0 := by linear_combination hd
    rcases mul_eq_zero.1 h1 with h | h
    · have e : θ = 1 := sub_eq_zero.1 h
      rw [e, map_one] at hσθ
      exact two_ne_zero (by linear_combination hσθ : (2 : E) = 0)
    · have e : θ = -1 := eq_neg_of_add_eq_zero_left h
      rw [e, map_neg, map_one] at hσθ
      exact two_ne_zero (by linear_combination -hσθ : (2 : E) = 0)
  set β0 := b2.repr δ 0 with hβ0_def
  have hδF : δ = algebraMap F E β0 := hfixF δ hδ
  have hβ0 : β0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hδF
    exact hδ0 hδF
  have h1d : (1 - d) ≠ 0 := sub_ne_zero.2 (Ne.symm hd1)
  set Pc : F := (1 + d) / (1 - d) with hPc
  set Qc : F := 2 / (1 - d) with hQc_def
  have hQc : Qc ≠ 0 := div_ne_zero two_ne_zero h1d
  have hpq : Pc ^ 2 - d * Qc ^ 2 = 1 := by
    rw [hPc, hQc_def]
    field_simp
    ring
  filter_upwards [ev_int (F := F) d, ev_int (F := F) β0, ev_int (F := F) β0⁻¹, ev_int (F := F) Pc,
    ev_int (F := F) Qc, ev_int (F := F) (Qc * d)⁻¹, ev_int (F := F) (4 : F)⁻¹, ev_oev (F := F) θ, ev_crd_oev b2]
    with v hdv hβv hβiv hPv hQv hKv h4v hθv hcrd
  intro t ht
  let ι : v.adicCompletionIntegers F →+* Fv F v ⊗[F] E :=
    (algebraMap (Fv F v) (Fv F v ⊗[F] E)).comp (v.adicCompletionIntegers F).subtype
  have hιF : ∀ (y : F) (hy : algebraMap F (Fv F v) y ∈ v.adicCompletionIntegers F),
      ι ⟨_, hy⟩ = algebraMap F (Fv F v ⊗[F] E) y := by
    intro y hy
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) y) = _
    rw [← IsScalarTower.algebraMap_apply]
  have hιO : ∀ r, ι r ∈ oevRing (E := E) v := by
    intro r
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v) ∈ OEv (E := E) v
    rw [Algebra.algebraMap_eq_smul_one]
    exact oev_smul' v r.2 (oev_one v)
  have hsι : ∀ r, sigR (Fv F v) σ (ι r) = ι r := by
    intro r
    show sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) (r : Fv F v)) = _
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hincl : ∀ y : F, inclR (F := F) (Fv F v) (algebraMap F E y) = algebraMap F (Fv F v ⊗[F] E) y :=
    fun y => (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).commutes y
  have hΘ : (inclR (F := F) (Fv F v) θ) ^ 2 = ι ⟨_, hdv⟩ := by
    rw [hιF, ← map_pow, hd, hincl]
  have hsΘ : sigR (Fv F v) σ (inclR (F := F) (Fv F v) θ) = -inclR (F := F) (Fv F v) θ := by
    simp [sigR, inclR, hσθ, TensorProduct.tmul_neg]
  have hcrd' := hcrd t ht
  have htd : t = ι ⟨_, hcrd' 0⟩ + ι ⟨_, hcrd' 1⟩ * inclR (F := F) (Fv F v) θ := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b2).sum_repr t]
    rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb2, hb2]
    show _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabW.PositiveNearLattice.crd b2 (Fv F v) t 0) +
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (PI.VolStabW.PositiveNearLattice.crd b2 (Fv F v) t 1) * inclR (F := F) (Fv F v) θ
    simp only [PI.VolStabW.PositiveNearLattice.crd, Algebra.smul_def, v2, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [inclR]
  have hPQ : (⟨_, hPv⟩ : v.adicCompletionIntegers F) ^ 2 - ⟨_, hdv⟩ * ⟨_, hQv⟩ ^ 2 = 1 := by
    apply Subtype.ext
    show (algebraMap F (Fv F v) Pc) ^ 2 - algebraMap F (Fv F v) d * (algebraMap F (Fv F v) Qc) ^ 2 = 1
    rw [← map_pow, ← map_pow, ← map_mul, ← map_sub, hpq, map_one]
  have hB : (⟨_, hβv⟩ : v.adicCompletionIntegers F) * ⟨_, hβiv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) β0 * algebraMap F (Fv F v) β0⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hβ0, map_one]
  have hK : (⟨_, hQv⟩ : v.adicCompletionIntegers F) * ⟨_, hdv⟩ * ⟨_, hKv⟩ = 1 := by
    apply Subtype.ext
    show algebraMap F (Fv F v) Qc * algebraMap F (Fv F v) d * algebraMap F (Fv F v) (Qc * d)⁻¹ = 1
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ (mul_ne_zero hQc hd0), map_one]
  have h4 : (4 : v.adicCompletionIntegers F) * ⟨_, h4v⟩ = 1 := by
    apply Subtype.ext
    show ((4 : v.adicCompletionIntegers F) : Fv F v) * algebraMap F (Fv F v) (4 : F)⁻¹ = 1
    have e4 : ((4 : v.adicCompletionIntegers F) : Fv F v) = algebraMap F (Fv F v) 4 := by
      rw [map_ofNat]; rfl
    rw [e4, ← map_mul, mul_inv_cancel₀ (by norm_num), map_one]
  obtain ⟨lam, hlamO, hlam, c', hc'O, hc'⟩ := core_loc ι (sigR (Fv F v) σ) (oevRing (E := E) v) hιO
    (inclR (F := F) (Fv F v) θ) hθv ⟨_, hdv⟩ ⟨_, hβv⟩ ⟨_, hPv⟩ ⟨_, hQv⟩ ⟨_, hcrd' 0⟩ ⟨_, hcrd' 1⟩
    hΘ hsΘ hsι hPQ ⟨_, hβiv⟩ ⟨_, hKv⟩ ⟨_, h4v⟩ hB hK h4
  refine ⟨lam, hlamO, hlam, c', hc'O, ?_⟩
  have hδι : inclR (F := F) (Fv F v) δ = ι ⟨_, hβv⟩ := by rw [hιF, hδF, hincl]
  rw [hδι]
  conv_lhs => rw [htd]
  exact hc'

end Formalism.L2.SG.Pf.NcX.IntWittPf
end
end

