import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnipotent
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

noncomputable section
namespace GlobalTheory.RootEx.UnfoldFlag

variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def flagMat (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  Matrix.of fun r s =>
    Sum.elim (fun s => (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inl s)) (fun i => y i r) s

theorem flagMat_mulVec (y : Fin c → (n ⊕ Fin c → k)) (v : n ⊕ Fin c → k) :
    flagMat y *ᵥ v = inX k n c (fun r => v (Sum.inl r)) + ∑ i, v (Sum.inr i) • y i := by
  funext r
  rw [inX_apply]
  simp only [mulVec, dotProduct, flagMat, of_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · rcases r with r | l
    · simp [one_apply]
    · simp [one_apply]
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem flagMat_uni {y : Fin c → (n ⊕ Fin c → k)} (hY : ∀ i, y i ∈ Yle k n c (i.val + 1))
    (h1 : ∀ i, y i (Sum.inr i) = 1) (h0 : ∀ i : Fin c, i.val = 0 → ∀ r, y i (Sum.inl r) = 0) :
    Radical.Uni (lev 1) (flagMat y) := by
  intro r s hrs
  rcases s with s | i
  · simp [flagMat]
  · simp only [flagMat, of_apply, Sum.elim_inr]
    rcases r with r | l
    · have hi : i.val = 0 := by
        simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
        omega
      rw [h0 i hi r, one_apply_ne (by simp)]
    · simp only [lev, Sum.elim_inr] at hrs
      rcases Nat.lt_or_eq_of_le hrs with h | h
      · rw [(mem_Yle.mp (hY i)) l h,
          one_apply_ne (fun e => by simp only [Sum.inr.injEq] at e; subst e; omega)]
      · have e : i = l := Fin.ext (by omega)
        subst e
        rw [h1, one_apply_eq]

theorem exists_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (hc : 1 ≤ c) (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), (∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) = Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)}) → (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ → ∃ u ∈ N k n c 1, act u Λ = chainLat ϖ c (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c hc ϖ hϖ Λ hΛ hfirst
  have hpow : ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) ≠ 0 := fun i => pow_ne_zero _ hϖ

  have hpick : ∀ i : Fin c, ∃ w : n ⊕ Fin c → k, w ∈ Λ ∧ w ∈ Yle k n c (i.val + 1) ∧
      w (Sum.inr i) = (ϖ : k) ^ (i.val + 1) ∧ (i.val = 0 → ∀ r, w (Sum.inl r) = 0) := by
    intro i
    by_cases hi : i.val = 0
    · have e : i = ⟨0, hc⟩ := Fin.ext hi
      subst e
      refine ⟨(ϖ : k) • aux k n (⟨0, hc⟩ : Fin c), hfirst, ?_, ?_, fun _ r => ?_⟩
      · rw [mem_Yle]
        intro l hl
        have hl0 : l ≠ ⟨0, hc⟩ := fun e => by subst e; simp at hl
        simp [aux, hl0]
      · simp [aux]
      · simp [aux]
    · have hmem : (ϖ : k) ^ (i.val + 1) ∈
          (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (R := 𝒪[k]) (Sum.inr i)) := by
        rw [hΛ i]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨w, hw, hwi⟩ := Submodule.mem_map.1 hmem
      exact ⟨w, (Submodule.mem_inf.1 hw).1, (Submodule.mem_inf.1 hw).2, hwi, fun h => absurd h hi⟩
  choose w hwΛ hwY hw1 hw0 using hpick

  obtain ⟨y, hy⟩ : ∃ y : Fin c → (n ⊕ Fin c → k), ∀ i, y i = ((ϖ : k) ^ (i.val + 1))⁻¹ • w i :=
    ⟨_, fun _ => rfl⟩
  have hyY : ∀ i, y i ∈ Yle k n c (i.val + 1) := by
    intro i
    rw [mem_Yle]
    intro l hl
    rw [hy, Pi.smul_apply, (mem_Yle.mp (hwY i)) l hl, smul_zero]
  have hy1 : ∀ i, y i (Sum.inr i) = 1 := by
    intro i
    rw [hy, Pi.smul_apply, hw1, smul_eq_mul, inv_mul_cancel₀ (hpow i)]
  have hy0 : ∀ i : Fin c, i.val = 0 → ∀ r, y i (Sum.inl r) = 0 := by
    intro i hi r
    rw [hy, Pi.smul_apply, hw0 i hi r, smul_zero]
  have hyw : ∀ i, (ϖ : k) ^ (i.val + 1) • y i = w i := by
    intro i
    rw [hy, smul_smul, mul_inv_cancel₀ (hpow i), one_smul]
  have hU := flagMat_uni hyY hy1 hy0
  have hdet : IsUnit (flagMat y).det := by
    rw [hU.det]
    exact isUnit_one
  obtain ⟨g, hg⟩ : ∃ g : GL (n ⊕ Fin c) k, g.val = flagMat y := ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩

  have himg : act g (chainLat ϖ c (Λ.comap (inX k n c))) = Λ := by
    apply le_antisymm
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := mem_act.1 hv
      obtain ⟨huL, hua⟩ := mem_chainLat.1 hu
      rw [hg, flagMat_mulVec]
      refine Λ.add_mem (Submodule.mem_comap.1 huL) (Λ.sum_mem fun i _ => ?_)
      obtain ⟨a, ha⟩ := hua i
      rw [ha, mul_smul, hyw i]
      exact Λ.smul_mem a (hwΛ i)
    · have hX : ∀ x ∈ Λ.comap (inX k n c),
          inX k n c x ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro x hx
        refine mem_act.2 ⟨inX k n c x, inX_mem_chainLat.2 hx, ?_⟩
        rw [hg, flagMat_mulVec]
        simp [inX_apply]
      have hW : ∀ i, w i ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro i
        refine mem_act.2 ⟨(ϖ : k) ^ (i.val + 1) • aux k n i, scaled_basis_mem_chainLattice ϖ _ i, ?_⟩
        rw [hg, mulVec_smul, ← hyw i]
        congr 1
        rw [aux, mulVec_single_one]
        rfl

      have key : ∀ j, j ≤ c → ∀ v ∈ Λ, v ∈ Yle k n c j →
          v ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro j
        induction j with
        | zero =>
          intro _ v hv hv0
          have e : v = inX k n c (fun r => v (Sum.inl r)) := by
            funext r
            rcases r with r | l
            · simp [inX_apply]
            · simp [inX_apply, (mem_Yle.mp hv0) l (by omega)]
          rw [e]
          apply hX
          rw [Submodule.mem_comap, ← e]
          exact hv
        | succ j ih =>
          intro hj v hv hvY
          obtain ⟨i, hi⟩ : ∃ i : Fin c, i.val = j := ⟨⟨j, by omega⟩, rfl⟩
          subst hi
          have hmem : v (Sum.inr i) ∈ Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)} := by
            rw [← hΛ i]
            exact Submodule.mem_map_of_mem (Submodule.mem_inf.2 ⟨hv, hvY⟩)
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
          have hrest : v - a • w i ∈ Yle k n c i.val := by
            rw [mem_Yle]
            intro l hl
            rcases eq_or_ne l i with rfl | hne
            · rw [Pi.sub_apply, Pi.smul_apply, hw1, ha, sub_self]
            · have hne' : l.val ≠ i.val := fun h => hne (Fin.ext h)
              have hl' : i.val + 1 < l.val + 1 := by omega
              rw [Pi.sub_apply, Pi.smul_apply, (mem_Yle.mp hvY) l hl', (mem_Yle.mp (hwY i)) l hl',
                smul_zero, sub_zero]
          have h1 := ih (by omega) (v - a • w i) (Λ.sub_mem hv (Λ.smul_mem a (hwΛ i))) hrest
          have h2 := Submodule.add_mem _ h1 (Submodule.smul_mem _ a (hW i))
          rwa [sub_add_cancel] at h2
      intro v hv
      exact key c le_rfl v hv (mem_Yle.2 fun l hl => absurd hl (by have := l.isLt; omega))
  refine ⟨g⁻¹, (Radical.mem_N_iff g⁻¹).2 ?_, ?_⟩
  · exact Radical.Uni.inv (g := g) (by rw [hg]; exact hU)
  · conv_lhs => rw [← himg]
    rw [← act_mul, inv_mul_cancel, act_one]

end GlobalTheory.RootEx.UnfoldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarIsMulRightInvariant
section
noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology Matrix
open scoped ENNReal

namespace GlobalTheory.SmGL.UnipHaar

section Algebra

variable {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)

theorem det_rmat_unip (u : unipRad R e) : (rmat e ((u : GL n R) : Matrix n n R)).det = 1 := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 u.2
  rw [← det_transpose, det_of_blocks (rmat e _)ᵀ (fun p => blk e p.1.2) ?_
    (fun a => {j : n // blk e j < a}) (fun _ => 1) (colEquiv e) ?_]
  · simp
  · intro p q h
    have h3 : ((u : GL n R) : Matrix n n R).BlockTriangular (blk e) := h1
    simp [rmat, h3 h]
  · intro a x y
    exact if_congr (eq_comm.trans Subtype.ext_iff.symm) (h2 a x.1 y.1) rfl

theorem unipEquiv_mul_right (u : unipRad R e) (x : Idx e → R) :
    unipEquiv e ((unipEquiv e).symm x * u) =
      unipEquiv e u + (rmat e ((u : GL n R) : Matrix n n R)).mulVec x := by
  rw [← ent_mat_mul]
  show ent e ((1 + mat e x) * ((u : GL n R) : Matrix n n R)) = _
  rw [add_mul, one_mul]
  rfl

end Algebra

section Measure

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]

theorem isMulRightInvariant_map :
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν)).IsMulRightInvariant := by
  haveI := secondCountable k
  haveI := t2Space k
  have hΦ : Measurable (unipHomeo (R := k) e).symm := (unipHomeo e).symm.measurable
  refine ⟨fun u => ?_⟩
  have hm : Measurable (rmat e ((u : GL n k) : Matrix n n k)).mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have h1 := WeilM.smul_map_mulVec_pi ν _ 1 (det_rmat_unip e u).symm
  rw [map_one, ENNReal.coe_one, one_smul] at h1
  have h2 : (· * u) ∘ (unipHomeo e).symm = (unipHomeo e).symm ∘ ((unipEquiv e u + ·) ∘
      (rmat e ((u : GL n k) : Matrix n n k)).mulVec) :=
    funext fun x => (unipEquiv e).eq_symm_apply.2 (unipEquiv_mul_right e u x)
  rw [Measure.map_map (measurable_mul_const u) hΦ, h2,
    ← Measure.map_map hΦ ((measurable_const_add _).comp hm),
    ← Measure.map_map (measurable_const_add _) hm, h1, map_add_left_eq_self]

end Measure

theorem haar_isMulRightInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] (μ : Measure (unipRad k e)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e _ _ μ _
  borelize k
  haveI := secondCountable k
  haveI := t2Space k
  haveI : LocallyCompactSpace (unipRad k e) := (unipHomeo e).isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (unipRad k e) := (unipHomeo e).secondCountableTopology
  haveI := isHaarMeasure_map e (Measure.addHaar : Measure k)
  haveI := isMulRightInvariant_map e (Measure.addHaar : Measure k)
  rw [Measure.isMulLeftInvariant_eq_smul μ
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => (Measure.addHaar : Measure k)))]
  infer_instance

end GlobalTheory.SmGL.UnipHaar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HilbertTensorTraceClassHasTraceProd
section
open ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory

open GlobalTheory.OpTrace

theorem tensorTrace_summable_sq {ι : Type} [Fintype ι] {Hs : ι → Type} [∀ i, NormedAddCommGroup (Hs i)]
    [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ)
    (hΨ : ∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) (A : ∀ i, Hs i →L[ℂ] Hs i)
    (hA : ∀ i, IsHilbertSchmidt (A i)) :
    Summable fun j : ∀ i, stdIndex (Hs i) => ‖Ψ (fun i => A i (stdBasis (Hs i) (j i)))‖ ^ 2 := by
  have hs := (splitHeight_summable_pi_prod (α := fun i => stdIndex (Hs i))
    (f := fun i k => ‖A i (stdBasis (Hs i) k)‖ ^ 2) (fun _ _ => sq_nonneg _) hA).mul_left c.re
  refine hs.congr fun j => ?_
  have h1 := hΨ (fun i => A i (stdBasis (Hs i) (j i))) (fun i => A i (stdBasis (Hs i) (j i)))
  simp only [inner_self_eq_norm_sq_to_K] at h1
  have h2 : ((‖Ψ (fun i => A i (stdBasis (Hs i) (j i)))‖ ^ 2 : ℝ) : ℂ)
      = c * ((∏ i, ‖A i (stdBasis (Hs i) (j i))‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; exact h1
  have h3 := congrArg Complex.re h2
  rw [Complex.ofReal_re, Complex.re_mul_ofReal] at h3
  exact h3.symm

theorem tensorTrace_hasTrace : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Φ Φ' : ContinuousMultilinearMap ℂ Hs H) (κ κ' : ℂ), (∀ y y', inner ℂ (Φ y') (Φ y) = ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ y') (Φ' y) = κ * ∏ i, inner ℂ (y' i) (y i)) → (∀ y y', inner ℂ (Φ' y') (Φ' y) = κ' * ∏ i, inner ℂ (y' i) (y i)) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ y, X (Φ y) = Φ' fun i => B i (y i)) → (∀ v, (∀ y, inner ℂ (Φ y) v = 0) → X v = 0) → HasTrace X (κ * ∏ i, b i) := by
  intro ι _ _ Hs _ _ _ H _ _ _ Φ Φ' κ κ' hΦ hΦΦ' hΦ' B b hB X hX hX0
  classical
  let J : ι → Type := fun i => stdIndex (Hs i)
  let e : ∀ i, HilbertBasis (J i) ℂ (Hs i) := fun i => stdBasis (Hs i)
  let u : (∀ i, J i) → H := fun j => Φ (fun i => e i (j i))

  have hu : Orthonormal ℂ u := by
    rw [orthonormal_iff_ite]
    intro j' j
    change ⟪Φ _, Φ _⟫_ℂ = _
    rw [hΦ]
    have : ∀ i, ⟪e i (j' i), e i (j i)⟫_ℂ = if j' i = j i then 1 else 0 := fun i =>
      (orthonormal_iff_ite.1 (e i).orthonormal) _ _
    simp only [this]
    by_cases h : ∀ x, j' x = j x
    · rw [if_pos (funext h)]
      exact Finset.prod_eq_one fun i _ => if_pos (h i)
    · rw [if_neg fun h' => h (congrFun h')]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

  have hperp : ∀ x : H, (∀ j, ⟪u j, x⟫_ℂ = 0) → ∀ y, ⟪Φ y, x⟫_ℂ = 0 := by
    intro x hx y
    have hL := GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e ℂ
      ((innerSL ℂ x).compContinuousMultilinearMap Φ) 0 fun j => by
        simp only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply,
          ContinuousMultilinearMap.zero_apply]
        rw [← inner_conj_symm]; simp [u] at hx; simp [hx]
    have := congrArg (fun L : ContinuousMultilinearMap ℂ Hs ℂ => L y) hL
    simp only [compContinuousMultilinearMap_coe, Function.comp_apply, innerSL_apply_apply,
      ContinuousMultilinearMap.zero_apply] at this
    rw [← inner_conj_symm, this, map_zero]

  have hinj : Function.Injective u := hu.linearIndependent.injective
  obtain ⟨w, bH, hsw, hb⟩ :=
    Orthonormal.exists_hilbertBasis_extension ((orthonormal_subtype_range hinj).2 hu)
  have hoff : ∀ x ∈ w, x ∉ Set.range u → ∀ y, ⟪Φ y, x⟫_ℂ = 0 := by
    intro x hxw hxu
    refine hperp x fun j => ?_
    have hne : (⟨u j, hsw ⟨j, rfl⟩⟩ : w) ≠ ⟨x, hxw⟩ := fun h => hxu ⟨j, congrArg Subtype.val h⟩
    have := bH.orthonormal.2 hne
    simpa [hb] using this

  choose n C D hC hD hBeq using fun i => (hB i).1

  have hG : ∀ (Ψ : ContinuousMultilinearMap ℂ Hs H) (c : ℂ),
      (∀ y y', ⟪Ψ y', Ψ y⟫_ℂ = c * ∏ i, ⟪y' i, y i⟫_ℂ) → ∀ A : ∀ i, Hs i →L[ℂ] Hs i,
      (∀ i, IsHilbertSchmidt (A i)) → ∃ G : H →L[ℂ] H, (∀ y, G (Φ y) = Ψ (fun i => A i (y i))) ∧
        (∀ v, (∀ y, ⟪Φ y, v⟫_ℂ = 0) → G v = 0) ∧ IsHilbertSchmidt G := by
    intro Ψ c hΨ A hA
    obtain ⟨G, hG1, hG2, hG3⟩ := GlobalTheory.T.exists_isHilbertSchmidt_orthonormal_apply_alt H H (∀ i, J i) u
      (fun j => Ψ (fun i => A i (e i (j i)))) hu (tensorTrace_summable_sq Ψ c hΨ A hA)
    refine ⟨G, fun y => ?_, fun v hv => hG2 v fun j => hv _, hG3⟩
    have := GlobalTheory.T.continuousMultilinearMap_ext_hilbertBasis' ι Hs J e H (G.compContinuousMultilinearMap Φ)
      (Ψ.compContinuousLinearMap A) fun j => by simpa using hG1 j
    simpa using congrArg (fun L : ContinuousMultilinearMap ℂ Hs H => L y) this
  have hΦ1 : ∀ y y', ⟪Φ y', Φ y⟫_ℂ = 1 * ∏ i, ⟪y' i, y i⟫_ℂ := fun y y' => by rw [one_mul, hΦ]
  choose GD hGD1 hGD2 hGD3 using fun k : ∀ i, Fin (n i) => hG Φ 1 hΦ1 (fun i => D i (k i)) fun i => hD i _
  choose GC hGC1 hGC2 hGC3 using fun k : ∀ i, Fin (n i) => hG Φ' κ' hΦ' (fun i => C i (k i)) fun i => hC i _

  have hXeq : X = ∑ k, GC k ∘L GD k := by
    have hd : Dense (Submodule.span ℂ w : Set H) := by
      have := bH.dense_span
      rw [hb, Subtype.range_coe] at this
      exact Submodule.dense_iff_topologicalClosure_eq_top.2 this
    refine ContinuousLinearMap.ext_on hd fun x hx => ?_
    by_cases hxu : x ∈ Set.range u
    · obtain ⟨j, rfl⟩ := hxu
      change X (Φ _) = _
      rw [hX, ContinuousLinearMap.sum_apply]
      simp only [comp_apply]
      rw [show (fun i => B i (e i (j i))) = fun i => ∑ m, C i m (D i m (e i (j i))) from
        funext fun i => by rw [hBeq i]; simp]
      rw [Φ'.map_sum (fun i m => C i m (D i m (e i (j i))))]
      refine Finset.sum_congr rfl fun k _ => ?_
      change _ = GC k (GD k (Φ fun i => e i (j i)))
      rw [hGD1, hGC1]
    · have h0 := hoff x hx hxu
      rw [hX0 x h0, ContinuousLinearMap.sum_apply]
      simp [hGD2 _ x h0]
  have hTC : IsTraceClass X := by
    rw [hXeq]; exact isTraceClass_sum _ fun k _ => (hGC3 k).isTraceClass_comp (hGD3 k)
  refine ⟨hTC, ?_⟩

  have htr := hTC.hasSum_trace bH
  let g : (∀ i, J i) → w := fun j => ⟨u j, hsw ⟨j, rfl⟩⟩
  have hg : Function.Injective g := fun j j' h => hinj (congrArg Subtype.val h)
  have hz : ∀ x ∉ Set.range g, ⟪bH x, X (bH x)⟫_ℂ = 0 := by
    intro x hx
    have hxu : x.1 ∉ Set.range u := fun ⟨j, hj⟩ => hx ⟨j, Subtype.ext hj⟩
    simp [hb, hX0 _ (hoff x.1 x.2 hxu)]
  rw [← hg.hasSum_iff hz] at htr
  have hval : ∀ j, ⟪bH (g j), X (bH (g j))⟫_ℂ = κ * ∏ i, ⟪e i (j i), B i (e i (j i))⟫_ℂ := by
    intro j
    simp only [hb, g]
    change ⟪Φ _, X (Φ _)⟫_ℂ = _
    rw [hX, hΦΦ']
  have hprod := (GlobalTheory.T.hasSum_tuple_prod_of_summable_norm_complex ι J (fun i k => ⟪e i k, B i (e i k)⟫_ℂ)
    fun i => (hB i).1.summable_norm (e i)).mul_left κ
  have hb' : ∀ i, ∑' k, ⟪e i k, B i (e i k)⟫_ℂ = b i := fun i =>
    ((hB i).1.hasSum_trace (e i)).tsum_eq.trans (hB i).2
  simp only [hb'] at hprod
  refine htr.unique ?_
  simpa only [Function.comp_def, hval] using hprod

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralPeriodicEqMeasureMulSumCosets
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

namespace GlobalTheory.RootEx.UnfoldShape

theorem integral_periodic_eq_measure_mul_sum_cosets :
    ∀ (V : Type) [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (μ : Measure V) [μ.IsAddLeftInvariant] (H : AddSubgroup V), MeasurableSet (H : Set V) → μ H ≠ ⊤ → ∀ (F : V → ℂ) (ι : Type) (T : Finset ι) (t : ι → V), (∀ x, ∀ h ∈ H, F (x + h) = F x) → (∀ x, F x ≠ 0 → ∃ w ∈ T, x - t w ∈ H) → (∀ w ∈ T, ∀ w' ∈ T, t w - t w' ∈ H → w = w') → ∫ x, F x ∂μ = (μ.real H : ℂ) * ∑ w ∈ T, F (t w) := by
  intro V _ _ _ μ _ H hH hμ F ι T t hper hsupp hinj
  set S : ι → Set V := fun w => (fun x => -t w + x) ⁻¹' (H : Set V) with hS
  have hmem : ∀ w x, x ∈ S w ↔ x - t w ∈ H := by
    intro w x
    simp only [hS, Set.mem_preimage, SetLike.mem_coe]
    rw [neg_add_eq_sub]
  have hSm : ∀ w, MeasurableSet (S w) := fun w => (measurable_const_add (-t w)) hH
  have hSμ : ∀ w, μ (S w) = μ H := fun w => measure_preimage_add μ (-t w) _
  have hval : ∀ w x, x - t w ∈ H → F x = F (t w) := by
    intro w x hx
    have := hper (t w) _ hx
    rwa [add_sub_cancel] at this
  have hF : F = fun x => ∑ w ∈ T, (S w).indicator (fun _ => F (t w)) x := by
    funext x
    by_cases hx : ∃ w ∈ T, x - t w ∈ H
    · obtain ⟨w, hw, hxw⟩ := hx
      rw [Finset.sum_eq_single w]
      · rw [Set.indicator_of_mem ((hmem w x).2 hxw)]
        exact hval w x hxw
      · intro w' hw' hne
        apply Set.indicator_of_notMem
        intro h
        apply hne
        apply hinj w' hw' w hw
        have := H.sub_mem hxw ((hmem w' x).1 h)
        rwa [sub_sub_sub_cancel_left] at this
      · intro h; exact absurd hw h
    · have h0 : F x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      rw [h0]
      symm
      apply Finset.sum_eq_zero
      intro w hw
      apply Set.indicator_of_notMem
      intro h
      exact hx ⟨w, hw, (hmem w x).1 h⟩
  have h1 : ∫ x, F x ∂μ = ∫ x, ∑ w ∈ T, (S w).indicator (fun _ => F (t w)) x ∂μ := by
    conv_lhs => rw [hF]
  rw [h1, integral_finset_sum, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro w _
    rw [integral_indicator_const _ (hSm w), Measure.real, hSμ w, Complex.real_smul]
    rfl
  · intro w _
    rw [integrable_indicator_iff (hSm w)]
    exact integrableOn_const (by rw [hSμ w]; exact hμ)

end GlobalTheory.RootEx.UnfoldShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenSetOfLeRank
section
open Matrix Topology

namespace GlobalTheory

theorem exists_mul_mul_eq_one_of_le_rank {k : Type} [Field k] {m n : Type} [Fintype m] [Fintype n]
    {κ : ℕ} (x : Matrix m n k) (h : κ ≤ x.rank) :
    ∃ (A : Matrix (Fin κ) m k) (B : Matrix n (Fin κ) k), A * x * B = 1 := by
  classical
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank
    (R := k) (M := LinearMap.range x.mulVecLin) (n := κ) h
  choose v hv using fun i => (w i).2
  let B : Matrix n (Fin κ) k := Matrix.of fun j i => v i j
  have hw' : LinearIndependent k (fun i => (w i : m → k)) :=
    hw.map' (LinearMap.range x.mulVecLin).subtype (Submodule.ker_subtype _)
  have hcol : (x * B).col = fun i => (w i : m → k) := by
    funext i j
    rw [← hv i]
    simp [B, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.col]
  have hinj : Function.Injective (x * B).mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hw'
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' (x * B))
    (LinearMap.ker_eq_bot.2 (fun a b hab => hinj (by simpa only [Matrix.toLin'_apply] using hab)))
  refine ⟨LinearMap.toMatrix' g, B, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  rw [Matrix.mul_assoc, this]

theorem isOpen_setOf_le_rank (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    [T1Space k] (m n : Type) [Fintype m] [Fintype n] (κ : ℕ) :
    IsOpen {x : Matrix m n k | κ ≤ x.rank} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨A, B, hAB⟩ := exists_mul_mul_eq_one_of_le_rank x hx
  refine ⟨{y | (A * y * B).det ≠ 0}, ?_, ?_, ?_⟩
  · intro y hy
    have hu : IsUnit (A * y * B) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hy)
    have h1 := Matrix.rank_of_isUnit _ hu
    rw [Fintype.card_fin] at h1
    change κ ≤ y.rank
    rw [← h1]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hc : Continuous fun y : Matrix m n k => (A * y * B).det :=
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_det
    exact isOpen_ne.preimage hc
  · simp [hAB]

end GlobalTheory
end

