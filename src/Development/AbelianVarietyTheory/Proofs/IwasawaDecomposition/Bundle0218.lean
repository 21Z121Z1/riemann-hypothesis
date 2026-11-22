import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalRingCardinality.DataCoeff
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasModelOfAntitone
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0052
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0129
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0027
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHarishChandraTypeDualWeylModuleFockNorm
section
open MvPolynomial Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.DualWeyl GlobalTheory.CompactDS
open Formalism.GradedWeylDivisibility (rowAct rowDeg)
open scoped Matrix

noncomputable section

namespace GlobalTheory.NablaType

variable {n : ℕ}

theorem cdom_of_partial_sums (μ ν : Fin n → ℕ)
    (h : ∀ k : ℕ, (∑ a : Fin n with a.val < k, μ a) ≤ ∑ a : Fin n with a.val < k, ν a)
    (he : ∑ a, μ a = ∑ a, ν a) : CDom (allPos n) (fun a => (μ a : ℝ)) (fun a => (ν a : ℝ)) := by
  classical
  let D : ℕ → ℕ := fun k => (∑ a : Fin n with a.val < k, ν a) - ∑ a : Fin n with a.val < k, μ a
  have hD : ∀ k, (D k : ℝ) = ∑ a : Fin n, if a.val < k then ((ν a : ℝ) - μ a) else 0 := by
    intro k
    simp only [D]
    rw [Nat.cast_sub (h k), ← Finset.sum_filter, Finset.sum_sub_distrib]
    push_cast
    rfl
  have hstep : ∀ i : Fin n, (D (i.val + 1) : ℝ) - D i.val = (ν i : ℝ) - μ i := by
    intro i
    rw [hD, hD, ← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      have : b.val ≠ i.val := fun e => hb (Fin.ext e)
      by_cases h1 : b.val < i.val
      · rw [if_pos h1, if_pos (by omega), sub_self]
      · rw [if_neg h1, if_neg (by omega), sub_self]
    · simp
  have h0 : D 0 = 0 := by simp [D]
  have hn : D n = 0 := by simp [D, he]
  refine ⟨fun a b => if b.val = a.val + 1 then D b.val else 0, fun a b hab => ?_, ?_⟩
  · have : b.val = a.val + 1 := by by_contra h'; exact hab (if_neg h')
    exact ⟨Fin.lt_def.2 (by omega), rfl⟩
  · funext i
    have e1 : ∑ b : Fin n, ((if b.val = i.val + 1 then D b.val else 0 : ℕ) : ℝ) = D (i.val + 1) := by
      by_cases hi : i.val + 1 < n
      · rw [Finset.sum_eq_single ⟨i.val + 1, hi⟩]
        · simp
        · intro b _ hb
          rw [if_neg (fun e => hb (Fin.ext e)), Nat.cast_zero]
        · simp
      · rw [Finset.sum_eq_zero, show i.val + 1 = n by omega, hn, Nat.cast_zero]
        intro b _
        rw [if_neg (by omega), Nat.cast_zero]
    have e2 : ∑ a : Fin n, ((if i.val = a.val + 1 then D i.val else 0 : ℕ) : ℝ) = D i.val := by
      by_cases hi : 0 < i.val
      · rw [Finset.sum_eq_single ⟨i.val - 1, by omega⟩]
        · rw [if_pos (by simp only; omega)]
        · intro b _ hb
          rw [if_neg (fun e => hb (Fin.ext (by simp only; omega))), Nat.cast_zero]
        · simp
      · rw [Finset.sum_eq_zero, show i.val = 0 by omega, h0, Nat.cast_zero]
        intro b _
        rw [if_neg (by omega), Nat.cast_zero]
    rw [Pi.sub_apply, ← hstep, ← e1, ← e2]
    simp only [Finset.sum_apply, Pi.smul_apply, Formalism.REAL.root, Pi.sub_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero]
    congr 1
    · rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem cdom_of_coeff_ne_zero {la : Fin n → ℕ} {f : Pol n ℂ} (hf : f ∈ nabla la ℂ) (m : Fin n × Fin n →₀ ℕ)
    (hm : coeff m f ≠ 0) : CDom (allPos n) (fun a => (rowDeg m a : ℝ)) (fun a => (la a : ℝ)) := by
  unfold nabla at hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ n n la] at hf
  by_contra hc
  apply hm
  clear hm
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, rfl, rfl⟩ := hx
    by_contra h0
    obtain ⟨h1, h2⟩ := Formalism.GradedWeylDivisibility.bidetDominance ℂ n n K sz hsz I m (mem_support_iff.2 h0)
    exact hc (cdom_of_partial_sums _ _ h1 h2)
  | zero => simp
  | add x y _ _ hx hy => rw [coeff_add, hx, hy, add_zero]
  | smul c x _ hx => rw [coeff_smul, hx, smul_zero]

def act (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) : Space lam.natW →L[ℂ] Space lam.natW :=
  LinearMap.toContinuousLinearMap
    ((g.det ^ lam.detShift) • ((toSpace lam.natW).conj (rho lam.natW ℂ g)))

def incl (lam : DomWeight n) : Space lam.natW →ₗ[ℂ] Pol n ℂ :=
  (nabla lam.natW ℂ).subtype ∘ₗ (toSpace lam.natW).symm.toLinearMap

theorem incl_injective (lam : DomWeight n) : Function.Injective (incl lam) :=
  (nabla lam.natW ℂ).injective_subtype.comp (toSpace lam.natW).symm.injective

theorem incl_mem (lam : DomWeight n) (x : Space lam.natW) : incl lam x ∈ nabla lam.natW ℂ :=
  ((toSpace lam.natW).symm x).2

theorem incl_act (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ) (x : Space lam.natW) :
    incl lam (act lam g x) = (g.det ^ lam.detShift) • rowAct ℂ gᵀ (incl lam x) := rfl

theorem act_unitary (lam : DomWeight n) (u : UN n) (x : Space lam.natW) :
    act lam u.1 x = (u.1.det ^ lam.detShift) • rhoSpace lam.natW u x := rfl

theorem det_ne_zero {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin n) ℂ) : g.det ≠ 0 :=
  (Matrix.UnitaryGroup.det_isUnit ⟨g, hg⟩).ne_zero

theorem isURepOn_act (lam : DomWeight n) : IsURepOn (UJset (allPos n)) (act lam) := by
  rw [ujset_eq]
  refine ⟨⟨?_, fun a _ b _ => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · ext x
    apply incl_injective
    rw [incl_act, Matrix.transpose_one, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]
    simp
  · ext x
    apply incl_injective
    rw [ContinuousLinearMap.comp_apply, incl_act, incl_act, incl_act, Matrix.transpose_mul,
      ← Formalism.GradedWeylDivisibility.rowActMul ℂ n n, Matrix.det_mul, mul_zpow, map_smul, smul_smul]
    rfl
  · have h1 : ‖g.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hg)
    rw [act_unitary lam ⟨g, hg⟩, norm_smul, norm_zpow, h1, one_zpow, one_mul, norm_rhoSpace]
  · rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun u : UN n => u.1.det ^ lam.detShift :=
      (continuous_subtype_val.matrix_det).zpow₀ _ fun u => Or.inl (det_ne_zero u.2)
    exact h1.smul (continuous_rhoSpace v)

theorem coeff_torus (lam : DomWeight n) (θ : Fin n → ℝ) (x : Space lam.natW) (m : Fin n × Fin n →₀ ℕ) :
    coeff m (incl lam (act lam (torus θ) x)) =
      chr (fun a => (rowDeg m a : ℝ) + lam.detShift) θ * coeff m (incl lam x) := by
  rw [incl_act, torus, Matrix.diagonal_transpose, coeff_smul, Formalism.GradedWeylDivisibility.ldrow_coeff_rowAct_diag, Matrix.det_diagonal,
    smul_eq_mul, mul_left_comm, mul_comm]
  congr 1
  simp only [← Complex.exp_nat_mul]
  rw [chr, ← Complex.exp_sum, ← Complex.exp_sum, ← Complex.exp_int_mul, ← Complex.exp_add]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem natW_add (lam : DomWeight n) (a : Fin n) : (lam.natW a : ℝ) + lam.detShift = lam.w a := by
  exact_mod_cast (factNatW n lam).2.1 a

theorem isKTypeOf_act (lam : DomWeight n) : IsKTypeOf (allPos n) (act lam) (fun a => (lam.w a : ℝ)) ⊤ := by
  have ha := (factNatW n lam).1
  refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ hS => ?_, ?_, fun μ v _ hv hw => ?_⟩
  · by_cases h0 : S = ⊥
    · exact Or.inl h0
    right
    have hU : ∀ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ f ∈ S.map (incl lam), rowAct ℂ u f ∈ S.map (incl lam) := by
      rintro u hu _ ⟨f, hf, rfl⟩
      have hu' := transpose_mem_unitaryGroup hu
      have h1 : incl lam (act lam uᵀ f) ∈ S.map (incl lam) := ⟨_, hS _ (by rw [kset_eq]; exact hu') f hf, rfl⟩
      rw [incl_act, Matrix.transpose_transpose] at h1
      exact (Submodule.smul_mem_iff _ (zpow_ne_zero _ (det_ne_zero hu'))).1 h1
    have hcl := GlobalTheory.Branching.rowDivClosed_of_rowAct_stable _ (GlobalTheory.Branching.rowAct_mem_of_unitary_stable _ hU)
    have hne : S.map (incl lam) ≠ ⊥ := fun e => h0 (Submodule.map_injective_of_injective (incl_injective lam)
      (e.trans (Submodule.map_bot _).symm))
    have hle := GlobalTheory.Branching.dualWeyl_le_of_rowDivClosed le_rfl lam.natW ha _
      (by rintro _ ⟨f, -, rfl⟩; exact incl_mem lam f) hcl hne
    refine eq_top_iff.2 fun f _ => ?_
    obtain ⟨g, hg, e⟩ := hle (incl_mem lam f)
    rwa [← incl_injective lam e]
  · refine ⟨toSpace _ ⟨_, extremal_mem ha⟩, trivial, fun h => ?_, fun θ _ => ?_⟩
    · exact extremal_ne_zero (congrArg (incl lam) h)
    · apply incl_injective
      ext m
      have h1 := coeff_torus lam θ (toSpace _ ⟨_, extremal_mem ha⟩) m
      refine h1.trans ?_
      rw [map_smul, coeff_smul, smul_eq_mul]
      by_cases hm : coeff m (incl lam (toSpace _ ⟨_, extremal_mem ha⟩)) = 0
      · rw [hm, mul_zero, mul_zero]
      have h2 := Formalism.GradedWeylDivisibility.hwRowWeight ℂ n n le_rfl lam.natW ha hm
      have h3 : (fun a => (rowDeg m a : ℝ) + lam.detShift) = fun a => (lam.w a : ℝ) := by
        funext a
        rw [← natW_add, ← Formalism.GradedWeylDivisibility.ldrow_weight_rowW, h2]
        simp [Formalism.GradedWeylDivisibility.rowNu]
      rw [h3]
      rfl
  · have h0 : incl lam v ≠ 0 := fun e => hv (incl_injective lam (e.trans (map_zero _).symm))
    obtain ⟨m, hm⟩ := ne_zero_iff.1 h0
    have h1 : μ = fun a => (rowDeg m a : ℝ) + lam.detShift := by
      refine chr_inj fun θ => ?_
      have h2 := coeff_torus lam θ v m
      have h3 : act lam (torus θ) v = chr μ θ • v := hw θ (by rw [kset_eq]; exact torus_mem θ)
      rw [h3, map_smul, coeff_smul, smul_eq_mul] at h2
      exact mul_right_cancel₀ hm h2
    have h4 := cdom_add (cdom_of_coeff_ne_zero (incl_mem lam v) m hm)
      (cdom_refl (allPos n) fun _ => (lam.detShift : ℝ))
    rw [h1]
    have h5 : (fun a => (lam.w a : ℝ)) = (fun a => (lam.natW a : ℝ)) + fun _ => (lam.detShift : ℝ) :=
      funext fun a => (natW_add lam a).symm
    rw [h5]
    exact h4

theorem exists_isHCTypeU_nablaSq : ∀ (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n), ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (e : H →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ), Formalism.MainNotions.S.IsHCTypeU n (fun i => (lam.w i : ℝ) + ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ)) π ∧ Function.Injective e ∧ (∀ x, e x ∈ Formalism.BasicNotions.nablaSq ℂ n lam) ∧ ∀ g : GL (Fin n) ℂ, (g : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ x, e (π (g : Matrix (Fin n) (Fin n) ℂ) x) = Formalism.BasicNotions.sqAct ℂ n lam g (e x) := by
  intro n lam
  have hK := isKTypeOf_act lam
  refine ⟨Space lam.natW, inferInstance, inferInstance, act lam, incl lam,
    ⟨?_, inferInstance, isURepOn_act lam, ?_⟩, incl_injective lam, incl_mem lam, fun g _ x => ?_⟩
  · obtain ⟨v, -, hv, -⟩ := hK.2.2.2.1
    exact ⟨v, 0, hv⟩
  · convert hK using 1
    funext a
    unfold allPos
    rw [GlobalTheory.DefiniteCheck.lowK_const]
    simp [rhoVec]
  · rw [incl_act]
    simp [sqAct, detPow]

end GlobalTheory.NablaType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntertwinerOfSameHarishChandraParamUnitary
section
open Matrix Finset

noncomputable section

namespace GlobalTheory.UnitaryHighestWeightUnique

open PI.UpqRep GlobalTheory.UnitaryHighestWeight

open Matrix Finset in
theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.height_le {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ}
    (h : _root_.PI.UpqRep.CDom ε μ Λ) :
    ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x ≤ ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x ∧
      (∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x = ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x → Λ = μ) := by
  unfold _root_.PI.UpqRep.CDom at h
  obtain ⟨c, hc, h⟩ := h
  have key : ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x - ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x =
      ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    have hx : ∀ x, Λ x - μ x = (Λ - μ) x := fun x => rfl
    simp_rw [← mul_sub, hx, h]
    unfold _root_.PI.UpqRep.root
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_sub, Finset.sum_sub_distrib, mul_comm, mul_left_comm]
    ring
  have hterm : ∀ a b : Fin n, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have hab := (hc a b h0).1
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hrow : ∀ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    fun a => Finset.sum_nonpos fun b _ => hterm a b
  have hsum : ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun a _ => hrow a
  refine ⟨by linarith, fun heq => ?_⟩
  have hzero : ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) = 0 := by
    linarith
  have hc0 : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have hab := (hc a b h0).1
    have hlt : ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) < 0 := by
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      exact mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero h0) (by linarith)
    have ha := (Finset.sum_eq_zero_iff_of_nonpos fun a _ => hrow a).1 hzero a (Finset.mem_univ a)
    have hb := (Finset.sum_eq_zero_iff_of_nonpos fun b _ => hterm a b).1 ha b (Finset.mem_univ b)
    linarith
  have : Λ - μ = 0 := by simp [h, hc0]
  exact sub_eq_zero.mp this

open Matrix Finset in

theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest {k : ℕ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)} {Λ : Fin k → ℝ}
    (hπ : _root_.PI.UpqRep.IsURepOn (_root_.PI.UpqRep.UJset (_root_.PI.UpqRep.allPos k)) π) (hK : _root_.PI.UpqRep.IsKTypeOf (_root_.PI.UpqRep.allPos k) π Λ ⊤) :
    ∃ E : Fin k → Fin k → Module.End ℂ W, _root_.Formalism.REAL.GlRel E ∧
      (∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
        HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0) ∧
      (∀ S : Submodule ℂ W, (∀ a b, ∀ x ∈ S, E a b x ∈ S) → S = ⊥ ∨ S = ⊤) ∧
      ∃ x, x ≠ 0 ∧ _root_.Formalism.REAL.IsHW E (fun a => (Λ a : ℂ)) x := by
  obtain ⟨E, hrel, -, hder⟩ := _root_.GlobalTheory.UnitaryDerived.exists_derived_action k W π hπ
  unfold _root_.PI.UpqRep.IsKTypeOf at hK
  obtain ⟨-, -, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hK
  refine ⟨E, hrel, hder, ?_, v, hv0, ?_⟩
  · intro S hS
    have hSπ : _root_.PI.UpqRep.IsKStableOn (_root_.PI.UpqRep.allPos k) π S := by
      unfold _root_.PI.UpqRep.IsKStableOn
      intro g hg w hw
      exact _root_.GlobalTheory.UnitaryHighestWeight.stable_of_derived hπ E hder S
        (by unfold _root_.Formalism.REAL.KStable; exact fun a b _ x hx => hS a b x hx) g
        ((_root_.GlobalTheory.UnitaryHighestWeight.mem_K_iff g).1 hg) w hw
    exact hirr S le_top hSπ
  · have hvE : _root_.Formalism.REAL.IsWeight E Λ v := _root_.GlobalTheory.UnitaryHighestWeight.isWeight_of_isWtOn E hder Λ v hvw
    unfold _root_.Formalism.REAL.IsWeight at hvE
    unfold _root_.Formalism.REAL.IsHW
    refine ⟨fun a => hvE a, fun a b hab => ?_⟩
    by_contra hne
    unfold _root_.Formalism.REAL.GlRel at hrel
    have hw : _root_.Formalism.REAL.IsWeight E (Λ + _root_.PI.UpqRep.root a b) (E a b v) := by
      unfold _root_.Formalism.REAL.IsWeight
      intro c
      have hc := congrArg (fun T : Module.End ℂ W => T v) (hrel c c a b)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
      have hsplit : E c c (E a b v) = E a b (E c c v) +
          ((if c = a then E c b else 0) - if b = c then E a c else 0) v := by
        rw [LinearMap.sub_apply, ← hc]; abel
      rw [hsplit, hvE c, map_smul]
      unfold _root_.PI.UpqRep.root
      by_cases hca : c = a
      · subst hca
        have hcb : b ≠ c := ne_of_gt hab
        simp [hcb, Ne.symm hcb, add_smul, add_comm]
      · by_cases hcb : b = c
        · subst hcb
          simp [hca, Ne.symm hca, add_smul, sub_eq_add_neg, add_comm]
        · simp [hca, hcb, Ne.symm hcb]
    have ht := _root_.GlobalTheory.UnitaryHighestWeight.isWtOn_of_isWeight hπ E hder _ _ hw
    have hD := hdom _ (E a b v) Submodule.mem_top hne ht
    have hle := (_root_.GlobalTheory.UnitaryHighestWeightUnique.height_le hD).1
    have hcomp : ∑ x : Fin k, ((x : ℕ) : ℝ) * (Λ + _root_.PI.UpqRep.root a b) x =
        ∑ x : Fin k, ((x : ℕ) : ℝ) * Λ x + (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
      unfold _root_.PI.UpqRep.root
      simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith

open Matrix Finset in

theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.intertwine_group {W₁ W₂ : Type} [NormedAddCommGroup W₁]
    [InnerProductSpace ℂ W₁] [NormedAddCommGroup W₂] [InnerProductSpace ℂ W₂]
    [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]
    (U₁ : ℝ → W₁ →L[ℂ] W₁) (A₁ : W₁ →ₗ[ℂ] W₁) (h₁ : ∀ v, U₁ 0 v = v)
    (hadd₁ : ∀ s t v, U₁ (s + t) v = U₁ s (U₁ t v)) (hd₁ : ∀ v, HasDerivAt (fun t => U₁ t v) (A₁ v) 0)
    (U₂ : ℝ → W₂ →L[ℂ] W₂) (A₂ : W₂ →ₗ[ℂ] W₂) (h₂ : ∀ v, U₂ 0 v = v)
    (hadd₂ : ∀ s t v, U₂ (s + t) v = U₂ s (U₂ t v)) (hd₂ : ∀ v, HasDerivAt (fun t => U₂ t v) (A₂ v) 0)
    (T : W₁ →ₗ[ℂ] W₂) (hT : ∀ v, T (A₁ v) = A₂ (T v)) (v : W₁) (t : ℝ) :
    T (U₁ t v) = U₂ t (T v) := by
  let Tc : W₁ →L[ℝ] W₂ := (LinearMap.toContinuousLinearMap T).restrictScalars ℝ
  let Ac : W₂ →L[ℝ] W₂ := (LinearMap.toContinuousLinearMap A₂).restrictScalars ℝ
  have hTc : ∀ x, Tc x = T x := fun x => rfl
  have hAc : ∀ x, Ac x = A₂ x := fun x => rfl
  have hf : ∀ s, HasDerivAt (fun s => T (U₁ s v)) (Ac (T (U₁ s v))) s := by
    intro s
    have h := _root_.GlobalTheory.UnitaryHighestWeight.deriv_left U₁ A₁ hadd₁ hd₁ v s
    have h' := Tc.hasFDerivAt.comp_hasDerivAt s h
    simp only [Function.comp_def, hTc] at h'
    rwa [hAc, ← hT]
  have hg : ∀ s, HasDerivAt (fun s => U₂ s (T v)) (Ac (U₂ s (T v))) s := by
    intro s
    rw [hAc]
    exact _root_.GlobalTheory.UnitaryHighestWeight.deriv_left U₂ A₂ hadd₂ hd₂ (T v) s
  have heq := ODE_solution_unique_univ (v := fun _ => Ac) (s := fun _ => Set.univ)
    (K := ‖Ac‖₊) (t₀ := 0) (fun _ => Ac.lipschitz.lipschitzOnWith)
    (fun s => ⟨hf s, Set.mem_univ _⟩) (fun s => ⟨hg s, Set.mem_univ _⟩) (by simp [h₁, h₂])
  exact congrFun heq t

open Matrix Finset in

theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU : ∀ (k : ℕ) (u : Fin k → ℝ)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (π₁ : Matrix (Fin k) (Fin k) ℂ → (H₁ →L[ℂ] H₁))
    (π₂ : Matrix (Fin k) (Fin k) ℂ → (H₂ →L[ℂ] H₂)), _root_.Formalism.MainNotions.S.IsHCTypeU k u π₁ → _root_.Formalism.MainNotions.S.IsHCTypeU k u π₂ →
    ∃ A : H₁ ≃ₗ[ℂ] H₂, ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ x, A (π₁ g x) = π₂ g (A x) := by
  intro k u H₁ _ _ H₂ _ _ π₁ π₂ h₁ h₂
  have h₁' : _root_.PI.UpqRep.IsHCTypeU k u π₁ := h₁
  have h₂' : _root_.PI.UpqRep.IsHCTypeU k u π₂ := h₂
  unfold _root_.PI.UpqRep.IsHCTypeU at h₁' h₂'
  obtain ⟨hnt₁, hfd₁, hπ₁, hK₁⟩ := h₁'
  obtain ⟨hnt₂, hfd₂, hπ₂, hK₂⟩ := h₂'
  obtain ⟨E₁, hrel₁, hder₁, hirr₁, x₁, hx₁, hw₁⟩ :=
    _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest hπ₁ hK₁
  obtain ⟨E₂, hrel₂, hder₂, hirr₂, x₂, hx₂, hw₂⟩ :=
    _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest hπ₂ hK₂
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.exists_linearEquiv_of_irreducible_isHW H₁ H₂ k E₁ E₂ _ x₁ x₂ hrel₁ hrel₂
    hirr₁ hirr₂ hw₁ hw₂ hx₁ hx₂
  refine ⟨T, fun g hg x => ?_⟩
  have hL : _root_.Formalism.REAL.Jm (_root_.PI.UpqRep.allPos k) = 1 := by
    unfold _root_.Formalism.REAL.Jm _root_.PI.UpqRep.allPos
    simp
  have hgL : g ∈ _root_.Formalism.REAL.Kset (_root_.PI.UpqRep.allPos k) := by
    unfold _root_.Formalism.REAL.Kset
    simp only [hL, mul_one, one_mul, and_true]
    exact hg
  obtain ⟨Y, hY, hexp, -⟩ := _root_.Formalism.REAL.compact_exists_log_bounded _ g hgL
  have hskew : Yᴴ = -Y := by
    unfold _root_.Formalism.REAL.inK _root_.Formalism.REAL.inG at hY
    rw [hL] at hY
    simp only [mul_one, one_mul, and_true] at hY
    exact eq_neg_of_add_eq_zero_left hY
  let A₁ : H₁ →ₗ[ℂ] H₁ := ∑ a, ∑ b, Y a b • E₁ a b
  let A₂ : H₂ →ₗ[ℂ] H₂ := ∑ a, ∑ b, Y a b • E₂ a b
  have hA₁ : ∀ v, A₁ v = ∑ a, ∑ b, Y a b • E₁ a b v := by
    intro v; simp [A₁, LinearMap.sum_apply]
  have hA₂ : ∀ v, A₂ v = ∑ a, ∑ b, Y a b • E₂ a b v := by
    intro v; simp [A₂, LinearMap.sum_apply]
  have hTA : ∀ v, T.toLinearMap (A₁ v) = A₂ (T.toLinearMap v) := by
    intro v
    simp [hA₁, hA₂, map_sum, map_smul, hT]
  have key := _root_.GlobalTheory.UnitaryHighestWeightUnique.intertwine_group
    (fun t : ℝ => π₁ (NormedSpace.exp ((t : ℂ) • Y))) A₁
    (fun v => _root_.GlobalTheory.UnitaryHighestWeight.group_zero hπ₁ Y v)
    (fun s t v => _root_.GlobalTheory.UnitaryHighestWeight.group_add hπ₁ hskew s t v)
    (fun v => by rw [hA₁]; exact hder₁ Y hskew v)
    (fun t : ℝ => π₂ (NormedSpace.exp ((t : ℂ) • Y))) A₂
    (fun v => _root_.GlobalTheory.UnitaryHighestWeight.group_zero hπ₂ Y v)
    (fun s t v => _root_.GlobalTheory.UnitaryHighestWeight.group_add hπ₂ hskew s t v)
    (fun v => by rw [hA₂]; exact hder₂ Y hskew v)
    T.toLinearMap hTA x 1
  simpa [hexp] using key

end GlobalTheory.UnitaryHighestWeightUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdAdelicChar

theorem eq_of_psiInf_eq {F : Type} [Field F] [NumberField F] {ψ ψ' : AddChar (AF F) ℂ}
    (h : IsCharAF F ψ) (h' : IsCharAF F ψ') (e : ∀ x, psiInf F ψ x = psiInf F ψ' x) : ψ = ψ' := by
  have hrat : ∀ x : F, ψ (pairA F 0 (algebraMap F (Af F) x)) = ψ' (pairA F 0 (algebraMap F (Af F) x)) := fun x => by
    rw [GlobalTheory.StdRat.char_fin_rat ψ h, GlobalTheory.StdRat.char_fin_rat ψ' h', e]
  have hp : Continuous fun y : Af F => pairA F 0 y := Continuous.prodMk continuous_const continuous_id
  have hint : ∀ α : Af F, (∀ v, α v ∈ v.adicCompletionIntegers F) → ψ (pairA F 0 α) = ψ' (pairA F 0 α) :=
    fun α hα => GlobalTheory.IntDense.mem_of_isClosed F (C := {y | ψ (pairA F 0 y) = ψ' (pairA F 0 y)})
      (isClosed_eq (h.1.comp hp) (h'.1.comp hp)) (fun a => hrat a) α hα
  have hfin : ∀ y : Af F, ψ (pairA F 0 y) = ψ' (pairA F 0 y) := fun y => by
    obtain ⟨a, s, hs, hy⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul F 1 one_pos y
    have e1 : pairA F 0 y = pairA F 0 (algebraMap F (Af F) a) + pairA F 0 s := by
      refine Prod.ext (add_zero _).symm ?_
      show y = algebraMap F (Af F) a + s
      simpa only [one_smul] using hy
    rw [e1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hrat, hint s hs]
  refine AddChar.ext _ _ fun a => ?_
  have e2 : a = pairA F a.1 0 + pairA F 0 a.2 := Prod.ext (add_zero _).symm (zero_add _).symm
  rw [e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hfin]
  exact congrArg (· * _) (e a.1)

theorem isCharAF_inv {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (h : IsCharAF F ψ) :
    IsCharAF F ψ⁻¹ := by
  refine ⟨?_, fun x => ?_, fun a => ?_, ?_⟩
  · exact h.1.comp continuous_neg
  · exact h.2.1 (-x)
  · rw [AddChar.inv_apply, ← map_neg]; exact h.2.2.1 _
  · obtain ⟨x, hx⟩ := h.2.2.2
    exact ⟨-x, by rwa [AddChar.inv_apply, neg_neg]⟩

theorem isStdChar_inv {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s) :
    IsStdChar D ψ⁻¹ (-s) := by
  refine ⟨isCharAF_inv h.1, h.2.1, fun θ hθ x => ?_⟩
  have e : psiInf D.host.F ψ⁻¹ x = psiInf D.host.F ψ (-x) := by
    rw [psiInf, psiInf, AddChar.inv_apply]
    exact congrArg ψ (Prod.ext rfl neg_zero)
  rw [e, h.2.2 θ hθ]
  simp only [TensorProduct.neg_tmul, map_neg, Finset.sum_neg_distrib]
  congr 1
  push_cast
  ring

theorem isStdChar_unique {D : D7} {ψ ψ' : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s)
    (h' : IsStdChar D ψ' s) : ψ = ψ' := by
  obtain ⟨θ, hθ⟩ := h.2.1
  exact eq_of_psiInf_eq h.1 h'.1 fun x => (h.2.2 θ hθ x).trans (h'.2.2 θ hθ x).symm

theorem existsUnique_isStdChar :
    ∀ (D : D7) (s : ℤ), s = 1 ∨ s = -1 → ∃! ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ s := by
  intro D s hs
  obtain ⟨ψ, hψ⟩ := exists_isStdChar D
  rcases hs with rfl | rfl
  · have h1 : IsStdChar D ψ⁻¹ 1 := by simpa using isStdChar_inv hψ
    exact ⟨ψ⁻¹, h1, fun ψ' h' => isStdChar_unique h' h1⟩
  · exact ⟨ψ, hψ, fun ψ' h' => isStdChar_unique h' hψ⟩

end GlobalTheory.StdAdelicChar

end
end

