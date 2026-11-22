import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.WuDecayPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0017

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RankOneTensors
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.SG.RealObj.RankOneTensors

open Formalism.L2.SG.RealObj

section Rk1

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V']

theorem norm_rankOneInnerOperator (a : V) (b : V') : ‖TermOp.rk1 a b‖ = ‖a‖ * ‖b‖ := by
  unfold TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem continuous_rankOneOperator {T : Type*} [TopologicalSpace T] {f : T → V} {g : T → V'} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => TermOp.rk1 (f x) (g x) := by
  have h1 : Continuous fun x => innerSL ℂ (g x) := (innerSL ℂ).continuous.comp hg
  have h2 : Continuous fun x => ContinuousLinearMap.smulRightL ℂ V' V (innerSL ℂ (g x)) :=
    (ContinuousLinearMap.smulRightL ℂ V' V).continuous.comp h1
  unfold TermOp.rk1
  exact h2.clm_apply hf

end Rk1

section Tens

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vt : Type*} [NormedAddCommGroup Vt] [InnerProductSpace ℂ Vt] (T : (∀ v, V v) → Vt)

theorem norm_tens (hT : ∀ x y, ⟪T x, T y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x : ∀ v, V v) : ‖T x‖ = ∏ v, ‖x v‖ := by
  have h := hT x x
  simp only [inner_self_eq_norm_sq_to_K] at h
  have h' : ‖T x‖ ^ 2 = (∏ v, ‖x v‖) ^ 2 := by
    rw [← Finset.prod_pow]
    exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) two_ne_zero).1 h'

theorem tens_eq_zero (hT : ∀ x y, ⟪T x, T y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x : ∀ v, V v) (v0 : ι) (h0 : x v0 = 0) :
    T x = 0 := by
  rw [← norm_eq_zero, norm_tens T hT x]
  exact Finset.prod_eq_zero (Finset.mem_univ v0) (by rw [h0, norm_zero])

theorem eq_of_inner_tens (hS : Submodule.span ℂ (Set.range T) = ⊤) (a b : Vt)
    (h : ∀ z, ⟪T z, a⟫_ℂ = ⟪T z, b⟫_ℂ) : a = b := by
  rw [← sub_eq_zero]
  have hmem : ∀ w ∈ Submodule.span ℂ (Set.range T), ⟪w, a - b⟫_ℂ = 0 := by
    intro w hw
    refine Submodule.span_induction (fun y hy => ?_) ?_ (fun y z _ _ hy hz => ?_) (fun c y _ hy => ?_) hw
    · obtain ⟨z, rfl⟩ := hy
      rw [inner_sub_right, h z, sub_self]
    · exact inner_zero_left _
    · rw [inner_add_left, hy, hz, add_zero]
    · rw [inner_smul_left, hy, mul_zero]
  have h2 := hmem (a - b) (by rw [hS]; exact Submodule.mem_top)
  exact inner_self_eq_zero.mp h2

end Tens

section Fact

variable {ι : Type*} [Fintype ι] {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, MeasurableSpace (G v)] [∀ v, BorelSpace (G v)]
  [∀ v, SecondCountableTopology (G v)] (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
  {V V' : ι → Type*} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  [∀ v, FiniteDimensional ℂ (V v)] [∀ v, NormedAddCommGroup (V' v)] [∀ v, InnerProductSpace ℂ (V' v)]
  [∀ v, FiniteDimensional ℂ (V' v)]
  {Vt Vt' : Type*} [NormedAddCommGroup Vt] [InnerProductSpace ℂ Vt] [FiniteDimensional ℂ Vt]
  [NormedAddCommGroup Vt'] [InnerProductSpace ℂ Vt'] [FiniteDimensional ℂ Vt']
  (T : (∀ v, V v) → Vt) (T' : (∀ v, V' v) → Vt')
  (hT : ∀ x y, ⟪T x, T y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (hT' : ∀ x y, ⟪T' x, T' y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ)
  (hS : Submodule.span ℂ (Set.range T) = ⊤)
  (W : ∀ v, G v → V v) (W' : ∀ v, G v → V' v) (hW : ∀ v, Continuous (W v)) (hW' : ∀ v, Continuous (W' v))
  (Wt : (∀ v, G v) → Vt) (Wt' : (∀ v, G v) → Vt') (hWt : Continuous Wt) (hWt' : Continuous Wt')
  (hten : ∀ x, Wt x = T fun v => W v (x v)) (hten' : ∀ x, Wt' x = T' fun v => W' v (x v))

include hT hT' hS hW hW' hWt hWt' hten hten' in

theorem oo_factor (γ : ∀ v, G v) (y : ∀ v, V' v) :
    haveI : ∀ v, CompleteSpace (V v) := fun v => FiniteDimensional.complete ℂ (V v)
    haveI := FiniteDimensional.complete ℂ Vt
    (∫ x, TermOp.rk1 (Wt x) (Wt' (γ⁻¹ * x)) ∂(Measure.pi μ)) (T' y) =
      T fun v => (∫ s, TermOp.rk1 (W v s) (W' v ((γ v)⁻¹ * s)) ∂(μ v)) (y v) := by
  have : ∀ v, CompleteSpace (V v) := fun v => FiniteDimensional.complete ℂ (V v)
  have := FiniteDimensional.complete ℂ Vt
  let f : ∀ v, G v → (V' v →L[ℂ] V v) := fun v s => TermOp.rk1 (W v s) (W' v ((γ v)⁻¹ * s))
  let F : (∀ v, G v) → (Vt' →L[ℂ] Vt) := fun x => TermOp.rk1 (Wt x) (Wt' (γ⁻¹ * x))
  show (∫ x, F x ∂(Measure.pi μ)) (T' y) = T fun v => (∫ s, f v s ∂(μ v)) (y v)
  have hfc : ∀ v, Continuous (f v) := fun v =>
    continuous_rankOneOperator (hW v) ((hW' v).comp (continuous_const.mul continuous_id))
  have hFc : Continuous F := continuous_rankOneOperator hWt (hWt'.comp (continuous_const.mul continuous_id))
  have hnorm : ∀ x, ‖F x‖ = ∏ v, ‖f v (x v)‖ := by
    intro x
    simp only [F, f, norm_rankOneInnerOperator, hten, hten', norm_tens T hT, norm_tens T' hT', Finset.prod_mul_distrib]
    rfl
  have hzero : ∀ v0, ¬ Integrable (f v0) (μ v0) → (T fun v => (∫ s, f v s ∂(μ v)) (y v)) = 0 := by
    intro v0 h0
    refine tens_eq_zero T hT _ v0 ?_
    show (∫ s, f v0 s ∂(μ v0)) (y v0) = 0
    rw [integral_undef h0, ContinuousLinearMap.zero_apply]
  by_cases hF : Integrable F (Measure.pi μ)
  · by_cases hloc : ∀ v, Integrable (f v) (μ v)
    · refine eq_of_inner_tens T hS _ _ fun z => ?_
      rw [ContinuousLinearMap.integral_apply hF, ← integral_inner (hF.apply_continuousLinearMap _), hT]
      have hl : ∀ v, ⟪z v, (∫ s, f v s ∂(μ v)) (y v)⟫_ℂ =
          ∫ s, ⟪W' v ((γ v)⁻¹ * s), y v⟫_ℂ * ⟪z v, W v s⟫_ℂ ∂(μ v) := by
        intro v
        rw [ContinuousLinearMap.integral_apply (hloc v), ← integral_inner ((hloc v).apply_continuousLinearMap _)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
        simp only [f, TermOp.rankOneInnerOperator_apply, inner_smul_right]
      have hp : ∀ x, ⟪T z, F x (T' y)⟫_ℂ = ∏ v, ⟪W' v ((γ v)⁻¹ * x v), y v⟫_ℂ * ⟪z v, W v (x v)⟫_ℂ := by
        intro x
        simp only [F, TermOp.rankOneInnerOperator_apply, inner_smul_right, hten, hten', hT, hT', Finset.prod_mul_distrib]
        rfl
      simp only [hl, hp]
      exact integral_fintype_prod_eq_prod (μ := μ)
        (fun v s => ⟪W' v ((γ v)⁻¹ * s), y v⟫_ℂ * ⟪z v, W v s⟫_ℂ)
    · push Not at hloc
      obtain ⟨v0, h0⟩ := hloc
      rw [hzero v0 h0]
      have h0' : ¬ Integrable (fun s => ‖f v0 s‖) (μ v0) := fun h =>
        h0 ((integrable_norm_iff (hfc v0).aestronglyMeasurable).1 h)
      have hprod : ∫ x, ∏ v, ‖f v (x v)‖ ∂(Measure.pi μ) = 0 := by
        have := integral_fintype_prod_eq_prod (𝕜 := ℝ) (μ := μ) (fun v s => ‖f v s‖)
        rw [this]
        exact Finset.prod_eq_zero (Finset.mem_univ v0) (integral_undef h0')
      have hint : Integrable (fun x => ∏ v, ‖f v (x v)‖) (Measure.pi μ) := by
        have := hF.norm
        simpa only [hnorm] using this
      have h00 := (integral_eq_zero_iff_of_nonneg
        (fun x => Finset.prod_nonneg fun v _ => norm_nonneg (f v (x v))) hint).1 hprod
      have hae : F =ᵐ[Measure.pi μ] 0 := h00.mono fun x hx => by
        have h1 : ‖F x‖ = 0 := by rw [hnorm]; simpa only [Pi.zero_apply] using hx
        simpa only [Pi.zero_apply] using norm_eq_zero.1 h1
      rw [integral_congr_ae hae]
      simp
  · rw [integral_undef hF, ContinuousLinearMap.zero_apply]
    by_cases hloc : ∀ v, Integrable (f v) (μ v)
    · exfalso
      apply hF
      have hP : Integrable (fun x => ∏ v, ‖f v (x v)‖) (Measure.pi μ) :=
        Integrable.fintype_prod_dep (fun v => (hloc v).norm)
      exact hP.mono' hFc.aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hnorm x).le)
    · push Not at hloc
      obtain ⟨v0, h0⟩ := hloc
      exact (hzero v0 h0).symm

end Fact

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem OOFactor_holds {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : OOFactor X u u' := by
  intro γ y
  have h := oo_factor (fun v => Formalism.REAL.muG (X.B.I.ε v)) (X.tensU u) (X.tensU u') (X.tensU_inner u)
    (X.tensU_inner u') (X.tensU_span u) (X.Wloc u) (X.Wloc u') (X.Wloc_cont u) (X.Wloc_cont u')
    (X.Wu u) (X.Wu u') (X.Wu_spec u).2.2.1 (X.Wu_spec u').2.2.1 (X.Wu_tens u) (X.Wu_tens u') γ y
  simpa only [OOinf, Jv, TermOp.OO, Measure.restrict_univ] using h

end Formalism.L2.SG.RealObj.RankOneTensors
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfI
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cof

variable {D : D7}

theorem GZ_apply (u v : Fin (D.R.rS + 1) → (VS D).V) (a b : Fin (D.R.rS + 1)) :
    GZ u v a b = (VS D).hT (u a) (v b) := rfl

theorem GDl_top' (u v : Fin (D.R.rS + 1) → (VS D).V) : GDl u v (D.R.rS + 1) = (GZ u v).det := by
  unfold GDl
  rw [dif_pos le_rfl]
  congr 1

theorem GDl_r' (u v : Fin (D.R.rS + 1) → (VS D).V) :
    GDl u v D.R.rS = ((GZ u v).submatrix Fin.castSucc Fin.castSucc).det := by
  unfold GDl
  rw [dif_pos (Nat.le_succ _)]
  have ecs : (Fin.castLE (Nat.le_succ D.R.rS) : Fin D.R.rS → Fin (D.R.rS + 1)) = Fin.castSucc :=
    funext fun i => Fin.ext rfl
  rw [ecs]

theorem om'_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (a : Fin (D.R.rS + 1)) :
    (VS D).hT (u a) (Gom' u v) = if a = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
  have key := congrFun (congrFun (Matrix.mul_adjugate (GZ u v)) a) (Fin.last _)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
  rw [GDl_top']
  unfold Gom'
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [show (∑ b, (GZ u v).adjugate b (Fin.last _) * (VS D).hT (u a) (v b)) =
      ∑ b, GZ u v a b * (GZ u v).adjugate b (Fin.last _) from
    Finset.sum_congr rfl fun b _ => by rw [GZ_apply, mul_comm], key]
  split_ifs <;> simp

theorem om'_decomp (u v : Fin (D.R.rS + 1) → (VS D).V) :
    Gom' u v - GDl u v D.R.rS • v (Fin.last _) ∈ Xs (S := VS D) v := by
  unfold Gom'
  rw [Fin.sum_univ_castSucc, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r', add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem om_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (Gom u v) (v b) = if b = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
  have key := congrFun (congrFun (Matrix.adjugate_mul (GZ u v)) (Fin.last _)) b
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
  rw [GDl_top']
  unfold Gom
  rw [map_sum, LinearMap.sum_apply]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  rw [show (∑ a, (GZ u v).adjugate (Fin.last _) a * (VS D).hT (u a) (v b)) =
      ∑ a, (GZ u v).adjugate (Fin.last _) a * GZ u v a b from rfl, key]
  rcases eq_or_ne b (Fin.last _) with hb | hb
  · subst hb
    simp
  · rw [if_neg (Ne.symm hb), if_neg hb, smul_zero]

theorem om_decomp (u v : Fin (D.R.rS + 1) → (VS D).V) :
    Gom u v - star (GDl u v D.R.rS) • u (Fin.last _) ∈ Xs (S := VS D) u := by
  unfold Gom
  rw [Fin.sum_univ_castSucc, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r', add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem lemB (u v : Fin (D.R.rS + 1) → (VS D).V) (hdet : GDl u v (D.R.rS + 1) ≠ 0) {q : (VS D).V}
    (hq : q ∈ Submodule.span D.host.E (Set.range v)) (h : ∀ a, (VS D).hT (u a) q = 0) : q = 0 := by
  obtain ⟨π, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hq
  have hm : Matrix.mulVec (GZ u v) π = 0 := by
    funext a
    have := h a
    rw [map_sum] at this
    simp only [map_smul, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, GZ_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [GDl_top'] at hdet
  have hπ := Matrix.eq_zero_of_mulVec_eq_zero hdet hm
  simp [hπ]

theorem eq_zero_of_orth_of_det_ne_zero (u v : Fin (D.R.rS + 1) → (VS D).V) (hdet : GDl u v (D.R.rS + 1) ≠ 0) {q : (VS D).V}
    (hq : q ∈ Submodule.span D.host.E (Set.range u)) (h : ∀ b, (VS D).hT q (v b) = 0) : q = 0 := by
  obtain ⟨κ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hq
  have hm : Matrix.vecMul (fun a => star (κ a)) (GZ u v) = 0 := by
    funext b
    have := h b
    rw [map_sum, LinearMap.sum_apply] at this
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at this
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, GZ_apply]
    exact this
  rw [GDl_top'] at hdet
  have hκ := Matrix.eq_zero_of_vecMul_eq_zero hdet hm
  have : κ = 0 := by
    funext a
    have := congrFun hκ a
    simpa using this
  simp [this]

theorem lemC (v : Fin (D.R.rS + 1) → (VS D).V) (hv : LinearIndependent D.host.E v) {c : D.host.E}
    (h : c • v (Fin.last _) ∈ Xs (S := VS D) v) : c = 0 := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 h
  have h0 : ∑ i, (Fin.snoc (α := fun _ => D.host.E) d (-c) i) • v i = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, neg_smul]
    rw [hd, add_neg_cancel]
  have := Fintype.linearIndependent_iff.1 hv _ h0 (Fin.last _)
  simpa using this

end Cof

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepIntOf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.WuDecay Formalism.L2.SG.WuDecayPf
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal Classical
open Matrix

namespace Formalism.L2.SG.RealObj.StepIntOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D)

def CoefDec (a : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ v (g : Formalism.REAL.UJ (X.B.I.ε v)), ‖coefV X v g‖ ≤ K * opn (uMat g) ^ (-a)

def MDec (a : ℝ) : Prop :=
  ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ g : X.B.I.Ginf, ‖mX X g‖ₑ ≤ K * ENNReal.ofReal (normInf X g ^ (-a))

def GrowthG (A : ℝ) : Prop :=
  ∫⁻ x, ENNReal.ofReal (normInf X x ^ (-A)) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤

def GrowthS (u : D.what₂.Word) (B : ℝ) : Prop :=
  ∫⁻ s, ENNReal.ofReal (normInf X s ^ (-B)) ∂(muS X u) < ⊤

def PropP (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (M : ℝ) : Prop :=
  ∃ CP : ℝ, 1 ≤ CP ∧ ∀ s ∈ X.SinfU u, ∀ s' ∈ X.SinfU u',
    max (normInf X s) (normInf X s') ≤ CP * normInf X (s * γ * s'⁻¹) ^ M

def LaFin (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (b : ℝ) : Prop :=
  ∫⁻ s, ∫⁻ s', ENNReal.ofReal (normInf X (s * γ * s'⁻¹) ^ (-b)) ∂(muS X u') ∂(muS X u) < ⊤

def NormInv : Prop := ∀ g : X.B.I.Ginf, normInf X g⁻¹ = normInf X g

def RealInputs : Prop :=
  ∃ a b M : ℝ, 0 ≤ b ∧ b ≤ a ∧ 0 < M ∧ CoefDec X a ∧ GrowthG X (a - b) ∧
    (∀ u, GrowthS X u (b / (2 * M))) ∧
    ∀ (u u' : D.what₂.Word) (sc : ℝ), ∀ c ∈ Formalism.L2.SG.RealObj.Good X u u', ∀ γ,
      Formalism.L2.SG.RealObj.HasDiag X u u' sc c γ → PropP X u u' γ M

end Defs

def StIntOfLint : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf),
    ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ →
      Formalism.L2.SG.TermOp.OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Set.univ (X.Wu u) (X.Wu u') γ

def StMDec : Prop := ∀ (D : D7) (X : HidaSetting D) (a : ℝ), CoefDec X a → MDec X a

def StLa : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (M b : ℝ), 0 < M → 0 ≤ b →
    (∀ g, 1 ≤ normInf X g) → PropP X u u' γ M → GrowthS X u (b / (2 * M)) → GrowthS X u' (b / (2 * M)) →
      LaFin X u u' γ b

def StTheta : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (a b : ℝ),
    (∀ g, 1 ≤ normInf X g) → NormInv X → 0 ≤ b → b ≤ a → WuDom X u → WuDom X u' → MDec X a →
      GrowthG X (a - b) → LaFin X u u' γ b →
        ∫⁻ x, ‖X.Wu u x‖ₑ * ‖X.Wu u' (γ⁻¹ * x)‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤

def StNormOne : Prop := ∀ (D : D7) (X : HidaSetting D), 0 < X.B.I.n → ∀ g, 1 ≤ normInf X g

def StNormInv : Prop := ∀ (D : D7) (X : HidaSetting D), NormInv X

end Formalism.L2.SG.RealObj.StepIntOf

namespace Formalism.L2.SG.RealObj.StepIntOf.Steps

open Formalism.L2.SG.RealObj.StepIntOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem norm_rank_one_le {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (v : V) (w : V') :
    ‖Formalism.L2.SG.TermOp.rk1 v w‖ ≤ ‖v‖ * ‖w‖ := by
  unfold Formalism.L2.SG.TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem stIntOfLint : StIntOfLint := by
  intro D X u u' γ hfin
  unfold Formalism.L2.SG.TermOp.OOInt
  rw [integrableOn_univ]
  have hW : Continuous (X.Wu u) := (X.Wu_spec u).2.2.1
  have hW' : Continuous (X.Wu u') := (X.Wu_spec u').2.2.1
  have hW'' : Continuous fun x : X.B.I.Ginf => X.Wu u' (γ⁻¹ * x) := hW'.comp (continuous_const.mul continuous_id)
  have hc : Continuous fun x : X.B.I.Ginf => Formalism.L2.SG.TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x)) := by
    rw [continuous_clm_apply]
    intro ξ
    simp only [Formalism.L2.SG.TermOp.rankOneInnerOperator_apply]
    exact (hW''.inner continuous_const).smul hW
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin
  simp only []
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_rank_one_le _ _)

end Formalism.L2.SG.RealObj.StepIntOf.Steps

namespace Formalism.L2.SG.RealObj.StepIntOf.Theta

open Formalism.L2.SG.RealObj.StepIntOf

section

variable {D : D7} (X : HidaSetting D)

end

end Formalism.L2.SG.RealObj.StepIntOf.Theta

namespace Formalism.L2.SG.RealObj.StepIntOf

end Formalism.L2.SG.RealObj.StepIntOf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TraceEqSumPlaces
section
noncomputable section

open NumberField
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def embOf (φ : InfinitePlace F → (E →+* ℂ)) (p : InfinitePlace F × Bool) : E →+* ℂ :=
  if p.2 then (starRingEnd ℂ).comp (φ p.1) else φ p.1

theorem embOf_injective [IsTotallyReal F] [IsTotallyComplex E] (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) : Function.Injective (embOf φ) := by
  have hre : ∀ (v : InfinitePlace F) (a : F), starRingEnd ℂ (v.embedding a) = v.embedding a := by
    intro v a
    have h := ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal v))
    exact RingHom.congr_fun h a
  have hres : ∀ p : InfinitePlace F × Bool, (embOf φ p).comp (algebraMap F E) = p.1.embedding := by
    rintro ⟨v, b⟩
    ext a
    cases b <;> simp [embOf, hφ, hre]
  have hnr : ∀ v, (starRingEnd ℂ).comp (φ v) ≠ φ v := by
    intro v h
    have hc := IsTotallyComplex.isComplex (InfinitePlace.mk (φ v))
    rw [InfinitePlace.isComplex_mk_iff, ComplexEmbedding.isReal_iff] at hc
    exact hc (RingHom.ext fun x => RingHom.congr_fun h x)
  rintro ⟨v, b⟩ ⟨v', b'⟩ h
  have hv : v = v' := by
    have := congrArg (fun σ => σ.comp (algebraMap F E)) h
    simp only [hres] at this
    rw [← InfinitePlace.mk_embedding v, ← InfinitePlace.mk_embedding v', this]
  subst hv
  cases b <;> cases b' <;> simp [embOf] at h ⊢
  · exact hnr v h.symm
  · exact hnr v h

theorem embOf_bijective [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2)
    (φ : InfinitePlace F → (E →+* ℂ)) (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) :
    Function.Bijective (embOf φ) := by
  classical
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨embOf_injective φ hφ, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bool, Embeddings.card E ℂ,
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
    ← Module.finrank_mul_finrank ℚ F E, h2]
  have h := InfinitePlace.card_add_two_mul_card_eq_rank F
  rw [IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h
  rw [h]

theorem trace_eq_sum_places [IsTotallyReal F] [IsTotallyComplex E] (h2 : Module.finrank F E = 2)
    (φ : InfinitePlace F → (E →+* ℂ)) (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ v, (φ v x + starRingEnd ℂ (φ v x)) := by
  classical
  have h1 : algebraMap ℚ ℂ (Algebra.trace ℚ E x) = ∑ τ : E →ₐ[ℚ] ℂ, τ x := trace_eq_sum_embeddings ℂ
  have h3 : ∑ σ : E →+* ℂ, σ x = ∑ τ : E →ₐ[ℚ] ℂ, τ x :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun τ => τ x)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])
  have h4 : ∑ p : InfinitePlace F × Bool, embOf φ p x = ∑ σ : E →+* ℂ, σ x :=
    (embOf_bijective h2 φ hφ).sum_comp (fun σ => σ x)
  rw [show ((Algebra.trace ℚ E x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E x) from rfl, h1, ← h3, ← h4,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fintype.sum_bool]
  simp [embOf, add_comm]

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem TraceSum_holds : Formalism.L2.SG.RealObj.RootCoordinateFrames.TraceSum := by
  intro D X g x
  have : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  have : IsTotallyComplex X.B.I.E := X.B.I.cm.cmUnram.1
  have htr : ((Algebra.trace ℚ D.host.E (X.ιE x) : ℚ) : ℂ) = ((Algebra.trace ℚ X.B.I.E x : ℚ) : ℂ) := by
    rw [show X.ιE x = X.ιE.toRatAlgEquiv x from rfl, Algebra.trace_eq_of_algEquiv]
  unfold Formalism.L2.SG.PairVal.psiInf
  rw [htr, trace_eq_sum_places X.B.I.cm.deg2 X.B.I.φ X.B.I.φ_over x, ← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_div]
  rfl

end Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums
end
end

