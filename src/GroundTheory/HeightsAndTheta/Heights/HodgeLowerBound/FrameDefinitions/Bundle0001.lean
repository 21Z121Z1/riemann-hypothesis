import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.EqZeroOfIsIsoSub
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Lattice

variable {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂]

def IsIsoSub (form : abelian₂ →ₗ[ℤ] abelian₂ →ₗ[ℤ] ℤ) (I : Submodule O abelian₂) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, form v w = 0

def IsSaturated (I : Submodule O abelian₂) : Prop :=
  ∀ (v : abelian₂) (n : ℤ), n ≠ 0 → n • v ∈ I → v ∈ I

def IsNzFamily (I : Submodule O abelian₂) (ρ : ℕ) (v : Fin ρ → abelian₂) : Prop :=
  1 ≤ ρ ∧ (∀ a, v a ∈ I) ∧ LinearIndependent O v ∧
    (Submodule.span O (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup ≠ 0

end Lattice

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

structure CuspData (D : ComponentData II Ψ K ι Ω E) (O : Type) [CommRing O] (abelian₂ : Type)
    [AddCommGroup abelian₂] [Module O abelian₂] where

  rank : ℕ
  basis : Module.Basis (Fin rank) ℤ abelian₂

  form : abelian₂ →ₗ[ℤ] abelian₂ →ₗ[ℤ] ℤ
  alt : ∀ v, form v v = 0
  unimod : IsUnit (Matrix.of fun a b => form (basis a) (basis b)).det

  emb : Ψ → O →+* ℂ

  normSq : ((Σ k, ι k) → ℂ) → abelian₂ → ℝ
  normSq_pos : ∀ z ∈ D.Xo, ∀ v, v ≠ 0 → 0 < normSq z v
  form_le : ∀ z ∈ D.Xo, ∀ v w, ((form v w : ℤ) : ℝ) ^ 2 ≤ normSq z v * normSq z w

  lie : ((Σ k, ι k) → ℂ) → Ψ → abelian₂ → Fin (D.N - D.j) → ℂ
  lie_add : ∀ z τ v w, lie z τ (v + w) = lie z τ v + lie z τ w
  lie_smul : ∀ z τ (a : O) v, lie z τ (a • v) = emb τ a • lie z τ v
  lie_le : ∀ z ∈ D.Xo, ∀ v, ∑ τ, ∑ c, ‖lie z τ v c‖ ^ 2 ≤ normSq z v
  inj : ∀ z ∈ D.Xo, ∀ τ (I : Submodule O abelian₂), IsIsoSub form I → ∀ (ρ : ℕ) (v : Fin ρ → abelian₂),
    (∀ a, v a ∈ I) → LinearIndependent O v → LinearIndependent ℂ fun a => lie z τ (v a)
  torus : ∀ z ∈ D.Xo, ∀ c : K → ℂ, (∀ k, c k ≠ 0) →
    normSq (torusSmul c z) = normSq z ∧ lie (torusSmul c z) = lie z

namespace CuspData

variable {D : ComponentData II Ψ K ι Ω E} {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂]
  (Cd : CuspData D O abelian₂)

def gramLie (z : (Σ k, ι k) → ℂ) (τ : Ψ) {ρ : ℕ} (v : Fin ρ → abelian₂) : Matrix (Fin ρ) (Fin ρ) ℂ :=
  Matrix.of fun a b => ∑ c, starRingEnd ℂ (Cd.lie z τ (v a) c) * Cd.lie z τ (v b) c

open Classical in

def Nz (z : (Σ k, ι k) → ℂ) (I : Submodule O abelian₂) : ℝ :=
  if h : ∃ ρ v, IsNzFamily I ρ v then
    (∏ τ, (Cd.gramLie z τ h.choose_spec.choose).det.re) /
      ((Submodule.span O (Set.range h.choose_spec.choose)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ)
  else 1

def cuspWeight (z : (Σ k, ι k) → ℂ) : ℝ :=
  max 0 (sSup {x | ∃ I : Submodule O abelian₂, I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub Cd.form I ∧
    x = -Real.log (Cd.Nz z I)})

end CuspData

namespace Line

open GaussianInt

def gaussEquiv : GaussianInt ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun v := ![v.re, v.im]
  invFun f := ⟨f 0, f 1⟩
  map_add' v w := by ext i; fin_cases i <;> simp
  map_smul' n v := by
    ext i; fin_cases i <;> simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]
  left_inv v := by simp
  right_inv f := by ext i; fin_cases i <;> simp

def gaussBasis : Module.Basis (Fin 2) ℤ GaussianInt := Module.Basis.ofEquivFun gaussEquiv

theorem gaussBasis_zero : gaussBasis 0 = ⟨1, 0⟩ := by
  simp [gaussBasis, gaussEquiv, Module.Basis.coe_ofEquivFun]

theorem gaussBasis_one : gaussBasis 1 = ⟨0, 1⟩ := by
  simp [gaussBasis, gaussEquiv, Module.Basis.coe_ofEquivFun]

def gaussForm : GaussianInt →ₗ[ℤ] GaussianInt →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun v w => v.re * w.im - v.im * w.re)
    (fun v v' w => by simp; ring) (fun n v w => by simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)
    (fun v w w' => by simp; ring) (fun n v w => by simp [zsmul_eq_mul, Zsqrtd.re_mul, Zsqrtd.im_mul]; ring)

theorem gaussForm_apply (v w : GaussianInt) : gaussForm v w = v.re * w.im - v.im * w.re := rfl

theorem normSq_toComplex (v : GaussianInt) : Complex.normSq (toComplex v) = (v.re : ℝ) ^ 2 + (v.im : ℝ) ^ 2 := by
  rw [toComplex_def₂, Complex.normSq_mk]
  ring

theorem eq_zero_of_isIsoSub {I : Submodule GaussianInt GaussianInt} (hI : IsIsoSub gaussForm I) {v : GaussianInt}
    (hv : v ∈ I) : v = 0 := by
  have h := hI v hv (⟨0, 1⟩ • v) (I.smul_mem _ hv)
  rw [gaussForm_apply, smul_eq_mul] at h
  simp [Zsqrtd.re_mul, Zsqrtd.im_mul] at h
  have h2 : v.re * v.re + v.im * v.im = 0 := by linarith
  have hre : v.re = 0 := by nlinarith [mul_self_nonneg v.re, mul_self_nonneg v.im]
  have him : v.im = 0 := by nlinarith [mul_self_nonneg v.re, mul_self_nonneg v.im]
  exact Zsqrtd.ext hre him

def gaussCusp (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2]) :
    CuspData (lineData II hII) GaussianInt GaussianInt where
  rank := 2
  basis := gaussBasis
  form := gaussForm
  alt v := by rw [gaussForm_apply]; ring
  unimod := by
    have : (Matrix.of fun a b => gaussForm (gaussBasis a) (gaussBasis b)).det = 1 := by
      rw [Matrix.det_fin_two]
      simp [gaussForm_apply, gaussBasis_zero, gaussBasis_one]
    rw [this]
    exact isUnit_one
  emb _ := toComplex
  normSq _ v := Complex.normSq (toComplex v)
  normSq_pos _ _ v hv := Complex.normSq_pos.2 fun h => hv (toComplex_injective (by rw [h, map_zero]))
  form_le _ _ v w := by
    rw [gaussForm_apply, normSq_toComplex, normSq_toComplex]
    push_cast
    nlinarith [sq_nonneg ((v.re : ℝ) * w.re + v.im * w.im)]
  lie _ _ v _ := toComplex v
  lie_add _ _ v w := by funext c; simp
  lie_smul _ _ a v := by funext c; simp [smul_eq_mul]
  lie_le _ _ v := by
    simp only [Finset.univ_unique, Finset.sum_singleton, Complex.sq_norm]
    show ∑ _c : Fin 1, Complex.normSq (toComplex v) ≤ Complex.normSq (toComplex v)
    simp
  inj _ _ _ I hI ρ v hv hli := by
    rcases Nat.eq_zero_or_pos ρ with rfl | hρ
    · exact linearIndependent_empty_type
    · exact absurd (eq_zero_of_isIsoSub hI (hv ⟨0, hρ⟩)) (hli.ne_zero ⟨0, hρ⟩)
  torus _ _ _ _ := ⟨rfl, rfl⟩

theorem cuspWeight_gauss (II : IntersectionSystem) (hII) (z : (Σ _ : Unit, Fin 2) → ℂ) :
    (gaussCusp II hII).cuspWeight z = 0 := by
  have : {x | ∃ I : Submodule GaussianInt GaussianInt, I ≠ ⊥ ∧ IsSaturated I ∧
      IsIsoSub (gaussCusp II hII).form I ∧ x = -Real.log ((gaussCusp II hII).Nz z I)} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro I hI _ hiso _
    exact hI ((Submodule.eq_bot_iff I).2 fun v hv => eq_zero_of_isIsoSub hiso hv)
  rw [CuspData.cuspWeight, this, Real.sSup_empty, max_self]

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Values

variable {Ω : Type} [Field Ω]

omit [Fintype K] in
theorem isValueAt_add {y : (Σ k, ι k) → Ω} {s t : Ω} {z : (Σ k, ι k) → ℂ} {v w : ℂ}
    (hv : IsValueAt y s z v) (hw : IsValueAt y t z w) : IsValueAt y (s + t) z (v + w) := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  obtain ⟨d', g', h', hg', hh', hy', heq', hz0', rfl⟩ := hw
  refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_,
    isMultiHomog_mul hh hh', ?_, ?_, ?_, ?_⟩
  · rw [add_comm d d']; exact isMultiHomog_mul hg' hh
  · rw [map_mul]; exact mul_ne_zero hy hy'
  · rw [map_add, map_mul, map_mul, map_mul, heq, heq']; ring
  · rw [map_mul, map_mul]; exact mul_ne_zero hz0 hz0'
  · simp only [map_add, map_mul]
    field_simp

theorem isValueAt_intCast (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (n : ℤ) :
    IsValueAt y (n : Ω) z (n : ℂ) :=
  ⟨0, C n, 1, isMultiHomog_C_zero n, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

theorem isValueAt_inv {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ}
    (hv : IsValueAt y s z v) (hs : s ≠ 0) (hv0 : v ≠ 0) : IsValueAt y s⁻¹ z v⁻¹ := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  have hgy : aeval y g ≠ 0 := by rw [heq]; exact mul_ne_zero hs hy
  have hgz : eval z (map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hv0; exact hv0 rfl
  refine ⟨d, h, g, hh, hg, hgy, ?_, hgz, by rw [inv_div]⟩
  rw [heq]
  field_simp

theorem isValueAt_pow {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} {v : ℂ}
    (hv : IsValueAt y s z v) (n : ℕ) : IsValueAt y (s ^ n) z (v ^ n) := by
  induction n with
  | zero => simpa using isValueAt_one_self y z
  | succ n ih => rw [pow_succ, pow_succ]; exact isValueAt_mul ih hv

theorem isMultiHomog_X_single [DecidableEq K] (p : Σ k, ι k) :
    IsMultiHomog (X p : MRing ι) (fun k => if k = p.1 then 1 else 0) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨a, i₀⟩ := p
  show ∑ i, (Finsupp.single (⟨a, i₀⟩ : Σ k, ι k) 1 : (Σ k, ι k) →₀ ℕ) ⟨k, i⟩ = if k = a then 1 else 0
  by_cases hk : k = a
  · subst hk
    rw [if_pos rfl, Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      classical
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hi (eq_of_heq (Sigma.mk.inj_iff.mp h).2).symm
    · simp
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun i _ => ?_
    classical
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm

theorem isMultiHomog_prod_X (c : (k : K) → ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι)) (fun _ => 1) := by
  classical
  have key : ∀ s : Finset K,
      IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι)) (fun k => if k ∈ s then 1 else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.notMem_empty, if_false]
      exact isMultiHomog_one
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      convert isMultiHomog_mul (isMultiHomog_X_single (ι := ι) ⟨a, c a⟩) ih using 1
      funext k
      by_cases hk : k = a
      · subst hk; simp [ha]
      · simp [hk]
  simpa using key Finset.univ

theorem exists_isValueAt_of_mem_chartRing {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k}
    {z : (Σ k, ι k) → ℂ} (hyc : segreCoord y c ≠ 0) (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) {r : Ω}
    (hr : r ∈ chartRing ℤ (segreCoord y) c) : ∃ v, IsValueAt y r z v := by
  classical
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨c', rfl⟩ := hx
    refine ⟨(∏ k, z ⟨k, c' k⟩) / ∏ k, z ⟨k, c k⟩, fun _ => 1, ∏ k, X ⟨k, c' k⟩, ∏ k, X ⟨k, c k⟩,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact isMultiHomog_prod_X c'
    · exact isMultiHomog_prod_X c
    · simpa [segreCoord] using hyc
    · simp only [map_prod, aeval_X]
      exact (div_mul_cancel₀ _ hyc).symm
    · simp only [map_prod, map_X, eval_X]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hz k
    · simp [map_prod]
  | algebraMap n => exact ⟨n, by simpa using isValueAt_intCast y z n⟩
  | add a b _ _ ha hb =>
    obtain ⟨v, hv⟩ := ha
    obtain ⟨w, hw⟩ := hb
    exact ⟨v + w, isValueAt_add hv hw⟩
  | mul a b _ _ ha hb =>
    obtain ⟨v, hv⟩ := ha
    obtain ⟨w, hw⟩ := hb
    exact ⟨v * w, isValueAt_mul hv hw⟩

theorem exists_isValueAt_of_pow_mul_mem {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k}
    {z : (Σ k, ι k) → ℂ} (hzP : z ∈ mcPts (mCoordIdeal y)) (hyc : segreCoord y c ≠ 0)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) {f r : Ω} (hf : IsUnitAt y f z) {n : ℕ}
    (hr : f ^ n * r ∈ chartRing ℤ (segreCoord y) c) : ∃ v, IsValueAt y r z v := by
  obtain ⟨w, hw⟩ := exists_isValueAt_of_mem_chartRing hyc hz hr
  obtain ⟨a, ha, ha0⟩ := hf
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact ha0 (isValueAt_zero hzP ha)
  have hinv := isValueAt_pow (isValueAt_inv ha hf0 ha0) n
  refine ⟨w * a⁻¹ ^ n, ?_⟩
  have := isValueAt_mul hw hinv
  rwa [mul_comm (f ^ n) r, mul_assoc, ← mul_pow, mul_inv_cancel₀ hf0, one_pow, mul_one] at this

end Values

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

