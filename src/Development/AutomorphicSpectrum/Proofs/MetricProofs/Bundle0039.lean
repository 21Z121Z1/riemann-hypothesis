import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0019
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0001
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ComplexHessianTwoPointCombination
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN

noncomputable section

def selL {D E : ℕ} (σ : Fin E → Fin D) : (Fin D → ℂ) →L[ℂ] (Fin E → ℂ) :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (σ a)

theorem selL_apply {D E : ℕ} (σ : Fin E → Fin D) (z : Fin D → ℂ) (a : Fin E) :
    selL σ z a = z (σ a) := rfl

theorem jacC_selL {D E : ℕ} (σ : Fin E → Fin D) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.A.jacC (selL σ) z = Matrix.of fun a k => if σ a = k then (1 : ℂ) else 0 := by
  ext a k
  simp [ReciprocityTheory.AnForm.A.jacC, ContinuousLinearMap.fderiv, selL_apply, Pi.single_apply]

theorem hessC_selL_apply {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (i j : Fin D) :
    hessC (φ ∘ selL σ) z i j = ∑ b, (∑ a, (if σ a = i then (1 : ℂ) else 0) *
      hessC φ (selL σ z) a b) * (if σ b = j then (1 : ℂ) else 0) := by
  rw [ReciprocityTheory.AnForm.A.hessC_comp φ (selL σ) z ((selL σ).analyticAt z) hφ, jacC_selL]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  split_ifs <;> simp

theorem hessC_selL_inj {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) {σ : Fin E → Fin D}
    (hσ : Function.Injective σ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (a b : Fin E) :
    hessC (φ ∘ selL σ) z (σ a) (σ b) = hessC φ (selL σ z) a b := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hσ.eq_iff]

theorem hessC_selL_left {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) {i : Fin D} (hi : ∀ a, σ a ≠ i) (j : Fin D) :
    hessC (φ ∘ selL σ) z i j = 0 := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hi]

theorem hessC_selL_right {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) (i : Fin D) {j : Fin D} (hj : ∀ a, σ a ≠ j) :
    hessC (φ ∘ selL σ) z i j = 0 := by
  rw [hessC_selL_apply φ σ z hφ]
  simp [hj]

theorem contDiffAt_comp_selL {D E : ℕ} (φ : (Fin E → ℂ) → ℝ) (σ : Fin E → Fin D) (z : Fin D → ℂ)
    (hφ : ContDiffAt ℝ 2 φ (selL σ z)) : ContDiffAt ℝ 2 (φ ∘ selL σ) z :=
  ContDiffAt.comp z hφ ((selL σ).restrictScalars ℝ).contDiff.contDiffAt

def selA {d : ℕ} (c : Fin (d + 2)) : Fin (d + 1) → Fin (d + 2) :=
  Fin.cons c fun i : Fin d => i.succ.succ

def selT {d : ℕ} : Fin d → Fin (d + 2) := fun i => i.succ.succ

theorem selT_injective {d : ℕ} : Function.Injective (selT (d := d)) := fun a b h =>
  Fin.succ_injective _ (Fin.succ_injective _ h)

theorem selA_injective {d : ℕ} {c : Fin (d + 2)} (hc : ∀ i : Fin d, i.succ.succ ≠ c) :
    Function.Injective (selA c) := by
  intro a b h
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => rfl
    | succ b => exact absurd h.symm (by simpa [selA] using hc b)
  | succ a =>
    induction b using Fin.cases with
    | zero => exact absurd h (by simpa [selA] using hc a)
    | succ b =>
      have : a.succ.succ = b.succ.succ := by simpa [selA] using h
      rw [Fin.succ_injective _ (Fin.succ_injective _ this)]

theorem selA_eq_cons {d : ℕ} (c : Fin (d + 2)) (z : Fin (d + 2) → ℂ) :
    selL (selA c) z = Fin.cons (z c) (Fin.tail (Fin.tail z)) := by
  funext a
  induction a using Fin.cases with
  | zero => simp [selL_apply, selA]
  | succ a => simp [selL_apply, selA, Fin.tail]

theorem selT_eq_tail {d : ℕ} (z : Fin (d + 2) → ℂ) :
    selL selT z = Fin.tail (Fin.tail z) := rfl

theorem blk_zero_zero {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) : blk e B 0 0 = e := rfl

theorem blk_zero_succ {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (q : Fin d) :
    blk e B 0 q.succ = 0 := rfl

theorem blk_succ_zero {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (p : Fin d) :
    blk e B p.succ 0 = 0 := rfl

theorem blk_succ_succ {d : ℕ} (e : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (p q : Fin d) :
    blk e B p.succ q.succ = B p q := rfl

theorem blk_assemble {d : ℕ} (T₀ T₁ T₂ : Matrix (Fin (d + 2)) (Fin (d + 2)) ℂ) (e₀ e₁ s t v : ℂ)
    (B₀ B₁ C : Matrix (Fin d) (Fin d) ℂ)
    (a₀ : ∀ a b, T₀ (selA 0 a) (selA 0 b) = blk e₀ B₀ a b)
    (l₀ : ∀ j, T₀ (Fin.succ 0) j = 0) (r₀ : ∀ i, T₀ i (Fin.succ 0) = 0)
    (a₁ : ∀ a b, T₁ (selA (Fin.succ 0) a) (selA (Fin.succ 0) b) = blk e₁ B₁ a b)
    (l₁ : ∀ j, T₁ 0 j = 0) (r₁ : ∀ i, T₁ i 0 = 0)
    (a₂ : ∀ a b, T₂ (selT a) (selT b) = C a b)
    (l₂ : ∀ j, T₂ 0 j = 0) (r₂ : ∀ i, T₂ i 0 = 0)
    (l₂' : ∀ j, T₂ (Fin.succ 0) j = 0) (r₂' : ∀ i, T₂ i (Fin.succ 0) = 0) :
    s • T₀ + t • T₁ + v • T₂ = blk (s * e₀) (blk (t * e₁) (s • B₀ + t • B₁ + v • C)) := by
  have p00 : T₀ 0 0 = e₀ := a₀ 0 0
  have p0k : ∀ k : Fin d, T₀ 0 k.succ.succ = 0 := fun k => a₀ 0 k.succ
  have pk0 : ∀ k : Fin d, T₀ k.succ.succ 0 = 0 := fun k => a₀ k.succ 0
  have pkl : ∀ k l : Fin d, T₀ k.succ.succ l.succ.succ = B₀ k l := fun k l => a₀ k.succ l.succ
  have q11 : T₁ (Fin.succ 0) (Fin.succ 0) = e₁ := a₁ 0 0
  have q1k : ∀ k : Fin d, T₁ (Fin.succ 0) k.succ.succ = 0 := fun k => a₁ 0 k.succ
  have qk1 : ∀ k : Fin d, T₁ k.succ.succ (Fin.succ 0) = 0 := fun k => a₁ k.succ 0
  have qkl : ∀ k l : Fin d, T₁ k.succ.succ l.succ.succ = B₁ k l := fun k l => a₁ k.succ l.succ
  have wkl : ∀ k l : Fin d, T₂ k.succ.succ l.succ.succ = C k l := fun k l => a₂ k l
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp only [p00, l₁, l₂, blk_zero_zero, mul_zero, add_zero]
    | succ j =>
      induction j using Fin.cases with
      | zero => simp only [r₀, l₁, l₂, blk_zero_succ, mul_zero, add_zero]
      | succ k => simp only [p0k, l₁, l₂, blk_zero_succ, mul_zero, add_zero]
  | succ i =>
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp only [l₀, r₁, l₂', blk_succ_zero, mul_zero, add_zero]
      | succ j =>
        induction j using Fin.cases with
        | zero => simp only [l₀, q11, l₂', blk_succ_succ, blk_zero_zero, mul_zero, add_zero, zero_add]
        | succ k => simp only [l₀, q1k, l₂', blk_succ_succ, blk_zero_succ, mul_zero, add_zero]
    | succ k =>
      induction j using Fin.cases with
      | zero => simp only [pk0, r₁, r₂, blk_succ_zero, mul_zero, add_zero]
      | succ j =>
        induction j using Fin.cases with
        | zero => simp only [r₀, qk1, r₂', blk_succ_succ, blk_succ_zero, mul_zero, add_zero]
        | succ l =>
          simp only [pkl, qkl, wkl, blk_succ_succ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem hessC_row_square : ∀ (d : ℕ) (f : (Fin (d + 1) → ℂ) → ℝ) (α : (Fin d → ℂ) → ℝ) (y : Fin d → ℂ) (p₀ p₁ e₀ e₁ : ℂ)
    (B₀ B₁ : Matrix (Fin d) (Fin d) ℂ) (s t v : ℝ),
    ContDiffAt ℝ 2 f (Fin.cons p₀ y) → ContDiffAt ℝ 2 f (Fin.cons p₁ y) → ContDiffAt ℝ 2 α y →
    hessC f (Fin.cons p₀ y) = blk e₀ B₀ → hessC f (Fin.cons p₁ y) = blk e₁ B₁ →
    hessC (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z)))
      (Fin.cons p₀ (Fin.cons p₁ y)) =
    blk ((s : ℂ) * e₀) (blk ((t : ℂ) * e₁) ((s : ℂ) • B₀ + (t : ℂ) • B₁ + (v : ℂ) • hessC α y)) := by
  intro d f α y p₀ p₁ e₀ e₁ B₀ B₁ s t v hf₀ hf₁ hα h₀ h₁
  have ho : (Fin.succ 0 : Fin (d + 2)) = 1 := by simp
  have hinj₀ : Function.Injective (selA (0 : Fin (d + 2))) :=
    selA_injective fun i => Fin.succ_ne_zero _
  have hinj₁ : Function.Injective (selA (Fin.succ 0 : Fin (d + 2))) :=
    selA_injective fun i h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  have q₀ : selL (selA 0) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) = Fin.cons p₀ y := by
    rw [selA_eq_cons]; simp [Fin.tail_cons]
  have q₁ : selL (selA (Fin.succ 0)) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) =
      Fin.cons p₁ y := by
    rw [selA_eq_cons]; simp [Fin.tail_cons]
  have q₂ : selL selT (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ) = y := by
    rw [selT_eq_tail]; simp [Fin.tail_cons]
  have g₀ : ContDiffAt ℝ 2 f (selL (selA 0) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by
    rwa [q₀]
  have g₁ : ContDiffAt ℝ 2 f
      (selL (selA (Fin.succ 0)) (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by rwa [q₁]
  have g₂ : ContDiffAt ℝ 2 α (selL selT (Fin.cons p₀ (Fin.cons p₁ y) : Fin (d + 2) → ℂ)) := by
    rwa [q₂]
  have c₀ := contDiffAt_comp_selL f _ _ g₀
  have c₁ := contDiffAt_comp_selL f _ _ g₁
  have c₂ := contDiffAt_comp_selL α _ _ g₂
  have E : (fun z : Fin (d + 2) → ℂ => s * f (Fin.cons (z 0) (Fin.tail (Fin.tail z))) +
        t * f (Fin.cons (z 1) (Fin.tail (Fin.tail z))) + v * α (Fin.tail (Fin.tail z))) =
      fun z => (fun z => (fun z => s * (f ∘ selL (selA 0)) z) z +
        (fun z => t * (f ∘ selL (selA (Fin.succ 0))) z) z) z +
        (fun z => v * (α ∘ selL selT) z) z := by
    funext z
    simp only [Function.comp, selA_eq_cons, selT_eq_tail, ho]
  rw [E, hessC_add' _ _ _ ((contDiffAt_const.mul c₀).add (contDiffAt_const.mul c₁))
      (contDiffAt_const.mul c₂),
    hessC_add' _ _ _ (contDiffAt_const.mul c₀) (contDiffAt_const.mul c₁),
    hessC_const_mul', hessC_const_mul', hessC_const_mul']
  refine blk_assemble _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b; rw [hessC_selL_inj f hinj₀ _ g₀, q₀, h₀]
  · intro j
    refine hessC_selL_left f _ _ g₀ ?_ j
    intro a
    induction a using Fin.cases with
    | zero => exact (Fin.succ_ne_zero _).symm
    | succ a => exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  · intro i
    refine hessC_selL_right f _ _ g₀ i ?_
    intro a
    induction a using Fin.cases with
    | zero => exact (Fin.succ_ne_zero _).symm
    | succ a => exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  · intro a b; rw [hessC_selL_inj f hinj₁ _ g₁, q₁, h₁]
  · intro j
    refine hessC_selL_left f _ _ g₁ ?_ j
    intro a
    induction a using Fin.cases with
    | zero => exact Fin.succ_ne_zero (0 : Fin (d + 1))
    | succ a => exact Fin.succ_ne_zero (Fin.succ a)
  · intro i
    refine hessC_selL_right f _ _ g₁ i ?_
    intro a
    induction a using Fin.cases with
    | zero => exact Fin.succ_ne_zero (0 : Fin (d + 1))
    | succ a => exact Fin.succ_ne_zero (Fin.succ a)
  · intro a b; rw [hessC_selL_inj α selT_injective _ g₂, q₂]
  · intro j; exact hessC_selL_left α _ _ g₂ (fun a => Fin.succ_ne_zero _) j
  · intro i; exact hessC_selL_right α _ _ g₂ i (fun a => Fin.succ_ne_zero _)
  · intro j
    exact hessC_selL_left α _ _ g₂ (fun a h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)) j
  · intro i
    exact hessC_selL_right α _ _ g₂ i (fun a h => Fin.succ_ne_zero _ (Fin.succ_injective _ h))

end

end GlobalTheory.CompanionTheory.Ar.PB.FibN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousCuspNormFamily
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NzCont

section Emb

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)

def charVec (a : 𝓞 E) : (E →+* ℂ) → ℂ := fun s => s (algebraMap (𝓞 E) E a)

def toChar (s : E →+* ℂ) : 𝓞 E →* ℂ := (s.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ)

theorem toChar_injective : Function.Injective (toChar (E := E)) := by
  intro s s' h
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  exact DFunLike.congr_fun h a

theorem span_charVec : Submodule.span ℂ (Set.range (charVec (E := E))) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ (toChar_injective (E := E))
  rw [Fintype.linearIndependent_iff] at li
  have hl := li (fun s => f fun j => if s = j then 1 else 0) (by
    funext a
    have h1 : f (charVec a) = 0 := hf (Submodule.subset_span ⟨a, rfl⟩)
    rw [LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, smul_eq_mul, Pi.zero_apply]
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_mul]
    exact mul_comm (_ : ℂ) _)
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ f v, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun s _ => (congrArg (v s • ·) (hl s)).trans (smul_zero _)

open Classical in

theorem exists_coeff (s : E →+* ℂ) : ∃ c : 𝓞 E →₀ ℂ, ∀ s' : E →+* ℂ,
    ∑ a ∈ c.support, c a * s' (algebraMap (𝓞 E) E a) = if s' = s then 1 else 0 := by
  have h : (Pi.single s 1 : (E →+* ℂ) → ℂ) ∈ Submodule.span ℂ (Set.range (charVec (E := E))) := by
    rw [span_charVec]
    trivial
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h
  refine ⟨c, fun s' => ?_⟩
  have h2 := congrFun hc s'
  simpa [Finsupp.sum, Finset.sum_apply, charVec, Pi.single_apply] using h2

end Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem mem_eigSp_iff (R : RiemLat E g Λ) {s : 𝓞 E →+* ℂ} {x : Fin g → ℂ} :
    x ∈ eigSp R.B s ↔ ∀ a, R.B a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

open Classical in

theorem eigComp_eq (R : RiemLat E g Λ) (s : E →+* ℂ) (c : 𝓞 E →₀ ℂ)
    (hc : ∀ s' : E →+* ℂ, ∑ a ∈ c.support, c a * s' (algebraMap (𝓞 E) E a) = if s' = s then 1 else 0)
    (u : Λ) :
    eigComp R.B (s.comp (algebraMap (𝓞 E) E)) (R.P u) = ∑ a ∈ c.support, c a • R.P (a • u) := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hy : ∀ a : 𝓞 E, R.P (a • u) = ∑ s' : E →+* ℂ, s' (algebraMap (𝓞 E) E a) •
      eigComp R.B (s'.comp (algebraMap (𝓞 E) E)) (R.P u) := by
    intro a
    rw [R.act]
    conv_lhs => rw [← h4 (R.P u)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    exact (mem_eigSp_iff R).1 ((h3 _).1 _) a
  simp_rw [hy, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hc]
  simp [ite_smul]

variable {X : Type} [TopologicalSpace X]

theorem continuous_eigComp (R : X → RiemLat E g Λ) (hP : ∀ v, Continuous fun x => (R x).P v)
    (s : 𝓞 E →+* ℂ) (u : Λ) : Continuous fun x => eigComp (R x).B s ((R x).P u) := by
  classical
  obtain ⟨c, hc⟩ := exists_coeff (extEmb s)
  have h : ∀ x, eigComp (R x).B s ((R x).P u) = ∑ a ∈ c.support, c a • (R x).P (a • u) := by
    intro x
    have h1 := eigComp_eq (R x) (extEmb s) c hc u
    rwa [extEmb_comp] at h1
  simp_rw [h]
  exact continuous_finset_sum _ fun a _ => (hP (a • u)).const_smul (c a)

theorem continuous_ip (R : X → RiemLat E g Λ) (hH : Continuous fun x => (R x).Hm) {p q : X → Fin g → ℂ}
    (hp : Continuous p) (hq : Continuous q) : Continuous fun x => (R x).ip (p x) (q x) := by
  unfold RiemLat.ip
  exact hq.dotProduct (hH.matrix_mulVec (continuous_star.comp hp))

theorem continuous_nzOf {Ψ : Type} [Fintype Ψ] (R : X → RiemLat E g Λ)
    (hP : ∀ v, Continuous fun x => (R x).P v) (hH : Continuous fun x => (R x).Hm)
    (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) {r : ℕ} (v : Fin r → Λ) :
    Continuous fun x => (R x).nzOf σ I v := by
  unfold RiemLat.nzOf
  refine Continuous.div_const (continuous_finset_prod _ fun τ _ => ?_) _
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_matrix fun a b => ?_
  exact continuous_ip R hH (continuous_eigComp R hP _ _) (continuous_eigComp R hP _ _)

theorem continuous_nz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ)
    (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), (∀ v, Continuous fun x => (R x).P v) →
    (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ I hP hH
  by_cases h : ∃ r v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsNzFamily I r v
  · have e : (fun x => (R x).nz σ I) = fun x => (R x).nzOf σ I h.choose_spec.choose := by
      funext x
      simp only [RiemLat.nz, dif_pos h]
    rw [e]
    exact continuous_nzOf R hP hH σ I _
  · have e : (fun x => (R x).nz σ I) = fun _ => 1 := by
      funext x
      simp only [RiemLat.nz, dif_neg h]
    rw [e]
    exact continuous_const

end GlobalTheory.CompanionTheory.Ar.Cusp.NzCont
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt
open ReciprocityTheory.AnForm.R (conePts)

abbrev cxIdeal {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Ideal (MRingOver ℂ ι) :=
  P.map (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)

def cxPosDens {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (S : Set ((Σ k, ι k) → ℂ)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) : ℝ :=
  ∑ᶠ w ∈ setFibre S Ψ y, max (setSheetDensity S Ψ φ g y w) 0

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsDescendedRingHomOnQuotient
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.QuotUniv

theorem ringAction_descends_along_surjection
    (O : Type) [Ring O] (g g' : ℕ) (B : O →+* Module.End ℂ (Fin g → ℂ))
    (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hq : Function.Surjective q)
    (hk : ∀ (a : O) z, q z = 0 → q (B a z) = 0) :
    ∃ B' : O →+* Module.End ℂ (Fin g' → ℂ), ∀ a z, B' a (q z) = q (B a z) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqs : ∀ w, q (s w) = w := fun w => LinearMap.congr_fun hs w
  obtain ⟨F, hF⟩ : ∃ F : O → Module.End ℂ (Fin g' → ℂ), ∀ a z, F a (q z) = q (B a z) := by
    refine ⟨fun a => q ∘ₗ (B a ∘ₗ s), fun a z => ?_⟩
    have h0 : q (B a (s (q z) - z)) = 0 := hk a _ (by rw [map_sub, hqs, sub_self])
    rw [map_sub, map_sub, sub_eq_zero] at h0
    exact h0
  have hext : ∀ L M : Module.End ℂ (Fin g' → ℂ), (∀ z, L (q z) = M (q z)) → L = M := by
    intro L M h
    refine LinearMap.ext fun w => ?_
    obtain ⟨z, rfl⟩ := hq w
    exact h z
  refine ⟨{ toFun := F, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ },
    fun a z => hF a z⟩
  · exact hext _ _ fun z => by simp [hF]
  · intro a b
    exact hext _ _ fun z => by simp [hF, Module.End.mul_apply]
  · exact hext _ _ fun z => by simp [hF]
  · intro a b
    exact hext _ _ fun z => by simp [hF]

end GlobalTheory.CompanionTheory.Ar.QuotUniv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHermitianOrthogonalProjection
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.PosFormProjection

theorem exists_orthogonal_coefficients :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u →
      ∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ,
        ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  intro g k Hm hpos u hli z
  let A : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
    { toFun := fun c j => (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j)
      map_add' := by
        intro a b
        funext j
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, add_dotProduct]
      map_smul' := by
        intro a b
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, ← Finset.smul_sum,
          smul_dotProduct] }
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hw : ∀ j, (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := fun j => congrFun hc j
    have hww : (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (∑ i, c i • u i) = 0 := by
      rw [star_sum, Matrix.mulVec_sum, dotProduct_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, hw j, smul_zero]
    have hw0 : ∑ i, c i • u i = 0 := by
      by_contra hne
      have := hpos _ hne
      rw [hww] at this
      simp at this
    funext i
    exact Fintype.linearIndependent_iff.mp hli c hw0 i
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.mp hinj (fun j => z ⬝ᵥ Hm *ᵥ star (u j))
  refine ⟨c, fun j => ?_⟩
  have hcj : (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = z ⬝ᵥ Hm *ᵥ star (u j) := congrFun hc j
  rw [sub_dotProduct, hcj, sub_self]

end GlobalTheory.CompanionTheory.Ar.PosFormProjection
end

