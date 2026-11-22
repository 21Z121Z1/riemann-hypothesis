import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateNontrivial
section
noncomputable section

open IsLocalRing GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc

namespace TateSys

def sqDeg {l : ℕ} (μ : Fin l × Fin 1 → ℤ) : ℤ := ∑ p, μ p * μ p

theorem qW_mul (y : Fin 1 → ℤ) : qW !![1] (LinearMap.mul ℤ ℤ) y = y 0 * y 0 := by
  simp [qW]

theorem lin_mul {l : ℕ} (μ : Fin l × Fin 1 → ℤ) :
    ∑ i : Fin 1, lin !![1] μ ((fun _ => LinearMap.mul ℤ ℤ) i) = sqDeg μ := by
  simp [lin, qW_mul, sqDeg, Fintype.sum_prod_type]

def low (N : ℕ) {l : ℕ} (a : Fin l × Fin 1 → ℤ) (n : ℤ) : Set (Fin l × Fin 1 → ℤ) :=
  {μ | μ ∈ orbit ℤ 3 N (LinearMap.id : ℤ →ₗ[ℤ] ℤ) a ∧ sqDeg μ < n}

theorem low_finite (N : ℕ) {l : ℕ} (a : Fin l × Fin 1 → ℤ) (n : ℤ) : (low N a n).Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin l × Fin 1 => Set.Icc (-n) n) fun _ => Set.finite_Icc _ _).subset ?_
  rintro μ ⟨-, hμ⟩ p -
  have h1 : μ p * μ p ≤ sqDeg μ :=
    Finset.single_le_sum (f := fun p => μ p * μ p) (fun p _ => mul_self_nonneg _) (Finset.mem_univ p)
  have h2 : |μ p| ≤ μ p * μ p := by
    rcases eq_or_ne (μ p) 0 with h | h
    · simp [h]
    · rw [← abs_mul_abs_self]; exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs h)
  exact abs_le.1 (by linarith)

def lowF (N : ℕ) {l : ℕ} (a : Fin l × Fin 1 → ℤ) (n : ℤ) : Finset (Fin l × Fin 1 → ℤ) := (low_finite N a n).toFinset

theorem mem_lowF {N l : ℕ} {a : Fin l × Fin 1 → ℤ} {n : ℤ} {μ} :
    μ ∈ lowF N a n ↔ μ ∈ orbit ℤ 3 N (LinearMap.id : ℤ →ₗ[ℤ] ℤ) a ∧ sqDeg μ < n := by
  simp [lowF, low]

theorem term_eq {l : ℕ} (μ : Fin l × Fin 1 → ℤ) :
    (∏ i, (1 : PowerSeries ℚ) * mono !![1] (fun _ : Fin 1 => PowerSeries.X) (fun _ => LinearMap.mul ℤ ℤ)
      (fun v => μ (i, v))) = PowerSeries.X ^ (sqDeg μ).toNat := by
  simp only [one_mul, mono, qW_mul, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have : sqDeg μ = ((∑ i : Fin l, (μ (i, 0) * μ (i, 0)).toNat : ℕ) : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (mul_self_nonneg (μ (i, 0)))]
    simp [sqDeg, Fintype.sum_prod_type]
  rw [this, Int.toNat_natCast]

theorem X_mem : (PowerSeries.X : PowerSeries ℚ) ∈ maximalIdeal (PowerSeries ℚ) := by
  rw [PowerSeries.maximalIdeal_eq_span_X]; exact Ideal.mem_span_singleton_self _

theorem term_mem {l : ℕ} (μ : Fin l × Fin 1 → ℤ) {e : ℕ} (h : (e : ℤ) ≤ sqDeg μ) :
    (∏ i, (1 : PowerSeries ℚ) * mono !![1] (fun _ : Fin 1 => PowerSeries.X) (fun _ => LinearMap.mul ℤ ℤ)
      (fun v => μ (i, v))) ∈ maximalIdeal (PowerSeries ℚ) ^ e := by
  rw [term_eq]
  exact Ideal.pow_le_pow_right (by omega) (Ideal.pow_mem_pow X_mem _)

end TateSys

open TateSys in

def VSys.tate : VSys (O := ℤ) id 1 !![1] 3 (PowerSeries ℚ) where
  posW := by
    unfold PosW
    have : ((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℤ).transpose).map (Int.cast : ℤ → ℝ)) = Matrix.diagonal fun _ => 2 := by
      ext i j
      fin_cases i; fin_cases j; simp
    rw [this, Matrix.posDef_diagonal_iff]
    intro _; norm_num
  Y := PUnit
  V _ := PowerSeries ℚ
  ring _ := inferInstance
  dom _ := inferInstance
  loc _ := inferInstance
  cn _ := ⟨inferInstance, inferInstance, inferInstance, algebraRat.charZero _⟩
  ev _ := RingHom.id _
  ev_loc _ := inferInstance
  X _ := ℤ
  add _ := inferInstance
  mod _ := inferInstance
  fin _ := inferInstance
  proj _ := inferInstance
  freeZ _ := inferInstance
  finZ _ := inferInstance
  rank_le _ := by simp
  m _ := 1
  t _ _ := PowerSeries.X
  t_mem _ _ := ⟨X_mem, PowerSeries.X_ne_zero⟩
  δ _ _ := LinearMap.mul ℤ ℤ
  bal _ _ := ⟨fun y z => by simp [mul_comm], fun a y z => by simp [mul_left_comm, mul_assoc]⟩
  nonneg _ _ x := by simpa using mul_self_nonneg x
  pos _ x hx := ⟨0, by simpa using mul_self_pos.2 hx⟩
  Q := Unit
  u _ _ _ := 1
  u_unit _ _ := ⟨(), isUnit_one⟩
  lam := ⟨1, fun _ _ _ x hx => ⟨PowerSeries.X, X_mem, dvd_pow_self _ (by
    have : 0 < x * x := mul_self_pos.2 hx
    simp only [LinearMap.mul_apply', one_mul]; omega)⟩⟩
  four y₀ N₀ := by
    refine ⟨3 * N₀, by omega, dvd_mul_right _ _, fun _ => LinearMap.id, rfl,
      fun _ => ⟨fun c x => ⟨0, by simp⟩, LinearEquiv.refl ℤ ℤ, by simp⟩, fun l a c e => ?_⟩
    refine ⟨∑ μ ∈ lowF (3 * N₀) a e, ∏ i, (1 : PowerSeries ℚ) * mono !![1] (fun _ : Fin 1 => PowerSeries.X)
      (fun _ => LinearMap.mul ℤ ℤ) (fun v => μ (i, v)), fun y j => ⟨lowF (3 * N₀) a (max j e), ?_, ?_, ?_⟩⟩
    · intro μ hμ; exact (mem_lowF.1 hμ).1
    · intro μ hμ hS
      rw [lin_mul]
      by_contra h
      exact hS (mem_lowF.2 ⟨hμ, by push_neg at h; exact lt_of_lt_of_le h (le_max_left _ _)⟩)
    · have hsub : lowF (3 * N₀) a e ⊆ lowF (3 * N₀) a (max j e) := fun μ hμ =>
        mem_lowF.2 ⟨(mem_lowF.1 hμ).1, lt_of_lt_of_le (mem_lowF.1 hμ).2 (le_max_right _ _)⟩
      apply Ideal.mem_sup_right
      rw [Ideal.map_id]
      change _ - ∑ μ ∈ lowF (3 * N₀) a (max j e), _ ∈ _
      rw [← Finset.sum_sdiff hsub, RingHom.id_apply, sub_add_cancel_right]
      refine (Ideal.neg_mem_iff _).2 (Ideal.sum_mem _ fun μ hμ => term_mem μ ?_)
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hμ
      by_contra h
      exact h2 (mem_lowF.2 ⟨(mem_lowF.1 h1).1, by push_neg at h; exact h⟩)

theorem VSys.tate_nontrivial : ∀ y, VSys.tate.m y = 1 ∧ ∀ i, VSys.tate.t y i = PowerSeries.X ∧ VSys.tate.t y i ≠ 0 :=
  fun _ => ⟨rfl, fun _ => ⟨rfl, PowerSeries.X_ne_zero⟩⟩

theorem TateSys.unit_eq_one {e : ℤ ≃ₗ[ℤ] ℤ} : e 1 = 1 ∨ e 1 = -1 := by
  have h : e 1 * e.symm 1 = 1 := by
    have := e.apply_symm_apply 1
    rw [show e.symm 1 = e.symm 1 • (1 : ℤ) by simp, map_smul, smul_eq_mul] at this
    linarith
  exact Int.eq_one_or_neg_one_of_mul_eq_one h

theorem dominant_tate : Dominant (O := ℤ) id (InvFun.minVal ℤ) 1 3 !![1] (X := ℤ) (fun _ : Fin 1 => LinearMap.mul ℤ ℤ)
    (fun _ : Fin 1 × Fin 1 => (1 : ℤ)) where
  span := by
    rw [eq_top_iff]; intro x _
    have : (1 : ℤ) ∈ Submodule.span ℤ (Set.range fun _ : Fin 1 × Fin 1 => (1 : ℤ)) :=
      Submodule.subset_span ⟨(0, 0), rfl⟩
    simpa using Submodule.smul_mem _ x this
  le β _ hβ := by
    have hlin : (lin !![1] (fun _ : Fin 1 × Fin 1 => (1 : ℤ)) β : ℝ) = β 1 1 := by simp [lin, qW]
    rw [hlin, Nat.cast_one, one_mul, InvFun.evalZ,
      (InvFun.minVal ℤ).eval_eq (n := 1) (r := LinearMap.proj 0) fun x => ⟨fun _ => x, rfl⟩]
    show sInf _ ≤ _
    have hsq : ∀ y : ℤ, β y y = y * y * β 1 1 := fun y => by
      have h1 : β y y = β (y • 1) (y • 1) := by simp
      rw [h1, LinearMap.map_smul₂, LinearMap.map_smul]; simp [mul_assoc]
    by_cases h0 : (β 1 1 : ℝ) = 0
    · rw [h0]
      refine Real.sInf_nonpos fun x ⟨⟨y, hy⟩, hx⟩ => ?_
      exfalso; apply hx; rw [← hy]
      have h00 : β 1 1 = 0 := by exact_mod_cast h0
      show (β (y 0) (y 0) : ℝ) = (β ((LinearMap.proj 0 : (Fin 1 → ℤ) →ₗ[ℤ] ℤ) 0) ((LinearMap.proj 0 : (Fin 1 → ℤ) →ₗ[ℤ] ℤ) 0) : ℝ)
      rw [hsq (y 0), h00]; simp
    · refine csInf_le ⟨0, ?_⟩ ⟨⟨fun _ => 1, rfl⟩, by
        simp only [LinearMap.proj_apply, map_zero, LinearMap.zero_apply, Int.cast_zero]; exact h0⟩
      rintro x ⟨⟨y, rfl⟩, -⟩
      show (0 : ℝ) ≤ (β (y 0) (y 0) : ℝ); exact_mod_cast hβ _
  min e _ j := by
    simp only [lin, TateSys.qW_mul, Finset.univ_unique, Finset.sum_singleton, LinearMap.mul_apply']
    rcases TateSys.unit_eq_one (e := e) with h | h <;> simp [h]
  strict e he := by
    rintro ⟨x, hx⟩
    exfalso; apply hx
    have h1 : e 1 = 1 := by
      obtain ⟨w, hw⟩ := he 1
      rcases TateSys.unit_eq_one (e := e) with h | h
      · exact h
      · rw [h] at hw; simp at hw; omega
    rw [show x = x • (1 : ℤ) by simp, map_smul, h1]

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem isAffine_aff {X : Scheme.{0}} (U : X.affineOpens) : IsAffineOpen U.1 := U.2

def preAff {X₀ X₁ : Scheme.{0}} (pr : X₁ ⟶ X₀) [IsAffineHom pr] : AffOp X₀ ⥤ AffOp X₁ where
  obj U := op ⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩
  map a := (homOfLE (pr.preimage_mono (leOfHom a.unop))).op

def natCoef {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F F' : C ⥤ CommAlgCat.{0} R}
    (α : ∀ T, F.obj T →+* F'.obj T) (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) : CoefMap (RingHom.id R) F F' where
  G := 𝟭 C
  α := α
  naturality := nat
  smul := smul

variable {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}

def prSec (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) :
    Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  GlobalTheory.CechDR.secPull (φ := pr) s₀ s₁ ⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩

def tensHom (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) :
    R₁ ⊗[R₀] Sec s₀ U.1 →ₐ[R₁] Sec s₁ (pr ⁻¹ᵁ U.1) :=
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId R₁ _)
    { prSec w U hU with commutes' := fun r ↦ (semiHom_secPull w (⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩ : Pair pr)).map_algebraMap r }
    (fun _ _ ↦ Commute.all _ _)

theorem tensHom_tmul (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens)
    (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) (r : R₁) (b : Sec s₀ U.1) :
    tensHom w U hU (r ⊗ₜ b) = algebraMap R₁ _ r * prSec w U hU b := by
  simp [tensHom, Algebra.ofId_apply]; rfl

variable [IsAffineHom pr]

theorem prSec_res (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) {U V : AffOp X₀} (a : U ⟶ V) (b : Sec s₀ U.unop.1) :
    prSec w V.unop ((isAffine_aff V.unop).preimage pr) (mp (OAff s₀) a b) =
      Sec.res s₁ (pr.preimage_mono (leOfHom a.unop)) (prSec w U.unop ((isAffine_aff U.unop).preimage pr) b) :=
  (pairPull w).naturality (T := op ⟨(⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩, U.unop), le_rfl⟩)
    (T' := op ⟨(⟨pr ⁻¹ᵁ V.unop.1, (isAffine_aff V.unop).preimage pr⟩, V.unop), le_rfl⟩)
    (homOfLE (show (⟨(⟨pr ⁻¹ᵁ V.unop.1, (isAffine_aff V.unop).preimage pr⟩, V.unop), le_rfl⟩ : Pair pr) ≤
      ⟨(⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩, U.unop), le_rfl⟩ from
        ⟨pr.preimage_mono (leOfHom a.unop), leOfHom a.unop⟩)).op b

def tensCoef (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) :
    CoefMap (RingHom.id R₁) (ext R₁ (OAff s₀)) (preAff pr ⋙ OAff s₁) :=
  natCoef (fun U ↦ (tensHom w U.unop ((isAffine_aff U.unop).preimage pr) : R₁ ⊗[R₀] Sec s₀ U.unop.1 →+* Sec s₁ (pr ⁻¹ᵁ U.unop.1)))
    (fun {U V} a b ↦ by
      change tensHom w V.unop _ (extHom R₁ (mp (OAff s₀) a) b) =
        Sec.res s₁ (pr.preimage_mono (leOfHom a.unop)) (tensHom w U.unop _ b)
      induction b using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul r x =>
        rw [Algebra.TensorProduct.map_tmul, tensHom_tmul, tensHom_tmul, map_mul, AlgHom.id_apply, prSec_res]
        congr 1
        exact ((Sec.res s₁ (pr.preimage_mono (leOfHom a.unop))).commutes r).symm
      | add x y hx hy => simp only [map_add, hx, hy])
    (fun U r b ↦ map_smul (tensHom w U.unop ((isAffine_aff U.unop).preimage pr)) r b)

variable {Y₀ Y₁ : Scheme.{0}} {pr' : Y₁ ⟶ Y₀} [IsAffineHom pr']

def pairBCObj (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) (p : Pair f₀) : Pair f₁ :=
  ⟨(⟨pr' ⁻¹ᵁ p.1.1.1, (isAffine_aff p.1.1).preimage pr'⟩,
    ⟨pr ⁻¹ᵁ p.1.2.1, (isAffine_aff p.1.2).preimage pr⟩), by
    change pr' ⁻¹ᵁ p.1.1.1 ≤ f₁ ⁻¹ᵁ pr ⁻¹ᵁ p.1.2.1
    rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
    exact pr'.preimage_mono p.2⟩

def pairBC (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) : (Pair f₀)ᵒᵖ ⥤ (Pair f₁)ᵒᵖ where
  obj p := op (pairBCObj pr pr' e p.unop)
  map {p q} a := (homOfLE (show pairBCObj pr pr' e q.unop ≤ pairBCObj pr pr' e p.unop from
    Subtype.coe_le_coe.1 (Prod.mk_le_mk.2 ⟨pr'.preimage_mono (Pair.le_fst (leOfHom a.unop)),
      pr.preimage_mono (Pair.le_snd (leOfHom a.unop))⟩))).op

variable {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁}

def tensPair (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) : CoefMap (RingHom.id R₁) (ext R₁ (OPair f₀ t₀)) (pairBC pr pr' e ⋙ OPair f₁ t₁) :=
  natCoef (fun p ↦ (tensCoef w').α ((pairFst f₀).obj p)) (fun a b ↦ (tensCoef w').naturality ((pairFst f₀).map a) b)
    (fun p r b ↦ (tensCoef w').smul ((pairFst f₀).obj p) r b)

end GlobalTheory.Obs.BC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFractionInjectiveOfTensorInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

theorem GlobalTheory.tensor_fraction_injective_of_injective
    (R R₁ B K L : Type) [CommRing R] [CommRing R₁] [CommRing B] [Field K] [Field L] [Algebra R R₁]
    [Algebra R B] [Algebra R K] [Algebra B K] [IsScalarTower R B K] [IsFractionRing B K]
    (θ : K →+* L) (c : R₁ →+* L) (β : B ⊗[R] R₁ →+ L) (hβ : Function.Injective β)
    (hβt : ∀ b r, β (b ⊗ₜ[R] r) = θ (algebraMap B K b) * c r)
    (n : ℕ) (u : Fin n → K) (r : Fin n → R₁) (h : ∑ j, c (r j) * θ (u j) = 0) :
    ∑ j, u j ⊗ₜ[R] r j = 0 := by
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) (Finset.univ : Finset (Fin n)) u
  choose x hx using fun j => hs j (Finset.mem_univ j)

  have hx' : ∀ j, algebraMap B K (x j) = algebraMap B K (s : B) * u j := by
    intro j; rw [hx j, Algebra.smul_def]
  have h0 : ∑ j, x j ⊗ₜ[R] r j = 0 := by
    apply hβ
    rw [map_sum, map_zero]
    simp only [hβt, hx', map_mul]
    calc ∑ j, θ (algebraMap B K (s : B)) * θ (u j) * c (r j)
        = θ (algebraMap B K (s : B)) * ∑ j, c (r j) * θ (u j) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by rw [h, mul_zero]
  have h1 := congrArg ((IsScalarTower.toAlgHom R B K).toLinearMap.rTensor R₁) h0
  simp only [map_sum, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
    IsScalarTower.coe_toAlgHom', map_zero] at h1
  have h2 : (algebraMap B K (s : B)) • ∑ j, u j ⊗ₜ[R] r j = 0 := by
    rw [Finset.smul_sum]
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, hx'] using h1
  have hne : algebraMap B K (s : B) ≠ 0 :=
    (IsLocalization.map_units K s).ne_zero
  have := congrArg (fun z => (algebraMap B K (s : B))⁻¹ • z) h2
  simp only [smul_zero] at this
  rwa [inv_smul_smul₀ hne] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TermsumTrFacDifferentiable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem termsum_fderiv_mul_affine {g : ℕ} (f F : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f) (hF : Differentiable ℂ F)
    (c : ℂ) (p W : Fin g → ℂ) :
    fderiv ℂ (fun Z => f Z * F (c • Z + p)) 0 W = fderiv ℂ f 0 W * F p + f 0 * fderiv ℂ F p (c • W) := by
  have h1 : HasFDerivAt (fun Z : Fin g → ℂ => c • Z + p) (c • ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0 :=
    ((hasFDerivAt_id (0 : Fin g → ℂ)).const_smul c).add_const p
  have h2 : HasFDerivAt F (fderiv ℂ F p) (c • (0 : Fin g → ℂ) + p) := by
    rw [smul_zero, zero_add]; exact (hF p).hasFDerivAt
  have h3 : HasFDerivAt (fun Z => F (c • Z + p)) _ 0 := h2.comp (0 : Fin g → ℂ) h1
  have h4 : HasFDerivAt (fun Z => f Z * F (c • Z + p)) _ 0 := (hf 0).hasFDerivAt.mul h3
  rw [h4.fderiv]
  simp
  ring

theorem termsum_trFac_differentiable {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (m : ℕ)
    (M N : Fin g → ℤ) : Differentiable ℂ (trFac τ a b m M N) := by
  unfold trFac
  simp only [dotProduct]
  fun_prop

theorem termsum_full_isSymm {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) (S : Matrix (Fin r) (Fin r) ℂ) (hS : S.IsSymm) : (d.full σ S).IsSymm := by
  unfold CD.full
  apply Matrix.IsSymm.submatrix
  exact Matrix.IsSymm.fromBlocks d.symm rfl (d.toricPeriodBlock_isSymm.add hS)

theorem termsum_half_aF {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) : Half (d.aF σ) := by
  intro j
  unfold CD.aF
  rcases σ j with i | l
  · exact d.ha i
  · exact Or.inl rfl

theorem termsum_half_bF {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)
    (σ : Fin g ≃ Fin g' ⊕ Fin r) : Half (d.bF σ) := by
  intro j
  unfold CD.bF
  rcases σ j with i | l
  · exact d.hb i
  · exact d.hb2 l

theorem term_sum_and_fderiv : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ S : Matrix (Fin r) (Fin r) ℂ, S.IsSymm → ((d.full σ S).map Complex.im).PosDef → ∀ (m : ℕ) (M Nn : Fin g → ℤ) (W : Fin g → ℂ), (Summable fun χ => ‖d.term σ S m M Nn χ 0‖) ∧ (Summable fun χ => ‖fderiv ℂ (d.term σ S m M Nn χ) 0 W‖) ∧ ∑' χ, d.term σ S m M Nn χ 0 = trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn 0 ∧ ∑' χ, fderiv ℂ (d.term σ S m M Nn χ) 0 W = fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn) 0 W := by
  intro N g' r g bX d σ S hS hpos m M Nn W
  have hθ := (GlobalTheory.T.thetaChar_differentiable_ne_zero_automorphy g _ _ _ (termsum_full_isSymm d σ S hS) hpos (termsum_half_aF d σ) (termsum_half_bF d σ)).1
  set p := (m : ℂ)⁻¹ • perV (d.full σ S) M Nn with hp
  obtain ⟨hs, he⟩ := GlobalTheory.T.thetaChar_blockPeriodMatrix_fourierJacobiExpansion N g' r g bX d σ S hS hpos p
  obtain ⟨hd, hD⟩ := GlobalTheory.T.fourierJacobiExpansion_fderiv_termwise N g' r g bX d σ S hS hpos
  obtain ⟨hs', he'⟩ := hD p ((m : ℂ) • W)
  have hf := termsum_trFac_differentiable (d.full σ S) (d.aF σ) (d.bF σ) m M Nn
  set f := trFac (d.full σ S) (d.aF σ) (d.bF σ) m M Nn with hfdef
  have e0 : ∀ χ, d.term σ S m M Nn χ 0 = f 0 * d.fj σ S χ p := fun χ => by
    simp only [CD.term, smul_zero, zero_add, hfdef, hp]
  have e1 : ∀ χ, fderiv ℂ (d.term σ S m M Nn χ) 0 W =
      fderiv ℂ f 0 W * d.fj σ S χ p + f 0 * fderiv ℂ (d.fj σ S χ) p ((m : ℂ) • W) := fun χ =>
    termsum_fderiv_mul_affine f (d.fj σ S χ) hf (hd χ) m p W
  have e2 : fderiv ℂ (trF (d.full σ S) (d.aF σ) (d.bF σ) m M Nn) 0 W = _ :=
    termsum_fderiv_mul_affine f _ hf hθ m p W
  have s1 := hs.of_norm
  have s2 := hs'.of_norm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [e0]
    exact (s1.mul_left _).norm
  · simp only [e1]
    exact ((s1.mul_left _).add (s2.mul_left _)).norm
  · simp only [e0]
    rw [tsum_mul_left, he]
    simp only [trF, smul_zero, zero_add, hfdef, hp]
  · simp only [e1]
    rw [(s1.mul_left _).tsum_add (s2.mul_left _), tsum_mul_left, tsum_mul_left, he, he', e2]

end GlobalTheory.MBLow.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariant
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.KCoinvGood

theorem augAt_le_SB {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (v : Pl F) : augAt om v ≤ SB _ :=
  Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ

theorem acts_zero {F : Type} [Field F] [NumberField F] {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts ev T 0 0 := fun r _ => by
  have e : tens ev (0 : (κ → R) → ℂ) r = 0 := funext fun x => by simp [tens]
  rw [e, map_zero]

theorem ker_eq_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    (S A : Submodule ℂ V) (p : V →ₗ[ℂ] P) (hA : A ≤ LinearMap.ker p) (honto : S.map p = ⊤)
    (h : S ⊓ LinearMap.ker p = A ∨ S ⊓ LinearMap.ker p = S) : ∀ φ ∈ S, p φ = 0 ↔ φ ∈ A := by
  rcases h with h | h
  · intro φ hφ
    refine ⟨fun h0 => h ▸ ⟨hφ, h0⟩, fun hm => hA hm⟩
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : P)
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    have hy' : y ∈ S ⊓ LinearMap.ker p := by rw [h]; exact hy
    exact hx hy'.2

theorem factor_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P]
    (S : Submodule ℂ V) (p : V →ₗ[ℂ] P) (l : V →ₗ[ℂ] ℂ) (honto : S.map p = ⊤) (hk : ∀ φ ∈ S, p φ = 0 → l φ = 0) :
    ∃ l₀ : P →ₗ[ℂ] ℂ, ∀ φ ∈ S, l φ = l₀ (p φ) := by
  set q := p.domRestrict S
  have hs : Function.Surjective q := by
    intro x
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : LinearMap.ker q ≤ LinearMap.ker (l.domRestrict S) := fun x hx => hk x.1 x.2 hx
  refine ⟨((LinearMap.ker q).liftQ (l.domRestrict S) hker).comp (q.quotKerEquivOfSurjective hs).symm.toLinearMap,
    fun φ hφ => ?_⟩
  have : (q.quotKerEquivOfSurjective hs).symm (p φ) = Submodule.Quotient.mk ⟨φ, hφ⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [this]

theorem kCoinv (hP : GlobalTheory.FunPr.Hypotheses₂) : GlobalTheory.ThK.KCoinv := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm
  have ht := hm.triple
  have hf := hm.fin
  refine ⟨fun v hv => ?_, GlobalTheory.T.weil_representation_preserves_space hP F E σ B a a' G X om om' ht⟩
  haveI := hf.nontriv v
  have hnr := GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' ht v hv
  have k1 : ∀ φ ∈ SB _, Rf.p v φ = 0 ↔ φ ∈ augAt om v :=
    ker_eq_of _ _ _ (hf.inv v) (hf.onto v) <|
      GlobalTheory.T.augmentation_submodule_first_factor hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om v) (hf.inv v)) inf_le_left
        fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by
          have := hf.equiv v h hh φ hφ.1 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero _ _)
            (by rw [map_zero]; exact hφ.2)
          rw [map_zero] at this; exact this⟩
  have k2 : ∀ φ ∈ SB _, Rf.p' v φ = 0 ↔ φ ∈ augAt om' v :=
    ker_eq_of _ _ _ (hf.inv' v) (hf.onto' v) <|
      GlobalTheory.T.augmentation_submodule_second_factor hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om' v) (hf.inv' v)) inf_le_left
        fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by
          have := hf.equiv v h hh 0 (zero_mem _) φ hφ.1 0 (zero_mem _) φ₁ hφ₁ (acts_zero _ _) hact
            (by rw [map_zero]; exact hφ.2.symm)
          rw [map_zero] at this; exact this.symm⟩
  refine ⟨k1, k2, fun t ξ => ?_, fun l hl => ?_⟩
  · have : ξ ∈ (SB _).map (Rf.p' v) := hf.onto' v ▸ Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := this
    obtain ⟨φ₀, h₀, hd⟩ := GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' ht v hv hnr t φ hφ
    refine ⟨φ₀, h₀, ?_⟩
    have := hf.inv' v hd
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this.symm
  · exact factor_of _ _ _ (hf.onto' v) fun φ hφ h0 => hl ((k2 φ hφ).1 h0)

end GlobalTheory.KCoinvGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLineBundleTrivialBasicOpenOfTrivialFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLineBundle_trivial_basicOpen_of_trivial_fibre : (∀ (T : Type) [CommRing T] [IsLocalRing T] (e : T), (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T → ∀ (A : Over (Sp T)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ k : ℕ, IsUnit (k : T) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (f' : X' ⟶ Sp (T ⧸ Ideal.span {e})), IsPullback π f' A.hom (spMap (Ideal.Quotient.mk (Ideal.span {e}))) → (∃ t : (M.pull π).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over (Sp R)) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit (k : R) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → ∀ (K : Type) [Field K] (g₀ : R →+* K), (∃ t : (M.pull (pullback.fst A.hom (spMap g₀))).Gen, t.IsGen) → ∃ r : R, g₀ r ≠ 0 ∧ ∃ t : (M.pull (A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι).Gen, t.IsGen := by
  first | (exact @GlobalTheory.TorsionSpread.triv_basicOpen_of_triv_fibre) | (exact GlobalTheory.TorsionSpread.triv_basicOpen_of_triv_fibre) | (intros; apply GlobalTheory.TorsionSpread.triv_basicOpen_of_triv_fibre <;> assumption)
end

