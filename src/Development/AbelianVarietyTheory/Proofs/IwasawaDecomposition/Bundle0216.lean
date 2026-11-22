import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0127
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0210
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AutSpace

variable {D : D7} (θ : InfF D) (V : HSp D)

def SmFun : Submodule ℂ (GA D V → ℂ) where
  carrier := {φ | ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
    (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)}
  add_mem' := fun ha hb k τs Xs h g => (ha k τs Xs h g).add (hb k τs Xs h g)
  zero_mem' := fun _ _ _ _ _ => contDiff_const
  smul_mem' := fun c _ ha k τs Xs h g => (ha k τs Xs h g).const_smul c

variable {θ V}

theorem differentiable_oneP {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) (g : GA D V) :
    Differentiable ℝ fun t : ℝ => φ (g * oneP θ V τ X t) := by
  have h := hφ 1 (fun _ => τ) (fun _ => X) (fun _ => hX) g
  have h2 : ContDiff ℝ ∞ fun t : ℝ => (fun _ : Fin 1 => t) := contDiff_pi.2 fun _ => contDiff_id
  have h3 := (h.comp h2).differentiable (by simp)
  simpa [Function.comp_def] using h3

theorem Rder_add {φ ψ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) (hψ : ψ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X (φ + ψ) = Rder θ V τ X φ + Rder θ V τ X ψ := by
  funext g
  exact deriv_fun_add (differentiable_oneP hφ hX g 0) (differentiable_oneP hψ hX g 0)

theorem Rder_smul (c : ℂ) (φ : GA D V → ℂ) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  exact deriv_const_mul_field c

theorem Rder_mem {φ : GA D V → ℂ} (hφ : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) : Rder θ V τ X φ ∈ SmFun θ V := by
  intro k τs Xs h g
  have h1 := hφ (k + 1) (Fin.snoc (α := fun _ => D.what₂.Tau) τs τ)
    (Fin.snoc (α := fun _ => Matrix (Fin V.rank) (Fin V.rank) ℂ) Xs X)
    (fun i => by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hX
      · simpa using h j) g
  have h2 : ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
    refine contDiff_pi.2 fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using contDiff_snd
    · simp only [Fin.snoc_castSucc]
      fun_prop
  have h3 : ContDiff ℝ ∞ (Function.uncurry fun (t : Fin k → ℝ) (s : ℝ) =>
      φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * oneP θ V τ X s)) := by
    convert h1.comp h2 using 1
    funext p
    simp [Function.uncurry, List.ofFn_succ', mul_assoc, -List.ofFn_succ]
  have h4 := ContDiff.fderiv (n := ∞) h3 (contDiff_const (c := (0 : ℝ))) (by simp)
  exact h4.clm_apply (contDiff_const (c := (1 : ℝ)))

variable (θ V) in

structure LinOnSm (T : (GA D V → ℂ) → (GA D V → ℂ)) : Prop where
  mem : ∀ φ ∈ SmFun θ V, T φ ∈ SmFun θ V
  add : ∀ φ ∈ SmFun θ V, ∀ ψ ∈ SmFun θ V, T (φ + ψ) = T φ + T ψ
  smul : ∀ (c : ℂ) φ, T (c • φ) = c • T φ

theorem linOnSm_Rder {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    LinOnSm θ V (Rder θ V τ X) :=
  ⟨fun _ h => Rder_mem h hX, fun _ h _ h' => Rder_add h h' hX, fun c φ => Rder_smul c φ τ X⟩

theorem linOnSm_RderC (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) : LinOnSm θ V (RderC θ V τ Z) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  refine ⟨fun φ h => ?_, fun φ h ψ h' => ?_, fun c φ => ?_⟩
  · exact add_mem (Rder_mem h h1) (Submodule.smul_mem _ _ (Rder_mem h h2))
  · simp only [RderC]
    rw [Rder_add h h' h1, Rder_add h h' h2, smul_add Complex.I, add_add_add_comm]
  · simp only [RderC]
    rw [Rder_smul, Rder_smul, smul_add c, smul_comm c Complex.I]

theorem linOnSm_foldr {α : Type} (T : α → (GA D V → ℂ) → (GA D V → ℂ)) (l : List α)
    (hl : ∀ a ∈ l, LinOnSm θ V (T a)) : LinOnSm θ V fun φ => l.foldr (fun a f => T a f) φ := by
  induction l with
  | nil => exact ⟨fun _ h => h, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  | cons a l ih =>
    have h1 := hl a (by simp)
    have h2 := ih fun b hb => hl b (by simp [hb])
    refine ⟨fun φ h => h1.mem _ (h2.mem φ h), fun φ h ψ h' => ?_, fun c φ => ?_⟩
    · simp only [List.foldr_cons]
      rw [h2.add φ h ψ h', h1.add _ (h2.mem φ h) _ (h2.mem ψ h')]
    · simp only [List.foldr_cons]
      rw [h2.smul, h1.smul]

theorem linOnSm_gelf (τ : D.what₂.Tau) (k : ℕ) : LinOnSm θ V (gelf θ V τ k) := by
  have h : ∀ idx : Fin (k + 1) → Fin V.rank, LinOnSm θ V fun φ =>
      (List.ofFn fun a : Fin (k + 1) => RderC θ V τ (Matrix.single (idx a) (idx (a + 1)) 1)).foldr
        (fun f acc => f acc) φ := fun idx =>
    linOnSm_foldr (fun f => f) _ fun f hf => by
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
      exact linOnSm_RderC τ _
  refine ⟨fun φ hφ => Submodule.sum_mem _ fun idx _ => (h idx).mem φ hφ, fun φ hφ ψ hψ => ?_, fun c φ => ?_⟩
  · simp only [gelf]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun idx _ => (h idx).add φ hφ ψ hψ
  · simp only [gelf]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun idx _ => (h idx).smul c φ

theorem one_le_sum_norm {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (h : A * B = 1) (i : Fin n) :
    1 ≤ ∑ a, ∑ b, (‖A a b‖ + ‖B a b‖) := by
  set S := ∑ a, ∑ b, (‖A a b‖ + ‖B a b‖) with hS
  have hS0 : 0 ≤ S := by positivity
  have hle : ∀ a b, ‖A a b‖ + ‖B a b‖ ≤ S := fun a b =>
    (Finset.single_le_sum (f := fun b => ‖A a b‖ + ‖B a b‖) (fun _ _ => by positivity) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (‖A a b‖ + ‖B a b‖)) (fun _ _ => by positivity) (Finset.mem_univ a))
  have hrow : ∑ b, ‖A i b‖ ≤ S :=
    (Finset.sum_le_sum fun b _ => le_add_of_nonneg_right (norm_nonneg (B i b))).trans
      (Finset.single_le_sum (f := fun a => ∑ b, (‖A a b‖ + ‖B a b‖)) (fun _ _ => by positivity) (Finset.mem_univ i))
  have h1 : (1 : ℝ) ≤ S * S := by
    have e : (1 : ℂ) = ∑ b, A i b * B b i := by rw [← Matrix.mul_apply, h, Matrix.one_apply_eq]
    calc (1 : ℝ) = ‖∑ b, A i b * B b i‖ := by rw [← e, norm_one]
      _ ≤ ∑ b, ‖A i b‖ * S := (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left ((le_add_of_nonneg_left (norm_nonneg (A b i))).trans (hle b i))
            (norm_nonneg _))
      _ ≤ S * S := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hrow hS0
  nlinarith

variable (θ V) in
theorem infMat_mul_inv (τ : D.what₂.Tau) (g : GA D V) :
    infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ = 1 := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  rw [e, e, ← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.map_one _ (map_zero _) (map_one _)]

variable (θ V) in

theorem normInf_dichotomy : (∀ g, normInf θ V g = 0) ∨ ∀ g, 1 ≤ normInf θ V g := by
  by_cases h : Nonempty D.what₂.Tau ∧ Nonempty (Fin V.rank)
  · obtain ⟨⟨τ⟩, ⟨i⟩⟩ := h
    refine Or.inr fun g => (one_le_sum_norm _ _ (infMat_mul_inv θ V τ g) i).trans ?_
    exact Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, (‖infMat D.sp.cm.sig V.gram (θ τ) g i j‖ +
      ‖infMat D.sp.cm.sig V.gram (θ τ) g⁻¹ i j‖)) (fun _ _ => by positivity) (Finset.mem_univ τ)
  · refine Or.inl fun g => Finset.sum_eq_zero fun τ _ => Finset.sum_eq_zero fun i _ => ?_
    exact (h ⟨⟨τ⟩, ⟨i⟩⟩).elim

variable (θ V) in
theorem exists_pow_ge (a b : ℕ) :
    ∃ N : ℕ, ∀ g, normInf θ V g ^ a ≤ normInf θ V g ^ N ∧ normInf θ V g ^ b ≤ normInf θ V g ^ N := by
  rcases normInf_dichotomy θ V with h | h
  · refine ⟨0, fun g => ?_⟩
    rw [h g, pow_zero]
    exact ⟨pow_le_one₀ le_rfl zero_le_one, pow_le_one₀ le_rfl zero_le_one⟩
  · exact ⟨max a b, fun g => ⟨pow_le_pow_right₀ (h g) (le_max_left _ _), pow_le_pow_right₀ (h g) (le_max_right _ _)⟩⟩

theorem normInf_nonneg (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf
  positivity

theorem isAutFunSm_smul (c : ℂ) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) : IsAutFunSm θ V (c • φ) := by
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.const_smul c⟩, (SmFun θ V).smul_mem c h.smooth, ?_, ?_⟩
  · simp only [Pi.smul_apply, h.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k h1 h2 g => by simp only [Pi.smul_apply, hk k h1 h2 g]⟩
  · obtain ⟨W, hW, h1, h2⟩ := h.zfin
    exact ⟨W, hW, W.smul_mem c h1, h2⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).smul c φ
    rw [this, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c)

variable (θ V) in
theorem isAutFunSm_zero : IsAutFunSm θ V 0 := by
  refine ⟨⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩, (SmFun θ V).zero_mem,
    ⟨⊥, inferInstance, zero_mem _, fun τ k f hf => ?_⟩, ⟨0, fun l hl x => ⟨0, fun g _ => ?_⟩⟩⟩
  · have := (linOnSm_gelf (θ := θ) (V := V) τ k).smul 0 f
    rw [(Submodule.mem_bot ℂ).1 hf, zero_smul, zero_smul] at this
    rw [(Submodule.mem_bot ℂ).1 hf, this]
    exact zero_mem _
  · have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    simp

theorem isAutFunSm_add {φ ψ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (h' : IsAutFunSm θ V ψ) :
    IsAutFunSm θ V (φ + ψ) := by
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.add h'.cont⟩, (SmFun θ V).add_mem h.smooth h'.smooth, ?_, ?_⟩
  · simp only [Pi.add_apply, h.left γ hγ g, h'.left γ hγ g]
  · obtain ⟨U, hU, hk⟩ := h.level
    obtain ⟨U', hU', hk'⟩ := h'.level
    exact ⟨U ⊓ U', hU.inter hU', fun k h1 h2 g => by simp only [Pi.add_apply, hk k h1.1 h2 g, hk' k h1.2 h2 g]⟩
  · obtain ⟨W, hW, h1, h2⟩ := h.zfin
    obtain ⟨W', hW', h1', h2'⟩ := h'.zfin
    refine ⟨(W ⊓ SmFun θ V) ⊔ (W' ⊓ SmFun θ V), inferInstance,
      Submodule.add_mem_sup ⟨h1, h.smooth⟩ ⟨h1', h'.smooth⟩, fun τ k f hf => ?_⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    have hg := linOnSm_gelf (θ := θ) (V := V) τ k
    rw [hg.add a ha.2 b hb.2]
    exact Submodule.add_mem_sup ⟨h2 τ k a ha.1, hg.mem a ha.2⟩ ⟨h2' τ k b hb.1, hg.mem b hb.2⟩
  · obtain ⟨N, hN⟩ := h.growth
    obtain ⟨N', hN'⟩ := h'.growth
    obtain ⟨M, hM⟩ := exists_pow_ge θ V N N'
    refine ⟨M, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    obtain ⟨C', hC'⟩ := hN' l hl x
    refine ⟨|C| + |C'|, fun g hg => ?_⟩
    have := (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
      fun p hp => linOnSm_Rder (hl p hp)).add φ h.smooth ψ h'.smooth
    rw [this, Pi.add_apply, add_mul]
    have h0 := normInf_nonneg (θ := θ) g
    refine (norm_add_le _ _).trans (add_le_add ((hC g hg).trans ?_) ((hC' g hg).trans ?_))
    · exact mul_le_mul (le_abs_self _) (hM g).1 (pow_nonneg h0 _) (abs_nonneg _)
    · exact mul_le_mul (le_abs_self _) (hM g).2 (pow_nonneg h0 _) (abs_nonneg _)

theorem mem_AFs_iff : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ),
    φ ∈ AFs θ V ↔ IsAutFunSm θ V φ := by
  intro D θ _ V φ
  refine ⟨fun h => ?_, fun h => Submodule.subset_span h⟩
  induction h using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact isAutFunSm_zero θ V
  | add x y _ _ hx hy => exact isAutFunSm_add hx hy
  | smul c x _ hx => exact isAutFunSm_smul c hx

end GlobalTheory.Mem.AutSpace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceModelSum

open GlobalTheory.PlaceModel

theorem smul_tmul_one {F A E : Type} [Field F] [CommRing A] [CommRing E] [Algebra F A] [Algebra F E]
    (t : F) (a : A) : (t • a) ⊗ₜ[F] (1 : E) = a ⊗ₜ[F] algebraMap F E t := by
  rw [TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

theorem trace_laws {R : Type} [CommRing R] {e c e' c' : R} (h1 : e * e = e) (c1 : c * c = c) (h2 : e * c = 0)
    (h1' : e' * e' = e') (c1' : c' * c' = c') (h2' : e' * c' = 0) :
    (e * e' + c * c') * (e * e' + c * c') = e * e' + c * c' ∧ (e + c) * (e * e' + c * c') = e * e' + c * c' ∧
      (e' + c') * (e * e' + c * c') = e * e' + c * c' ∧ (0 = e * e' + c * c' → e * e' = 0) ∧
      (e + c = e * e' + c * c' → e' + c' = e * e' + c * c' → e = e') :=
  ⟨by linear_combination (e' * e') * h1 + e * h1' + (c' * c') * c1 + c * c1' + (2 * e' * c') * h2,
    by linear_combination e' * h1 + c' * c1 + (e' + c') * h2,
    by linear_combination e * h1' + c * c1' + (e + c) * h2',
    fun ht => by linear_combination (-e) * ht - e' * h1 - c' * h2,
    fun b1 b2 => by
      linear_combination e * b1 - e' * b2 - h1 - h2 + h1' + h2' + e' * h1 + c' * h2 - e * h1' - c * h2'⟩

theorem eq_or_orth {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (hinj : Function.Injective ι)
    {e c e' c' : R} {ε ε' t : A} (h1 : e * e = e) (c1 : c * c = c) (h2 : e * c = 0)
    (h1' : e' * e' = e') (c1' : c' * c' = c') (h2' : e' * c' = 0) (h3 : e + c = ι ε) (h3' : e' + c' = ι ε')
    (ht : ι t = e * e' + c * c') (p : t * t = t → ε * t = t → t = 0 ∨ t = ε)
    (p' : t * t = t → ε' * t = t → t = 0 ∨ t = ε') : e = e' ∨ e * e' = 0 := by
  obtain ⟨k1, k2, k3, k4, k5⟩ := trace_laws h1 c1 h2 h1' c1' h2'
  rw [← ht] at k1 k2 k3 k4 k5
  rw [h3] at k2 k5
  rw [h3'] at k3 k5
  have tt : t * t = t := hinj (by rw [map_mul]; exact k1)
  have t1 : ε * t = t := hinj (by rw [map_mul]; exact k2)
  have t2 : ε' * t = t := hinj (by rw [map_mul]; exact k3)
  by_cases h0 : t = 0
  · exact Or.inr (k4 (by rw [h0, map_zero]))
  · exact Or.inl (k5 (by rw [← (p tt t1).resolve_left h0]) (by rw [← (p' tt t2).resolve_left h0]))

variable {D : D7}

theorem exists_add_conj (a : AE D) : ∃ t : AF D.host.F, algebraMap (AF D.host.F) (AE D) t = a + cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [RingHom.map_zero, RingHom.map_zero, add_zero]⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add, RingHom.map_add, hs, ht]; ring⟩
  | tmul a x =>
    have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
    obtain ⟨t, ht⟩ : ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
      apply (D.sp.cm.fixed _).1
      change D.sp.cm.sig _ = _
      rw [map_add, hσ, add_comm]
    refine ⟨t • a, ?_⟩
    change (t • a) ⊗ₜ[D.host.F] (1 : D.host.E) = a ⊗ₜ[D.host.F] x + a ⊗ₜ[D.host.F] D.sp.cm.sig x
    rw [← TensorProduct.tmul_add, ← ht, smul_tmul_one]

theorem eq_zero_or_eq_of_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε t : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (ht : t * t = t) (hεt : ε * t = t) : t = 0 ∨ t = ε := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  have e1 : t.1 = 0 := by
    have : (0 : Ainf D.host.F) * t.1 = t.1 := congrArg Prod.fst hεt
    rw [← this, zero_mul]
  have e2 : α * t.2 = t.2 := congrArg Prod.snd hεt
  have e3 : t.2 * t.2 = t.2 := congrArg Prod.snd ht
  have e4 : ∀ w, w ≠ v → evalV D.host.F w t.2 = 0 := fun w hw => by rw [← e2, map_mul, h0 w hw, zero_mul]
  have e5 : evalV D.host.F v t.2 * (evalV D.host.F v t.2 - 1) = 0 := by
    rw [mul_sub, ← map_mul, e3, mul_one, sub_self]
  have ext : ∀ β : Af D.host.F, (∀ w, evalV D.host.F w t.2 = evalV D.host.F w β) → t = pairA D.host.F 0 β :=
    fun β h => Prod.ext e1 (RestrictedProduct.ext _ _ h)
  rcases mul_eq_zero.1 e5 with h | h
  · refine Or.inl (ext 0 fun w => ?_)
    rw [map_zero]
    by_cases hw : w = v
    · rw [hw, h]
    · exact e4 w hw
  · refine Or.inr (ext α fun w => ?_)
    by_cases hw : w = v
    · rw [hw, h1, sub_eq_zero.1 h]
    · rw [e4 w hw, h0 w hw]

theorem eq_or_mul_eq_zero {e e' : AE D} (he : IsSplitIdem D e) (he' : IsSplitIdem D e') : e = e' ∨ e * e' = 0 := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  obtain ⟨h1', h2', v', ε', hε', h3'⟩ := he'
  have hinj : Function.Injective (algebraMap (AF D.host.F) (AE D)) :=
    Algebra.TensorProduct.includeLeft_injective (S := D.host.F) (algebraMap D.host.F D.host.E).injective
  have c1 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have c1' : cA D e' * cA D e' = cA D e' := by rw [← map_mul, h1']
  obtain ⟨t, ht⟩ := exists_add_conj (e * e')
  rw [RingHom.map_mul] at ht
  exact eq_or_orth _ hinj h1 c1 h2 h1' c1' h2' h3 h3' ht (eq_zero_or_eq_of_placeIdem hε)
    (eq_zero_or_eq_of_placeIdem hε')

theorem isSplitIdem_cA {e : AE D} (he : IsSplitIdem D e) : IsSplitIdem D (cA D e) := by
  obtain ⟨h1, h2, v, ε, hε, h3⟩ := he
  exact ⟨by rw [← map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩

def IsOrthSum (e : AE D) : Prop :=
  ∃ (ι : Type) (P : Finset ι) (es : ι → AE D), (∀ i ∈ P, IsSplitIdem D (es i)) ∧
    (∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0) ∧ e = ∑ i ∈ P, es i

theorem isOrthSum_of_isIdemSum {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    IsOrthSum e := by
  obtain ⟨⟨es, h1, h2⟩, -⟩ := h
  refine ⟨_, P, es, fun i hi => (h1 i hi).1, fun i hi j hj hij => ?_, h2⟩
  refine (eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h => hij ?_
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [(h1 i hi).2 x hx, (h1 j hj).2 x hx, h]

theorem IsOrthSum.conj {e : AE D} (h : IsOrthSum e) : IsOrthSum (cA D e) := by
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := h
  exact ⟨ι, P, fun i => cA D (es i), fun i hi => isSplitIdem_cA (h1 i hi),
    fun i hi j hj hij => by rw [← map_mul, h2 i hi j hj hij, map_zero], map_sum _ _ _⟩

theorem mul_sum_orth {ι : Type} {P : Finset ι} {es : ι → AE D} (h1 : ∀ i ∈ P, IsSplitIdem D (es i))
    (h2 : ∀ i ∈ P, ∀ j ∈ P, j ≠ i → es i * es j = 0) {i : ι} (hi : i ∈ P) : es i * ∑ j ∈ P, es j = es i := by
  rw [Finset.mul_sum, Finset.sum_eq_single_of_mem i hi (h2 i hi), (h1 i hi).1]

theorem IsOrthSum.idem {e : AE D} (h : IsOrthSum e) : e * e = e := by
  obtain ⟨ι, P, es, h1, h2, rfl⟩ := h
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => mul_sum_orth h1 h2 hi

theorem infPart_split {e : AE D} (he : IsSplitIdem D e) : infPart D e = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨β, rfl, -⟩, h3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have : e = (e + cA D e) * e := by linear_combination -h1 - h2
  rw [this, h3, map_mul, h0, zero_mul]

theorem IsOrthSum.infPart_eq {e : AE D} (h : IsOrthSum e) : infPart D e = 0 := by
  obtain ⟨ι, P, es, h1, -, rfl⟩ := h
  exact Finset.sum_induction _ (fun y => infPart D y = 0)
    (fun x y hx hy => by rw [RingHom.map_add, hx, hy, add_zero]) (RingHom.map_zero _) fun i hi => infPart_split (h1 i hi)

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem idem_smul_latO {e : AE D} (he : e * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    e • u ∈ latO S T LS LT fun _ => True :=
  GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])) u hu

theorem idem_smul_half {e : AE D} (he : e * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    e • u ∈ (latO S T LS LT fun _ => True) ⊓ half S T e :=
  AddSubgroup.mem_inf.2 ⟨idem_smul_latO he hu, by rw [mem_half, smul_smul, he]⟩

theorem IsOrthSum.infPart_half {e : AE D} (h : IsOrthSum e) {u : WO S T} (hu : u ∈ half S T e) :
    u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, ← (isHalf_iff S T).2 hu i j, map_mul, h.infPart_eq, zero_mul]
  rfl

theorem IsOrthSum.heisO_eq {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} (h : IsOrthSum e) (hec : cA D e * e = 0)
    {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) f) (u : WO S T)
    (hu : u ∈ (latO S T LS LT fun _ => True) ⊓ half S T e) : heisO ψ S T u f = f := by
  obtain ⟨ι, P, es, h1, h2, he⟩ := h
  have e1 : u = ∑ i ∈ P, es i • u := by rw [← Finset.sum_smul, ← he, (mem_half S T).1 hu.2]
  have key : (∑ i ∈ P, es i • u) ∈ half S T e ∧ heisL S T ψ (∑ i ∈ P, es i • u) f = f := by
    refine Finset.sum_induction _ (fun y => y ∈ half S T e ∧ heisL S T ψ y f = f) (fun x y hx hy => ?_) ?_
      fun i hi => ?_
    · exact ⟨add_mem hx.1 hy.1, by rw [← heisL_half S T ψ hec x hx.1 y hy.1, hy.2, hx.2]⟩
    · exact ⟨zero_mem _, GlobalTheory.LatVac.heisO_zero ψ f⟩
    · have := idem_smul_half (h1 i hi).1 hu.1
      refine ⟨?_, hf.2 _ (h1 i hi) _ this.1 ((isHalf_iff S T).2 this.2)⟩
      rw [mem_half, smul_smul, mul_comm, he, mul_sum_orth h1 h2 hi]
  rw [← e1] at key
  exact key.2

theorem IsOrthSum.mem_of_dual {ψ : AddChar (AF D.host.F) ℂ}
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ (latO S T LS LT fun _ => True) ↔
      ∀ u' ∈ (latO S T LS LT fun _ => True), ψ (symplO S T u u') = 1))
    {a : AE D} (ha : IsOrthSum a) (x : WO S T) (hx : x ∈ half S T a)
    (h : ∀ y ∈ (latO S T LS LT fun _ => True) ⊓ half S T (cA D a), ψ (symplO S T x y) = 1) :
    x ∈ (latO S T LS LT fun _ => True) ⊓ half S T a :=
  AddSubgroup.mem_inf.2 ⟨(hdual x (ha.infPart_half hx)).2 fun u hu => by
    have := h _ (idem_smul_half ha.conj.idem hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this, hx⟩

theorem IsOrthSum.exists_model {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {e : AE D} (he : IsOrthSum e) (hec : e * cA D e = 0)
    {f₀ : WO S T → ℂ} (hvac : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm := by
  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  refine exists_placeModel ψ hec _ (fun u hu y hy => (hdual u (he.infPart_half hu.2)).1 hu.1 y hy.1)
    (he.mem_of_dual hdual) (fun y hy h => ?_) (fun k hk => ?_) one_ne_zero f₀
    (he.heisO_eq (by rw [mul_comm, hec]) hvac) (he.conj.heisO_eq (by rw [cA_cA, hec]) hvac)
  · refine he.conj.mem_of_dual hdual y hy fun u hu => ?_
    rw [cA_cA] at hu
    rw [symplO_skew, AddChar.map_neg_eq_inv, h u hu, inv_one]
  · obtain ⟨R, hR, h⟩ := hfin k hk
    refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
    obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
    refine ⟨_, ⟨r, hr, rfl⟩, e • u, idem_smul_half he.idem hu, ?_⟩
    have := (mem_half S T).1 ht.2
    rw [← this, htr, smul_add, smul_comm e k u]

theorem placeModelExistsSum : ∀ D : D7, PlaceModelExistsSum D := by
  intro D ψ hψ S T ΛS ΛT hS hT P e he f₀ _ hvac
  have h := isOrthSum_of_isIdemSum he
  exact ⟨h.exists_model hψ hS hT he.2 hvac,
    h.conj.exists_model hψ hS hT (by rw [cA_cA, mul_comm, he.2]) hvac⟩

end GlobalTheory.PlaceModelSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueInfFam
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.InfFamUnique

theorem existsUnique_infFam : ∀ D : D7, ∃! θ : InfF D, IsInfFam θ := by
  intro D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  exact ⟨θ, hθ, fun θ' h' => funext fun ρ =>
    GlobalTheory.Mem.VolEmb.infEmb_unique (tauE D ρ) (θ' ρ) (θ ρ) (h' ρ) (hθ ρ)⟩

end GlobalTheory.Mem.InfFamUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreMeasuresTransportUnitarySimilitudeStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreMeasures_transport_unitary_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J J₂ : Matrix (Fin M) (Fin M) E) (lam : Measure (R ⊗[F] E)) (ν : Measure R) (β c : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)), lam.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsUnit g.det → IsUnit c → (∀ z, qR R σ J₂ (g.mulVec z) = c * qR R σ J z) → FibAt R σ J (tupMeas lam 1 M) ν β m → FibAt R σ J₂ (tupMeas lam 1 M) ν (c * β) ((modu (R ⊗[F] E) g.det * (modu R c)⁻¹) • m.map (lrAct g 1)) := by
  first | exact @GlobalTheory.GaugeEx.fibAt_similitude | exact GlobalTheory.GaugeEx.fibAt_similitude | (intros; apply GlobalTheory.GaugeEx.fibAt_similitude <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerGaussianVectorsFockSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_gaussianVectors_fockSpace : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A B : Matrix (Fin P) (Fin Q) ℂ) (x y : Ix P Q → ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → ∀ v w : F.H, HasCoeff F v (expPS (gaussPoly A x)) → HasCoeff F w (expPS (gaussPoly B y)) → let a : Fin P → ℂ := fun i => star (x (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (x (Sum.inr j)); let c : Fin P → ℂ := fun i => y (Sum.inl i); let d : Fin Q → ℂ := fun j => y (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; inner ℂ v w = ((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c) := by
  first | exact @GlobalTheory.GaussInner.inner_gauss_gauss | exact GlobalTheory.GaussInner.inner_gauss_gauss | (intros; apply GlobalTheory.GaussInner.inner_gauss_gauss <;> assumption)
end

