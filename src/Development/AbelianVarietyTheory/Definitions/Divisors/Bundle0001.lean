import Mathlib

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.AltPullApply
section
noncomputable section

namespace GlobalTheory.KS

variable {O : Type} [Ring O] {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

def matAct (ρ : O →+* Module.End R V) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : (Fin m → V) →ₗ[R] (Fin m → V) :=
  LinearMap.pi fun i => ∑ j, ρ (M i j) ∘ₗ LinearMap.proj j

theorem matAct_apply (ρ : O →+* Module.End R V) {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (x : Fin m → V) (i : Fin m) :
    matAct ρ M x i = ∑ j, ρ (M i j) (x j) := by
  simp [matAct]

abbrev Alt (R : Type) [CommRing R] (W : Type) [AddCommGroup W] [Module R W] (E : Type) [CommRing E] [Algebra R E] (q : ℕ) :
    Type := W [⋀^Fin q]→ₗ[R] E

variable {E : Type} [CommRing E] [Algebra R E]

def altPull (E : Type) [CommRing E] [Algebra R E] {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (u : W' →ₗ[R] W) (q : ℕ) : Alt R W E q →ₗ[E] Alt R W' E q where
  toFun f := f.compLinearMap u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem altPull_apply {W W' : Type} [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (u : W' →ₗ[R] W) (q : ℕ) (f : Alt R W E q) (x : Fin q → W') : altPull E u q f x = f fun i => u (x i) := rfl

def altOp (ρ : O →+* Module.End R V) {m : ℕ} (ε : Matrix (Fin m) (Fin m) O →₀ E) (q : ℕ) :
    Module.End E (Alt R (Fin m → V) E q) :=
  ε.sum fun M c => c • altPull E (matAct ρ M) q

structure IsCut (ρ : O →+* Module.End R V) {m : ℕ} (ε : Matrix (Fin m) (Fin m) O →₀ E) (k : ℕ) : Prop where
  idem : altOp ρ ε k * altOp ρ ε k = altOp ρ ε k
  zero : ∀ q, q ≠ k → altOp ρ ε q = 0

variable {Γ : Type} [Group Γ]

def altRep (E : Type) [CommRing E] [Algebra R E] {W : Type} [AddCommGroup W] [Module R W] (σ : Representation R Γ W) (q : ℕ) :
    Representation E Γ (Alt R W E q) where
  toFun γ := altPull E (σ γ⁻¹) q
  map_one' := by
    ext f x
    simp [altPull]
  map_mul' γ δ := by
    ext f x
    simp [Module.End.mul_apply]

def powRep (σ : Representation R Γ V) (m : ℕ) : Representation R Γ (Fin m → V) where
  toFun γ := LinearMap.pi fun i => σ γ ∘ₗ LinearMap.proj i
  map_one' := by
    ext x i
    simp
  map_mul' γ δ := by
    ext x i
    simp

theorem altOp_comm (ρ : O →+* Module.End R V) (σ : Representation R Γ V) (hσ : ∀ γ b, σ γ * ρ b = ρ b * σ γ) {m : ℕ}
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (q : ℕ) (γ : Γ) :
    altRep E (powRep σ m) q γ * altOp ρ ε q = altOp ρ ε q * altRep E (powRep σ m) q γ := by
  have h : ∀ (M : Matrix (Fin m) (Fin m) O) (x : Fin m → V),
      matAct ρ M (powRep σ m γ⁻¹ x) = powRep σ m γ⁻¹ (matAct ρ M x) := by
    intro M x
    funext i
    have h1 : ∀ b y, σ γ⁻¹ (ρ b y) = ρ b (σ γ⁻¹ y) := fun b y => LinearMap.congr_fun (hσ γ⁻¹ b) y
    simp [matAct_apply, powRep, map_sum, h1]
  unfold altOp Finsupp.sum
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  ext f x
  change f (fun i => matAct ρ M (powRep σ m γ⁻¹ (x i))) = f (fun i => powRep σ m γ⁻¹ (matAct ρ M (x i)))
  simp only [h]

def xiRep (ρ : O →+* Module.End R V) (σ : Representation R Γ V) (hσ : ∀ γ b, σ γ * ρ b = ρ b * σ γ) {m : ℕ}
    (ε : Matrix (Fin m) (Fin m) O →₀ E) (k : ℕ) : Representation E Γ (LinearMap.range (altOp ρ ε k)) :=
  (altRep E (powRep σ m) k).subrepresentation _ fun γ => by
    rintro _ ⟨f, rfl⟩
    exact ⟨altRep E (powRep σ m) k γ f, (LinearMap.congr_fun (altOp_comm ρ σ hσ ε k γ) f).symm⟩

example (ρ : O →+* Module.End R V) : IsCut ρ (Finsupp.single (1 : Matrix (Fin 0) (Fin 0) O) (1 : E)) 0 where
  idem := by
    have : altOp ρ (Finsupp.single (1 : Matrix (Fin 0) (Fin 0) O) (1 : E)) 0 = 1 := by
      ext f x
      simp only [altOp, zero_smul, Finsupp.sum_single_index, one_smul, altPull_apply, Module.End.one_apply]
      exact congrArg f (Subsingleton.elim _ _)
    rw [this, one_mul]
  zero q hq := by
    ext f x
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    simp only [altOp, zero_smul, Finsupp.sum_single_index, one_smul, altPull, LinearMap.coe_mk, AddHom.coe_mk,
      AlternatingMap.compLinearMap_apply, LinearMap.zero_apply, AlternatingMap.zero_apply]
    exact f.map_coord_zero 0 (Subsingleton.elim _ _)

end GlobalTheory.KS
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ChainComp
section
noncomputable section

namespace GlobalTheory.SSG

def stdStep {C : Type} [CommRing C] (ϖ : C) {n : ℕ} (i : Fin n) : (Fin n → C) →ₗ[C] (Fin n → C) where
  toFun v j := if j = i then ϖ * v j else v j
  map_add' v w := by
    funext j
    by_cases h : j = i <;> simp [h, mul_add]
  map_smul' c v := by
    funext j
    by_cases h : j = i <;> simp [h, smul_eq_mul, mul_left_comm]

structure LMPoint (C : Type) [CommRing C] (ϖ : C) (n : ℕ) [NeZero n] where

  ℓ : Fin n → Submodule C (Fin n → C)

  line : ∀ i, ∃ v : Fin n → C, ℓ i = Submodule.span C {v} ∧ Ideal.span (Set.range v) = ⊤

  step : ∀ i, (ℓ i).map (stdStep ϖ i) ≤ ℓ (i + 1)

def LMPoint.worst {C : Type} [CommRing C] (n : ℕ) [NeZero n] : LMPoint C 0 n where
  ℓ i := Submodule.span C {Pi.single i 1}
  line i := ⟨Pi.single i 1, rfl, by
    rw [eq_top_iff, ← Ideal.span_singleton_one]
    exact Ideal.span_mono (by rintro _ rfl; exact ⟨i, by simp⟩)⟩
  step i := by
    rw [Submodule.map_span, Set.image_singleton]
    have : stdStep (0 : C) i (Pi.single i 1) = 0 := by
      funext j; by_cases h : j = i <;> simp [stdStep, h]
    rw [this, Submodule.span_singleton_eq_bot.2 rfl]
    exact bot_le

def chainComp {C : Type} [CommRing C] {n : ℕ} {M : Fin (n + 1) → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module C (M i)]
    (f : ∀ i : Fin n, M i.castSucc →ₗ[C] M i.succ) : ∀ i : Fin (n + 1), M 0 →ₗ[C] M i :=
  Fin.induction LinearMap.id (fun i g => f i ∘ₗ g)

end GlobalTheory.SSG

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer

variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E'']

def holSub (W : Opens E) : Subalgebra ℂ (W → ℂ) where
  carrier := {f | ∃ F : E → ℂ, AnalyticOnNhd ℂ F W ∧ ∀ p : W, f p = F p}
  mul_mem' := by
    rintro f g ⟨F, hF, e⟩ ⟨G, hG, e'⟩
    exact ⟨fun p ↦ F p * G p, hF.mul hG, fun p ↦ by simp [e, e']⟩
  add_mem' := by
    rintro f g ⟨F, hF, e⟩ ⟨G, hG, e'⟩
    exact ⟨fun p ↦ F p + G p, hF.add hG, fun p ↦ by simp [e, e']⟩
  algebraMap_mem' c := ⟨fun _ ↦ c, analyticOnNhd_const, fun _ ↦ rfl⟩

abbrev Hol (W : Opens E) : Type := holSub W

namespace Hol

variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''}

open Classical in

def fn (f : Hol W) (p : E) : ℂ := if h : p ∈ W then f.1 ⟨p, h⟩ else 0

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_of_mem (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (h : p ∈ W) :
    f.fn p = f.1 ⟨p, h⟩ := by
  simp [_root_.GlobalTheory.AnPer.Hol.fn, h]

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.ext_fn {f g : _root_.GlobalTheory.AnPer.Hol W}
    (h : ∀ p ∈ W, f.fn p = g.fn p) : f = g := by
  refine Subtype.ext (funext fun p ↦ ?_)
  have hp := h p p.2
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f p.2, _root_.GlobalTheory.AnPer.Hol.fn_of_mem g p.2] at hp
  exact hp

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.analytic (f : _root_.GlobalTheory.AnPer.Hol W) :
    AnalyticOnNhd ℂ f.fn W := by
  obtain ⟨F, hF, e⟩ : ∃ F : E → ℂ, AnalyticOnNhd ℂ F W ∧ ∀ p : W, f.1 p = F p := f.2
  intro p hp
  refine (hF p hp).congr ?_
  filter_upwards [W.isOpen.mem_nhds hp] with q hq
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f hq, e]

def mk (F : E → ℂ) (h : AnalyticOnNhd ℂ F W) : Hol W := ⟨fun p ↦ F p, F, h, fun _ ↦ rfl⟩

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_mk (F : E → ℂ) (h : AnalyticOnNhd ℂ F W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.mk F h).fn p = F p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

def ev (p : E) (hp : p ∈ W) : Hol W →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : W ↦ ℂ) ⟨p, hp⟩).comp (holSub W).val

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.ev_apply (p : E) (hp : p ∈ W) (f : _root_.GlobalTheory.AnPer.Hol W) :
    _root_.GlobalTheory.AnPer.Hol.ev p hp f = f.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_add (f g : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (f + g).fn p = f.fn p + g.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_mul (f g : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (f * g).fn p = f.fn p * g.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_smul (c : ℂ) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (c • f).fn p = c * f.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_algebraMap (c : ℂ) {p : E} (hp : p ∈ W) :
    (algebraMap ℂ (_root_.GlobalTheory.AnPer.Hol W) c).fn p = c := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

def comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W') (h : ∀ p ∈ W', Φ p ∈ W) : Hol W →ₐ[ℂ] Hol W' where
  toFun f := ⟨fun p ↦ f.1 ⟨Φ p, h p p.2⟩, fun p ↦ f.fn (Φ p), f.analytic.comp hΦ h,
    fun p ↦ (fn_of_mem f _).symm⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W') (h : ∀ p ∈ W', Φ p ∈ W)
    (f : _root_.GlobalTheory.AnPer.Hol W) {p : E'} (hp : p ∈ W') :
    (_root_.GlobalTheory.AnPer.Hol.comap Φ hΦ h f).fn p = f.fn (Φ p) := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  exact (_root_.GlobalTheory.AnPer.Hol.fn_of_mem f (h p hp)).symm

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fderiv_fn_congr (f : _root_.GlobalTheory.AnPer.Hol W) {F : E → ℂ}
    (e : ∀ q ∈ W, f.fn q = F q) {p : E} (hp : p ∈ W) :
    fderiv ℂ f.fn p = fderiv ℂ F p := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [W.isOpen.mem_nhds hp] with q hq using e q hq

def derFun (v : E) (f : Hol W) : Hol W :=
  mk (fun p ↦ fderiv ℂ f.fn p v) fun p hp ↦
    ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp (f.analytic p hp).fderiv

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_derFun (v : E) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.derFun v f).fn p =
      fderiv ℂ f.fn p v :=
  _root_.GlobalTheory.AnPer.Hol.fn_mk _ _ hp

def der (v : E) : Derivation ℂ (Hol W) (Hol W) :=
  Derivation.mk'
    { toFun := derFun v
      map_add' f g := ext_fn fun p hp ↦ by
        rw [fn_add _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
          fderiv_fn_congr (f + g) (F := fun q ↦ f.fn q + g.fn q) (fun q hq ↦ fn_add f g hq) hp,
          fderiv_fun_add (f.analytic p hp).differentiableAt (g.analytic p hp).differentiableAt]
        rfl
      map_smul' c f := ext_fn fun p hp ↦ by
        rw [RingHom.id_apply, fn_smul _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
          fderiv_fn_congr (c • f) (F := fun q ↦ c * f.fn q) (fun q hq ↦ fn_smul c f hq) hp,
          fderiv_const_mul (f.analytic p hp).differentiableAt]
        rfl }
    fun f g ↦ ext_fn fun p hp ↦ by
      change (derFun v (f * g)).fn p = (f * derFun v g + g * derFun v f).fn p
      rw [fn_add _ _ hp, fn_mul _ _ hp, fn_mul _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
        fderiv_fn_congr (f * g) (F := fun q ↦ f.fn q * g.fn q) (fun q hq ↦ fn_mul f g hq) hp,
        fderiv_fun_mul (f.analytic p hp).differentiableAt (g.analytic p hp).differentiableAt]
      rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_der (v : E) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.der v f).fn p =
      fderiv ℂ f.fn p v :=
  _root_.GlobalTheory.AnPer.Hol.fn_derFun v f hp

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in

theorem _root_.GlobalTheory.AnPer.Hol.fn_der_comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W')
    (h : ∀ p ∈ W', Φ p ∈ W) (v : E') (f : _root_.GlobalTheory.AnPer.Hol W) {p : E'} (hp : p ∈ W') :
    (_root_.GlobalTheory.AnPer.Hol.der v (_root_.GlobalTheory.AnPer.Hol.comap Φ hΦ h f)).fn p =
      fderiv ℂ f.fn (Φ p) (fderiv ℂ Φ p v) := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_der v _ hp,
    _root_.GlobalTheory.AnPer.Hol.fderiv_fn_congr _ (F := f.fn ∘ Φ)
      (fun q hq ↦ _root_.GlobalTheory.AnPer.Hol.fn_comap Φ hΦ h f hq) hp,
    fderiv_comp p (f.analytic (Φ p) (h p hp)).differentiableAt
      (hΦ p hp).differentiableAt]
  rfl

end Hol

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FormalModule
section
noncomputable section

open PowerSeries

namespace GlobalTheory.FOM

section Basic

variable {R : Type*} [CommRing R]

abbrev atX (f : PowerSeries R) : MvPowerSeries (Fin 2) R := f.subst (MvPowerSeries.X (0 : Fin 2))

abbrev atY (f : PowerSeries R) : MvPowerSeries (Fin 2) R := f.subst (MvPowerSeries.X (1 : Fin 2))

def IsHom (F G : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ f.subst F.toPowerSeries = G.toPowerSeries.subst ![atX f, atY f]

def addF (F : FormalGroup R) (f g : PowerSeries R) : PowerSeries R :=
  F.toPowerSeries.subst ![f, g]

end Basic

structure FormalModule (O : Type*) [CommRing O] (R : Type*) [CommRing R] [Algebra O R] where
  F : FormalGroup R
  comm : F.IsComm
  act : O → PowerSeries R
  act_hom : ∀ a, IsHom F F (act a)
  act_lin : ∀ a, coeff 1 (act a) = algebraMap O R a
  act_one : act 1 = X
  act_mul : ∀ a b, act (a * b) = (act a).subst (act b)
  act_add : ∀ a b, act (a + b) = addF F (act a) (act b)

variable {O : Type*} [CommRing O] {R : Type*} [CommRing R] [Algebra O R]

def IsModHom (M N : FormalModule O R) (f : PowerSeries R) : Prop :=
  IsHom M.F N.F f ∧ ∀ a : O, f.subst (M.act a) = (N.act a).subst f

def WDeg (m : Ideal R) (f : PowerSeries R) (d : ℕ) : Prop :=
  (∀ n < d, coeff n f ∈ m) ∧ IsUnit (coeff d f)

def HasHeight (m : Ideal R) (M : FormalModule O R) (ϖ : O) (q h : ℕ) : Prop :=
  WDeg m (M.act ϖ) (q ^ h)

def chainComp {h : ℕ} (f : Fin h → PowerSeries R) : PowerSeries R :=
  (List.finRange h).foldl (fun g i => (f i).subst g) X

structure IsoChain (m : Ideal R) (ϖ : O) (q h : ℕ) where
  M : Fin (h + 1) → FormalModule O R
  f : Fin h → PowerSeries R
  hom : ∀ i : Fin h, IsModHom (M i.castSucc) (M i.succ) (f i)
  deg : ∀ i : Fin h, WDeg m (f i) q
  closed : M (Fin.last h) = M 0
  comp : chainComp f = (M 0).act ϖ

end GlobalTheory.FOM

namespace GlobalTheory.FOM

section Image

variable {O : Type*} [CommRing O] {R S : Type*} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]

def IsImage (φ : R →+* S) (M : FormalModule O R) (N : FormalModule O S) : Prop :=
  N.F.toPowerSeries = MvPowerSeries.map φ M.F.toPowerSeries ∧
    ∀ a : O, N.act a = PowerSeries.map φ (M.act a)

def IsChainImage {mR : Ideal R} {mS : Ideal S} {ϖ : O} {q h : ℕ} (φ : R →+* S)
    (C : IsoChain (O := O) mR ϖ q h) (D : IsoChain (O := O) mS ϖ q h) : Prop :=
  (∀ i, IsImage φ (C.M i) (D.M i)) ∧ ∀ i, D.f i = PowerSeries.map φ (C.f i)

def IsStar (m : Ideal R) (u : PowerSeries R) : Prop :=
  ∀ n : ℕ, coeff n u - coeff n (X : PowerSeries R) ∈ m

def StarIso {m : Ideal R} {ϖ : O} {q h : ℕ} (C D : IsoChain (O := O) m ϖ q h) : Prop :=
  ∃ u : Fin (h + 1) → PowerSeries R, (∀ i, IsStar m (u i)) ∧ (∀ i, IsModHom (C.M i) (D.M i) (u i)) ∧
    u (Fin.last h) = u 0 ∧ ∀ i : Fin h, (D.f i).subst (u i.castSucc) = (u i.succ).subst (C.f i)

end Image

section Ring

variable (Ob : Type*) [CommRing Ob]

def relIdeal (h : ℕ) (w : Ob) : Ideal (MvPowerSeries (Fin h) Ob) :=
  Ideal.span {(∏ i : Fin h, MvPowerSeries.X i) - MvPowerSeries.C w}

abbrev IwRing (h : ℕ) (w : Ob) : Type _ := MvPowerSeries (Fin h) Ob ⧸ relIdeal Ob h w

variable [IsLocalRing Ob]

def iwRed (h : ℕ) (hh : 1 ≤ h) (w : Ob) (hw : w ∈ IsLocalRing.maximalIdeal Ob) :
    IwRing Ob h w →+* IsLocalRing.ResidueField Ob :=
  Ideal.Quotient.lift (relIdeal Ob h w) ((IsLocalRing.residue Ob).comp MvPowerSeries.constantCoeff) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have h0 : MvPowerSeries.constantCoeff (∏ i : Fin h, (MvPowerSeries.X i : MvPowerSeries (Fin h) Ob)) = 0 := by
      rw [map_prod]
      exact Finset.prod_eq_zero (i := ⟨0, hh⟩) (Finset.mem_univ _) (by simp)
    simp [map_mul, map_sub, h0, (IsLocalRing.residue_eq_zero_iff w).mpr hw]
    exact Or.inr (by omega))

def iwMax (h : ℕ) (hh : 1 ≤ h) (w : Ob) (hw : w ∈ IsLocalRing.maximalIdeal Ob) : Ideal (IwRing Ob h w) :=
  RingHom.ker (iwRed Ob h hh w hw)

end Ring

end GlobalTheory.FOM
end
end

