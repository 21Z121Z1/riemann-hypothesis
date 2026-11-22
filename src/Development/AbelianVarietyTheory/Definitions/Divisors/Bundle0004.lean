import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

section Abstract

variable {k : Type} [Field k] {M M' M₁ M₂ M₃ : Type} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]

structure Cx (k M : Type) [Field k] [AddCommGroup M] [Module k M] where

  C : ℤ → Submodule k M

  D : M →ₗ[k] M

namespace Cx

def IsCx (K : Cx k M) : Prop := ∀ n, ∀ a ∈ K.C n, K.D a ∈ K.C (n + 1) ∧ K.D (K.D a) = 0

def Z (K : Cx k M) (n : ℤ) : Submodule k M := K.C n ⊓ LinearMap.ker K.D

def B (K : Cx k M) (n : ℤ) : Submodule k M := (K.C (n - 1)).map K.D

abbrev H (K : Cx k M) (n : ℤ) : Type := K.Z n ⧸ (K.B n).submoduleOf (K.Z n)

end Cx

def Adj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N : ℤ) : Prop :=
  ∀ n, ∃ ε : ℤˣ, ∀ a ∈ K.C n, ∀ b ∈ L.C (N - n - 1), β (K.D a) b = ε • β a (L.D b)

def Inj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N n : ℤ) : Prop :=
  ∀ a ∈ K.Z n, (∀ b ∈ L.Z (N - n), β a b = 0) → a ∈ K.B n

def Surj (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N n : ℤ) : Prop :=
  ∀ φ : Module.Dual k M', (∀ b ∈ L.B (N - n), φ b = 0) → ∃ a ∈ K.Z n, ∀ b ∈ L.Z (N - n), φ b = β a b

def Perf (K : Cx k M) (L : Cx k M') (β : M →ₗ[k] M' →ₗ[k] k) (N : ℤ) : Prop := ∀ n, Inj K L β N n ∧ Surj K L β N n

def IsMap (K : Cx k M) (L : Cx k M') (f : M →ₗ[k] M') : Prop := ∀ n, ∀ a ∈ K.C n, f a ∈ L.C n ∧ f (K.D a) = L.D (f a)

structure SES (K₁ : Cx k M₁) (K₂ : Cx k M₂) (K₃ : Cx k M₃) (f : M₁ →ₗ[k] M₂) (g : M₂ →ₗ[k] M₃) : Prop where
  cx₁ : K₁.IsCx
  cx₂ : K₂.IsCx
  cx₃ : K₃.IsCx
  mapf : IsMap K₁ K₂ f
  mapg : IsMap K₂ K₃ g
  inj : ∀ n, ∀ a ∈ K₁.C n, f a = 0 → a = 0
  exact : ∀ n, ∀ a ∈ K₂.C n, g a = 0 ↔ ∃ a' ∈ K₁.C n, f a' = a
  surj : ∀ n, ∀ c ∈ K₃.C n, ∃ a ∈ K₂.C n, g a = c

structure DualSES {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module k N₁] [AddCommGroup N₂] [Module k N₂] [AddCommGroup N₃] [Module k N₃]
    (K₁ : Cx k M₁) (K₂ : Cx k M₂) (K₃ : Cx k M₃) (f : M₁ →ₗ[k] M₂) (g : M₂ →ₗ[k] M₃)
    (L₁ : Cx k N₁) (L₂ : Cx k N₂) (L₃ : Cx k N₃) (f' : N₂ →ₗ[k] N₁) (g' : N₃ →ₗ[k] N₂)
    (β₁ : M₁ →ₗ[k] N₁ →ₗ[k] k) (β₂ : M₂ →ₗ[k] N₂ →ₗ[k] k) (β₃ : M₃ →ₗ[k] N₃ →ₗ[k] k) (N : ℤ) : Prop where
  left : SES K₁ K₂ K₃ f g
  right : SES L₃ L₂ L₁ g' f'
  adj : Adj K₂ L₂ β₂ N
  adjf : ∀ n, ∀ a ∈ K₁.C n, ∀ b ∈ L₂.C (N - n), β₂ (f a) b = β₁ a (f' b)
  adjg : ∀ n, ∀ a ∈ K₂.C n, ∀ b ∈ L₃.C (N - n), β₂ a (g' b) = β₃ (g a) b

def pt (k : Type) [Field k] : Cx k k := ⟨fun n => if n = 0 then ⊤ else ⊥, 0⟩

end Abstract

section Cech

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [Module k E]

variable (k ι E) in

def deltaL : (Finset ι → E) →ₗ[k] (Finset ι → E) where
  toFun := GlobalTheory.DI.delta
  map_add' a b := by
    funext t
    simp [GlobalTheory.DI.delta, Finset.sum_add_distrib]
  map_smul' r a := by
    funext t
    simp only [GlobalTheory.DI.delta, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

def cechC (F : Finset ι → Submodule k E) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s => if s.Nonempty ∧ (s.card : ℤ) = n + 1 then F s else ⊥

def cech (F : Finset ι → Submodule k E) : Cx k (Finset ι → E) := ⟨cechC F, deltaL k ι E⟩

def totD (d : E →ₗ[k] E) : (Finset ι → E) →ₗ[k] (Finset ι → E) :=
  deltaL k ι E + LinearMap.pi fun s => ((-1 : ℤ) ^ s.card) • (d ∘ₗ LinearMap.proj s)

def totC (T : ℕ → Finset ι → Submodule k E) (a b : ℕ) (n : ℤ) : Submodule k (Finset ι → E) :=
  Submodule.pi Set.univ fun s =>
    if s.Nonempty ∧ (a : ℤ) ≤ n + 1 - s.card ∧ n + 1 - s.card < b then T (n + 1 - s.card).toNat s else ⊥

def cupPair [Fintype ι] {E' : Type} [AddCommGroup E'] [Module k E'] (β : E →ₗ[k] E' →ₗ[k] k) :
    (Finset ι → E) →ₗ[k] (Finset ι → E') →ₗ[k] k :=
  ∑ j : ι, β.compl₁₂ (LinearMap.proj (Finset.univ.filter (· ≤ j))) (LinearMap.proj (Finset.univ.filter (j ≤ ·)))

end Cech

section Alg

variable {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [Ring E] [Algebra k E]

structure IsDga (sg : E →ₐ[k] E) (d : E →ₗ[k] E) : Prop where
  sg_sg : ∀ x, sg (sg x) = x
  d_sg : ∀ x, d (sg x) = -sg (d x)
  d_mul : ∀ x y, d (x * y) = d x * y + sg x * d y
  d_d : ∀ x, d (d x) = 0

def cup (sg : E →ₐ[k] E) (a b : Finset ι → E) : Finset ι → E := fun u =>
  ∑ j ∈ u, (sg ^ ((u.filter (j ≤ ·)).card - 1)) (a (u.filter (· ≤ j))) * b (u.filter (j ≤ ·))

def tsg (sg : E →ₐ[k] E) (a : Finset ι → E) : Finset ι → E := fun s => (-1 : ℤ) ^ (s.card + 1) • sg (a s)

def const (x : E) : Finset ι → E := fun s => if s.card = 1 then x else 0

def cupPow (sg : E →ₐ[k] E) (a : Finset ι → E) (m : ℕ) : Finset ι → E :=
  Nat.rec (const 1) (fun _ y => cup sg y a) m

end Alg

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
section
namespace GlobalTheory.OTY

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def jz (A : WeightedAtlas n Y ι La) (z : Y → V n) (i : ι) (y : Y) : V n →L[ℂ] V n :=
  fderiv ℂ (z ∘ (A.chart i).symm) (A.chart i y)

def jdet (A : WeightedAtlas n Y ι La) (z : Y → V n) : ι → Y → ℂ :=
  fun i y => (jz A z i y).det

structure Etale (A : WeightedAtlas n Y ι La) (U : Set Y) (z : Y → V n) : Prop where
  isOpen : IsOpen U
  holo : ∀ i, DifferentiableOn ℂ (z ∘ (A.chart i).symm)
    ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)
  det_ne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → jdet A z i y ≠ 0

def nz (A : WeightedAtlas n Y ι La) (τ : ι → Y → ℂ) : Set Y := {y | τ (A.pick y) y ≠ 0}

structure Cover (A : WeightedAtlas n Y ι La) where

  m : ℕ

  idx : Fin m → ι

  c : Fin m → V n

  r : Fin m → ℝ

  chi : Fin m → Y → ℝ
  r_pos : ∀ a, 0 < r a
  sub : ∀ a, Metric.closedBall (c a) (r a) ⊆ (A.chart (idx a)).target
  smooth : ∀ a, A.SmoothFn (chi a)
  supp : ∀ a, tsupport (chi a) ⊆
    (A.chart (idx a)).source ∩ A.chart (idx a) ⁻¹' Metric.ball (c a) (r a)
  nonneg : ∀ a y, 0 ≤ chi a y
  sum_one : ∀ y, ∑ a, chi a y = 1

def n0 (A : WeightedAtlas n Y ι La) (la : La) (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) F y) ∂A.mu

def n1 {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (F : ι → Y → ℂ) : ℝ≥0∞ :=
  ∑ a, ∫⁻ v in Metric.ball (C.c a) (C.r a), ENNReal.ofReal
    ((∑ j, ‖wdb n j (F (C.idx a) ∘ (A.chart (C.idx a)).symm) v‖ ^ 2) *
      Real.exp (-A.ph la (C.idx a) ((A.chart (C.idx a)).symm v)))

def CurvGe {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (t : ℝ) : Prop :=
  ∀ a, ∀ v ∈ Metric.ball (C.c a) (C.r a), ∀ ξ : Fin n → ℂ,
    t * ∑ j, ‖ξ j‖ ^ 2 ≤ A.leviAt (C.idx a) (A.ph la (C.idx a)) ((A.chart (C.idx a)).symm v) ξ

def glue {A : WeightedAtlas n Y ι La} (C : Cover A) (la : La) (u : Fin C.m → V n → ℂ) :
    ι → Y → ℂ :=
  fun i y => ∑ a, (C.chi a y : ℂ) * A.g (A.kap + la) i (C.idx a) y * u a (A.chart (C.idx a) y)

def wT (T x : ℝ) : ℝ := 1 / (1 + min (x ^ 2) ((T + 1) ^ 2))

def IsCut (T : ℝ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ x, x ≤ -T - 1 → θ x = 1) ∧ (∀ x, -T + 1 ≤ x → θ x = 0) ∧
    (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧ ∀ x, |deriv θ x| ≤ 3 / 4

theorem etale_empty (A : WeightedAtlas n Y ι La) (z : Y → V n) : Etale A ∅ z :=
  ⟨isOpen_empty, fun _ => by simp [differentiableOn_empty], fun _ _ h => h.elim⟩

end

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

open CategoryTheory GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in

theorem _root_.GlobalTheory.AnPer.Charts.tsze_nil {O : Type} [CommRing O] [Algebra ℂ O] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ O (Fin g → O)).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Submodule.zero_eq_bot, ← le_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [RingHom.mem_ker] at hx hy
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]

variable (K) in

@[reducible] def jet (k : K.K) : K.Obj where
  k := k
  C := TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))
  alg := ((TrivSqZeroExt.inlHom _ _).comp (K.cst k)).toAlgebra
  J := RingHom.ker (TrivSqZeroExt.fstHom ℂ (Hol (K.W k)) (Fin g → Hol (K.W k))).toRingHom
  nil := tsze_nil
  ρ := TrivSqZeroExt.inlHom _ _
  ρ_cst _ := rfl

def tszeSec {O : Type} [CommRing O] [Algebra ℂ O] (D : Fin g → Derivation ℂ O O) : O →+* TrivSqZeroExt O (Fin g → O) where
  toFun h := TrivSqZeroExt.inl h + TrivSqZeroExt.inr fun a ↦ D a h
  map_one' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_zero' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_add' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_mul' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp [mul_comm])

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in

theorem _root_.GlobalTheory.AnPer.Charts.fst_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).fst = h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in

theorem _root_.GlobalTheory.AnPer.Charts.snd_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) (a : Fin g) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).snd a = D a h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]

def jetSec (k : K.K) : Hol (K.W k) →+* TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) := tszeSec dw

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
open CategoryTheory in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} {K : _root_.GlobalTheory.AnPer.Charts F} in

theorem _root_.GlobalTheory.AnPer.Charts.tsze_expand {O : Type} [CommRing O] (h : O) (v : Fin g → O) :
    (TrivSqZeroExt.inl h + TrivSqZeroExt.inr v : TrivSqZeroExt O (Fin g → O)) = TrivSqZeroExt.inl h +
      ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) := by
  congr 1
  simp only [TrivSqZeroExt.inl_mul_inr]
  ext b
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum, Finset.sum_apply, Pi.single_apply]

def jet0 (k : K.K) : K.triv k ⟶ K.jet k := ptHom (K.jet k) (K.le_refl k)

def jet1 (k : K.K) : K.triv k ⟶ K.jet k :=
  fromTriv (K.jet k) (K.le_refl k) (jetSec k)
    (fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)))
    (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, sh_refl]
        exact tsze_expand h fun a ↦ dw a h⟩)

end GlobalTheory.AnPer.Charts
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsStrictlySemistableIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.SSG

def ChartAt {O : Type} [CommRing O] (ϖ : O) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (m r : ℕ) (_ : 1 ≤ r) (_ : r ≤ m)
    (ψ : (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ}) →+* Γ(X, U)),
    ψ.Etale ∧ ψ.comp (algebraMap O _) = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ p.appLE ⊤ U le_top).hom

end GlobalTheory.SSG

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SecMapApply
section
noncomputable section

open GlobalTheory.WeilM
open scoped Matrix

namespace GlobalTheory.LinPair

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] (c : E →ₐ[k] E)
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  [TopologicalSpace k]

def IsYInv (ψ : AddChar k ℂ) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} (d : Darboux (symp c ξ JA JB) κ)
    (Cy : Matrix β ν E) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ z : Matrix α ν E, ∀ φ ∈ SB (κ → k), l (d.rho ψ (z * Cyᵀ) φ) = l φ

def IsYForm (ψ : AddChar k ℂ) {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} (d : Darboux (symp c ξ JA JB) κ)
    (Cy : Matrix β ν E) (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  IsYInv c ψ d Cy l ∧ ∃ φ ∈ SB (κ → k), l φ ≠ 0

structure IsLinPair [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E]
    (ψ : AddChar k ℂ) (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (d : Darboux (symp c ξ JA JB) κ) (χ : Eˣ →* Circle)
    (Cy : Matrix β ν E) (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)) : Prop where
  split : IsUWeilSplit c (sbClass k) ψ ξ JA JB d χ Cy (om.comp (MonoidHom.inr _ _))
  pres : ∀ g : UG c JA, ∀ φ ∈ SB (κ → k), om (g, 1) φ ∈ SB (κ → k)
  impl : ∀ (g : UG c JA) (w : Matrix α β E), ∀ φ ∈ SB (κ → k),
    om (g, 1) (d.rho ψ w φ) = d.rho ψ (((g : GL α E) : Matrix α α E) * w) (om (g, 1) φ)
  lin : ∀ l, IsYInv c ψ d Cy l → ∀ g : UG c JA, ∀ φ ∈ SB (κ → k), l (om (g, 1) φ) = l φ

section Abstract

variable {G H Y : Type} [Group G] [Group H]

def secMap (om : G × H →* Module.End ℂ (Y → ℂ)) (l : (Y → ℂ) →ₗ[ℂ] ℂ) : (Y → ℂ) →ₗ[ℂ] (H → ℂ) :=
  LinearMap.pi fun h => l ∘ₗ om (1, h)

def secSpace [TopologicalSpace Y] (om : G × H →* Module.End ℂ (Y → ℂ)) (l : (Y → ℂ) →ₗ[ℂ] ℂ) : Submodule ℂ (H → ℂ) :=
  (SB Y).map (secMap om l)

def locAug [TopologicalSpace Y] (om : G × H →* Module.End ℂ (Y → ℂ)) : Submodule ℂ (Y → ℂ) :=
  Submodule.span ℂ {z | ∃ g : G, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ}

def IsCoinvQuot {G' Y' : Type} [Group G'] [TopologicalSpace Y] [TopologicalSpace Y'] (om : G × H →* Module.End ℂ (Y → ℂ))
    (om' : G' × H →* Module.End ℂ (Y' → ℂ)) : Prop :=
  locAug om' ≠ SB Y' ∧
  (∀ N : Submodule ℂ (Y' → ℂ), locAug om' ≤ N → N ≤ SB Y' → (∀ h : H, ∀ φ ∈ N, om' (1, h) φ ∈ N) → N = locAug om' ∨ N = SB Y') ∧
  ∃ p : (Y → ℂ) →ₗ[ℂ] ((Y' → ℂ) ⧸ locAug om'), (SB Y).map p = (SB Y').map (locAug om').mkQ ∧ locAug om ≤ LinearMap.ker p ∧
    ∀ h : H, ∀ φ ∈ SB Y, ∀ φ' ∈ SB Y', p φ = (locAug om').mkQ φ' → p (om (1, h) φ) = (locAug om').mkQ (om' (1, h) φ')

theorem secMap_apply (om : G × H →* Module.End ℂ (Y → ℂ)) (l : (Y → ℂ) →ₗ[ℂ] ℂ) (φ : Y → ℂ) (h : H) :
    secMap om l φ h = l (om (1, h) φ) := rfl

end Abstract

def IsWittStep {a a' : ℕ} (r : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JA' : Matrix (Fin a') (Fin a') E) : Prop :=
  a = a' + 2 * r ∧ ∃ P : Matrix (Fin a) (Fin a' ⊕ (Fin r ⊕ Fin r)) E,
    Pᵀ * JA * P.map c = (Matrix.fromBlocks JA' 0 0 (Matrix.fromBlocks 0 1 1 0) :
      Matrix (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fin a' ⊕ (Fin r ⊕ Fin r)) E)

def LocalCompl : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] [Invertible (2 : k)] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (E : Type) [Field E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E] (c : E →ₐ[k] E) (δ : E), IsQuad c δ →
  ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
  ∀ (n a a' r d : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JA' : Matrix (Fin a') (Fin a') E) (JB : Matrix (Fin d) (Fin d) E)
    (Cy : Matrix (Fin d) (Fin n) E), IsHerm c JA → IsHerm c JA' → (∀ i j, c (JB j i) = -JB i j) → IsLagr c JB Cy →
    JB.det ≠ 0 → a + a' = 2 * n → 0 < r → IsWittStep c r JA JA' →
  ∀ χ : Eˣ →* Circle, Continuous χ → ResEtaPow (R := k) ⊥ χ a →
  ∀ (κ κ' : Type) [Fintype κ] [Fintype κ'] (co : Darboux (symp c (-1) JA JB) κ) (co' : Darboux (symp c (-1) JA' JB) κ')
    (om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)) (om' : UG c JA' × UG c JB →* Module.End ℂ ((κ' → k) → ℂ)),
    IsUWeilPair c (sbClass k) ψ (-1) JA JB co χ 1 om → IsUWeilPair c (sbClass k) ψ (-1) JA' JB co' χ 1 om' →
    IsCoinvQuot om om'

end GlobalTheory.LinPair

end
end

