import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointOperatorIdentities
section
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Notions
variable {n : Type}

def KeepsFinite (A : Module.End ℂ (Form k n ℂ)) : Prop :=
  ∀ φ : Form k n ℂ, (Function.support φ).Finite → (Function.support (A φ)).Finite

def IsScaledUnitaryOn (W : Submodule ℂ (Form k n ℂ)) (a : ℂ) (A : Module.End ℂ (Form k n ℂ)) : Prop :=
  Set.BijOn A {φ | φ ∈ W ∧ (Function.support φ).Finite} {φ | φ ∈ W ∧ (Function.support φ).Finite} ∧
    ∀ φ ∈ W, ∀ φ' ∈ W, (Function.support φ).Finite → (Function.support φ').Finite →
      cntIp (A φ) (A φ') = a * cntIp φ φ'

def IsUnitStable {V : Type} [AddCommGroup V] [Module 𝓀[k] V] (S : Finset {x : V // x ≠ 0}) : Prop :=
  ∀ (c : 𝓀[k]ˣ) (x y : {x : V // x ≠ 0}), x ∈ S → y.1 = (c : 𝓀[k]) • x.1 → y ∈ S

end Notions

variable (k) in

structure Vanishing (n : Type) [Fintype n] [DecidableEq n] (M : Type) [AddCommGroup M] [Module ℂ M] (ϖ : Unif k) :
    Prop where

  trLat_eq_zero : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k], trLat L φ = 0

  trKer_eq_zero : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k], trKer L φ = 0

  partial_lat : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (S : Finset {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}), IsUnitStable (k := k) S → ∑ f ∈ S, φ (ofDual L f) = 0

  partial_ker : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (S : Finset {x : Red L // x ≠ 0}), IsUnitStable (k := k) S → ∑ x ∈ S, φ (up L ϖ x) = 0

  invariant_eq_zero : ∀ (π : Representation ℂ (GL n k) M) (P : Pair k n) (v : levelVec π P),
    formOf π P v ∈ Mram k n M → ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (θ : M →ₗ[ℂ] M'),
    ((∀ g ∈ latStab P.lat, ∀ w, θ (π g w) = θ w) ∨ (∀ g ∈ latStab P.ker, ∀ w, θ (π g w) = θ w)) → θ v = 0

variable (k) in

structure OperatorIdentities (n : Type) [Fintype n] (M : Type) [AddCommGroup M] [Module ℂ M] (ϖ : Unif k)
    (χ : AddChar 𝓀[k] ℂ) : Prop where

  FFStar_formula : ∀ (φ : Form k n M) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] [Fintype {x : Red L // x ≠ 0}]
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}),
    FFStar ϖ χ φ (ofDual L f) = ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) • φ (up L ϖ x)

  FFStar_mul_FF : (FFStar ϖ χ * FF ϖ χ : Module.End ℂ (Form k n M)) = ((resCard k : ℂ) ^ Fintype.card n) • 1 - tr

  FF_mul_FFStar : (FF ϖ χ * FFStar ϖ χ : Module.End ℂ (Form k n M)) = ((resCard k : ℂ) ^ Fintype.card n) • 1 - tr'

  FFStar_FF_ram : ∀ φ ∈ Mram k n M, FFStar ϖ χ (FF ϖ χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  FF_FFStar_ram : ∀ φ ∈ Mram k n M, FF ϖ χ (FFStar ϖ χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  FF_mem_ram : ∀ φ ∈ Mram k n M, FF ϖ χ φ ∈ Mram k n M

  FFStar_mem_ram : ∀ φ ∈ Mram k n M, FFStar ϖ χ φ ∈ Mram k n M

  D_dia : ∀ c : 𝓀[k]ˣ, (D ϖ * dia c : Module.End ℂ (Form k n M)) = dia c * D ϖ

  FF_dia : ∀ c : 𝓀[k]ˣ, (FF ϖ χ * dia c : Module.End ℂ (Form k n M)) = dia c * FF ϖ χ

  FF_eq_D_Gs : ∀ φ ∈ Mram k n M, FF ϖ χ φ = D ϖ (Gs χ φ)

  Gs_mul_GsStar : (Gs χ * GsStar χ : Module.End ℂ (Form k n M)) = (resCard k : ℂ) • 1 - Nm

  D_U_ram : ∀ φ ∈ Mram k n M, D ϖ (U ϖ φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ

  U_D_ram : ∀ φ ∈ Mram k n M, U ϖ (D ϖ φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ

  FFStar_dia : ∀ c : 𝓀[k]ˣ, (FFStar ϖ χ * dia c : Module.End ℂ (Form k n M)) = dia c * FFStar ϖ χ

  U_dia : ∀ c : 𝓀[k]ˣ, (U ϖ * dia c : Module.End ℂ (Form k n M)) = dia c * U ϖ

  dia_mem_ram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n M, dia c φ ∈ Mram k n M

  phiOne_dia : ∀ (c : 𝓀[k]ˣ) (m : Type) [Fintype m] (P : Pair k n) (Q : Pair k m),
    phiOne (c • P) (c • Q) = phiOne P Q

  twisted_class_sum : ∀ (ε : 𝓀[k]ˣ) (φ : Form k n M) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    [Fintype {x : Red L // x ≠ 0}] (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}),
    ∑ x : {x : Red L // x ≠ 0}, χ (-((ε : 𝓀[k]) * f.1 x.1)) • φ (up L ϖ x) = dia ε (FFStar ϖ χ φ) (ofDual L f)

  sign_FFStar_sign_FF : (dia (-1) * FFStar ϖ χ * (dia (-1) * FF ϖ χ) : Module.End ℂ (Form k n M)) =
    FFStar ϖ χ * FF ϖ χ

  sign_ram : ∀ φ ∈ Mram k n M,
    dia (-1) (FFStar ϖ χ (dia (-1) (FF ϖ χ φ))) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  unit_ram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n M,
    dia c (FFStar ϖ χ (dia c⁻¹ (FF ϖ χ φ))) = ((resCard k : ℂ) ^ Fintype.card n) • φ

variable (k) in

structure AdjointIdentities (n : Type) [Fintype n] (ϖ : Unif k) (χ : AddChar 𝓀[k] ℂ) : Prop where

  FF_finite : KeepsFinite (n := n) (FF ϖ χ) ∧ KeepsFinite (n := n) (FFStar ϖ χ)

  D_finite : KeepsFinite (n := n) (D ϖ) ∧ KeepsFinite (n := n) (U ϖ)

  FF_adj : IsAdj (n := n) (FF ϖ χ) (FFStar ϖ χ)

  FF_unitary : IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (FF ϖ χ)

  Gs_adj : IsAdj (n := n) (Gs χ) (GsStar χ)

  U_adj : IsAdj (n := n) (U ϖ) (D ϖ)

  dia_adj : ∀ c : 𝓀[k]ˣ, IsAdj (n := n) (dia c) (dia c⁻¹)

  dia_unitary : ∀ c : 𝓀[k]ˣ, IsScaledUnitaryOn (n := n) ⊤ 1 (dia c) ∧ IsScaledUnitaryOn (Mram k n ℂ) 1 (dia c)

  sign_adj : IsAdj (n := n) (dia (-1) * FF ϖ χ) (dia (-1) * FFStar ϖ χ)

  sign_unitary : IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia (-1) * FF ϖ χ)

  unit_unitary : ∀ c : 𝓀[k]ˣ, IsAdj (n := n) (dia c⁻¹ * FF ϖ χ) (dia c * FFStar ϖ χ) ∧
    IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia c⁻¹ * FF ϖ χ)

def PairOperatorStatement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (n : Type) [Fintype n] [DecidableEq n],
    (∀ (M : Type) [AddCommGroup M] [Module ℂ M],
      Vanishing k n M ϖ ∧ OperatorIdentities k n M ϖ (resChar ψ hψ ϖ)) ∧
    AdjointIdentities k n ϖ (resChar ψ hψ ϖ)

section Examples

example {n : Type} (W : Submodule ℂ (Form k n ℂ)) : IsScaledUnitaryOn W 1 1 :=
  ⟨Set.bijOn_id _, fun _ _ _ _ _ _ => (one_mul _).symm⟩

example {V : Type} [AddCommGroup V] [Module 𝓀[k] V] [Fintype {x : V // x ≠ 0}] :
    IsUnitStable (k := k) (Finset.univ : Finset {x : V // x ≠ 0}) := fun _ _ _ _ _ => Finset.mem_univ _

example {n : Type} [Fintype n] [Nonempty n] (a : ℂ) : ¬ IsScaledUnitaryOn (k := k) (n := n) ⊤ a 0 := by
  classical
  obtain ⟨P⟩ : Nonempty (Pair k n) := inferInstance
  rintro ⟨h, -⟩
  obtain ⟨φ, -, hφ⟩ := h.surjOn (show Pi.single P (1 : ℂ) ∈ {φ : Form k n ℂ | φ ∈ (⊤ : Submodule ℂ _) ∧ (Function.support φ).Finite} from
    ⟨trivial, (Set.finite_singleton P).subset Pi.support_single_subset⟩)
  simpa using congrFun hφ P

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DualLatticeExchange
section
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.DualLatticeExchange
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair

section Defs
variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n]

def dualLat (L : Submodule 𝒪[k] (n → k)) : Submodule 𝒪[k] (n → k) where
  carrier := {u | ∀ x ∈ L, u ⬝ᵥ x ∈ 𝒪[k]}
  add_mem' hu hv x hx := by
    rw [add_dotProduct]
    exact add_mem (hu x hx) (hv x hx)
  zero_mem' x _ := by
    rw [zero_dotProduct]
    exact zero_mem _
  smul_mem' s u hu x hx := by
    have : (s • u) ⬝ᵥ x = (s : k) * (u ⬝ᵥ x) := smul_dotProduct (s : k) u x
    rw [this]
    exact mul_mem s.2 (hu x hx)

def intPart (L : Submodule 𝒪[k] (n → k)) (u : n → k) : Submodule 𝒪[k] (n → k) where
  carrier := {x | x ∈ L ∧ u ⬝ᵥ x ∈ 𝒪[k]}
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, by
    rw [dotProduct_add]
    exact add_mem hx.2 hy.2⟩
  zero_mem' := ⟨zero_mem _, by
    rw [dotProduct_zero]
    exact zero_mem _⟩
  smul_mem' s x hx := ⟨L.smul_mem s hx.1, by
    have : u ⬝ᵥ (s • x) = (s : k) * (u ⬝ᵥ x) := dotProduct_smul (s : k) u x
    rw [this]
    exact mul_mem s.2 hx.2⟩

end Defs

section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def GluedPrimitive : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (f : n → k),
    IsGlue L f → 1 ≤ p → p ≤ c → ∀ i j : Fin c, j.val = i.val + 1 →
      (fun g : GL (n ⊕ Fin c) k => g.val (Sum.inr i) (Sum.inr j)) ''
        ((N k n c p ⊓ latStab (gluedLat q c p L f) : Subgroup (GL (n ⊕ Fin c) k)) : Set (GL (n ⊕ Fin c) k)) =
        (𝒪[k] : Set k)

def GluedExchange : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (q : Unif k) (ψ : AddChar k Circle)
    (L : Submodule 𝒪[k] (n → k)) (f : n → k), IsGlue L f → 2 ≤ p → p ≤ c →
    ∀ u₁ ∈ dualLat L, q.inv • u₁ ∉ dualLat L → ∀ l₀ ∈ L, q.inv * (u₁ ⬝ᵥ l₀ - 1) ∈ 𝒪[k] →
      IsGlue (intPart L (q.inv • u₁)) l₀ ∧
      ∃ g ∈ N k n c (p - 1),
        g.val *ᵥ avec k n c p =
          avec k n c p + inX k n c (q.1 • f) + ((q.inv • u₁) ⬝ᵥ (q.1 • f)) • avec k n c (p - 1) ∧
        (∀ i, 1 ≤ i → i ≤ c → i ≠ p → g.val *ᵥ avec k n c i = avec k n c i) ∧
        (∀ x : n → k, g.val *ᵥ inX k n c x = inX k n c x) ∧
        ψ (simpleSum g) = ψ ((q.inv • u₁) ⬝ᵥ (q.1 • f)) ∧
        rowE c (p - 1) (q.inv • u₁) • gluedLat q c p L f =
          g • gluedLat q c (p - 1) (intPart L (q.inv • u₁)) l₀

def FunctionalExchange [MeasurableSpace k] [BorelSpace k] : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1)
    (ν : Measure k), ν.IsAddHaarMeasure →
  ∀ (V A : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
    (π : Representation ℂ (GL n k) V) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (M₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [M₀.IsLattice k] (v : sphVecs σ M₀)
    (b : V →ₗ[ℂ] A →ₗ[ℂ] ℂ), 2 ≤ p → p ≤ c → IsPos ψ (p - 1) π σ b →
    (∀ (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (f : n → k), IsGlue L f →
      (∀ φ : V,
        (∀ u : n → k, b φ (σ (rowE c (p - 1) u) (vecAt σ v (gluedLat q c p L f))) ≠ 0 → q.1 • u ∈ dualLat L) ∧
        (∀ u : n → k, ∀ u' ∈ dualLat L, b φ (σ (rowE c (p - 1) (u + u')) (vecAt σ v (gluedLat q c p L f))) =
          b φ (σ (rowE c (p - 1) u) (vecAt σ v (gluedLat q c p L f)))) ∧
        Integrable (fun u : n → k => b φ (σ (rowE c (p - 1) u) (vecAt σ v (gluedLat q c p L f))))
          (Measure.pi fun _ => ν) ∧
        (∀ u ∈ dualLat L, b φ (σ (rowE c (p - 1) u) (vecAt σ v (gluedLat q c p L f))) =
          b φ (vecAt σ v (gluedLat q c p L f)))) ∧
      (∀ Φ ∈ EqForm π, Φ ∈ Mram k n V → ∀ P₀ : Pair k n,
        b (Φ P₀) (vecAt σ v (gluedLat q c p L f)) = 0 ∧
        exUp ν (p - 1) σ (b (Φ P₀)) (vecAt σ v (gluedLat q c p L f)) =
          (((Measure.pi fun _ : n => ν).real (dualLat L : Set (n → k)) : ℝ) : ℂ) *
            ∑ Q ∈ withLat L, resChar ψ hψ q (Q.ev (q.1 • f)) * b (Φ P₀) (vecAt σ v (Q.glued q c (p - 1))))) ∧
    (3 ≤ Fintype.card n → ∀ Φ ∈ EqForm π, Φ ∈ Mram k n V → ∀ P₀ : Pair k n,
      exUp ν (p - 1) σ (b (Φ P₀)) (vecAt σ v (P₀.glued q c p)) =
        (((Measure.pi fun _ : n => ν).real (dualLat P₀.ker : Set (n → k)) : ℝ) : ℂ) *
          (((resCard k : ℝ) ^ ((p : ℝ) - 1 - ((c : ℝ) + 1) / 2) : ℝ) : ℂ) *
          b (dia (-1 : 𝓀[k]ˣ) (FFStar q (resChar ψ hψ q) Φ) P₀) (vecAt σ v (P₀.glued q c (p - 1))))

end Statements

def LevelPrimeExchange : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k], GluedPrimitive k ∧ GluedExchange k ∧ FunctionalExchange k

section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

example (c p : ℕ) (u x : n → k) :
    (rowE c p u).val *ᵥ inX k n c x = inX k n c x + (u ⬝ᵥ x) • avec k n c p := by
  ext (i | i)
  · simp [rowE, lowU, inX, avec, fromBlocks_mulVec]
  · by_cases h : i.val + 1 = p <;> simp [rowE, lowU, inX, avec, fromBlocks_mulVec, mulVec, dotProduct, h]

example : dualLat (stdLat k n) = stdLat k n := by
  ext u
  refine ⟨fun h => mem_stdLat.2 fun i => ?_, fun h x hx => ?_⟩
  · have := h (Pi.single i 1) (mem_stdLat.2 fun j => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _])
    simpa using this
  · exact sum_mem fun i _ => mul_mem (mem_stdLat.1 h i) (mem_stdLat.1 hx i)

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.DualLatticeExchange
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

section General

variable {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]

def IsIntegralOp (μ : Measure G) (π : Representation ℂ G V) (f : G → ℂ) (A : V →ₗ[ℂ] V) : Prop :=
  ∀ (v : V) (l : Module.Dual ℂ V),
    Integrable (fun g => f g * l (π g v)) μ ∧ l (A v) = ∫ g, f g * l (π g v) ∂μ

theorem IsIntegralOp.unique {μ : Measure G} {π : Representation ℂ G V} {f : G → ℂ} {A B : V →ₗ[ℂ] V}
    (hA : IsIntegralOp μ π f A) (hB : IsIntegralOp μ π f B) : A = B := by
  ext v
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, (hA v l).2, (hB v l).2, sub_self]

def HasFinTrace (A : V →ₗ[ℂ] V) (c : ℂ) : Prop :=
  FiniteDimensional ℂ (LinearMap.range A) ∧
    LinearMap.trace ℂ (LinearMap.range A)
      (A.restrict (p := LinearMap.range A) (q := LinearMap.range A)
        fun v _ => LinearMap.mem_range_self A v) = c

def HasTrace (μ : Measure G) (π : Representation ℂ G V) (f : G → ℂ) (c : ℂ) : Prop :=
  ∃ A : V →ₗ[ℂ] V, IsIntegralOp μ π f A ∧ HasFinTrace A c

theorem HasTrace.unique {μ : Measure G} {π : Representation ℂ G V} {f : G → ℂ} {c d : ℂ}
    (hc : HasTrace μ π f c) (hd : HasTrace μ π f d) : c = d := by
  obtain ⟨A, hA, -, rfl⟩ := hc
  obtain ⟨B, hB, -, rfl⟩ := hd
  obtain rfl := hA.unique hB
  rfl

end General

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n] [LinearOrder n]

def unipO : Subgroup (GL n k) := unipB k n ⊓ KO k n

def unipLowerOne : Subgroup (GL n k) := unipBLower k n ⊓ KOne k n

variable {k n}

def Contracts (t : n → kˣ) : Prop :=
  (∀ u ∈ unipO k n, diagT k n t * u * (diagT k n t)⁻¹ ∈ unipO k n) ∧
    ∀ u ∈ unipLowerOne k n, (diagT k n t)⁻¹ * u * diagT k n t ∈ unipLowerOne k n

example : Contracts (1 : n → kˣ) := ⟨fun u hu => by simpa using hu, fun u hu => by simpa using hu⟩

def deltaB (t : n → kˣ) : ℝ := ∏ i, ∏ j with i < j, nabs k (t i / t j)

theorem deltaB_pos (t : n → kˣ) : 0 < deltaB t :=
  Finset.prod_pos fun _ _ => Finset.prod_pos fun _ _ => nabs_pos' k _

theorem deltaB_eq_modulus (t : n → kˣ) :
    deltaB t = modulus k (fun _ : n => Unit) (leviTorus k n t) := (modulus_torus t).symm

def iwahoriCoset (t : n → kˣ) : Set (GL n k) :=
  {g | ∃ a ∈ iwahori k n, ∃ b ∈ iwahori k n, g = a * diagT k n t * b}

def cosetInd (t : n → kˣ) : GL n k → ℂ := (iwahoriCoset t).indicator fun _ => 1

variable {V : Type} [AddCommGroup V] [Module ℂ V]

open scoped Classical in

def IsExponents (π : Representation ℂ (GL n k) V) (E : Multiset ((n → kˣ) →* ℂˣ)) : Prop :=
  (∀ χ ∈ E, ∀ s ∈ torusO k n, χ s = 1) ∧ ∀ χ, (E.count χ : ℕ∞) = expMult π χ

theorem IsExponents.unique {π : Representation ℂ (GL n k) V} {E E' : Multiset ((n → kˣ) →* ℂˣ)}
    (h : IsExponents π E) (h' : IsExponents π E') : E = E' := by
  classical
  ext χ
  have := (h.2 χ).trans (h'.2 χ).symm
  have h2 := Nat.cast_injective this
  convert h2

variable (k n)

def DominantContracts : Prop :=
  ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ a : n → ℤ, Antitone a → Contracts fun i => ϖ ^ a i

def TraceFormula : Prop :=
  ∀ [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure]
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), IsAdmissible π →
    FiniteDimensional ℂ (fixed (jacBU π) (torusO k n)) ∧
    (∀ t : n → kˣ, Contracts t →
      HasTrace μ π (cosetInd t)
        ((μ.real (iwahori k n : Set (GL n k)) : ℂ) * ((deltaB t : ℂ))⁻¹ *
          LinearMap.trace ℂ (fixed (jacBU π) (torusO k n)) (jacBUFixed π t))) ∧
    ∃ E : Multiset ((n → kˣ) →* ℂˣ), IsExponents π E ∧
      ∀ t : n → kˣ, Contracts t →
        HasTrace μ π (cosetInd t)
          ((μ.real (iwahori k n : Set (GL n k)) : ℂ) * ((deltaB t : ℂ))⁻¹ *
            (E.map fun χ => (χ t : ℂ)).sum)

end Local

def IwahoriTrace : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r : ℕ),
    DominantContracts k (Fin r) ∧ TraceFormula k (Fin r)

def IwahoriTraceOfBorelCasselman : Prop := GlobalTheory.Published.BorelCasselman → IwahoriTrace

end GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
end
end

