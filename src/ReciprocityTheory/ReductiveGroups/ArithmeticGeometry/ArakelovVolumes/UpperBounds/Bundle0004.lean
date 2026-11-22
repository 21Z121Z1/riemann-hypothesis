import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

def nD (f p q : ℕ) : ℕ := f * (p * q)

def Zof {f p q : ℕ} (v : V (nD f p q)) (k : Fin f) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun a b => v (finProdFinEquiv (k, finProdFinEquiv (a, b)))

def Dset (f p q : ℕ) : Set (V (nD f p q)) :=
  {v | ∀ k, (1 - Zof v k * (Zof v k)ᴴ).PosDef}

def rh {f p q : ℕ} (v : V (nD f p q)) : ℝ :=
  -∑ k, Real.log (1 - Zof v k * (Zof v k)ᴴ).det.re

def zPart {f p q N' : ℕ} (v : V (nD f p q + N')) : V (nD f p q) :=
  WithLp.toLp 2 fun j => v (Fin.castAdd N' j)

def tPart {f p q N' : ℕ} (v : V (nD f p q + N')) : V N' :=
  WithLp.toLp 2 fun j => v (Fin.natAdd (nD f p q) j)

def OmSet (f p q N' : ℕ) : Set (V (nD f p q + N')) := {v | zPart v ∈ Dset f p q}

def eOm {f p q N' : ℕ} (v : V (nD f p q + N')) : ℝ :=
  rh (zPart v) + Real.log (1 + ‖tPart v‖ ^ 2)

def ExhaustStatement : Prop :=
  ∀ f p q N' : ℕ, ∃ S : EtaleStein (nD f p q + N') (OmSet f p q N'),
    S.z = Subtype.val ∧ S.e = fun y => eOm y.1

def RhGradStatement : Prop :=
  ∀ f p q : ℕ, ∀ v ∈ Dset f p q, ∀ ξ : Fin (nD f p q) → ℂ,
    Complex.normSq (∑ j, wd (nD f p q) j (fun w => ((rh w : ℝ) : ℂ)) v * ξ j) ≤
      ((f * min p q : ℕ) : ℝ) * (leviV (nD f p q) (fun w => ((rh w : ℝ) : ℂ)) v ξ).re

def PolyGrowthStatement : Prop :=
  ∀ (D m : ℕ) (P Q : MvPolynomial (Fin D) ℂ), Q ≠ 0 →
    (∃ C : ℝ, ∀ y : Fin D → ℂ, MvPolynomial.eval y Q ≠ 0 →
      ‖MvPolynomial.eval y P / MvPolynomial.eval y Q‖ ≤ C * (1 + ∑ i, ‖y i‖) ^ m) →
    ∃ R : MvPolynomial (Fin D) ℂ, R.totalDegree ≤ m ∧ P = R * Q

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SCoordStatementPfD
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.SCoD

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.AR.Up.SCoA ReciprocityTheory.ChartRestriction.G.AR.Up.SCoC

noncomputable section

variable {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω]
  {Fr : Type*} [NormedAddCommGroup Fr] [NormedSpace ℂ Fr]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem zero_of_dense {U G : Set Fr} (hU : IsOpen U) (hUG : U ⊆ closure G) {F : Fr → ℂ}
    (hF : ContinuousOn F U) (h0 : ∀ y ∈ G ∩ U, F y = 0) : ∀ y ∈ U, F y = 0 := by
  have hsub : U ⊆ closure (G ∩ U) := by
    intro y hy
    have := hU.inter_closure ⟨hy, hUG hy⟩
    rwa [Set.inter_comm] at this
  exact Set.EqOn.of_subset_closure (f := F) (g := fun _ => 0) (fun y hy => h0 y hy) hF
    continuousOn_const Set.inter_subset_right hsub

theorem rel_deriv {ιB : Type} [Fintype ιB] (sg : K →+* ℂ) {U Gen : Set Fr} (hU : IsOpen U)
    (hUG : U ⊆ closure Gen) (pt : Fr → Ω →+* ℂ) (hpt : ∀ y ∈ Gen, (pt y).comp (algebraMap K Ω) = sg)
    (vb : ιB → Fr → ℂ) (vj : Fr → ℂ) (hvb : ∀ b, ∀ y ∈ U, DifferentiableAt ℂ (vb b) y)
    (hvj : ∀ y ∈ U, DifferentiableAt ℂ vj y) (yB : ιB → Ω) (a : Ω)
    (hGb : ∀ y ∈ Gen ∩ U, ∀ b, vb b y = pt y (yB b)) (hGa : ∀ y ∈ Gen ∩ U, vj y = pt y a)
    (hy : AlgebraicIndependent K yB) (ha : IsAlgebraic (Algebra.adjoin K (Set.range yB)) a)
    (c : V → Fr) (hc : Differentiable ℂ c) (x : Fr) (hc0 : c 0 = x) (hx : x ∈ Gen ∩ U) :
    ∃ co : ιB → Ω, fderiv ℂ (fun z => vj (c z)) 0 =
      ∑ b, pt x (co b) • fderiv ℂ (fun z => vb b (c z)) 0 := by
  obtain ⟨P, hP, hP'⟩ := exists_rel hy ha
  refine ⟨coef yB a P, ?_⟩
  set F : Fr → ℂ := fun y => P.eval₂ (eval₂Hom sg (fun b => vb b y)) (vj y) with hFdef
  have hFcont : ContinuousOn F U := fun y hyU =>
    (hasFDerivAt_eval₂ sg P (h := fun y b => vb b y) (fun b => (hvb b y hyU).hasFDerivAt)
      (hvj y hyU).hasFDerivAt).continuousAt.continuousWithinAt
  have hF0 : ∀ y ∈ Gen ∩ U, F y = 0 := by
    intro y hyGU
    have hb : (fun b => vb b y) = pt y ∘ yB := funext (hGb y hyGU)
    show P.eval₂ (eval₂Hom sg (fun b => vb b y)) (vj y) = 0
    rw [hb, hGa y hyGU, ← hpt y hyGU.1, eval₂Hom_comp, ← Polynomial.hom_eval₂, hP, map_zero]
  have hFU := zero_of_dense hU hUG hFcont hF0
  have hev : ∀ᶠ z in 𝓝 (0 : V), c z ∈ U :=
    hc.continuous.continuousAt.preimage_mem_nhds (by rw [hc0]; exact hU.mem_nhds hx.2)
  have hxU : c 0 ∈ U := by rw [hc0]; exact hx.2
  refine deriv_rel (pt x) P hP' (h := fun z b => vb b (c z)) (g := fun z => vj (c z))
    (fun b => ((hvb b (c 0) hxU).comp 0 (hc 0)).hasFDerivAt)
    ((hvj (c 0) hxU).comp 0 (hc 0)).hasFDerivAt ?_ ?_ ?_
  · funext b; show vb b (c 0) = pt x (yB b); rw [hc0]; exact hGb x hx b
  · show vj (c 0) = pt x a; rw [hc0]; exact hGa x hx
  · rw [hpt x hx.1]
    exact hev.mono fun z hz => hFU (c z) hz

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.SCoD
end

