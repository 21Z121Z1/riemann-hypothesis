import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.CoeffMatrixZeroCorrectedLineGramPoly
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Polynomial Matrix ReciprocityTheory.AnForm.P

variable {r m : ℕ} (hm : m ≤ r) (D : Fin r → ℝ) (Y : Matrix (Fin r) (Fin r) ℂ)

def lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ[X] := 1 + (X : ℂ[X]) • A.map C

theorem cf_lin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    cf k (lin A) = if k = 0 then 1 else if k = 1 then A else 0 := by
  ext i j
  rcases k with _ | _ | k <;> by_cases h : i = j <;>
    simp [cf, lin, Matrix.one_apply, h, Polynomial.coeff_one, Polynomial.coeff_C]

theorem coeffMatrix_zero_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 0 (lin A) = 1 := by
  simp [cf_lin]
theorem coeffMatrix_one_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 1 (lin A) = A := by
  simp [cf_lin]
theorem coeffMatrix_two_linearMatrixPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : cf 2 (lin A) = 0 := by
  simp [cf_lin]

theorem cf_submatrix {α β γ δ : Type*} (k : ℕ) (P : Matrix α β ℂ[X]) (f : γ → α) (g : δ → β) :
    cf k (P.submatrix f g) = (cf k P).submatrix f g := rfl

abbrev Dc : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => (D k : ℂ)

abbrev Ym : Matrix (Fin m) (Fin m) ℂ := Y.submatrix (Fin.castLE hm) (Fin.castLE hm)

abbrev Dm : Matrix (Fin m) (Fin m) ℂ := diagonal fun i => (D (Fin.castLE hm i) : ℂ)

theorem Dc_sub : (Dc D).submatrix (Fin.castLE hm) (Fin.castLE hm) = Dm hm D := by
  ext i j
  by_cases h : i = j <;> simp [Dc, Dm, Matrix.diagonal_apply, h]

def GP (t : ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  (lin ((starRingEnd ℂ t) • Yᴴ) * ((Dc D).map C * lin (t • Y))).submatrix (Fin.castLE hm) (Fin.castLE hm)

def GnP (t : ℂ) : Matrix (Fin m) (Fin m) ℂ[X] :=
  lin (-((starRingEnd ℂ t) • (Ym hm Y)ᴴ)) * (GP hm D Y t * lin (-(t • Ym hm Y)))

theorem coeffMatrix_zero_lineGramPoly (t : ℂ) : cf 0 (GP hm D Y t) = Dm hm D := by
  rw [GP, cf_submatrix, cf_mul_zero, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, one_mul, mul_one, Dc_sub]

theorem coeffMatrix_one_lineGramPoly (t : ℂ) : cf 1 (GP hm D Y t) =
    (starRingEnd ℂ t) • ((Ym hm Y)ᴴ * Dm hm D) + t • (Dm hm D * Ym hm Y) := by
  rw [GP, cf_submatrix, cf_mul_one, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly,
    one_mul, mul_one]
  ext i j
  simp [Dc, Dm, Ym, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  ring

theorem coeffMatrix_two_lineGramPoly (t : ℂ) : cf 2 (GP hm D Y t) =
    ((starRingEnd ℂ t) * t) • (Yᴴ * Dc D * Y).submatrix (Fin.castLE hm) (Fin.castLE hm) := by
  rw [GP, cf_submatrix, cf_mul_two, cf_mapC_mul, cf_mapC_mul, cf_mapC_mul, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly,
    coeffMatrix_two_linearMatrixPoly, coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly]
  simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, one_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
  rw [mul_comm t]
  rfl

theorem coeffMatrix_zero_correctedLineGramPoly (t : ℂ) : cf 0 (GnP hm D Y t) = Dm hm D := by
  rw [GnP, cf_mul_zero, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, one_mul, mul_one]

theorem coeffMatrix_one_correctedLineGramPoly (t : ℂ) : cf 1 (GnP hm D Y t) = 0 := by
  rw [GnP, cf_mul_one, cf_mul_one, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, coeffMatrix_one_lineGramPoly]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.add_mul]
  abel

theorem coeffMatrix_two_correctedLineGramPoly (t : ℂ) : cf 2 (GnP hm D Y t) =
    ((starRingEnd ℂ t) * t) • ((Yᴴ * Dc D * Y).submatrix (Fin.castLE hm) (Fin.castLE hm) -
      (Ym hm Y)ᴴ * Dm hm D * Ym hm Y) - t ^ 2 • (Dm hm D * Ym hm Y * Ym hm Y) -
      (starRingEnd ℂ t) ^ 2 • ((Ym hm Y)ᴴ * (Ym hm Y)ᴴ * Dm hm D) := by
  rw [GnP, cf_mul_two, cf_mul_two, cf_mul_one, cf_mul_zero, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly, coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_linearMatrixPoly, coeffMatrix_one_linearMatrixPoly,
    coeffMatrix_two_linearMatrixPoly, coeffMatrix_zero_lineGramPoly, coeffMatrix_one_lineGramPoly, coeffMatrix_two_lineGramPoly]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, smul_smul]
  module

def Gz (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((1 + ζ • Y)ᴴ * Dc D * (1 + ζ • Y)).submatrix (Fin.castLE hm) (Fin.castLE hm)

def Gnz (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (1 - ζ • Ym hm Y)ᴴ * (Gz hm D Y ζ * (1 - ζ • Ym hm Y))

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def NfacRmulStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
    X.nfac la (rmul x b) = ‖bchar la b‖⁻¹ * X.nfac la x

def NfacLactStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, X.nfac la (lact γ x) = X.nfac la x

def PnormInvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x

def KapGGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 x1 : Frame X.Ψ r) (γ : GL (Fin r) E) (U : Set (V (nd X)))
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r), IsOpen U → DifferentiableOn ℂ Φ U →
    (∀ z ∈ U, cpt X x0 z ∈ X.dom ∧ bf z ∈ Bor X.Ψ r ∧
      cpt X x0 z = lact γ (rmul (cpt X x1 (Φ z)) (bf z))) →
    ∀ z ∈ U, (fderiv ℂ Φ z).det = bchar (kapW X) (bf z)

def CurvGGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom →
    (X.IsDominant la → ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re) ∧
    (IsStrictDom X la → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re)

def LineBundleFirstBoundGlobalGeneration : Prop :=
  ∀ (r : ℕ) (X : Data E r), 0 < r →
    (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.la1 (lact γ (rmul x b)) = X.la1 x) ∧
    ContinuousOn X.la1 X.dom ∧ ∀ x ∈ X.dom, 0 < X.la1 x

end

end ReciprocityTheory.ChartRestriction.G.AR.Inst
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff
section
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y MeasureTheory Topology

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def PropDisc {r : ℕ} (X : Data E r) : Prop :=
  ∀ x ∈ X.dom, ∀ x' ∈ X.dom, ∃ U ∈ 𝓝 x, ∃ U' ∈ 𝓝 x',
    {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b}.Finite

def GGConnStatement : Prop := ∀ (r : ℕ) (X : Data E r), IsConnected X.dom

def YConnStatement : Prop := ∀ (r : ℕ) (X : Data E r), ConnectedSpace (Yq X)

def QuotientIsHausdorff : Prop := ∀ (r : ℕ) (X : Data E r), PropDisc X → T2Space (Yq X)

def YSCStatement : Prop := ∀ (r : ℕ) (X : Data E r), SecondCountableTopology (Yq X)

def AtlasStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)], PropDisc X →
    (∀ γ ∈ X.Γ, X.χ (kapW X) γ = 1) →
    ∃ A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r), Fits X A

def CurvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
    (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)), Fits X A → ∀ la : Wt X.Ψ r,
    (X.IsDominant la → A.Pos la fun _ => 0) ∧
    (IsStrictDom X la → ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < A.leviAt i (A.ph la i) y ξ)

def LineBundleFirstBound : Prop :=
  ∀ (r : ℕ) (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
    (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)), 0 < r → Fits X A → PropDisc X →
    Continuous (la1Y X A) ∧ (∀ y, 0 < la1Y X A y) ∧
      ∀ ε : ℝ, 0 < ε → IsCompact {y | ε ≤ la1Y X A y}

def DecStatement {r : ℕ} (X : Data E r) : Prop :=
  ∀ (la : Wt X.Ψ r) (c : ℝ), ∀ P ∈ X.SSgt la c, ∃ C : ℝ, ∀ x ∈ X.dom,
    X.pnorm la P x ^ 2 ≤ C * Real.exp (-(2 * Real.pi * c) / X.la1 x ^ 2)

def GapStatement {r : ℕ} (X : Data E r) : Prop :=
  ∀ (la : Wt X.Ψ r), ∀ P ∈ X.SSgt la 0, ∃ c : ℝ, 0 < c ∧ P ∈ X.SSgt la c

variable {r : ℕ} (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]

def cfwY (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)) (ps : Yq X → ℝ) (a : ℝ) : Prop :=
  (∃ C A' : ℝ, ∀ y, ps y ≤ C + A' * Real.log (1 + 1 / la1Y X A y)) ∧
  ∀ η : ℝ, 0 < η → η < 1 / 2 → ∃ C A' : ℝ, ∀ y, ∀ ξ : Fin r → E, X.IsIso ξ →
    (∀ τ, 1 ≤ X.tt ξ (lift X A y) τ) →
    ps y ≤ C + A' * Real.log (1 + 1 / la1Y X A y) -
      8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ (lift X A y) τ

def CfStatement (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)) : Prop :=
  ∀ (G L : Wt X.Ψ r) (N : ℕ) (w : Fin N → X.dom → Yq X → ℂ) (F : X.dom → Yq X → ℂ)
    (ps : Yq X → ℝ) (a η : ℝ),
    (∀ k, A.IsSec L (w k)) → (∀ k, Bdd A L (w k)) → (∀ k, vanY X A L 0 (w k)) →
    (∀ y, ∃ k, w k (A.pick y) y ≠ 0) → 0 < η → 0 ≤ a → A.IsSec G F → cfwY X A ps a →
    ∫⁻ y, ENNReal.ofReal (A.nsq G F y * Real.exp (-ps y) * A.sqn L w y ^ (-η)) ∂A.mu < ⊤ →
    Bdd A G F ∧ vanY X A G 0 F ∧ vanY X A G a F

omit [T2Space (Yq X)] [SecondCountableTopology (Yq X)] in

def CuspInstStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
    (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)), 0 < r → Fits X A → PropDisc X →
    A.mu Set.univ < ⊤ → DecStatement X → GapStatement X → CfStatement X A →
    ∃ C : Cusp A, C.la1 = la1Y X A ∧ C.van = vanY X A ∧ C.kd = 2 * Real.pi ∧ C.cfw = cfwY X A

omit [T2Space (Yq X)] [SecondCountableTopology (Yq X)] in

def FlatStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]
    (A : WeightedAtlas (nd X) (Yq X) X.dom (Wt X.Ψ r)), Fits X A → ∀ (C : Cusp A) (Xa : ArchIn A C),
    ∃ (w0 : X.dom → Yq X → ℂ) (s : Fin (nd X) → X.dom → Yq X → ℂ) (De : MvPolynomial (Fin (nd X)) ℂ)
      (thp : X.dom → Yq X → ℂ) (h1 : A.IsSec Xa.Fp thp) (h2 : Bdd A Xa.Fp thp)
      (h3 : C.van Xa.Fp 0 thp) (h4 : ∃ y, thp (A.pick y) y ≠ 0),
      FlatDatum A C { Xa with thp := thp, thp_sec := h1, thp_bdd := h2, thp_van := h3, thp_ne := h4 }
        w0 s De

end

end ReciprocityTheory.ChartRestriction.G.AR.Inst
end

