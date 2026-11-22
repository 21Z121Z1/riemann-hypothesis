import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0734
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0748

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFibreClassEqZeroOfSmulPullbackEqZeroStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueFibre_class_eq_zero_of_smul_pullback_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → CohomZeroIsConstants (OAff q') → ∀ (u : HO1 s₀) (y : HO1 s), TMul h₀.w t u y → pullHO1 w y = 0 → pullHO1 w₀ u = 0 := by
  first | exact @GlobalTheory.AbCoh.tmul_pull_eq_zero | exact GlobalTheory.AbCoh.tmul_pull_eq_zero | (intros; apply GlobalTheory.AbCoh.tmul_pull_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiposAddSmul
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.SemiPosLarge

theorem semipos_add_smul : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∃ k0 : ℕ, ∀ k ≥ k0, A.Pos (G + k • H) (fun _ => 0) := by
  intro n Y _ _ _ _ _ _ ι La _ A H G hH
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_atlasBallPartitionCover n Y ι La A
  obtain ⟨k0, hk0⟩ := GlobalTheory.T.curvature_lower_bound_on_cover_balls n Y ι La A C H G hH 0
  refine ⟨k0, fun k hk i y hy ξ => ?_⟩
  have hcurv := hk0 k hk

  have hex : ∃ a, C.chi a y ≠ 0 := by
    by_contra hno
    push_neg at hno
    have := C.sum_one y
    simp [hno] at this
  obtain ⟨a, ha⟩ := hex
  have hts : y ∈ tsupport (C.chi a) := subset_tsupport _ (Function.mem_support.2 ha)
  obtain ⟨hsrc, hball⟩ := C.supp a hts
  have hsm : A.SmoothFn (fun _ : Y => (0 : ℝ)) := fun _ => contDiffOn_const
  have ht := A.levi_transfer (G + k • H) (fun _ => (0 : ℝ)) hsm i (C.idx a) hy hsrc ξ
  simp only [add_zero] at ht ⊢
  rw [ht]
  have h1 := hcurv a (A.chart (C.idx a) y) hball
    (fderiv ℂ ((A.chart (C.idx a)) ∘ (A.chart i).symm) (A.chart i y) (WithLp.toLp 2 ξ)).ofLp
  rw [(A.chart (C.idx a)).left_inv hsrc, zero_mul] at h1
  exact h1

end GlobalTheory.SemiPosLarge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelWeilAnisotropic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

def LaurentConst (h : ℂ → ℂ) (s₀ c : ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Tendsto (fun s => h s - p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 c)

open Classical in

def withReal {F : Type} [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) : Finset (Pl F) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ ∪ Sf.map ⟨Sum.inr, Sum.inr_injective⟩

section Interface

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)

def zGlob {π : O.Pi} (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch) (s : ℂ) : ℂ :=
  ∫ g : O.GQ × O.GQ, O.Eis (O.tensor φ₁ φ₂) s (O.io g.1 g.2) * star (O.form π f₁ g.1) * O.form π f₂ g.2 *
    O.muInv g.2 ∂(O.muG.prod O.muG)

def HalfPlaneCont (π : O.Pi) (S : Finset (Pl F)) (t : ℕ) (g : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ g {s | (t : ℝ) / 2 ≤ s.re} ∧
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → HasProd (fun v : {v : Pl F // v ∉ S} => O.Lv π v (s + 1 / 2)) (g s)

def TripleIntegrable {π : O.Pi} (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch) : Prop :=
  Integrable (fun p : (O.GQ × O.GQ) × O.HQ => O.thetaK φ₁ p.1.1 p.2 * star (O.thetaK φ₂ p.1.2 p.2) *
    star (O.form π f₁ p.1.1) * O.form π f₂ p.1.2) ((O.muG.prod O.muG).prod O.muH)

variable (F E) in

def DInvAnalytic : Prop :=
  ∀ (n M : ℕ) (P : HeightOneSpectrum (𝓞 F) → Prop), ∃ e : ℂ → ℂ, AnalyticOnNhd ℂ e {s | 1 / 2 < s.re} ∧
    ∀ s : ℂ, 1 / 2 < s.re → e s ≠ 0 ∧ (∀ w : HeightOneSpectrum (𝓞 F), dvLoc (E := E) n M w s ≠ 0) ∧
      HasProd (fun w : {w // P w} => (dvLoc (E := E) n M w.1 s)⁻¹) (e s)

def Measurability : Prop :=
  SFinite O.muG ∧ (∀ φ, O.good φ → Measurable fun p : O.GQ × O.HQ => O.thetaK φ p.1 p.2) ∧
    (∀ π f, Measurable (O.form π f)) ∧ Measurable O.muInv ∧ ∀ g, ‖O.muInv g‖ = 1

def FlatLocal : Prop :=
  ∀ (π : O.Pi) (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch), O.good φ₁ → O.good φ₂ → ∀ v : Pl F,
    ∃ (Y : Type) (_ : MeasurableSpace Y) (ν : Measure Y) (f : Y → ℂ) (a : Y → ℝ),
      Measurable a ∧ (∀ y, 0 < a y) ∧ (∀ y, a y ≤ 1) ∧ ∀ s : ℂ,
        (O.zconv π f₁ f₂ φ₁ φ₂ v s ↔
          Integrable (GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand f a (((B.rank : ℂ) - A.rank) / 2) s) ν) ∧
        (O.zconv π f₁ f₂ φ₁ φ₂ v s →
          O.Zv π f₁ f₂ φ₁ φ₂ v s = GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatZeta ν f a (((B.rank : ℂ) - A.rank) / 2) s)

def CuspDecay : Prop :=
  ∀ (π : O.Pi) (f₁ f₂ : O.Vec π) (N : ℝ),
    Integrable (fun g : O.GQ × O.GQ => (max 1 (O.ht (O.io g.1 g.2))) ^ N * ‖O.form π f₁ g.1‖ * ‖O.form π f₂ g.2‖)
      (O.muG.prod O.muG)

def SiegelWeilAnisotropic : Prop :=
  ∀ t : ℕ, B.rank = A.rank + t → 1 ≤ t → wittIdx B = 0 → ∀ φ₁ φ₂, O.good φ₁ → O.good φ₂ → ∀ g,
    AnalyticAt ℂ (fun s => O.Eis (O.tensor φ₁ φ₂) s g) ((t : ℂ) / 2) ∧
      O.Eis (O.tensor φ₁ φ₂) ((t : ℂ) / 2) g = Ith O (O.tensor φ₁ φ₂) g

def SiegelWeilConvergent : Prop :=
  ∀ t : ℕ, B.rank = A.rank + t → A.rank < t → ∀ φ₁ φ₂, O.good φ₁ → O.good φ₂ → ∀ g,
    O.Eis (O.tensor φ₁ φ₂) ((t : ℂ) / 2) g = Ith O (O.tensor φ₁ φ₂) g

def EisensteinRegular : Prop :=
  ∀ φ₁ φ₂, O.good φ₁ → O.good φ₂ →
    (∀ s₀ : ℂ, (A.rank : ℝ) / 2 < s₀.re → ∀ g, AnalyticAt ℂ (fun s => O.Eis (O.tensor φ₁ φ₂) s g) s₀) ∧
    ∀ s₀ : ℂ, (∀ g, AnalyticAt ℂ (fun s => O.Eis (O.tensor φ₁ φ₂) s g) s₀) →
      ∃ C N : ℝ, ∀ᶠ s in 𝓝 s₀, Measurable (fun g : O.GQ × O.GQ => O.Eis (O.tensor φ₁ φ₂) s (O.io g.1 g.2)) ∧
        ∀ g, ‖O.Eis (O.tensor φ₁ φ₂) s g‖ ≤ C * (max 1 (O.ht g)) ^ N

def DoublingMeromorphic : Prop :=
  ∀ (π : O.Pi) (f₁ f₂ : O.Vec π) (φ₁ φ₂ : O.Sch), O.good φ₁ → O.good φ₂ → Meromorphic (zGlob O f₁ f₂ φ₁ φ₂)

def PairInputs : Prop :=
  Measurability O ∧ FlatLocal O ∧ CuspDecay O ∧ admW O ∧ DoublingBasicIdentity O ∧ SiegelWeilAnisotropic O ∧ SiegelWeilConvergent O ∧
    EisensteinRegular O ∧ DoublingMeromorphic O

variable {O}

def IsTensorModel {π : O.Pi} {n : ℕ} {I Xf : Type} (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) (loc : Xf → Xf → HeightOneSpectrum (𝓞 F) → ℂ) : Prop :=
  (∀ ι ι' i a, O.form π (vec (ι + ι') i a) = O.form π (vec ι i a) + O.form π (vec ι' i a)) ∧
  (∀ (c : ℂ) ι i a, O.form π (vec (c • ι) i a) = c • O.form π (vec ι i a)) ∧
  (∀ ι ι' i i' a b, O.be π (vec ι i a) (vec ι' i' b) = ⟪ι, ι'⟫_ℂ) ∧
  (∀ a, ∀ w ∈ Sf, loc a a w = 1) ∧
  ∀ ι ι' i a b, ∫ g, star (O.form π (vec ι i a) g) * O.form π (vec ι' i b) g ∂O.muG = ⟪ι, ι'⟫_ℂ * ∏ w ∈ Sf, loc a b w

def IsLocalValues {π : O.Pi} {n : ℕ} {I K Xf : Type} (t : ℕ) (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) (φ : I → K → O.Sch)
    (zf : Xf → Xf → HeightOneSpectrum (𝓞 F) → ℂ) (zr : I → I → K → InfinitePlace F → ℂ) : Prop :=
  ∀ ι ι' i i' k a b,
    (∀ w ∈ Sf, O.Zv π (vec ι i a) (vec ι' i' b) (φ i k) (φ i' k) (Sum.inr w) ((t : ℂ) / 2) = zf a b w) ∧
    ∀ ρ, O.Zv π (vec ι i a) (vec ι' i' b) (φ i k) (φ i' k) (Sum.inl ρ) ((t : ℂ) / 2) = zr i i' k ρ

def IsAdmissible {π : O.Pi} {n : ℕ} {I K Xf : Type} (t : ℕ) (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) (φ : I → K → O.Sch) : Prop :=
  ∀ ι ι' i i' k a b, RFData O π (vec ι i a) (vec ι' i' b) (φ i k) (φ i' k) (withReal Sf) ((t : ℂ) / 2)

end Interface

def LocalScalar {P Xf : Type} (Sf : Finset P) (loc zf : Xf → Xf → P → ℂ) : Prop :=
  ∀ w ∈ Sf, ∃ z : ℂ, ∀ a b, zf a b w = z * loc a b w

def IsUnitValue {P Xf : Type} (zf : Xf → Xf → P → ℂ) (w : P) (c : ℂ) : Prop :=
  Nonempty Xf → ∃ a, zf a a w = c

def IsLValue {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B) (π : O.Pi) (S : Finset (Pl F)) (t : ℕ) (c : ℂ) : Prop :=
  ∀ g, HalfPlaneCont O π S t g → c = g ((t : ℂ) / 2)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev ChainObj (D : D7) : Type 1 :=
  ∀ (_μ : D.what₂.Tup) (i : ℕ), RFObj D.host.F D.host.E (D.sp.Y i) (D.sp.Y (i + 1))

abbrev BlockObj (D : D7) : Type 1 :=
  ∀ (_μ : D.what₂.Tup) (j : ℕ), RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)

section Towers

variable (T : ThetaX D)

def IsPetClosed (V : HSp D) (ϖ : Submodule ℂ (T.cusp V)) : Prop :=
  ∀ G : T.cusp V, (∀ ε : ℝ, 0 < ε → ∃ G' ∈ ϖ, (T.pet V ((G - G' : T.cusp V) : T.AF V) (G - G')).re < ε) → G ∈ ϖ

def IsIrredCusp (V : HSp D) (ϖ : Submodule ℂ (T.cusp V)) : Prop :=
  ϖ ≠ ⊥ ∧ T.IsStable V (ϖ.map (T.cusp V).subtype) ∧ IsPetClosed T V ϖ ∧
    ∀ ϖ' ≤ ϖ, T.IsStable V (ϖ'.map (T.cusp V).subtype) → IsPetClosed T V ϖ' → ϖ' = ⊥ ∨ ϖ' = ϖ

def InnerProductLowRange (μ : D.what₂.Tup) (i : ℕ) (O : RFObj D.host.F D.host.E (D.sp.Y i) (D.sp.Y (i + 1)))
    (ev : T.AF (D.sp.Y i) →ₗ[ℂ] (O.GQ → ℂ)) : Prop :=
  (D.sp.Y (i + 1)).rank = (D.sp.Y i).rank + D.R.t → D.R.t ≤ (D.sp.Y i).rank →
  (wittIdx (D.sp.Y (i + 1)) = 0 ∨ wittIdx (D.sp.Y (i + 1)) < D.R.t) →
  ∀ ϖ : Submodule ℂ (T.cusp (D.sp.Y i)), IsIrredCusp T _ ϖ →
    (∀ l, 1 ≤ l → l ≤ wittIdx (D.sp.Y (i + 1)) → ∀ (Φ : T.Sch (D.sp.Y i) (T.YsLow D.R.t (i + 1) l)), ∀ G ∈ ϖ,
      Formalism.MainNotions.InnerProductFormulaField.thS T μ i _ Φ G = 0) →
    ∀ (π : O.Pi) (f₁ f₂ : O.Vec π), (∃ G ∈ ϖ, ev (G : T.AF _) = O.form π f₁) → (∃ G ∈ ϖ, ev (G : T.AF _) = O.form π f₂) →
    ∀ φ₁ φ₂, O.good φ₁ → O.good φ₂ → LaurentConst (zGlob O f₁ f₂ φ₁ φ₂) ((D.R.t : ℂ) / 2) (thetaIP O f₁ f₂ φ₁ φ₂)

def LowerLiftsVanish : Prop :=
  ∀ (μ : D.what₂.Tup) (i l : ℕ), i < D.R.m → 1 ≤ l → l ≤ (sigYD D.R (i + 1)).2 →
    ∀ (Φ : T.Sch (D.sp.Y i) (T.YsLow D.R.t (i + 1) l)) (G : T.cusp (D.sp.Y i)), Formalism.MainNotions.InnerProductFormulaField.IsTypeD T i G →
      Formalism.MainNotions.InnerProductFormulaField.thS T μ i _ Φ G = 0

end Towers

variable (Z : DivX D) (T : ThetaX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)

open Classical in

def finPl (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (μ : D.what₂.Tup) : Finset (Formalism.MainNotions.InnerProductFormulaField.Pl D) :=
  X.Sg ∪ Finset.univ.map (e μ)

def PlacesTie (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) : Prop :=
  ∀ μ, (∀ v, Z.qv μ v = Ideal.absNorm (e μ v).asIdeal) ∧ (∀ v, e μ v ∉ X.Sg) ∧
    ∀ w ∈ finPl Z X e μ, IsSplit (E := D.host.E) w

def DTie : Prop :=
  ∀ a, X.dFin a = ∏' w : Formalism.MainNotions.InnerProductFormulaField.Pl D, dvLoc (E := D.host.E) a (a + D.R.t) w ((D.R.t : ℂ) / 2)

def ConstTie (κC κB : ℕ → ℂ) (rC rB : ℕ → ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → (κC j ≠ 0 ∧ 0 < rC j ∧ X.cCh j = ‖κC j‖ ^ 2 * rC j) ∧
    (κB j ≠ 0 ∧ 0 < rB j ∧ X.cSb j = ‖κB j‖ ^ 2 * rB j)

def ChainTowerTie (μ : D.what₂.Tup) (i : ℕ) (O : RFObj D.host.F D.host.E (D.sp.Y i) (D.sp.Y (i + 1)))
    (evG : T.AF (D.sp.Y i) →ₗ[ℂ] (O.GQ → ℂ)) (evH : T.AF (D.sp.Y (i + 1)) →ₗ[ℂ] (O.HQ → ℂ)) (κ : ℂ) (φ : O.Sch) : Prop :=
  (∀ G, evG (T.conjAF _ G) = star (evG G)) ∧ (∀ G, evH (T.conjAF _ G) = star (evH G)) ∧
  (∀ G G' : T.cusp (D.sp.Y i), T.petY μ i (G : T.AF _) G' = ∫ g, star (evG G g) * evG G' g ∂O.muG) ∧
  (∀ G G' : T.cusp (D.sp.Y (i + 1)),
    T.petY μ (i + 1) (G : T.AF _) G' = (X.volCh Z μ (i + 1) : ℂ) * ∫ h, star (evH G h) * evH G' h ∂O.muH) ∧
  ∀ (G : T.cusp (D.sp.Y i)) (h : O.HQ),
    (T.mY μ i : ℂ) * evH (T.th _ _ (T.carY μ (i + 1) i) (T.carY μ (i + 1) (i + 1)) (T.PhiYup μ i) G) h =
      κ * ∫ g, O.thetaK φ g h * evG G g ∂O.muG

def OneFinitePart (μ : D.what₂.Tup) (i : ℕ) (πf : D.what₂.FT) {O : RFObj D.host.F D.host.E (D.sp.Y i) (D.sp.Y (i + 1))}
    (evG : T.AF (D.sp.Y i) →ₗ[ℂ] (O.GQ → ℂ)) {π : O.Pi} {n : ℕ} {Xf : Type}
    (vec : EuclideanSpace ℂ (Fin n) → Unit → Xf → O.Vec π) : Prop :=
  (∀ x ∈ D.what₂.EEpart πf, Formalism.MainNotions.InnerProductFormulaField.upChain D μ i x ∈ Submodule.span ℂ
    {u : D.what₂.Mult μ i | ∃ ι a, evG ((T.rowAF μ i u : T.cusp _) : T.AF _) = O.form π (vec ι () a)}) ∧
  ∀ ι, ι ≠ 0 → ∃ ϖ : Submodule ℂ (T.cusp (D.sp.Y i)), IsIrredCusp T _ ϖ ∧ (∀ G ∈ ϖ, Formalism.MainNotions.InnerProductFormulaField.IsTypeD T i G) ∧
    ∀ a, ∃ G ∈ ϖ, evG (G : T.AF _) = O.form π (vec ι () a)

def ChainNumbersTie (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (μ : D.what₂.Tup) (i : ℕ) (πf : D.what₂.FT)
    {O : RFObj D.host.F D.host.E (D.sp.Y i) (D.sp.Y (i + 1))} (π : O.Pi) {Xf : Type}
    (zf : Xf → Xf → Formalism.MainNotions.InnerProductFormulaField.Pl D → ℂ) (zr : Unit → Unit → Unit → InfinitePlace D.host.F → ℂ) (r : ℝ) : Prop :=
  IsLValue O π (withReal (finPl Z X e μ)) D.R.t (X.LChS μ (i + 1) πf) ∧
  (∀ w ∈ X.Sg, IsUnitValue zf w (X.ZgCh μ (i + 1) πf w)) ∧ (∀ v, IsUnitValue zf (e μ v) (Z.ZQ μ v (i + 1))) ∧
  ∏ ρ, zr () () () ρ = (r : ℂ) * X.ZChR (i + 1)

def ChainInputs (O : ChainObj D) (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (κ : ℕ → ℂ) (r : ℕ → ℝ) : Prop :=
  ∀ μ i, i < D.R.m → ∃ (evG : T.AF (D.sp.Y i) →ₗ[ℂ] ((O μ i).GQ → ℂ)) (evH : T.AF (D.sp.Y (i + 1)) →ₗ[ℂ] ((O μ i).HQ → ℂ))
    (φ : (O μ i).Sch), ChainTowerTie Z T X μ i (O μ i) evG evH (κ (i + 1)) φ ∧ InnerProductLowRange T μ i (O μ i) evG ∧
    ∀ πf, ∃ (π : (O μ i).Pi) (n : ℕ) (Xf : Type) (vec : EuclideanSpace ℂ (Fin n) → Unit → Xf → (O μ i).Vec π)
      (loc zf : Xf → Xf → Formalism.MainNotions.InnerProductFormulaField.Pl D → ℂ) (zr : Unit → Unit → Unit → InfinitePlace D.host.F → ℂ),
      IsTensorModel (finPl Z X e μ) vec loc ∧ IsLocalValues D.R.t (finPl Z X e μ) vec (fun _ (_ : Unit) => φ) zf zr ∧
      OneFinitePart T μ i πf evG vec ∧ IsAdmissible D.R.t (finPl Z X e μ) vec (fun _ (_ : Unit) => φ) ∧
      LocalScalar (finPl Z X e μ) loc zf ∧ (∃ g, HalfPlaneCont (O μ i) π (withReal (finPl Z X e μ)) D.R.t g) ∧
      ChainNumbersTie Z X e μ i πf π zf zr (r (i + 1))

def BlockMapTie (μ : D.what₂.Tup) (j : ℕ) (O : RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)) {I K : Type} [Fintype I] [Fintype K]
    (evW : D.what₂.Mj j →ₗ[ℂ] (I → O.GQ → ℂ)) (evV : D.what₂.Mt μ j →ₗ[ℂ] (K → O.HQ → ℂ)) (κ : ℂ) (φ : I → K → O.Sch) : Prop :=
  (∀ x y, ⟪x, y⟫_ℂ = ∑ i, ∫ g, star (evW x i g) * evW y i g ∂O.muG) ∧
  (∀ y k, MemLp (evV y k) 2 O.muH) ∧
  (∀ y y', ⟪y, y'⟫_ℂ = (X.volSb Z μ j : ℂ) * ∑ k, ∫ h, star (evV y k h) * evV y' k h ∂O.muH) ∧
  ∀ y x, ⟪D.what₂.thetaP μ j y, x⟫_ℂ = ∑ i, ∫ g,
    star (κ * (X.volSb Z μ j : ℂ) * ∑ k, ∫ h, O.thetaK (φ i k) g h * evV y k h ∂O.muH) * evW x i g ∂O.muG

def BlockPart (j : ℕ) (πf : D.what₂.FT) {O : RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)} {I : Type}
    (evW : D.what₂.Mj j →ₗ[ℂ] (I → O.GQ → ℂ)) {π : O.Pi} {n : ℕ} {Xf : Type}
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) : Prop :=
  D.what₂.isot j πf ≤ Submodule.span ℂ {x : D.what₂.Mj j | ∃ ι a, ∀ i, evW x i = O.form π (vec ι i a)}

def LiftHasType (μ : D.what₂.Tup) (j : ℕ) {O : RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)} {I K : Type} [Fintype I]
    (evV : D.what₂.Mt μ j →ₗ[ℂ] (K → O.HQ → ℂ)) (φ : I → K → O.Sch) {π : O.Pi} {n : ℕ} {Xf : Type}
    (vec : EuclideanSpace ℂ (Fin n) → I → Xf → O.Vec π) : Prop :=
  ∀ ι a, ∃ y : D.what₂.Mt μ j, ∀ k h, evV y k h = ∑ i, star (thetaLift O (vec ι i a) (φ i k) h)

def BlockNumbersTie (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (μ : D.what₂.Tup) (j : ℕ) (πf : D.what₂.FT)
    {O : RFObj D.host.F D.host.E (D.sp.W j) (D.sp.V j)} (π : O.Pi) {I K Xf : Type} [Fintype I] [Fintype K]
    (zf : Xf → Xf → Formalism.MainNotions.InnerProductFormulaField.Pl D → ℂ) (zr : I → I → K → InfinitePlace D.host.F → ℂ) (r : ℝ) : Prop :=
  IsLValue O π (withReal (finPl Z X e μ)) D.R.t (X.LsS μ j πf) ∧
  (∀ w ∈ X.Sg, IsUnitValue zf w (X.ZgSb μ j πf w)) ∧ (∀ v, IsUnitValue zf (e μ v) (Z.quotientLocalValueFirst μ v)) ∧
  ∑ k, ∑ i, ∑ i', ∏ ρ, zr i i' k ρ = (r : ℂ) * X.ZSbR j * Fintype.card I

def BlockInputs (O : BlockObj D) (e : ∀ μ, Z.QPl μ ↪ Formalism.MainNotions.InnerProductFormulaField.Pl D) (κ : ℕ → ℂ) (r : ℕ → ℝ) : Prop :=
  ∀ μ j, 1 ≤ j → j ≤ D.R.m → ∃ (I K : Type) (_ : Fintype I) (_ : Fintype K)
    (evW : D.what₂.Mj j →ₗ[ℂ] (I → (O μ j).GQ → ℂ)) (evV : D.what₂.Mt μ j →ₗ[ℂ] (K → (O μ j).HQ → ℂ))
    (φ : I → K → (O μ j).Sch), BlockMapTie Z X μ j (O μ j) evW evV (κ j) φ ∧
    ∀ πf, ∃ (π : (O μ j).Pi) (n : ℕ) (Xf : Type) (vec : EuclideanSpace ℂ (Fin n) → I → Xf → (O μ j).Vec π)
      (loc zf : Xf → Xf → Formalism.MainNotions.InnerProductFormulaField.Pl D → ℂ) (zr : I → I → K → InfinitePlace D.host.F → ℂ),
      IsTensorModel (finPl Z X e μ) vec loc ∧ IsLocalValues D.R.t (finPl Z X e μ) vec φ zf zr ∧
      BlockPart j πf evW vec ∧ LiftHasType μ j evV φ vec ∧ IsAdmissible D.R.t (finPl Z X e μ) vec φ ∧
      LocalScalar (finPl Z X e μ) loc zf ∧ (∃ g, HalfPlaneCont (O μ j) π (withReal (finPl Z X e μ)) D.R.t g) ∧
      BlockNumbersTie Z X e μ j πf π zf zr (r j)

end GlobalTheory.ThetaInner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfNilpotentReductionStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_nilpotent_reduction : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (g : ℕ) (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    SmoothOfRelativeDimension g X₀.hom → SmoothOfRelativeDimension g X.hom := by
  first | exact @GlobalTheory.LiftDim.smoothOfRelativeDimension_of_reduction | exact GlobalTheory.LiftDim.smoothOfRelativeDimension_of_reduction | (intros; apply GlobalTheory.LiftDim.smoothOfRelativeDimension_of_reduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEnlargeGoodAtOrigin
section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginEnlarge

theorem enlarge_good : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A')
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime),
      QA'.comap (algebraMap (Polynomial A') EA') = GlobalTheory.KeyOriginCut.originIdeal A' ∧ IsUnit (q : A') ∧
      ∃ (ρ' : Localization.AtPrime QA' →+* A'),
        ρ'.comp (algebraMap A' (Localization.AtPrime QA')) = RingHom.id A' ∧
        RingHom.ker ρ' = Ideal.span {algebraMap (Polynomial A') (Localization.AtPrime QA') Polynomial.X} ∧
      ∃ (jA' : Localization.AtPrime QA' →+* O)
        (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA'.comp (algebraMap (Localization.AtPrime QA') (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA' ∧
      ∃ (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
        (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA' q actA' ∧
        GlobalTheory.KeyOriginNoeth.Good A' (Localization.AtPrime QA') DA' ρ' ∧
        ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA'))
          (h : DA →+* DA'),
          ψA'.comp β = ψA ∧
          h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
            (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i hi hil hqA EA _ _ _ _ _ QA _ hQA jA hjA
    ψA hψA DA _ _ actA htor
  have hF : GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA :=
    ⟨hi, hil, hqA, hQA, hjA, hψA, htor⟩
  obtain ⟨A₁, _, _, _, _, _, _, i₁, EA₁, _, _, _, _, _, QA₁, _, jA₁, ψA₁, DA₁, _, _, act₁, hF₁,
    ⟨ρ₁, hR₁, -⟩, β₁, h₁, hβ₁, hh₁⟩ := GlobalTheory.T.enlarge_strictHenselisation_retract_mod T O hT P φ hφ hsh hP q hq0 hqT A i EA QA jA ψA DA actA hF
  obtain ⟨A₂, _, _, _, _, _, _, i₂, EA₂, _, _, _, _, _, QA₂, _, jA₂, ψA₂, DA₂, _, _, act₂, hF₂,
    ⟨ρ₂, hR₂, hpt₂⟩, β₂, h₂, hβ₂, hh₂⟩ :=
    GlobalTheory.T.enlarge_base_separable_point_integralClosure T O hT P φ hφ hsh hP q hq0 hqT A₁ i₁ EA₁ QA₁ jA₁ ψA₁ DA₁ act₁ hF₁ ρ₁ hR₁
  obtain ⟨A₃, _, _, _, _, _, _, i₃, EA₃, _, _, _, _, _, QA₃, _, jA₃, ψA₃, DA₃, _, _, act₃, hF₃,
    ⟨ρ₃, hR₃, hgood⟩, β₃, h₃, hβ₃, hh₃⟩ :=
    GlobalTheory.T.etale_enlarge_by_uniformiser_roots T O hT P φ hφ hsh hP q hq0 hqT A₂ i₂ EA₂ QA₂ jA₂ ψA₂ DA₂ act₂ hF₂ ρ₂ hR₂ hpt₂
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    EA₃, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, QA₃, inferInstance,
    hF₃.2.2.2.1, hF₃.2.2.1, ρ₃, hR₃.1, hR₃.2.1, jA₃, ψA₃, hF₃.2.2.2.2.2.1, DA₃, inferInstance,
    inferInstance, act₃, hF₃.2.2.2.2.2.2, hgood, β₃.comp (β₂.comp β₁), h₃.comp (h₂.comp h₁), ?_, ?_⟩
  · ext x
    have a1 := RingHom.congr_fun hβ₁ x
    have a2 := RingHom.congr_fun hβ₂ (β₁ x)
    have a3 := RingHom.congr_fun hβ₃ (β₂ (β₁ x))
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a3, a2, a1]
  · ext x
    have a1 := RingHom.congr_fun hh₁ x
    have a2 := RingHom.congr_fun hh₂ (β₁ x)
    have a3 := RingHom.congr_fun hh₃ (β₂ (β₁ x))
    simp only [RingHom.comp_apply] at a1 a2 a3 ⊢
    rw [a1, a2, a3]

end GlobalTheory.KeyOriginEnlarge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEtaleOverPolynomialStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictHenselisation_etale_over_polynomial_alt : ∀ (T E : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing E]
    [Algebra (Polynomial T) E] [Algebra T E] [IsScalarTower T (Polynomial T) E]
    [Algebra.Etale (Polynomial T) E] (y : Ideal E) [y.IsPrime],
    ∃ (S : Type) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra E S) (_ : Algebra T S)
      (_ : IsScalarTower T E S) (_ : Algebra (Polynomial T) S) (_ : IsScalarTower T (Polynomial T) S)
      (_ : IsScalarTower (Polynomial T) E S),
      (IsLocalRing.maximalIdeal S).comap (algebraMap E S) = y ∧ Module.Flat E S ∧
      GlobalTheory.LocAcyc.LocPiecesEtale E S ∧
      ∃ φ : Localization.AtPrime (y.comap (algebraMap (Polynomial T) E)) →+* S,
        φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) S ∧
        GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ := by
  first | (exact @GlobalTheory.strictHenselisation_etale_over_polynomial) | (exact GlobalTheory.strictHenselisation_etale_over_polynomial) | (intros; apply GlobalTheory.strictHenselisation_etale_over_polynomial  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstGroupLawEqMulOfDualTateCharacter
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
open TensorProduct

namespace GlobalTheory.QLog.Chart

theorem subst_μ_eq_inL_mul_inR : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) →
    subst c.μ u = inL u * inR u := by
  intro p _ O _ _ _ G d c χ u hu
  set D := subst c.μ u - inL u * inR u with hD
  have hev : ∀ n, c.ev₂ n D = 0 := by
    intro n
    obtain ⟨h1, h2, h3, -⟩ := ev₂_eval p O G d c n u
    rw [hD, map_sub, map_mul, h1, h2, h3, hu n, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      (isGroupLikeElem_charElem χ n).comul_eq_tmul_self, sub_self]
  rw [← sub_eq_zero, ← hD]
  ext α
  rw [map_zero]
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(p : O)})) _ fun m => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  obtain ⟨n, hn⟩ := c.ker m (α.degree + 1)
  exact T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O (G.A n) (G.A n) (Fin d) (Fin d) (c.x n) (c.x n) (c.ev n) (c.ev n) (c.ev₂ n) m
    (α.degree + 1) (c.isEval n) (c.isEval n) (c.isEval₂ n) (c.surj n) (c.surj n) hn hn D (hev n) α
    (Nat.lt_succ_self _)

end GlobalTheory.QLog.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSubValueEqSumSqZeroVectorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_sub_value_eq_sum_sqZero_vector : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → ∀ τ : (I → ℂ) → Fin g → ℂ, AnalyticAt ℂ τ 0 → ∃ n : Fin r → Fin g → R, (∀ j a, n j a ∈ J) ∧ (∀ j a b, n j a * n j b = 0) ∧ ∀ a, taylor N (fun i ↦ ∑ j, m j i) (fun z ↦ τ z a) - algebraMap ℂ R (τ 0 a) = ∑ j, n j a := by
  first | exact @GlobalTheory.PeriodFamily.taylor_sub_value_eq_sum_sqZero | exact GlobalTheory.PeriodFamily.taylor_sub_value_eq_sum_sqZero | (intros; apply GlobalTheory.PeriodFamily.taylor_sub_value_eq_sum_sqZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationLinearPullbackStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedOneFormEvaluation_linear_pullback : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (p : Pair φ.left), ∀ z ∈ pre u'.ex p.1.1.1, M z ∈ pre u.ex p.1.2.1 ∧ (∀ b, val u'.ex p.1.1.1 (secPull (str A) (str A') p b) z = val u.ex p.1.2.1 b (M z)) ∧ ∀ ξ, evForm u'.ex p.1.1.1 z ((semiHom_secPull h p).m1 ξ) = (evForm u.ex p.1.2.1 (M z) ξ).comp M := by
  first | exact @GlobalTheory.CechPer.evForm_secPull | exact GlobalTheory.CechPer.evForm_secPull | (intros; apply GlobalTheory.CechPer.evForm_secPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRestrictionEqStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evForm_restriction_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U V : A.left.affineOpens) (a : Opposite.op U ⟶ Opposite.op V) (ξ : Ω[Sec (str A) U.1⁄ℂ]), ∀ z ∈ pre u.ex V.1, evForm u.ex V.1 z (p1 (OAff (str A)) a ξ) = evForm u.ex U.1 z ξ := by
  first | exact @GlobalTheory.CechPer.uniformisedOneFormEvaluation_restriction_eq | exact GlobalTheory.CechPer.uniformisedOneFormEvaluation_restriction_eq | (intros; apply GlobalTheory.CechPer.uniformisedOneFormEvaluation_restriction_eq <;> assumption)
end

