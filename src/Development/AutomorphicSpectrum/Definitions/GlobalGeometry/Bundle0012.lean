import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Ht

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp

section Points

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ptHt (a : K → ℝ) (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) : ℝ :=
  (Module.finrank ℚ L : ℝ)⁻¹ *
    ((∑ᶠ v : FinitePlace L, ∑ k, a k * Real.log (⨆ i, v (w ⟨k, i⟩))) + ∑ σ : L →+* ℂ, φ fun p => σ (w p))

def lineHt (A : HermLine ι) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L) : ℝ :=
  ptHt (fun k => (A.a k : ℝ)) (fun z => Real.log (A.h z)) L w

def GenUnit (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) : Prop :=
  ∀ (L : Type) [Field L] [CharZero L], ∀ z ∈ ptsOver L (mCoordIdeal y), ∃ val : L, val ≠ 0 ∧ HasVal y a u z val

def VertBound (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (c : ℝ) : Prop :=
  u ≠ 0 ∧ ∃ q m : ℕ, 0 < q ∧ 0 < m ∧ Real.log m ≤ q * c ∧ (m : Ω) * u ^ q ∈ chartLatNm y a q ∧
    (m : Ω) * u⁻¹ ^ q ∈ chartLatNm y (-a) q

def PlaceBound (y : (Σ k, ι k) → Ω) (a : K → ℤ) (u : Ω) (g : MRing ι) (α : ℕ → ℝ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], ∀ z ∈ algPts p (mCoordIdeal y), aeval z g ≠ 0 →
    ValLe y a u z (Real.exp (α p) * supMet a z)

def AmpleQ (y : (Σ k, ι k) → Ω) (a : K → ℤ) : Prop :=
  ∃ (m l : ℕ) (s : Fin l → Ω), (∀ i, s i ∈ chartLatNm y (fun k => m * a k - 1) 1) ∧
    ∀ (L : Type) [Field L] [CharZero L], ∀ z ∈ ptsOver L (mCoordIdeal y),
      ∃ (i : Fin l) (val : L), val ≠ 0 ∧ HasVal y (fun k => m * a k - 1) (s i) z val

end Points

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

def rootHt (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, M.ι k) → L) : ℝ :=
  ∑ j, M.coef lam s j * lineHt (M.line t j) L w

def joinOf (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) : (Σ k, joinIdx M.ι R.ι k) → M.Ω :=
  joinVec M.y fun p => i (R.y p)

def joinDeg (M R : RootModel Ψ N) (j : Option (Ψ × Fin N)) : M.K ⊕ R.K → ℤ :=
  Sum.elim (M.line 1 j).a (-(R.line 1 j).a)

structure Close (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (c : ℝ) : Prop where
  kA : M.kA = R.kA
  unit : ∀ j, GenUnit (joinOf M R i) (joinDeg M R j) (u j)
  vert : ∀ j, VertBound (joinOf M R i) (joinDeg M R j) (u j) c

def ArchBetween (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (u : Option (Ψ × Fin N) → M.Ω) (t : ℝ) (lam : Wt Ψ N)
    (s lo hi : ℝ) : Prop :=
  ∀ z ∈ ptsOver ℂ (mCoordIdeal (joinOf M R i)), ∀ val : Option (Ψ × Fin N) → ℂ,
    (∀ j, HasVal (joinOf M R i) (joinDeg M R j) (u j) z (val j)) →
      ∑ j, M.coef lam s j * (Real.log ((M.line t j).h fun p => z (joinInl M.ι R.ι p)) -
        Real.log ((R.line 1 j).h fun p => z (joinInr M.ι R.ι p)) - Real.log ‖val j‖) ∈ Set.Icc lo hi

def HasRef (T : RootTower Ψ N) (R : T.Comp → RootModel Ψ N) : Prop :=
  ∃ (C s₀ : ℝ), 0 < s₀ ∧ ∀ B : ℕ, 2 ≤ B → ∀ c, ∃ (i : (R c).Ω →+* (T.M B c).Ω) (u : Option (Ψ × Fin N) → (T.M B c).Ω),
    Close (T.M B c) (R c) i u (C * Real.log B) ∧ ∀ (mu : Wt Ψ N) (s : ℝ), Dominant mu → ‖mu‖ ≤ 2 → 0 < s → s ≤ s₀ →
      ArchBetween (T.M B c) (R c) i u (scale s) mu s (-(C * Real.log (1 / s)) - C) C

def RefLower (R : RootModel Ψ N) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L R.P,
    -C ≤ rootHt R 1 0 1 L w ∧ ∀ mu : Wt Ψ N, Dominant mu → ‖mu‖ ≤ 2 →
      -(C * Real.log (2 + C + rootHt R 1 0 1 L w)) - C ≤ rootHt R 1 mu 0 L w

def FlatUnit (R : RootModel Ψ N) : Prop :=
  ∀ τ, ∃ (k : ℕ) (u : R.Ω) (c : ℝ), 0 < k ∧ GenUnit R.y (fun b => k * ∑ i, R.xdeg (τ, i) b) u ∧
    VertBound R.y (fun b => k * ∑ i, R.xdeg (τ, i) b) u c

def FibreInput {j k : ℕ} (R : RootModel Ψ (j + k)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L R.P,
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : L →+* L')
      (E : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L') (A : FlagPair E Ψ j k), A.IsOrthFull ∧
      (∀ τ (i : Fin j), |lineHt (R.x 1 (τ, Fin.castAdd k i)) L w - (A.W τ).grDeg i| ≤ C) ∧
      (∀ τ (i : Fin k), |lineHt (R.x 1 (τ, Fin.natAdd j i)) L w + (A.S τ).grDeg i.rev| ≤ C) ∧
      E.slopeMax ≤ ((C * Real.log (2 + C + max (-E.normDegree ⊤) 0) + C : ℝ) : EReal)

end GlobalTheory.CompanionTheory.Ar.Ht
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBareNormDisc
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

abbrev FracBase {O : Type} [CommRing O] (β : O →+* c.F) : Prop :=
  Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a

def Reads (U : Set (Xo.XF c)) (τ : E →+* ℂ) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) : Prop :=
  ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) (y : Sp F ⟶ Xo.XF c),
    under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) → Set.range y ⊆ U →
    ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q),
      (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) →
      (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) →
      ψ (s p z) = φ F y v w

def Restricts (Y : Model Xo c (RingHom.id c.F)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (sig : GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.Rule Y)
    (φ : FrameFn Xo c) : Prop :=
  ∀ (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (v' : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w' : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)),
    IsFramed U τ βF y v w → (∀ i, SameVec Y y (v i) (v' i)) → (∀ j, SameVec Y y (w j) (w' j)) →
    sig F (y ≫ Y.j) v' w' = φ F y v w

def UnitRule (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (sig : GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.Rule Y) :
    Prop :=
  ∀ (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Y.X) v w,
    GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.IsFrame Y U τ j x v w → IsUnit (sig R x v w)

def IsChart (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) (φ : FrameFn Xo c) {R : Type}
    [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Y.X) (v : Fin D.p → (epsAt x ⟶ Y.t.G))
    (w : Fin D.q → (epsAt x ⟶ Y.t.G)) (u : R) : Prop :=
  IsOpenImmersion x ∧ GlobalTheory.IndefiniteRowSideFullHecke.EigenbasisGramSquares.IsFrame Y U τ j x v w ∧
    ∀ (F : Type) [Field F] (f : R →+* F) (y : Sp F ⟶ Xo.XF c) (v₀ : Vecs y D.p) (w₀ : Vecs y D.q)
      (v' : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w' : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)),
      y ≫ Y.j = spMap f ≫ x → (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) →
      (∀ i, (w' i).left = spMap (dualMap f) ≫ (w i).left) →
      (∀ i, SameVec Y y (v₀ i) (v' i)) → (∀ i, SameVec Y y (w₀ i) (w' i)) → f u = φ F y v₀ w₀

def IsModelMap {O : Type} [CommRing O] {β : O →+* c.F} (Y' : Model Xo c (RingHom.id c.F)) (Y : Model Xo c β)
    (n : Y'.X ⟶ Y.X) (mu : SABMap Y'.t Y.t n) : Prop :=
  n ≫ Y.s = Y'.s ≫ spMap β ∧ Y'.j ≫ n = Y.j ∧
    ∀ (T : Scheme.{0}) (g' : T ⟶ Y'.oF.t.G.left) (g : T ⟶ Y.oF.t.G.left),
      g' ≫ Y'.oF.t.G.hom = g ≫ Y.oF.t.G.hom → g' ≫ Y'.m0.toSABMap.φ = g ≫ Y.m0.toSABMap.φ →
      g' ≫ Y'.m.φ ≫ mu.φ = g ≫ Y.m.φ

def IsBareFrame {V K : Type} [CommRing V] [Field K] [Algebra V K] {y : Sp K ⟶ Xo.XF c} {𝒢 : Over (Sp V)} [GrpObj 𝒢]
    (a₁ : OAct (𝓞 E) 𝒢) {A : Over (Sp K)} (φ₀ : A.left ⟶ Xo.univ.t.G.left) (φ₁ : A.left ⟶ 𝒢.left)
    (σ : 𝓞 E →+* K) {n : ℕ} (v : Vecs y n) : Prop :=
  ∃ (σV : 𝓞 E →+* V) (vV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ 𝒢)), (algebraMap V K).comp σV = σ ∧
    IsEigFrame a₁ (𝟙 (Sp V)) σV vV ∧ ∀ a, ∃ u : Sp (DualNumber K) ⟶ A.left,
      u ≫ φ₀ = (v a).left ∧ u ≫ φ₁ = spMap (dualMap (algebraMap V K)) ≫ (vV a).left

def BareNormOver (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (t : ℝ)
    (V K : Type) [CommRing V] [Field K] [Algebra V K] (j : K →+* ℂ_[p]) : Prop :=
  ∀ (β : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (𝒢 : Over (Sp V)) [GrpObj 𝒢]
    (a₁ : OAct (𝓞 E) 𝒢) (A : Over (Sp K)) [GrpObj A] (a : OAct (𝓞 E) A) (φ₀ : A.left ⟶ Xo.univ.t.G.left)
    (φ₁ : A.left ⟶ 𝒢.left), Function.Injective (algebraMap V K) →
    (∀ z : K, ‖j z‖ ≤ 1 ↔ z ∈ (algebraMap V K).range) → j.comp β = κ → IsFramed U τ β y v w → IsSemiAbelian 𝒢 →
    IsGrpPullback A Xo.univ.t.G (under y) φ₀ → IsGrpPullback A 𝒢 (spMap (algebraMap V K)) φ₁ →
    (∀ b, (a.act b).left ≫ φ₀ = φ₀ ≫ (Xo.univ.t.act.act b).left) → (∀ b, (a.act b).left ≫ φ₁ = φ₁ ≫ (a₁.act b).left) →
    IsBareFrame a₁ φ₀ φ₁ (β.comp (tauIn c τ)) v →
    IsBareFrame a₁ φ₀ φ₁ (β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w →
    Real.log ‖j (φ K y v w)‖ = t

def HasBareNormDisc (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p])
    (t : ℝ) : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] (j : K →+* ℂ_[p]),
    BareNormOver U τ φ p κ t V K j

def HasBareNorm (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p])
    (t : ℝ) : Prop :=
  ∀ (V K : Type) [CommRing V] [Field K] [Algebra V K] (j : K →+* ℂ_[p]), BareNormOver U τ φ p κ t V K j

example (Y : Model Xo c (RingHom.id c.F)) (U : (Xo.XF c).Opens) (τ : E →+* ℂ) :
    UnitRule Y U τ (fun _ _ _ _ _ => 1) := fun _ _ _ _ _ _ _ => isUnit_one

end GlobalTheory.CompanionTheory.Ar.Br
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

section Metric

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

structure LieMetric (M : LieModel G ξ Li) {K : Type} {J : K → Type} (y : (Σ k, J k) → Ω) where

  ip : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ
  herm : ∀ (z : Sp ℂ ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V),
    ∃ core : InnerProductSpace.Core ℂ V, ∀ a b, core.inner a b = ip z (Mz.pt a) (Mz.pt b)
  conj : ∀ (z : Sp ℂ ⟶ X) (v w : epsAt z ⟶ G) (v' w' : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G),
    v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left → w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left →
      ip _ v' w' = starRingEnd ℂ (ip z v w)
  cont : ∀ a b : Li, ∃ F : ((Σ k, J k) → ℂ) → ℂ,
    ContinuousOn F {w | ∃ (z : Sp ℂ ⟶ X) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w ∧ M.ValAt z a va ∧ M.ValAt z b vb} ∧
      ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w → M.ValAt z a va →
        M.ValAt z b vb → F w = ip z va vb

def LieMetric.Orth {M : LieModel G ξ Li} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (h : LieMetric M y)
    {O : Type} [CommRing O] (act : OAct O G) : Prop :=
  ∀ (z : Sp ℂ ⟶ X) (τ τ' : O →+* ℂ) (v w : epsAt z ⟶ G), τ ≠ τ' → IsLieEigen act z τ v → IsLieEigen act z τ' w →
    h.ip z v w = 0

variable {L : Type} [Field L] [NumberField L]

def IsFibre (rel : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ → Prop) (z : Sp (𝓞 L) ⟶ X)
    (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier) : Prop :=
  ∀ (σ : L →+* ℂ) (x x' : B.carrier) (v v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G),
    MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) x v → MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) x' v' →
      rel _ v v' ((B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x'))

def IsSubFibre (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) (F : Submodule (𝓞 L) V) : Prop :=
  ∀ x, x ∈ F ↔ ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L)
    {x' | ∃ e ∈ U, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
      M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v}

end Metric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure AbPart {S : Scheme.{0}} (t : SAB H S) {K : Type} [Field K] (z : Sp K ⟶ S) where

  tK : SAB H (Sp K)
  m : SABMap tK t z

  τ : TorusExtension tK.G

  tB : SAB H (Sp K)

  e : τ.B ≅ tB.G
  e_hom : letI := τ.grpB; IsMonHom e.hom
  act : ∀ a, tK.act.act a ≫ τ.q ≫ e.hom = τ.q ≫ e.hom ≫ tB.act.act a
  pp : LBIso tK.PP.L (tB.PP.L.pull (τ.q ≫ e.hom).left)

def IsPrincipal {K : Type} [Field K] (t : SAB H (Sp K)) : Prop :=
  IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L

def SlopeBoundSt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L]
    (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (_ : SABMap tK t (spMap (algebraMap (𝓞 L) L))), IsPrincipal tK →
    ∀ (B : HermitianBundle.{0} L) (MB : LieModel t.G (𝟙 _) B.carrier), IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB →
      B.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 L) B.carrier + max (-B.normDegree ⊤) 0) : ℝ) : EReal)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitCompsOfIsTowerOf
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TowerOfTest

open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

theorem factor {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : IsCptGen ξ) (ξ' : Spec (CommRingCat.of Ω') ⟶ X) (e : genPt ξ' = genPt ξ) :
    ∃ i : Ω →+* Ω', ξ' = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
  have key : ∀ (x x' : X) (_ : x' = x) (φ : X.presheaf.stalk x ⟶ CommRingCat.of Ω) [IsIso φ]
      (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of Ω'), ∃ i : Ω →+* Ω',
      Spec.map φ' ≫ X.fromSpecStalk x' = Spec.map (CommRingCat.ofHom i) ≫ Spec.map φ ≫ X.fromSpecStalk x := by
    intro x x' e φ _ φ'
    subst e
    refine ⟨(inv φ ≫ φ').hom, ?_⟩
    rw [CommRingCat.ofHom_hom, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id_assoc]
  haveI : IsIso (Scheme.stalkClosedPointTo ξ) := (ConcreteCategory.isIso_iff_bijective _).2 h.bij
  obtain ⟨i, hi⟩ := @key _ _ e (Scheme.stalkClosedPointTo ξ) this (Scheme.stalkClosedPointTo ξ')
  refine ⟨i, ?_⟩
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ').symm.trans (hi.trans
    (congrArg (Spec.map (CommRingCat.ofHom i) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)))

theorem spec_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

def SplitOver {O F : Type} [CommRing O] [Field F] {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of O))
    (β : O →+* F) : Prop :=
  ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (cst : F →+* Ω), IsCptGen ξ →
    ξ ≫ s = Spec.map (CommRingCat.ofHom (cst.comp β)) → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ cst.range

theorem isCptGen_id (K : Type) [Field K] : IsCptGen (𝟙 (Spec (CommRingCat.of K))) := by
  have hb : Function.Bijective (Scheme.stalkClosedPointTo (𝟙 (Spec (CommRingCat.of K)))).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 (by
      unfold Scheme.stalkClosedPointTo
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (by erw [Scheme.Hom.stalkMap_id]; exact IsIso.id _) inferInstance)
  exact ⟨hb, fun p => hb.1.comp (CptInh.spec_inj _ p.2)⟩

theorem splitOver_field (F K : Type) [Field F] [Field K] (j : F →+* K) :
    SplitOver (Spec.map (CommRingCat.ofHom j)) (RingHom.id F) ↔ ∀ a : K, IsAlgebraic ℤ a → a ∈ j.range := by
  constructor
  · intro h a ha
    exact h K (𝟙 _) j (isCptGen_id K) (by simp) a ha
  · intro h Ω _ ξ cst hξ hs a ha
    obtain ⟨i, hi⟩ := factor ξ hξ (𝟙 _) (Subsingleton.elim (α := PrimeSpectrum K) _ _)
    have e : i.comp cst = j := by
      apply spec_inj
      have : Spec.map (CommRingCat.ofHom j) = Spec.map (CommRingCat.ofHom i) ≫ ξ ≫ Spec.map (CommRingCat.ofHom j) := by
        rw [← Category.assoc, ← hi, Category.id_comp]
      rw [this, hs, ← Spec.map_comp]
      rfl
    obtain ⟨b, hb⟩ := h (i a) (ha.algHom i.toIntAlgHom)
    refine ⟨b, i.injective ?_⟩
    rw [← hb, ← e]; rfl

theorem splitOver_self (F : Type) [Field F] :
    SplitOver (Spec.map (CommRingCat.ofHom (RingHom.id F))) (RingHom.id F) :=
  (splitOver_field F F _).2 fun a _ => ⟨a, rfl⟩

theorem not_splitOver_complex : ¬ SplitOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) (RingHom.id ℚ) := by
  rw [splitOver_field]
  intro h
  have hI : IsAlgebraic ℤ Complex.I := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_, by simp⟩
    exact (Polynomial.monic_X_pow_add_C (1 : ℤ) two_ne_zero).ne_zero
  obtain ⟨b, hb⟩ := h _ hI
  have := congrArg Complex.im hb
  simp at this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem splitComps_iff {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    SplitComps Y ↔ SplitOver Y.s β := Iff.rfl

theorem splitComps_of_isTowerOf {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {T : Top.RootTower (CMType H) (D.p + D.q)} (h : IsTowerOf Y T) : SplitComps Y := by
  obtain ⟨o, -⟩ := h
  haveI := c.fin
  haveI : NumberField c.F := {}
  intro Ω _ ξ cst hξ hs a ha
  obtain ⟨k, hk⟩ := o.comp_onto (genPt ξ) (CptInh.nogen ξ hξ)
  obtain ⟨i, hi⟩ := factor ξ hξ (o.Fx k).ξf hk
  let R := o.Or 0 k
  have e0 : ((R.g.comp i).comp cst).comp (algebraMap (𝓞 c.F) c.F) = R.𝔐.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    apply spec_inj
    have h1 := R.𝔐.cst_over
    rw [← Category.assoc, R.g_over, hi, Category.assoc, Category.assoc, hs] at h1
    refine Eq.trans ?_ h1
    change _ = Spec.map (CommRingCat.ofHom R.g) ≫ Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom _)
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have e : (R.g.comp i).comp cst = R.𝔐.cst := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) e0
  obtain ⟨b, hb⟩ := R.g_const (i a) (ha.algHom i.toIntAlgHom)
  refine ⟨b, (R.g.comp i).injective ?_⟩
  rw [← e] at hb
  exact hb

theorem sign_pos_of_isTowerOf {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)}
    {T : Top.RootTower (CMType H) (D.p + D.q)} (h : IsTowerOf Y T) : 1 ≤ D.p ∧ 1 ≤ D.q ∧ Nonempty Y.X := by
  obtain ⟨o, -⟩ := h
  have h1 := T.j_pos
  have h2 := T.j_lt
  rw [o.j_eq] at h1 h2
  obtain ⟨k⟩ := T.neC
  exact ⟨h1, by omega, ⟨genPt (o.Fx k).ξf⟩⟩

section
variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}

theorem finrank_dual_Vgen (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H) :
    Module.finrank Ω (Module.Dual Ω (𝔐.Vgen s)) = labelRk D s := by
  obtain ⟨U, hU, b, hb, hf⟩ := 𝔐.vb s ⟨genPt 𝔐.ξ, specializes_rfl⟩ trivial
  have hl := (hf _ trivial hU).1
  rw [Subspace.dual_finrank_eq]
  have : 𝔐.Vgen s = Submodule.span Ω (Set.range b) := hb.symm
  rw [this, finrank_span_eq_card hl, Fintype.card_fin]

theorem htOm_le (𝔐 : HodgeCpt Y S y) (n : ℕ) (q : Cpt 𝔐.ξ) : 𝔐.M.htOm 𝔐.t.PP.L n q ≤ 𝔐.M.omLat q :=
  Submodule.span_le.2 fun _ ⟨_, _, h⟩ => h.1

theorem omVB_empty (𝔐 : HodgeCpt Y ∅ y) : 𝔐.OmVB := fun _ hp => absurd hp (Finset.notMem_empty _)

end

theorem two_mem_S {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {T : Top.RootTower (CMType H) (D.p + D.q)}
    (o : TowerOrigin Y T) (B : ℕ) : 2 ∈ o.S B := (o.S_iff B 2).2 ⟨Nat.prime_two, Or.inr T.two_mem⟩

end GlobalTheory.CompanionTheory.Ar.TowerOfTest
end
end

