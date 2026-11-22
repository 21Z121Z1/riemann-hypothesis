import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFSingleOne

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
section
noncomputable section

open NumberField Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE npow)
open scoped TensorProduct NNReal

namespace GlobalTheory.Published

def EisensteinMaximalParabolic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (j : ℕ) (hj : j ≤ r) (C : Matrix (Fin n) (Fin j) E), C = X.submatrix id (Fin.castLE hj) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ≥0,
        (∀ (p : GAd σ J) (b : GL (Fin j) (AF F ⊗[F] E)), (matHom _ σ J p).1 * adMat F C = adMat F C * b.1 →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E (Matrix.GeneralLinearGroup.det b)) →
      ∀ φ : GAd σ J → ℂ, IsAutOn σ J (leftGrp σ J C fun _ => 0) (levelAll σ J L a) φ →
      ∃ (Eis : ℂ → GAd σ J → ℂ) (σ₀ : ℝ),
        (∀ s : ℂ, σ₀ < s.re → ∀ g,
          GlobalTheory.Eis.CosetConv (parFlag σ J C fun _ => 0) (ratPts σ J) (fun x => φ x * npow (h x) s) g ∧
          Eis s g = GlobalTheory.Eis.cosetSum (parFlag σ J C fun _ => 0) (ratPts σ J) (fun x => φ x * npow (h x) s) g) ∧
        ∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
          (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
          ∀ μ, IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentityHecke
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch

def RegBy {D : D7} {n : ℕ} {V V₀ : HSp D} {r : ℕ} {K : Subgroup (GA D V)} (ν : Measure K)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {θ : InfFam D} (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (d : HypDec V V₀ r) (m : Measure (GA D V)) (z : Loc V v →₀ ℂ) (P : ℂ → ℂ) (Φ Ψ : schwartzA θ V.rank n) : Prop :=
  Ψ.1 = heckeS ν z Φ.1 ∧ (∀ s, heckeF ν z (sphericalSectionIwasawa d K s) = P s • sphericalSectionIwasawa d K s) ∧
  (∀ g, Grow.RapidDec V (StdUnn.theta ω Ψ g)) ∧
  ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ g,
    Integrable (descend (GQ V) fun h => StdUnn.theta ω Ψ g h * sphericalEisensteinSeriesOnGroup d K h s) (autMeasure V m)

end GlobalTheory.RegSch

namespace GlobalTheory.Published

open GlobalTheory.RegSch

def FirstTermIdentityHecke : Prop :=
  ∀ (D : D7) (n : ℕ) (T T' : HSp D) (t : ℕ) (d : HypDec T T' t),
    T.rank + T'.rank = 2 * n → T'.rank < T.rank → 0 < T'.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ T.rank →
  ∀ (μ : Measure (Mx D T.rank n)) (𝓕 : Set (Mx D T.rank n)), IsCovolOne (ratMx D T.rank n) μ 𝓕 →
  ∀ (μ' : Measure (Mx D T'.rank n)) (𝓕' : Set (Mx D T'.rank n)), IsCovolOne (ratMx D T'.rank n) μ' 𝓕' →
  ∀ (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
  ∀ (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ T.rank n)) (ω' : StdUnn.G D n →* Module.End ℂ (schwartzA θ T'.rank n)),
    StdUnn.IsWeilSch ψ χ θ T μ ω → StdUnn.IsWeilSch ψ χ θ T' μ' ω' →
  ∀ H : StdUnn.G D n → ℝ≥0, StdUnn.IsHeight H →
  ∀ (l : Lvl T) (l' : Lvl T'), l.Good → l'.Good → Compat d l l' → HasIw d l.K →
  ∀ ν : Measure l.K, ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ m : Measure (GA D T'), m.IsHaarMeasure →
  ∀ lr : D.what₂.Tau → ℝ, StdUnn.HasRealPar ψ θ lr →
  ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) →
    (∀ k ∈ l.K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) →
    (IsAniso T' → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : schwartzA θ T.rank n, Φ.1 ∈ StdUnn.fockA θ T n lr s → KFin ω Φ →
      ∀ Φ' : schwartzA θ T'.rank n, Φ'.1 = ikS d μ₁ (projS ν Φ.1) → ∀ g,
        ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) (κ * StdUnn.thetaInt ω' m Φ' g)) ∧
    ∀ (T₀ : HSp D) (r' : ℕ) (d₀ : HypDec T' T₀ r'), IsAniso T₀ → 0 < r' →
    ∀ l₀ : Lvl T₀, l₀.Good → Compat d₀ l' l₀ → HasIw d₀ l'.K →
    ∀ ν' : Measure l'.K, ν'.IsHaarMeasure → IsProbabilityMeasure ν' →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : schwartzA θ T.rank n, Φ.1 ∈ StdUnn.fockA θ T n lr s → KFin ω Φ →
        ∀ Φ' : schwartzA θ T'.rank n, Φ'.1 = ikS d μ₁ (projS ν Φ.1) →
          ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Loc T' v →₀ ℂ) (P : ℂ → ℂ) (Ψ : schwartzA θ T'.rank n),
            RegBy ν' ω' d₀ m z P Φ' Ψ ∧ ∀ g, ∃ B : ℂ, ResidueAt (regIntH l'.K ω' d₀ m P Ψ g) (rhoH T' r') B ∧
              ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) (κ * B)

end GlobalTheory.Published

end
end

