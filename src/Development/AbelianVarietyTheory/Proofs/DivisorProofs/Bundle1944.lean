import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Formalism.LocalToGlobal.Divisibility.NumbersLink

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
section
noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsLocPart {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) : Prop :=
  ei ≠ 0 ∧ (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

def fac (χ : Chr F E) (z : ℝ) (t : (AE F E)ˣ) : ℂ := (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)

def LocOpMul : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ v : Pl F, ∀ x y : UA σ X.J × UA σ W.J,
      x.1 ∈ UAt σ X (evFin F v) → x.2 ∈ UAt σ W (evFin F v) → y.1 ∈ UAt σ X (evFin F v) → y.2 ∈ UAt σ W (evFin F v) →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), locOp v (om (x * y)) φ = locOp v (om x) (locOp v (om y) φ)

def EvZeroLocLaw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ ei ev, IsLocPart M M₁ e ei ev → ∀ v : Pl F, ∀ g ∈ UAt σ X (evFin F v), ∀ t h₁ m, IsLevi H' t h₁ m →
      m ∈ UAt σ W (evFin F v) → h₁ ∈ UAt σ W₁ (evFin F v) → ∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        ev v (locOp v (om (g, u * m)) φ) = fac χX ((n : ℝ) / 2) t • locOp v (om₁ (g, h₁)) (ev v φ)

def EvZeroInfLaw : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ ei ev, IsLocPart M M₁ e ei ev → ∀ g ∈ UAt σ X (evI F), ∀ t h₁ m, IsLevi H' t h₁ m →
      m ∈ UAt σ W (evI F) → h₁ ∈ UAt σ W₁ (evI F) → ∀ u ∈ unip σ W H', u ∈ UAt σ W (evI F) →
      ∀ f : SInf F (Fin n × Fin d),
        ei (locOpInf (om (g, u * m)) f) = fac χX ((n : ℝ) / 2) t • locOpInf (om₁ (g, h₁)) (ei f)

def ConeLawB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∈ SB (Fin b × Fin (a + b) → Fv F v)) ∧
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, u)) φ) =
          coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ) ∧
      ∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, m)) φ) =
          fac X.β ((a : ℝ) / 2) t •
            locOp v (om₁' (1, h₁)) (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ)

def ConeLawA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ ∈ SB (Fin b × Fin (b + a') → Fv F v)) ∧
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, u)) φ) =
          coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ) ∧
      ∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
      ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, m)) φ) =
          fac X.α ((a' : ℝ) / 2) t •
            locOp v (om₁ (1, h₁)) (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ)

def ConeInvB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V' (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), l (locOp v (om₁' (g₀, 1)) ψ) = l ψ) →
      ∀ g ∈ UAt σ G.V' (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        l (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (g, 1)) φ)) =
          l (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ)

def ConeInvA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure → ∀ l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), l (locOp v (om₁ (g₀, 1)) ψ) = l ψ) →
      ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        l (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (g, 1)) φ)) =
          l (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) φ)

def EvInvB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (l : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      (∀ g₀ ∈ UAt σ G₁.V' (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (a + b) → Fv F v), l (locOp v (om₁' (g₀, 1)) ψ) = l ψ) →
      (∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        l (ev' v (locOp v (om' (u, 1)) φ)) = l (ev' v φ)) ∧
      ∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V' (evFin F v) → g₀ ∈ UAt σ G₁.V' (evFin F v) →
        ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v), l (ev' v (locOp v (om' (g, 1)) φ)) = l (ev' v φ)

def EvInvA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ),
      (∀ g₀ ∈ UAt σ G₁.V (evFin F v), ∀ ψ ∈ SB (Fin b × Fin (b + a') → Fv F v), l (locOp v (om₁ (g₀, 1)) ψ) = l ψ) →
      (∀ u ∈ unip σ G.V H, u ∈ UAt σ G.V (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        l (ev v (locOp v (om (u, 1)) φ)) = l (ev v φ)) ∧
      ∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V (evFin F v) → g₀ ∈ UAt σ G₁.V (evFin F v) →
        ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v), l (ev v (locOp v (om (g, 1)) φ)) = l (ev v φ)

def InfInvB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ l : SInf F (Fin b × Fin (a + b)) →L[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V' (evI F), ∀ f, l (locOpInf (om₁' (g₀, 1)) f) = l f) →
      (∀ u ∈ unip σ G.V' H, u ∈ UAt σ G.V' (evI F) → ∀ f, l (ei' (locOpInf (om' (u, 1)) f)) = l (ei' f)) ∧
      (∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V' (evI F) → g₀ ∈ UAt σ G₁.V' (evI F) →
        ∀ f, l (ei' (locOpInf (om' (g, 1)) f)) = l (ei' f)) ∧
      ∀ g ∈ UAt σ G.V' (evI F), ∀ f : SInf F (Fin (b + 2) × Fin (a + (b + 2))),
        ∫ k, ∫ y, l (coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOpInf (om' (g, 1)) f)
          k.1 y.1) ∂μ ∂μK =
        ∫ k, ∫ y, l (coneInfInt B G.M' om' ei' (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) f k.1 y.1) ∂μ ∂μK

def InfInvA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F))), μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ l : SInf F (Fin b × Fin (b + a')) →L[ℂ] ℂ,
      (∀ g₀ ∈ UAt σ G₁.V (evI F), ∀ f, l (locOpInf (om₁ (g₀, 1)) f) = l f) →
      (∀ u ∈ unip σ G.V H, u ∈ UAt σ G.V (evI F) → ∀ f, l (ei (locOpInf (om (u, 1)) f)) = l (ei f)) ∧
      (∀ g₀ g, IsLevi H 1 g₀ g → g ∈ UAt σ G.V (evI F) → g₀ ∈ UAt σ G₁.V (evI F) →
        ∀ f, l (ei (locOpInf (om (g, 1)) f)) = l (ei f)) ∧
      ∀ g ∈ UAt σ G.V (evI F), ∀ f : SInf F (Fin (b + 2) × Fin (b + 2 + a')),
        ∫ k, ∫ y, l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) (locOpInf (om (g, 1)) f) k.1 y.1) ∂μ ∂μK =
        ∫ k, ∫ y, l (coneInfInt B G.M om ei (shiftA H H') X.ν ((b + 2 - a') / 2) f k.1 y.1) ∂μ ∂μK

def LemFZero : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ ei ev, IsLocPart M M₁ e ei ev → ∀ v : Pl F,
      (∀ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) → ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
        ev v (locOp v (om (1, u * h)) φ) = ev v (locOp v (om (1, h)) φ)) ∧
      (∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ W (evFin F v) → h₁ ∈ UAt σ W₁ (evFin F v) → ∀ h ∈ UAt σ W (evFin F v),
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (locOp v (om (1, m * h)) φ) =
          fac χX ((n : ℝ) / 2) t • locOp v (om₁ (1, h₁)) (ev v (locOp v (om (1, h)) φ))) ∧
      ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (p₁ : ((Fin n × Fin d₁ → Fv F v) → ℂ) →ₗ[ℂ] P₁),
        augAt om₁ v ≤ LinearMap.ker p₁ → ∀ g ∈ UAt σ X (evFin F v), ∀ h ∈ UAt σ W (evFin F v),
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
          p₁ (ev v (locOp v (om (1, h)) (locOp v (om (g, 1)) φ))) = p₁ (ev v (locOp v (om (1, h)) φ))

def LemFConeB : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, u * h)) φ) =
          coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, h)) φ)) ∧
      (∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, m * h)) φ) =
          fac X.β ((a : ℝ) / 2) t • locOp v (om₁' (1, h₁))
            (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, h)) φ))) ∧
      ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (p₁ : ((Fin b × Fin (a + b) → Fv F v) → ℂ) →ₗ[ℂ] P₁),
        augAt om₁' v ≤ LinearMap.ker p₁ → ∀ g ∈ UAt σ G.V' (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
          p₁ (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1)
            (locOp v (om' (1, h)) (locOp v (om' (g, 1)) φ))) =
          p₁ (coneFin B G.M' om' v (ev' v) K μK μ (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) (locOp v (om' (1, h)) φ))

def LemFConeA : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v))), μK.IsHaarMeasure →
      μ.IsHaarMeasure →
      (∀ u ∈ unip σ G.W H', u ∈ UAt σ G.W (evFin F v) → ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, u * h)) φ) =
          coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, h)) φ)) ∧
      (∀ t h₁ m, IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) → h₁ ∈ UAt σ G₁.W (evFin F v) →
        ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
        coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, m * h)) φ) =
          fac X.α ((a' : ℝ) / 2) t • locOp v (om₁ (1, h₁))
            (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, h)) φ))) ∧
      ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (p₁ : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] P₁),
        augAt om₁ v ≤ LinearMap.ker p₁ → ∀ g ∈ UAt σ G.V (evFin F v), ∀ h ∈ UAt σ G.W (evFin F v),
        ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
          p₁ (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2)
            (locOp v (om (1, h)) (locOp v (om (g, 1)) φ))) =
          p₁ (coneFin B G.M om v (ev v) K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (locOp v (om (1, h)) φ))

end GlobalTheory.ThK.LemF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroPrimitiveFrameDatumRenumber
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
open GlobalTheory.PureMatch GlobalTheory.SquareFlipReach ValuativeRel

noncomputable section
namespace GlobalTheory.ColumnRenumber

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]

def permGL (π : C ≃ C) : GL C k :=
  ⟨π.toPEquiv.toMatrix, π.symm.toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] [DecidableEq A'] in

theorem frameMatrixFirstColumnBlock_renumber (σ σ' : A ⊕ A' ≃ C) (h : GL C k) :
    X0 k σ' * (invT h).val = X0 k σ * (invT (permGL (σ.symm.trans σ') * h)).val := by
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply, frameMatrixFirstColumnBlock_mul_apply, invT_val, invT_val, _root_.mul_inv_rev]
  simp [permGL, Matrix.mul_apply, PEquiv.toMatrix_apply, Units.val_mul, Option.mem_def, Equiv.symm_apply_eq]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A] [DecidableEq A'] in

theorem frameMatrixSecondColumnBlock_renumber (σ σ' : A ⊕ A' ≃ C) (h : GL C k) :
    Y0 k σ * (permGL (σ.symm.trans σ') * h).val = Y0 k σ' * h.val := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply, frameMatrixSecondColumnBlock_mul_apply]
  simp [permGL, Matrix.mul_apply, PEquiv.toMatrix_apply, Units.val_mul]

variable [MeasurableSpace k] [BorelSpace k]

theorem fFun_renumber (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ)
    (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k) :
    fFun μ σ' ν Ψ X = ((ν (gdet (permGL (k := k) (σ.symm.trans σ'))) : ℂ) *
      apow (gdet (permGL (k := k) (σ.symm.trans σ'))) ((Fintype.card C : ℂ) / 2))⁻¹ * fFun μ σ ν Ψ X := by
  set Q : GL C k := permGL (σ.symm.trans σ') with hQ
  by_cases hX : ∃ h : GL C k, X = X0 k σ' * (invT h).val
  · obtain ⟨h, rfl⟩ := hX
    have hc : (ν (gdet Q) : ℂ) * apow (gdet Q) ((Fintype.card C : ℂ) / 2) ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
    rw [splitTheta_fFun_frameFirstBlock_mul μ σ', frameMatrixFirstColumnBlock_renumber σ σ' h, splitTheta_fFun_frameFirstBlock_mul μ σ, ← hQ, frameMatrixSecondColumnBlock_renumber, gdet_mul, map_mul, apow_mul,
      Units.val_mul]
    have ha := apow_ne_zero (gdet Q) ((Fintype.card C : ℂ) / 2)
    have hn : (ν (gdet Q) : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · have hX' : ¬ ∃ h : GL C k, X = X0 k σ * (invT h).val := fun H =>
      hX ((rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ' X).1 ((rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).2 H))
    rw [fFun, dif_neg hX, fFun, dif_neg hX', mul_zero]

end GlobalTheory.ColumnRenumber

open GlobalTheory.ColumnRenumber in

theorem GlobalTheory.ColumnRenumber.phiA_renumber : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (A A' C : Type) [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]
    (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ σ' : A ⊕ A' ≃ C) (ν : kˣ →* ℂˣ),
    ∃ u : ℂ, u ≠ 0 ∧ ∀ (ϖ : kˣ) (n : ℕ) (Λ : Submodule 𝒪[k] (C → k)) (Ψ : Matrix A' C k → ℂ) (X : Matrix A C k),
      phiA μ σ' ν ϖ n Λ Ψ X = u * phiA μ σ ν ϖ n Λ Ψ X := by
  intro k _ _ _ _ _ _ A A' C _ _ _ _ _ _ μ _ σ σ' ν
  refine ⟨((ν (gdet (permGL (k := k) (σ.symm.trans σ'))) : ℂ) *
      apow (gdet (permGL (k := k) (σ.symm.trans σ'))) ((Fintype.card C : ℂ) / 2))⁻¹,
    inv_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)), fun ϖ n Λ Ψ X => ?_⟩
  unfold phiA
  split_ifs
  · exact fFun_renumber μ σ σ' ν Ψ X
  · rw [mul_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentCornerIsUnitInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertTransv

theorem exists_unip_corner_isUnit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ u ∈ GlobalTheory.DblVac.KD σ X v, u ∈ GlobalTheory.DblVac.PDiag σ X ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD (g * u) * GlobalTheory.DblVac.antiCols n)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro F E _ _ _ _ _ σ B n r s X hB hX v w hvw g hg
  obtain ⟨Z, hZs, hZl, hZn, hdet, hinv⟩ := GlobalTheory.T.exists_inertPlace_transversal_of_localCore GlobalTheory.T.exists_isotropic_graph_unitary_isUnit_lowerBlock F E σ B n r s X hB hX v w hvw g hg
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hB.inert v w hvw).1
  obtain ⟨u, huK, huP, hu⟩ := GlobalTheory.T.halfSkewUnipotent_mem_doubledLatticeStabilizer F E σ n X v h2 Z hZs hZl hZn
  set N : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := GlobalTheory.DblVac.antiCols (F := F) (E := E) n with hN
  set Δ : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E) := diagCols (Fin n) with hΔ
  have hNN : Nᵀ * N = (2 : AF F) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [hN, GlobalTheory.DblVac.antiCols, Matrix.transpose_fromRows, Matrix.transpose_one, Matrix.transpose_neg,
      Matrix.transpose_one, Matrix.fromCols_mul_fromRows]
    simp [two_smul]
  have hmul : GlobalTheory.DblVac.matD (g * u) = GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD u := rfl
  have key : Nᵀ * GlobalTheory.DblVac.matD (g * u) * N = Nᵀ * GlobalTheory.DblVac.matD g * N + Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z := by
    rw [hmul, hu]
    have : Nᵀ * (GlobalTheory.DblVac.matD g * (1 + (⅟(2 : AF F)) • (Δ * Z * Nᵀ))) * N =
        Nᵀ * GlobalTheory.DblVac.matD g * N + (⅟(2 : AF F)) • (Nᵀ * GlobalTheory.DblVac.matD g * Δ * Z * (Nᵀ * N)) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [this, hNN, Matrix.mul_smul, smul_smul, invOf_mul_self, one_smul, Matrix.mul_one]
  refine ⟨u, huK, huP, ?_, ?_⟩
  · convert hdet using 2
    exact congrArg Matrix.det key
  · intro z hz; convert hinv z hz using 3
    exact key

end GlobalTheory.InertTransv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinUA

theorem hermA_neg_transpose {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA c (-Jᵀ) x y =
      -((fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (y b)) ⬝ᵥ
        ((J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E)) *ᵥ x)) := by
  unfold GlobalTheory.AdLat.hermA
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply,
    TensorProduct.tmul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hermA_mulVec {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (c : E ≃ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E))
    (h : (g.map (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c))ᵀ *
      (J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E)) * g =
      J.map fun t => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] t : GlobalTheory.AdLat.RA F E))
    (x y : Fin n → GlobalTheory.AdLat.RA F E) :
    GlobalTheory.AdLat.hermA c (-Jᵀ) (g *ᵥ x) (g *ᵥ y) = GlobalTheory.AdLat.hermA c (-Jᵀ) x y := by
  rw [hermA_neg_transpose, hermA_neg_transpose]
  congr 1
  have e : (fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c ((g *ᵥ y) b)) =
      (g.map (GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c)) *ᵥ
        (fun b => GlobalTheory.AdLat.sg (FiniteAdeleRing (𝓞 F) F) c (y b)) := by
    funext b
    simp [Matrix.mulVec, dotProduct, map_sum]
  rw [e]
  conv_rhs => rw [← h]
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (Matrix.transpose _),
    Matrix.vecMul_transpose]

theorem isUA_finHom : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (g : GA D V),
    GlobalTheory.UCls.IsUA (IsCMField.complexConj D.host.E) (-(V.gram)ᵀ)
      ((finHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)) := by
  intro D V g
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 (finHom V g).isUnit, fun x y => hermA_mulVec _ _ _ ?_ x y⟩
  have h : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1.1 * JR (AF D.host.F) V.gram * g.1.1
      = JR (AF D.host.F) V.gram := g.2
  let φ := (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hc : ∀ t, D.sp.cm.sig t = IsCMField.complexConj D.host.E t :=
    (GlobalTheory.Member.latHat_eq_hat_and_gram D V).2.2.2.2.2.1
  have hφ : ∀ z, φ (sigR (AF D.host.F) D.sp.cm.sig z) =
      GlobalTheory.AdLat.sg (Af D.host.F) (IsCMField.complexConj D.host.E) (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp [φ, sigR, GlobalTheory.AdLat.sg, hc]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hJ : (JR (AF D.host.F) V.gram).map φ =
      V.gram.map fun t => ((1 : Af D.host.F) ⊗ₜ[D.host.F] t : Af D.host.F ⊗[D.host.F] D.host.E) := by
    ext a b
    simp [φ, JR, inclR]
  have h2 := congrArg (fun M => Matrix.map M φ) h
  simp only [Matrix.map_mul] at h2
  rw [hJ] at h2
  have hg : (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1.1).map φ =
      ((g.1.1.map φ).map (GlobalTheory.AdLat.sg (Af D.host.F) (IsCMField.complexConj D.host.E)))ᵀ := by
    ext a b
    exact hφ _
  rw [hg] at h2
  exact h2

end GlobalTheory.FinUA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesCoprimeTwoQDStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridLocalTensorPlaces_coprime_two_q_d : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.SqTop.Rec large₂ → ∀ {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T), ∀ w ∈ locPl G t, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  first | exact @GlobalTheory.StdPairPlaces.natCast_two_q_d_notMem | exact GlobalTheory.StdPairPlaces.natCast_two_q_d_notMem | (intros; apply GlobalTheory.StdPairPlaces.natCast_two_q_d_notMem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HalfCosetIndicatorModIdealIsSchwartzBruhatHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfCosetIndicatorModIdeal_isSchwartzBruhatHalf : ∀ {D : D7} (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    Submodule.IsLattice D.host.E LS → Submodule.IsLattice D.host.E LT → ∀ (a : Formalism.L2.Theta.AE D), infPart D a = 0 →
    ∀ (I : Ideal (𝓞 D.host.E)), I ≠ ⊥ → ∀ x : WO S T, IsHalf a x → IsSBHalf a (latO S T LS LT fun _ => True) (cosetFn a I x) := by
  first | exact @GlobalTheory.BotSmallDict.cosetFn_isSBHalf | exact GlobalTheory.BotSmallDict.cosetFn_isSBHalf | (intros; apply GlobalTheory.BotSmallDict.cosetFn_isSBHalf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberRowsOfKernelDatumSizesStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberRows_of_kernelDatum_sizes : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) [IsTotallyComplex t.X.K] (W : Formalism.L2.Col.Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (hX : t.X.Ok) (Bs : DefBase t.X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 t.X.E t.Pr.vGs D.R.r → t.X.K)) (tup : Bs.Tup → D.what₂.Tup) (hP : ∀ τ, (mtildeGSD W t.Ch t.sel (t.tup (tup τ)) (rPsymF (R := D.R) t.Ch)).Ok) (b : ∀ τ, D.what₂.Word → (t.idx (tup τ)).β (t.m2 + 1)) (hY : ∀ τ x, YbHyp (R := D.R) t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) (t.word x) t.m2 (b τ x)) (hK : ∀ τ x, KerEquivC W t.Ch t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) t.amb (t.word x) t.m2 (b τ x) (hY τ x) (rPsymF (R := D.R) t.Ch)) (hF : ∀ τ x j, (chF W t.sel (t.tup (tup τ)) (t.idx (tup τ)) (t.word x) j).Ok) (hE : ∀ x, (evGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch) (t.word x)).Ok) (ev : ∀ τ, (Fin (Df.nV τ) → t.X.K) →ₗ[t.X.K] V0X W t.Ch t.sel (t.tup (tup τ)) Xg (rPsymF (R := D.R) t.Ch)) (u : D.what₂.Word) (eJ : Bs.J ≃ Fin D.R.m) (Nc lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) Nc lam0 c0 ce Ch Sw C1), tup Bs.μ0 = D.what₂.mu0 → KerTies t W Del h0 → KerSizes t W Del h0 CY CT → C0 ≤ Ch → (∀ v : InfinitePlace t.X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun t.X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) (fun τ => t.idx_ok (tup τ)) hP D.what₂.Word t.word b hY (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK) hF ev) u (memQ (A := (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK)) (hF := hF) hE (x := u)) (colsIn W t.Ch hX t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.idx (tup Bs.μ0)) (t.idx_ok (tup Bs.μ0)) (t.word u)) (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) ∧ ∀ v, IsUnit ((MramH W t.Ch hX (t.word u)).X v).det := by
  first | exact @GlobalTheory.ColRows.rowsBody_of_kerTies | exact GlobalTheory.ColRows.rowsBody_of_kerTies | (intros; apply GlobalTheory.ColRows.rowsBody_of_kerTies <;> assumption)
end

