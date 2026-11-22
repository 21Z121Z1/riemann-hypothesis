import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.ZeroSetFinite
import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauIIsBasisOf

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDegPolyEvalX
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.TheoremB

open MvPolynomial Finset

theorem polarPoly_eval {σ R : Type*} [CommRing R] [Fintype σ]
    (Φ : MvPolynomial σ R →ₗ[R] R) (n : ℕ) (u : σ → R) :
    eval u (polarPoly Φ n) = Φ ((-∑ v : σ, C (u v) * X v) ^ n) := by
  set P : MvPolynomial σ (MvPolynomial σ R) := (-outerDot σ R) ^ n with hP
  let ψ : MvPolynomial σ (MvPolynomial σ R) →+* MvPolynomial σ R :=
    eval₂Hom (RingHom.id _) (fun v => C (u v))
  have hψ : ψ P = (-∑ v : σ, C (u v) * X v) ^ n := by
    simp [P, ψ, outerDot, map_pow, map_neg, map_sum]
  have hψ' : ψ P = ∑ m ∈ P.support, C (∏ i, u i ^ m i) * coeff m P := by
    change eval₂ (RingHom.id _) (fun v => C (u v)) P = _
    rw [eval₂_eq']
    refine sum_congr rfl fun m _ => ?_
    simp [map_prod, map_pow, mul_comm]
  rw [← hψ, hψ', map_sum]
  unfold polarPoly
  rw [map_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), C_mul', map_smul,
    smul_eq_mul, mul_comm]

theorem DegPolyEval.proof : DegPolyEval.Statement := by
  intro d u
  exact polarPoly_eval (intFl d) d.D u

end GroundTheory.Heights₂.Heights.TheoremB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFramePlaneGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

theorem FramePlaneGraph.zeroSetEuc_sup_span {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ))
    (q : MvPolynomial (Fin n) ℂ) :
    zeroSetEuc (J ⊔ Ideal.span {q}) = zeroSetEuc J ∩ {z | eval (fun i => z i) q = 0} := by
  ext z
  simp only [zeroSetEuc, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun p hp => h p (Ideal.mem_sup_left hp),
      h q (Ideal.mem_sup_right (Ideal.mem_span_singleton_self q))⟩
  · rintro ⟨h1, h2⟩ p hp
    have hle : J ⊔ Ideal.span {q} ≤ RingHom.ker (eval fun i => z i) :=
      sup_le (fun p hp => RingHom.mem_ker.mpr (h1 p hp))
        ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr h2))
    exact RingHom.mem_ker.mp (hle hp)

theorem FramePlaneGraph.lt_of_add_one_le_nat {x : WithBot ℕ∞} {d : ℕ} (h : x + 1 ≤ (d : WithBot ℕ∞)) :
    x < d := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe y =>
    have h' : y + 1 ≤ (d : ℕ∞) := by exact_mod_cast h
    have hy : y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) (le_trans le_self_add h')
    have : y < d := (ENat.add_one_le_iff hy).mp h'
    exact_mod_cast this

theorem FramePlaneGraph.dim_sup_span_lt {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) {q : MvPolynomial (Fin n) ℂ} (hq : q ∉ J) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {q})) < d := by
  have hr : Ideal.Quotient.mk J q ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hle : J ≤ J ⊔ Ideal.span {q} := le_sup_left
  have h1 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
    (Ideal.Quotient.factor_surjective hle) hr (by
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self q))
  exact FramePlaneGraph.lt_of_add_one_le_nat (hd ▸ h1)

theorem FramePlaneGraph.proof (hG : FrameGraphGeneric.Statement) : FramePlaneGraph.Statement := by
  intro n d J hJ hd b
  obtain ⟨I₀, q, hcard, hq, hloc⟩ := hG n d J hJ hd b
  refine ⟨I₀, J ⊔ Ideal.span {q}, hcard, FramePlaneGraph.dim_sup_span_lt hJ hd hq, ?_⟩
  set W : Set (EuclideanSpace ℂ (Fin n)) := {z | eval (fun i => z i) q ≠ 0} with hWdef
  have hS : zeroSetEuc J \ zeroSetEuc (J ⊔ Ideal.span {q}) = zeroSetEuc J ∩ W := by
    rw [FramePlaneGraph.zeroSetEuc_sup_span]
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq, hWdef]
    tauto
  have hW : IsOpen W := isOpen_ne_fun ((MvPolynomial.continuous_eval q).comp
    (by fun_prop : Continuous fun z : EuclideanSpace ℂ (Fin n) => fun i => z i)) continuous_const
  rw [hS]
  intro z hz
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hπ, hgraph⟩ := hloc z hz.1 hz.2
  refine ⟨Ω ∩ g ⁻¹' W, V ∩ W, g, hg.continuousOn.isOpen_inter_preimage hΩ hW, hV.inter hW,
    ⟨hzV, hz.2⟩, hg.mono Set.inter_subset_left, fun w hw => hπ w hw.1, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxJ, hxW⟩, hxV, -⟩
    have hx : x ∈ g '' Ω := hgraph ▸ ⟨hxJ, hxV⟩
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w, ⟨hw, hxW⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwW⟩, rfl⟩
    have hx : g w ∈ zeroSetEuc J ∩ V := hgraph.symm ▸ ⟨w, hw, rfl⟩
    exact ⟨⟨hx.1, hwW⟩, hx.2, hwW⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMassBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

theorem frameFibreCount_mono {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) {S T : Set (EuclideanSpace ℂ (Fin n))} (h : S ⊆ T) (x : I → ℂ) :
    frameFibreCount b I S x ≤ frameFibreCount b I T x := by
  unfold frameFibreCount
  exact ENat.toENNReal_mono (Set.encard_le_encard fun z hz => ⟨h hz.1, hz.2⟩)

theorem MassBound.proof (hG : FramePlaneGraph.Statement) (hL : LocalGraphMass.Statement)
    (hN : NullSmaller.Statement) : MassBound.Statement := by
  intro n d J hJ hd b R
  obtain ⟨I₀, J', hcard, hJ', hloc⟩ := hG n d J hJ hd b
  have h0 : μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J') = 0 := hN n d J' hJ'
  have h1 := hL n d b I₀ (zeroSetEuc J \ zeroSetEuc J') hcard hloc R
  calc μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball 0 R)
      ≤ μH[((2 * d : ℕ) : ℝ)] ((zeroSetEuc J \ zeroSetEuc J') ∩ Metric.ball 0 R ∪ zeroSetEuc J') := by
        refine measure_mono fun z hz => ?_
        by_cases h : z ∈ zeroSetEuc J'
        · exact Or.inr h
        · exact Or.inl ⟨⟨hz.1, h⟩, hz.2⟩
    _ ≤ μH[((2 * d : ℕ) : ℝ)] ((zeroSetEuc J \ zeroSetEuc J') ∩ Metric.ball 0 R) +
          μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J') := measure_union_le _ _
    _ = μH[((2 * d : ℕ) : ℝ)] ((zeroSetEuc J \ zeroSetEuc J') ∩ Metric.ball 0 R) := by
        rw [h0, add_zero]
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d,
          (⨆ x : I → ℂ, frameFibreCount b I (zeroSetEuc J \ zeroSetEuc J') x) *
            μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R) := h1
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d,
          (⨆ x : I → ℂ, frameFibreCount b I (zeroSetEuc J) x) *
            μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R) :=
        Finset.sum_le_sum fun I _ => mul_le_mul'
          (iSup_mono fun x => frameFibreCount_mono b I Set.sdiff_subset x) le_rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameImplicitGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def FrameImplicitGraph.Statement : Prop :=
  ∀ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (f : {j // j ∉ I} → MvPolynomial (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n)),
    (∀ k, eval (fun i => z i) (f k) = 0) → eval (fun i => z i) (frameJacobianDet b I f) ≠ 0 →
    ∀ U : Set (EuclideanSpace ℂ (Fin n)), IsOpen U → z ∈ U →
      ∃ (Ω : Set (I → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n))) (g : (I → ℂ) → EuclideanSpace ℂ (Fin n)),
        IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ DifferentiableOn ℂ g Ω ∧
          (∀ w ∈ Ω, frameProj b I (g w) = w) ∧
          {x : EuclideanSpace ℂ (Fin n) | ∀ k, eval (fun i => x i) (f k) = 0} ∩ V = g '' Ω

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StJacobianRankGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial

def genericGradient {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    Fin n → FractionRing (MvPolynomial (Fin n) ℂ ⧸ J) :=
  fun l => algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
    (Ideal.Quotient.mk J (pderiv l f))

def JacobianRankGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime],
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
      Module.finrank (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J))
        (Submodule.span (FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)) (genericGradient J '' (J : Set _))) ≤ n - d

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.TorsionAverage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

namespace RigSymForm

variable {K : Type} [Field K] [Algebra K ℂ] (P : RigSymForm K)

def latVec (u v : Fin P.g → ℤ) : Fin P.g → ℂ := intVec v + P.pt.τ *ᵥ intVec u

def autL (N : ℕ) (u v : Fin P.g → ℤ) (w : Fin P.g → ℂ) : ℂ :=
  perFactor P.ch N v * autFactor P.pt P.ch N u w

def torsIdx {g m : ℕ} (u : Fin g → Fin m) : Fin g → ℤ := fun i => ((u i : ℕ) : ℤ)

def torsAvg (N m : ℕ) (F : P.Fn) : P.Fn := fun z =>
  ((m : ℂ) ^ (2 * P.g))⁻¹ * ∑ u : Fin P.g → Fin m, ∑ v : Fin P.g → Fin m,
    (P.autL N (torsIdx u) (torsIdx v) ((m : ℂ) • z))⁻¹ *
      F (z + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v))

end RigSymForm

open RigSymForm

def PullbackMulMem.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (m N : ℕ) (f : P.Fn), f ∈ P.S N → (fun z => f ((m : ℂ) • z)) ∈ P.S (N * m ^ 2)

def TorsAvgDescends.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (m : ℕ), 1 ≤ m → ∀ (N : ℕ) (F : P.Fn), F ∈ P.S (N * m ^ 2) →
    ∃ f ∈ P.S N, ∀ z, P.torsAvg N m F z = f ((m : ℂ) • z)

end

end GroundTheory.Heights₂.Heights.KeyFormula
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.VanishingCechMultInvariants
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

def VanishingCechMultInvariants.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a : ℕ), 3 ≤ a → ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ m : ℕ, 1 ≤ m → ∀ n q : ℕ,
      (∀ φ : Finset (Fin (r + 1)) → P.Fn,
        P.IsCocycle (a * m ^ 2) (n * m ^ 2) (q + 1) (fun j z => x j ((m : ℂ) • z)) φ →
        P.IsCoboundary (a * m ^ 2) (n * m ^ 2) q (fun j z => x j ((m : ℂ) • z)) φ) →
      ∀ φ : Finset (Fin (r + 1)) → P.Fn, P.IsCocycle a n (q + 1) x φ → P.IsCoboundary a n q x φ

end

end GroundTheory.Heights₂.Heights.KeyFormula
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.VanishingCechResidue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

def VanishingCechResidue.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a : ℕ), 3 ≤ a → ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ b : ℕ, b < a → ∃ c₀ : ℕ, ∀ c, c₀ ≤ c → ∀ (q : ℕ) (φ : Finset (Fin (r + 1)) → P.Fn),
      P.IsCocycle a (b + a * c) (q + 1) x φ → P.IsCoboundary a (b + a * c) q x φ

end

end GroundTheory.Heights₂.Heights.KeyFormula
end

