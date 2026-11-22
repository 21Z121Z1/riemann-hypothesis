import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDirAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjEqNegOfSqEqNegNat
section
set_option autoImplicit false

namespace GlobalTheory.ConjugateNegativeSquare

open NumberField

theorem conj_eq_neg_of_sq_eq_neg_nat (z : ℂ) (d : ℕ) (h : z ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have him : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h0 : z.re = 0 := by
    by_contra hne
    have hi : z.im = 0 := by
      have h2 : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left hne
    rw [hi] at hre
    have hpos : 0 < z.re * z.re := mul_self_pos.2 hne
    linarith
  apply Complex.ext
  · simp [h0]
  · simp

theorem conjugate_rt {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (σ : E →+* ℂ) :
    (ComplexEmbedding.conjugate σ : E → ℂ) (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) =
      -(σ : E → ℂ) (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) := by
  obtain ⟨d, _, _, rt, hrt, _, _, _, _, _, _, _⟩ := H
  change ComplexEmbedding.conjugate σ (rt : E) = -σ (rt : E)
  rw [ComplexEmbedding.conjugate_coe_eq]
  apply conj_eq_neg_of_sq_eq_neg_nat _ d
  have h1 : (rt : E) ^ 2 = -(d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hrt
    simpa using this
  rw [← map_pow, h1, map_neg, map_natCast]

end GlobalTheory.ConjugateNegativeSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjToricPeriodCoordinateSumOverClassesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_toricPeriodCoordinate_sum_over_classes : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := by
  first | exact @GlobalTheory.ConjCoordToric.conj_coordIn_toric | exact GlobalTheory.ConjCoordToric.conj_coordIn_toric | (intros; apply GlobalTheory.ConjCoordToric.conj_coordIn_toric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAdelicThetaTransformSymplecticOfDecayStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_adelicThetaTransformSymplectic_of_decay : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsCharAF F ψ → ∀ Φ : (Fin N → AF F) → ℂ, Decay Φ → Continuous (thV ψ Φ) := by
  first | exact @GlobalTheory.ThetaTransform.continuous_thV | exact GlobalTheory.ThetaTransform.continuous_thV | (intros; apply GlobalTheory.ThetaTransform.continuous_thV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubF
section
open GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.MBLow.Cl

def cubF {B : NumB ℂ} {g : ℕ} (d : AB B g) (x y z : Fin g → ℂ) : ℂ :=
  (B.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) * d.fr (x + y) * d.fr (x + z) * d.fr (y + z) /
    (d.fr (x + y + z) * d.fr x * d.fr y * d.fr z)

end GlobalTheory.MBLow.Cl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCompactCharacterVanishing
section
open MeasureTheory Matrix

namespace GlobalTheory

theorem typeFunction_unip_add {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {a b : ℕ} (e : ι ≃ Fin a ⊕ Fin b) (u : (Fin a → Fin b → K) → GL ι K)
    (hu : ∀ X, (u X : Matrix ι ι K) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1))
    (X Y : Fin a → Fin b → K) : u (Y + X) = u X * u Y := by
  apply Units.ext
  rw [Units.val_mul, hu, hu, hu]
  simp only [Matrix.reindex_apply, Equiv.symm_symm]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.of_add_of]

theorem typeFunction_constantTerm_eq_zero :
  ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] (J : Subgroup (GL ι K)), IsOpen (J : Set (GL ι K)) → IsCompact (J : Set (GL ι K)) →
  ∀ χ : J →* ℂˣ, IsOpen (χ.ker : Set J) →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ h : GL ι K, ∃ X, ∃ hX : h⁻¹ * u X * h ∈ J, χ ⟨_, hX⟩ ≠ 1) →
  ∀ f : GL ι K → ℂ, (∀ g (hg : g ∈ J), f g = (((χ ⟨g, hg⟩)⁻¹ : ℂˣ) : ℂ)) → (∀ g, g ∉ J → f g = 0) →
  IsLocallyConstant f ∧ HasCompactSupport f ∧
  (∀ x ∈ (χ.ker.map J.subtype), ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (x * g * y) = f g) ∧
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) := by
  intro K _ _ _ _ _ _ ι _ _ J hJo hJc χ hχ hnt f hf1 hf0
  have hR : ∀ g j (hj : j ∈ J), f (g * j) = f g * (((χ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) := by
    intro g j hj
    by_cases hg : g ∈ J
    · rw [hf1 _ (J.mul_mem hg hj), hf1 g hg]
      have : (⟨g * j, J.mul_mem hg hj⟩ : J) = ⟨g, hg⟩ * ⟨j, hj⟩ := rfl
      rw [this, map_mul, mul_inv, Units.val_mul]
    · rw [hf0 g hg, hf0 _ (fun h => hg ((J.mul_mem_cancel_right hj).1 h)), zero_mul]
  have hL : ∀ g j (hj : j ∈ J), f (j * g) = (((χ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) * f g := by
    intro g j hj
    by_cases hg : g ∈ J
    · rw [hf1 _ (J.mul_mem hj hg), hf1 g hg]
      have : (⟨j * g, J.mul_mem hj hg⟩ : J) = ⟨j, hj⟩ * ⟨g, hg⟩ := rfl
      rw [this, map_mul, mul_inv, Units.val_mul]
    · rw [hf0 g hg, hf0 _ (fun h => hg ((J.mul_mem_cancel_left hj).1 h)), mul_zero]
  have hRk : ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (g * y) = f g := by
    rintro _ ⟨y, hy, rfl⟩ g
    have h1 : χ y = 1 := hy
    have := hR g y y.2
    simp only [Subtype.coe_eta, h1, inv_one, Units.val_one, mul_one] at this
    exact this
  have hLk : ∀ y ∈ (χ.ker.map J.subtype), ∀ g, f (y * g) = f g := by
    rintro _ ⟨y, hy, rfl⟩ g
    have h1 : χ y = 1 := hy
    have := hL g y y.2
    simp only [Subtype.coe_eta, h1, inv_one, Units.val_one, one_mul] at this
    exact this
  have hNo : IsOpen ((χ.ker.map J.subtype : Subgroup (GL ι K)) : Set (GL ι K)) := by
    rw [Subgroup.coe_map]
    exact hJo.isOpenMap_subtype_val _ hχ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' ((χ.ker.map J.subtype : Subgroup (GL ι K)) : Set (GL ι K)),
      hNo.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
      exact Subgroup.one_mem _
    · intro x hx
      have := hRk _ hx g
      rwa [mul_inv_cancel_left] at this
  · exact HasCompactSupport.intro' hJc (J.isClosed_of_isOpen hJo) (fun g hg => hf0 g hg)
  · intro x hx y hy g
    rw [hRk y hy, hLk x hx]
  · intro a b e ha hb μ hμ u hu g h
    obtain ⟨Y, hY, hne⟩ := hnt a b e ha hb u hu h
    have key : ∀ X, f (g * (h⁻¹ * u (Y + X) * h)) =
        f (g * (h⁻¹ * u X * h)) * (((χ ⟨_, hY⟩)⁻¹ : ℂˣ) : ℂ) := by
      intro X
      rw [← hR _ _ hY, typeFunction_unip_add e u hu]
      congr 1
      group
    have h1 := integral_add_left_eq_self (μ := μ) (fun X => f (g * (h⁻¹ * u X * h))) Y
    simp only [key] at h1
    rw [integral_mul_const] at h1
    have hc : (((χ ⟨_, hY⟩)⁻¹ : ℂˣ) : ℂ) ≠ 1 := by
      intro hc
      exact hne (inv_eq_one.1 (Units.val_eq_one.1 hc))
    by_contra hI
    exact hc (mul_left_cancel₀ hI (h1.trans (mul_one _).symm))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSNeZero
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH

namespace GlobalTheory.CharPair

variable (P Q R S : ℕ)

abbrev Mdl : Type := MvPolynomial (Fin P × Fin Q) ℂ

def mR (a : Fin P) (b : Fin Q) : Pol P Q R 0 :=
  ∑ c : Fin R, X (Sum.inl a, Sum.inl c) * X (Sum.inr b, Sum.inl c)

def mS (a : Fin P) (b : Fin Q) : Pol P Q 0 S :=
  ∑ c : Fin S, X (Sum.inl a, Sum.inr c) * X (Sum.inr b, Sum.inr c)

def detR (h : P ≤ R) : Pol P Q R 0 :=
  (Matrix.of fun a c : Fin P => (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)).det

def detS (h : Q ≤ S) : Pol P Q 0 S :=
  (Matrix.of fun b c : Fin Q => (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)).det

def embR (h : P ≤ R) (k : ℕ) : Mdl P Q →ₗ[ℂ] Pol P Q R 0 :=
  LinearMap.mulRight ℂ (detR P Q R h ^ k) ∘ₗ (aeval fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2).toLinearMap

def embS (h : Q ≤ S) (k' : ℕ) : Mdl P Q →ₗ[ℂ] Pol P Q 0 S :=
  LinearMap.mulRight ℂ (detS P Q S h ^ k') ∘ₗ (aeval fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2).toLinearMap

variable {P Q}

abbrev mulM (a : Fin P) (b : Fin Q) : Module.End ℂ (Mdl P Q) := LinearMap.mulLeft ℂ (X (a, b))

abbrev derM (a : Fin P) (b : Fin Q) : Module.End ℂ (Mdl P Q) := (pderiv (a, b)).toLinearMap

variable (P Q)

def opR (k : ℕ) : Ix P Q → Ix P Q → Module.End ℂ (Mdl P Q)
  | .inl a, .inr b => mulM a b
  | .inr b, .inl a => -(∑ a', ∑ b', mulM a' b' * derM a' b * derM a b' + ((R + k : ℕ) : ℂ) • derM a b)
  | .inl a, .inl a' => ∑ b, mulM a b * derM a' b + (if a = a' then (k : ℂ) + (R : ℂ) / 2 else 0) • 1
  | .inr b, .inr b' => -(∑ a, mulM a b' * derM a b) - (if b = b' then (R : ℂ) / 2 else 0) • 1

def opS (k' : ℕ) : Ix P Q → Ix P Q → Module.End ℂ (Mdl P Q)
  | .inl a, .inr b => -mulM a b
  | .inr b, .inl a => ∑ a', ∑ b', mulM a' b' * derM a' b * derM a b' + ((S + k' : ℕ) : ℂ) • derM a b
  | .inl a, .inl a' => -(∑ b, mulM a b * derM a' b) - (if a = a' then (S : ℂ) / 2 else 0) • 1
  | .inr b, .inr b' => ∑ a, mulM a b' * derM a b + (if b = b' then (k' : ℂ) + (S : ℂ) / 2 else 0) • 1

def actR (k : ℕ) : Mat P Q →ₗ[ℂ] Module.End ℂ (Mdl P Q) :=
  ∑ i, ∑ j, (Matrix.entryLinearMap ℂ ℂ i j).smulRight (opR P Q R k i j)

def actS (k' : ℕ) : Mat P Q →ₗ[ℂ] Module.End ℂ (Mdl P Q) :=
  ∑ i, ∑ j, (Matrix.entryLinearMap ℂ ℂ i j).smulRight (opS P Q S k' i j)

theorem actR_apply (k : ℕ) (Z : Mat P Q) : actR P Q R k Z = ∑ i, ∑ j, Z i j • opR P Q R k i j := by
  simp [actR, LinearMap.sum_apply]

theorem actS_apply (k' : ℕ) (Z : Mat P Q) : actS P Q S k' Z = ∑ i, ∑ j, Z i j • opS P Q S k' i j := by
  simp [actS, LinearMap.sum_apply]

theorem detR_ne_zero (P Q R : ℕ) (h : P ≤ R) : detR P Q R h ≠ 0 := by
  let g : Fin P × Fin P → Ix P Q × Ix R 0 := fun ac => (Sum.inl ac.1, Sum.inl (Fin.castLE h ac.2))
  have hf : Function.Injective g := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ hac
    simp only [g, Prod.mk.injEq, Sum.inl.injEq] at hac
    exact Prod.ext hac.1 (Fin.castLE_injective h hac.2)
  have : detR P Q R h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin P) (Fin P) ℂ)) := by
    rw [detR, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext a c; simp [g, Matrix.mvPolynomialX]
  rw [this]; intro h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ ((map_eq_zero_iff _ (rename_injective _ hf)).1 h0)

theorem detS_ne_zero (P Q S : ℕ) (h : Q ≤ S) : detS P Q S h ≠ 0 := by
  let g : Fin Q × Fin Q → Ix P Q × Ix 0 S := fun bc => (Sum.inr bc.1, Sum.inr (Fin.castLE h bc.2))
  have hf : Function.Injective g := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ hbc
    simp only [g, Prod.mk.injEq, Sum.inr.injEq] at hbc
    exact Prod.ext hbc.1 (Fin.castLE_injective h hbc.2)
  have : detS P Q S h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin Q) (Fin Q) ℂ)) := by
    rw [detS, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext b c; simp [g, Matrix.mvPolynomialX]
  rw [this]; intro h0
  exact Matrix.det_mvPolynomialX_ne_zero _ _ ((map_eq_zero_iff _ (rename_injective _ hf)).1 h0)

end GlobalTheory.CharPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPolynomialCoefficientsEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_polynomial_coefficients_eq : ∀ (q r : ℕ) (f : ℂ[X]) (a w : ℕ → ℂ), q ≠ 0 → f.coeff 0 = 1 → f.natDegree ≤ r → (∀ k, a k = (f.map (starRingEnd ℂ)).coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2))) → (∀ k, w k = (dualPoly ((q : ℂ) ^ (r - 1)) f).coeff k / ((-1) ^ k * (q : ℂ) ^ (k * (k - 1) / 2))) → ((a r ≠ 0 ∧ ∀ k ≤ r, star (a k) * a r = a (r - k)) ∨ (w r ≠ 0 ∧ ∀ k ≤ r, star (w k) * w r = w (r - k))) → ∀ k ≤ r, a k = w k := by
  first | exact @GlobalTheory.PolUnitary.conj_eq_dual | exact GlobalTheory.PolUnitary.conj_eq_dual | (intros; apply GlobalTheory.PolUnitary.conj_eq_dual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingReducedResidueFieldBijectiveUnramified
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PrimePart

open Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDirAlg

theorem exists_inv_of_not_dvd_discr (E : Type) [Field E] [NumberField E] {V : Type} [CommRing V] [IsDomain V]
    [IsLocalRing V] {Fr : Type} [Field Fr] [Algebra V Fr]
    [DecidableEq (E →+* ℂ)] (hinj : Function.Injective (algebraMap V Fr)) {F : Type} [Field F] (j : F →+* ℂ)
    (io : F →+* Fr)
    (φ : (E →+* ℂ) → (E →+* F)) (hφ : ∀ σ x, j (φ σ x) = σ x)
    (χ : (E →+* ℂ) → (𝓞 E →+* V)) (hχ : ∀ σ (a : 𝓞 E), algebraMap V Fr (χ σ a) = io (φ σ (a : E)))
    (g : ℕ) (hg : g.Prime) (hgV : ¬ IsUnit (g : V)) (hd : ¬ (g : ℤ) ∣ discr E) :
    ∃ Cm : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → V,
      (∀ σ τ, ∑ i, χ σ (RingOfIntegers.basis E i) * Cm i τ = if σ = τ then 1 else 0) ∧
      (∀ i i', ∑ τ, Cm i τ * χ τ (RingOfIntegers.basis E i') = if i = i' then 1 else 0) := by
  classical
  let bs := RingOfIntegers.basis E
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let e' : Module.Free.ChooseBasisIndex ℤ (𝓞 E) ≃ (E →+* ℂ) := e.trans (RingHom.equivRatAlgHom E ℂ).symm
  let A : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) V :=
    fun i k => χ (e' k) (bs i)
  have hAij : ∀ i k, A i k = χ (e' k) (bs i) := fun _ _ => rfl
  let AF : Matrix (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) F :=
    fun i k => φ (e' k) (bs i : E)
  have hAF : AF.map j = Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => (bs i : E)) e := by
    ext i k
    simp only [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, Equiv.refl_symm, Equiv.refl_apply,
      Equiv.symm_symm]
    show j (φ (e' k) (bs i : E)) = (e k) (bs i : E)
    rw [hφ]
    rfl
  have hdF : AF.det ^ 2 = ((discr E : ℤ) : F) := by
    apply j.injective
    rw [map_pow, RingHom.map_det, RingHom.mapMatrix_apply, hAF,
      ← Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two, map_intCast]
    have hb : (fun i => (bs i : E)) = ⇑(integralBasis E) := funext fun i => (integralBasis_apply E i).symm
    rw [hb, ← coe_discr, map_intCast]
  have hdV : A.det ^ 2 = ((discr E : ℤ) : V) := by
    apply hinj
    rw [map_pow, RingHom.map_det, map_intCast]
    have hA : (algebraMap V Fr).mapMatrix A = io.mapMatrix AF := by
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hAij, AF, hχ]
      rfl
    rw [hA, ← RingHom.map_det, ← map_pow, hdF, map_intCast]
  have hu : IsUnit A.det := by
    have h := isUnit_of_not_dvd g hg hgV _ hd
    rw [← hdV] at h
    exact (isUnit_pow_iff two_ne_zero).1 h
  refine ⟨fun i τ => A⁻¹ (e'.symm τ) i, ?_, ?_⟩
  · intro σ τ
    have h1 := congrFun (congrFun (Matrix.nonsing_inv_mul A hu) (e'.symm τ)) (e'.symm σ)
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simp only [hAij, Equiv.apply_symm_apply] at h1
    rw [show (∑ i, χ σ (bs i) * A⁻¹ (e'.symm τ) i) = ∑ i, A⁻¹ (e'.symm τ) i * χ σ (bs i) from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
    by_cases h : σ = τ
    · subst h; simp
    · rw [if_neg (fun h' => h (e'.symm.injective h').symm), if_neg h]
  · intro i i'
    have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hu) i') i
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    simp only [hAij] at h1
    rw [← Equiv.sum_comp e' (fun τ => A⁻¹ (e'.symm τ) i * χ τ (bs i'))]
    simp only [Equiv.symm_apply_apply]
    rw [show (∑ k, A⁻¹ k i * χ (e' k) (bs i')) = ∑ k, χ (e' k) (bs i') * A⁻¹ k i from
      Finset.sum_congr rfl fun _ _ => mul_comm _ _, h1]
    by_cases h : i = i'
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]

theorem red_bijective (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H)
    (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p)
    (hp : UnramIn E p) : Function.Bijective (red io X) := by
  classical
  haveI : IsDomain X.O := X.ints.hom_inj.isDomain _
  obtain ⟨Cm, hAC, hCA⟩ := exists_inv_of_not_dvd_discr E (V := X.O) (Fr := X.C) X.ints.hom_inj
    (c.F.val : c.F →+* ℂ) (X.ιF.comp io) (embF c) (fun σ x => by simp [embF])
    (embO io X) (fun σ a => algebraMap_embO io X σ a) p Fact.out X.nonunit.out hp
  set b := RingOfIntegers.basis E
  let Cr : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → (E →+* ℂ) → ResidueField X.O := fun i τ => residue X.O (Cm i τ)
  have hAC' : ∀ σ τ, ∑ i, red io X σ (b i) * Cr i τ = if σ = τ then 1 else 0 := by
    intro σ τ
    have := congrArg (residue X.O) (hAC σ τ)
    simpa [map_sum, red, Cr, apply_ite (residue X.O)] using this
  have hCA' : ∀ i i', ∑ τ, Cr i τ * red io X τ (b i') = if i = i' then 1 else 0 := by
    intro i i'
    have := congrArg (residue X.O) (hCA i i')
    simpa [map_sum, red, Cr, apply_ite (residue X.O)] using this
  refine ⟨fun σ τ hst => ?_, fun χ => ?_⟩
  · by_contra hne
    have h1 := hAC' σ τ
    rw [if_neg hne, hst, hAC' τ τ, if_pos rfl] at h1
    exact one_ne_zero h1
  · let ρ : 𝓞 E →+* Module.End (ResidueField X.O) (ResidueField X.O) :=
      (Algebra.lmul (ResidueField X.O) (ResidueField X.O)).toRingHom.comp χ
    obtain ⟨mσ, hm, hs⟩ := ((decomp_of_inv ρ (red io X) b Cr hAC' hCA').1 1)
    obtain ⟨σ, hσ⟩ : ∃ σ, mσ σ ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      simp [h] at hs
    refine ⟨σ, RingHom.ext fun a => ?_⟩
    have : χ a * mσ σ = red io X σ a * mσ σ := hm σ a
    exact (mul_right_cancel₀ hσ this).symm

end GlobalTheory.PrimePart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsAfterBaseChangeSpecTopOpenOfStableBasisStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeds_after_baseChange_specTopOpen_of_stable_basis : ∀ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k : ℕ) {mB : ℕ} (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))), IsAbelianScheme B → M.IsLB → VeryAmpleAt B M k → IsBCBasis B M k bB → ∃ (x : Sp Rg ⟶ (topS Rg).left) (b' : Fin mB → LB.Sec (LPow B M (k : ℤ) (baseAt x))), IsIso x ∧ (∀ i, IsPullSec B M (k : ℤ) (homAt x ▷ B) (whiskerRight_snd (homAt x) B) (bB i) (b' i)) ∧ GlobalTheory.AmpleSpan.EmbedsBy (fst (baseAt x) B).left b' := by
  first | (exact @GlobalTheory.HomFixMat.EmbedsBC.embeds_bc) | (exact GlobalTheory.HomFixMat.EmbedsBC.embeds_bc) | (intros; apply GlobalTheory.HomFixMat.EmbedsBC.embeds_bc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProportionalGermsSectionsEmbedProjectivelyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_proportional_germs_sectionsEmbedProjectively : ∀ {X Y Z : Scheme.{0}} (π : Y ⟶ Z) {N : LB Y} {κ : Type} (s : κ → LB.Sec N), GlobalTheory.AmpleSpan.EmbedsBy π s → ∀ (f₁ f₂ : X ⟶ Y), f₁ ≫ π = f₂ ≫ π → (∀ x : X, ∃ σ : κ → X.presheaf.stalk x, (∃ p, f₁ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₁ x (N.U p) ((s l).f p) = u * σ l) ∧ (∃ p, f₂ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₂ x (N.U p) ((s l).f p) = u * σ l)) → f₁ = f₂ := by
  first | (exact @GlobalTheory.HomFixGerm.eq_of_germs) | (exact GlobalTheory.HomFixGerm.eq_of_germs) | (intros; apply GlobalTheory.HomFixGerm.eq_of_germs  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOnDoubleCosetOfEqOnArchimedeanSlice
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirPatch

theorem eq_on_cell_of_eq_on_slice : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (V : Subgroup (GL (Fin (m + 1)) (Af E))) (q : GA E (m + 1)), q ∈ GlobalTheory.JSW.mirS E S m → GeneralLinearGroup.map (pInf E) q = 1 → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ V, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ u ∈ V, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∀ p ∈ GlobalTheory.JSW.mirS E S m, p ∈ GlobalTheory.JSW.MirPatch.cell V q → W p = b p := by
  intro E _ _ _ m S b W V q hq hqi hb hW hbV hWV hsl p hp hpc
  obtain ⟨u, hu, k, hk, y, rfl⟩ := hpc
  have key : u * q * finGL E (m + 1) k * infGL E (m + 1) y = u * ((q * infGL E (m + 1) y) * finGL E (m + 1) k) := by
    rw [mul_assoc (q) (infGL E (m + 1) y), infGL_comm, ← mul_assoc, ← mul_assoc]

  have hy : ∀ j, (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    have h1 := congrArg (pInf E) (hp.2 j)
    have hmap : GeneralLinearGroup.map (pInf E) (u * q * finGL E (m + 1) k * infGL E (m + 1) y)
        = GeneralLinearGroup.map (pInf E) u * y := by
      simp [map_mul, hqi]
    have h2 : (GeneralLinearGroup.map (pInf E) (u * q * finGL E (m + 1) k * infGL E (m + 1) y) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j
        = if j = Fin.last m then 1 else 0 := by
      rw [GeneralLinearGroup.map_apply] at *
      simpa [apply_ite (pInf E)] using h1
    rw [hmap] at h2
    rw [← h2]
    simp only [Units.val_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single (Fin.last m)]
    · have : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) (Fin.last m) = 1 := hu.2 _
      simp [GeneralLinearGroup.map_apply, this]
    · intro l _ hl
      have hlt : l < Fin.last m := lt_of_le_of_ne (Fin.le_last l) hl
      have : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l = 0 := hu.1 _ _ hlt
      simp [GeneralLinearGroup.map_apply, this]
    · simp
  have hslice : q * infGL E (m + 1) y ∈ GlobalTheory.JSW.mirS E S m := by
    refine ⟨?_, ?_⟩
    · intro w hw
      rw [map_mul, hq.1 w hw, one_mul]
      exact map_cornerGL_of_zero _ _ (fun _ => map_zero (pLoc E w)) y
    · intro j
      refine ad_ext ?_ ?_
      · have := congrArg (fun g : GL (Fin (m + 1)) (Cinf E) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j)
          (show GeneralLinearGroup.map (pInf E) (q * infGL E (m + 1) y) = y by simp [hqi])
        simp only [GeneralLinearGroup.map_apply] at this
        rw [this, hy j]; split_ifs <;> simp
      · have := congrArg (fun g : GL (Fin (m + 1)) (Af E) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j)
          (show GeneralLinearGroup.map (pFin E) (q * infGL E (m + 1) y) = GeneralLinearGroup.map (pFin E) q by simp)
        simp only [GeneralLinearGroup.map_apply] at this
        rw [this, hq.2 j]
  rw [key, hW u hu, hb u hu, hWV k hk, hbV k hk, hsl y hslice]

end GlobalTheory.JSW.MirPatch
end

