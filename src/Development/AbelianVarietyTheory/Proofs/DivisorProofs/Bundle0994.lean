import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0131
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSectionSpecialFibre
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIdPowEqOneOfIsFiniteOfFlat
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatSecUnitGenericFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
import GroundTheory.Brauer.SkolemNoether
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0975
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentation
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelRep

set_option maxHeartbeats 1000000 in

theorem exists_cusp_rep : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → (∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) → ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i), ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) := by
  intro D G _ T κ i lev _ hL hW
  have hnat := fun f (hf : f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) => ((mem_cusp _ _ _ _ _ _).1 hf).1.1
  exact ⟨{ toFun := fun g => (actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev g).restrict (hW g)
           map_one' := LinearMap.ext fun F => Subtype.ext
             (actL_one _ _ _ hL.total hL.func hL.one (hnat _ F.2))
           map_mul' := fun g g' => LinearMap.ext fun F => Subtype.ext
             (actL_mul _ _ _ hL.total hL.func hL.mul g g' (hnat _ F.2)) },
    fun _ _ => rfl⟩

end GlobalTheory.LevelRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalIsometry
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalIsometryEqualRank

theorem exists_of_frames {A : Type} [CommRing A] (σ : A →+* A) {m n : ℕ} (hr : m = n)
    (J : Matrix (Fin n) (Fin n) A) (J' : Matrix (Fin m) (Fin m) A) (h : GL (Fin n) A) (h' : GL (Fin m) A)
    (h2 : (h.1.map σ)ᵀ * J * h.1 = 1) (h2' : (h'.1.map σ)ᵀ * J' * h'.1 = 1) (S : Subring A) :
    ∃ (φ : Matrix (Fin m) (Fin n) A) (ψ : Matrix (Fin n) (Fin m) A), φ * ψ = 1 ∧ ψ * φ = 1 ∧
      ((φ.map σ)ᵀ * J' : Matrix (Fin n) (Fin m) A) * φ = J ∧
      ∀ x, (∀ i, (h⁻¹).1.mulVec x i ∈ S) ↔ (∀ i, (h'⁻¹).1.mulVec (φ.mulVec x) i ∈ S) := by
  subst hr
  refine ⟨(h' * h⁻¹).1, (h * h'⁻¹).1, ?_, ?_, ?_, fun x => ?_⟩
  · rw [← Units.val_mul]; simp
  · rw [← Units.val_mul]; simp
  · have e : ((h⁻¹).1.map σ)ᵀ * (h.1.map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
    have e2 : h.1 * (h⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    calc ((h⁻¹).1.map σ)ᵀ * (h'.1.map σ)ᵀ * J' * (h'.1 * (h⁻¹).1)
        = ((h⁻¹).1.map σ)ᵀ * ((h'.1.map σ)ᵀ * J' * h'.1) * (h⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = ((h⁻¹).1.map σ)ᵀ * ((h.1.map σ)ᵀ * J * h.1) * (h⁻¹).1 := by rw [h2, h2']
      _ = (((h⁻¹).1.map σ)ᵀ * (h.1.map σ)ᵀ) * J * (h.1 * (h⁻¹).1) := by simp only [Matrix.mul_assoc]
      _ = J := by rw [e, e2, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel_left]

section CM
attribute [local instance] IsCMField.starRing

theorem exists_of_cm {E : Type} [Field E] [NumberField E] [IsCMField E] (hc : CMData (maximalRealSubfield E) E)
    (V V' : HSpace E) (hr : V'.rank = V.rank) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E))
      (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)),
      φ * ψ = 1 ∧ ψ * φ = 1 ∧
      (Formalism.UG.cT (sigR (Fv (maximalRealSubfield E) v) hc.sig) φ * JR (Fv (maximalRealSubfield E) v) V'.gram :
        Matrix (Fin V.rank) (Fin V'.rank) (Fv (maximalRealSubfield E) v ⊗[maximalRealSubfield E] E)) * φ =
        JR (Fv (maximalRealSubfield E) v) V.gram ∧
      ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V v ↔
        φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := maximalRealSubfield E) V' v := by
  obtain ⟨h, h1, h2⟩ := exists_orthonormal hc V v
  obtain ⟨h', h1', h2'⟩ := exists_orthonormal hc V' v
  obtain ⟨φ, ψ, a, b, c, d⟩ := exists_of_frames (sigR (Fv (maximalRealSubfield E) v) hc.sig) hr
    (JR (Fv (maximalRealSubfield E) v) V.gram) (JR (Fv (maximalRealSubfield E) v) V'.gram) h h' h2 h2' (ordAt E v)
  exact ⟨φ, ψ, a, b, c, fun x => (h1 x).trans ((d x).trans (h1' _).symm)⟩

end CM

theorem exists_local_isometry : ∀ (D : D7) (V V' : Formalism.BasicNotions.TH.HSp D), V'.rank = V.rank → ∀ v : HeightOneSpectrum (𝓞 D.host.F), ∃ (φ : Matrix (Fin V'.rank) (Fin V.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)) (ψ : Matrix (Fin V.rank) (Fin V'.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)), φ * ψ = 1 ∧ ψ * φ = 1 ∧ (Formalism.UG.cT (sigR (Fv D.host.F v) D.sp.cm.sig) φ * JR (Fv D.host.F v) V'.gram : Matrix (Fin V.rank) (Fin V'.rank) (Fv D.host.F v ⊗[D.host.F] D.host.E)) * φ = JR (Fv D.host.F v) V.gram ∧ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V v ↔ φ.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := D.host.F) V' v := by
  intro D V V' hr v
  have := D.host.isCMField_hostE
  have key := exists_of_cm (E := D.host.E) D.sp.cm V V' hr v
  exact key

end GlobalTheory.LocalIsometryEqualRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicPowMulMemTensorUnramifiedIntegers
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKRes.Denom

variable (p : ℕ) [Fact p.Prime]

theorem exists_pow_mul_norm_le_one (y : PadicAlgCl p) : ∃ k : ℕ, ‖(p : PadicAlgCl p) ^ k * y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one
  | exact _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one
  | (apply _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerScaledNormBound.exists_pow_mul_norm_le_one ..)

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

theorem inclK_mem (a : K) (ha : ‖(a : PadicAlgCl p)‖ ≤ 1) : inclK p K r a ∈ intKQ p K r :=
  Subring.subset_closure (Or.inl ⟨⟨a, (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff (p := p)).2 ha⟩, rfl⟩)

theorem inclQ_mem (b : Qr p r) (hb : ‖(b : PadicAlgCl p)‖ ≤ 1) : inclQ p K r b ∈ intKQ p K r :=
  Subring.subset_closure (Or.inr ⟨⟨b, (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff (p := p)).2 hb⟩, rfl⟩)

theorem aux (x : K ⊗[ℚ_[p]] Qr p r) :
    ∃ k : ℕ, (p : K ⊗[ℚ_[p]] Qr p r) ^ k * x ∈ intKQ p K r := by
  have hp : ∀ m : ℕ, (p : K ⊗[ℚ_[p]] Qr p r) ^ m ∈ intKQ p K r := fun m => pow_mem (natCast_mem _ p) m
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [mul_zero]; exact (intKQ p K r).zero_mem⟩
  | tmul a b =>
    obtain ⟨k, hk⟩ := exists_pow_mul_norm_le_one p (a : PadicAlgCl p)
    obtain ⟨l, hl⟩ := exists_pow_mul_norm_le_one p (b : PadicAlgCl p)
    refine ⟨k + l, ?_⟩
    have e : (p : K ⊗[ℚ_[p]] Qr p r) ^ (k + l) * (a ⊗ₜ[ℚ_[p]] b) =
        ((p : K) ^ k * a) ⊗ₜ[ℚ_[p]] ((p : Qr p r) ^ l * b) := by
      calc (p : K ⊗[ℚ_[p]] Qr p r) ^ (k + l) * (a ⊗ₜ[ℚ_[p]] b)
          = (Algebra.TensorProduct.includeLeft (R := ℚ_[p]) (S := ℚ_[p]) (B := Qr p r) ((p : K) ^ k)) *
            (Algebra.TensorProduct.includeRight (R := ℚ_[p]) (A := K) ((p : Qr p r) ^ l)) * (a ⊗ₜ[ℚ_[p]] b) := by
            simp only [map_pow, map_natCast, pow_add]
        _ = _ := by
            simp only [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    have hm := mul_mem (inclK_mem p K r ((p : K) ^ k * a) (by simpa using hk))
      (inclQ_mem p K r ((p : Qr p r) ^ l * b) (by simpa using hl))
    have e2 : inclK p K r ((p : K) ^ k * a) * inclQ p K r ((p : Qr p r) ^ l * b) =
        ((p : K) ^ k * a) ⊗ₜ[ℚ_[p]] ((p : Qr p r) ^ l * b) := by
      change (((p : K) ^ k * a) ⊗ₜ[ℚ_[p]] (1 : Qr p r)) * ((1 : K) ⊗ₜ[ℚ_[p]] ((p : Qr p r) ^ l * b)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [← e2]
    exact hm
  | add x y hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    refine ⟨k + l, ?_⟩
    have e : (p : K ⊗[ℚ_[p]] Qr p r) ^ (k + l) * (x + y) =
        (p : K ⊗[ℚ_[p]] Qr p r) ^ l * ((p : K ⊗[ℚ_[p]] Qr p r) ^ k * x) +
          (p : K ⊗[ℚ_[p]] Qr p r) ^ k * ((p : K ⊗[ℚ_[p]] Qr p r) ^ l * y) := by
      ring
    rw [e]
    exact add_mem (mul_mem (hp l) hk) (mul_mem (hp k) hl)

end GlobalTheory.LKRes.Denom

namespace GlobalTheory.LKRes

theorem exists_pow_mul_mem_intKQ : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)
    (x : KQ p K r), ∃ k : ℕ, (p : KQ p K r) ^ k * x ∈ intKQ p K r :=
  fun p _ K r x => Denom.aux p K r x

end GlobalTheory.LKRes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerSectionSpecialFibreStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_power_section_special_fibre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X],
  (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) →
  ∀ (π : Γ(X, ⊤)), genericPoint X ∈ X.basicOpen π → (∃ z : X, z ∉ X.basicOpen π) →
  ∀ (L : LB X) (τ : L.ι → X.functionFieldˣ), L.IsLB → IsRatSec L τ →
    (∀ (i : L.ι) (z : X), z ∈ L.U i → z ∈ X.basicOpen π → UnitAt z (τ i : X.functionField)) →
    ∃ (M : ℕ) (n : ℤ) (x₀ : X), 1 ≤ M ∧ x₀ ∉ X.basicOpen π ∧
      (∀ (i : L.ι) (z : X), z ∈ L.U i → IsDiscreteValuationRing (X.presheaf.stalk z) →
        RegAt z (fnOf ⊤ trivial π ^ n * ((τ i : X.functionField) ^ M)⁻¹)) ∧
      (∀ i : L.ι, x₀ ∈ L.U i → UnitAt x₀ (fnOf ⊤ trivial π ^ n * ((τ i : X.functionField) ^ M)⁻¹)) := by
  first | exact @GlobalTheory.ExpChoice.exists_exponents | exact GlobalTheory.ExpChoice.exists_exponents | (intros; apply GlobalTheory.ExpChoice.exists_exponents <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimePowMulEqIntOfIntegralFiniteAdeleAway
section
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.RatDenAwayP

theorem val_le_one (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) (v : AwayP p) :
    v.1.valuation ℚ q ≤ 1 := by
  have h1 : (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q) v.1 ∈ v.1.adicCompletionIntegers ℚ := h v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  exact h1

def primeHOS (l : ℕ) (hl : l.Prime) : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(l : ℤ)}
  isPrime := (Ideal.span_singleton_prime (by exact_mod_cast hl.ne_zero)).2 (Nat.prime_iff_prime_int.mp hl)
  ne_bot := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hl.ne_zero

theorem prime_dvd_den (p : ℕ) (q : ℚ) (h : algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p) {l : ℕ} (hl : l.Prime)
    (hd : l ∣ q.den) : l = p := by
  by_contra hne
  have hv : (primeHOS l hl).asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro e
    have e' : Ideal.span {(l : ℤ)} = Ideal.span {(p : ℤ)} := e
    rw [Ideal.span_singleton_eq_span_singleton] at e'
    have h1 : l ∣ p := Int.natCast_dvd_natCast.1 e'.dvd
    have h2 : p ∣ l := Int.natCast_dvd_natCast.1 e'.symm.dvd
    exact hne (Nat.dvd_antisymm h1 h2)
  let v : AwayP p := ⟨primeHOS l hl, hv⟩
  have hq := val_le_one p q h v
  have hden : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) < 1 := by
    rw [valuation_lt_one_iff_mem]
    show ((q.den : ℤ)) ∈ Ideal.span {(l : ℤ)}
    rw [Ideal.mem_span_singleton]; exact_mod_cast hd
  have hnum : (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ q.num) < 1 := by
    have e : algebraMap ℤ ℚ q.num = q * algebraMap ℤ ℚ (q.den : ℤ) := by
      rw [algebraMap_int_eq, eq_intCast, eq_intCast, Int.cast_natCast, Rat.mul_den_eq_num]
    rw [e, map_mul]
    calc (primeHOS l hl).valuation ℚ q * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ))
        ≤ 1 * (primeHOS l hl).valuation ℚ (algebraMap ℤ ℚ (q.den : ℤ)) := by gcongr
      _ < 1 := by rw [one_mul]; exact hden
  rw [valuation_lt_one_iff_mem] at hnum
  change q.num ∈ Ideal.span {(l : ℤ)} at hnum
  rw [Ideal.mem_span_singleton, Int.natCast_dvd] at hnum
  have hc : Nat.Coprime l q.den := Nat.Coprime.coprime_dvd_left hnum q.reduced
  exact (Nat.Prime.coprime_iff_not_dvd hl).1 hc hd

end GlobalTheory.RatDenAwayP

namespace GlobalTheory

theorem ratDen_pow_of_intAfP : ∀ (p : ℕ) [Fact p.Prime] (q : ℚ), algebraMap ℚ (AfP p) q ∈ LevelExists.intAfP p →
    ∃ k : ℕ, ∃ a : ℤ, ((p ^ k : ℕ) : ℚ) * q = a := by
  intro p _ q h
  have hden : q.den = p ^ q.den.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd q.den_nz (fun hl hd => RatDenAwayP.prime_dvd_den p q h hl hd)
  refine ⟨q.den.primeFactorsList.length, q.num, ?_⟩
  rw [← hden]
  exact Rat.den_mul_eq_num q

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeSaturationGenericHyperplaneSectionStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_saturation_generic_hyperplane_section : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (∀ u : Fin N → AlgebraicClosure K, ∃ y : Fin N → AlgebraicClosure K, y ≠ 0 ∧ (∀ g ∈ P, aeval y g = 0) ∧ ∑ j, u j * y j = 0) → ∃ Q : Ideal (MvPolynomial (Fin N) L), Q.IsPrime ∧ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)} ≤ Q ∧ ∀ g ∈ Q, ∀ j, ∃ m : ℕ, X j ^ m * g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) ⊔ Ideal.span {(∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L)} := by
  first | exact @GlobalTheory.Chow.exists_prime_saturation_generic_section | exact GlobalTheory.Chow.exists_prime_saturation_generic_section | (intros; apply GlobalTheory.Chow.exists_prime_saturation_generic_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyFiniteSubgroupScheme
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbelianQuotientField

open AffineQuotient AbelianQuotient

set_option backward.isDefEq.respectTransparency false in

theorem exists_quotient : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (H : Over (Sp K)) [GrpObj H] (i : H ⟶ A), IsMonHom i → Mono i → IsFinite H.hom → ∃ (A' : Over (Sp K)) (_ : GrpObj A'), IsAbelianScheme A' ∧ ∃ q : A ⟶ A', IsMonHom q ∧ IsFinite q.left ∧ Flat q.left ∧ Surjective q.left ∧ IsPullback i (toUnit H) q η[A'] := by
  intro K _ _ A _ hA H _ i hi hmono hfin
  have := hA.comm
  have := hA.proper
  have := hA.smooth
  have := hA.geomConnected
  have hflat : Flat H.hom := inferInstance
  have : IsCommMonObj H := ⟨by
    rw [← cancel_mono i, Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  obtain ⟨N, hN, hH⟩ := GlobalTheory.FiniteFlatKilled.main K H hfin hflat
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsFinite (𝟙 A ^ N : A ⟶ A).left := GlobalTheory.T.isFinite_mulByNat_abelianVariety K A hA N hN
  have : IsFinite H.hom := hfin
  obtain ⟨Λ, _, _, _, _, e, _⟩ := exists_hopfAlgebra K H
  have hi' : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hH, MonObj.one_comp]
  obtain ⟨Q, q, π, h₁, h₂, h₃, h₄, h₅⟩ := exists_quotient_hopf
    (GlobalTheory.HopfQuot.affine_quotient GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal)
    (e.hom ≫ i) (𝟙 A ^ N) (by
      rw [comp_pow, comp_pow, Category.comp_id, Category.comp_id, mul_pow, ← comp_pow,
        ← comp_pow i, hi', comp_one, comp_one, _root_.one_mul])
  have hq : IsPullback ((fst H A ≫ i) * snd H A) (snd H A) q q := by
    refine h₅.of_iso (whiskerRightIso e A) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      <;> simp [comp_mul]
  have : Flat q.left := h₃
  have : Surjective q.left := h₄
  have : IsFinite q.left := h₂
  have : IsFinite π.left := h₁
  obtain ⟨inst, hcomm, hhom, hker⟩ := exists_grpObj i q hq
  refine ⟨Q, inst, ?_, q, hhom, h₂, h₃, h₄, hker⟩
  have hπ : π.left ≫ A.hom = Q.hom := Over.w π
  have : IsSeparated Q.hom := by rw [← hπ]; infer_instance
  have : LocallyOfFiniteType Q.hom := by rw [← hπ]; infer_instance
  have hw : q.left ≫ Q.hom = A.hom := Over.w q
  have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : Flat (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : UniversallyClosed (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyReduced (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have : GeometricallyConnected (q.left ≫ Q.hom) := by rw [hw]; infer_instance
  have := flat_of_comp_of_flat_of_surjective q.left Q.hom
  have := UniversallyClosed.of_comp_surjective q.left Q.hom
  have := geometricallyReduced_of_comp q.left Q.hom
  have : LocallyOfFinitePresentation Q.hom := inferInstance
  exact ⟨hcomm, smooth_of_grpObj_of_flat Q, ⟨⟩, geometricallyConnected_of_comp q.left Q.hom⟩

end GlobalTheory.AbelianQuotientField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatSecUnitGenericFibreStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratSec_unit_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (Z : Scheme.{0}) [IsIntegral Z] (f : Z ⟶ Spec (.of O)) (D : LB Z), Flat f → D.IsLB →
  ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
  ∃ τ : D.ι → Z.functionFieldˣ, IsRatSec D τ ∧
    (∀ (i : D.ι) (z : Z), z ∈ D.U i → z ∈ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) →
      UnitAt z (τ i : Z.functionField)) ∧
    ∀ (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen),
      (∀ (i : D.ι) (h : genericPoint Z ∈ D.U i),
        fnOf ((lbPow D M).U i) h (gen.s i).1 * fnOf ⊤ trivial (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) ^ n =
          (τ i : Z.functionField) ^ M) →
      PowEq f ϖ hϖ D sig M n gen := by
  first | exact @GlobalTheory.GenericRatSec.exists_ratSec | exact GlobalTheory.GenericRatSec.exists_ratSec | (intros; apply GlobalTheory.GenericRatSec.exists_ratSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedFibrePointStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduced_fibre_point : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (z : Z),
  z ∉ Z.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (.of O)).inv.hom ϖ)) → ∃ y : reducedSpecialFibre f, reducedSpecialι f y = z := by
  first | exact @GlobalTheory.exists_reducedSpecialFibre_of_not_mem_basicOpen | exact GlobalTheory.exists_reducedSpecialFibre_of_not_mem_basicOpen | (intros; apply GlobalTheory.exists_reducedSpecialFibre_of_not_mem_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitSupportedUnitaryLiftDetOneStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_supported_unitary_lift_detOne : ∀ {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}, IsBaseFrame V β Λ N → ∀ {P : Pl D.host.E} {e : AE D}, Formalism.L2.NTheta.IsIdemAt e P → ∀ (k : GL (Fin V.rank) (kP P)), Matrix.GeneralLinearGroup.det k = 1 → ∃ κ : GA D V, SuppAt e V κ ∧ κ ∈ GfC V ∧ finE V κ ∈ St β ∧ redFn β P (finE V κ) = k ∧ (∀ P', P' ≠ P → ¬ Lev.IsConjPl P P' → redFn β P' (finE V κ) = 1) ∧ IsDetAt e V κ 1 := by
  first | exact @GlobalTheory.ParahoricLiftDet.exists_local_lift_det | exact GlobalTheory.ParahoricLiftDet.exists_local_lift_det | (intros; apply GlobalTheory.ParahoricLiftDet.exists_local_lift_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitConjOfMinpolyEq
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def evalQuot {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : AdjoinRoot q →ₐ[F] C :=
  Ideal.Quotient.liftₐ (Ideal.span {q}) (Polynomial.aeval x) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hx, mul_zero])

theorem evalQuot_root {F C : Type} [Field F] [Ring C] [Algebra F C] (q : Polynomial F) (x : C)
    (hx : Polynomial.aeval x q = 0) : evalQuot q x hx (AdjoinRoot.root q) = x := by
  change Polynomial.aeval x Polynomial.X = x
  simp

section Generic2

variable {S : Type*} [Ring S]

theorem triv_change (σ : S →+* Sᵐᵒᵖ) (x u : Sˣ) (b : S) :
    ((x * u⁻¹ : Sˣ) : S) * ((u : S) * b * (σ u).unop) * (σ ((x * u⁻¹ : Sˣ) : S)).unop =
      x * b * (σ x).unop := by
  have h1 : (σ u).unop * (σ ((u⁻¹ : Sˣ) : S)).unop = 1 := by
    rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
  calc ((x * u⁻¹ : Sˣ) : S) * ((u : S) * b * (σ u).unop) * (σ ((x * u⁻¹ : Sˣ) : S)).unop
      = x * ((((u⁻¹ : Sˣ) : S) * u) * b * ((σ u).unop * (σ ((u⁻¹ : Sˣ) : S)).unop)) * (σ x).unop := by
        simp only [Units.val_mul, map_mul, MulOpposite.unop_mul, mul_assoc]
    _ = _ := by rw [Units.inv_mul, h1, one_mul, mul_one]

end Generic2

namespace Pair

variable {G : HTGroup p}

theorem sh_mul (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_sh (a : G.C) : sh G (sh G a) = a := G.star_star a

theorem sh_units_mul_inv (y : G.Cˣ) : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul, Units.inv_mul]; simp [sh]

theorem inC_sh (R : Type) [CommRing R] [Algebra ℚ R] (a : G.C) :
    inC G R (sh G a) = (starT G.star R (inC G R a)).unop :=
  (starT_tmul G.star R 1 a).symm

theorem triv_conj (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (y : G.Cˣ) (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ)
    (hx : Triv G R β x t) :
    Triv G R ((y : G.C) * β * sh G y) (x * (Units.map (inC G R).toMonoidHom y)⁻¹) t := by
  unfold Triv at hx ⊢
  have e : inC G R ((y : G.C) * β * sh G y) =
      ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C) * inC G R β *
        (starT G.star R ((Units.map (inC G R).toMonoidHom y : (R ⊗[ℚ] G.C)ˣ) : R ⊗[ℚ] G.C)).unop := by
    rw [map_mul, map_mul, inC_sh]; rfl
  rw [e, triv_change, hx]

def conjBy (Q : Pair G) (y : G.Cˣ) (γ' : G.Cˣ) (hγ : (γ' : G.C) = y * Q.γ * ↑y⁻¹)
    (hreg : (minpoly G.F (γ' : G.C)).natDegree = G.n ∧ (minpoly G.F (γ' : G.C)).Separable) : Pair G where
  β := y * Q.β * Units.mk (sh G y) (sh G ((y⁻¹ : G.Cˣ) : G.C)) (sh_units_mul_inv y)
    (by rw [← sh_mul, Units.mul_inv]; simp [sh])
  γ := γ'
  c := Q.c
  sym := by
    simp only [Units.val_mul, Units.val_mk, sh_mul, sh_sh, Q.sym, mul_assoc]
  sim := by
    simp only [Units.val_mul, Units.val_mk]
    rw [hγ, sh_mul, sh_mul]
    have h1 : ((y⁻¹ : G.Cˣ) : G.C) * y = 1 := Units.inv_mul y
    have h2 : sh G (y : G.C) * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := sh_units_mul_inv y
    calc (y : G.C) * Q.γ * ↑y⁻¹ * (y * Q.β * sh G y) * (sh G ((y⁻¹ : G.Cˣ) : G.C) * (sh G ↑Q.γ * sh G y))
        = y * (Q.γ * (((y⁻¹ : G.Cˣ) : G.C) * y) * Q.β * (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C)) *
            sh G Q.γ) * sh G y := by
          simp only [mul_assoc]
      _ = y * (algebraMap ℚ G.C Q.c * Q.β) * sh G y := by rw [h1, h2, mul_one, mul_one, Q.sim]
      _ = _ := by rw [← mul_assoc, ← Algebra.commutes, mul_assoc, mul_assoc, mul_assoc]
  reg := hreg
  trivAf := by
    obtain ⟨x, t, hx⟩ := Q.trivAf
    exact ⟨_, t, by simpa only [Units.val_mul, Units.val_mk] using triv_conj (AfP p) Q.β y x t hx⟩
  trivR := by
    obtain ⟨z, hz⟩ := Q.trivR
    exact ⟨_, by simpa only [Units.val_mul, Units.val_mk] using triv_conj ℝ Q.β y z 1 hz⟩

end Pair

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsThroughZeroLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factors_through_zero_locus : ∀ (Rg : Type) [CommRing Rg] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) Rg)) (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)), (∃ w : T ⟶ Sp (MvPolynomial (Fin n) Rg ⧸ I), w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔ ∀ P ∈ I, GlobalTheory.FormsLocus.ringOf g P = 0 := by
  first | (exact @GlobalTheory.FormsLocus.factors_quot_iff) | (exact GlobalTheory.FormsLocus.factors_quot_iff) | (intros; apply GlobalTheory.FormsLocus.factors_quot_iff  <;> assumption)
end

