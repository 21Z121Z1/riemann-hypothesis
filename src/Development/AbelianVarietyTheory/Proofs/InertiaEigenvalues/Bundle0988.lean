import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0982
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0983
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumKeepingLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralScalarInverseUniformisersIdempotentSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CentralScalar

section Alg

variable {R ι : Type} [CommRing R] {s : Finset ι} {p q : ι → R}

def comp (s : Finset ι) (p q u v : ι → R) : R := 1 + ∑ i ∈ s, (p i * (u i - 1) + q i * (v i - 1))

theorem comp_swap (u v : ι → R) : comp s p q u v = comp s q p v u := by
  unfold comp
  congr 1
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

theorem left_mul_comp (h1 : ∀ i ∈ s, p i * p i = p i) (h2 : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * p j = 0)
    (h3 : ∀ i ∈ s, ∀ j ∈ s, p i * q j = 0) (u v : ι → R) {i : ι} (hi : i ∈ s) :
    p i * comp s p q u v = p i * u i := by
  unfold comp
  rw [mul_add, Finset.mul_sum, Finset.sum_eq_single_of_mem i hi]
  · rw [mul_add, ← mul_assoc, ← mul_assoc, h1 i hi, h3 i hi i hi]; ring
  · intro j hj hji
    rw [mul_add, ← mul_assoc, ← mul_assoc, h2 i hi j hj hji, h3 i hi j hj]; ring

theorem comp_mul (hp : ∀ u v : ι → R, ∀ i ∈ s, p i * comp s p q u v = p i * u i)
    (hq : ∀ u v : ι → R, ∀ i ∈ s, q i * comp s p q u v = q i * v i) (u v u' v' : ι → R) :
    comp s p q u v * comp s p q u' v' = comp s p q (fun i => u i * u' i) (fun i => v i * v' i) := by
  have h : comp s p q u v * comp s p q u' v' =
      comp s p q u' v' + ∑ i ∈ s, (p i * u' i * (u i - 1) + q i * v' i * (v i - 1)) := by
    conv_lhs => rw [comp]
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← hp u' v' i hi, ← hq u' v' i hi]; ring
  rw [h]
  unfold comp
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem comp_eq_one {u v : ι → R} (hu : ∀ i ∈ s, u i = 1) (hv : ∀ i ∈ s, v i = 1) : comp s p q u v = 1 := by
  unfold comp
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [hu i hi, hv i hi]; ring

theorem mul_pow_of_mul_eq {e a w : R} (h : e * a = e * w) (n : ℕ) : e * a ^ n = e * w ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_right_comm, h, pow_succ]; ring

theorem map_comp (c : R →+* R) (hc : ∀ x, c (c x) = x) (u v : ι → R) :
    c (comp s p (fun i => c (p i)) u v) = comp s p (fun i => c (p i)) (fun i => c (v i)) (fun i => c (u i)) := by
  unfold comp
  rw [map_add, map_one, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_add, map_mul, map_sub, map_one, hc]
  ring

end Alg

variable {D : D7}

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem mt_inj (V : HSp D) {a b : GA D V} (h : Formalism.L2.Theta.mt V a = Formalism.L2.Theta.mt V b) : a = b :=
  Subtype.ext (Units.ext h)

theorem exists_scalar (V : HSp D) (a : AE D) (ha : cA D a * a = 1) :
    ∃ z : GA D V, Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a := by
  have h1 : (Matrix.diagonal fun _ : Fin V.rank => a) * (Matrix.diagonal fun _ => cA D a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one]
  have h2 : (Matrix.diagonal fun _ : Fin V.rank => cA D a) * (Matrix.diagonal fun _ => a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ha, Matrix.diagonal_one]
  refine ⟨⟨⟨_, _, h1, h2⟩, ?_⟩, rfl⟩
  change Formalism.UG.cT (cA D) (Matrix.diagonal fun _ => a) * _ * (Matrix.diagonal fun _ => a) = _
  have h3 : Formalism.UG.cT (cA D) (Matrix.diagonal fun _ : Fin V.rank => a) = Matrix.diagonal fun _ => cA D a := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [h3]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_right_comm, ha, one_mul]

theorem scalar_central (V : HSp D) {a : AE D} {z : GA D V} (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) :
    z ∈ Subgroup.center (GA D V) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply mt_inj V
  change Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V z = Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V g
  rw [hz]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem scalar_fin (V : HSp D) {a : AE D} (ha : infPart D a = 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) : z ∈ GfC V := by
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  change (Formalism.L2.Theta.mt V z).map (infPart D) = 1
  rw [hz, Matrix.diagonal_map (map_zero _)]
  simp only [ha, Matrix.diagonal_one]

theorem scalar_inv (V : HSp D) {a : AE D} (ha : cA D a * a = 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) :
    Formalism.L2.Theta.mt V z⁻¹ = Matrix.diagonal fun _ => cA D a := by
  have h1 : (Matrix.diagonal fun _ : Fin V.rank => a) * (Matrix.diagonal fun _ => cA D a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one]
  have h := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_inv_mul V z
  rw [← Matrix.mul_one (Formalism.L2.Theta.mt V z⁻¹), ← h1, ← Matrix.mul_assoc, ← hz, h, Matrix.one_mul]

theorem scalar_supp (V : HSp D) {e a : AE D} (ha : (e + cA D e) * (a - 1) = a - 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) : SuppAt e V z := by
  intro i j
  rw [hz]
  by_cases h : i = j
  · subst h
    simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using ha
  · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero, mul_zero]

theorem centralScalar : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → (∀ PP ∈ Q, ϖ PP ≠ 0) → (∃ z : GA D V, mt V z = Matrix.diagonal fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ ∀ z : GA D V, mt V z = Matrix.diagonal (fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) → z ∈ Subgroup.center (GA D V) ∧ z ∈ GfC V ∧ SuppAt (∑ PP ∈ Q, es PP) V z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D (∑ PP ∈ Q, es PP)) V z x ∧ (x : AE D) = 1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1)) ∧ mt V z⁻¹ = Matrix.diagonal (fun _ => cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E)) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) := by
  intro D V Q es ϖ hes hc hϖ
  have h1 : ∀ i ∈ Q, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es Q h1 hc
  have h2 : ∀ i ∈ Q, ∀ j ∈ Q, j ≠ i → es i * es j = 0 := fun i hi j hj h =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes i hi) (hes j hj) (hx i hi j hj) (hx j hj i hi) h
  have hp : ∀ u v : Pl D.host.E → AE D, ∀ i ∈ Q,
      es i * comp Q es (fun i => cA D (es i)) u v = es i * u i := fun u v i hi => left_mul_comp h1 h2 hx u v hi
  have hq : ∀ u v : Pl D.host.E → AE D, ∀ i ∈ Q,
      cA D (es i) * comp Q es (fun i => cA D (es i)) u v = cA D (es i) * v i := fun u v i hi => by
    rw [comp_swap]
    refine left_mul_comp (p := fun i => cA D (es i)) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun i hi j hj => ?_) v u hi
    · rw [← map_mul, h1 i hi]
    · rw [← map_mul, h2 i hi j hj h, map_zero]
    · rw [mul_comm]; exact hx j hj i hi
  have hne : ∀ i ∈ Q, (ϖ i : D.host.E) ≠ 0 := fun i hi h => hϖ i hi (RingOfIntegers.coe_eq_zero_iff.1 h)
  set a : AE D := 1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) +
    cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)) with ha
  have ha' : a = comp Q es (fun i => cA D (es i)) (fun PP => incA D ((ϖ PP : D.host.E)⁻¹))
    (fun PP => incA D (star (ϖ PP : D.host.E))) := rfl
  have hca : cA D a = comp Q es (fun i => cA D (es i)) (fun PP => incA D (ϖ PP : D.host.E))
      (fun PP => incA D (star (ϖ PP : D.host.E)⁻¹)) := by
    rw [ha', map_comp (cA D) GlobalTheory.DualPairCheck.cA_cA]
    simp only [cA_incA, star_star]
  have hn : cA D a * a = 1 := by
    rw [hca, ha', comp_mul hp hq]
    refine comp_eq_one (fun i hi => ?_) (fun i hi => ?_)
    · rw [← map_mul, mul_inv_cancel₀ (hne i hi), map_one]
    · rw [← map_mul, ← star_mul, mul_inv_cancel₀ (hne i hi), star_one, map_one]
  refine ⟨exists_scalar V a hn, fun z hz => ⟨scalar_central V hz, scalar_fin V ?_ hz, scalar_supp V ?_ hz, ?_,
    scalar_inv V hn hz, ?_, ?_, ?_, ?_⟩⟩
  · rw [ha, map_add, map_one, map_sum, Finset.sum_eq_zero, add_zero]
    intro i hi
    have h0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_splitIdem (hes i hi).1
    rw [map_add, map_mul, map_mul, h0, GlobalTheory.PlaceVec.infPart_cA h0, zero_mul, zero_mul, add_zero]
  · have : a - 1 = ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) +
      cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)) := by rw [ha, add_sub_cancel_left]
    conv_rhs => rw [this]
    rw [map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [add_mul, mul_sub, mul_sub, ha', hp _ _ i hi, hq _ _ i hi]
    ring
  · have hu : comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) *
        comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)⁻¹) ^ V.rank) = 1 := by
      rw [comp_mul hp hq]
      refine comp_eq_one (fun i _ => one_mul _) (fun i hi => ?_)
      rw [← mul_pow, ← map_mul, ← star_mul, inv_mul_cancel₀ (hne i hi), star_one, map_one, one_pow]
    have hv : comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) =
        1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1) := by
      simp only [comp, sub_self, mul_zero, zero_add]
    refine ⟨Units.mkOfMulEqOne _ _ hu, ?_, hv⟩
    change comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) = _
    rw [hv, hz, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_sum, Finset.sum_mul]
    have : ∀ i ∈ Q, cA D (es i) * a ^ V.rank = cA D (es i) * incA D (star (ϖ i : D.host.E)) ^ V.rank :=
      fun i hi => mul_pow_of_mul_eq (hq _ _ i hi) _
    rw [Finset.sum_congr rfl this]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    ring
  · rw [mul_comm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => hp _ _ i hi
  · rw [mul_comm, Finset.sum_mul, hca]
    exact Finset.sum_congr rfl fun i hi => hp _ _ i hi
  · rw [mul_comm, map_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [map_mul, cA_incA]; exact hq _ _ i hi
  · rw [mul_comm, map_sum, map_sum, Finset.sum_mul, hca]
    exact Finset.sum_congr rfl fun i hi => by rw [map_mul, cA_incA]; exact hq _ _ i hi

end GlobalTheory.CentralScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenFieldFormsProportionalOfReadings
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem tensor_exists_basis_expansion {O K L M ι : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    [Field L] [Algebra O L] [AddCommGroup M] [Module O M] [Module K M] [IsScalarTower O K M] [Fintype ι]
    (hinj : ∀ d : O, d ≠ 0 → algebraMap O L d ≠ 0) (v : Module.Basis ι K M) (x : L ⊗[O] M) :
    ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨c, e⟩ := hx
    obtain ⟨c', e'⟩ := hy
    refine ⟨c + c', ?_⟩
    rw [e, e']
    simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) fun c => v.repr f c
    choose y hy using hd
    have e : (d : O) • (a ⊗ₜ[O] f) = ∑ c, (y c • a) ⊗ₜ[O] v c := by
      rw [← TensorProduct.tmul_smul]
      conv_lhs => rw [← v.sum_repr f]
      rw [Finset.smul_sum, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [TensorProduct.smul_tmul, ← algebraMap_smul K (y c), hy, smul_assoc]
    have h0 := hinj d (nonZeroDivisors.coe_ne_zero d)
    refine ⟨fun c => (algebraMap O L d)⁻¹ • y c • a, ?_⟩
    rw [← algebraMap_smul L (d : O)] at e
    rw [← inv_smul_smul₀ h0 (a ⊗ₜ[O] f), e, Finset.smul_sum]
    simp only [TensorProduct.smul_tmul']

private theorem tensor_scalar_relation {O L M N ι : Type*} [CommRing O] [Field L] [Algebra O L] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module ℂ N] [Fintype ι] (ε : L →+* ℂ) (v : ι → M) (r : M → N) (R : L ⊗[O] M →ₛₗ[ε] N)
    (hR : ∀ a f, R (a ⊗ₜ f) = ε a • r f) (hli : LinearIndependent ℂ fun c => r (v c))
    (hsp : ∀ x : L ⊗[O] M, ∃ cf : ι → L, x = ∑ a, cf a ⊗ₜ v a) (A B : L ⊗[O] M) (z : ℂ) (h : R A = z • R B) :
    (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : L, ε t = z ∧ A = t • B) := by
  obtain ⟨α, rfl⟩ := hsp A
  have hind := Fintype.linearIndependent_iff.1 hli
  constructor
  · rintro rfl
    rw [map_zero, smul_zero, map_sum] at h
    simp only [hR] at h
    have h2 : ∀ a, α a = 0 := fun a => ε.injective ((hind _ h a).trans (map_zero _).symm)
    simp [h2]
  · obtain ⟨β, rfl⟩ := hsp B
    intro hB
    rw [map_sum, map_sum] at h
    simp only [hR] at h
    have h1 : ∀ a, ε (α a) - z * ε (β a) = 0 := hind (fun a => ε (α a) - z * ε (β a)) (by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, h, sub_self])
    have h2 : ∃ a, β a ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hB (by simp [hc])
    obtain ⟨a0, ha0⟩ := h2
    have h3 : ε (β a0) ≠ 0 := (map_ne_zero ε).2 ha0
    have ht : ε (α a0 / β a0) = z := by
      rw [map_div₀, sub_eq_zero.1 (h1 a0), mul_div_cancel_right₀ _ h3]
    refine ⟨α a0 / β a0, ht, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    congr 1
    apply ε.injective
    rw [map_mul, ht, sub_eq_zero.1 (h1 a)]

theorem _root_.GlobalTheory.T.chosenField_forms_proportional_of_readings : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw) (hρ : ρ.Good) (j : Fin D.R.m) (rd : Rd ρ D.nexp (c.twI w) j (c.sd w)), Faithful rd → ∀ (ε : KE c w →+* ℂ) (hε : Extends ρ ε) (A B : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w)) (z : ℂ),
  rdF rd hρ hε A = z • rdF rd hρ hε B → (B = 0 → A = 0) ∧ (B ≠ 0 → ∃ t : KE c w, ε t = z ∧ A = t • B) := by
  intro D c w ρ hρ j rd hF ε hε A B z h
  let v := Module.finBasis (FractionRing (D.ntw.O (c.twI w))) (D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w))
  have hinj : ∀ d : D.ntw.O (c.twI w), d ≠ 0 → algebraMap _ (KE c w) d ≠ 0 := fun d hd h0 => by
    have h1 := congrArg ε h0
    rw [IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply, hρ.ek_e, map_zero] at h1
    exact hd (ρ.eO_injective (c.twI w) (c.sd w) (h1.trans (map_zero _).symm))
  exact tensor_scalar_relation ε v rd (rdF rd hρ hε) (rdF_tmul hρ hε) (hF _ v v.linearIndependent) (tensor_exists_basis_expansion hinj v) A B z h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenTwistViaEmbeddingGoodConjugate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

noncomputable section

namespace GlobalTheory.PlaceRead

open GlobalTheory.TwistGood

theorem twistOf_good (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X) (hρ : ρ.Good)
    (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ)
    (e : X.Ok i k →+* ℂ) (hψ : Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ) :
    (twistOf ρ.rc e (ρ.ch i) Q ψ).Good ∧ (ρ.B i j b).admitted (twistOf ρ.rc e (ρ.ch i) Q ψ).Q := by
  classical
  obtain ⟨hsplit, hdisj, hopen, hanti, hzk, hram, -⟩ := hψ
  have hadm : (ρ.B i j b).admitted (half (ρ.ch i) Q) := GlobalTheory.T.chosenPlaces_admissible_goodSetup D N X ρ hρ i j b Q hsplit hdisj
  let g : (X.Ok i k)ˣ →* Circle := unitPart.comp (Units.map e.toMonoidHom)
  have hkey : charOf ρ.rc e ψ = ρ.rc.pull (g.comp ψ) := by
    rw [Recip.pull_comp _ hopen]
    rfl
  have hz : X.zk i k ^ (X.l i ^ k) = 1 := Units.ext (by simpa using (X.zk_prim i k).pow_eq_one)
  have hpow : ∀ σ, ψ σ ^ (X.l i ^ k) = 1 := by
    intro σ
    obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  refine ⟨?_, hadm⟩
  show (⟨half (ρ.ch i) Q, charOf ρ.rc e ψ, resOf (charOf ρ.rc e ψ)⟩ : Twist D Circle).Good
  rw [hkey]
  refine GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame D N X ρ.rc hρ.rc Circle (g.comp ψ) (X.l i) (X.lPrime i).out
    (fun σ => ⟨k, by rw [MonoidHom.comp_apply, ← map_pow, hpow, map_one]⟩) ?_ ?_ _ ?_ ?_ ?_
  · exact Subgroup.isOpen_mono (H₁ := ψ.ker) (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) hopen
  · intro x x' hx
    show g (ψ x') = (g (ψ x))⁻¹
    rw [hanti x x' hx, map_inv]
  · obtain ⟨P, -, h2, h3⟩ := hadm.1.split
    exact h3.mono (Finset.subset_union_right.trans h2)
  · intro P hP hl
    exact Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 (X.twistExcludedPlaces_contains_residueChar i (show P ∈ placesOver D.host.E (X.l i) from hl))
  · intro v hv hnc B hB σ hσ
    have hvQ : v ∉ Q := by
      intro hvQ
      by_cases hc : v ∈ ρ.ch i
      · exact hv (mem_half.2 ⟨hvQ, hc⟩)
      · obtain ⟨v', hv'⟩ := GlobalTheory.TwistDet.exists_isConjPl v
        have hv'Q : v' ∈ Q := ramExactly_conj X ψ _ hanti hram v hvQ v' hv'
        have hne := ne_of_split (hsplit v hvQ) hv'
        have hv'c : v' ∈ ρ.ch i := by
          by_contra h
          exact hc (((hρ.ch i).pair v v' hv' hne).2 h)
        exact hnc v' (mem_half.2 ⟨hv'Q, hv'c⟩) (GlobalTheory.TwistDet.isConjPl_symm hv')
    have h1 : ψ σ = 1 := by
      by_contra h
      exact hvQ ((hram v B hB).1 ⟨σ, hσ, h⟩)
    rw [MonoidHom.comp_apply, h1, map_one]

theorem twVia_good : ∀ (D : D7) (c : NChoice D) (w : D.what₂.places.Pl) (ρ : Setup D.ntw), ρ.Good → TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w) → ∀ (j : Fin D.R.m) (ι : KE c w →+* ℂ),
  (twVia ρ ι).Good ∧ (ρ.B (c.twI w) j (c.sd w)).admitted (twVia ρ ι).Q ∧ ∀ τ : ℂ ≃+* ℂ, ConjChar τ (twVia ρ ι) (twVia ρ ((τ : ℂ →+* ℂ).comp ι)) := by
  intro D c w ρ hρ hψ j ι
  obtain ⟨h1, h2⟩ := twistOf_good D D.nd D.ntw ρ hρ (c.twI w) j (c.sd w) (c.k' w) (c.Q w) (chr c w) (viaOk ι) hψ
  refine ⟨h1, h2, fun τ => ⟨rfl, fun x => ?_⟩⟩
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  have hn : D.ntw.l (c.twI w) ^ (c.k' w) ≠ 0 := pow_ne_zero _ (D.ntw.lPrime (c.twI w)).out.ne_zero
  have hp : chr c w σ ^ (D.ntw.l (c.twI w) ^ (c.k' w)) = 1 := by
    obtain ⟨n, hn⟩ := hψ.2.2.2.2.1 σ
    have hz : D.ntw.zk (c.twI w) (c.k' w) ^ (D.ntw.l (c.twI w) ^ (c.k' w)) = 1 :=
      Units.ext (by simpa using (D.ntw.zk_prim (c.twI w) (c.k' w)).pow_eq_one)
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  change ((charOf ρ.rc (viaOk ((τ : ℂ →+* ℂ).comp ι)) (chr c w) x : Circle) : ℂ) =
    τ ((charOf ρ.rc (viaOk ι) (chr c w) x : Circle) : ℂ)
  rw [charOf_eq ρ.rc _ hψ.2.2.1 hσ hn hp, charOf_eq ρ.rc _ hψ.2.2.1 hσ hn hp]
  rfl

end GlobalTheory.PlaceRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientBuiltLocalHypothesisStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_built_local_hypothesis : ∀ (hPr : PrN) (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}, KPx B f → Forced K B T → Start K B f T w → ∀ (x : St P) (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (M : MtFam (withLoc L)) (Tn : NormalizedLocalCompatibility (withLoc L) M) (Q : (withLoc L).what₂.places.Pl → Finset (PlE (withLoc L).host)), HeckeStdTw Tn.B → (∀ i, (withLoc L).nd.Q i = Q ((withLoc L).nd.w i)) → (∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ (withLoc L).R.m) (w' : (withLoc L).what₂.places.Pl), (withLoc L).what₂.muAt w' ≠ (withLoc L).what₂.mu0 → GlobalTheory.CoefDuty.LatInt (withLoc L) M (Q w') j h1 h2 w') → HeckeTied (withLoc L) M → HeckeRational (withLoc L) M → AVTied (withLoc L) M → (∀ i, GlobalTheory.CoefDuty.ClassSum (M.loc i)) → (withLoc L).nd.EigSpan → Rows.IsotInternal (withLoc L).what₂ → SumRepresentations.Conclusion42 (withLoc L) → SumRepresentations.ConclusionZ (withLoc L) → GoodFTAll (withLoc L) → ∀ (j : ℕ) (v : B.places.Pl), 1 ≤ j → j ≤ (Dof x).R.m → ∀ v' : (withLoc L).what₂.places.Pl, HEq v' v → (withLoc L).what₂.etaJ j v' = P.q.eta j v := by
  first | exact @GlobalTheory.etaJ_withLoc_eq_pkg | exact GlobalTheory.etaJ_withLoc_eq_pkg | (intros; apply GlobalTheory.etaJ_withLoc_eq_pkg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateFunctionAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open Formalism.IndefR.Mult Formalism.L2.Pj
open GlobalTheory.HeightCounting.Up (PrN)

theorem GlobalTheory.PlaceRead.evaluates_of_lunif {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : Formalism.L2.Pj.CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (hu : R.LUnif) : fw.Evaluates := by
  intro i σ hσ hV
  refine fw.ev i σ hσ hV ?_
  by_contra hne
  have h0 := fw.ev0 i σ hσ hV hne
  have hx : ∀ x : Fin (R.nW i) → D.what₂.LL, x = 0 := fun x => by
    by_contra hx
    have h1 : LinearIndependent D.what₂.LL (fun _ : Fin 1 => x) := linearIndependent_unique_iff.2 hx
    have h2 := ((hu i σ).1 1 _ h1).ne_zero 0
    rw [h0] at h2
    exact h2 rfl
  refine hne ⟨0, fun f => ?_⟩
  have hf : f = 0 := (fw.e i).injective (Subtype.ext ((hx _).trans (hx _).symm))
  subst hf
  refine Eq.trans ?_ (GlobalTheory.phiC_zero_rule T hV (wtA (κ i))).symm
  rw [LinearMap.zero_apply, map_zero]
  rfl

theorem GlobalTheory.PlaceRead.conj_expansion_evW : PrN → ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ τ : ℂ ≃+* ℂ, (∀ a, τ (embLL0 D a) = embLL0 D a) → ∀ (ζ : ℂ) (Φ Φ' : GA D (Wc D j) → ℂ), ConjFun (X.geo.O j) (X.geo.κ j) τ ζ Φ Φ' →
  ∀ (n : ℕ) (a : Fin n → ℂ) (f : Fin n → NX.FmK S (j.1 + 1)), Φ = ∑ k, a k • evW YS X.geo.v₀ j (f k).val → Φ' = ζ • ∑ k, τ (a k) • evW YS X.geo.v₀ j (f k).val := by
  intro _ D X X0 Y S YS Z c w j _ τ _ ζ Φ Φ' hC n a f hΦ
  have hb := GlobalTheory.IndefiniteRowSideFullHecke.LatticePartsOverBalls.base_of_tie (i := j) X.geo.fw
  have hso : (X.geo.O j).s0 = res X.core (sg0 _ X.A3.A) :=
    (sOv_eq X.core.toCore (X.geo.O j).c' (X.geo.O j).hle).trans hb.1.symm
  have hev := GlobalTheory.PlaceRead.evaluates_of_lunif X.geo.fw X.unif j (sg0 _ X.A3.A) hb.2.1 hb.2.2

  let cf : NX.FmK S ((j : ℕ) + 1) → X.core.cuspA ((j : ℕ) + 1) (wtA (X.geo.κ j)) (X.geo.κ j).n := fun g =>
    (X.geo.fw.e j).symm ⟨(YS.fi j).e g.val, ((YS.fi j).wk _).1 g.2⟩
  have hread : ∀ (g : NX.FmK S ((j : ℕ) + 1)) h,
      (lieFac (X.core.Q.Dw ((j : ℕ) + 1)) (xiR D) (wtA (X.geo.κ j)) : ℂ) *
      (X.geo.O j).phi (X.core.cE ((j : ℕ) + 1) (X.geo.O j).s0) (cf g : X.core.R ((j : ℕ) + 1)) h =
        evW YS X.geo.v₀ j g.val h := by
    intro g h
    rw [phi_cE X.core X.R.toRealDat X.geo.O j]
    refine Eq.trans ?_ ((congrFun (hev (cf g)) h).symm.trans ?_)
    · exact congrFun (GlobalTheory.LiftRatObj.phiC_congr X.core hso (X.geo.O j).hV hb.2.2 _ _) h
    · have he : X.geo.fw.e j (cf g) = ⟨(YS.fi j).e g.val, ((YS.fi j).wk _).1 g.2⟩ := LinearEquiv.apply_symm_apply _ _
      exact congrArg (fun x : (X.R.FW j).WK => (X.R.HW j (sg0 D X.A3.A)).e ((X.R.FW j).j (sg0 D X.A3.A) x.val)
        (X.geo.v₀ j (sg0 D X.A3.A)) h) he
  have h1 : Expands (X.geo.O j) (X.geo.κ j) Φ a fun k => cf (f k) := fun h => by
    rw [hΦ, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    exact congrArg _ (hread _ _).symm
  have h2 := hC.2 n a _ h1
  funext h
  rw [h2 h, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  exact (congrArg (fun z => ζ * τ (a k) * z) (hread (f k) h)).trans (mul_assoc _ _ _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesTwistedThetaSeriesConjugateStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_tuples_twisted_thetaSeries_conjugate : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → IoExt R → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → PhaseTie T R κ v₀ O ph i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → ∃ ζ0 : ℂ, IsRoot1 ζ0 ∧ ∀ t t' : T0, ConjTup R τ t t' → ∃ s : (AE D)ˣ, ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ConjFun (O i) (κ i) τ (ζ0 * ((R.xi t' s : Circle) : ℂ)) (fun g => ph i * ser R i t (R.vP i t) u h (c x) g) (fun g => ph i * ser R i t' (R.vP i t') u h (c x') g) := by
  first | exact @GlobalTheory.ConjTwist.conjFun_ser | exact GlobalTheory.ConjTwist.conjFun_ser | (intros; apply GlobalTheory.ConjTwist.conjFun_ser <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormulaStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localRankinSelberg_logarithm_formula : (∀ (q : ℕ) (A B : Multiset ℂˣ) (s : ℂ), 1 < q → (∀ α ∈ A, ∀ β ∈ B, ‖(α : ℂ) * (β : ℂ)‖ * (q : ℝ) ^ (-s.re) < 1) → ∃ L : ℂ, HasSum (fun r : ℕ => (A.map fun α => (α : ℂ) ^ (r + 1)).sum * (B.map fun β => (β : ℂ) ^ (r + 1)).sum * (q : ℂ) ^ (-(((r : ℂ) + 1) * s)) / ((r : ℂ) + 1)) L ∧ locL q A B s = Complex.exp L) ∧ (∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => ‖((sat σ p.1.1).map fun α => (α : ℂ) ^ (p.2 + 1)).sum * ((sat σ' p.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (p.2 + 1)).sum * (Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * (x : ℂ))) / ((p.2 : ℂ) + 1)‖) ∧ HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (Complex.exp (∑' p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, ((sat σ p.1.1).map fun α => (α : ℂ) ^ (p.2 + 1)).sum * ((sat σ' p.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (p.2 + 1)).sum * (Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * (x : ℂ))) / ((p.2 : ℂ) + 1)))) := by
  first | (exact @GlobalTheory.JSLog.logRankinSelberg) | (exact GlobalTheory.JSLog.logRankinSelberg) | (intros; apply GlobalTheory.JSLog.logRankinSelberg  <;> assumption)
end

