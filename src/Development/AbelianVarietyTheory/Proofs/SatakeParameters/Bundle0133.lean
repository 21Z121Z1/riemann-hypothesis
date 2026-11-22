import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletedLatticeBasisAtPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completedLattice_basis_at_prime : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D), IsIdemAt e P → ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), (∀ z, IntVec z → (fun a => finPart D e * B.mulVec z a) ∈ LamHat V) ∧ ∀ y ∈ LamHat V, ∃ z, IntVec z ∧ (fun a => finPart D e * y a) = fun a => finPart D e * B.mulVec z a := by
  first | exact @GlobalTheory.LatLocBasis.exists_loc_basis | exact GlobalTheory.LatLocBasis.exists_loc_basis | (intros; apply GlobalTheory.LatLocBasis.exists_loc_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKummerFracCoboundaryFullGaloisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerFracCoboundary_full_galois : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l) (b b' : P.R.B), b ≠ 0 →
  (∀ g ∈ GK K, b * P.actQ g b' - P.actQ g b * b' = b * P.actQ g b * ((kummer P g : ℚ_[l]) • P.tB)) →
  ∃ x y : P.R.B, x ≠ 0 ∧ ∀ g : GQ l, x * P.actQ g y - P.actQ g x * y = x * P.actQ g x * ((kummer P g : ℚ_[l]) • P.tB) := by
  first | exact @GlobalTheory.Pst.NoLog.exists_full_frac | exact GlobalTheory.Pst.NoLog.exists_full_frac | (intros; apply GlobalTheory.Pst.NoLog.exists_full_frac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelVectorGoodTypeStableSubspace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.Meet

theorem sum_char_conj_mul {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] {χ : G → K}
    (h : IsAbsIrrChar χ) (y s : G) :
    (∑ g : G, χ (g * y * g⁻¹ * s)) * χ 1 = (Fintype.card G : K) * χ y * χ s := by
  classical
  have hconj := h.conj
  obtain ⟨n, ρ, hi, hρ⟩ := h
  let j := algebraMap K (AlgebraicClosure K)
  have hj : Function.Injective j := j.injective
  set T : Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K) := ∑ g : G, ρ (g * y * g⁻¹) with hTdef
  have hT : ∀ a v, T (ρ a v) = ρ a (T v) := by
    intro a v
    simp only [hTdef, LinearMap.sum_apply, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft a)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  obtain ⟨c, hc⟩ := schur_scalar ρ T hT
  have h1 : ∀ u : G, ∑ g : G, ρ.character (g * y * g⁻¹ * u) = c * ρ.character u := by
    intro u
    have : LinearMap.trace _ _ (T * ρ u) = c * ρ.character u := by
      rw [hc]; simp [Representation.character, Module.End.mul_eq_comp]
    rw [← this, hTdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.character, map_mul]
  have h2 : j ((Fintype.card G : K) * χ y) = c * j (χ 1) := by
    have := h1 1
    simp only [mul_one, hρ, hconj] at this
    rw [← this]
    simp [j]
  have h3 : j (∑ g : G, χ (g * y * g⁻¹ * s)) = c * j (χ s) := by
    have := h1 s
    simp only [hρ] at this
    rw [map_sum, this]
  apply hj
  rw [map_mul, h3, map_mul _ _ (χ s), h2]
  ring

section Op

variable {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
  (σ : K →+* ℂ) (ρ : Representation ℂ G W)

theorem class_sum_apply {χ : G → K} (h : IsAbsIrrChar χ) (h1 : χ 1 ≠ 0) (y : G) (u : W) :
    ∑ g : G, ρ (g * y * g⁻¹) (∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u) =
      σ ((Fintype.card G : K) * χ y / χ 1) • ∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have e1 : ∀ g : G, ρ (g * y * g⁻¹) (∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u) =
      ∑ s : G, σ ((chiIdem χ).coeff ((g * y * g⁻¹)⁻¹ * s)) • ρ s u := by
    intro g
    rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft (g * y * g⁻¹)⁻¹)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  simp only [e1]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_smul, ← map_sum, smul_smul, ← map_mul]
  congr 2
  have e2 : ∀ g : G, (chiIdem χ).coeff ((g * y * g⁻¹)⁻¹ * s) =
      χ 1 / (Fintype.card G : K) * χ (g * y * g⁻¹ * s⁻¹) := by
    intro g
    rw [coeff_chiIdem]
    congr 1
    have := h.conj s (s⁻¹ * (g * y * g⁻¹))
    rw [_root_.mul_inv_rev, inv_inv, ← this]
    congr 1
    group
  simp only [e2]
  rw [← Finset.mul_sum, coeff_chiIdem]
  have := sum_char_conj_mul h y s⁻¹
  field_simp
  linear_combination this

end Op

def lvlCoef {K G : Type} [Field K] [Group G] (P : Subgroup G) (ψ : P →* Kˣ) (h : P) : K :=
  (Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)

open Classical in

theorem coeff_chiIdem_mul_lvlIdem {K G : Type} [Field K] [Group G] [Fintype G] (χ : G → K) (P : Subgroup G)
    (ψ : P →* Kˣ) (t : G) :
    (chiIdem χ * lvlIdem P ψ).coeff t =
      χ 1 / (Fintype.card G : K) * ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹) := by
  classical
  unfold lvlIdem
  rw [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [MonoidAlgebra.coeff_mul_single_apply, coeff_chiIdem]
  simp only [lvlCoef, _root_.mul_inv_rev, inv_inv]
  ring

end GlobalTheory.Hk3.Meet

namespace GlobalTheory.Hk3

open GlobalTheory.Hk3.Meet in

theorem exists_level_vector : ∀ {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : K →+* ℂ) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) (ρ : Representation ℂ G W)
    (U : Submodule ℂ W), (∀ χ ∈ X, IsAbsIrrChar χ) → (∀ χ ∈ X, chiIdem χ * lvlIdem P ψ ≠ 0) → (∀ g, U.map (ρ g) ≤ U) →
    U ≠ ⊥ → (∀ u ∈ U, ∑ g, σ ((idemOf X).coeff g) • ρ g u = u) →
    ∃ u ∈ U, u ≠ 0 ∧ ∀ p : P, ρ p u = σ (ψ p : K) • u := by
  intro K G W _ _ _ _ _ _ _ σ X P ψ ρ U hX hne hst hbot hid
  classical
  have hmem : ∀ g, ∀ u ∈ U, ρ g u ∈ U := fun g u hu => hst g (Submodule.mem_map_of_mem hu)

  obtain ⟨u₀, hu₀, hu₀ne⟩ := (Submodule.ne_bot_iff U).1 hbot
  have hsplit : ∑ χ ∈ X, ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ = u₀ := by
    refine Eq.trans ?_ (hid u₀ hu₀)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : (idemOf X).coeff g = ∑ φ ∈ X, (chiIdem φ).coeff g := by
      unfold idemOf
      simp
    rw [← Finset.sum_smul, ← map_sum, e]
  obtain ⟨χ, hχ, hw⟩ : ∃ χ ∈ X, ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu₀ne (by rw [← hsplit]; exact Finset.sum_eq_zero hcon)
  set w₀ := ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ with hw₀
  have hw₀U : w₀ ∈ U := Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hmem g _ hu₀)

  obtain ⟨t, ht⟩ : ∃ t, (chiIdem χ * lvlIdem P ψ).coeff t ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne χ hχ (by
      apply MonoidAlgebra.ext
      ext t
      simpa using hcon t)
  rw [coeff_chiIdem_mul_lvlIdem] at ht
  have h1 : χ 1 ≠ 0 := fun e => ht (by simp [e])
  have hc : ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹) ≠ 0 := right_ne_zero_of_mul ht
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

  set L : W → W := fun w => ∑ h : P, σ (lvlCoef P ψ h) • ρ (h : G) w with hL
  have hLU : ∀ w ∈ U, L w ∈ U := fun w hw => Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (hmem _ _ hw)
  have hLe : ∀ (p : P) w, ρ p (L w) = σ (ψ p : K) • L w := by
    intro p w
    simp only [hL, map_sum, map_smul, Finset.smul_sum]
    refine (Equiv.sum_comp (Equiv.mulLeft p⁻¹) _).symm.trans (Finset.sum_congr rfl fun h _ => ?_)
    simp only [Equiv.coe_mulLeft]
    have e1 : lvlCoef P ψ (p⁻¹ * h) = (ψ p : K) * lvlCoef P ψ h := by
      simp only [lvlCoef, _root_.mul_inv_rev, inv_inv, map_mul, Units.val_mul]
      ring
    have e2 : ρ (p : G) (ρ ((p⁻¹ * h : P) : G) w) = ρ (h : G) w := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [e1, e2, map_mul, mul_smul]
  by_contra hno
  push_neg at hno
  have hL0 : ∀ w ∈ U, L w = 0 := by
    intro w hw
    by_contra hLw
    obtain ⟨p, hp⟩ := hno _ (hLU w hw) hLw
    exact hp (hLe p w)
  have hz : ∑ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) = 0 :=
    Finset.sum_eq_zero fun g _ => by rw [hL0 _ (hmem _ _ hw₀U), map_zero]
  have hz2 : ∑ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) =
      σ ((Fintype.card G : K) / χ 1 * ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹)) • w₀ := by
    have e : ∀ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) =
        ∑ h : P, σ (lvlCoef P ψ h) • ρ (g * ((h : G) * t⁻¹) * g⁻¹) w₀ := by
      intro g
      simp only [hL, map_sum, map_smul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← Module.End.mul_apply (ρ (h : G)), ← map_mul, ← Module.End.mul_apply (ρ g), ← map_mul]
      simp [mul_assoc]
    simp only [e]
    rw [Finset.sum_comm]
    have e2 : ∀ h : P, ∑ g : G, σ (lvlCoef P ψ h) • ρ (g * ((h : G) * t⁻¹) * g⁻¹) w₀ =
        σ (lvlCoef P ψ h * ((Fintype.card G : K) * χ ((h : G) * t⁻¹) / χ 1)) • w₀ := by
      intro h
      rw [← Finset.smul_sum, map_mul, mul_smul]
      congr 1
      exact class_sum_apply σ ρ (hX χ hχ) h1 _ u₀
    simp only [e2]
    rw [← Finset.sum_smul, ← map_sum, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  rw [hz2] at hz
  rcases smul_eq_zero.1 hz with h0 | h0
  · exact (mul_ne_zero (div_ne_zero hN h1) hc) ((map_eq_zero σ).1 h0)
  · exact hw h0

end GlobalTheory.Hk3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus : ∀ (l : ℕ) [Fact l.Prime] (w : Per.AinfP l), w ∈ Per.kerP l → ∃ u : Per.BdRp l, IsLogP w u := by
  first | exact @GlobalTheory.Pst.LogExist.exists_isLogP | exact GlobalTheory.Pst.LogExist.exists_isLogP | (intros; apply GlobalTheory.Pst.LogExist.exists_isLogP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryRepR
section
open MeasureTheory

noncomputable section

namespace GlobalTheory.AutomorphicL2Unitary

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

def Riso (g : G) : L2 Γ μ ≃ₗᵢ[ℂ] L2 Γ μ where
  toLinearEquiv := LinearEquiv.ofLinear (R Γ μ g).toLinearMap (R Γ μ g⁻¹).toLinearMap
    (by ext F; simp [← ContinuousLinearMap.mul_apply, ← map_mul])
    (by ext F; simp [← ContinuousLinearMap.mul_apply, ← map_mul])
  norm_map' := norm_R g

@[simp] theorem Riso_apply (g : G) (F : L2 Γ μ) : Riso Γ μ g F = R Γ μ g F := rfl

def Rhom : G →* (L2 Γ μ ≃ₗᵢ[ℂ] L2 Γ μ) where
  toFun := Riso Γ μ
  map_one' := LinearIsometryEquiv.ext fun F => by simp
  map_mul' g h := LinearIsometryEquiv.ext fun F => by
    show R Γ μ (g * h) F = R Γ μ g (R Γ μ h F)
    rw [map_mul]; rfl

def Rurep : GroundTheory.Automorphic.UnitaryRep G (L2 Γ μ) :=
  GroundTheory.Automorphic.UnitaryRep.ofLinearIsometryEquiv (Rhom Γ μ) fun F => continuous_R F

end GlobalTheory.AutomorphicL2Unitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FilPEqSpanBetaDPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filP_eq_span_betaD_pow_of_kerP_eq_span_beta : ∀ (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  ∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n} := by
  first | exact @GlobalTheory.Pst.StLat.filtration_eq_span_pow | exact GlobalTheory.Pst.StLat.filtration_eq_span_pow | (intros; apply GlobalTheory.Pst.StLat.filtration_eq_span_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisLogTeichmullerRatioEqAddKummerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (Co : Core l), Co.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
  (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ u : Per.BdRp l, IsLogP (beta ϖ) u → ∀ g : GQ l,
    Per.σDp g u = u + Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t) := by
  first | exact @GlobalTheory.Pst.StLat.gal_log | exact GlobalTheory.Pst.StLat.gal_log | (intros; apply GlobalTheory.Pst.StLat.gal_log <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem conv_map_idem {K : Type} [Field K] {H : Type} [Group H] [Fintype H] (z : MonoidAlgebra K H) (hz : z * z = z)
    (σ : K →+* ℂ) (g : H) : ∑ a, σ (z.coeff a) * σ (z.coeff (a⁻¹ * g)) = σ (z.coeff g) := by
  conv_rhs => rw [← hz]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp [map_mul]

theorem coeff_conj_central {K : Type} [Field K] {H : Type} [Group H] (z : MonoidAlgebra K H)
    (hz : ∀ b, b * z = z * b) (g h : H) : z.coeff (g * h * g⁻¹) = z.coeff h := by
  have e := congrArg (fun y : MonoidAlgebra K H => y.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simpa [mul_assoc] using e.symm

theorem sum_rep_idem {H : Type} [Group H] [Fintype H] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H Y) (c : H → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) :
    (∑ g, c g • ρ g) * (∑ g, c g • ρ g) = ∑ g, c g • ρ g := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, smul_mul_smul_comm, ← map_mul]
  calc ∑ a, ∑ b, (c a * c b) • ρ (a * b) = ∑ a, ∑ g, (c a * c (a⁻¹ * g)) • ρ g := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun b => by simp
    _ = ∑ g, (∑ a, c a * c (a⁻¹ * g)) • ρ g := by
        rw [Finset.sum_comm]; simp_rw [Finset.sum_smul]
    _ = ∑ g, c g • ρ g := by simp_rw [hc]

theorem sum_rep_comm {H : Type} [Group H] [Fintype H] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H Y) (c : H → ℂ) (hc : ∀ g h, c (g * h * g⁻¹) = c h) (g : H) :
    Commute (∑ h, c h • ρ h) (ρ g) := by
  unfold Commute SemiconjBy
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
  symm
  refine Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hc]
  congr 2
  group

theorem eH_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i, eH R i * eH R i = eH R i ∧ (∀ g, Commute (eH R i) (R.gW i (sg0 D A) g)) ∧ (∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv) ∧ ∀ t y, eH R i (R.thG i t y) = R.thG i t y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hX i
  have hc : ∀ g, ∑ a, RealDat.eC (A := A) (sg0 D A) a * RealDat.eC (A := A) (sg0 D A) (a⁻¹ * g) =
      RealDat.eC (A := A) (sg0 D A) g := fun g => conv_map_idem _ (idemOf_mul_self A.X hX) (sg0 D A) g
  have hcc : ∀ g h, RealDat.eC (A := A) (sg0 D A) (g * h * g⁻¹) = RealDat.eC (A := A) (sg0 D A) h := fun g h => by
    unfold RealDat.eC
    rw [coeff_conj_central _ (fun b => idemOf_central A.X hX b) g h]
  have happ : ∀ x v, (R.HW i (sg0 D A)).e (eH R i x) v = R.eWf i (sg0 D A) ((R.HW i (sg0 D A)).e x v) := fun x v => by
    unfold eH RealDat.eWf gaL
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, MultilinearMap.sum_apply,
      MultilinearMap.smul_apply]
    refine Finset.sum_congr rfl fun g _ => congrArg _ ?_
    rw [hC.models.gW i (sg0 D A) g x]; rfl
  have hinj := (hC.models.HW i (sg0 D A)).1
  have hrange := (hC.models.HW i (sg0 D A)).2.1
  have hfix : ∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv := fun x => by
    rw [RealDat.Wat, mem_goodPart]
    constructor
    · intro h
      refine ⟨?_, fun v => ?_⟩
      · have : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := hrange ▸ LinearMap.mem_range_self _ x
        exact this
      · rw [← happ, h]
    · rintro ⟨_, h⟩
      apply hinj
      refine MultilinearMap.ext fun v => ?_
      rw [happ, h]
  have hI : eH R i * eH R i = eH R i := sum_rep_idem _ _ hc
  refine ⟨hI, fun g => sum_rep_comm _ _ hcc g, hfix, fun t y => ?_⟩
  have hm := hC.thP.thF_mem i t y
  rw [← hrange] at hm
  obtain ⟨x0, hx0⟩ := hm
  have e1 : R.thG i t y = eH R i x0 := by
    apply hinj
    rw [hC.thP.thG i t y, ← hx0]
    refine MultilinearMap.ext fun v => ?_
    rw [happ]
    exact (postOn_apply _ _ _ _).symm
  rw [e1, ← Module.End.mul_apply, hI]

end GlobalTheory.Hk3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

variable {D : D7}

theorem symplO_half_off (S T : HSp D) {a : AE D} {x u : WO S T} (hx : IsHalf a x) (hu : ∀ i j, cA D a * u i j = 0) :
    symplO S T x u = 0 := by
  have h0 : cA D a • u = 0 := Matrix.ext fun i j => by
    show cA D a * u i j = 0
    exact hu i j
  rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx, GlobalTheory.SplitScalar.symplO_smul, h0, GlobalTheory.SplitScalar.symplO_zero_right]

theorem heisO_comm_off (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {a : AE D} {x u : WO S T} (hx : IsHalf a x)
    (hu : ∀ i j, cA D a * u i j = 0) (g : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T x g) = heisO ψ S T x (heisO ψ S T u g) := by
  rw [GlobalTheory.SplitScalar.heisO_comm, GlobalTheory.SplitScalar.symplO_skew, symplO_half_off S T hx hu, neg_zero,
    AddChar.map_zero_eq_one, one_smul]

theorem heisO_fix_thetaAt_off : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T))
    (c : ℂ) (f₀ Φ f : WO S T → ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → ∀ u : WO S T,
    (∀ i j, e * u i j = 0 ∧ cA D e * u i j = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u f = f := by
  intro D ψ S T e Λ c f₀ Φ f h u hu hf₀
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := h
  have hm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ ((GlobalTheory.SplitScalar.heisL ψ S T u).comp Tm) :=
    { trans := fun Φ' hΦ' x hx => by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.trans Φ' hΦ' x hx, heisO_comm_off ψ S T hx (fun i j => (hu i j).2)]
      modul := fun Φ' hΦ' y hy => by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.modul Φ' hΦ' y hy,
          heisO_comm_off ψ S T hy (fun i j => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact (hu i j).1)]
      vac := by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.vac, hf₀] }
  have h1 := hall _ hm
  have h2 := hall _ hTm
  simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply] at h1
  rw [h2] at h1 ⊢
  exact h1.symm

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapOfAlgebraMaximalRealSubfieldInjective
section
open NumberField HeckeCharacterZeroLocus.ThmBIn GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.UnitaryHeckeBaseChange

namespace GlobalTheory.IdeleMapInjective

theorem adeleMap_injective {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Function.Injective (adeleMap F E) := by
  intro a b hab
  rw [← toAdele_algebraMap, ← toAdele_algebraMap] at hab
  exact Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E)
    (algebraMap F E).injective ((bijective_toAdele h).1 hab)

theorem ideleMap_injective (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E) := by
  have h : IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  intro a b hab
  exact Units.ext (adeleMap_injective h (congrArg Units.val hab))

end GlobalTheory.IdeleMapInjective
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLineStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_stable_line' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l),
  (∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB) → GlobalTheory.RegularRing.LineUnit (P.PD K) →
  ∀ b : Bst P, b ≠ 0 → (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b := by
  first | exact @GlobalTheory.Pst.StLine.isUnit_of_stable_line | exact GlobalTheory.Pst.StLine.isUnit_of_stable_line | (intros; apply GlobalTheory.Pst.StLine.isUnit_of_stable_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerPEqSpanBetaStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} := by
  first | exact @GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta | exact GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta | (intros; apply GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta <;> assumption)
end

