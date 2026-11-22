import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalRingOfVarietyPointLocalizationPlaceTensor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GraphLocal

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

theorem exists_mul_mem_tens (E : Place (algebraMap ℂ K)) (w : K ⊗[ℂ] κ') :
    ∃ d ∈ E.ring, d ≠ 0 ∧ (d ⊗ₜ[ℂ] (1 : κ')) * w ∈ tens (κ' := κ') (placeAlg E) := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, one_ne_zero, by simpa using zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha, b, hb, hb0, e⟩ := E.isLocModel.frac x
    refine ⟨b, hb, hb0, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, e]
    exact tmul_mem ha y
  | add u v hu hv =>
    obtain ⟨d₁, hd₁, hd₁0, h₁⟩ := hu
    obtain ⟨d₂, hd₂, hd₂0, h₂⟩ := hv
    refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, mul_ne_zero hd₁0 hd₂0, ?_⟩
    have e : ((d₁ * d₂) ⊗ₜ[ℂ] (1 : κ')) * (u + v) =
        (d₂ ⊗ₜ[ℂ] (1 : κ')) * ((d₁ ⊗ₜ[ℂ] (1 : κ')) * u) +
          (d₁ ⊗ₜ[ℂ] (1 : κ')) * ((d₂ ⊗ₜ[ℂ] (1 : κ')) * v) := by
      rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm d₂ d₁, mul_add]
    rw [e]
    exact add_mem (mul_mem (tmul_mem hd₂ 1) h₁) (mul_mem (tmul_mem hd₁ 1) h₂)

theorem isLocModel_locAt : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K] [Algebra ℂ κ'] [Algebra ℂ L]
    [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (E : Place (algebraMap ℂ K)) (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  (∃ O' : Subring κ', IsLocModel (algebraMap ℂ κ') O') →
  IsLocModel (algebraMap ℂ L) (locAt (L := L) 𝔭) := by
  intro K κ' L _ _ _ _ _ _ _ _ _ E 𝔭 _ hO
  obtain ⟨O', hO'⟩ := hO
  have hinj : Function.Injective (algebraMap (K ⊗[ℂ] κ') L) := IsFractionRing.injective _ L
  have hc : ∀ a : ℂ, algebraMap ℂ L a ∈ locAt (L := L) 𝔭 := fun a => by
    rw [IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L]
    exact (toQ (L := L) 𝔭 (algebraMap ℂ (tens (κ' := κ') (placeAlg E)) a)).2
  refine
    { const_mem := hc
      isLocalRing := isLocalRing_locAt 𝔭 hinj
      essFiniteType := ?_
      frac := ?_ }
  · have e : (algebraMap ℂ L).codRestrict (locAt (L := L) 𝔭) hc =
        (toQ (L := L) 𝔭).comp (algebraMap ℂ (tens (κ' := κ') (placeAlg E))) := by
      ext a
      simp only [RingHom.codRestrict_apply, RingHom.comp_apply, coe_toQ]
      exact IsScalarTower.algebraMap_apply ℂ (K ⊗[ℂ] κ') L a
    rw [e]

    letI : Algebra ℂ O' := ((algebraMap ℂ κ').codRestrict O' hO'.const_mem).toAlgebra
    haveI : IsScalarTower ℂ O' κ' := IsScalarTower.of_algebraMap_eq' rfl
    haveI : Algebra.EssFiniteType ℂ O' := hO'.essFiniteType
    haveI : IsFractionRing O' κ' := IsFractionRing.of_field O' κ' fun f => by
      obtain ⟨a, ha, b, hb, hb0, e⟩ := hO'.frac f
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, (eq_div_iff hb0).2 e⟩
    haveI : Algebra.EssFiniteType O' κ' :=
      Algebra.EssFiniteType.of_isLocalization κ' (nonZeroDivisors O')
    haveI : Algebra.EssFiniteType ℂ κ' := Algebra.EssFiniteType.comp ℂ O' κ'

    haveI : Algebra.EssFiniteType ℂ (placeAlg E) := by
      let φ : E.ring →+* placeAlg E :=
        { toFun := fun x => ⟨x.1, x.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hφ : φ.FiniteType := RingHom.FiniteType.of_surjective φ fun y => ⟨⟨y.1, y.2⟩, rfl⟩
      have e : φ.comp ((algebraMap ℂ K).codRestrict E.ring E.const_mem) =
          algebraMap ℂ (placeAlg E) := RingHom.ext fun _ => rfl
      have h := RingHom.EssFiniteType.comp E.essFiniteType hφ.essFiniteType
      rw [e] at h
      exact RingHom.essFiniteType_algebraMap.1 h
    haveI : Algebra.EssFiniteType (placeAlg E) (placeAlg E ⊗[ℂ] κ') :=
      Algebra.EssFiniteType.baseChange ℂ κ' (placeAlg E)
    haveI : Algebra.EssFiniteType ℂ (placeAlg E ⊗[ℂ] κ') :=
      Algebra.EssFiniteType.comp ℂ (placeAlg E) (placeAlg E ⊗[ℂ] κ')
    haveI : Algebra.EssFiniteType ℂ (tens (κ' := κ') (placeAlg E)) :=
      Algebra.EssFiniteType.of_surjective (tensEquiv (κ' := κ') (placeAlg E)).toAlgHom
        (tensEquiv (κ' := κ') (placeAlg E)).surjective
    have h1 : (algebraMap ℂ (tens (κ' := κ') (placeAlg E))).EssFiniteType :=
      RingHom.essFiniteType_algebraMap.2 inferInstance

    letI : Algebra (tens (κ' := κ') (placeAlg E)) (locAt (L := L) 𝔭) := (toQ (L := L) 𝔭).toAlgebra
    haveI : IsLocalization 𝔭.primeCompl (locAt (L := L) 𝔭) :=
      { map_units := fun s => isUnit_toQ 𝔭 hinj s.2
        surj := fun x => by
          obtain ⟨a, s, hs, hx⟩ := exists_mul_toQ 𝔭 x
          exact ⟨(a, ⟨s, hs⟩), hx⟩
        exists_of_eq := fun {x y} h => ⟨1, by
          simp only [OneMemClass.coe_one, one_mul]
          exact Subtype.ext (hinj (congrArg Subtype.val h))⟩ }
    haveI : Algebra.EssFiniteType (tens (κ' := κ') (placeAlg E)) (locAt (L := L) 𝔭) :=
      Algebra.EssFiniteType.of_isLocalization (locAt (L := L) 𝔭) 𝔭.primeCompl
    have h2 : (toQ (L := L) 𝔭).EssFiniteType := RingHom.essFiniteType_algebraMap.2 this
    exact RingHom.EssFiniteType.comp h1 h2
  · intro f
    obtain ⟨u, v, hv, rfl⟩ := IsFractionRing.div_surjective (A := K ⊗[ℂ] κ') f
    have hv0 : algebraMap (K ⊗[ℂ] κ') L v ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hv
    obtain ⟨d₁, hd₁, hd₁0, h₁⟩ := exists_mul_mem_tens (κ' := κ') E u
    obtain ⟨d₂, hd₂, hd₂0, h₂⟩ := exists_mul_mem_tens (κ' := κ') E v
    set D : K ⊗[ℂ] κ' := (d₁ * d₂) ⊗ₜ[ℂ] (1 : κ') with hD
    have hD1 : D = (d₂ ⊗ₜ[ℂ] (1 : κ')) * (d₁ ⊗ₜ[ℂ] (1 : κ')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm d₂ d₁]
    have hD2 : D = (d₁ ⊗ₜ[ℂ] (1 : κ')) * (d₂ ⊗ₜ[ℂ] (1 : κ')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hu : D * u ∈ tens (κ' := κ') (placeAlg E) := by
      rw [hD1, mul_assoc]; exact mul_mem (tmul_mem hd₂ 1) h₁
    have hv' : D * v ∈ tens (κ' := κ') (placeAlg E) := by
      rw [hD2, mul_assoc]; exact mul_mem (tmul_mem hd₁ 1) h₂
    have hDu : IsUnit D := by
      refine IsUnit.of_mul_eq_one ((d₁ * d₂)⁻¹ ⊗ₜ[ℂ] (1 : κ')) ?_
      rw [hD, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        mul_inv_cancel₀ (mul_ne_zero hd₁0 hd₂0)]
      rfl
    have hD0 : algebraMap (K ⊗[ℂ] κ') L D ≠ 0 := (hDu.map _).ne_zero
    refine ⟨_, (toQ (L := L) 𝔭 ⟨D * u, hu⟩).2, _, (toQ (L := L) 𝔭 ⟨D * v, hv'⟩).2, ?_, ?_⟩
    · show algebraMap (K ⊗[ℂ] κ') L (D * v) ≠ 0
      rw [map_mul]; exact mul_ne_zero hD0 hv0
    · show _ * algebraMap (K ⊗[ℂ] κ') L (D * v) = algebraMap (K ⊗[ℂ] κ') L (D * u)
      rw [map_mul, map_mul]
      field_simp

end GlobalTheory.GraphLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem divOver_ord_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (f : X.functionFieldˣ) (r : ℤ) : E.ord (f ^ r) = r * E.ord f := by
  rcases Int.eq_nat_or_neg r with ⟨s, rfl | rfl⟩
  · rw [zpow_natCast, E.ord_pow]
  · rw [zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]
    ring

theorem isLogEqn_add_smul : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ D : X → ℚ) (η : RatForms p n) (x : X) (m m' : ℕ) (g f : X.functionFieldˣ) (c : ℚ), 0 < m → 0 < m' → IsLogEqn p Γ η x m g → (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m') → ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + c • D) η x m'' g'' ∧ ∀ E : DivOver p, discrep E η m'' g'' = discrep E η m g - c * ((E.ord f : ℚ) / m') := by
  intro X _ _ p n Γ D η x m m' g f c hm hm' hg hD
  have hb : 0 < c.den := c.den_pos
  have hc : c * (c.den : ℚ) = c.num := Rat.mul_den_eq_num c
  have h₁ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h₂ : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have h₃ : (c.den : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  refine ⟨m * m' * c.den, g ^ (m' * c.den) * f ^ (c.num * m), Nat.mul_pos (Nat.mul_pos hm hm') hb,
    fun z hz E hE => ?_, fun E => ?_⟩
  · have e₁ := hg z hz E hE
    have e₂ := hD z hz E hE
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [E.ord_mul, E.ord_pow, divOver_ord_zpow, e₂]
    push_cast
    rw [← e₁]
    field_simp
    linear_combination (E.ord f : ℚ) * hc
  · simp only [discrep]
    rw [E.ord_mul, E.ord_pow, divOver_ord_zpow]
    push_cast
    field_simp
    linear_combination ((m : ℚ) * (E.ord f : ℚ)) * hc

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalMultipleAddQWeil
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory

theorem isLogCanonicalMultiple_add_qWeil : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Δ : X → ℚ) (m m' : ℕ) (G D₀ : CartierDiv X), 0 < m → 0 < m' → IsLogCanonicalMultiple p n Δ m G → IsLogCanonicalMultiple p n (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) := by
  intro X _ _ p n Δ m m' G D₀ hm hm' hG
  obtain ⟨η, hη, hG⟩ := hG
  refine ⟨η, hη, fun x g hg z hz E hE => ?_⟩
  obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
  obtain ⟨a, ha⟩ := G.exists_isEqn z
  obtain ⟨d, hd⟩ := D₀.exists_isEqn z
  have h3 := ((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans
    ((ha.nsmul m').add (hd.nsmul m)).mult_eq)
  rw [← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow, E.ord_pow] at h3
  have h4 := hG z a ha z specializes_rfl E hE
  have hd' := hd.mult_eq
  rw [← hE.ord_eq] at hd'
  have h1 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have h2 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  rw [Pi.add_apply, qWeil, hd', h3]
  push_cast
  rw [← h4]
  field_simp
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogEqnAddSmulIffOfOff
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]

theorem isLogEqn_add_smul_iff_of_off {p : X ⟶ Sp k} {n : ℕ} {Γ B : X → ℚ} (c : ℚ) {x : X}
    (hB : Off B x) (η : RatForms p n) (m : ℕ) (g : X.functionFieldˣ) :
    IsLogEqn p (Γ + c • B) η x m g ↔ IsLogEqn p Γ η x m g := by
  refine forall_congr' fun z => forall_congr' fun hz => ?_
  have : (Γ + c • B) z = Γ z := by simp [hB z hz]
  rw [this]

theorem off_add_smul (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ)
    (n : ℕ) (Γ B : X → ℚ) (c : ℚ) (x : X) (hB : Off B x) :
    (KltAt p n (Γ + c • B) x ↔ KltAt p n Γ x) ∧ (LcAt p n (Γ + c • B) x ↔ LcAt p n Γ x) ∧
      (IsNkltCentre p n (Γ + c • B) x ↔ IsNkltCentre p n Γ x) ∧ ∀ z, z ⤳ x → Off B z := by
  have e := isLogEqn_add_smul_iff_of_off (p := p) (n := n) (Γ := Γ) c hB
  refine ⟨?_, ?_, ?_, fun z hz w hw => hB w (hw.trans hz)⟩
  · unfold KltAt
    simp only [e]
  · unfold LcAt
    simp only [e]
  · unfold IsNkltCentre
    simp only [e]

end GlobalTheory.PairStep

example : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ B : X → ℚ) (c : ℚ) (x : X), Off B x → (KltAt p n (Γ + c • B) x ↔ KltAt p n Γ x) ∧ (LcAt p n (Γ + c • B) x ↔ LcAt p n Γ x) ∧ (IsNkltCentre p n (Γ + c • B) x ↔ IsNkltCentre p n Γ x) ∧ ∀ z, z ⤳ x → Off B z :=
  fun X _ _ p n Γ B c x hB => GlobalTheory.PairStep.off_add_smul X p n Γ B c x hB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPsEffPullReducedClosedOfDimLe
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem IsNef.isPsEff_pull_red_of_dim_le (k : Type) [Field k] [Infinite k] (d : ℕ)
    (H : ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) →
      topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N →
        IsAmpleLB (CechPic.tens A N))
    (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (hX : IsProjOver (strHom k X)) (M : LB X)
    (hM : IsNef k M) (Z : Closeds X) (hZ : IsIrreducible (Z : Set X))
    (hd : topologicalKrullDim (Z : Set X) ≤ (d : ℕ)) : IsPsEff (M.pull (redι Z)) := by
  letI := algebraΓAlong k (redι Z)
  have := isIntegral_red hZ
  obtain ⟨B, hB⟩ := exists_isAmpleLB_of_isProjOver hX
  have : IsProper (strHom k X) := by
    obtain ⟨N, i, hi, e⟩ := hX
    have := isProper_str k N
    rw [← e]
    infer_instance
  have hA := hB.pull_of_isClosedImmersion (redι Z)
  have : IsProper (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom (appTop_algebraMap_along k (redι Z))]
    infer_instance
  have hN := hM.pull_of_isClosedImmersion (redι Z) (appTop_algebraMap_along k (redι Z))
  refine ⟨hN.isLB, _, hA, fun m _ => ?_⟩
  have hP := H _ (hA.isProjOver _) ((topologicalKrullDim_red Z).trans_le hd) _ _ hA (hN.pow hA m)
  obtain ⟨r, hr, hg⟩ := hP.exists_isGenerated_pow
  refine ⟨r, hr, hg.hasNonzeroSec.of_cls_eq
    (isLB_lbPow (isLB_tens (isLB_lbPow hN.isLB m) hA.isLB) r) hg.isLB ?_⟩
  rw [cls_lbPow (isLB_tens (isLB_lbPow hN.isLB m) hA.isLB), cls_lbPow hP.isLB,
    cls_tens (isLB_lbPow hN.isLB m) hA.isLB, cls_tens hA.isLB (isLB_lbPow hN.isLB m), add_comm]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPseudoEffectiveReducedUnivOfSectionPow
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

namespace GlobalTheory

theorem isPsEff_pull_redι_univ_of_hasNonzeroSec_pow :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (M : LB X), M.IsLB → ∀ r : ℕ, 1 ≤ r → HasNonzeroSec (lbPow M r) → ∀ Z : Closeds X, (Z : Set X) = Set.univ → IsPsEff (M.pull (redι Z)) := by
  intro k _ _ X _ _ hp M hM r hr hs Z hZ
  have hirr : IsIrreducible (Z : Set X) := hZ ▸ IrreducibleSpace.isIrreducible_univ X
  have := isIntegral_red hirr
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨s, hs⟩ := hasNonzeroSec_iff.1 hs
  obtain ⟨x, hx⟩ := (range_redι Z).ge (hZ.ge (Set.mem_univ (genericPoint X)))
  rw [← hx] at hs
  have e := nonzeroLocus_secPull s (redι Z)
  have h1 : HasNonzeroSec ((lbPow M r).pull (redι Z)) :=
    ⟨secPull s (redι Z), sec_ne_zero_of_mem (x := x) (e.ge hs)⟩
  have hM' := LB.isLB_pull hM (redι Z)
  refine isPsEff_of_hasNonzeroSec_pow (hH.pull_of_isClosedImmersion (redι Z)) hM' hr
    (h1.of_cls_eq (isLB_lbPow hM' r) (LB.isLB_pull (isLB_lbPow hM r) _) ?_)
  rw [cls_lbPow hM', cls_pull hM, cls_pull (isLB_lbPow hM r), cls_lbPow hM, map_nsmul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCColumnLatticeOfOrthonormalFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDualC_columnLattice_of_orthonormalFrame : ∀ {D : D7} (S : HSp D) (B : GL (Fin S.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → IsSelfDualC S (colLat B) := by
  first | exact @GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal | exact GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal | (intros; apply GlobalTheory.FunObj.OrthoFrame.isSelfDualC_colLat_of_orthonormal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBalls
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.BallFam

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {y : CxPts p σ} {f g : X.functionField}

theorem ratVal_sub (hf : RegAt (under y) f) (hg : RegAt (under y) g) :
    ratVal (f - g) y = ratVal f y - ratVal g y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  obtain ⟨W, hW, b, rfl⟩ := hg.exists_fnOf
  have hy : y ∈ ptsIn p σ (U ⊓ W) := mem_ptsIn.2 ⟨hU, hW⟩
  rw [← fnOf_resG (inf_le_left : U ⊓ W ≤ U) (gen_mem (memInf hU hW)),
    ← fnOf_resG (inf_le_right : U ⊓ W ≤ W) (gen_mem (memInf hU hW)), ← map_sub,
    ratVal_fnOf hy, ratVal_fnOf hy, ratVal_fnOf hy, ev_eq hy, ev_eq hy, ev_eq hy, map_sub]

theorem ratVal_zero : ratVal (0 : X.functionField) y = 0 := by
  have h0 : RegAt (under y) (0 : X.functionField) := ⟨0, map_zero _⟩
  simpa using ratVal_sub h0 h0

theorem ratVal_nsmul (hf : RegAt (under y) f) (n : ℕ) : ratVal (n • f) y = n • ratVal f y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hy : y ∈ ptsIn p σ U := mem_ptsIn.2 hU
  rw [← map_nsmul, ratVal_fnOf hy, ratVal_fnOf hy, ev_eq hy, ev_eq hy, map_nsmul]

namespace Pair

variable (P : Pair p) (a b : ℤ)

theorem regAt_loc {f : X.functionField} (hf : f ∈ P.H a b) (σ : k →+* ℂ) (y : CxPts p σ) :
    RegAt (under y) (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) :=
  hf _ _ _ (mem_ptsIn.1 (mem_pick _ y)) (mem_ptsIn.1 (mem_pick _ y))

theorem loc_sub (f g : X.functionField) (i j) : P.loc a b (f - g) i j = P.loc a b f i j - P.loc a b g i j := by
  simp only [VolBr.Pair.loc]; ring

theorem loc_nsmul (n : ℕ) (f : X.functionField) (i j) : P.loc a b (n • f) i j = n • P.loc a b f i j := by
  simp only [VolBr.Pair.loc, nsmul_eq_mul]; ring

theorem nu_zero (σ : k →+* ℂ) (y : CxPts p σ) : P.nu a b σ y 0 = 0 := by
  simp only [VolBr.Pair.nu, VolBr.Pair.loc, zero_mul, ratVal_zero, norm_zero]

theorem nu_sub {f g : X.functionField} (hf : f ∈ P.H a b) (hg : g ∈ P.H a b) (σ : k →+* ℂ) (y : CxPts p σ) :
    P.nu a b σ (y) (f - g) ≤ P.nu a b σ y f + P.nu a b σ y g := by
  simp only [VolBr.Pair.nu]
  rw [loc_sub, ratVal_sub (regAt_loc P a b hf σ y) (regAt_loc P a b hg σ y), ← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le

theorem nu_nsmul {f : X.functionField} (hf : f ∈ P.H a b) (n : ℕ) (σ : k →+* ℂ) (y : CxPts p σ) :
    P.nu a b σ y (n • f) = n * P.nu a b σ y f := by
  simp only [VolBr.Pair.nu]
  rw [loc_nsmul, ratVal_nsmul (regAt_loc P a b hf σ y), nsmul_eq_mul, norm_mul, Complex.norm_natCast, mul_assoc]

end Pair

end GlobalTheory.VolBr.BallFam

open GlobalTheory.VolBr.BallFam in

theorem GlobalTheory.VolBr.Pair.isBallFam : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ a b : ℤ, IsBallFam (P.H a b) (P.Bl a b) := by
  intro k _ X _ p P a b
  exact {
    subset := fun r f hf => hf.1
    zero_mem := fun r hr => ⟨zero_mem _, fun σ y => by rw [Pair.nu_zero]; exact hr⟩
    sub_mem := fun r r' f g hf hg => ⟨sub_mem hf.1 hg.1, fun σ y =>
      (Pair.nu_sub P a b hf.1 hg.1 σ y).trans (add_le_add (hf.2 σ y) (hg.2 σ y))⟩
    nsmul_iff := fun n r f hn hf => by
      have h0 : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [VolBr.Pair.Bl, Set.mem_setOf_eq, Pair.nu_nsmul P a b hf, mul_le_mul_iff_right₀ h0,
        and_iff_right (nsmul_mem hf n), and_iff_right hf] }
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalLogCanonicalGenerisation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.Discrepancy

theorem kltAt_lcAt_of_specializes (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Sp ℂ) (n : ℕ) (Γ : X → ℚ) (x z : X) (hzx : z ⤳ x) :
    (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) :=
  ⟨fun ⟨η, m, g, h₁, h₂, h₃, h₄⟩ =>
      ⟨η, m, g, h₁, h₂, fun w hw E hE => h₃ w (hw.trans hzx) E hE,
        fun E hE => h₄ E (hE.of_specializes hzx)⟩,
    fun ⟨η, m, g, h₁, h₂, h₃, h₄⟩ =>
      ⟨η, m, g, h₁, h₂, fun w hw E hE => h₃ w (hw.trans hzx) E hE,
        fun E hE => h₄ E (hE.of_specializes hzx)⟩⟩

theorem kltAt_lcAt_generisation :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ),
      ∀ (Γ : X → ℚ) (x z : X), z ⤳ x →
        (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) :=
  fun X _ _ p n Γ x z h => kltAt_lcAt_of_specializes X p n Γ x z h

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftModelHolomorphicOverReflexFieldStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftModel_holomorphic_overReflexField : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Core5 R F → ∀ i σ s, IsEmbOverK D σ s → HolShape (R.MW i σ) ∧ ∃ w, WtIs (R.MW i σ) w := by
  first | exact @GlobalTheory.LowRow.holShape_overK | exact GlobalTheory.LowRow.holShape_overK | (intros; apply GlobalTheory.LowRow.holShape_overK <;> assumption)
end

