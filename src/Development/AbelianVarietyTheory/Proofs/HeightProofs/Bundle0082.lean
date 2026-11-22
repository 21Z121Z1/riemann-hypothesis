import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0081
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0182
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0183
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValuesStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmCurveTorsion_definedOver_of_weberValues : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (F : IntermediateField ℚ ℂ) (n : ℕ), 0 < n → (H.rt0 ∈ F → WeberIn H F n → CurveOver H F n) ∧ ∀ m, m ∣ n → CurveOver H F n → CurveOver H F m := by
  first | exact @GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn | exact GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn | (intros; apply GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField
section
noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open scoped IntermediateField

theorem exists_xiOK_of_root (D : D7) (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde')
    (h : Complex.exp (2 * Real.pi * Complex.I / (xiOrd D.host (D.host.g 0 * D.host.g 1 * p) : ℕ)) ∈ FO D) :
    ∃ xi, XiOK D p xi := by
  have hp0 : 0 < p := by
    rcases hp with rfl | rfl
    exacts [D.host.pde_prime.pos, D.host.pde'_prime.pos]
  have hN : 0 < D.host.g 0 * D.host.g 1 * p :=
    Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hp0
  obtain ⟨xi, m, hm, a1, a2, a3, a4, -⟩ := GlobalTheory.NormOneChar.exists_xi D p hp
  have hI : Ideal.span {((D.host.g 0 * D.host.g 1 * p : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hN.ne'
  have : Finite (𝓞 D.host.E ⧸ Ideal.span {((D.host.g 0 * D.host.g 1 * p : ℕ) : 𝓞 D.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have ho : 0 < xiOrd D.host (D.host.g 0 * D.host.g 1 * p) :=
    Nat.mul_pos (Nat.mul_pos two_pos (classNumber_pos _)) Nat.card_pos
  refine ⟨xi, a1, a2, a3, ⟨m, hm, a4⟩, fun x hn => GlobalTheory.NormOneChar.mem_of_pow_eq_one ho h ?_⟩
  rw [← Units.val_pow_eq_pow_val]
  exact congrArg Units.val (GlobalTheory.NormOneChar.tame_pow_eq_one D _ xi hN a1 a2 x hn)

theorem curveOver_of_weberSet (D : D7) (F : IntermediateField ℚ ℂ) {n : ℕ} (hn : 0 < n)
    (h0 : D.host.φ₀ D.host.sqrtMinusD ∈ F)
    (h : ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔
      ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + D.host.φ₀ D.host.sqrtMinusD) / 2)) → weberSet L n ⊆ F) :
    GlobalTheory.CompRat.CurveOver (hostOfRecord D) F n :=
  (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ (hostOfRecord D) F n hn).1 h0 fun L hL =>
    ⟨h L hL (Set.mem_insert _ _), fun s hs =>
      h L hL (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩

set_option maxHeartbeats 4000000 in

theorem jointQ_of_small_field : ∀ (X : Stages) (F : IntermediateField ℚ ℂ), Rich X.B.toPre F → (∀ L : ℝ, HostSz X.B.host L → Sz F (poR X.B.R L) (poR X.B.R L)) → (∀ z, z ∈ F ↔ ∃ x ∈ X.B.Ks, X.B.embLL x = z) → JointQ X.toD7 := by
  intro X F hR hS hF
  obtain rfl : F = FO X.toD7 := SetLike.ext fun z => (hF z).trans (mem_FO_assembled_iff X z).symm
  have key : ∀ p, (p = X.B.host.pde ∨ p = X.B.host.pde') → FieldOK0 X.toD7 p := by
    intro p hp
    have hp0 : 0 < p := by
      rcases hp with rfl | rfl
      exacts [X.B.host.pde_prime.pos, X.B.host.pde'_prime.pos]
    refine ⟨hp, hermitianCodeWordStages_ringOfIntegers_full _, hermitianCodeWordStages_has_rootOfUnity _, ?_, ?_, TypeNormPin.hermitianCodeWordStages_typeNorms_principal _,
      fun h => Nat.not_prime_zero (X.B.toPre.level_cond 0 h).1, ?_⟩
    · rcases hp with rfl | rfl
      exacts [hR.roots _ (by simp), hR.roots _ (by simp)]
    · exact curveOver_of_weberSet X.toD7 _
        (Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hp0) (hR.host _)
        fun L hL => hR.weber L hL p (by simpa using hp)
    · rcases hp with rfl | rfl
      exacts [X.B.toPre.level_split _ X.B.host.pde_level.1, X.B.toPre.level_split _ X.B.host.pde_level.2]
  refine ⟨key _ (Or.inl rfl), key _ (Or.inr rfl), exists_xiOK_of_root _ _ (Or.inl rfl) ?_,
    exists_xiOK_of_root _ _ (Or.inr rfl) ?_, hS⟩
  · exact hR.roots (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * X.B.host.pde)) (by simp)
  · exact hR.roots (xiOrd X.B.host (X.B.host.g 0 * X.B.host.g 1 * X.B.host.pde')) (by simp)

end GlobalTheory.FieldSize
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.KFourierCoefficientRapidDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFourier_coefficient_rapid_decay : ∀ {n : ℕ} (ε : Fin n → Bool) (N : ℕ) (F : List (Mx n) → Mx n → ℂ), IsDerFam ε F → FamGrowth ε N F → ContinuousOn (F []) (UJset ε) → ∀ e : ℕ → KG ε → ℂ, (∀ i, GlobalTheory.KFourier.IsKer ε i (e i)) → ∀ u : List (Mx n), (∀ X ∈ u, inK ε X) → ∃ b : ℕ → ℝ, Summable b ∧ ∀ i, ∀ y ∈ UJset ε, ‖∫ k, e i k * F u (y * toMK k) ∂(muK ε)‖ ≤ b i * (1 + hs y) ^ N := by
  first | exact @GlobalTheory.KFourier.kFourier_coeff_decay | exact GlobalTheory.KFourier.kFourier_coeff_decay | (intros; apply GlobalTheory.KFourier.kFourier_coeff_decay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesFiniteAlgebraicPermuted
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize

theorem weberSet_finite (L : PeriodPair) {n : ℕ} (hn : 0 < n) : (weberSet L n).Finite := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  let f : ℤ × ℤ → ℂ := fun s => L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) *
    L.weierstrassP ((s.1 * L.ω₁ + s.2 * L.ω₂) / n)
  refine Set.Finite.insert _
    ((((Set.finite_Ico (0 : ℤ) n).prod (Set.finite_Ico (0 : ℤ) n)).image f).subset ?_)
  rintro _ ⟨z, hz, -, rfl⟩
  obtain ⟨a, b, rfl⟩ := PeriodPair.mem_lattice.1 hz
  refine ⟨(a % n, b % n), ⟨⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩,
    ⟨Int.emod_nonneg _ hnZ.ne', Int.emod_lt_of_pos _ hnZ⟩⟩, ?_⟩
  have e : (a * L.ω₁ + b * L.ω₂) / n = (((a % n : ℤ) : ℂ) * L.ω₁ + ((b % n : ℤ) : ℂ) * L.ω₂) / n +
      (((a / n : ℤ) : ℂ) * L.ω₁ + ((b / n : ℤ) : ℂ) * L.ω₂) := by
    have a1 : ((a % n : ℤ) : ℂ) + n * ((a / n : ℤ) : ℂ) = a := by
      exact_mod_cast Int.emod_add_mul_ediv a n
    have a2 : ((b % n : ℤ) : ℂ) + n * ((b / n : ℤ) : ℂ) = b := by
      exact_mod_cast Int.emod_add_mul_ediv b n
    rw [← a1, ← a2]
    field_simp
    ring
  simp only [f]
  rw [e, L.weierstrassP_add_coe _ ⟨_, PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩⟩]

theorem exists_map_weber_eq (L : PeriodPair) (n : ℕ) (h2 : L.g₂ ≠ 0) (h3 : L.g₃ ≠ 0) (τ : ℂ ≃+* ℂ)
    (hτ : τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2))
    (t : ℂ) (hnt : (n : ℂ) * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    ∃ t', (n : ℂ) * t' ∈ L.lattice ∧ t' ∉ L.lattice ∧
      τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) =
        L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t' := by
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  set J := L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) with hJ
  set u := L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) with hu
  have hu0 : u ≠ 0 := div_ne_zero (mul_ne_zero h2 h3) hD
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hu0 (by simpa using hm.symm)
  have hmu : (m ^ 2)⁻¹ = u := by rw [hm, inv_inv]
  have H := isHomothetic_scalePeriods L m hm0
  set L' := scalePeriods L m hm0
  have hJ1 : J - 1 = 27 * L.g₃ ^ 2 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [hJ, div_sub_one hD, sub_sub_cancel]
  have e2 : L'.g₂ = J * (J - 1) / 27 := by
    rw [H.g₂_eq, show (m ^ 4)⁻¹ = ((m ^ 2)⁻¹) ^ 2 by ring, hmu, hJ1, hu, hJ]
    generalize L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = D
    ring
  have e3 : L'.g₃ = J * (J - 1) ^ 2 / 729 := by
    rw [H.g₃_eq, show (m ^ 6)⁻¹ = ((m ^ 2)⁻¹) ^ 3 by ring, hmu, hJ1, hu, hJ]
    generalize L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = D
    ring
  have f2 : L'.g₂ = τ L'.g₂ := by
    rw [e2]; simp [hτ, map_ofNat]
  have f3 : L'.g₃ = τ L'.g₃ := by
    rw [e3]; simp [hτ, map_ofNat]
  obtain ⟨s, -, hc⟩ := GlobalTheory.ConjPoint.exists_conjEquiv f2 f3
  obtain ⟨w, hw⟩ := latticePoint_surjective L' (s (latticePoint L' (m * t)))
  obtain ⟨t', rfl⟩ : ∃ t', w = m * t' := ⟨m⁻¹ * w, by field_simp⟩
  have hconj := (hc _ _).2 hw.symm
  have h1 := (hconj.nsmul_mem_iff f2 f3 n).1 (by rw [mul_left_comm]; exact (H _).2 hnt)
  rw [mul_left_comm] at h1
  obtain ⟨-, h4, h5, -⟩ := hconj.resolve_left fun h => ht ((H t).1 h.1)
  refine ⟨t', (H _).1 h1, fun h => h4 ((H _).2 h), ?_⟩
  rw [H.weierstrassP_mul, H.weierstrassP_mul, hmu] at h5
  exact h5.symm

theorem weberSet_finite_algebraic_permuted : ∀ (L : PeriodPair) (n : ℕ), 0 < n → L.g₂ ≠ 0 → L.g₃ ≠ 0 → (weberSet L n).Finite ∧ (IsAlgebraic ℚ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ w ∈ weberSet L n, IsAlgebraic ℚ w) ∧ ∀ τ : ℂ ≃+* ℂ, τ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) = (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) → ∀ t, (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice → ∃ t', (n : ℂ) * t' ∈ L.lattice ∧ t' ∉ L.lattice ∧ τ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) = (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') := by
  intro L n hn h2 h3
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  refine ⟨weberSet_finite L hn, fun hj => ?_, exists_map_weber_eq L n h2 h3⟩
  rintro _ (rfl | ⟨z, hz, hz', rfl⟩)
  · exact hj
  · exact GlobalTheory.WeberField.weber_isAlgebraic L hj hn hz' (by rwa [mul_div_cancel₀ _ hn0])

end GlobalTheory.FieldSize
end

