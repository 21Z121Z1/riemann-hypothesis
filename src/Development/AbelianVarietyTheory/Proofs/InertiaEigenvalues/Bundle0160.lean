import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0150
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0143
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0156
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Formalism.WachLatticeTwists.LatticeDualFibres.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0151
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0050

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsKMultiplicativeUnitOneHaarScalingStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absK_multiplicative_unitOne_haarScaling : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) := by
  first | exact @GlobalTheory.JR.Et.absK_facts | exact GlobalTheory.JR.Et.absK_facts | (intros; apply GlobalTheory.JR.Et.absK_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinTransportAlgClosureEquivStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_transport_algClosure_equiv : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] [Algebra E E'] (φ : Ω ≃+* Ω'), (∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x)) → ∀ (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (art' : Neutral.B1.Ideles E' →* GlobalTheory.HeckeGal.Gab E' Ω'), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → ∀ (ρ : GlobalTheory.HeckeGal.Gab E' Ω' →* GlobalTheory.HeckeGal.Gab E Ω), (∀ (τ : Formalism.ConjugateSelfDual.G E' Ω') (σ : Formalism.ConjugateSelfDual.G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (GlobalTheory.HeckeGal.toAb E' Ω' τ) = GlobalTheory.HeckeGal.toAb E Ω σ) → ∀ (B : Type) [CommGroup B] (χ : GlobalTheory.HeckeGal.Gab E Ω →* B) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E')), w.asIdeal.comap (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers E')) = v.asIdeal → (∀ x, Formalism.L2.Host.IsUnitAt v x → χ (art (Neutral.B1.localIdele E v x)) = 1) → (∀ x, Formalism.L2.Host.IsUnitAt w x → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = 1) ∧ ∀ x ϖ, Formalism.L2.Host.IsUnifAt w x → Formalism.L2.Host.IsUnifAt v ϖ → χ (ρ (art' (Neutral.B1.localIdele E' w x))) = χ (art (Neutral.B1.localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers E) := by
  first | exact @GlobalTheory.ArtinTransport.chi_artin_transport | exact GlobalTheory.ArtinTransport.chi_artin_transport | (intros; apply GlobalTheory.ArtinTransport.chi_artin_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH0LevelRepEqStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H0_level_rep_eq : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M]
    [Module O M] (ρ : Representation O G M) (c : O), Finite ρ.invariants →
    Nat.card (ReciprocityTheory.Gal.H0 (GlobalTheory.ShapeNeg.levRep ρ c)) =
      Nat.card (ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  first | exact @GlobalTheory.ShapeNeg.card_H0_level_rep | exact GlobalTheory.ShapeNeg.card_H0_level_rep | (intros; apply GlobalTheory.ShapeNeg.card_H0_level_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOntoOfUnramified
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.UnramCyc

open PowerSeries in

theorem _root_.GlobalTheory.UnramCyc.chi_onto_of_unramified : ∀ {l : ℕ} [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (K : _root_.Formalism.BasicNotions.Loc.FinExt l),
    K.1 ≤ _root_.Formalism.BasicNotions.Loc.MaximalUnramifiedExtension l → ∀ c : ℤ_[l]ˣ, ∃ g ∈ _root_.Formalism.BasicNotions.Loc.GK K, (P.χQ g : ℚ_[l]) = ((c : ℤ_[l]) : ℚ_[l]) := by
  intro l _ P K hK c
  have hnorm : ‖((c : ℤ_[l]) : ℚ_[l])‖ = 1 := by
    rw [PadicInt.padic_norm_e_of_padicInt]
    exact PadicInt.norm_units c
  obtain ⟨g, hg, hgc⟩ := _root_.GlobalTheory.Cyc.exists_chi_eq K P.χQ P.χQ_cyc _ hnorm
  have hK0 : _root_.Formalism.BasicNotions.Loc.K0 K = K.1 := by
    unfold _root_.Formalism.BasicNotions.Loc.K0
    exact inf_eq_left.mpr hK
  refine ⟨g, ?_, hgc⟩
  unfold _root_.Formalism.BasicNotions.Loc.GK
  rw [← hK0]
  exact hg

end GlobalTheory.UnramCyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContActionTorsionLevelZModOfIsLocallyConstantStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contAction_torsionLevelZMod_of_isLocallyConstant : ∀ {G : Type} [Group G] [TopologicalSpace G] {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (p r : ℕ) [NeZero (p ^ r)] (c : O) (h : ((p : O) ^ r) ∈ Ideal.span {c}),
    (∀ m : M, c • m = 0 → IsLocallyConstant (fun g => ρ g m)) →
    letI := GlobalTheory.ShapeNeg.levZ (M := M) p r h
    ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p r h ρ) := by
  first | exact @GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | exact GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant | (intros; apply GlobalTheory.ShapeNeg.contAction_levRepZ_of_isLocallyConstant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterIsLocallyConstantModPowStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_character_isLocallyConstant_mod_pow : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O]
    (ε : Formalism.GaloisCohomology.GK p K →* Oˣ), (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ N : ℕ,
    IsLocallyConstant (fun σ : Formalism.GaloisCohomology.GK p K => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O)) := by
  first | exact @GlobalTheory.ShapeNeg.cyclotomic_isLocallyConstant_mod | exact GlobalTheory.ShapeNeg.cyclotomic_isLocallyConstant_mod | (intros; apply GlobalTheory.ShapeNeg.cyclotomic_isLocallyConstant_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPowNeOneOfMovesRootStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_character_pow_ne_one_of_moves_root : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], (p : O) ∈ IsLocalRing.maximalIdeal O → (p : O) ≠ 0 →
    ∀ ε : Formalism.GaloisCohomology.GK p K →* Oˣ, (∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) → ∀ k : ℕ,
    (∃ (σ : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 ∧ (σ ^ k) ζ ≠ ζ) →
    ∃ σ : Formalism.GaloisCohomology.GK p K, ε σ ^ k ≠ 1 := by
  first | exact @GlobalTheory.ShapeNeg.cyc_char_pow_ne_one | exact GlobalTheory.ShapeNeg.cyc_char_pow_ne_one | (intros; apply GlobalTheory.ShapeNeg.cyc_char_pow_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescentOfPointsKilled
section
open scoped NNReal TensorProduct

namespace GlobalTheory

theorem descent_of_points_killed : ∀ (l : ℕ) [Fact l.Prime] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B] (u : A) (pr : B →ₗ[A] A), ((l : ℕ) : B) = 0 → algebraMap A B u ∈ nonZeroDivisors B → IsHausdorff (Ideal.span {algebraMap A B u}) B → ∀ (κ : Type) [Fintype κ] (x : κ → B), (∀ (T : Type) [CommRing T] (i₁ i₂ : B →+* T), (∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a)) → IsUnit (i₁ (algebraMap A B u)) → ∃ c : κ → κ → T, ∀ j, i₁ (x j) - i₂ (x j) = ∑ i, (i₁ (x i) - i₂ (x i)) ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ ψ' : B →+* O), ψ (algebraMap A B u) ≠ 0 → ¬ IsUnit (ψ (algebraMap A B u)) → IsAdicComplete (Ideal.span {ψ (algebraMap A B u)}) O → (∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a)) → ∀ j, ψ (x j) = ψ' (x j)) → pr 1 = 1 → ∀ j, x j = algebraMap A B (pr (x j)) := by
  intro l _ A B _ _ _ _ u pr hl hu hH κ _ x hEq hPt hpr
  let iL : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeLeft
  let iR : B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.includeRight
  let U : B ⊗[A] B := algebraMap A (B ⊗[A] B) u
  let D : κ → B ⊗[A] B := fun j => iL (x j) - iR (x j)
  have hiL : ∀ a, iL (algebraMap A B a) = algebraMap A (B ⊗[A] B) a := fun a => iL.commutes a
  have hiR : ∀ a, iR (algebraMap A B a) = algebraMap A (B ⊗[A] B) a := fun a => iR.commutes a

  have hlR : ((l : ℕ) : B ⊗[A] B) = 0 := by
    rw [← map_natCast iL, hl, map_zero]

  have hUreg : U ∈ nonZeroDivisors (B ⊗[A] B) := by
    have hinj : Function.Injective (LinearMap.mulLeft A (algebraMap A B u)) := by
      intro b b' hbb
      have h0 : (b - b') * algebraMap A B u = 0 := by
        simp only [LinearMap.mulLeft_apply] at hbb
        rw [sub_mul, mul_comm b, mul_comm b', hbb, sub_self]
      exact sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff hu).mp h0)
    have hinj' := Module.Flat.rTensor_preserves_injective_linearMap (M := B) _ hinj
    have hmul : ∀ y : B ⊗[A] B, y * U = LinearMap.rTensor B (LinearMap.mulLeft A (algebraMap A B u)) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b b' =>
        simp [U, Algebra.TensorProduct.algebraMap_apply, mul_comm]
      | add y z hy hz => rw [add_mul, hy, hz, map_add]
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    rw [hmul] at hy
    exact hinj' (by rw [hy, map_zero])

  obtain ⟨h, c', hc'⟩ : ∃ (h : ℕ) (c' : κ → κ → B ⊗[A] B), ∀ j, U ^ h * D j = ∑ i, D i ^ l * c' i j := by
    let T := Localization.Away U
    let i₁ : B →+* T := (algebraMap (B ⊗[A] B) T).comp iL.toRingHom
    let i₂ : B →+* T := (algebraMap (B ⊗[A] B) T).comp iR.toRingHom
    have hA : ∀ a, i₁ (algebraMap A B a) = i₂ (algebraMap A B a) := by
      intro a
      simp only [i₁, i₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, hiR]
    have hunit : IsUnit (i₁ (algebraMap A B u)) := by
      simp only [i₁, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL]
      exact IsLocalization.Away.algebraMap_isUnit U
    obtain ⟨c, hc⟩ := hEq T i₁ i₂ hA hunit
    obtain ⟨⟨b, hb⟩, hb'⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers U) (S := T)
      (Finset.univ : Finset (κ × κ)) (fun p => c p.1 p.2)
    obtain ⟨h, rfl⟩ := hb
    choose c' hc'' using fun (p : κ × κ) => hb' p (Finset.mem_univ p)
    refine ⟨h, fun i j => c' (i, j), fun j => ?_⟩
    have hD : ∀ i, algebraMap (B ⊗[A] B) T (D i) = i₁ (x i) - i₂ (x i) := by
      intro i; simp [D, i₁, i₂]
    apply IsLocalization.injective T (M := Submonoid.powers U) (Submonoid.powers_le.mpr hUreg)
    rw [map_mul, map_sum, hD, hc j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, map_pow, hD]
    rw [hc'' (i, j)]
    change _ = _ * ((U ^ h) • c i j)
    rw [Algebra.smul_def, map_pow]
    ring

  have hkey : ∀ (m : ℕ) j, U ^ m ∣ D j := by
    refine GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points l (B ⊗[A] B) U hlR hUreg κ D c' h hc' ?_
    intro O _ _ _ _ _ f hf0 hfnu hcomp j
    let ψ : B →+* O := f.comp iL.toRingHom
    let ψ' : B →+* O := f.comp iR.toRingHom
    have hψ : ψ (algebraMap A B u) = f U := by
      simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, U]
    have hagree : ∀ a, ψ (algebraMap A B a) = ψ' (algebraMap A B a) := by
      intro a
      simp only [ψ, ψ', RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hiL, hiR]
    have := hPt O ψ ψ' (by rw [hψ]; exact hf0) (by rw [hψ]; exact hfnu) (by rw [hψ]; exact hcomp) hagree j
    simp only [ψ, ψ', RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
    simp only [D, map_sub, this, sub_self]

  let φ : B ⊗[A] B →ₗ[A] B := TensorProduct.lift ((LinearMap.lsmul A B).comp pr)
  have hφ : ∀ b b' : B, φ (b ⊗ₜ b') = pr b • b' := fun b b' => by simp [φ]
  intro j
  have hφD : φ (D j) = algebraMap A B (pr (x j)) - x j := by
    simp only [D, map_sub]
    change φ (x j ⊗ₜ 1) - φ (1 ⊗ₜ x j) = _
    rw [hφ, hφ, hpr, one_smul, Algebra.smul_def, mul_one]
  have hmem : ∀ n : ℕ, algebraMap A B (pr (x j)) - x j ∈ Ideal.span {algebraMap A B u ^ n} := by
    intro n
    obtain ⟨r, hr⟩ := hkey n j
    rw [← hφD, hr]
    have : U ^ n * r = u ^ n • r := by simp [U, Algebra.smul_def, map_pow]
    rw [this, LinearMap.map_smul, Algebra.smul_def, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hz := hH.haus (algebraMap A B (pr (x j)) - x j) (fun n => by
    rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
    exact hmem n)
  exact (sub_eq_zero.mp hz).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualCinvOKSmall
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem dual_cinvOK_small : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ V ∈ 𝓝 (0 : A.K),
    ∀ᶠ c in 𝓝[≠] (0 : F), {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} ⊆ V := by
  intro F E _ _ _ _ _ A ψ hψ V hV
  classical
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOpen, -, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  let b := Module.finBasis F A.K
  let d := (Algebra.traceForm F A.K).dualBasis hnd b

  have hU : (⋂ i, {t : F | t • b i ∈ A.OK}) ∈ 𝓝 (0 : F) := by
    refine Filter.iInter_mem.2 fun i => ?_
    have hc : Continuous fun t : F => t • b i := continuous_id.smul continuous_const
    have : A.OK ∈ 𝓝 ((fun t : F => t • b i) 0) := by simpa using hOpen.mem_nhds h0
    exact hc.continuousAt this
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  have hx₀0 : x₀ ≠ 0 := by rintro rfl; exact hx₀ (AddChar.map_zero_eq_one ψ)

  have key : ∀ t : F, (∀ l : F, ‖l‖ < ε → ψ (l * t) = 1) → ‖t‖ ≤ ‖x₀‖ / ε := by
    intro t ht
    by_contra hlt
    push_neg at hlt
    have ht0 : t ≠ 0 := by
      rintro rfl; simp at hlt; linarith [div_pos (norm_pos_iff.2 hx₀0) hε]
    have hn : ‖x₀ / t‖ < ε := by
      rw [norm_div, div_lt_iff₀ (norm_pos_iff.2 ht0)]
      rw [div_lt_iff₀ hε] at hlt; linarith
    apply hx₀
    have := ht (x₀ / t) hn
    rwa [div_mul_cancel₀ x₀ ht0] at this
  set Rr := ‖x₀‖ / ε with hRr
  have hRr0 : 0 ≤ Rr := div_nonneg (norm_nonneg _) hε.le

  let g : (Fin (Module.finrank F A.K) → F) → A.K := fun t => ∑ i, t i • d i
  have hg : Continuous g := continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hg0 : g 0 = 0 := by simp [g]
  have hgV : g ⁻¹' V ∈ 𝓝 (0 : Fin (Module.finrank F A.K) → F) := by
    rw [← hg0] at hV; exact hg.continuousAt hV
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.1 hgV
  have hev : ∀ᶠ c in 𝓝 (0 : F), ‖c‖ * Rr < δ := by
    have : Tendsto (fun c : F => ‖c‖ * Rr) (𝓝 0) (𝓝 (‖(0:F)‖ * Rr)) :=
      (continuous_norm.mul continuous_const).tendsto 0
    simp only [norm_zero, zero_mul] at this
    exact this.eventually (gt_mem_nhds hδ)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with c hc hc0
  intro y hy
  have hc0' : c ≠ 0 := hc0
  have hbound : ∀ i, ‖Algebra.trace F A.K (y * b i)‖ ≤ ‖c‖ * Rr := by
    intro i
    have h1 : ‖c⁻¹ * Algebra.trace F A.K (b i * y)‖ ≤ Rr := by
      apply key
      intro l hl
      have hmem : c • ((l * c⁻¹) • b i) ∈ A.OK := by
        rw [smul_smul, mul_comm l, ← mul_assoc, mul_inv_cancel₀ hc0', one_mul]
        have : l ∈ Metric.ball (0:F) ε := by simpa using hl
        simpa using Set.mem_iInter.1 (hεU this) i
      have := hy _ hmem
      simp only [Et.psiK, smul_mul_assoc, map_smul, smul_eq_mul] at this
      rw [← this]; congr 1; ring
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hc0')] at h1
    rwa [mul_comm y]
  have hy' : y = g (fun i => Algebra.trace F A.K (y * b i)) := by
    simp only [g]
    conv_lhs => rw [← d.sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply]
    rfl
  rw [hy']
  apply hδV
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hδ]
  intro i
  exact lt_of_le_of_lt (hbound i) hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatFiniteFree
section
open Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory

theorem dualLat_finite_free {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {V V' : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [AddCommGroup V'] [Module O V']
    [Module (FractionRing O) V'] [IsScalarTower O (FractionRing O) V']
    (b : V →ₗ[O] V' →ₗ[O] FractionRing O) (T : Submodule O V) :
    IsLatticeIn T → PerfectRight b →
      Module.Finite O (dualLat b T) ∧ Module.Free O (dualLat b T) := by
  classical
  rintro ⟨⟨s, hs⟩, hspan⟩ hb
  have hsT : ∀ x ∈ s, x ∈ T := fun x hx => hs ▸ Submodule.subset_span hx
  have hmem : ∀ (f : dualLat b T) (x : s), ∃ o : O, algebraMap O (FractionRing O) o = b x f :=
    fun f x => Submodule.mem_one.mp (f.2 x (hsT x x.2))
  let g0 : dualLat b T → s → O := fun f x => Classical.choose (hmem f x)
  have hg0 : ∀ f x, algebraMap O (FractionRing O) (g0 f x) = b x f :=
    fun f x => Classical.choose_spec (hmem f x)
  have hinj : Function.Injective (algebraMap O (FractionRing O)) :=
    IsFractionRing.injective O (FractionRing O)
  let g : dualLat b T →ₗ[O] (s → O) :=
    { toFun := g0
      map_add' := fun f f' => by
        funext x; apply hinj
        rw [Pi.add_apply, map_add, hg0, hg0, hg0, Submodule.coe_add, map_add]
      map_smul' := fun c f => by
        funext x; apply hinj
        rw [Pi.smul_apply, smul_eq_mul, map_mul, hg0, hg0, Submodule.coe_smul, map_smul,
          RingHom.id_apply, Algebra.smul_def] }
  have ginj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h0 : ∀ x ∈ s, b x f = 0 := fun x hx => by
      rw [← hg0 f ⟨x, hx⟩]
      have : g0 f ⟨x, hx⟩ = 0 := congrFun hf ⟨x, hx⟩
      rw [this, map_zero]
    have hT0 : T ≤ LinearMap.ker (b.flip (f : V')) := by
      intro x hx
      rw [← hs] at hx
      refine (Submodule.span_le.mpr ?_ : Submodule.span O (s : Set V) ≤ _) hx
      intro y hy
      simpa using h0 y hy
    let ψ : V →ₗ[FractionRing O] FractionRing O :=
      (b.flip (f : V')).extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)
    have hψ : ψ = 0 := by
      have : Submodule.span (FractionRing O) (T : Set V) ≤ LinearMap.ker ψ := by
        rw [Submodule.span_le]
        intro x hx
        have := hT0 hx
        simpa [ψ] using this
      rw [hspan, top_le_iff, LinearMap.ker_eq_top] at this
      exact this
    obtain ⟨f0, _, huniq⟩ := hb 0
    have e1 : (f : V') = f0 := huniq _ (fun x => by
      have := congrArg (fun φ => φ x) hψ
      simpa [ψ] using this)
    have e2 : (0 : V') = f0 := huniq _ (fun x => by simp)
    exact Subtype.ext (e1.trans e2.symm)
  have hfin : Module.Finite O (dualLat b T) := Module.Finite.of_injective g ginj
  have htf : Module.IsTorsionFree O (dualLat b T) :=
    Function.Injective.moduleIsTorsionFree g ginj (fun c m => g.map_smul c m)
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaGramDetInvAlgBaseChangeUnramifiedOdd
section
noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

namespace GlobalTheory.UnitLemma.Unr

theorem val_mul_of_ne {K : UQ} {a b : K.E} (ha : a ≠ 0) (hb : b ≠ 0) :
    val K.O (a * b) = val K.O a + val K.O b := by
  unfold val
  have ha' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E a ≠ 0 := by simpa using ha
  have hb' : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E b ≠ 0 := by simpa using hb
  rw [map_mul, WithZero.log_mul ha' hb']; ring

theorem val_pow_of_ne {K : UQ} {a : K.E} (ha : a ≠ 0) (n : ℕ) : val K.O (a ^ n) = n * val K.O a := by
  induction n with
  | zero => simp [val]
  | succ n ih => rw [pow_succ, val_mul_of_ne (pow_ne_zero _ ha) ha, ih]; push_cast; ring

theorem eta_overExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → Odd d → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (x : B.Aˣ), B.σ (x : B.A) = x → K'.eta ((overExt φ B ψ hψ hσ).gramDet (x : B.A)) = K.eta (B.gramDet (x : B.A)) := by
  intro K K' d φ hU hd B ψ hψ hσ x _
  have hd0 : 0 < d := hd.pos
  obtain ⟨w, hw0, hwv⟩ := GlobalTheory.T.exists_basis_trace_involution_det_unit_unramified K K' d φ hU hd0
  letI : Algebra K.E K'.E := φ.toAlgebra
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact hd0)
  letI : Algebra K'.E B.A := ψ.toAlgebra
  haveI : IsScalarTower K.E K'.E B.A := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  haveI : Module.Finite K'.E B.A := (overExt φ B ψ hψ hσ).fd
  set u := Module.finBasis K'.E B.A with hu
  set H : Matrix (Fin (Module.finrank K'.E B.A)) (Fin (Module.finrank K'.E B.A)) K'.E :=
    Matrix.of fun i j => Algebra.trace K'.E B.A ((x : B.A) * u i * B.σ (u j)) with hH
  have h1 : (overExt φ B ψ hψ hσ).gramDet (x : B.A) = H.det := rfl
  set b0 := w.smulTower u with hb0
  set e := b0.indexEquiv (Module.finBasis K.E B.A) with he
  rw [h1, ← Orbit.eta_gram B _ (b0.reindex e)]
  have h2 : (Matrix.of fun i j => B.herm x ((b0.reindex e) i) ((b0.reindex e) j)) =
      (Matrix.of fun (p q : Fin d × Fin (Module.finrank K'.E B.A)) =>
        Algebra.trace K.E K'.E (w p.1 * H p.2 q.2 * K'.c (w q.1))).submatrix e.symm e.symm := by
    ext i j
    simp only [Module.Basis.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply, hb0,
      Module.Basis.smulTower_apply, InvAlg.herm, hH]
    rw [← Algebra.trace_trace (S := K'.E)]
    refine congrArg (Algebra.trace K.E K'.E) ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul B.σ]
    have hc : ∀ y : K'.E, B.σ (algebraMap K'.E B.A y) = algebraMap K'.E B.A (K'.c y) := hσ
    rw [hc]
    have : (x : B.A) * (algebraMap K'.E B.A (w (e.symm i).1) * u (e.symm i).2) *
        (algebraMap K'.E B.A (K'.c (w (e.symm j).1)) * B.σ (u (e.symm j).2)) =
        (w (e.symm i).1 * K'.c (w (e.symm j).1)) • ((x : B.A) * u (e.symm i).2 * B.σ (u (e.symm j).2)) := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [this, LinearMap.map_smul, smul_eq_mul]; ring
  rw [h2, Matrix.det_submatrix_equiv_self, GlobalTheory.T.det_trace_gram_block_eq_pow_mul_norm_det w H (fun l => K'.c (w l))]
  by_cases hH0 : H.det = 0
  · rw [hH0, Algebra.norm_zero, mul_zero]; simp [UQ.eta, val]
  have hN : Algebra.norm K.E H.det ≠ 0 := by
    rw [Ne, Algebra.norm_eq_zero_iff]; exact hH0
  unfold UQ.eta
  rw [val_mul_of_ne (pow_ne_zero _ hw0) hN, val_pow_of_ne hw0, hwv, GlobalTheory.T.addVal_norm_unramifiedInvolutionFieldExt_eq_mul K K' d φ hU hd0, mul_zero, zero_add,
    zpow_mul]
  rw [zpow_natCast, hd.neg_one_pow]

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivFractionRingQuotPiProdFiniteStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_fractionRingQuot_pi_prod_finite : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ {Y : Type} [AddCommGroup Y] [Module O Y], (∀ y : Y, ∃ n : ℕ, ϖ ^ n • y = 0) →
    Finite (LinearMap.ker (ϖ • LinearMap.id : Y →ₗ[O] Y)) →
    ∃ (a : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Module O F), Finite F ∧ Nonempty (Y ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) := by
  first | exact @GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | exact GlobalTheory.CofinGen.exists_equiv_pi_prod_finite | (intros; apply GlobalTheory.CofinGen.exists_equiv_pi_prod_finite <;> assumption)
end

