import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0048
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0092
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0069
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitValuationBounds.PrvFOfOrbitLetterBounds
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeInSumTwistedDualsFitsWord
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_of_isSubOfSums : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsSubOfSums T.ρ (fun x s => Ms x s) → Fits W T (recWord L j ε g) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hJ hRd T hT
  have hO := GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension l LL
  have hW := GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR
  have hjump : ∀ a τ, Over W τ a →
      JumpsInV (P.PD K) T.ρ τ {u | u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))} := fun a τ hτ =>
    GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (P.PD K) T.ρ Ms τ _ hT
      (fun x => hJ.jumps x τ (g a) (hRd τ a hτ))
  refine ⟨?_, ?_, ?_⟩
  · exact GlobalTheory.CrysSub.isCrys_of_isSubOfSums (P.PD K) hF hO (GRep.ofLat T) Ms hJ.cont hT hJ.crys
  · intro a τ hτ u hu
    exact ((hW a).1 u (hjump a τ hτ u hu)).1
  · intro a τ hτ u hu
    exact ((hW a).1 u (hjump a τ hτ u hu)).2

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTwistedDualFitsWordFewSmallJumps
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem fits_lowCount_of_matRep : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1) {ι : Type} {k r : ℕ} (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (M' : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG), Roomy L C → Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → K.1 ≤ MaximalUnramifiedExtension l → JumpIn P D j ε c κ Ms M' → (∀ τ a, Over W τ a → Reads D.host c κ τ (g a)) → ∀ T : Lat K LL, IsMatRep T M' → Fits W T (recWord L j ε g) ∧ ∀ (_ft : Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)) (a), lowCount W T a (recWord L j ε g).η ≤ ((recWord L j ε g).m : ℤ) := by
  intro D L C j ε l _ P K LL W c κ ι k r Ms M' g hR hF hK hJ hRd T hT
  obtain ⟨hcr, hmu⟩ := GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation P K LL T M' hT
  have hmem : ∀ a τ, Over W τ a → ∀ u, IsJumpV (P.PD K) T.ρ τ u →
      u ∈ (recWord L j ε g).win a ∧
        u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ) := by
    intro a τ hτ u hu
    have h0 := GlobalTheory.T.crystalline_hodgeTateMultiplicity_ne_zero_of_jump P K LL T hF τ u hu
    rw [hmu, hJ.mult' τ (g a) (hRd τ a hτ) u] at h0
    have hc : u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)) := by
      by_contra hn
      exact h0 (by simp [Multiset.count_eq_zero.mpr hn])
    obtain ⟨h1, h2, _⟩ := GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR a
    exact h1 u (h2 u hc)
  refine ⟨⟨hcr hJ.crys', fun a τ hτ u hu => (hmem a τ hτ u hu).1,
    fun a τ hτ u hu => (hmem a τ hτ u hu).2⟩, ?_⟩
  intro _ft a
  obtain ⟨τ0, hτ0, huniq⟩ := GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified P K LL W hK a
  unfold lowCount
  rw [Finset.sum_eq_single_of_mem τ0 (by simpa using hτ0) (fun b hb hne => by
    exact absurd (huniq b (by simpa using hb)) hne)]
  have h3 := (GlobalTheory.T.twistedDualJumps_mem_window_box L C j ε g hR a).2.2
  have he : ∀ u, multV (P.PD K) T.ρ τ0 u = (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) := fun u => by
    rw [hmu, hJ.mult' τ0 (g a) (hRd τ0 a hτ0) u]
  simp only [he]
  exact h3

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OpenCharacterEqOneOfIntegralUnitOneAtRamified
section
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UnitCut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open Classical in

def cutA (z : FiniteAdeleRing (𝓞 E) E) (hz : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (z P) ≤ 1)
    (S : Set (HeightOneSpectrum (𝓞 E))) : FiniteAdeleRing (𝓞 E) E :=
  ⟨fun P => if P ∈ S then z P else 1, Filter.Eventually.of_forall fun P => by
    by_cases h : P ∈ S
    · simp only [h, if_true]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz P)
    · simp only [h, if_false]
      exact one_mem _⟩

open Classical in
theorem cutA_apply (z : FiniteAdeleRing (𝓞 E) E) (hz : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (z P) ≤ 1)
    (S : Set (HeightOneSpectrum (𝓞 E))) (P : HeightOneSpectrum (𝓞 E)) :
    cutA z hz S P = if P ∈ S then z P else 1 := by
  rfl

open GlobalTheory.Mem.Col2 (afIso mem_rInt_iff mem_suppAt_iff)

section Cut

theorem apply_mul (a b : FiniteAdeleRing (𝓞 E) E) (P : HeightOneSpectrum (𝓞 E)) : (a * b) P = a P * b P := rfl

theorem apply_one (P : HeightOneSpectrum (𝓞 E)) : (1 : FiniteAdeleRing (𝓞 E) E) P = 1 := rfl

theorem int_val {x : (AfE F E)ˣ} (hx : x ∈ intU F E) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v (afIso F E (x : AfE F E) P) ≤ 1 :=
  (mem_rInt_iff F E _).1 hx.1 P

theorem int_inv {x : (AfE F E)ˣ} (hx : x ∈ intU F E) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v (afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E) P) ≤ 1 :=
  (mem_rInt_iff F E _).1 hx.2 P

theorem afIso_mul_inv (x : (AfE F E)ˣ) (P : HeightOneSpectrum (𝓞 E)) :
    afIso F E (x : AfE F E) P * afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1 := by
  rw [← apply_mul, ← map_mul, Units.mul_inv, map_one, apply_one]

theorem eq_of_afIso {y y' : (AfE F E)ˣ} (h : ∀ P, afIso F E (y : AfE F E) P = afIso F E (y' : AfE F E) P) : y = y' :=
  Units.ext ((afIso F E).injective (FiniteAdeleRing.ext _ h))

def cutU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E))) : (AfE F E)ˣ where
  val := (afIso F E).symm (cutA (afIso F E (x : AfE F E)) (int_val hx) S)
  inv := (afIso F E).symm (cutA (afIso F E ((x⁻¹ : (AfE F E)ˣ) : AfE F E)) (int_inv hx) S)
  val_inv := by
    rw [← map_mul, (afIso F E).symm_apply_eq, map_one]
    refine FiniteAdeleRing.ext _ fun P => ?_
    rw [apply_mul, cutA_apply, cutA_apply, apply_one]
    split_ifs
    · exact afIso_mul_inv x P
    · exact one_mul 1
  inv_val := by
    rw [← map_mul, (afIso F E).symm_apply_eq, map_one]
    refine FiniteAdeleRing.ext _ fun P => ?_
    rw [apply_mul, cutA_apply, cutA_apply, apply_one]
    split_ifs
    · rw [mul_comm]; exact afIso_mul_inv x P
    · exact one_mul 1

open Classical in
theorem afIso_cutU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E)))
    (P : HeightOneSpectrum (𝓞 E)) :
    afIso F E (cutU x hx S : AfE F E) P = if P ∈ S then afIso F E (x : AfE F E) P else 1 := by
  show afIso F E ((afIso F E).symm _) P = _
  rw [RingEquiv.apply_symm_apply, cutA_apply]

theorem afIso_cutU_inv (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E)))
    (P : HeightOneSpectrum (𝓞 E)) : Valued.v (afIso F E (((cutU x hx S)⁻¹ : (AfE F E)ˣ) : AfE F E) P) ≤ 1 := by
  show Valued.v (afIso F E ((afIso F E).symm _) P) ≤ 1
  rw [RingEquiv.apply_symm_apply, cutA_apply]
  split_ifs
  · exact int_inv hx P
  · rw [map_one]

theorem cutU_mem_intU (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (S : Set (HeightOneSpectrum (𝓞 E))) :
    cutU x hx S ∈ intU F E := by
  refine ⟨(mem_rInt_iff F E _).2 fun P => ?_, (mem_rInt_iff F E _).2 fun P => afIso_cutU_inv x hx S P⟩
  show Valued.v (afIso F E (cutU x hx S : AfE F E) P) ≤ 1
  rw [afIso_cutU]
  split_ifs
  · exact int_val hx P
  · rw [map_one]

theorem cutU_union (x : (AfE F E)ˣ) (hx : x ∈ intU F E) {S S' : Set (HeightOneSpectrum (𝓞 E))} (hd : Disjoint S S') :
    cutU x hx (S ∪ S') = cutU x hx S * cutU x hx S' := by
  refine eq_of_afIso fun P => ?_
  rw [Units.val_mul, map_mul, apply_mul, afIso_cutU, afIso_cutU, afIso_cutU]
  by_cases h : P ∈ S
  · have h' : P ∉ S' := Set.disjoint_left.1 hd h
    simp [h, h']
  · by_cases h' : P ∈ S' <;> simp [h, h']

theorem cutU_univ (x : (AfE F E)ˣ) (hx : x ∈ intU F E) : cutU x hx Set.univ = x :=
  eq_of_afIso fun P => by rw [afIso_cutU]; simp

theorem cutU_empty (x : (AfE F E)ˣ) (hx : x ∈ intU F E) : cutU x hx ∅ = 1 :=
  eq_of_afIso fun P => by rw [afIso_cutU, Units.val_one, map_one, apply_one]; simp

theorem cutU_mem_inertAt (x : (AfE F E)ˣ) (hx : x ∈ intU F E) (v : HeightOneSpectrum (𝓞 F)) :
    cutU x hx {P | P.under (𝓞 F) = v} ∈ inertAt E v :=
  ⟨cutU_mem_intU x hx _, (mem_suppAt_iff F E v _).2 fun P hP => by
    rw [afIso_cutU]
    simp [hP]⟩

theorem natCast_notMem_of_under {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} (h : (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal) :
    (N : 𝓞 E) ∉ P.asIdeal := fun h' => h (by
  show (N : 𝓞 F) ∈ P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
  rw [Ideal.mem_comap, map_natCast]
  exact h')

theorem cutU_mem_congN (x : (AfE F E)ˣ) (hx : x ∈ intU F E) {N : ℕ} (hN : 0 < N) :
    cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} ∈ congN F E N := by
  rw [GlobalTheory.Mem.ReadEx.mem_congN_iff]
  refine ⟨cutU_mem_intU x hx _, (afIso F E).symm (algebraMap E _ (N : E)⁻¹ *
    (afIso F E (cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} : AfE F E) - 1)), ?_, ?_⟩
  · rw [mem_rInt_iff, RingEquiv.apply_symm_apply]
    intro P
    show Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P *
      (afIso F E (cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} : AfE F E) P - 1)) ≤ 1
    rw [afIso_cutU]
    by_cases h : (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal
    · have h3 : Valued.v ((algebraMap E (FiniteAdeleRing (𝓞 E) E) (N : E)⁻¹) P) = 1 := by
        change Valued.v (algebraMap E (P.adicCompletion E) (N : E)⁻¹) = 1
        rw [map_inv₀, map_inv₀, ← map_natCast (algebraMap (𝓞 E) E), GlobalTheory.TwistPlaces.valued_int,
          GlobalTheory.TwistPlaces.intValuation_eq_one P (natCast_notMem_of_under h), inv_one]
      have h4 : P ∈ {P : HeightOneSpectrum (𝓞 E) | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} := h
      rw [if_pos h4, map_mul, h3, one_mul]
      exact Valuation.map_sub_le _ (int_val hx P) (by rw [map_one])
    · have h4 : P ∉ {P : HeightOneSpectrum (𝓞 E) | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} := h
      rw [if_neg h4, sub_self, mul_zero, map_zero]
      exact zero_le'
  · apply (afIso F E).injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_natCast, GlobalTheory.Mem.ReadEx.inv_mul_mul_nat hN, map_sub, map_one]

end Cut

theorem map_eq_one_of_one_at_ramified : ∀ (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Field L] (σ : L →+* ℂ) (ξ : Chr F E L), ξ ∈ openChr F E L → (ratId F E).range ≤ ξ.ker → ∀ x ∈ intU F E,
    (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∈ Qprime ξ → GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1) → ξ x = 1 := by
  intro F E L _ _ _ _ _ _ _ ξ hξ _ x hx h1
  classical
  obtain ⟨N, hN, hk⟩ := hξ
  have h0 : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by simpa using hN.ne'
  have hT : {v : HeightOneSpectrum (𝓞 F) | (N : 𝓞 F) ∈ v.asIdeal}.Finite :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 F)), ξ (cutU x hx {P | P.under (𝓞 F) ∈ T}) = 1 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have e : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ (∅ : Finset (HeightOneSpectrum (𝓞 F)))} = ∅ := by
        ext P
        simp
      rw [e, cutU_empty, map_one]
    | insert v T hv ih =>
      have e : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ insert v T} =
          {P | P.under (𝓞 F) = v} ∪ {P | P.under (𝓞 F) ∈ T} := by
        ext P
        simp
      have hd : Disjoint {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) = v} {P | P.under (𝓞 F) ∈ T} :=
        Set.disjoint_left.2 fun P h h' => hv (by
          have h2 : P.under (𝓞 F) = v := h
          have h3 : P.under (𝓞 F) ∈ T := h'
          rw [← h2]
          exact h3)
      rw [e, cutU_union x hx hd, map_mul, ih, mul_one]
      by_cases hq : v ∈ Qprime ξ
      · have e1 : cutU x hx {P | P.under (𝓞 F) = v} = 1 := eq_of_afIso fun P => by
          rw [afIso_cutU, Units.val_one, map_one, apply_one]
          split_ifs with hP
          · have h2 : P.under (𝓞 F) = v := hP
            exact h1 P (by rw [h2]; exact hq)
          · rfl
        rw [e1, map_one]
      · have hle : inertAt E v ≤ ξ.ker := by
          by_contra h
          exact hq h
        exact MonoidHom.mem_ker.1 (hle (cutU_mem_inertAt x hx v))
  have hd : Disjoint {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ hT.toFinset}
      {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} :=
    Set.disjoint_left.2 fun P h h' => h' (by simpa using h)
  have eu : {P : HeightOneSpectrum (𝓞 E) | P.under (𝓞 F) ∈ hT.toFinset} ∪
      {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} = Set.univ := by
    ext P
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.Finite.mem_toFinset, Set.mem_univ, iff_true]
    exact em _
  have e : cutU x hx {P | P.under (𝓞 F) ∈ hT.toFinset} * cutU x hx {P | (N : 𝓞 F) ∉ (P.under (𝓞 F)).asIdeal} = x := by
    rw [← cutU_union x hx hd, eu, cutU_univ]
  have e2 := congrArg ξ e
  rw [map_mul, key, one_mul, MonoidHom.mem_ker.1 (hk (cutU_mem_congN x hx hN))] at e2
  exact e2.symm

end GlobalTheory.UnitCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrbitBoundOverSecondEmbeddingAnyBasePoint
section
noncomputable section

open scoped BigOperators
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical Formalism.MainNotions.OrbitPlaces PI.OrbBoundFW

namespace GlobalTheory.TwU

theorem orbitBound_overSecondEmbedding_anyBasePoint_alt : ∀ (D : D7) (L : SizeData₂ D) (X : Inst D L) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D) (C6 C : ℝ), OrbitPlaces.OrbitLetterBoundsAll C6 C → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge C6 C K ce → ∀ (p : ℕ) [Fact p.Prime] (h : OrbitPlaces.OrbOK D p), IsResidueClassZero D p → hP D p ≠ 0 → (p : ℝ) ≤ L.sc.X'' D.R.n → ∀ u, ∀ i < D.R.m, ∀ (t : HH D) (ep sg : ℂ_[p]) (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]), ‖ep‖ = 1 → (sg = 1 ∨ sg = -1) → product_zeroth_first_parts.B1 p (nP D p) be → product_zeroth_first_parts.B2 p (nP D p) be → product_zeroth_first_parts.B3 p (nP D p) be → product_zeroth_first_parts.B4 p (nP D p) be → OrbitPlaces.OrbGe E p h u i (true, t) ep sg be (FOrb D (i + 1) p (true, t) - OrbitPlaces.errF L K ce (i + 1) p (true, t)) := by
  intro D L X K ce E C6 C hA hS hC p _ h _hc0 _hP hp u i hi t ep sg be hep hsg h1 h2 h3 h4 Th hB0
  have hAdm := admissible_of_jet_bounds h u i (true, t) Th ep sg be hep hsg h1 h2 h3 h4 hB0
  have hCor := (hA.1 _ hAdm).2 (L.sc.a ^ 2) (setting_sq hS h hp u hi (true, t) Th) D.R.k (wOrb D p i (true, t))
    (eOrb E p u i (true, t)) (three_le_k D) (wOrb_pos hS p hi (true, t)) (eOrb_bounds hS p u hi (true, t))
    (dl_off h u i (true, t) Th) (dl_on h u i (true, t) Th)
  refine kvalGe_mono hCor ?_
  have hg : 0 ≤ ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, (orbLoc E p h u i (true, t) Th).baseTerm s :=
    Finset.sum_nonneg fun s _ => orbit_local_term_nonneg _ s
  have hw := sum_Wc_le hS h u hi (true, t) Th
  have hl := loss_le hS hC h hp hi (true, t)
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast h.five
  have hgam : Formalism.MainNotions.product_zeroth_first_parts.gam p = Formalism.MainNotions.G.gam p := rfl
  have hgpos : 0 ≤ Formalism.MainNotions.G.gam p := by
    unfold Formalism.MainNotions.G.gam
    apply div_nonneg (by linarith)
    nlinarith
  have hsw : 0 ≤ ∑ s, wOrb D p i (true, t) s := Finset.sum_nonneg fun s _ => (wOrb_pos hS p hi (true, t) s).le
  have hc6 : C6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) ≤ ce.c6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_right hC.c6 hsw
  have hgw : Formalism.MainNotions.G.gam p * ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, ((orbLoc E p h u i (true, t) Th).Wc s : ℝ) ≤
      Formalism.MainNotions.G.gam p * (topsOrb D p (true, t) : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hw hgpos
  have hi1 : i + 1 - 1 = i := by omega
  rw [hi1] at hl
  have hF : FOrb D (i + 1) p (true, t) = lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i (true, t) s) := rfl
  have hE : errF L K ce (i + 1) p (true, t) = Formalism.MainNotions.G.gam p * (topsOrb D p (true, t) : ℝ) * (L.sc.b + L.etaSz + 1 + 3 * L.Sc) +
      ce.c6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) +
      ((nP D p : ℝ) * (D.R.N (i + 1 - 1) : ℝ) * (D.R.N (i + 1) : ℝ) *
          (Real.logb p (4 * (nP D p : ℝ) * Nm D * L.sc.a) + 1) +
        (K.dl1 * (nP D p : ℝ) * Nm D ^ 2 * Real.logb p (2 * L.sc.a) +
          K.dl2 * (topsOrb D p (true, t) : ℝ) * Real.logb p (2 * L.sc.a) ^ 2)) := by
    unfold errF; simp only [wOrb]; ring
  rw [hi1] at hE
  show FOrb D (i + 1) p (true, t) - errF L K ce (i + 1) p (true, t) ≤
    (∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, (orbLoc E p h u i (true, t) Th).baseTerm s +
      lpF p (nP D p) (fun s => ((D.R.k : ℝ) - 1) * wOrb D p i (true, t) s)) - C6 * (∑ s, wOrb D p i (true, t) s) / (p : ℝ) -
      Formalism.MainNotions.product_zeroth_first_parts.gam p * ∑ s ∈ (orbLoc E p h u i (true, t) Th).TT, ((orbLoc E p h u i (true, t) Th).Wc s : ℝ) -
      C * ((nP D p : ℝ) * (D.R.N i : ℝ) * (D.R.N (i + 1) : ℝ) * (Real.logb p (L.sc.a ^ 2) + 1))
  rw [hF, hE, hgam]
  linarith

end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartnerPlaceInvolutiveNormConjEq
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

theorem eTau_tauSg (D : D7) (τ : D.what₂.Tau) :
    ((D.eTau (tauSg D τ) : D.R.Psi) : D.R.GG) =
      (D.eTau τ : D.R.GG) * sgm D := by
  have h : (D.eTau τ : D.R.GG) * sgm D ∈ D.R.Psi := by
    rw [Formalism.HC.Frame.mem_Psi_iff]
    have := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2
    simp [sgm, this]
  unfold tauSg
  rw [dif_pos h, Equiv.apply_symm_apply]

theorem sgm_mul_sgm (D : D7) : sgm D * sgm D = 1 := by
  simp [sgm, Prod.ext_iff]

theorem sgm_ne_one (D : D7) : sgm D ≠ 1 := by
  intro h
  have : (((sgm D).1.1 : ℤˣ) : ℤ) = 1 := by rw [h]; rfl
  simp [sgm] at this

theorem sgm_mul_cc (D : D7) : sgm D * D.R.cc = ((1, -1), 1) := by
  simp [sgm, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, Prod.ext_iff]

theorem tauSg_invol_norm_conj_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p = D.host.d →
    ∀ (τ : D.what₂.Tau), tauSg D (tauSg D τ) = τ ∧ tauSg D τ ≠ τ ∧
      ∀ y : D.host.E, ‖tauEmb D lam (tauSg D τ) (D.host.conj y)‖ = ‖tauEmb D lam τ y‖ := by
  intro D p _ lam hp τ
  subst hp
  refine ⟨?_, ?_, ?_⟩
  · apply D.eTau.injective
    apply Subtype.ext
    rw [eTau_tauSg, eTau_tauSg, mul_assoc, sgm_mul_sgm, mul_one]
  · intro h
    have h1 := congrArg (fun t => ((D.eTau t : D.R.Psi) : D.R.GG)) h
    simp only [eTau_tauSg] at h1
    exact sgm_ne_one D (mul_eq_left.mp h1)
  · intro y
    set g : D.R.GG := (D.eTau τ : D.R.GG) with hg
    let σ : D.host.E ≃ₐ[ℚ] D.host.E := D.host.sigmaOf ((1, -1), 1)
    have hgσ : D.host.galE σ = ((1, -1), 1) := by
      change D.host.galE
        ((D.host.gal).symm ((1, -1), 1)) = _
      exact D.host.gal.apply_symm_apply _
    have hemb : embT D (tauSg D τ) (D.host.conj y) = embT D τ (σ y) := by
      change D.host.emb _ (D.host.conj y) = D.host.emb g (σ y)
      rw [eTau_tauSg, ← hg]
      have e1 := emb_mul_galE D.host (g * sgm D) D.host.conj y
      have e2 := emb_mul_galE D.host g σ y
      have hc : D.host.galE D.host.conj = D.R.cc :=
        D.host.galE_conjE
      rw [hc] at e1
      rw [hgσ] at e2
      rw [← e1, ← e2, mul_assoc, sgm_mul_cc]
    have hsp : SamePrime (rhoH D lam τ) ((rhoH D lam τ).comp (σ : D.host.E →+* D.host.E)) := by
      intro a
      have hPp := primeOf_isPrime (rhoH D lam τ)
      have hd : (D.host.d : 𝓞 D.host.E) ∈ primeOf (rhoH D lam τ) := natCast_mem_primeOf _
      obtain ⟨z, hz, hze⟩ := (Formalism.MainNotions.GlobalTheoryTheory.jnt_inertiaD D _ hPp hd σ).2 (Or.inr hgσ) a
      have hz' : ‖rhoH D lam τ (σ (a : D.host.E)) - rhoH D lam τ (a : D.host.E)‖ < 1 := by
        rw [← map_sub, ← hze]
        exact hz
      change ‖rhoH D lam τ (a : D.host.E)‖ < 1 ↔ ‖rhoH D lam τ (σ (a : D.host.E))‖ < 1
      constructor
      · intro h
        rw [← sub_add_cancel (rhoH D lam τ (σ (a : D.host.E))) (rhoH D lam τ (a : D.host.E))]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hz' h)
      · intro h
        rw [← add_sub_cancel (rhoH D lam τ (σ (a : D.host.E))) (rhoH D lam τ (a : D.host.E))]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h (by rw [norm_sub_rev]; exact hz'))
    have h1 := SamePrime.norm_eq hsp y
    have h2 : tauEmb D lam (tauSg D τ) (D.host.conj y) = tauEmb D lam τ (σ y) := by
      unfold tauEmb
      rw [hemb]
    rw [h2, ← coe_rhoH, h1]
    rfl

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiInvarianceRamifiedPlaceSharp
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
theorem _root_.GlobalTheory.T.phi_invariance_ramified_place_sharp : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (sharp : Bool) (i : ℕ) (P : rowSG Pr sel mu), i + 2 ≤ R.m → (qOf P.1).Prime → ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2 → P.1 ∈ Pr.vGs → sharp = true → ∀ κ ∈ Jat (Pr := Pr) (R := R) sharp (i + 1) P.1, ∀ x, PhiAt Ch mu sharp i P.1 (κ.toLinearMap ∘ₗ x) * muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E) = lamRow Ch mu sharp (i + 1) P.1 κ.toLinearMap * PhiAt Ch mu sharp i P.1 x :=
  fun Ch sel _ mu cst sharp _ P hi _ _ _ _ _ hκ x => GlobalTheory.DatumLaw.phiAt_target Ch sel mu cst sharp hi P hκ x
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiInvarianceUnramifiedPlace
section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col NumberField IsDedekindDomain Classical
theorem _root_.GlobalTheory.T.phi_invariance_unramified_place : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (sharp : Bool) (i : ℕ) (P : rowSG Pr sel mu), i + 2 ≤ R.m → (qOf P.1).Prime → ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2 → P.1 ∉ Pr.vGs → ∀ κ ∈ Jat (Pr := Pr) (R := R) sharp (i + 1) P.1, ∀ x, PhiAt Ch mu sharp i P.1 (κ.toLinearMap ∘ₗ x) * muAt Ch sel mu cst i P ((LinearEquiv.det κ : X.Eˣ) : X.E) = lamRow Ch mu sharp (i + 1) P.1 κ.toLinearMap * PhiAt Ch mu sharp i P.1 x := by
  intro X Pr R Ch sel S mu cst sharp i P hi _ _ _ κ hκ x
  exact GlobalTheory.DatumLaw.phiAt_target Ch sel mu cst sharp hi P hκ x
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanMapNabKDelK
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem use₂ {Kf K ι : Type} [Field Kf] [Field K] [Fintype ι] {n : ℕ} (eK : K →+* Kf) (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map eK (actP lam B F) = actP lam (fun τ => Formalism.UG.bc eK (B τ)) (MvPolynomial.map eK F) := by
  have h1 : (MvPolynomial.map eK).comp (trAct B).toRingHom =
      (trAct (fun τ => Formalism.UG.bc eK (B τ))).toRingHom.comp (MvPolynomial.map eK) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, blockAct_X, bc_coe]
  have h2 : MvPolynomial.map eK (trAct B F) = trAct (fun τ => Formalism.UG.bc eK (B τ)) (MvPolynomial.map eK F) :=
    congrArg (fun φ : Pol K ι n →+* Pol Kf ι n => φ F) h1
  have h3 : eK (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc eK (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h2, h3]

end GlobalTheory.ValCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrimeStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_series_b_conditions_large_prime : ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]), 5 ≤ l → 2 ≤ d → Even d → BeStd l d be → product_zeroth_first_parts.B1 l d be ∧ product_zeroth_first_parts.B2 l d be ∧ product_zeroth_first_parts.B3 l d be ∧ product_zeroth_first_parts.B4 l d be := by
  first | exact @GlobalTheory.KerStd.bHyps_of_beStd | exact GlobalTheory.KerStd.bHyps_of_beStd | (intros; apply GlobalTheory.KerStd.bHyps_of_beStd <;> assumption)
end

