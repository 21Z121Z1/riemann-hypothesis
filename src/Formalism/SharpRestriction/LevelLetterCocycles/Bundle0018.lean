import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0016
import Formalism.SharpRestriction.LevelLetterCocycles.LengthRestrictNat
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section CoreW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem cancel_unit_mul_uniformizer_pow {w : (LetA O n)ˣ} {k : ℕ} {a b : LetA O n}
    (h : (w : LetA O n) * letπ ^ k * a = (w : LetA O n) * letπ ^ k * b) : a = b := by
  unfold letπ at h
  have h' : (fun _ => PowerSeries.X) ^ k * a = (fun _ => PowerSeries.X) ^ k * b := by
    have := congrArg (fun x => (↑w⁻¹ : LetA O n) * x) h
    simpa [← mul_assoc, Units.inv_mul] using this
  funext i
  have hi := congrFun h' i
  simp only [Pi.mul_apply, Pi.pow_apply] at hi
  ext m
  have hm := congrArg (PowerSeries.coeff (m + k)) hi
  rwa [mul_comm, PowerSeries.coeff_mul_X_pow, mul_comm, PowerSeries.coeff_mul_X_pow] at hm

theorem pi0Core_of (W : LocWach PD LL O v n) (w : (LetA O n)ˣ) (k : ℕ) (h1 : W.π₀ ∈ W.AΔ)
    (h3 : W.π₀ = (w : LetA O n) * letπ ^ k) : Pi0LatticeCondition W := by
  intro g
  obtain ⟨t, ht⟩ := Formalism.MainNotions.LiftingTheory.gamma_X_eq W g
  obtain ⟨Uc, hUc⟩ : ∃ Uc : LetA O n,
      Uc = fun _ => PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t := ⟨_, rfl⟩
  have hπ : W.γA g letπ = letπ * Uc := by
    funext i
    rw [hUc]
    show W.γ₀ g PowerSeries.X = PowerSeries.X * (PowerSeries.C ((W.χΓ g : Oˣ) : O) + PowerSeries.X * t)
    exact ht
  obtain ⟨u, hu⟩ : ∃ u : LetA O n, u = (↑w⁻¹ : LetA O n) * W.γA g (w : LetA O n) * Uc ^ k :=
    ⟨_, rfl⟩
  have heq : W.γA g W.π₀ = W.π₀ * u := by
    rw [h3, map_mul, map_pow, hπ, hu,
      show (↑w : LetA O n) * letπ ^ k * (↑w⁻¹ * W.γA g ↑w * Uc ^ k) =
        (↑w * ↑w⁻¹) * (W.γA g ↑w * (letπ * Uc) ^ k) by ring,
      Units.mul_inv, one_mul]
  refine ⟨u, ?_, heq⟩
  have hmem : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := h1
  show ∀ δ ∈ W.DelF, W.γA δ u = u
  intro δ hδ
  have e1 : W.γA δ (W.γA g W.π₀) = W.γA g W.π₀ := by
    rw [Formalism.MainNotions.LiftingTheory.gammaA_comm W δ g, hmem δ hδ]
  rw [heq, map_mul, hmem δ hδ, h3] at e1
  exact cancel_unit_mul_uniformizer_pow e1

end CoreW

theorem finrank_K0_eq_one_of_le_Kur {l : ℕ} [Fact l.Prime] {K : FinExt l} (hK : K.1 ≤ MaximalUnramifiedExtension l) :
    Module.finrank ↥(K0 K) ↥K.1 = 1 := by
  unfold K0
  rw [finrank_eq_one_iff_of_nonzero' (1 : ↥K.1) one_ne_zero]
  intro x
  refine ⟨⟨(x : Om l), IntermediateField.mem_inf.mpr ⟨x.2, hK x.2⟩⟩, ?_⟩
  first
    | exact Subtype.ext (mul_one _)
    | exact Subtype.ext (by simp)
    | rfl

theorem ring_condition_uniformizer_polynomial (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (h : CaseA K LL) :
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL h.2.2) 1 (((D.loc l).PD K).p - 1) ((HW l).W K 1 LL h.2.2).π₀
      (fun _ => Polynomial.X + Polynomial.C ((((D.loc l).PD K).p : ℕ) : ↥(OL LL))) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h9W := h9 l K 1 LL h.2.2
  have hp := h9W _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL h.2.2))
  refine ((hp ?_ ?_).2.2 ?_).1
  · exact (HW l).W_s K 1 LL h.2.2
  · rw [(D.loc l).PD_p K]
    exact h.2.1
  · exact finrank_K0_eq_one_of_le_Kur h.1

theorem gamma_uniformizer_divisible_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : UniformiserGammaTheorem D HW F := by
  intro h9 l _ K LL h _
  obtain ⟨h1, -, ⟨w, hw⟩, -⟩ := ring_condition_uniformizer_polynomial D HW F h9 l K LL h
  exact pi0Core_of _ w _ h1 hw

end Formalism.MainNotions.UnusedSlot80
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.BcAtDesc
section
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Asm

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem bcAt_desc (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) {ι : Type} [Fintype ι] (bO : Module.Basis ι O O')
    (bL : Module.Basis ι LL LL') (hb : ∀ i, bL i = algebraMap O' LL' (bO i))
    (hlin : ∀ φ : LL' →ₗ[LL] LL, Continuous φ) [IsLocalRing O'] (hk : lenOl PD (O := O) ≠ ⊤) :
    Formalism.MainNotions.WachCoordinates.BCAt PD (LL := LL) (O := O) (O' := O') (IsScalarTower.toAlgHom Qp LL LL') :=
  bcAt_of PD hc hO' hJ (descLift_at PD hc hO' bO bL hb hlin) (descCol_at PD hc hO' bO bL hb hlin hk)

end Asm

end Formalism.MainNotions.UnusedSlot80.BCW
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
section
noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions

structure RowsAllN : Prop where
  bloch_kato_dropping_admitted : ∀ D : D7, LocalSituation.Conclusion5 D
  bloch_kato_rank_admitted : ∀ D : D7, LocalSituation.adm5 D
  euler_characteristic_admitted : ∀ D : D7, LocalSituation.adm6 D
  bloch_kato_exactness_admitted : ∀ D : D7, LocalSituation.adm7 D
  tate_duality_admitted : ∀ D : D7, LocalSituation.adm8 D
  selmer_control_admitted : ∀ D : D7, RamifiedCoefficientChains.adm11 D
  automorphic_lift_admitted : ∀ D : D7, RamifiedCoefficientChains.adm12 D
  hecke_eigenvalue_admitted : ∀ D : D7, RamifiedCoefficientChains.adm13 D
  frobenius_semilinearity_admitted : ∀ D : D7, RamifiedCoefficientChains.adm15 D
  crystalline_dimension_admitted : ∀ D : D7, TruncatedSeriesCountingBounds.adm8 D
  dimension_formula_admitted : ∀ D : D7, TruncatedSeriesCountingBounds.adm9 D
  galois_invariants_admitted : ∀ D : D7, TruncatedSeriesCountingBounds.adm10 D
  dual_rank_formula_admitted : ∀ D : D7, TruncatedSeriesCountingBounds.adm15 D
  period_ring_admitted : ∀ D : D7, TruncatedSeriesCountingBounds.adm16 D
  congruence_prime_admitted : ∀ D : D7, ElementDenominator.adm7 D
  local_factor_bound_admitted : ∀ D : D7, ElementDenominator.adm8 D
  ramification_bound_admitted : ∀ D : D7, ElementDenominator.adm11 D
  residual_irreducibility_admitted : ∀ D : D7, ElementDenominator.adm12 D
  wach_filtration_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LiftingTheory.adm22 D HW F
  wach_lattice_duality_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), LiftingTheory.adm23 D HW F
  lattice_saturation_admitted : ∀ D : D7, tableLineDegreeTwo.adm19 D
  fontaine_comparison_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), tableLineDegreeTwo.adm20 D HW F
  hecke_module_freeness_admitted : ∀ D : D7, tableLineDegreeTwo.adm22 D
  delta_invariant_admitted : ∀ D : D7, WachCoordinates.adm14 D
  fontaine_congruence_admitted : ∀ D : D7, PairedCharacterCondition.FontaineAtPlacesOverL (D := D)
  fontaine_local_admitted : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i
  colength_bound_admitted : ∀ D : D7, LocalTheoryWindows.ArchimedeanSignatureMatching D
  lifting_generators_admitted : ∀ D : D7, LocalTheoryWindows.adm5 D
  unramified_length_admitted : ∀ (D : D7) (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i), EmbeddingTypes.UnramifiedTrivialH1f (D := D) i dc
  crysOn : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), CrysOnCond D HW F
  litFont : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), InvariantsGenerators.LitFont D HW F
  crysIffWD : ∀ D : D7, CrysIffWD D.nd D.naut
  potCrysIffWD : ∀ D : D7, PotCrysIffWD D.nd D.naut

end Formalism.MainNotions.N

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def B1 (l h η S : ℕ) : ℝ :=
  (2 * (aN l (h + η) : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((l : ℝ) - 1) + lam l (h + η)

def B2 (l h η : ℕ) : ℝ := 2 * Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.sig l h η + 2

theorem bound_sum_eq (l h η S : ℕ) : B1 l h η S + B2 l h η = cocyclesToWachVectorsExponent l h η S := by
  unfold B1 B2 cocyclesToWachVectorsExponent; ring

def uOf (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (N s₁ : ℕ) {FF : Type} [AddCommGroup FF]
    [Module O FF] (μ ms : ZMod n → FF →ₗ[O] W.DD T) (c : ZMod n) (f : FF) : W.DD T :=
  ((PD.p : ℕ) : O) ^ N • ms c f - ((PD.p : ℕ) : O) ^ s₁ • μ c f

def Step1Out [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d a N s₁ : ℕ) {FF : Type}
    [AddCommGroup FF] [Module O FF] (z : FF →ₗ[O] W.DD T) (μ : ZMod n → FF →ₗ[O] W.DD T)
    (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T) : Prop :=
  ∀ c ∈ evens n d, ∀ f : FF,
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T c (ms c f) ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1
      (((PD.p : ℕ) : O) ^ s₁ • ((letE c : LetA O n) • z f) + (W.γ T (ms c f) - ms c f)) ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ a • uOf W T N s₁ μ ms c f ∈ W.N T ∧
    Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 (W.γ T (uOf W T N s₁ μ ms c f) - uOf W T N s₁ μ ms c f) ∧
    (f ∈ F₁ → uOf W T N s₁ μ ms c f ∈ W.N T)

def Step1 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ s₁ : ℕ, (s₁ : ℝ) ≤ B1 PD.p (hpar n b S) η S ∧
    ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
      (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
      Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν →
      ∃ (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) ⊤ F₁
          (evens n d).card 0 ∧
        (m = 0 → F₁ = ⊤) ∧
        Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms

def Step2 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∃ sg : ℕ, (sg : ℝ) ≤ B2 PD.p (hpar n b S) η ∧
    ∀ (s₁ : ℕ) (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
      (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
      Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν →
      ∀ (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂),
      Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms →
      ∃ (F₂ : Submodule O FF) (w : ZMod n → ↥F₂ →ₗ[O] W.DD T₂),
        PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) F₁ F₂
          (evens n d).card 0 ∧
        (m = 0 → F₂ = F₁) ∧
        (∀ c ∈ evens n d, ∀ f : ↥F₂, QPowSmulMemPullback W T₂ c η (w c f)) ∧
        ∀ f : ↥F₂, ∃ κ : ZMod n → G → T₂.V,
          (∀ c ∈ evens n d, RhoCoc W T₂ c (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (hpar n b S)) η
            (sigC PD.p (hpar n b S) η) (w c f) (κ c)) ∧
          (((PD.p : O) ^ (s₁ + sg)) • (g (f : FF) : G → T₂.V) - (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L ∨
            ((PD.p : O) ^ (s₁ + sg)) • (g (f : FF) : G → T₂.V) + (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L)

theorem cocyclesToWachVectorsBound_of_extTool [NeZero n] (W : LocWach PD LL O v n) (hE : Sh.ExtTool W) (h1 : Step1 W)
    (h2 : Step2 W) : CocyclesToWachVectorsBound W := by
  intro d T₁ T₂ F b S η m hS
  obtain ⟨s₁, hs₁, H1⟩ := h1 d T₁ T₂ F b S η m hS
  obtain ⟨sg, hsg, H2⟩ := h2 d T₁ T₂ F b S η m hS
  refine ⟨s₁ + sg, ?_, ?_⟩
  · have := bound_sum_eq PD.p (hpar n b S) η S
    push_cast
    linarith
  · intro FF _ _ _ _ g
    obtain ⟨N, y, z, μ, ν, hX⟩ := hE d T₁ T₂ F b S η m hS FF g
    obtain ⟨F₁, ms, hc1, hm1, ho⟩ := H1 FF g N y z μ ν hX
    obtain ⟨F₂, w, hc2, hm2, h36, hid⟩ := H2 s₁ FF g N y z μ ν hX F₁ ms ho
    refine ⟨F₂, w, ?_, ?_, h36, hid⟩
    · have hn : Even n := hS.2.2.1
      have := two_mul_card_evens_le hn d
      exact (hc1.trans hc2).mono (by omega) le_rfl
    · intro h0
      rw [hm2 h0, hm1 h0]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CompleteOfPow
section
noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.OL

open Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

theorem complete_of_pow {R : Type*} [CommRing R] (J : Ideal R) {n : ℕ} (hn : 0 < n)
    (h : IsAdicComplete (J ^ n) R) : IsAdicComplete J R := by
  let : WithIdeal R := ⟨J⟩
  have hJ : IsAdic J := rfl
  have hJn : IsAdic (J ^ n) := is_ideal_adic_pow hJ hn
  rw [hJ.isAdicComplete_iff]
  exact hJn.isAdicComplete_iff.mp h

variable {l : ℕ} [Fact l.Prime]

theorem l_ne_zero (LL : FinExt l) : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
  intro h
  have h2 := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h
  simp only [ZeroMemClass.coe_zero, SubringClass.coe_natCast] at h2
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)

theorem l_not_unit (P : LocPrime l) (LL : FinExt l) : ¬ IsUnit ((l : ℕ) : ↥(OL LL)) := by
  intro hu
  have h0 := Formalism.MainNotions.LiftingTheory.zl_v_unit P LL hu.unit
  have h1 := Formalism.MainNotions.LiftingTheory.zl_v_pow P LL 1
  rw [IsUnit.unit_spec, map_natCast] at h0
  rw [pow_one, h0] at h1
  exact absurd h1 (by simp)

theorem l_mem_max (P : LocPrime l) (LL : FinExt l) :
    letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
    ((l : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) := by
  let := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 (l_not_unit P LL))

theorem OL_dvr (P : LocPrime l) (LL : FinExt l) : IsDiscreteValuationRing ↥(OL LL) := by
  letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  have hfd : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have hded : IsDedekindDomain ↥(OL LL) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have hnf : ¬ IsField ↥(OL LL) := fun hf => by
    have hm := l_mem_max P LL
    rw [isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at hm
    exact l_ne_zero LL hm
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded

theorem OL_complete_max (P : LocPrime l) (LL : FinExt l) :
    letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
    IsAdicComplete (maximalIdeal ↥(OL LL)) ↥(OL LL) := by
  letI := Formalism.MainNotions.LiftingTheory.lkd_local P LL
  have := OL_dvr P LL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(OL LL)
  have hl0 : Ideal.span {((l : ℕ) : ↥(OL LL))} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact l_ne_zero LL
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hl0 hϖ
  have hC := Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  rw [he, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at hC
  refine complete_of_pow _ (n := e) (Nat.pos_of_ne_zero ?_) hC
  rintro rfl
  rw [pow_zero, Ideal.one_eq_top] at hC
  exact not_subsingleton _ hC.subsingleton

end Formalism.MainNotions.CrystallineLiftingInputs.OL
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.InvariantsIsoOfGenerators
section
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

section Gen

variable (S : Sit)

def oneT (T : LocLat S.G S.Qp S.LL S.O) : ↥T.L.T →ₗ[S.O] TW S.RW T :=
  TensorProduct.mk S.O S.RW ↥T.L.T 1

def OneInj : Prop := ∀ T : LocLat S.G S.Qp S.LL S.O, Function.Injective (oneT S T)

def GenFix : Prop :=
  ∀ (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T),
    (∀ g, S.W.resΓ g = S.W.gamK → T.actT g t = t) →
    (∀ g, S.W.resΓ g ∈ S.W.DelF → T.actT g t = t) →
    (∀ g, S.W.resΓ g = 1 → T.actT g t = t) → ∀ g, T.actT g t = t

variable {S}

theorem oneT_apply (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T) : oneT S T t = (1 : S.RW) ⊗ₜ[S.O] t := rfl

theorem TWact_one {R : Type} [CommRing R] [Algebra S.O R] (f : R →ₐ[S.O] R) (T : LocLat S.G S.Qp S.LL S.O)
    (g : S.G) (t : ↥T.L.T) : TWact f T g ((1 : R) ⊗ₜ[S.O] t) = (1 : R) ⊗ₜ[S.O] T.actT g t := by
  simp only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]

theorem TWmap_one {R : Type} [CommRing R] [Algebra S.O R] (f : R →ₐ[S.O] R) (T : LocLat S.G S.Qp S.LL S.O)
    (t : ↥T.L.T) : TWmap f T ((1 : R) ⊗ₜ[S.O] t) = (1 : R) ⊗ₜ[S.O] t := by
  simp only [TWmap, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply]

theorem mem_H0Lat {T : LocLat S.G S.Qp S.LL S.O} (t : ↥T.L.T) : t ∈ invariantLattice T ↔ ∀ g, T.actT g t = t := by
  simp only [invariantLattice, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  first
  | rfl
  | exact Iff.rfl
  | (constructor <;> intro h g <;> exact h g)

theorem mem_fixDD {T : LocLat S.G S.Qp S.LL S.O} (x : S.W.DD T) : x ∈ fixDD S.W T ↔
    S.W.φD T x = x ∧ S.W.γD T S.W.gamK x = x ∧ ∀ δ ∈ S.W.DelF, S.W.γD T δ x = x := by
  simp only [fixDD, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, and_assoc]

private theorem nonempty_invariantLattice_equiv_fixDD (E : S.Comparison₂)
    (hin : ∀ (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T), (∀ g, T.actT g t = t) →
      (1 : S.RW) ⊗ₜ[S.O] t ∈ Set.range (E.jD T))
    (hfix : ∀ (T : LocLat S.G S.Qp S.LL S.O) (b : TW S.RW T), TWmap S.φR T b = b →
      ∃ t : ↥T.L.T, b = (1 : S.RW) ⊗ₜ[S.O] t)
    (hi : OneInj S) (hg : GenFix S) (T : LocLat S.G S.Qp S.LL S.O) :
    Nonempty (↥(invariantLattice T) ≃ₗ[S.O] ↥(fixDD S.W T)) := by

  have key : (invariantLattice T).map (oneT S T) = (fixDD S.W T).map (E.jD T) := by
    ext b
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mem_H0Lat] at ht
      obtain ⟨d, hd⟩ := hin T t ht
      refine ⟨d, ?_, ?_⟩
      · rw [mem_fixDD]
        refine ⟨?_, ?_, ?_⟩
        · apply E.jD_inj T
          rw [E.jD_φ, hd, TWmap_one]
        · obtain ⟨g, hgg⟩ := S.W.resΓ_onto S.W.gamK
          apply E.jD_inj T
          rw [← hgg, E.jD_act, hd, TWact_one, ht g]
        · intro δ _
          obtain ⟨g, hgg⟩ := S.W.resΓ_onto δ
          apply E.jD_inj T
          rw [← hgg, E.jD_act, hd, TWact_one, ht g]
      · rw [oneT_apply, hd]
    · rintro ⟨d, hd, rfl⟩
      rw [mem_fixDD] at hd
      obtain ⟨hφ, hγ, hδ⟩ := hd
      obtain ⟨t, ht⟩ := hfix T (E.jD T d) (by rw [← E.jD_φ, hφ])
      have hact : ∀ g : S.G, S.W.γD T (S.W.resΓ g) d = d → T.actT g t = t := by
        intro g hgd
        apply hi T
        rw [oneT_apply, oneT_apply, ← TWact_one (S.gR g), ← ht, ← E.jD_act, hgd]
      refine ⟨t, ?_, ?_⟩
      · rw [mem_H0Lat]
        apply hg T t
        · intro g hgK
          exact hact g (by rw [hgK, hγ])
        · intro g hgD
          exact hact g (hδ _ hgD)
        · intro g h1
          exact hact g (by rw [h1, S.W.γD_one])
      · rw [oneT_apply, ht]
  exact ⟨(Submodule.equivMapOfInjective (oneT S T) (hi T) (invariantLattice T)).trans
    ((LinearEquiv.ofEq _ _ key).trans
      (Submodule.equivMapOfInjective (E.jD T) (E.jD_inj T) (fixDD S.W T)).symm)⟩

end Gen

theorem invariants_iso_of_generators (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (hi : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      OneInj (sit D.loc HW l (D.locA l) K 1 LL hA.2.2))
    (hg : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      GenFix (sit D.loc HW l (D.locA l) K 1 LL hA.2.2)) :
    H0InvariantsTheorem D HW F := by
  intro hF l hl K LL hA T
  obtain ⟨hW, hD⟩ := hF l K 1 LL hA.2.2
  refine nonempty_invariantLattice_equiv_fixDD (S := sit D.loc HW l (D.locA l) K 1 LL hA.2.2) ((F l).E K 1 LL hA.2.2).tie
    (fun T t ht => ?_) (fun T b hb => (hW T).2.1 b hb) (hi l K LL hA) (hg l K LL hA) T

  refine Set.mem_range.mpr (LinearMap.mem_range.mp ((hD T).2 _ ?_ ?_))
  · intro g _
    rw [TWact_one, ht g]
  · rw [TWmap_one, sub_self]
    exact Submodule.zero_mem _

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.TwQDist
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.MainNotions

def QDistinct (D : D7) (Q : Finset (PlE D.host)) : Prop :=
  ∀ P ∈ Q, ∀ P' ∈ Q, P.asIdeal.comap (algebraMap ℤ (𝓞 D.host.E)) = P'.asIdeal.comap (algebraMap ℤ (𝓞 D.host.E)) →
    P' = P ∨ IsConjPl D.host P P'

def QDistinctAt (D : D7) (C : NChoice D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → QDistinct D (C.Q w)

end Formalism.MainNotions
end
end

