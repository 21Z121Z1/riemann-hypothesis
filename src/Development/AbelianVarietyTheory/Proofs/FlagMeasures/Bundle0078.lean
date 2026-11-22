import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0070
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0071
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuadricCharacterLeakSharesFinite
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0051
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0046
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0020
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitMassEqOfFiniteDoubleCosets
section
open GlobalTheory.HL
open scoped ENNReal Classical

namespace GlobalTheory.HL

theorem inv_encard_stab_ne {G : Type} [Group G] (Γ K0 : Subgroup G)
    (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) (y : G ⧸ K0) :
    ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ ≠ 0 ∧
    ((((Γ ⊓ MulAction.stabilizer G y : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ ≠ ⊤ := by
  induction y using QuotientGroup.induction_on with
  | H g =>
    have hsub : ((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G) ⊆
        {γ | γ ∈ Γ ∧ g⁻¹ * γ * g ∈ K0} := by
      intro γ hγ
      simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, MulAction.mem_stabilizer_iff] at hγ
      refine ⟨hγ.1, ?_⟩
      have h2 := hγ.2
      rw [MulAction.Quotient.smul_coe, QuotientGroup.eq] at h2
      have := K0.inv_mem h2
      simpa [mul_assoc] using this
    have hfin := (hF g).subset hsub
    have hne : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).Nonempty :=
      ⟨1, Subgroup.one_mem _⟩
    constructor
    · rw [ne_eq, ENNReal.inv_eq_zero]
      intro h
      have : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = ⊤ := by
        exact_mod_cast h
      exact (Set.encard_ne_top_iff.2 hfin) this
    · rw [ne_eq, ENNReal.inv_eq_top]
      intro h
      have : (((Γ ⊓ MulAction.stabilizer G (g : G ⧸ K0) : Subgroup G) : Set G)).encard = 0 := by
        exact_mod_cast h
      exact hne.ne_empty (Set.encard_eq_zero.1 this)

theorem mass_quotient_pos_finite {G : Type} [Group G] (Γ K0 : Subgroup G)
    (hS : ∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ)
    (hF : ∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) :
    (∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ K0),
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) ≠ 0 ∧
    (∑' o : MulAction.orbitRel.Quotient Γ (G ⧸ K0),
      ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹) ≠ ⊤ := by
  obtain ⟨S, hS⟩ := hS
  have hfin : Finite (MulAction.orbitRel.Quotient Γ (G ⧸ K0)) := by
    let f : S → MulAction.orbitRel.Quotient Γ (G ⧸ K0) := fun a =>
      Quotient.mk _ ((a.1 : G) : G ⧸ K0)
    refine Finite.of_surjective f ?_
    intro o
    induction o using Quotient.inductionOn with
    | h y =>
      induction y using QuotientGroup.induction_on with
      | H g =>
        obtain ⟨a, ha, γ, hγ, κ, hκ, rfl⟩ := hS g
        refine ⟨⟨a, ha⟩, ?_⟩
        apply Quotient.sound
        refine ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, ?_⟩
        show (γ⁻¹ : G) • ((γ * a * κ : G) : G ⧸ K0) = _
        rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
        simpa [mul_assoc] using K0.inv_mem hκ
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Γ (G ⧸ K0))
  constructor
  · rw [ne_eq, ENNReal.tsum_eq_zero, not_forall]
    exact ⟨Quotient.mk _ ((1 : G) : G ⧸ K0), (inv_encard_stab_ne Γ K0 hF _).1⟩
  · rw [tsum_fintype]
    exact ENNReal.sum_ne_top.2 (fun o _ => (inv_encard_stab_ne Γ K0 hF _).2)

theorem mass_orbit_eq_of_finite_double_cosets : ∀ {G : Type} [Group G] (Γ K0 : Subgroup G), (∃ S : Finset G, ∀ g : G, ∃ a ∈ S, ∃ γ ∈ Γ, ∃ κ ∈ K0, g = γ * a * κ) → (∀ a : G, {γ | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K0}.Finite) → ∃ V0 : ℝ, 0 < V0 ∧ ∀ (X : Type) [MulAction G X] (x : X), K0.relIndex (MulAction.stabilizer G x) ≠ 0 → (MulAction.stabilizer G x).relIndex K0 ≠ 0 → (∑' o : MulAction.orbitRel.Quotient Γ X, if o.out ∈ MulAction.orbit G x then ((((Γ ⊓ MulAction.stabilizer G o.out : Subgroup G) : Set G).encard : ℝ≥0∞))⁻¹ else 0) = ENNReal.ofReal (V0 * invVol K0 (MulAction.stabilizer G x)) := by
  intro G _ Γ K0 hS hF
  obtain ⟨V, hV⟩ := GlobalTheory.T.orbit_mass_eq_inv_stabilizer_volume Γ K0
  have hstab : MulAction.stabilizer G ((1 : G) : G ⧸ K0) = K0 := MulAction.stabilizer_quotient K0
  have h0 := hV (G ⧸ K0) ((1 : G) : G ⧸ K0) (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)
    (by rw [hstab, Subgroup.relIndex_self]; exact one_ne_zero)
  have horb : ∀ y : G ⧸ K0, y ∈ MulAction.orbit G ((1 : G) : G ⧸ K0) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H g => exact ⟨g, show g • ((1 : G) : G ⧸ K0) = g by rw [MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]⟩
  simp only [horb, ite_true, hstab] at h0
  rw [show invVol K0 K0 = 1 by simp [invVol, Subgroup.relIndex_self], ENNReal.ofReal_one,
    mul_one] at h0
  obtain ⟨hV0, hVt⟩ := mass_quotient_pos_finite Γ K0 hS hF
  have hV0' : V ≠ 0 := by rw [← h0]; exact hV0
  have hVt' : V ≠ ⊤ := by rw [← h0]; exact hVt
  refine ⟨V.toReal, ENNReal.toReal_pos hV0' hVt', fun X _ x h1 h2 => ?_⟩
  rw [hV X x h1 h2, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hVt']

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumTransportEquivariantStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitWeightedStabilizerSum_transport_equivariant : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), Stable G X → Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → orbSum G X (fun x => N (f x)) = orbSum G' Y N := by
  first | exact @GlobalTheory.Mass.OrbTransport.main | exact GlobalTheory.Mass.OrbTransport.main | (intros; apply GlobalTheory.Mass.OrbTransport.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingSecondTypeTestOnRepresentativesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_second_type_test_on_representatives : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ¬ S.BBzero d Λ → ∀ B₀ : Set S.V, (∀ y ∈ B₀, y ∈ Λ ∧ y ∈ S.X ⊔ S.X') → (∀ y ∈ S.sat Λ, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ) → (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', algebraMap F E S.th⁻¹ • (x₁ + x₁') ∈ B₀ → algebraMap F E S.th⁻¹ • (x₂ + x₂') ∈ B₀ → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) → S.TypeBe d Λ := by
  first | exact @GlobalTheory.HL.TypeRep.main | exact GlobalTheory.HL.TypeRep.main | (intros; apply GlobalTheory.HL.TypeRep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PatternUnitriangularStrongApproximationStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pattern_unitriangular_strong_approximation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (m : ℕ) (I : Fin m → Fin m → Prop), (∀ i j, I i j → i < j) → (∀ i j l, I i j → I j l → I i l) → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ s : ∀ p, Matrix (Fin m) (Fin m) (A.loc p).Ep, (∀ p i j, ¬ I i j → s p i j = if i = j then 1 else 0) → {p | ¬ IsIntM (A.L p) (s p)}.Finite → ∃ t : Matrix (Fin m) (Fin m) E, (∀ i j, ¬ I i j → t i j = if i = j then 1 else 0) ∧ ∀ p i j, ∃ o ∈ (A.L p).O, ((s p)⁻¹ * t.map (A.loc p).ιE - 1) i j = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  first | exact @GlobalTheory.HL.pattern_strong_approx | exact GlobalTheory.HL.pattern_strong_approx | (intros; apply GlobalTheory.HL.pattern_strong_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticesMoveWithIsometriesStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_sublattices_move_with_isometries : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (g : isom h) (L : Submodule (𝓞 K) V) (U : Submodule K V) (j n : ℕ), (g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n) ∧ (primSp h (g • L) j n).encard = (primSp h L j n).encard := by
  first | exact @GlobalTheory.Mass.PrimMove.main | exact GlobalTheory.Mass.PrimMove.main | (intros; apply GlobalTheory.Mass.PrimMove.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiOfEq
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PhaseProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem coef_eq (A : Places F E sig) {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
    (n : G.GLV) (m : (G.S p).GLV) (hx : A.Ext p n m)
    (sf : Fin (r + 1) → (G.S p).V) (se : Fin r → (G.S p).V)
    (f : Fin (r + 1) → G.V) (es : Fin r → G.V)
    (hsf : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • sf a = A.bc p (f a))
    (hse : ∀ a : Fin r, se a = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)) (a : Fin r) :
    (G.S p).coef sf se m a = algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) *
      (A.loc p).ιE (∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j)) := by
  have hexp : r - (a : ℕ) = (r - ((a.succ : Fin (r + 1)) : ℕ)) + 1 := by
    have := a.isLt
    simp only [Fin.val_succ]
    omega
  set t := algebraMap (A.loc p).Fp (A.loc p).Ep
    ((G.c p : (A.loc p).Fp) ^ (r - ((a.succ : Fin (r + 1)) : ℕ))) with ht
  set u := algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) with hu
  have key : ∀ i, t * m (sf a.succ) i = (A.loc p).ιE (n (f a.succ) i) := by
    intro i
    have h1 := congrArg m (hsf a.succ)
    rw [map_smul, hx] at h1
    exact congrFun h1 i
  have hcj : ∀ j, (A.L p).cj (se a j) = t * u * (A.loc p).ιE (sig (es a j)) := by
    intro j
    rw [A.L_cj p, hse a]
    change (A.loc p).cj (algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) * (A.loc p).ιE (es a j)) = _
    rw [map_mul, AlgEquiv.commutes, (A.loc p).cj_ιE, hexp, pow_succ, map_mul]
  simp only [Frames.coef, Frames.h, hf, map_sum, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hcj j, (G.Hm_eq p), Matrix.map_apply]
  linear_combination (u * (A.loc p).ιE (G.Hm i j) * (A.loc p).ιE (sig (es a j))) * key i

theorem psiOf_eq (A : Places F E sig) {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))
    (δ : ((A.loc p).Fp)ˣ) (g : ℕ) (hg : g ≠ 0)
    (h1 : ∀ y, (A.L p).psi0 y = (A.loc p).psiE
      (-(y * algebraMap (A.loc p).Fp (A.loc p).Ep ((δ : (A.loc p).Fp))⁻¹)))
    (h2 : (G.c p : (A.loc p).Fp) * g = δ * (G.S p).th)
    (n : G.GLV) (m : (G.S p).GLV) (hx : A.Ext p n m)
    (sf : Fin (r + 1) → (G.S p).V) (se : Fin r → (G.S p).V)
    (f : Fin (r + 1) → G.V) (es : Fin r → G.V)
    (hsf : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • sf a = A.bc p (f a))
    (hse : ∀ a : Fin r, se a = algebraMap (A.loc p).Fp (A.loc p).Ep
      ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (es a)) :
    (G.S p).psiOf sf se m = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j)) / g))) := by
  have hth : (G.S p).th ≠ 0 := by
    unfold Frames.th
    split_ifs
    · exact fun h => (G.S p).ϖ_irr.ne_zero (Subtype.ext h)
    · exact one_ne_zero
  have hgE : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  set X : E := ∑ a : Fin r, ∑ i, ∑ j, n (f a.succ) i * G.Hm i j * sig (es a j) with hX
  have hXg : (A.loc p).ιE X = (A.loc p).ιE (X / g) * algebraMap (A.loc p).Fp (A.loc p).Ep (g : (A.loc p).Fp) := by
    rw [map_natCast, ← map_natCast (A.loc p).ιE g, ← map_mul, div_mul_cancel₀ _ hgE]
  have hsc : (G.S p).th⁻¹ * ((G.c p : (A.loc p).Fp) * g) * (δ : (A.loc p).Fp)⁻¹ = 1 := by
    rw [h2]
    field_simp
  have hsum : ∑ j, (G.S p).coef sf se m j =
      algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) * (A.loc p).ιE X := by
    rw [hX, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => coef_eq A G p n m hx sf se f es hsf hse a
  have harg : algebraMap (A.loc p).Fp (A.loc p).Ep (G.S p).th⁻¹ *
      (algebraMap (A.loc p).Fp (A.loc p).Ep (G.c p : (A.loc p).Fp) * (A.loc p).ιE X) *
      algebraMap (A.loc p).Fp (A.loc p).Ep ((δ : (A.loc p).Fp))⁻¹ = (A.loc p).ιE (X / g) := by
    have h3 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) hsc
    simp only [map_mul, map_one] at h3
    rw [hXg]
    linear_combination ((A.loc p).ιE (X / g)) * h3
  unfold Frames.psiOf
  rw [hsum, h1, harg, map_neg (A.loc p).ιE]

theorem main {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) [StarRing E] (hCM : Formalism.BasicNotions.CMData F E)
    (hsig : ∀ x, sig x = star x) (δ : ∀ p, ((A.loc p).Fp)ˣ) (g : ℕ) (hg : g ≠ 0)
    (h1 : ∀ p y, (A.L p).psi0 y = (A.loc p).psiE
      (-(y * algebraMap (A.loc p).Fp (A.loc p).Ep ((δ p : (A.loc p).Fp))⁻¹)))
    (h2 : ∀ p, (G.c p : (A.loc p).Fp) * g = δ p * (G.S p).th)
    (n : G.GLV) (m : ∀ p, (G.S p).GLV) (hx : ∀ p, A.Ext p n (m p)) :
    (∏ᶠ p, (G.S p).psi (m p) = Complex.exp (-(2 * Real.pi * Complex.I *
      ((Algebra.trace ℚ E ((∑ a : Fin r, ∑ i, ∑ j, n (G.f a.succ) i * G.Hm i j * sig (G.es a j)) / g) : ℚ) : ℂ)))) ∧
    (∏ᶠ p, (G.S p).psi' (m p) = Complex.exp (-(2 * Real.pi * Complex.I *
      ((Algebra.trace ℚ E ((∑ a : Fin r, ∑ i, ∑ j, n (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) / g) : ℚ) : ℂ)))) ∧
    {p | (G.S p).psi (m p) ≠ 1 ∨ (G.S p).psi' (m p) ≠ 1}.Finite := by
  have hp : ∀ p, (G.S p).psi (m p) = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f a.succ) i * G.Hm i j * sig (G.es a j)) / g))) := fun p =>
    psiOf_eq A G p (δ p) g hg (h1 p) (h2 p) n (m p) (hx p) (G.S p).f (G.S p).es G.f G.es
      (G.f_eq p) (G.es_eq p)
  have hp' : ∀ p, (G.S p).psi' (m p) = (A.loc p).psiE ((A.loc p).ιE
      (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) / g))) := fun p =>
    psiOf_eq A G p (δ p) g hg (h1 p) (h2 p) n (m p) (hx p) (G.S p).f' (G.S p).es' G.f' G.es'
      (G.f'_eq p) (G.es'_eq p)
  obtain ⟨s1, e1⟩ := GlobalTheory.AddCharProduct.finprod_psiE_eq_exp_trace hCM sig hsig A.loc
    (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f a.succ) i * G.Hm i j * sig (G.es a j)) / g))
  obtain ⟨s2, e2⟩ := GlobalTheory.AddCharProduct.finprod_psiE_eq_exp_trace hCM sig hsig A.loc
    (-((∑ a : Fin r, ∑ i, ∑ j, n (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) / g))
  refine ⟨?_, ?_, ?_⟩
  · simp only [hp]
    rw [e1, map_neg, Rat.cast_neg, mul_neg]
  · simp only [hp']
    rw [e2, map_neg, Rat.cast_neg, mul_neg]
  · refine (s1.union s2).subset ?_
    intro p hq
    rcases hq with hq | hq
    · left
      simpa [Function.mem_mulSupport, hp p] using hq
    · right
      simpa [Function.mem_mulSupport, hp' p] using hq

end GlobalTheory.HL.PhaseProduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.QuadricCharacterLeakSharesFiniteStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadric_character_leak_shares_finite : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (J : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (N : ℕ) (R : Finset S.V) (Z : S.V → Prop), S.a + 1 ≤ N → (∀ u, Z u ↔ ∃ c : 𝒪[F], S.h u u = algebraMap F E ((S.ϖ : F) ^ S.a * c)) → (∀ u ∈ R, u ∈ Λ ∧ u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)) → (∀ u ∈ Λ, u ∈ perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J) → ∃! w, w ∈ R ∧ ∃ y ∈ Λ, u - w = algebraMap F E ((S.ϖ : F) ^ N) • y) → |((R.filter Z).card : ℝ) - R.card / (S.q : ℝ) ^ S.a| ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) ∧ (((R.filter fun u => Z u ∧ ¬ ∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1).card : ℝ) ≤ 16 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a)) ∧ ∀ y : S.V, (∀ u ∈ R, algebraMap F E ((S.ϖ : F) ^ N) * S.h y u ∈ L.O) → (∃ u ∈ R, L.psi0 (S.h y u) ≠ 1) → ‖∑ u ∈ R.filter Z, L.psi0 (S.h y u)‖ ≤ 8 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * (R.card / (S.q : ℝ) ^ S.a) := by
  first | exact @GlobalTheory.HL.QuadricShare.shares | exact GlobalTheory.HL.QuadricShare.shares | (intros; apply GlobalTheory.HL.QuadricShare.shares <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfAdjointIdempotentPosType
section
noncomputable section

namespace GlobalTheory.RowLev.GroupAlgPos

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

variable {Q : Type} [Group Q]

theorem coeff_mul_eq_sum [Fintype Q] (a b : MonoidAlgebra ℂ Q) (q : Q) :
    (a * b).coeff q = ∑ x, a.coeff x * b.coeff (x⁻¹ * q) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]

def adj [Finite Q] (a : MonoidAlgebra ℂ Q) : MonoidAlgebra ℂ Q :=
  MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun q => star (a.coeff q⁻¹))

theorem adj_coeff [Finite Q] (a : MonoidAlgebra ℂ Q) (q : Q) : (adj a).coeff q = star (a.coeff q⁻¹) := rfl

theorem adj_mul [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a * b) = adj b * adj a := by
  haveI := Fintype.ofFinite Q
  ext q
  rw [adj_coeff, coeff_mul_eq_sum, coeff_mul_eq_sum, star_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft q) _ _ fun x => ?_
  simp [adj_coeff, mul_comm, mul_assoc]

theorem adj_adj [Finite Q] (a : MonoidAlgebra ℂ Q) : adj (adj a) = a := by
  ext q; simp [adj_coeff]

theorem adj_sub [Finite Q] (a b : MonoidAlgebra ℂ Q) : adj (a - b) = adj a - adj b := by
  ext q; simp [adj_coeff]

theorem isSA_iff [Finite Q] (a : MonoidAlgebra ℂ Q) : IsSA a ↔ adj a = a := by
  constructor
  · intro h
    ext q
    rw [adj_coeff, h q, star_star]
  · intro h q
    have := adj_coeff a q⁻¹
    rw [h, inv_inv] at this
    exact this

theorem coeff_mul_adj_one [Fintype Q] (a : MonoidAlgebra ℂ Q) :
    (a * adj a).coeff 1 = ∑ x, a.coeff x * star (a.coeff x) := by
  rw [coeff_mul_eq_sum]
  simp only [adj_coeff, mul_one, inv_inv]

theorem eq_zero_of_coeff_mul_adj [Finite Q] (a : MonoidAlgebra ℂ Q) (h : (a * adj a).coeff 1 = 0) : a = 0 := by
  haveI := Fintype.ofFinite Q
  rw [coeff_mul_adj_one] at h
  ext q
  have := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => mul_star_self_nonneg (a.coeff x)).1 h q (Finset.mem_univ _)
  simpa using this

theorem isSA_central [Finite Q] (z : MonoidAlgebra ℂ Q) (hz : z * z = z) (hc : ∀ a, z * a = a * z) : IsSA z := by
  have hs : adj z * adj z = adj z := by rw [← adj_mul, hz]
  have h0 : z - z * adj z = 0 := by
    apply eq_zero_of_coeff_mul_adj
    rw [adj_sub, adj_mul, adj_adj]
    have e1 : z * adj z * adj z = z * adj z := by rw [mul_assoc, hs]
    have e2 : z * (z * adj z) = z * adj z := by rw [← mul_assoc, hz]
    have e3 : z * adj z * (z * adj z) = z * adj z := by
      rw [mul_assoc, ← mul_assoc (adj z), ← hc (adj z), mul_assoc z (adj z), hs, e2]
    rw [sub_mul, mul_sub, mul_sub, e1, e2, e3]; simp
  have h1 : z = z * adj z := sub_eq_zero.1 h0
  rw [isSA_iff]
  conv_lhs => rw [h1, adj_mul, adj_adj]
  exact h1.symm

theorem coeff_inv_mul [Fintype Q] (a : MonoidAlgebra ℂ Q) (h : a * a = a) (hs : IsSA a) (x y : Q) :
    a.coeff (x⁻¹ * y) = ∑ q, star (a.coeff (q⁻¹ * x)) * a.coeff (q⁻¹ * y) := by
  conv_lhs => rw [← h, coeff_mul_eq_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun q => ?_
  simp [hs q, mul_assoc]

theorem posType [Finite Q] (a : MonoidAlgebra ℂ Q) (h : a * a = a) (hs : IsSA a) (m : ℕ) (x : Fin m → Q)
    (c : Fin m → ℂ) : 0 ≤ ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j) := by
  haveI := Fintype.ofFinite Q
  have e : ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j) =
      ∑ q : Q, star (∑ j, c j * a.coeff (q⁻¹ * x j)) * ∑ j, c j * a.coeff (q⁻¹ * x j) := by
    simp only [coeff_inv_mul a h hs (x _), star_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
    rw [star_mul']
    ring
  rw [e]
  exact Finset.sum_nonneg fun q _ => star_mul_self_nonneg _

theorem selfAdjoint_idempotent_posType : ∀ (Q : Type) [Group Q] [Finite Q],
    (∀ a : MonoidAlgebra ℂ Q, a * a = a → IsSA a →
      (∀ (m : ℕ) (x : Fin m → Q) (c : Fin m → ℂ), 0 ≤ ∑ i, ∑ j, star (c i) * c j * a.coeff ((x i)⁻¹ * x j)) ∧
        0 ≤ a.coeff 1 ∧ (a.coeff 1 = 0 → a = 0)) ∧
    (∀ z : MonoidAlgebra ℂ Q, z * z = z → (∀ a, z * a = a * z) → IsSA z) ∧
    ∀ a b : MonoidAlgebra ℂ Q, IsSA a → IsSA b → a * b = b * a → IsSA (a * b) := by
  intro Q _ _
  haveI := Fintype.ofFinite Q
  refine ⟨fun a h hs => ?_, isSA_central, fun a b ha hb hab => ?_⟩
  · have e : a * adj a = a := by rw [(isSA_iff a).1 hs, h]
    refine ⟨posType a h hs, ?_, fun h0 => eq_zero_of_coeff_mul_adj a (by rw [e, h0])⟩
    rw [← e, coeff_mul_adj_one]
    exact Finset.sum_nonneg fun q _ => mul_star_self_nonneg _
  · rw [isSA_iff] at ha hb ⊢
    rw [adj_mul, ha, hb, hab]

end GlobalTheory.RowLev.GroupAlgPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerCommensurableInvVolumeSmulComplement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem Frames.stab_commensurable_invVol_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ Λ : Submodule L.O S.V, IsLat L Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.complementReferenceCompactSubgroup ≠ 0 ∧ ∀ h ∈ S.H0, invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV (h • Λ)) = invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV Λ)) ∧ ∀ d Λ, S.IsTerm d Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV d) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV d).relIndex S.complementReferenceCompactSubgroup ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S
  obtain ⟨x, hdet, hspan, hH0, hstd, -⟩ := GlobalTheory.T.exists_nondegenerate_tuple_complement_fixer L r k S
  set Λs : Submodule L.O S.V := Submodule.span L.O (Set.range fun i => (Pi.single i 1 : S.V)) with hΛs
  have hK : S.complementReferenceCompactSubgroup = S.H0 ⊓ MulAction.stabilizer S.GLV Λs := rfl
  have comm : ∀ Λ Λ' : Submodule L.O S.V, IsLat L Λ → IsLat L Λ' →
      (S.H0 ⊓ MulAction.stabilizer S.GLV Λ').relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 :=
    fun Λ Λ' hΛ hΛ' => (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ' hΛ hΛ' S.H0).1
  have latPart : ∀ Λ : Submodule L.O S.V, IsLat L Λ →
      S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧
        (S.H0 ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.complementReferenceCompactSubgroup ≠ 0 := by
    intro Λ hΛ
    rw [hK]
    exact ⟨comm Λ Λs hΛ hstd, comm Λs Λ hstd hΛ⟩
  refine ⟨fun Λ hΛ => ⟨(latPart Λ hΛ).1, (latPart Λ hΛ).2, ?_⟩, ?_⟩
  · intro h hh
    have hfix : S.H0 = fixG L S.Hm (Submodule.span E (Set.range x)) := by rw [hspan]; exact hH0
    have hh' : h ∈ fixG L S.Hm (Submodule.span E (Set.range x)) := hfix ▸ hh
    have key := GlobalTheory.T.unitaryGroup_orthogonalComplement_unimodular L S.Hm S.herm (2 * r + 2) x hdet Λs Λ hstd hΛ h hh'
    rw [hK, hfix]
    exact key
  · intro d Λ hT
    have hΛ : IsLat L Λ := (GlobalTheory.T.hermitian_double_coset_term_basic_facts L r k S d Λ hT).1.1
    obtain ⟨hlo, Λ₂, hΛ₂, hhi⟩ := GlobalTheory.T.datum_stabilizer_between_lattice_stabilizers L r k S d Λ hT
    refine ⟨fun h0 => (latPart Λ₂ hΛ₂).1 (Subgroup.relIndex_eq_zero_of_le_right hhi h0),
      fun h0 => (latPart Λ hΛ).2 (Subgroup.relIndex_eq_zero_of_le_left hlo h0)⟩

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerFramesCoordinateLatticeGoodPlaceStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_framesCoordinateLattice_goodPlace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → S.a = 0 → ∀ d₀, S.IsTermW d₀ (coordLat S) 1 1 → S.St ⊓ MulAction.stabilizer S.GLV (coordLat S) = S.K0 := by
  first | exact @GlobalTheory.HL.StdStab.stab_coordLat | exact GlobalTheory.HL.StdStab.stab_coordLat | (intros; apply GlobalTheory.HL.StdStab.stab_coordLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransferenceCoverHolds
section
namespace GlobalTheory

theorem transferenceCover_holds : PI.TransferenceCover :=
  PI.Tr.transferenceCover_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitianStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_extension_totally_definite_hermitian : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ U U' : Submodule K V, ∀ e : U ≃ₗ[K] U', (∀ x y, h (e x : V) (e y : V) = h (x : V) (y : V)) → ∃ g ∈ isom h, ∀ x : U, g (x : V) = (e x : V)) ∧ ∀ U : Submodule K V, IsCompl U (perp h U) ∧ (hRes h U).IsSymm ∧ PD (hRes h U) ∧ perp h (perp h U) = U := by
  first | exact @GlobalTheory.Mass.Witt.witt_definite | exact GlobalTheory.Mass.Witt.witt_definite | (intros; apply GlobalTheory.Mass.Witt.witt_definite <;> assumption)
end

