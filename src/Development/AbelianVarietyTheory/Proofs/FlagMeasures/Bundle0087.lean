import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
import Formalism.HermitianLattices.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0074
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0066
import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMassEqOneOfSingleOrbitStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_mass_eq_one_of_single_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∃ Λ, S.IsTerm d Λ) → (∀ Λ Λ', S.IsTerm d Λ → S.IsTerm d Λ' → ∃ h ∈ S.St, Λ' = h • Λ) → (∀ Λ, S.IsTerm d Λ → P Λ ∧ S.mu Λ = 1 ∧ S.om d Λ = 1) → S.amp d P = 1 ∧ S.mass d P = 1 := by
  first | exact @GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit | exact GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit | (intros; apply GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DedekindZetaResidueLeSixteenLogRootDiscrPowStatement
section
open MeasureTheory NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dedekindZeta_residue_le_sixteen_log_rootDiscr_pow : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → 0 < dedekindZeta_residue K ∧ dedekindZeta_residue K ≤ (16 * Real.log (2 * Formalism.HermitianLatticesTheory.vInv K)) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K) := by
  first | exact @GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow | exact GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow | (intros; apply GlobalTheory.dedekindZeta_residue_le_log_rootDiscr_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Equality
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GoodPlace

theorem equality : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → S.gg = false → vE L S.ϖ S.G = 0 → (∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0) → (∀ d Λ, S.IsTerm d Λ → S.BBzero d Λ) ∧ S.Hp = 1 ∧ (S.ampSq fun _ _ => True) = S.nn ∧ ∀ d, (S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ hgg hG hD
  have hvth : S.vth = 0 := by simp [Frames.vth, hgg]
  have ha : S.a = 0 := by simp [Frames.a, hvth, hG]
  have hvD : S.vD = 0 := Finset.sum_eq_zero fun l _ => by
    split_ifs with h
    · exact hD l h.2
    · rfl
  have huniq := fun d Λ h => GlobalTheory.HL.UnimodTerm.term_unique L r k S d Λ h ha
  have key : ∀ d, ((S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1) ∧
      ENNReal.ofReal (‖S.amp d fun _ => True‖ ^ 2) = S.mass d fun _ => True := by
    intro d
    by_cases hex : ∃ Λ, S.IsTerm d Λ
    swap
    · have h0 : ∀ Λ, ¬ S.IsTerm d Λ := fun Λ h => hex ⟨Λ, h⟩
      simp [Frames.mass, Frames.amp, h0]
    obtain ⟨Λ₀, h₀⟩ := hex
    obtain ⟨-, -, hDO, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ₀ h₀
    obtain ⟨-, -, -, -, hDu, -⟩ := GlobalTheory.FrameBasic.main L r k S
    obtain ⟨-, -, -, hvu⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
    have hunit : ∀ l, S.D l ≠ 0 → S.D l ∈ L.O ∧ ∃ y ∈ L.O, S.D l * y = 1 := by
      intro l hl
      refine ⟨hDO l, ?_⟩
      obtain ⟨e, he⟩ := GlobalTheory.UnramOrder.exists_norm L (hDO l)
      have he0 : (e : F) ≠ 0 := fun h0 => by
        rw [h0, map_zero] at he
        apply hl
        rw [← L.cj_cj (S.D l), (hDu l hl).mul_right_eq_zero.1 he, map_zero]
      obtain ⟨u, hu⟩ := hvu _ he0
      rw [← he, hD l hl, zpow_zero, one_mul] at hu
      refine ⟨L.cj (S.D l) * algebraMap F E (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F),
        L.O.mul_mem (GlobalTheory.UnramOrder.cj_mem L (hDO l))
          ((GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 (Subtype.property _)), ?_⟩
      rw [← mul_assoc, he, ← map_mul, hu, ← Subring.coe_mul, Units.mul_inv]
      simp
    obtain ⟨hC0, hw0, hall⟩ := GlobalTheory.HL.GoodClass.one_class L r k S hgg hunit
    set C0 := S.frameCls S.f S.f' with hC0def
    have hact := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d
    have hint : ∀ Λ, S.IsTerm d Λ → S.IsIntCls (S.Fr d Λ) := fun Λ h =>
      (TermBasic.term_basic L r k S d Λ h).2.2.2.2.2.2.1

    have hm : (S.mass d fun _ => True) = 0 ∨ (S.mass d fun _ => True) = 1 := by
      rw [mass_eq_sumCls L r k S d _ (fun _ _ _ _ _ => trivial)]
      unfold Frames.sumCls
      let o₀ : MulAction.orbitRel.Quotient S.St (Set S.FrP) := Quotient.mk _ C0
      rw [tsum_eq_single o₀ (fun o ho => if_neg fun hI => ho (by
        obtain ⟨h, hh, e⟩ := hall _ hI
        rw [← Quotient.out_eq o]
        exact Quotient.sound ⟨⟨h, hh⟩, e.symm⟩))]
      split_ifs with hI
      swap
      · exact Or.inl rfl
      obtain ⟨h, hh, e⟩ := hall _ hI
      have hw : S.wC o₀.out = 1 := by
        rw [e, ((volSt L r k S).2 C0 hC0.1).2.2.2 h hh, hw0]
      rw [hw, ENNReal.ofReal_one, one_mul]
      have hs : ({Λ | S.IsTerm d Λ ∧ True ∧ S.Fr d Λ = o₀.out} : Set (Submodule L.O S.V)).Subsingleton :=
        fun Λ hΛ Λ' hΛ' => (huniq d Λ' hΛ'.1).2 Λ hΛ.1 (hΛ.2.2.trans hΛ'.2.2.symm)
      unfold Frames.nT
      beta_reduce
      rcases hs.eq_empty_or_singleton with h1 | ⟨x, h1⟩
      · left; rw [h1]; simp
      · right; rw [h1]; simp
    refine ⟨hm, ?_⟩

    let o₁ : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V) := Quotient.mk _ Λ₀
    have hone : ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o ≠ o₁ →
        ¬ (S.IsTerm d o.out ∧ True) := by
      intro o ho hT
      apply ho
      obtain ⟨h, hh, e⟩ := hall _ (hint _ hT.1)
      obtain ⟨h', hh', e'⟩ := hall _ (hint _ h₀)
      have hmem : h * h'⁻¹ ∈ S.St := S.St.mul_mem hh (S.St.inv_mem hh')
      have hA := hact Λ₀ h₀ _ hmem
      have e2 : (h * h'⁻¹) • Λ₀ = o.out := (huniq d _ hT.1).2 _ hA.1 (by
        rw [hA.2.2.2.2.1, e', e, smul_smul, inv_mul_cancel_right])
      rw [← Quotient.out_eq o]
      exact Quotient.sound ⟨⟨_, hmem⟩, e2⟩
    have e1 : (S.mass d fun _ => True) =
        if S.IsTerm d o₁.out ∧ True then ENNReal.ofReal (S.mu o₁.out) else 0 := by
      unfold Frames.mass
      rw [tsum_eq_single o₁]
      · congr
      · exact fun o ho => if_neg (hone o ho)
    have e2 : (S.amp d fun _ => True) =
        if S.IsTerm d o₁.out ∧ True then (S.mu o₁.out : ℂ) * S.om d o₁.out else 0 := by
      unfold Frames.amp
      rw [tsum_eq_single o₁]
      · congr
      · exact fun o ho => if_neg (hone o ho)
    rw [e1] at hm ⊢
    rw [e2]
    by_cases hT : S.IsTerm d o₁.out ∧ True
    swap
    · simp only [if_neg hT]; simp
    simp only [if_pos hT] at hm ⊢
    have hom : ‖S.om d o₁.out‖ = 1 := by
      obtain ⟨p, hp⟩ := hT.1
      exact (WitIndep.witness_independence L r k S d _ _ _ hp).2.2.2.2
    have hmu : 0 ≤ S.mu o₁.out := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    rw [norm_mul, hom, mul_one, Complex.norm_real, Real.norm_of_nonneg hmu]
    rcases hm with h | h
    · rw [le_antisymm (ENNReal.ofReal_eq_zero.1 h) hmu]; simp
    · rw [ENNReal.ofReal_eq_one.1 h]; simp
  refine ⟨fun d Λ h => (huniq d Λ h).1, by simp [Frames.Hp, hvth, ha, hvD], ?_, fun d => (key d).1⟩
  unfold Frames.ampSq Frames.nn
  congr 1
  funext d
  exact (key d).2

end GlobalTheory.HL.GoodPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormal
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.MaxExists

open NumberField Matrix in
open scoped ENNReal Classical in
private lemma isIntLat_of_isUnimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K M)
    (hU : _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M) : _root_.GlobalTheory.Mass.IsIntLat h M := by
  unfold _root_.GlobalTheory.Mass.IsIntLat
  refine ⟨hL, ?_⟩
  unfold _root_.Formalism.HermitianLatticesTheory.IsIntegralLat
  intro x hx y hy
  unfold _root_.Formalism.HermitianLatticesTheory.IsUnimodular at hU
  have hy' : y ∈ _root_.Formalism.HermitianLatticesTheory.dual h M := by rw [hU]; exact hy
  exact (_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M y).1 hy' x hx

open NumberField Matrix in
open scoped ENNReal Classical in
theorem _root_.GlobalTheory.Mass.MaxExists.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → h.Nondegenerate → (∀ M : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h M → ∃ M', _root_.GlobalTheory.Mass.IsMaxLat h M' ∧ M ≤ M') ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M → _root_.GlobalTheory.Mass.IsMaxLat h M ∧ _root_.GlobalTheory.Mass.badP h M = ∅ ∧ _root_.GlobalTheory.Mass.lamMax h M = 1) ∧ (∀ (M : Submodule (𝓞 K) V) (n : ℕ), _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h M n → Submodule.IsLattice K M ∧ _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M ∧ Module.finrank K V = n) := by
  intro K V _ _ _ _ _ _ _ _ h hK hS hN
  have D := fun M hM => _root_.GlobalTheory.Mass.DiscOrder.main K V h hK hS hN M hM
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ n : ℕ, ∀ M : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h M →
        _root_.GlobalTheory.Mass.discN h M = n →
        ∃ M', _root_.GlobalTheory.Mass.IsMaxLat h M' ∧ M ≤ M' := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro M hM hn
        by_cases hmax : ∀ N : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h N → M ≤ N → N = M
        · exact ⟨M, by unfold _root_.GlobalTheory.Mass.IsMaxLat; exact ⟨hM, hmax⟩, le_rfl⟩
        · push_neg at hmax
          obtain ⟨N, hNi, hMN, hne⟩ := hmax
          obtain ⟨hidx0, hdisc⟩ := (D M hM).2.2.1 N hNi hMN
          have hidx1 : _root_.GlobalTheory.Mass.idxN N M ≠ 1 := by
            intro h1
            exact hne (le_antisymm (_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1) hMN)
          have hNpos : 0 < _root_.GlobalTheory.Mass.discN h N :=
            Nat.pos_of_ne_zero (D N hNi).1
          have hlt : _root_.GlobalTheory.Mass.discN h N < n := by
            rw [← hn, hdisc]
            have h2 : 2 ≤ _root_.GlobalTheory.Mass.idxN N M := by omega
            have h4 : 1 < _root_.GlobalTheory.Mass.idxN N M ^ 2 :=
              Nat.one_lt_pow (by norm_num) (by omega)
            calc _root_.GlobalTheory.Mass.discN h N
                = _root_.GlobalTheory.Mass.discN h N * 1 := (mul_one _).symm
              _ < _root_.GlobalTheory.Mass.discN h N * _root_.GlobalTheory.Mass.idxN N M ^ 2 :=
                  Nat.mul_lt_mul_of_pos_left h4 hNpos
          obtain ⟨M', hM', hNM'⟩ := ih _ hlt N hNi rfl
          exact ⟨M', hM', hMN.trans hNM'⟩
    exact fun M hM => key _ M hM rfl
  · intro M hL hU
    have hI := isIntLat_of_isUnimodular hL hU
    have hD1 : _root_.GlobalTheory.Mass.discN h M = 1 := ((D M hI).2.1).2 hU
    have hbad : _root_.GlobalTheory.Mass.badP h M = ∅ := by
      unfold _root_.GlobalTheory.Mass.badP
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hP
      refine (D M hI).2.2.2.2.1 P hP ?_
      rw [hD1, Nat.cast_one]
      exact fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
    refine ⟨?_, hbad, ?_⟩
    · unfold _root_.GlobalTheory.Mass.IsMaxLat
      refine ⟨hI, fun N hNi hMN => ?_⟩
      obtain ⟨_, hdisc⟩ := (D M hI).2.2.1 N hNi hMN
      rw [hD1] at hdisc
      have h1 : _root_.GlobalTheory.Mass.idxN N M ^ 2 = 1 :=
        Nat.eq_one_of_mul_eq_one_left hdisc.symm
      have h1' : _root_.GlobalTheory.Mass.idxN N M = 1 := by
        simpa using h1
      exact le_antisymm (_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1') hMN
    · unfold _root_.GlobalTheory.Mass.lamMax
      rw [hbad]
      exact finprod_mem_empty
  · intro M n hO
    exact ⟨_root_.ReciprocityTheory.ChartRestriction.L3.isLattice_of_ortho hO, _root_.ReciprocityTheory.ChartRestriction.L3.isUnimodular_of_ortho hO, _root_.ReciprocityTheory.ChartRestriction.L3.finrank_of_ortho hO⟩

end GlobalTheory.Mass.MaxExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveVectorNormNegHyperbolicPairStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_vector_norm_neg_hyperbolicPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], CMData F E → ∀ (S : HSpace E) (Λ : Submodule (𝓞 E) S.V), Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∃ x : 𝓞 E, (x : E) + star (x : E) = 1) → ∀ (e f : S.V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → S.hT e e = 0 → S.hT f f = 0 → S.hT e f = 1 → (∀ x ∈ c, x • e ∈ Λ) → (∀ y ∈ Λ, S.hT f y ∈ c) → ∀ T : ℕ, T ≠ 0 → ∃ z : S.V, z ∈ Submodule.span E {e, f} ∧ z ∈ Λ ∧ S.hT z z = -((T : ℕ) : E) ∧ ∀ γ : E, γ • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = γ := by
  first | exact @GlobalTheory.HypPrimVec.exists_primitive_norm_neg | exact GlobalTheory.HypPrimVec.exists_primitive_norm_neg | (intros; apply GlobalTheory.HypPrimVec.exists_primitive_norm_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataMassEqSumFrameClasses
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem sumData_mass_eq_sumCls : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ P : S.Datum → Submodule L.O S.V → Prop, (∀ h ∈ S.St, ∀ d Λ, S.IsTerm d Λ → P d Λ → P d (h • Λ)) → (S.sumData fun d => S.mass d (P d)) = (S.sumCls fun C => S.sumData fun d => S.nT d C (P d)) ∧ ∀ h ∈ S.St, ∀ d C, S.nT d (h • C) (P d) = S.nT d C (P d) := by
  intro F _ _ _ _ _ E _ _ _ L r k S P hP
  refine ⟨?_, fun h hh d C => ?_⟩
  · have e : (fun d => S.mass d (P d)) = fun d => S.sumCls fun C => S.nT d C (P d) :=
      funext fun d => mass_eq_sumCls L r k S d (P d) fun h hh Λ => hP h hh d Λ
    rw [e]
    unfold Frames.sumData Frames.sumCls
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun c => ?_
    split_ifs
    · exact tsum_congr fun o => mul_left_comm _ _ _
    · simp
  · unfold Frames.nT
    have e : ({Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = h • C} : Set (Submodule L.O S.V)) =
        (fun Λ => h • Λ) '' {Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = C} := by
      ext Λ
      constructor
      · rintro ⟨h1, h2, h3⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h⁻¹ (S.St.inv_mem hh)
        refine ⟨h⁻¹ • Λ, ⟨A.1, hP _ (S.St.inv_mem hh) d Λ h1 h2, ?_⟩, smul_inv_smul h Λ⟩
        rw [A.2.2.2.2.1, h3, inv_smul_smul]
      · rintro ⟨Λ, ⟨h1, h2, h3⟩, rfl⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h hh
        refine ⟨A.1, hP _ hh d Λ h1 h2, ?_⟩
        rw [A.2.2.2.2.1, h3]
    rw [e, (MulAction.injective h).encard_image]

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumEqOfSameLatticeStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDatum_eq_of_same_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d d' : LocNG.Datum P) (τ τ' : Term V M r), LocNG.IsTermOver P d τ → LocNG.IsTermOver P d' τ' → τ.abelian₂ = τ'.abelian₂ → d = d' := by
  first | exact @GlobalTheory.HL.LatUniq.datum_of_lattice | exact GlobalTheory.HL.LatUniq.datum_of_lattice | (intros; apply GlobalTheory.HL.LatUniq.datum_of_lattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDefectClassMemTraceFirstFrameSpan
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TraceRep

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E}

theorem hf_add {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_sub {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a - b) y = hf L Hm a y - hf L Hm b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_smul {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_zero {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    hf L Hm 0 y = 0 := by
  simp [hf]

theorem hf_neg_right {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a y : Fin n → E) :
    hf L Hm a (-y) = - hf L Hm a y := by
  simp [hf, Finset.sum_neg_distrib]

theorem hf_swap {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) (v w : Fin n → E) :
    hf L Hm w v = L.cj (hf L Hm v w) := by
  have h' : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun h i) j
  simp only [hf, map_sum, map_mul, L.cj_cj, h']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_swap_zero {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) {v w : Fin n → E}
    (h0 : hf L Hm v w = 0) : hf L Hm w v = 0 := by
  rw [hf_swap h, h0, map_zero]

variable {r k : ℕ} (S : Frames L r k)

theorem frame_perp (g : Fin (r + 1) → S.V) (T : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then T else 0)
    (n : S.GLV) (hn : n ∈ S.Nof g) (b : Fin (r + 1)) :
    n (g b) ∈ perp L S.Hm (S.spanTo g r) := by
  refine (hn.2.1 (g b)).2 ?_
  intro y hy
  apply hf_swap_zero S.herm.1
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, hi, rfl⟩ := hy
    rw [hg, if_neg]
    rintro ⟨rfl, -⟩
    simp at hi
  | zero => exact hf_zero _ _
  | add a c _ _ ha hc => rw [hf_add, ha, hc, add_zero]
  | smul c a _ ha => rw [hf_smul, ha, mul_zero]

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem mof_transport (Λ : Submodule L.O S.V) (Y : Submodule E S.V) (g g' g₁ g₁' : Fin (r + 1) → S.V)
    (x x' u : S.V) (h1 : ∀ b, g₁ b = g b - S.h (g b) u • x) (h1' : ∀ b, g₁' b = g' b + S.h (g' b) u • x')
    (hO : ∀ b, S.h (g' b) u ∈ L.O) (hΛ : algebraMap F E S.th⁻¹ • (x + x') ∈ Λ) (hY : x + x' ∈ Y)
    (m : S.V) (hm : m ∈ S.Mof g g') :
    ∃ y₁ ∈ Λ, y₁ ∈ Y ∧ m - S.h m u • x + y₁ ∈ S.Mof g₁ g₁' := by
  induction hm using Submodule.span_induction with
  | mem m hm =>
    rcases hm with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · refine ⟨0, Λ.zero_mem, Y.zero_mem, ?_⟩
      rw [add_zero, ← h1]
      exact Submodule.subset_span (Or.inl ⟨b, rfl⟩)
    · refine ⟨S.h (g' b) u • (algebraMap F E S.th⁻¹ • (x + x')), Λ.smul_mem ⟨_, hO b⟩ hΛ,
        Y.smul_mem _ (Y.smul_mem _ hY), ?_⟩
      have : algebraMap F E S.th⁻¹ • (g' b - g b) - S.h (algebraMap F E S.th⁻¹ • (g' b - g b)) u • x +
          S.h (g' b) u • (algebraMap F E S.th⁻¹ • (x + x')) = algebraMap F E S.th⁻¹ • (g₁' b - g₁ b) := by
        rw [h1, h1']
        simp only [Frames.h, hf_smul, hf_sub]
        module
      simp only []
      rw [this]
      exact Submodule.subset_span (Or.inr ⟨b, rfl⟩)
  | zero =>
    refine ⟨0, Λ.zero_mem, Y.zero_mem, ?_⟩
    simp [Frames.h, hf_zero]
  | add a c _ _ ha hc =>
    obtain ⟨y, hy, hy', ha⟩ := ha
    obtain ⟨z, hz, hz', hc⟩ := hc
    refine ⟨y + z, Λ.add_mem hy hz, Y.add_mem hy' hz', ?_⟩
    have : a + c - S.h (a + c) u • x + (y + z) = (a - S.h a u • x + y) + (c - S.h c u • x + z) := by
      simp only [Frames.h, hf_add]
      module
    rw [this]
    exact Submodule.add_mem _ ha hc
  | smul c a _ ha =>
    obtain ⟨y, hy, hy', ha⟩ := ha
    refine ⟨(c : E) • y, Λ.smul_mem c hy, Y.smul_mem _ hy', ?_⟩
    have : c • a - S.h (c • a) u • x + (c : E) • y = (c : E) • (a - S.h a u • x + y) := by
      change (c : E) • a - S.h ((c : E) • a) u • x + (c : E) • y = _
      simp only [Frames.h, hf_smul]
      module
    rw [this]
    exact Submodule.smul_mem _ c ha

theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

end GlobalTheory.HL.TraceRep

open GlobalTheory.HL.TraceRep in

theorem GlobalTheory.HL.TraceRep.class_from_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → ∀ y ∈ S.sat Λ₁, ∃ y₀ ∈ Λ, y₀ ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ y - y₀ ∈ S.M d Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hF x x' u s hmv hw Λ₁ hΛ₁ y hy
  obtain ⟨w, hwΛ, hwW, huw⟩ := hw
  obtain ⟨hsx, -, -, -, -, -, -, hux, hux', hxX, hxX'⟩ :=
    GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties L r k S j β βJ d Λ hT hF x x' u s hmv
  obtain ⟨n₀, hn₀, n₀', hn₀', n'', hn'', -, e1, e2, e3, e4, hW₁⟩ :=
    GlobalTheory.T.move_lattice_isTerm_same_datum_with_witnesses L r k S j β βJ d Λ hT hF x x' u s hmv
  obtain ⟨hSD, hW, hMs, -, hf', -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hlev := (GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound L r k S d Λ hT).2.2.2.2.2.2.2.2.2.2
  have hΛe : n₀⁻¹ • Λ = Λ₁ := SetLike.coe_injective (e4.trans hΛ₁.symm)
  rw [hΛe] at hW₁
  have hM₁ := (GlobalTheory.HL.WitIndep.witness_independence L r k S d Λ₁ _ _ hW₁).2.1
  obtain ⟨hx, hx', ⟨t, ht, hte⟩, -, huΛ, huY, -⟩ := hmv
  have hH := S.herm.1
  have hint : ∀ a ∈ Λ, ∀ b ∈ Λ, S.h a b ∈ L.O := fun a ha b hb => (hSD.2 b).2 hb a ha
  have hp := frame_perp S S.f _ S.gram _ hW.2.2.1
  have hp' := frame_perp S S.f' _ S.gram' _ hW.2.2.2.1
  have hxME : x ∈ S.ME :=
    Submodule.mem_sup_left (spanTo_mono S S.f (Nat.le_succ r) hxX)
  have hyME : y ∈ S.ME := hy.2
  have hyΛ : eich L S.Hm x u s y ∈ Λ := by
    have : y ∈ (Λ₁ : Set S.V) := hy.1
    rw [hΛ₁] at this
    exact this
  have hκ : hf L S.Hm y x ∈ L.O := by
    have h1 := hint _ hyΛ _ hwΛ
    have h2 : hf L S.Hm y w = 0 := hf_swap_zero hH (hwW y hyME)
    have h3 : hf L S.Hm x w = 0 := hf_swap_zero hH (hwW x hxME)
    have h4 : hf L S.Hm u w = 1 := huw
    simp only [Frames.h, eich, hf_sub, hf_add, hf_smul, h2, h3, h4] at h1
    have := L.O.neg_mem h1
    simpa using this
  have hbΛ : y + hf L S.Hm y u • x ∈ Λ := by
    have : y + hf L S.Hm y u • x = eich L S.Hm x u s y + hf L S.Hm y x • (u + s • x) := by
      simp [eich]
    rw [this]
    exact Λ.add_mem hyΛ (Λ.smul_mem ⟨_, hκ⟩ (Λ.add_mem huΛ hsx))
  have hbs : y + hf L S.Hm y u • x ∈ S.sat Λ :=
    ⟨hbΛ, S.ME.add_mem hyME (S.ME.smul_mem _ hxME)⟩
  obtain ⟨y₀, hy₀Y, hm⟩ := (hlev _ hbs (j + 1)).1 (hF.2.2.1 _ hbs)
  have hy₀Λ : y₀ ∈ Λ := by
    have := Λ.sub_mem hbΛ (hMs hm).1
    simpa using this
  have hfrΛ : ∀ b, S.fr' d Λ b ∈ Λ := fun b =>
    (hf' (r + 1) le_rfl _).2 (Submodule.subset_span ⟨b, b.2, rfl⟩) |>.1
  have hth : algebraMap F E S.th⁻¹ • (x + x') ∈ Λ := by
    rw [hte, smul_smul, ← map_mul, inv_mul_cancel₀ (th_ne S), map_one, one_smul]
    exact ht
  obtain ⟨y₁, hy₁Λ, hy₁Y, hm₁⟩ := mof_transport S Λ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1))
    (S.fr d Λ) (S.fr' d Λ) (fun b => (n₀⁻¹ * (S.wit d Λ).1) (S.f b))
    (fun b => (n'' * n₀' * (S.wit d Λ).2) (S.f' b)) x x' u
    (fun b => by
      change n₀⁻¹ (S.fr d Λ b) = _
      have h0 : hf L S.Hm (S.fr d Λ b) x = 0 := hp b x hxX
      rw [e1, eich, h0, hf_neg_right]
      simp [Frames.h, sub_eq_add_neg])
    (fun b => by
      change n'' (n₀' (S.fr' d Λ b)) = _
      have h0 : hf L S.Hm (S.fr' d Λ b) x' = 0 := hp' b x' hxX'
      rw [e3 (n₀' (S.fr' d Λ b)) ((hn₀'.2.1 _).2 (hp' b)), e2, eich, h0]
      simp [Frames.h])
    (fun b => hint _ (hfrΛ b) _ huΛ) hth (Submodule.add_mem_sup hx hx') _ hm
  refine ⟨y₀ - y₁, Λ.sub_mem hy₀Λ hy₁Λ, Submodule.sub_mem _ hy₀Y hy₁Y, ?_⟩
  rw [hM₁]
  have h5 : hf L S.Hm x u = 0 := hf_swap_zero hH hux
  have h6 : hf L S.Hm y₀ u = 0 := hf_swap_zero hH (huY y₀ hy₀Y)
  have : y - (y₀ - y₁) = y + hf L S.Hm y u • x - y₀ - S.h (y + hf L S.Hm y u • x - y₀) u • x + y₁ := by
    simp only [Frames.h, hf_sub, hf_add, hf_smul, h5, h6]
    module
  rw [this]
  exact hm₁
end

