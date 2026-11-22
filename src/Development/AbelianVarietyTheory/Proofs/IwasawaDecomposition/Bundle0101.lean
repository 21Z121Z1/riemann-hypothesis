import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKsOfFinExt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem finiteDimensional_Ks_of_finExt {l : ℕ} [Fact l.Prime] (K : FinExt l) (s : ℕ) :
    FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h0 : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  have hfin : Finite ↥{x : Om l | x ^ (l ^ s) = 1} := by
    apply Set.Finite.to_subtype
    refine (Multiset.finite_toSet (Polynomial.nthRoots (l ^ s) (1 : Om l))).subset ?_
    intro x hx
    exact (Polynomial.mem_nthRoots hpos).2 hx
  have h1 : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  unfold Ks
  exact IntermediateField.finiteDimensional_sup _ _

theorem exists_good_situation (l : ℕ) [Fact l.Prime] :
    ∀ (K : FinExt l) (s : ℕ), 1 ≤ s → (l = 2 → 2 ≤ s) → K.1 ≤ Ks K s →
      ∃ L0 : FinExt l, ∀ LL : FinExt l, L0.1 ≤ LL.1 → Good K s LL := by
  intro K s h1 h2 h3
  have := finiteDimensional_Ks_of_finExt K s
  refine ⟨⟨IntermediateField.normalClosure ℚ_[l] ↥(Ks K s) (Om l), inferInstance⟩,
    fun LL hL => ⟨h1, h2, h3, fun τ x => hL ?_⟩⟩
  exact AlgHom.fieldRange_le_normalClosure τ ⟨x, rfl⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIndexUnitIdlSup
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.UnitIndex

variable (L : Type) [Field L] [NumberField L]

def finIdele : Ideles L →* (FiniteAdeleRing (𝓞 L) L)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def idealHom : (FiniteAdeleRing (𝓞 L) L)ˣ →* FractionalIdeal (𝓞 L)⁰ L where
  toFun := GlobalTheory.Idele.idealOf
  map_one' := GlobalTheory.Idele.idealOf_one
  map_mul' := GlobalTheory.Idele.idealOf_mul

def classHom : Ideles L →* ClassGroup (𝓞 L) :=
  (ClassGroup.mk L).comp ((idealHom L).comp (finIdele L)).toHomUnits

theorem ker_classHom_le : (classHom L).ker ≤ unitIdl L ⊔ (diagUnits L).range := by
  intro a ha
  have h1 : ClassGroup.mk L (((idealHom L).comp (finIdele L)).toHomUnits a) = 1 := ha
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  have hx' : GlobalTheory.Idele.idealOf (finIdele L a) = FractionalIdeal.spanSingleton (𝓞 L)⁰ x := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))
  have hd : finIdele L (diagUnits L (Units.mk0 x hx0)) =
      FiniteAdeleRing.unitEmbedding (𝓞 L) L (Units.mk0 x hx0) := Units.ext rfl
  have hu : a * (diagUnits L (Units.mk0 x hx0))⁻¹ ∈ unitIdl L := by
    refine (GlobalTheory.Idele.smul_eq_self_iff (finIdele L (a * (diagUnits L (Units.mk0 x hx0))⁻¹))
      (I := 1) one_ne_zero).1 ?_
    rw [GlobalTheory.Idele.smul_one_eq, map_mul, map_inv, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hd,
      GlobalTheory.Idele.idealOf_unitEmbedding, hx']
    exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)
  have : a = a * (diagUnits L (Units.mk0 x hx0))⁻¹ * diagUnits L (Units.mk0 x hx0) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup hu ⟨_, rfl⟩

open Classical in

theorem finiteIndex_unitIdl_sup : ∀ (L : Type) [Field L] [NumberField L],
    (unitIdl L ⊔ (diagUnits L).range).FiniteIndex := by
  intro L _ _
  have : (classHom L).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.finiteIndex_of_le (ker_classHom_le L)

end GlobalTheory.Mem.UnitIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Filter Topology

namespace GlobalTheory.Mem.UnrAe

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (Neutral.B1.finiteSingle L v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Function.update (fun _ => 1) v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Function.update_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_const.update v continuous_id
  have := (RestrictedProduct.continuous_inclusion hle).comp hf
  exact this

theorem continuous_localIdele (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finSingle v)

theorem tendsto_finSingle (y : ∀ v : HeightOneSpectrum (𝓞 L), v.adicCompletion L) (hy : ∀ v, Valued.v (y v) ≤ 1) :
    Tendsto (fun v => Neutral.B1.finiteSingle L v (y v)) cofinite (𝓝 1) := by
  classical
  let A : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w => w.adicCompletionIntegers L
  let o : ∀ w, A w := fun w => ⟨1, one_mem (w.adicCompletionIntegers L)⟩
  let g : HeightOneSpectrum (𝓞 L) → ∀ w, A w := fun v => Function.update o v ⟨y v, hy v⟩
  have hg : Tendsto g cofinite (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with v hv
    have h' : w ≠ v := fun h => hv h.symm
    exact (Function.update_of_ne h' _ _).symm
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  refine Tendsto.congr (fun v => ?_) h2
  apply Subtype.ext
  funext w
  show (g v w : w.adicCompletion L) = Function.update (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L)) v (y v) w
  by_cases hw : w = v
  · subst hw; simp [g]
  · simp [g, o, Function.update_of_ne hw]

theorem tendsto_localIdele (x : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ) (hx : ∀ v, IsUnitAt v (x v)) :
    Tendsto (fun v => localIdele L v (x v)) cofinite (𝓝 1) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  have h1 := tendsto_finSingle (fun v => (x v : v.adicCompletion L)) fun v => (hx v).le
  have h2 := tendsto_finSingle (fun v => (((x v)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L)) fun v => by
    have h : Valued.v (x v : v.adicCompletion L) = 1 := hx v
    rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]
  have h3 : Tendsto (fun v => ((localIdele L v (x v) : Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h1
  have h4 : Tendsto (fun v => (((localIdele L v (x v))⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)) cofinite (𝓝 1) :=
    (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h2
  exact h3.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h4)

theorem isUnitAt_pow {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) (m : ℕ) :
    IsUnitAt v (x ^ m) := by
  unfold IsUnitAt at *
  rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]

theorem finite_ramified (χ : HChar L) : {v | ¬ χ.UnrAt v}.Finite := by
  have h : ∀ v, ∃ x : (v.adicCompletion L)ˣ, IsUnitAt v x ∧
      (‖((χ.loc v x : ℂˣ) : ℂ) - 1‖ < 1 / 2 → χ.UnrAt v) := fun v => by
    by_contra hc
    push Not at hc
    refine (hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
    rw [← Units.val_pow_eq_pow_val, ← map_pow]
    exact (hc _ (isUnitAt_pow hx m)).1
  choose x hx hx' using h
  have hc : Continuous fun a : Ideles L => ‖((χ.1 a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp χ.2.1).sub continuous_const).norm
  have h1 := (hc.tendsto 1).comp (tendsto_localIdele x hx)
  have h2 := h1.eventually_lt_const (u := 1 / 2) (by simp)
  exact eventually_cofinite.1 (h2.mono fun v hv => hx' v hv)

theorem exists_levelLe (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) : ∃ n, χ.LevelLe v n := by
  have hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp (χ.2.1.comp (continuous_localIdele v))).sub continuous_const).norm
  have h0 : {a : (v.adicCompletion L)ˣ | ‖((χ.loc v a : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat, fun x hx hx1 => ?_⟩
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
  have h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1) := by ring
      rw [e]
      refine Valuation.map_add_le _ ?_ ih
      rw [map_mul, map_pow, hx', one_pow, one_mul]
  refine (h1.trans hx1).trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)

open Classical in

theorem unr_ae_and_level : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), {v | ¬ χ.UnrAt v}.Finite ∧ ∀ v, ∃ n, χ.LevelLe v n :=
  fun _ _ _ χ => ⟨finite_ramified χ, exists_levelLe χ⟩

end GlobalTheory.Mem.UnrAe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.HostCM

theorem valuation_eq_of_unram (K : Type) [Field K] [NumberField K] [IsCMField K]
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (P : HeightOneSpectrum (𝓞 K)) (x : maximalRealSubfield K) :
    P.valuation K (algebraMap (maximalRealSubfield K) K x) =
      (P.under (𝓞 (maximalRealSubfield K))).valuation (maximalRealSubfield K) x := by
  have hp := P.isPrime
  have hp' := (P.under (𝓞 (maximalRealSubfield K))).isPrime
  have : P.asIdeal.LiesOver (P.under (𝓞 (maximalRealSubfield K))).asIdeal := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[maximalRealSubfield K] K)
    (P.under (𝓞 (maximalRealSubfield K))).asIdeal P.asIdeal
  have h1 : Nat.card (P.asIdeal.inertia (K ≃ₐ[maximalRealSubfield K] K)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_mem _⟩⟩⟩
    have key : ∀ z : P.asIdeal.inertia (K ≃ₐ[maximalRealSubfield K] K),
        (z : K ≃ₐ[maximalRealSubfield K] K) = 1 := by
      intro z
      rcases Eta.cases K z.1 with hz | hz
      · exact hz
      · exfalso
        have hm := AddSubgroup.mem_inertia.mp z.2
        rw [hz] at hm
        exact hunr P.asIdeal hp P.ne_bot hm
    rw [key x, key y]
  rw [h1, Ideal.ramificationIdxIn_eq_ramificationIdx _ P.asIdeal (K ≃ₐ[maximalRealSubfield K] K)] at hcard
  rw [← HeightOneSpectrum.valuation_liesOver K (P.under (𝓞 (maximalRealSubfield K))) P x,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (P.under (𝓞 (maximalRealSubfield K))).ne_bot, ← hcard, pow_one]

open Classical in

theorem host_cm_embedding_properties : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ c : H.E ≃ₐ[H.F] H.E, (∀ x, c x = H.conj x) ∧ (IsTotallyReal H.F ∧ IsTotallyComplex H.E ∧ Module.finrank H.F H.E = 2 ∧ c ≠ 1 ∧ Function.Bijective fun g => InfinitePlace.mk (embPsi H g)) ∧ (∀ (P : HeightOneSpectrum (𝓞 H.E)) (k : (H.F)ˣ), ordF P (upF H.F k) = ordF (P.under (𝓞 H.F)) k) ∧ (∀ g : R.Psi, embPsi H g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)) ∧ Fintype.card (R.Psi) = R.f := by
  intro R H
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  have hmem : ∀ g : R.Psi, embPsi H g ∈ H.cmType := fun g => ((factEmb R H).2 g).2 g.2
  have hT := H.der.cmType.1
  refine ⟨IsCMField.complexConj H.E, hc, ⟨inferInstance, inferInstance,
    Algebra.IsQuadraticExtension.finrank_eq_two _ _, IsCMField.complexConj_ne_one _,
    ?_, ?_⟩, ?_, hmem, ?_⟩
  · intro g g' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact Subtype.ext ((factEmb R H).1.1 h)
    · have h' := hmem g'
      rw [← h] at h'
      exact absurd h' ((hT _).1 (hmem g))
  · intro w
    by_cases hw : w.embedding ∈ H.cmType
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 w.embedding
      refine ⟨⟨g, ((factEmb R H).2 g).1 (hg ▸ hw)⟩, ?_⟩
      show InfinitePlace.mk (H.emb g) = w
      rw [hg, InfinitePlace.mk_embedding]
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 (ComplexEmbedding.conjugate w.embedding)
      have hw' : ComplexEmbedding.conjugate w.embedding ∈ H.cmType := by
        by_contra h'
        exact hw ((hT _).2 h')
      refine ⟨⟨g, ((factEmb R H).2 g).1 (hg ▸ hw')⟩, ?_⟩
      show InfinitePlace.mk (H.emb g) = w
      rw [hg, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  · intro P k
    have := valuation_eq_of_unram H.E (fun P hP h0 hx => H.der.unramEF P hP h0 fun x => by
      have e : H.conj • x = IsCMField.complexConj H.E • x := Subtype.ext (hc x).symm
      rw [e]
      exact hx x) P k
    unfold ordF
    rw [← this]
    rfl
  · rw [← Nat.card_eq_fintype_card]
    exact (factCardPsi R H).1

open Classical in

theorem host_cm : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ c : H.E ≃ₐ[H.F] H.E, (∀ x, c x = H.conj x) ∧ CMData H.F c (embPsi H) ∧ (∀ (P : HeightOneSpectrum (𝓞 H.E)) (k : (H.F)ˣ), ordF P (upF H.F k) = ordF (P.under (𝓞 H.F)) k) ∧ (∀ g : R.Psi, embPsi H g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)) ∧ Fintype.card (R.Psi) = R.f := by
  intro R H
  obtain ⟨c, hc, ⟨h1, h2, h3, h4, h5⟩, h⟩ := host_cm_embedding_properties R H
  exact ⟨c, hc, ⟨h1, h2, h3, h4, h5⟩, h⟩

end GlobalTheory.Mem.HostCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Filter Topology

namespace GlobalTheory.Mem.LocTriv

variable {L : Type} [Field L] [NumberField L]

theorem tendsto_finiteAdele {ι : Type} {l : Filter ι} (f : ι → FiniteAdeleRing (𝓞 L) L) (b : FiniteAdeleRing (𝓞 L) L)
    (hf : ∀ i v, f i v ∈ v.adicCompletionIntegers L) (hb : ∀ v, b v ∈ v.adicCompletionIntegers L)
    (h : ∀ v, Tendsto (fun i => f i v) l (𝓝 (b v))) : Tendsto f l (𝓝 b) := by
  first
  | exact @_root_.GlobalTheory.TendstoOfIntegrals.target_check
  | exact _root_.GlobalTheory.TendstoOfIntegrals.target_check
  | (apply _root_.GlobalTheory.TendstoOfIntegrals.target_check <;> assumption)
  | (intros; apply _root_.GlobalTheory.TendstoOfIntegrals.target_check <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TendstoOfIntegrals.target_check <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TendstoOfIntegrals.target_check ..)

def ev (v : HeightOneSpectrum (𝓞 L)) : AdeleRing (𝓞 L) L →* v.adicCompletion L where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def part (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : Ideles L :=
  ∏ v ∈ S, localIdele L v (Units.map (ev v) a)

theorem part_inv (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : (part a S)⁻¹ = part a⁻¹ S := by
  simp only [part, map_inv, Finset.prod_inv_distrib]

theorem ev_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ev v (localIdele L v x : AdeleRing (𝓞 L) L) = x := by
  classical
  have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem ev_local_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ev w (localIdele L v x : AdeleRing (𝓞 L) L) = 1 := by
  classical
  have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem ev_part_mem (a : Ideles L) {S : Finset (HeightOneSpectrum (𝓞 L))} {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ S) :
    ev w (part a S : AdeleRing (𝓞 L) L) = ev w (a : AdeleRing (𝓞 L) L) := by
  rw [part, Units.coe_prod, map_prod, Finset.prod_eq_single_of_mem w hw (fun v _ hv => ev_local_ne hv.symm _),
    ev_local_self]
  rfl

theorem ev_part_not_mem (a : Ideles L) {S : Finset (HeightOneSpectrum (𝓞 L))} {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∉ S) : ev w (part a S : AdeleRing (𝓞 L) L) = 1 := by
  rw [part, Units.coe_prod, map_prod]
  exact Finset.prod_eq_one fun v hv => ev_local_ne (fun e : w = v => hw (e ▸ hv)) _

theorem part_fst (a : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : (part a S : AdeleRing (𝓞 L) L).1 = 1 := by
  have h : finPartI L (part a S) = part a S := by
    rw [part, map_prod]
    exact Finset.prod_congr rfl fun v _ => Units.ext rfl
  rw [← h]
  rfl

theorem tendsto_part_val {a : Ideles L} (ha : a ∈ unitIdl L) (h1 : (a : AdeleRing (𝓞 L) L).1 = 1) :
    Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L)) atTop (𝓝 (a : AdeleRing (𝓞 L) L)) := by
  have h2 : Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L).2) atTop (𝓝 (a : AdeleRing (𝓞 L) L).2) := by
    refine tendsto_finiteAdele _ _ (fun S v => ?_) (fun v => (ha v).le) fun v => ?_
    · show ev v (part a S : AdeleRing (𝓞 L) L) ∈ _
      by_cases hv : v ∈ S
      · rw [ev_part_mem a hv]
        exact (ha v).le
      · rw [ev_part_not_mem a hv]
        exact one_mem _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ({v} : Finset _)] with S hS
      exact (ev_part_mem a (hS (Finset.mem_singleton_self v))).symm
  have h3 : Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L).1) atTop (𝓝 (a : AdeleRing (𝓞 L) L).1) := by
    rw [h1]
    exact tendsto_const_nhds.congr fun S => (part_fst a S).symm
  exact h3.prodMk_nhds h2

theorem tendsto_part {a : Ideles L} (ha : a ∈ unitIdl L) (h1 : ∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) :
    Tendsto (part a) atTop (𝓝 a) := by
  have e : finPartI L a = a := finPartI_eq_self h1
  have e' : finPartI L a⁻¹ = a⁻¹ := by rw [map_inv, e]
  have t1 := tendsto_part_val ha (by rw [← e]; rfl)
  have t2 := tendsto_part_val ((unitIdl L).inv_mem ha) (by rw [← e']; rfl)
  simp only [← part_inv] at t2
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact t1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp t2)

open Classical in

theorem eq_one_of_local : ∀ (L : Type) [Field L] [NumberField L] (ψ : Ideles L →* ℂˣ), Continuous ψ → ∀ a : Ideles L, a ∈ unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ v (x : (v.adicCompletion L)ˣ), (x : v.adicCompletion L) = (a : AdeleRing (𝓞 L) L).2 v → ψ (localIdele L v x) = 1) → ψ a = 1 := by
  intro L _ _ ψ hψ a ha h1 hl
  have t := (hψ.tendsto a).comp (tendsto_part ha h1)
  have e : ψ ∘ part a = fun _ => 1 := funext fun S => by
    show ψ (part a S) = 1
    rw [part, map_prod]
    exact Finset.prod_eq_one fun v _ => hl v _ rfl
  rw [e] at t
  exact tendsto_nhds_unique t tendsto_const_nhds

end GlobalTheory.Mem.LocTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionUnflattenStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linComb_pow_section_unflatten : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  first | exact @GlobalTheory.SecPowUnflat.unflat | exact GlobalTheory.SecPowUnflat.unflat | (intros; apply GlobalTheory.SecPowUnflat.unflat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonVEqZeroIffMemRangeCrisIncl
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Pst

theorem monV_eq_zero_iff_mem_range_crisIncl {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (x : V ⊗[ℚ_[l]] Bst P) : monV P LL V x = 0 ↔ ∃ y, crisIncl P LL V y = x := by
  have h : Function.Exact (CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap (monSt P) := fun p =>
    (monSt_eq_zero_iff P p).trans ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  exact Module.Flat.lTensor_exact V h x

theorem mem_Dst_and_monV_eq_zero_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (x : V ⊗[ℚ_[l]] Bst P), (x ∈ Dst P ρ ∧ monV P ↥LL.1 V x = 0) ↔ x ∈ (Dcris (P.PD K) ρ).map (crisIncl P ↥LL.1 V) := by
  intro l _ P K LL V _ _ _ _ ρ x
  have key : ∀ y, crisIncl P ↥LL.1 V y ∈ Dst P ρ ↔ y ∈ Dcris (P.PD K) ρ := fun y => by
    rw [mem_Dst, Dcris, Submodule.mem_iInf]
    refine forall_congr' fun g => ?_
    rw [stRep_crisIncl, (crisIncl_injective P).eq_iff, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  rw [monV_eq_zero_iff_mem_range_crisIncl, Submodule.mem_map]
  constructor
  · rintro ⟨hx, y, rfl⟩
    exact ⟨y, (key y).mp hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(key y).mpr hy, y, rfl⟩

end GlobalTheory.Pst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitsCOfModEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr

open Classical in

theorem splitsC_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (p : ℕ), p.Prime →
    p ≡ 1 [MOD H.QS * H.q * H.d] → SplitsC H.E p := by
  intro R H p hp h
  have hd16 : H.d % 16 = 7 := H.hyp.2.2.2.1
  have hpos : 0 < H.QS * H.q * H.d := Nat.pos_of_ne_zero H.condN_ne_zero
  have hlt : 1 < H.QS * H.q * H.d :=
    lt_of_lt_of_le (by omega : 1 < H.d) (Nat.le_of_dvd hpos (dvd_mul_left _ _))
  refine (GlobalTheory.HostSplit.split_of_one_mod R H p hp ?_).1
  rw [h]
  exact Nat.mod_eq_of_lt hlt

end GlobalTheory.Mem.Chr
end

