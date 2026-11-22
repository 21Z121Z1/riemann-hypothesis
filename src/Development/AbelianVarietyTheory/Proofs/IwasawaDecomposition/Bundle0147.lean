import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
import Formalism.LocalToGlobal.Columns.HeckeInertComm
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0138
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0136

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicUnramifiedCompletedIntegers
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CycClosure

variable {l : ℕ} [Fact l.Prime]

theorem mem_clC {F : IntermediateField ℚ_[l] (PadicAlgCl l)} {x : ℂ_[l]} :
    x ∈ clC l F ↔ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖x‖ ≤ 1 := by
  simp only [clC, Subring.mem_inf]
  apply and_congr Iff.rfl
  change x ∈ PadicComplexInt l ↔ _
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem coe_clC (F : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    (clC l F : Set ℂ_[l]) =
      closure ((fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1}) := by
  have hc : IsClopen (Metric.closedBall (0 : ℂ_[l]) 1) :=
    IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have e : (fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1} =
      (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∩ Metric.closedBall 0 1 := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, h⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [mem_closedBall_zero_iff, PadicComplex.norm_extends]; exact h⟩
    · rintro ⟨⟨y, hy, rfl⟩, h⟩
      rw [mem_closedBall_zero_iff] at h
      exact ⟨y, ⟨hy, by rw [← PadicComplex.norm_extends]; exact h⟩, rfl⟩
  rw [e]
  apply Set.Subset.antisymm
  · intro x hx
    rw [SetLike.mem_coe, mem_clC] at hx
    exact hc.isOpen.closure_inter ⟨hx.1, by simpa using hx.2⟩
  · intro x hx
    have := closure_inter_subset_inter_closure _ _ hx
    rw [hc.isClosed.closure_eq] at this
    exact mem_clC.2 ⟨this.1, by simpa using this.2⟩

theorem clC_mono {F G : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : F ≤ G) {x : ℂ_[l]}
    (hx : x ∈ clC l F) : x ∈ clC l G :=
  mem_clC.2 ⟨closure_mono (Set.image_mono h) (mem_clC.1 hx).1, (mem_clC.1 hx).2⟩

theorem clC_props (LL : Loc.FinExt l) (F : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hF : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = F) :
    ∃ _ : IsDiscreteValuationRing ↥(clC l F),
      IsAlgClosed (IsLocalRing.ResidueField ↥(clC l F)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l F)) ↥(clC l F) ∧
      IsAdic (IsLocalRing.maximalIdeal ↥(clC l F)) ∧
      (∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) := by
  subst hF
  obtain ⟨O, hdvr, -, -, hdiv, hres, hcomp, hadic, hO⟩ := GlobalTheory.BigInt.exists_integers_completion l LL
  have e : O = clC l (LL.1 ⊔ Loc.MaximalUnramifiedExtension l) := SetLike.coe_injective (hO.trans (coe_clC _).symm)
  subst e
  exact ⟨hdvr, hres, hcomp, hadic, hdiv⟩

theorem muK_spec (k : ℕ) : FiniteDimensional ℚ_[l] ↥(muK l k) ∧
    ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ (l ^ k) ∧ muK l k = IntermediateField.adjoin ℚ_[l] {ζ} := by
  have hn : 0 < l ^ k := pow_pos (Fact.out : l.Prime).pos k
  haveI : NeZero (l ^ k) := ⟨hn.ne'⟩
  classical
  have hfin : ({x | x ^ (l ^ k) = 1} : Set (PadicAlgCl l)).Finite := by
    refine (Polynomial.nthRoots (l ^ k) (1 : PadicAlgCl l)).toFinset.finite_toSet.subset fun x hx => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hx
  haveI := hfin.to_subtype
  refine ⟨IntermediateField.finiteDimensional_adjoin fun x hx =>
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [show x ^ (l ^ k) = 1 from hx]⟩, ?_⟩
  have hdeg : (cyclotomic (l ^ k) (PadicAlgCl l)).degree ≠ 0 := by
    rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have hp : IsPrimitiveRoot ζ (l ^ k) := (isRoot_cyclotomic_iff).1 hζ
  refine ⟨ζ, hp, le_antisymm ?_ ?_⟩
  · rw [muK, IntermediateField.adjoin_le_iff]
    intro x hx
    have hx' : x ^ (l ^ k) = 1 := hx
    obtain ⟨i, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx'
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ) _
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin _ _ hp.pow_eq_one

end GlobalTheory.CycClosure

namespace GlobalTheory.CycClosure

theorem exists_cyclotomic_integers : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ), ∃ _ : IsDiscreteValuationRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), IsAlgClosed (IsLocalRing.ResidueField ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ (∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∀ y ∈ clC l (Kt l K₀ L ⊔ muK l k), ‖x‖ ≤ ‖y‖ → x / y ∈ clC l (Kt l K₀ L ⊔ muK l k)) ∧ muK l 0 = ⊥ ∧ (∃ T : Finset ℂ_[l], ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ Submodule.span ↥(clC l (Kt l K₀ L)) (T : Set ℂ_[l])) ∧ ∃ ζ ∈ clC l (Kt l K₀ L ⊔ muK l k), IsPrimitiveRoot ζ (l ^ k) ∧ ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ (p : Polynomial ↥(clC l (Kt l K₀ L))) (d : ↥(clC l (Kt l K₀ L))), d ≠ 0 ∧ x * (d : ℂ_[l]) = Polynomial.aeval ζ p := by
  intro l _ K₀ L k
  have hp : l.Prime := Fact.out
  obtain ⟨hfd, ζ, hζ, hmu⟩ := muK_spec (l := l) k
  let LL : Loc.FinExt l := ⟨K₀.1 ⊔ L.1 ⊔ muK l k, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  have hM : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = Kt l K₀ L ⊔ muK l k := by
    simp only [LL, Kt]; exact sup_right_comm _ _ _
  let L0 : Loc.FinExt l := ⟨K₀.1 ⊔ L.1, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  obtain ⟨hdvr, hres, hcomp, hadic, hdiv⟩ := clC_props LL _ hM
  obtain ⟨hdvr0, -, -, -, -⟩ := clC_props L0 (Kt l K₀ L) rfl
  have mu0 : muK l 0 = ⊥ := by
    rw [muK, eq_bot_iff, IntermediateField.adjoin_le_iff]
    intro x hx
    have : x = 1 := by simpa using hx
    rw [this]; exact one_mem _
  have hn : 0 < l ^ k := pow_pos hp.pos k
  have hint : IsIntegral ℚ_[l] ζ :=
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [hζ.pow_eq_one]⟩
  obtain ⟨n, Cb, hC⟩ := GlobalTheory.T.exists_coeff_bounded_in_closure_of_norm_le_one l (Kt l K₀ L) ζ hint
  have hB : ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ clC l (Kt l K₀ L ⊔ IntermediateField.adjoin ℚ_[l] {ζ}) := by
    intro x; rw [hmu]
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [← map_natCast (algebraMap (PadicAlgCl l) ℂ_[l])]
    refine lt_of_eq_of_lt (PadicComplex.norm_extends l (l : PadicAlgCl l)) ?_
    rw [GlobalTheory.UnramValue.norm_l]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (max Cb 1) by positivity) hl
  have cmem : ∀ c ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((Kt l K₀ L : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))),
      ‖c‖ ≤ Cb → (l : ℂ_[l]) ^ N * c ∈ clC l (Kt l K₀ L) := by
    intro c hc hcb
    refine mem_clC.2 ⟨map_mem_closure (continuous_const.mul continuous_id) hc ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨(l : PadicAlgCl l) ^ N * z, mul_mem (pow_mem (natCast_mem _ _) _) hz, ?_⟩
      simp
    · rw [norm_mul, norm_pow]
      have h1 : ‖c‖ ≤ max Cb 1 := hcb.trans (le_max_left _ _)
      have h2 : (0 : ℝ) < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      calc ‖(l : ℂ_[l])‖ ^ N * ‖c‖ ≤ ‖(l : ℂ_[l])‖ ^ N * max Cb 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 / max Cb 1 * max Cb 1 := mul_le_mul_of_nonneg_right hN.le h2.le
        _ = 1 := by field_simp
  set ζ' : ℂ_[l] := algebraMap (PadicAlgCl l) ℂ_[l] ζ with hζ'
  have hζn : ‖ζ‖ = 1 := by
    have := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  have hζB : ζ' ∈ clC l (Kt l K₀ L ⊔ muK l k) := by
    rw [hB]
    refine mem_clC.2 ⟨subset_closure ⟨ζ, (le_sup_right : IntermediateField.adjoin ℚ_[l] {ζ} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ), rfl⟩, ?_⟩
    exact ((PadicComplex.norm_extends l ζ).trans hζn).le
  have hAB : ∀ x ∈ clC l (Kt l K₀ L), x ∈ clC l (Kt l K₀ L ⊔ muK l k) := fun x hx => clC_mono le_sup_left hx
  have hlN : (l : ℂ_[l]) ^ N ∈ clC l (Kt l K₀ L) := pow_mem (natCast_mem _ _) _
  have rep : ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ c : Fin n → ℂ_[l],
      (∀ i, (l : ℂ_[l]) ^ N * c i ∈ clC l (Kt l K₀ L)) ∧ x = ∑ i, c i * ζ' ^ (i : ℕ) := by
    intro x hx
    rw [hB] at hx
    obtain ⟨c, hc, e⟩ := hC x (mem_clC.1 hx).1 (mem_clC.1 hx).2
    exact ⟨c, fun i => cmem _ (hc i).1 (hc i).2, e⟩
  refine ⟨hdvr, hres, hcomp, hadic, hdiv, mu0, ?_, ζ', hζB, hζ.map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective, ?_⟩
  · classical
    let g : Fin n → ℂ_[l] := fun i => ((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ)
    let P : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] := Submodule.span ↥(clC l (Kt l K₀ L)) (Set.range g)
    let B' : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] :=
      { carrier := (clC l (Kt l K₀ L ⊔ muK l k) : Set ℂ_[l])
        add_mem' := fun ha hb => add_mem ha hb
        zero_mem' := zero_mem _
        smul_mem' := fun a x hx => by
          rw [Subring.smul_def, smul_eq_mul]
          exact mul_mem (hAB _ a.2) hx }
    have hBP : B' ≤ P := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := rep x hx
      refine Submodule.sum_mem _ fun i _ => ?_
      have := Submodule.smul_mem P (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L)))
        (Submodule.subset_span ⟨i, rfl⟩ : g i ∈ P)
      convert this using 1
      rw [Subring.smul_def, smul_eq_mul]
      change c i * ζ' ^ (i : ℕ) = ((l : ℂ_[l]) ^ N * c i) * (((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ))
      field_simp
    haveI : IsNoetherian ↥(clC l (Kt l K₀ L)) ↥P :=
      isNoetherian_of_fg_of_noetherian P (Submodule.fg_span (Set.finite_range g))
    have hfg : B'.FG := by
      have h1 : (B'.comap P.subtype).FG := IsNoetherian.noetherian _
      have h2 := h1.map P.subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.2 hBP] at h2
    obtain ⟨T, hT⟩ := hfg
    exact ⟨T, fun x => by rw [hT]; rfl⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := rep x hx
    refine ⟨∑ i : Fin n, monomial (i : ℕ) (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L))),
      ⟨(l : ℂ_[l]) ^ N, hlN⟩, fun h => pow_ne_zero N hl0 (congrArg Subtype.val h), ?_⟩
    simp only [map_sum, aeval_monomial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change c i * ζ' ^ (i : ℕ) * (l : ℂ_[l]) ^ N = ((l : ℂ_[l]) ^ N * c i) * ζ' ^ (i : ℕ)
    ring

end GlobalTheory.CycClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersToCompletedUnramifiedCompositum
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.HeightCounting.ToClC

theorem norm_le_one_of_mem_OL (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (x : ↥(Loc.OL K)) :
    ‖((x : ↥K.1) : PadicAlgCl l)‖ ≤ 1 := by
  have h : IsIntegral ℤ_[l] ((x : ↥K.1) : PadicAlgCl l) :=
    (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).2 x.2
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral _))]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
  exact ((minpoly ℤ_[l] _).coeff n).2

theorem mem_clC_of_OL (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (y : ↥(Loc.OL K₀)) :
    algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) ∈ clC l (Kt l K₀ L) := by
  refine ⟨Subring.le_topologicalClosure _ ⟨((y : ↥K₀.1) : PadicAlgCl l), ?_, rfl⟩, ?_⟩
  · show ((y : ↥K₀.1) : PadicAlgCl l) ∈ Kt l K₀ L
    exact (le_sup_left.trans (le_sup_left : K₀.1 ⊔ L.1 ≤ _)) (y : ↥K₀.1).2
  · change algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) ∈ PadicComplexInt l
    rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, ← PadicComplex.coe_eq, PadicComplex.valuation_extends, ← NNReal.coe_le_one, PadicAlgCl.valuation_coe]
    exact norm_le_one_of_mem_OL l K₀ y

def toClC (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)) :=
  ((algebraMap (PadicAlgCl l) ℂ_[l]).comp (K₀.1.val.toRingHom.comp (Loc.OL K₀).val.toRingHom)).codRestrict _
    fun y => mem_clC_of_OL l K₀ L y

theorem exists_toClC : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l), ∃ f : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)),
    ∀ y, (f y : ℂ_[l]) = algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) :=
  fun l _ K₀ L => ⟨toClC l K₀ L, fun _ => rfl⟩

end GlobalTheory.HeightCounting.ToClC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
section
open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR.Datum

namespace GlobalTheory.Member

theorem exists_isInfFam_family : ∀ D : D7, ∃ θ : InfFam D, IsInfFam θ :=
  fun D => GlobalTheory.DualPairCompare.exists_infFam D

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity
section
open Formalism.BasicNotions Formalism.L2.Theta Formalism.IndefR MeasureTheory
open scoped ENNReal NNReal

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf_of_density {p q : ℕ} (μ : Measure (UpqT p q)) (hμ : μ.IsHaarMeasure) (c : ℝ≥0∞)
    (h0 : c ≠ 0) (ht : c ≠ ⊤) (hc : OmegaDensity μ c) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  have hm0 : minfDensity (p + q) ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top (by simp))
  have hmt : minfDensity (p + q) ≠ ⊤ := ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)
  have hne0 : minfDensity (p + q) / c ≠ 0 := ENNReal.div_ne_zero.2 ⟨hm0, ht⟩
  have hnet : minfDensity (p + q) / c ≠ ⊤ := ENNReal.div_ne_top hmt h0
  lift minfDensity (p + q) / c to ℝ≥0 using hnet with t htc
  refine ⟨t • μ, Measure.IsHaarMeasure.nnreal_smul μ (by exact_mod_cast hne0), ?_⟩
  have h := GlobalTheory.CompactDualUnique.omegaDensity_smul t hc
  rwa [htc, ENNReal.div_mul_cancel h0 ht] at h

theorem exists_isMinf_of_cd (h : Nonempty CDHaar) (p q : ℕ) : ∃ m : Measure (UpqT p q), Lev.IsMinf m := by
  obtain ⟨cd⟩ := h
  obtain ⟨c, h0, ht, hc, -⟩ := cd.trick p q
  exact exists_isMinf_of_density _ (cd.haar p q) c h0 ht hc

end GlobalTheory.MinfMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalDomainValuationCenter
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem valuativeChart_localise :
    ∀ (A B k : Type) [CommRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B] [Field k]
      (φ : B →+* k) (V : ValuationSubring k) (C : Subalgebra A B), RingHom.ker φ = maximalIdeal B →
      Algebra.FiniteType A C → IsIntegrallyClosed C → (∀ c ∈ C, V.valuation (φ c) ≤ 1) →
      (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a) →
      ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B),
        IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧
        (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧
        ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  intro A B k _ _ _ _ _ _ φ V C hker hft hic hle hfrac
  let ψ : C →+* V := (φ.comp C.val.toRingHom).codRestrict V
    (fun c => (V.valuation_le_one_iff _).1 (hle c c.2))
  let p : Ideal C := (maximalIdeal V).comap ψ
  have hmem : ∀ c : C, c ∈ p ↔ V.valuation (φ c) < 1 := by
    intro c
    exact V.valuation_lt_one_iff (ψ c)
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let D := Localization.AtPrime p
  haveI : IsDomain D := IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  have hval1 : ∀ y : p.primeCompl, V.valuation (φ (y : C)) = 1 := by
    intro y
    have h1 := hle (y : C) (y : C).2
    have h2 : ¬ V.valuation (φ (y : C)) < 1 := fun h => y.2 ((hmem _).2 h)
    exact le_antisymm h1 (not_lt.1 h2)
  have hunit : ∀ y : p.primeCompl, IsUnit (C.val (y : C)) := by
    intro y
    by_contra hnu
    have hm : ((y : C) : B) ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [← hker, RingHom.mem_ker] at hm
    have := hval1 y
    rw [hm, map_zero] at this
    exact zero_ne_one this
  let ι : D →ₐ[A] B := IsLocalization.liftAlgHom (M := p.primeCompl) (S := D) (f := C.val) hunit
  have hιalg : ∀ c : C, ι (algebraMap C D c) = c := by
    intro c
    simp [ι, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  have hrep : ∀ d : D, ∃ c : C, ∃ s : p.primeCompl, ((s : C) : B) * ι d = c ∧
      d * algebraMap C D s = algebraMap C D c := by
    intro d
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl d
    refine ⟨c, s, ?_, IsLocalization.mk'_spec _ _ _⟩
    have := (IsLocalization.lift_mk'_spec (M := p.primeCompl) (S := D) (hg := hunit) c
      (IsLocalization.lift hunit (IsLocalization.mk' D c s)) s).1 rfl
    simpa [ι, IsLocalization.liftAlgHom_apply] using this.symm
  have hvald : ∀ d : D, ∃ c : C, V.valuation (φ (ι d)) = V.valuation (φ c) ∧
      (d ∈ maximalIdeal D → c ∈ p) := by
    intro d
    obtain ⟨c, s, h1, h2⟩ := hrep d
    refine ⟨c, ?_, ?_⟩
    · rw [← h1, map_mul, Valuation.map_mul, hval1 s, one_mul]
    · intro hd
      have : algebraMap C D c ∈ maximalIdeal D := by
        rw [← h2]; exact Ideal.mul_mem_right _ _ hd
      have h3 : c ∈ (maximalIdeal D).under C := Ideal.mem_comap.2 this
      rwa [IsLocalization.AtPrime.comap_maximalIdeal D p] at h3
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, ι, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isIntegrallyClosed_of_isLocalization D p.primeCompl p.primeCompl_le_nonZeroDivisors
  · infer_instance
  · show Function.Injective (IsLocalization.lift hunit : D → B)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      have := congrArg (IsLocalization.lift (S := D) hunit) h
      simpa [IsLocalization.lift_eq] using this
    · intro h
      rw [Subtype.ext (show (x : B) = y from h)]
  · intro d
    obtain ⟨c, hc, -⟩ := hvald d
    rw [hc]; exact hle c c.2
  · intro d hd
    obtain ⟨c, hc, hp⟩ := hvald d
    rw [hc]; exact (hmem c).1 (hp hd)
  · intro b
    obtain ⟨a, ha, s, hs, hu, hsb⟩ := hfrac b
    refine ⟨algebraMap C D ⟨a, ha⟩, algebraMap C D ⟨s, hs⟩, ?_, ?_⟩
    · rw [hιalg]; exact hu
    · rw [hιalg, hιalg]; exact hsb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalFiniteTypeOver
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem isFractionRing_of_forall_eq_div {B : Type} [CommRing B] [IsDomain B]
    (K : Type) [Field K] [Algebra B K] [IsFractionRing B K]
    (R : Type) [CommRing R] [Algebra R B] [Algebra R K]
    [IsScalarTower R B K] (hinj : Function.Injective (algebraMap R B))
    (h : ∀ b : B, ∃ a s : R, s ≠ 0 ∧ algebraMap R B s * b = algebraMap R B a) :
    IsFractionRing R K := by
  have hcomp : algebraMap R K = (algebraMap B K).comp (algebraMap R B) :=
    IsScalarTower.algebraMap_eq R B K
  have hinjK : Function.Injective (algebraMap R K) := by
    rw [hcomp]; exact (IsFractionRing.injective B K).comp hinj
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr hinjK
  refine IsFractionRing.of_field R K (fun z => ?_)
  obtain ⟨b₁, b₂, -, rfl⟩ := IsFractionRing.div_surjective (A := B) z
  obtain ⟨a₁, s₁, hs₁, e₁⟩ := h b₁
  obtain ⟨a₂, s₂, hs₂, e₂⟩ := h b₂
  refine ⟨a₁ * s₂, s₁ * a₂, ?_⟩
  have n₁ : algebraMap B K (algebraMap R B s₁) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective B K), map_ne_zero_iff _ hinj]; exact hs₁
  have n₂ : algebraMap B K (algebraMap R B s₂) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective B K), map_ne_zero_iff _ hinj]; exact hs₂
  simp only [hcomp, RingHom.comp_apply, map_mul, ← e₁, ← e₂]
  set u := algebraMap B K (algebraMap R B s₁)
  set v := algebraMap B K (algebraMap R B s₂)
  rw [show u * algebraMap B K b₁ * v = (u * v) * algebraMap B K b₁ by ring,
    show u * (v * algebraMap B K b₂) = (u * v) * algebraMap B K b₂ by ring,
    mul_div_mul_left _ _ (mul_ne_zero n₁ n₂)]

theorem exists_finiteType_isIntegrallyClosed_integral_over :
    ∀ (A B : Type) [CommRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B]
      [IsIntegrallyClosed B] [Algebra A B] (C : Subalgebra A B), Algebra.FiniteType A C →
      (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, s ≠ 0 ∧ s * b = a) →
      ∃ C' : Subalgebra A B, C ≤ C' ∧ Algebra.FiniteType A C' ∧ IsIntegrallyClosed C' ∧
        ∀ x ∈ C', IsIntegral C x := by
  intro A B _ _ _ _ _ _ C hC hfrac
  haveI : Algebra.FiniteType A C := hC
  haveI : Algebra.EssFiniteType ℤ C := Algebra.EssFiniteType.comp ℤ A C
  haveI : IsNoetherianRing C := Algebra.EssFiniteType.isNoetherianRing ℤ C
  set K := FractionRing B
  set D : Subalgebra C B := integralClosure C B with hD
  haveI hCK : IsFractionRing C K := by
    refine isFractionRing_of_forall_eq_div (B := B) K C Subtype.val_injective
      (fun b => ?_)
    obtain ⟨a, ha, s, hs, hne, e⟩ := hfrac b
    refine ⟨⟨a, ha⟩, ⟨s, hs⟩, ?_, e⟩
    intro h0; apply hne; simpa using congrArg Subtype.val h0
  haveI hDK : IsFractionRing D K := by
    refine isFractionRing_of_forall_eq_div (B := B) K D Subtype.val_injective
      (fun b => ?_)
    obtain ⟨a, ha, s, hs, hne, e⟩ := hfrac b
    refine ⟨⟨a, D.algebraMap_mem ⟨a, ha⟩⟩, ⟨s, D.algebraMap_mem ⟨s, hs⟩⟩, ?_, e⟩
    intro h0; apply hne; simpa using congrArg Subtype.val h0
  have hinjBK : Function.Injective (IsScalarTower.toAlgHom C B K) :=
    IsFractionRing.injective B K

  have hfinK : Module.Finite C (integralClosure C K) := by
    haveI := finite_integralClosure_of_essFiniteType_int C
    let e : FractionRing C ≃ₐ[C] K := IsLocalization.algEquiv (nonZeroDivisors C) _ _
    exact Module.Finite.equiv e.mapIntegralClosure.toLinearEquiv
  have hfinD : Module.Finite C D := by
    let f : D →ₗ[C] integralClosure C K :=
      { toFun := fun x => ⟨algebraMap B K x, x.2.map (IsScalarTower.toAlgHom C B K)⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun c x => by
          ext; simp [Algebra.smul_def]; left; exact (IsScalarTower.algebraMap_apply C B K c).symm }
    refine Module.Finite.of_injective f (fun x y hxy => ?_)
    apply Subtype.ext; apply IsFractionRing.injective B K
    exact congrArg Subtype.val hxy
  have hftD : Algebra.FiniteType A D := Algebra.FiniteType.trans hC inferInstance
  have hicD : IsIntegrallyClosed D := by
    refine (isIntegrallyClosed_iff K).mpr (fun {x} hx => ?_)
    have hxB : IsIntegral B x := hx.tower_top
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxB
    have hxC : IsIntegral C (algebraMap B K y) := isIntegral_trans _ hx
    have hyC : IsIntegral C y := (isIntegral_algHom_iff _ hinjBK).mp hxC
    exact ⟨⟨y, hyC⟩, rfl⟩
  refine ⟨D.restrictScalars A, fun x hx => ?_, hftD, hicD, fun x hx => hx⟩
  exact isIntegral_algebraMap (R := C) (A := B) (x := ⟨x, hx⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimePowSmulLeOfLocalizationsEqAwayStatement
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_smul_le_of_localizations_eq_away : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A → Submodule.IsLattice E B → (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → localization₂ Q.asIdeal A = localization₂ Q.asIdeal B) → ∃ k : ℕ, P.asIdeal ^ k • A ≤ B ∧ P.asIdeal ^ k • B ≤ A := by
  first | exact @GlobalTheory.InertExchange.exists_pow_smul_le_of_locP_eq | exact GlobalTheory.InertExchange.exists_pow_smul_le_of_locP_eq | (intros; apply GlobalTheory.InertExchange.exists_pow_smul_le_of_locP_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWdSide
section
noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem exists_wdSide : GlobalTheory.Published.DeRhamPotSemistable → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), Nonempty (WDSide D T) :=
  fun hB D T => nonempty_wdSide_of_tie hB D T

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOkStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLatticeChartFamily_fam_ok : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → (S.fam emb lam).Ok := by
  first | exact @GlobalTheory.Mem.Col2.fam_ok | exact GlobalTheory.Mem.Col2.fam_ok | (intros; apply GlobalTheory.Mem.Col2.fam_ok <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasisStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLatticeChartFamily_lawBasis : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawBasis emb σ lam h := by
  first | exact @GlobalTheory.Mem.Col2.lawBasis_all | exact GlobalTheory.Mem.Col2.lawBasis_all | (intros; apply GlobalTheory.Mem.Col2.lawBasis_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFundamentalDomainEqSumDoubleCosetUnfoldStatement
section
open MeasureTheory
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_sum_doubleCoset_unfold : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ Ω : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (Ω : Set G) → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ Ω, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.Finite) → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ i, IntegrableOn (fun k => f (h i * k)) Ω ν) → IntegrableOn f 𝓖 ν ∧ ∫ x in 𝓖, f x ∂ν = ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ Ω}.ncard : ℕ) : ℂ)⁻¹ * ∫ k in (Ω : Set G), f (h i * k) ∂ν := by
  first | exact @GlobalTheory.Unfold.integral_fundamentalDomain_eq_sum_unfold | exact GlobalTheory.Unfold.integral_fundamentalDomain_eq_sum_unfold | (intros; apply GlobalTheory.Unfold.integral_fundamentalDomain_eq_sum_unfold <;> assumption)
end

