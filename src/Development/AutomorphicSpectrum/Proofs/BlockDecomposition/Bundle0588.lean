import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0222
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0250
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0076
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0025
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.TnsIsTopologicalAddGroup
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzero
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.JacSph

theorem hecke_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : CassData G) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π) (t : D.T) (ht : D.IsDom t)
    (U : Module.End ℂ (fixed π D.J)) (hU : PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U) (r : ℕ) :
    D.IsDom (t ^ r) ∧ PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
  induction r with
  | zero =>
    refine ⟨by simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1, ?_⟩
    intro w l _
    simp
  | succ r ih =>
    rw [pow_succ, pow_succ U]
    exact ⟨(GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih.1 ht,
      GlobalTheory.T.casselman_first_property G D V π hπ (t ^ r) t ih.1 ht _ _ ih.2 hU⟩

theorem jacNeU : JacNeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hu hadm _ hsat
  obtain ⟨v₀, hv₀⟩ := hsat.exists_vec
  have hfixK : v₀ ∈ fixed ρ (KU σ n) := hv₀.2.1
  refine ⟨v₀, fun hjac => ?_, fun k hk _ => ?_⟩
  · obtain ⟨D, hJ, hN, hNm, hT⟩ := GlobalTheory.T.iwahori_unipotent_datum L ϖ σ q hu n
    obtain ⟨hKo, hKc, hIK, t₀, ht₀d, ht₀s⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n hu
    have hstr : D.IsStrDom ⟨t₀, (hT _).2 ht₀d⟩ :=
      (GlobalTheory.T.dominant_unipotent_contraction L ϖ σ q hu n D hJ hN hNm hT ⟨t₀, (hT _).2 ht₀d⟩).2 ht₀s
    have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
    have hproj0 : D.proj ρ v₀ = 0 := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [hker]
      exact hjac
    have hJK : ∀ x ∈ D.J, x ∈ KU σ n := fun x hx => hIK (hJ ▸ hx)
    have hfixJ : v₀ ∈ fixed ρ D.J :=
      GlobalTheory.LGrp.mem_fixed.2 fun x hx => GlobalTheory.LGrp.mem_fixed.1 hfixK x (hJK x hx)
    obtain ⟨U, hU, -⟩ := GlobalTheory.T.hecke_character_exists_unique (GU σ n) D.J D.isOpen_J D.isCompact_J V ρ hadm.1 t₀
    obtain ⟨j₀, hj₀⟩ := GlobalTheory.CompanionTheory.Cass.hecke_pow_kills_of_proj_eq_zero (GU σ n) D V ρ hadm.1 _ hstr U hU
      ⟨v₀, hfixJ⟩ hproj0
    obtain ⟨l, hlK, hl1⟩ := GlobalTheory.CompanionTheory.KAvg.kInvForm (GU σ n) (KU σ n) hKo hKc V ρ hadm.1 v₀ hfixK hv₀.1
    obtain ⟨j, hj, hS⟩ := GlobalTheory.T.satake_power_nonvanishing L ϖ σ q n hu α t₀ ht₀d ht₀s j₀
    have hUj : (U ^ j) ⟨v₀, hfixJ⟩ = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [add_comm, pow_add, Module.End.mul_apply, hj₀, map_zero]
    have hl0 : l (ρ (t₀ ^ j) v₀) = 0 := by
      have h := (hecke_pow D ρ hadm.1 _ hstr.1 U hU j).2 ⟨v₀, hfixJ⟩ l fun x hx => hlK x (hJK x hx)
      rw [hUj] at h
      simpa using h
    have hc := GlobalTheory.CompanionTheory.SphComp.sphCompare L ϖ σ q n hu V ρ α v₀ hv₀ l hlK (t₀ ^ j)
    rw [hl0, mul_zero, hl1, mul_one] at hc
    exact hS hc.symm
  · rw [GlobalTheory.LGrp.mem_fixed.1 hfixK k hk, sub_self]
    exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.JacSph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLevelSubgroupProperties
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.IwLevels

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem KGL_eq_KO (w : Pl E) (n : ℕ) :
    GlobalTheory.LFun.KGL w n = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) := by
  ext g
  rw [GlobalTheory.CompanionTheory.IwEntries.mem_KGL_iff, GlobalTheory.CompanionTheory.IwEntries.mem_KO_iff]

theorem isCompact_KGL (w : Pl E) (n : ℕ) : IsCompact (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := by
  rw [KGL_eq_KO]
  exact GlobalTheory.SplitFlip.isCompact_KO

theorem iwGL_le_KGL (w : Pl E) (n : ℕ) : iwGL n w ≤ GlobalTheory.LFun.KGL w n := by
  rw [KGL_eq_KO]
  exact GlobalTheory.SmGL.iwahori_le_KO _ _

theorem isClosed_UL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (hc : Continuous (cj w)) :
    IsClosed (UL n w : Set (GLw n w)) := by
  rw [GlobalTheory.CompanionTheory.UnitaryWitt.UL_eq_of_not_split hw]
  exact GlobalTheory.CompanionTheory.UnitaryWitt.isClosed_UJ_one n hc

theorem isOpen_KL (n : ℕ) (w : Pl E) : IsOpen (KL n w : Set (UL n w)) := by
  have h : IsOpen (GlobalTheory.LFun.KGL w n : Set (GLw n w)) := by
    rw [KGL_eq_KO]
    exact GlobalTheory.SplitFlip.isOpen_KO
  exact h.preimage (continuous_subtype_val (p := (· ∈ UL n w)))

theorem isCompact_KL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (hc : Continuous (cj w)) :
    IsCompact (KL n w : Set (UL n w)) :=
  (isClosed_UL hw n hc).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_KGL w n)

theorem isOpen_iwU (n : ℕ) (w : Pl E) (b : GLw n w) : IsOpen (iwU n w b : Set (UL n w)) := by
  have ho : IsOpen (iwGL n w : Set (GLw n w)) :=
    GlobalTheory.SmGL.IwahoriOnto.isOpen_iwahori (w.adicCompletion E) (Fin n)
  have hcont : Continuous fun γ : UL n w => b⁻¹ * γ.1 * b :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have e : (iwU n w b : Set (UL n w)) = (fun γ : UL n w => b⁻¹ * γ.1 * b) ⁻¹' (iwGL n w : Set (GLw n w)) := by
    ext γ
    exact GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ
  rw [e]
  exact ho.preimage hcont

theorem iwU_le_KL (n : ℕ) (w : Pl E) (b : GLw n w) (hb : b ∈ GlobalTheory.LFun.KGL w n) :
    iwU n w b ≤ KL n w := by
  intro γ hγ
  have h1 := iwGL_le_KGL w n ((GlobalTheory.CompanionTheory.UnitaryWitt.mem_iwU_iff n w b γ).1 hγ)
  have h2 : γ.1 = b * (b⁻¹ * γ.1 * b) * b⁻¹ := by group
  rw [KL, Subgroup.mem_subgroupOf, h2]
  exact mul_mem (mul_mem hb h1) (inv_mem hb)

theorem relIndex_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H K : Subgroup G}
    (hH : IsOpen (H : Set G)) (hK : IsCompact (K : Set G)) : H.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let U : OpenSubgroup K := ⟨H.subgroupOf K, hH.preimage continuous_subtype_val⟩
  haveI : Finite (K ⧸ (U : Subgroup K)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  exact Subgroup.index_ne_zero_of_finite

theorem isCompact_support_fU {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (b : GLw n w)
    (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) (hc : Continuous (cj w)) :
    IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  set t : GLw n w := b * tdiag ϖ (wexp n l) * b⁻¹ with ht
  have hI : IsCompact (iwU n w b : Set (UL n w)) :=
    GlobalTheory.CompanionTheory.UnitaryWitt.isCompact_iwU hw n b hc
  have hS : IsCompact ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
      ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) :=
    (hI.prod hI).image (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
      (continuous_subtype_val.comp continuous_snd))
  have e : {g : UL n w | fU n w b ϖ l g ≠ 0} = Subtype.val ⁻¹'
      ((fun p : UL n w × UL n w => p.1.1 * t * p.2.1) ''
        ((iwU n w b : Set (UL n w)) ×ˢ (iwU n w b : Set (UL n w)))) := by
    ext γ
    simp only [Set.mem_setOf_eq, fU, Set.mem_preimage, Set.mem_image, Set.mem_prod, SetLike.mem_coe]
    constructor
    · intro h
      by_contra hn
      refine h (if_neg ?_)
      rintro ⟨x, hx, z, hz, e⟩
      exact hn ⟨(x, z), ⟨hx, hz⟩, e.symm⟩
    · rintro ⟨⟨x, z⟩, ⟨hx, hz⟩, e⟩
      rw [if_pos ⟨x, hx, z, hz, e.symm⟩]
      exact one_ne_zero
  rw [e]
  exact (isClosed_UL hw n hc).isClosedEmbedding_subtypeVal.isCompact_preimage hS

theorem levels_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w), IsWitt n w b → ∀ (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ), IsUnifAt ϖ → Cone l → IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) ∧ IsLevel (MonoidHom.id _) (KL n w) (iwU n w b) ∧ (iwU n w b).relIndex (KL n w) ≠ 0 ∧ IsCompact {g : UL n w | fU n w b ϖ l g ≠ 0} := by
  intro E _ _ _ hU w hw n b hb ϖ l _ _
  have hc : Continuous (cj w) := (GlobalTheory.T.placeConjugation_properties_cmField E hU w).1
  exact ⟨isOpen_KL n w, isCompact_KL hw n hc,
    ⟨isOpen_iwU n w b, iwU_le_KL n w b hb.1, fun k hk => hk⟩,
    relIndex_ne_zero (isOpen_iwU n w b) (isCompact_KL hw n hc),
    isCompact_support_fU hw n b ϖ l hc⟩

end GlobalTheory.CompanionTheory.IwLevels
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.One

open PositivityTheory.Rg.Mass

theorem finite_rat_compact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (n M : ℕ) (K : Set (Fin n → Fin M → AF F ⊗[F] E)) (hK : IsCompact K) :
    {X : Fin n → Fin M → E | ratTup (AF F) X ∈ K}.Finite := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  let f : (Fin n → Fin M → E) →+ (Fin n → Fin M → AF F ⊗[F] E) :=
    AddMonoidHom.mk' (ratTup (F := F) (AF F)) (fun X Y => by funext a i; simp [ratTup, map_add])
  have hdisc : DiscreteTopology f.range := Formalism.IndefR.Eqv.G5.tup_disc (F := F) (E := E) M n
  have hcl : IsClosed (f.range : Set (Fin n → Fin M → AF F ⊗[F] E)) := AddSubgroup.isClosed_of_discrete
  have hfin : (K ∩ (f.range : Set (Fin n → Fin M → AF F ⊗[F] E))).Finite :=
    (hK.inter_right hcl).finite ⟨DiscreteTopology.of_subset (s := (f.range : Set (Fin n → Fin M → AF F ⊗[F] E))) hdisc Set.inter_subset_right⟩
  refine (hfin.preimage hri.injOn).subset fun X hX => ⟨hX, X, rfl⟩

theorem theta_locFin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (hμ : IsHaarH F E σ M J μ) (h𝓕 : IsFDH F E σ M J μ 𝓕)
    (C : Set (HA (AF F) σ J)) (hC : IsCompact C) (hcov : ∀ h, ∃ γ : HFinIn (AF F) σ J, ∃ c ∈ C, h = γ • c)
    (hμ0 : μ 𝓕 ≠ 0) (hμt : μ 𝓕 ≠ ⊤) (n : ℕ) (S : Set (Fin n → Fin M → E)) :
    IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 S) := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, -⟩ := hact n
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  refine ⟨fun X₀ => ?_⟩
  obtain ⟨K, hK, hX⟩ := exists_compact_mem_nhds X₀
  have hK' : IsCompact ((fun p : HA (AF F) σ J × (Fin n → Fin M → AF F ⊗[F] E) => actW (AF F) σ J p.1 p.2) '' (C ×ˢ K)) :=
    (hC.prod hK).image ac
  have hP := finite_rat_compact σ hcm n M _ hK'
  set P := {X : Fin n → Fin M → E | ratTup (AF F) X ∈
    ((fun p : HA (AF F) σ J × (Fin n → Fin M → AF F ⊗[F] E) => actW (AF F) σ J p.1 p.2) '' (C ×ˢ K))} with hPdef
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have hcov' : ∀ h : HA (AF F) σ J, ∃ γ : Γ, ∃ c ∈ C, h = (γ : HA (AF F) σ J) * c := fun h => by
    obtain ⟨γ, c, hc, e⟩ := hcov h
    exact ⟨γ, c, hc, e⟩
  have hbound : ∀ h : HA (AF F) σ J, ∑' X : S, K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
      (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ≤ (P.encard : ℝ≥0∞) := fun h => by
    obtain ⟨γ, c, hc, rfl⟩ := hcov' h
    choose t ht using fun X : Fin n → Fin M → E => PositivityTheory.PlacePermOperatorBicommutantSpan.act_rat (n := n) γ⁻¹ X
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X) = ratTup (AF F) (t X) := ht
    have hti : Function.Injective t := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J (γ : HA (AF F) σ J)) ((ht' X).trans ((congrArg (ratTup (AF F)) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact hri h1
    let A : Set S := {X | actW (AF F) σ J ((γ : HA (AF F) σ J) * c)⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E)) ∈ K}
    have e1 : ∑' X : S, K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
        (actW (AF F) σ J ((γ : HA (AF F) σ J) * c)⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) = (A.encard : ℝ≥0∞) := by
      rw [← ENNReal.tsum_set_one, tsum_subtype A (fun _ => (1 : ℝ≥0∞))]
      refine tsum_congr fun X => ?_
      by_cases hx : X ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show _ ∈ K from hx)]; rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show _ ∉ K from hx)]
    rw [e1]
    refine ENat.toENNReal_le.2 (Set.encard_le_encard_of_injOn (f := fun X : S => t X.1) ?_ ?_)
    · intro X hX
      refine ⟨(c, _), ⟨hc, hX⟩, ?_⟩
      change actW (AF F) σ J c (actW (AF F) σ J ((γ : HA (AF F) σ J) * c)⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) = ratTup (AF F) (t X.1)
      rw [← a2, mul_inv_rev, mul_inv_cancel_left, ht']
    · intro X _ Y _ e
      exact Subtype.ext (hti e)
  refine ⟨K, hX, ?_⟩
  have hm : Measurable (K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)) :=
    measurable_one.indicator hK.measurableSet
  rw [← lintegral_indicator_one hK.measurableSet, PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 _ _ _ hm]
  have hle : ∫⁻ h in 𝓕, ∑' X : S, K.indicator (1 : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
      (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ ≤ (P.encard : ℝ≥0∞) * μ 𝓕 := by
    refine (lintegral_mono hbound).trans ?_
    simp
  have hPt : (P.encard : ℝ≥0∞) ≠ ⊤ := by
    simpa using hP.encard_lt_top.ne
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hμ0))
    (lt_of_le_of_lt hle (ENNReal.mul_lt_top hPt.lt_top hμt.lt_top))

theorem euler_of_summable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ)
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hdet : T.det ≠ 0) (d : ℕ)
    (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v))
    (hinf : IsStdInf laminf) (hlam : ∀ v, IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : IsGramFib (Ainf F) σ J n (coordW (Ainf F) b laminf n M) (coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : HeightOneSpectrum (𝓞 F), HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, IsGramFib (Fv F v) σ J n (coordW (Fv F v) b (lam v) n M) (coordHerm (Fv F v) σ b (lam v) n) (m v))
    (hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤)
    (hsum : Summable fun v => |(m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1|)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hIf : IsLocallyFiniteMeasure I)
    (hIinv : ∀ h : HA (AF F) σ J, I.map (actW (AF F) σ J h) = I)
    (hIsupp : I {X | gramR (AF F) σ J X = T.map (inclR (AF F))}ᶜ = 0) :
    ∃ c : ℝ≥0, IsEulerProd b I c (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)) := by
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  have hFi := GlobalTheory.CompanionTheory.SW.Fact.fib_facts σ hCM J hJ (Ainf F) hLi T hT hdet b laminf hinf.1 minf hminf
  have hFv : ∀ v, SigmaFinite (m v (hermOf (Fv F v) σ T hT)) ∧
      (m v (hermOf (Fv F v) σ T hT) = 0 →
        ∀ X, gramR (Fv F v) σ J X ≠ T.map (inclR (Fv F v))) := fun v => by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact GlobalTheory.CompanionTheory.SW.Fact.fib_facts σ hCM J hJ (Fv F v) (hLv v) T hT hdet b (lam v) (hlam v).1 (m v) (hm v)
  by_cases h0 : minf (hermOf (Ainf F) σ T hT) = 0 ∨ ∃ v, m v (hermOf (Fv F v) σ T hT) = 0
  · have hempty : {X | gramR (AF F) σ J X = T.map (inclR (AF F))} = ∅ := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hX
      have hloc := (GlobalTheory.T.gram_matrix_local_global F E σ hCM M J hJ n X T).1.1 hX
      rcases h0 with h | ⟨v, h⟩
      · exact hFi.2 h _ hloc.1
      · exact (hFv v).2 h _ (hloc.2 v)
    rw [hempty, Set.compl_empty] at hIsupp
    rw [Measure.measure_univ_eq_zero.mp hIsupp]
    exact ⟨0, (GlobalTheory.T.euler_product_measure_zero F E σ hCM d b n M 0 0 _ _).2.2 hfin hsum h0⟩
  · push Not at h0
    obtain ⟨hinf0, hv0⟩ := h0
    choose c hc using GlobalTheory.T.siegel_weil_orbital_measure F E σ hCM M J hJ n T hT hdet d b laminf lam hinf hlam minf hminf m hm
      I hIf hIinv hIsupp
    obtain ⟨A, hAm, hA0, hAt⟩ := @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (minf (hermOf (Ainf F) σ T hT)) hFi.1 hinf0
    choose B hBm hB0 hBt using fun v =>
      @GlobalTheory.CompanionTheory.SW.Fact.exists_test_set _ _ (m v (hermOf (Fv F v) σ T hT)) (hFv v).1 (hv0 v)
    have hstep : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∅ ⊆ S → ∀ v, v ∉ S →
        (c S : ℝ) = c (insert v S) * (m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal := by
      intro S _ v hv
      have hlatm : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
        haveI := GlobalTheory.CompanionTheory.SW.Fact.borel_tup σ hCM (Fv F v) (hLv v) n M
        exact ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2.measurableSet
      let φ0 : ∀ w : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F w ⊗[F] E) → ℝ≥0∞ :=
        fun w => (B w).indicator 1
      let φ1 := Function.update φ0 v ((latV b v).indicator 1)
      have hφ0 : ∀ w, Measurable (φ0 w) := fun w => measurable_one.indicator (hBm w)
      have hφ1 : ∀ w, Measurable (φ1 w) := by
        intro w
        by_cases hw : w = v
        · subst hw
          simpa [φ1] using measurable_one.indicator hlatm
        · simpa [φ1, Function.update_of_ne hw] using hφ0 w
      have hAφ : Measurable (A.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hAm
      have e1 := hc S _ φ0 hAφ hφ0
      have e2 := hc (insert v S) _ φ1 hAφ hφ1
      have e3 : ∫⁻ X, pureL b (insert v S) (A.indicator 1) φ1 X ∂I =
          ∫⁻ X, pureL b S (A.indicator 1) φ0 X ∂I :=
        lintegral_congr fun X => GlobalTheory.CompanionTheory.SW.Fact.pureL_insert b S v hv _ φ0 X
      rw [e3, e1, Finset.prod_insert hv] at e2
      have hp : ∏ w ∈ S, ∫⁻ X, φ1 w X ∂(m w (hermOf (Fv F w) σ T hT)) =
          ∏ w ∈ S, ∫⁻ X, φ0 w X ∂(m w (hermOf (Fv F w) σ T hT)) :=
        Finset.prod_congr rfl fun w hw => by
          have hne : w ≠ v := fun h => hv (h ▸ hw)
          simp only [φ1, Function.update_of_ne hne]
      have hL : ∫⁻ X, φ1 v X ∂(m v (hermOf (Fv F v) σ T hT)) =
          m v (hermOf (Fv F v) σ T hT) (latV b v) := by
        simp only [φ1, Function.update_self]
        exact lintegral_indicator_one hlatm
      have hB : ∀ w, ∫⁻ X, φ0 w X ∂(m w (hermOf (Fv F w) σ T hT)) =
          m w (hermOf (Fv F w) σ T hT) (B w) := fun w => lintegral_indicator_one (hBm w)
      have hA : ∫⁻ X, A.indicator (1 : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞) X ∂(minf (hermOf (Ainf F) σ T hT)) =
          minf (hermOf (Ainf F) σ T hT) A := lintegral_indicator_one hAm
      rw [hp, hL, hA] at e2
      simp only [hB] at e2
      set Q := ∏ w ∈ S, m w (hermOf (Fv F w) σ T hT) (B w) with hQ
      set a := minf (hermOf (Ainf F) σ T hT) A with ha
      set L := m v (hermOf (Fv F v) σ T hT) (latV b v) with hLdef
      have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hB0 w
      have hQt : Q ≠ ⊤ := ENNReal.prod_ne_top fun w _ => hBt w
      have hP0 : a * Q ≠ 0 := mul_ne_zero hA0 hQ0
      have hPt : a * Q ≠ ⊤ := ENNReal.mul_ne_top hAt hQt
      have e4 : (c S : ℝ≥0∞) * (a * Q) = ((c (insert v S) : ℝ≥0∞) * L) * (a * Q) := by
        rw [e2]; ring
      have e5 := (ENNReal.mul_left_inj hP0 hPt).mp e4
      have e6 := congrArg ENNReal.toReal e5
      simpa [ENNReal.toReal_mul] using e6
    obtain ⟨c₀, S₀, -, hS₀⟩ := GlobalTheory.T.infinite_product_renormalization _ (fun v => (m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal) c ∅
      (fun _ => ENNReal.toReal_nonneg) hsum hstep
    refine ⟨c₀, hfin, hsum, S₀, fun S hS φinf φ hφi hφ => ?_⟩
    rw [hc S φinf φ hφi hφ]
    have hcS : (c S : ℝ≥0∞) = (c₀ : ℝ≥0∞) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) := by
      rw [← ENNReal.ofReal_coe_nnreal (p := c S), (hS₀ S hS).2, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_coe_nnreal]
    rw [hcS]
    ring

theorem vector_length_formula_up_to_constant : CoCpt → LocMass → Prop1 := by
  intro hCo hLoc F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm β hβ
  obtain ⟨⟨C, hC, hcov⟩, hμ0, hμt⟩ := hCo F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm
  obtain ⟨C₁, hC₁⟩ := hLoc F E σ J d b li lam μ 𝓕 mi m hcm hJ hA hli hlam hμ h𝓕 hmi hm
  have hE : algebraMap F E β ≠ 0 := fun h => hβ ((map_eq_zero _).1 h)
  let T : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E β
  have hT : ∀ a b, σ (T b a) = T a b := fun _ _ => σ.commutes β
  have hd : T.det ≠ 0 := by
    rw [Matrix.det_unique]
    exact hE
  obtain ⟨β', e, -, hh⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm T hT
  have hββ : β' = β := (algebraMap F E).injective (congrFun (congrFun e 0) 0).symm
  rw [hββ] at hh
  obtain ⟨t1, t2⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_inv F E σ hcm 2 J hJ μ 𝓕 hμ h𝓕 1 T
  have hlf : IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | gramE σ J X = T}) :=
    theta_locFin σ hcm 2 J hJ μ 𝓕 hμ h𝓕 C hC hcov hμ0 hμt 1 _
  have hfin : ∀ v, m v (hermOf (Fv F v) σ T hT) (latV b v) < ⊤ := fun v => by
    have hloc : IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F v
    obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
    haveI := hTR
    haveI := hLC
    haveI := hSC
    haveI := hT2
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    have hh' := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    haveI hW := hh'.2.1 1 2
    haveI hH := hh'.2.2 1
    have hl := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) hloc 1 _ _ (m v) hW hH (hm v)
      (hermOf (Fv F v) σ T hT)).1
    exact ((GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v).1.measure_lt_top
  have hsum : Summable fun v => |(m v (hermOf (Fv F v) σ T hT) (latV b v)).toReal - 1| := by
    refine Summable.of_norm_bounded_eventually
      (g := fun v : HeightOneSpectrum (𝓞 F) => C₁ * (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2))
      ((GlobalTheory.CompanionTheory.SW.Primes.summable_one_div_absNorm_sq F).mul_left C₁) ?_
    filter_upwards [hC₁, (GlobalTheory.T.integral_almost_all_places F E σ hcm d b).2 β hβ] with v h1 h2
    have h3 := h1.2.2 _ h2
    rw [Real.norm_eq_abs, abs_abs, hh]
    simpa [div_eq_mul_inv] using h3
  obtain ⟨c, hc⟩ := euler_of_summable σ hcm 2 J hJ 1 T hT hd d b li lam hli hlam mi hmi m hm hfin hsum _ hlf t1 t2
  simp only [hh] at hc
  exact ⟨c, hc⟩

end GlobalTheory.CompanionTheory.Mass.One
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerExpansionUnipotent
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open GroundTheory.Automorphic.FourierWhittaker (vecDomain vecMeasure pair)
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.GA.WhitU

abbrev idl (a : ℚˣ) : (𝔸[ℚ])ˣ := Units.map (algebraMap ℚ 𝔸[ℚ]).toMonoidHom a

theorem dia_dg (a : ℚˣ) : dia (dg a 1 1) = (dg (idl a) 1 1 : G3) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dia, dg, idl, AdelicGLn.diagonal]

theorem conj (a : ℚˣ) (x : 𝔸[ℚ]) : (dg (idl a) 1 1 : G3) * uni x 0 0 =
    uni (algebraMap ℚ 𝔸[ℚ] a * x) 0 0 * (dg (idl a) 1 1 : G3) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg, uni, Matrix.mul_apply, Fin.sum_univ_three, idl]

theorem pt {V : Submodule ℂ (G3 → ℂ)} (hV : WhA V) {W : G3 → ℂ} (hW : W ∈ V) (a : ℚˣ) (g : G3)
    (x : 𝔸[ℚ]) :
    W (dia (dg a 1 1) * (uni x 0 0 * g)) * (adelicChar ℚ (-x) : ℂ) =
      W (dg (idl a) 1 1 * g) * (adelicChar ℚ (algebraMap ℚ 𝔸[ℚ] ((a : ℚ) - 1) * x) : ℂ) := by
  have e : dia (dg a 1 1) * (uni x 0 0 * g) =
      uni (algebraMap ℚ 𝔸[ℚ] a * x) 0 0 * (dg (idl a) 1 1 * g) := by
    rw [dia_dg, ← mul_assoc, conj, mul_assoc]
  have e2 : algebraMap ℚ 𝔸[ℚ] ((a : ℚ) - 1) * x = algebraMap ℚ 𝔸[ℚ] a * x + -x := by
    rw [map_sub, map_one]; ring
  rw [e, hV.psi W hW, e2, add_zero, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

end GlobalTheory.CompanionTheory.GA.WhitU
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneGradedFiniteStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_level_one_graded_finite : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (ρ : O →+* k) (U : Cov q) (r j : ℕ),
    Module.Finite (Wc.Wm l k 1) (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) r) (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((r : ℤ) + 1))) j) := by
  first | exact @GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite | exact GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite | (intros; apply GlobalTheory.CompanionTheory.FibGr.level_one_gr_finite <;> assumption)
end

