import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.CrystallineUnitParts.UnitPart
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0058
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0150
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0155
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0160
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0157
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0757

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateChar
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct CompanionTheory.PRW.ACWD
open Topology

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LTExt

theorem ext_dense {W D B : Type} [Group W] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    [CompactSpace D] [T2Space D] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]
    (i : W →* D) (hi : DenseRange i) (χ : W →* B) (C : Set B) (hC : IsCompact C) (hχ : ∀ σ, χ σ ∈ C)
    (h1 : ∀ V ∈ 𝓝 (1 : B), ∃ U ∈ 𝓝 (1 : D), ∀ σ, i σ ∈ U → χ σ ∈ V) :
    ∃! κ : D →* B, Continuous κ ∧ ∀ σ, κ (i σ) = χ σ := by
  let Γ : Subgroup (D × B) := (i.prod χ).range.topologicalClosure
  have hΓ : IsCompact (Γ : Set (D × B)) := by
    refine (isCompact_univ.prod hC).of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
    refine closure_minimal ?_ (isCompact_univ.prod hC).isClosed
    rintro _ ⟨σ, rfl⟩
    exact ⟨trivial, hχ σ⟩
  haveI : CompactSpace Γ := isCompact_iff_compactSpace.1 hΓ
  let p : Γ →* D := (MonoidHom.fst D B).comp Γ.subtype
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hmem : ∀ σ, (i σ, χ σ) ∈ Γ := fun σ => Subgroup.le_topologicalClosure _ ⟨σ, rfl⟩
  have hinj : Function.Injective p := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨d, k⟩, hk⟩ hd
    obtain rfl : d = 1 := hd
    by_contra hne
    have hk1 : (1 : B) ≠ k := by
      rintro rfl
      exact hne rfl
    obtain ⟨V, V', hV, hV', hVV⟩ := t2_separation_nhds hk1
    obtain ⟨U, hU, H⟩ := h1 V hV
    obtain ⟨_, ⟨h2, h3⟩, σ, rfl⟩ := mem_closure_iff_nhds.1 hk _ (prod_mem_nhds hU hV')
    exact Set.disjoint_left.1 hVV (H σ h2) h3
  have hsurj : Function.Surjective p := by
    have h2 : IsClosed (Set.range p) := (isCompact_range hp).isClosed
    have h3 : Set.range i ⊆ Set.range p := by
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨_, hmem σ⟩, rfl⟩
    intro d
    exact closure_minimal h3 h2 (hi d)
  let e : Γ ≃* D := MulEquiv.ofBijective p ⟨hinj, hsurj⟩
  have he : Continuous e.symm := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) hp
  refine ⟨((MonoidHom.snd D B).comp Γ.subtype).comp e.symm.toMonoidHom,
    ⟨continuous_snd.comp (continuous_subtype_val.comp he), fun σ => ?_⟩, ?_⟩
  · have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show (e.symm (i σ)).1.2 = _
    rw [this]
  · rintro κ ⟨hκ, H⟩
    refine DFunLike.coe_injective (hi.equalizer hκ (continuous_snd.comp (continuous_subtype_val.comp he)) ?_)
    funext σ
    have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show κ (i σ) = (e.symm (i σ)).1.2
    rw [this, H]

variable {E : Type} [Field E] [NumberField E]

def unitSub (w : HeightOneSpectrum (𝓞 E)) : Subgroup (w.adicCompletion E)ˣ where
  carrier := {x | IsUnitAt w x}
  one_mem' := by simp [IsUnitAt]
  mul_mem' := by
    intro x y hx hy
    simp only [IsUnitAt, Set.mem_setOf_eq] at *
    simp [hx, hy]
  inv_mem' := by
    intro x hx
    simp only [IsUnitAt, Set.mem_setOf_eq] at *
    simp [hx]

theorem compactSpace_unitSub (w : HeightOneSpectrum (𝓞 E)) : CompactSpace (unitSub w) := by
  refine isCompact_iff_compactSpace.1 (?_ : IsCompact (unitSub w : Set (w.adicCompletion E)ˣ))
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have h1 : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (Formalism.MainNotions.Gaps.LevGap.compact_Ov w)
  have h2 : Units.val '' (unitSub w : Set (w.adicCompletion E)ˣ) = {x | Valued.v x = 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hx' : Valued.v x = 1 := hx
      have h0 : x ≠ 0 := fun h => by simp [h] at hx'
      exact ⟨Units.mk0 x h0, hx', rfl⟩
  rw [h2]
  refine h1.of_isClosed_subset ?_ fun x hx => le_of_eq hx
  have h3 : IsOpen {x : w.adicCompletion E | Valued.v x < 1} := by
    simpa using Valued.isOpen_ball (w.adicCompletion E) 1
  have h4 : {x : w.adicCompletion E | Valued.v x = 1} =
      (w.adicCompletionIntegers E : Set (w.adicCompletion E)) \ {x | Valued.v x < 1} := by
    ext x
    exact ⟨fun hx => ⟨le_of_eq hx, fun h => (ne_of_lt h) hx⟩, fun hx => le_antisymm hx.1 (not_lt.1 hx.2)⟩
  rw [h4]
  exact h1.isClosed.sdiff h3

variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem ext_profinite (h : IsPlaceOver A w) {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [CompactSpace B] [T2Space B] [TotallyDisconnectedSpace B] (χ : Weil h →* B)
    (hI : Continuous fun τ : Ine (F := E) A => χ (ineIncl h τ)) :
    DenseRange (Subgroup.inclusion (Weil_le_Dec h)) ∧
    ∃ κ : ↥(Dec (F := E) A) →* B, Continuous κ ∧ ∀ σ : Weil h, κ (Subgroup.inclusion (Weil_le_Dec h) σ) = χ σ := by
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  haveI : CompactSpace (Dec (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have hd : DenseRange (Subgroup.inclusion (Weil_le_Dec h)) := by
    have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine E Ω A w h
      (Subgroup.inclusion (Weil_le_Dec h) (frob h)) (isFrob_frob (h := h))
    have h2 : Subgroup.zpowers (Subgroup.inclusion (Weil_le_Dec h) (frob h)) ⊔
        (Ine (F := E) A).subgroupOf (Dec (F := E) A) ≤ (Subgroup.inclusion (Weil_le_Dec h)).range := by
      refine sup_le ?_ fun σ hσ => ⟨⟨σ, Ine_le_Weil h hσ⟩, rfl⟩
      rw [Subgroup.zpowers_le]
      exact ⟨_, rfl⟩
    intro d
    have h3 : d ∈ (⊤ : Subgroup (Dec (F := E) A)) := trivial
    rw [← h1] at h3
    exact closure_mono h2 h3
  refine ⟨hd, (ext_dense (Subgroup.inclusion (Weil_le_Dec h)) hd χ Set.univ isCompact_univ (fun _ => trivial)
    fun V hV => ?_).exists⟩
  obtain ⟨V', hVV, hV', h1V⟩ := mem_nhds_iff.1 hV
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV' h1V
  haveI := H.toSubgroup.quotient_finite_of_isOpen H.isOpen
  obtain ⟨N, hN, -, hNH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := H.toSubgroup)) (χ (frob h))
  have hM := (H.isOpen.preimage hI).mem_nhds (x := 1) (by simpa using H.toSubgroup.one_mem)
  rw [nhds_subtype_eq_comap, Filter.mem_comap] at hM
  obtain ⟨U, hU, hUM⟩ := hM
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).1 hU
  have hLo : IsOpen (L.fixingSubgroup : Set (G E Ω)) := L.fixingSubgroup_isOpen
  haveI := L.fixingSubgroup.quotient_finite_of_isOpen hLo
  obtain ⟨m, hm, -, hmL⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := L.fixingSubgroup)) (frob h : G E Ω)
  obtain ⟨ζ, hζ⟩ := GlobalTheory.exists_fixed_dvd_deg E Ω A w h (m * N) (Nat.mul_pos hm hN)
  have hζo : IsOpen (MulAction.stabilizer (G E Ω) ζ : Set (G E Ω)) := stabilizer_isOpen_of_isIntegral ζ
  refine ⟨_, continuous_subtype_val.continuousAt.preimage_mem_nhds
    ((hLo.inter hζo).mem_nhds ⟨L.fixingSubgroup.one_mem, (MulAction.stabilizer (G E Ω) ζ).one_mem⟩),
    fun σ hσ => hVV (hH ?_)⟩
  obtain ⟨k, hk⟩ := hζ σ hσ.2
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
  have h1 : ((frob h ^ deg σ : Weil h) : G E Ω) ∈ L.fixingSubgroup := by
    rw [hk, Subgroup.coe_zpow, Nat.cast_mul, mul_assoc, zpow_mul, zpow_natCast]
    exact L.fixingSubgroup.zpow_mem hmL _
  have h2 : (τ : G E Ω) ∈ L.fixingSubgroup := by
    have h3 : (σ : G E Ω) ∈ L.fixingSubgroup := hσ.1
    rw [hτ, Subgroup.coe_mul] at h3
    exact (L.fixingSubgroup.mul_mem_cancel_left h1).1 h3
  show χ σ ∈ H.toSubgroup
  rw [hτ, map_mul, map_zpow]
  refine H.toSubgroup.mul_mem ?_ (hUM (hLU h2))
  rw [hk, Nat.cast_mul, mul_comm (m : ℤ), mul_assoc, zpow_mul, zpow_natCast]
  exact H.toSubgroup.zpow_mem hNH _

theorem exists_lubinTate_char : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (π : (w.adicCompletion E)ˣ), IsUnifAt w π →
    ∃ c : ↥(Dec (F := E) A) →* (w.adicCompletion E)ˣ,
      Continuous (fun g => ((c g : (w.adicCompletion E)ˣ) : w.adicCompletion E)) ∧
      (∀ σ : Weil h, c ⟨σ, Weil_le_Dec h σ.2⟩ = a σ * π ^ deg σ) ∧ (∀ g, IsUnitAt w (c g)) ∧
      ∀ c' : ↥(Dec (F := E) A) →* (w.adicCompletion E)ˣ,
        Continuous (fun g => ((c' g : (w.adicCompletion E)ˣ) : w.adicCompletion E)) →
        (∀ σ : Weil h, c' ⟨σ, Weil_le_Dec h σ.2⟩ = a σ * π ^ deg σ) → c' = c := by
  intro E Ω _ _ _ _ _ w A h a ha π hπ
  let u : Weil h →* (w.adicCompletion E)ˣ := a * (zpowersHom _ π).comp (degHom h)
  have hu : ∀ σ, u σ = a σ * π ^ deg σ := fun _ => rfl
  have hunit : ∀ σ, u σ ∈ unitSub w := by
    intro σ
    have h1 := ha.ord_eq σ
    rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_inj] at h1
    have h0 : Valued.v ((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 := by simp
    show Valued.v ((a σ * π ^ deg σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    unfold IsUnifAt at hπ
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπ, ← WithZero.exp_log h0, h1,
      ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  haveI := compactSpace_unitSub w
  haveI : TotallyDisconnectedSpace (w.adicCompletion E)ˣ :=
    Units.isEmbedding_val₀.isTotallyDisconnected_range.1 (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  obtain ⟨hd, κ, hκ, hκu⟩ := ext_profinite h (u.codRestrict _ hunit) (by
    refine Continuous.subtype_mk ?_ _
    simpa [hu] using ha.cont)
  have hc : Continuous fun g => (((unitSub w).subtype.comp κ g : (w.adicCompletion E)ˣ) : w.adicCompletion E) :=
    Units.continuous_val.comp (continuous_subtype_val.comp hκ)
  have hv : ∀ σ : Weil h, (unitSub w).subtype.comp κ ⟨σ, Weil_le_Dec h σ.2⟩ = a σ * π ^ deg σ :=
    fun σ => congrArg Subtype.val (hκu σ)
  refine ⟨(unitSub w).subtype.comp κ, hc, hv, fun g => (κ g).2, fun c' hc' H => ?_⟩
  have := hd.equalizer hc' hc (funext fun σ => congrArg Units.val ((H σ).trans (hv σ).symm))
  exact MonoidHom.ext fun g => Units.ext (congrFun this g)

end GlobalTheory.LTExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinCompatLocalDegreeOne
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.LocDegOne

theorem val_div_sub_one_le₁ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {a c : K}
    (hc : c ≠ 0) {N m : ℕ} (hm : (WithZero.log (w.valuation K c)).natAbs ≤ m)
    (h : w.valuation K (a - c) ≤ WithZero.exp (-((N : ℤ) + m))) :
    w.valuation K (a / c - 1) ≤ WithZero.exp (-(N : ℤ)) := by
  have hv : w.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc
  rw [div_sub_one hc, map_div₀, ← WithZero.exp_log hv, div_le_iff₀ (by simp), ← WithZero.exp_add]
  refine h.trans (WithZero.exp_le_exp.mpr ?_)
  have : -(m : ℤ) ≤ WithZero.log (w.valuation K c) := by omega
  omega

theorem val_le_of_le₁ {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K} {N N' : ℤ}
    (h : w.valuation K x ≤ WithZero.exp (-N)) (hN : N' ≤ N) : w.valuation K x ≤ WithZero.exp (-N') :=
  h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem res_art_eq_art (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] [Algebra E E']
    (φ : Ω ≃+* Ω') (hφ : ∀ x, φ (algebraMap E Ω x) = algebraMap E' Ω' (algebraMap E E' x))
    (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E'))
    (i : w.adicCompletion E ≃+* w'.adicCompletion E') (hi : Continuous i)
    (hloc : ∀ x : E, i (algebraMap E _ x) = algebraMap E' _ (algebraMap E E' x))
    (art : Ideles E →* Gab E Ω) (art' : Ideles E' →* Gab E' Ω') (ha : IsGlobalArtin art) (ha' : IsGlobalArtin art')
    (ρ : Gab E' Ω' →* Gab E Ω) (hρc : Continuous ρ)
    (hρ : ∀ (τ : G E' Ω') (σ : G E Ω), (∀ z, φ (σ z) = τ (φ z)) → ρ (toAb E' Ω' τ) = toAb E Ω σ)
    (x : (w.adicCompletion E)ˣ) :
    ρ (art' (localIdele E' w' (Units.map i.toRingHom.toMonoidHom x))) = art (localIdele E w x) := by
  classical
  have hw' := GlobalTheory.T.comap_eq_of_continuous_adicCompletion_iso E E' w w' i hi hloc
  have hdE : ∀ k : Eˣ, art (diagUnits E k) = 1 := fun k => by
    have hk : diagUnits E k ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hdK : ∀ k : E'ˣ, art' (diagUnits E' k) = 1 := fun k => by
    have hk : diagUnits E' k ∈ art'.ker := by
      rw [ha'.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
    exact hk
  have hiE : ∀ y ∈ infConn E, art y = 1 := fun y hy => by
    have hk : y ∈ art.ker := by
      rw [ha.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hy)
    exact hk
  have hiK : ∀ y ∈ infConn E', art' y = 1 := fun y hy => by
    have hk : y ∈ art'.ker := by
      rw [ha'.ker]
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_right hy)
    exact hk
  rw [← div_eq_one]
  refine GlobalTheory.GabSep.eq_one_of_forall_isOpen_subgroup E Ω _ fun U hU => ?_
  let χ : Gab E Ω →* Gab E Ω ⧸ U := QuotientGroup.mk' U
  suffices h : χ (ρ (art' (localIdele E' w' (Units.map i.toRingHom.toMonoidHom x)))) = χ (art (localIdele E w x)) by
    have h2 : χ (ρ (art' (localIdele E' w' (Units.map i.toRingHom.toMonoidHom x))) / art (localIdele E w x)) = 1 := by
      rw [_root_.map_div, h, div_self']
    exact (QuotientGroup.eq_one_iff _).mp h2
  let ψ1 : Ideles E' →* Gab E Ω ⧸ U := χ.comp (ρ.comp art')
  let ψ2 : Ideles E →* Gab E Ω ⧸ U := χ.comp art
  have hker1 : (ψ1.ker : Set (Ideles E')) = (ρ.comp art') ⁻¹' U := by
    ext y; simp [ψ1, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hker2 : (ψ2.ker : Set (Ideles E)) = art ⁻¹' U := by
    ext y; simp [ψ2, χ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have ho1 : IsOpen (ψ1.ker : Set (Ideles E')) := by
    rw [hker1]; exact hU.preimage (hρc.comp ha'.quot.continuous)
  have ho2 : IsOpen (ψ2.ker : Set (Ideles E)) := by
    rw [hker2]; exact hU.preimage ha.quot.continuous

  let f1 : (w.adicCompletion E)ˣ →* Gab E Ω ⧸ U :=
    ψ1.comp ((localIdele E' w').comp (Units.map i.toRingHom.toMonoidHom))
  let f2 : (w.adicCompletion E)ˣ →* Gab E Ω ⧸ U := ψ2.comp (localIdele E w)
  have hf1 : IsOpen (f1.ker : Set (w.adicCompletion E)ˣ) := by
    have e : (f1.ker : Set (w.adicCompletion E)ˣ) =
        ((localIdele E' w').comp (Units.map i.toRingHom.toMonoidHom)) ⁻¹' (ψ1.ker : Set (Ideles E')) := by
      ext y; simp only [f1, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, MonoidHom.comp_apply]
    rw [e]
    exact ho1.preimage ((GlobalTheory.Mem.UnrAe.continuous_localIdele w').comp (Continuous.units_map _ hi))
  have hf2 : IsOpen (f2.ker : Set (w.adicCompletion E)ˣ) := by
    have e : (f2.ker : Set (w.adicCompletion E)ˣ) = (localIdele E w) ⁻¹' (ψ2.ker : Set (Ideles E)) := by
      ext y; simp only [f2, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, MonoidHom.comp_apply]
    rw [e]
    exact ho2.preimage (GlobalTheory.Mem.UnrAe.continuous_localIdele w)
  show f1 x = f2 x
  refine GlobalTheory.T.units_adicCompletion_hom_ext_of_isOpen_ker E w _ f1 f2 hf1 hf2 (fun c => ?_) x
  let y : E'ˣ := Units.map (algebraMap E E').toMonoidHom c
  have hc1 : f1 (Units.map (algebraMap E (w.adicCompletion E)).toMonoidHom c) = ψ1 (locUnit E' w' y) := by
    simp only [f1, MonoidHom.comp_apply, locUnit_apply]
    congr 2
    ext
    simp [y, hloc]
  rw [hc1]
  change _ = ψ2 (locUnit E w c)

  let NK : E'ˣ →* Eˣ := Units.map (Algebra.norm E (S := E'))
  obtain ⟨SE, ME, hvS, hSu, hSc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E ψ2.ker ho2 {w}
  have hwSE : w ∈ SE := hvS (Finset.mem_singleton_self w)
  obtain ⟨TSK, hTSK⟩ := GlobalTheory.PlacesOver.places_over_finset E E' SE
  have hWT : w' ∈ TSK := (hTSK w').mpr ⟨w, hwSE, hw'⟩
  obtain ⟨MainNotions, MK, hTS, -, hSKc⟩ := GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr E' ψ1.ker ho1 TSK
  choose M' hM' using fun v' : HeightOneSpectrum (𝓞 E) => GlobalTheory.NormCompat.NormCont.norm_close_to_one E E' v' ME
  obtain ⟨ML, hML⟩ := GlobalTheory.T.norm_close_to_component_localDegreeOne E E' w w' i hi hloc ME
  let M'' : ℕ := SE.sup M'
  let m : ℕ := (WithZero.log (w'.valuation E' (y : E'))).natAbs
  let P0 : ℕ := MK + M'' + ML + 1
  obtain ⟨a, hap, hapos⟩ := GlobalTheory.T.exists_totallyPositive_approx_at_finite_places E' TSK (fun u => if u = w' then (y : E') else 1) (P0 + m)
  have haW : w'.valuation E' (a - y) ≤ WithZero.exp (-((P0 : ℤ) + m)) := by
    have := hap w' hWT
    rw [if_pos rfl] at this
    exact val_le_of_le₁ w' this (by push_cast; omega)
  have hz : w'.valuation E' (a / y - 1) ≤ WithZero.exp (-(P0 : ℤ)) :=
    val_div_sub_one_le₁ w' y.ne_zero le_rfl haW
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_div, zero_sub, Valuation.map_neg, map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at hz
    omega
  let au : E'ˣ := Units.mk0 a ha0
  let zu : E'ˣ := au / y
  have hzu : (zu : E') = a / y := by simp [zu, au]
  have hauy : au = y * zu := by simp [zu]
  have hoth : ∀ u ∈ TSK, u ≠ w' → u.valuation E' (a - 1) ≤ WithZero.exp (-(P0 : ℤ)) := fun u hu hne => by
    have := hap u hu
    rw [if_neg hne] at this
    exact val_le_of_le₁ u this (by push_cast; omega)

  have F1 : ψ1 (locUnit E' w' au) = ψ1 (locUnit E' w' y) := by
    have hm : locUnit E' w' zu ∈ ψ1.ker := hSKc w' (hTS hWT) zu (by
      rw [hzu]; exact val_le_of_le₁ w' hz (by push_cast; omega))
    rw [hauy, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F2 : ψ2 (locUnit E w (NK au)) = ψ2 (locUnit E w c) := by
    have hn : w.valuation E (Algebra.norm E a / (c : E) - 1) ≤ WithZero.exp (-(ME : ℤ)) := by
      refine hML (c : E) a c.ne_zero (fun u hu hne => ?_) ?_
      · exact val_le_of_le₁ u (hoth u ((hTSK u).mpr ⟨w, hwSE, hu⟩) hne) (by push_cast; omega)
      · have e : algebraMap E E' (c : E) = (y : E') := rfl
        rw [e]; exact val_le_of_le₁ w' hz (by push_cast; omega)
    let q : Eˣ := NK au / c
    have hq : (q : E) = Algebra.norm E a / (c : E) := by simp [q, NK, au]
    have hm : locUnit E w q ∈ ψ2.ker := hSc w hwSE q (by rw [hq]; exact hn)
    have e : NK au = c * q := by simp [q]
    rw [e, map_mul, map_mul, MonoidHom.mem_ker.mp hm, mul_one]

  have F3 : ∀ u ∈ TSK, u ≠ w' → ψ1 (locUnit E' u au) = 1 := fun u hu hne =>
    MonoidHom.mem_ker.mp (hSKc u (hTS hu) au (val_le_of_le₁ u (hoth u hu hne) (by push_cast; omega)))
  have F4 : ∀ v' ∈ SE, v' ≠ w → ψ2 (locUnit E v' (NK au)) = 1 := fun v' hv' hne => by
    refine MonoidHom.mem_ker.mp (hSc v' hv' (NK au) ?_)
    refine hM' v' (au : E') fun u hu => ?_
    have huT : u ∈ TSK := (hTSK u).mpr ⟨v', hv', hu⟩
    have huW : u ≠ w' := by
      rintro rfl
      exact hne (HeightOneSpectrum.ext (hu.symm.trans hw'))
    exact val_le_of_le₁ u (hoth u huT huW) (by
      have : M' v' ≤ M'' := Finset.le_sup hv'
      push_cast; omega)

  have hunitE : ∀ v' ∉ SE, ∀ z, IsUnitAt v' z → ψ2 (localIdele E v' z) = 1 := fun v' hv' z hz =>
    MonoidHom.mem_ker.mp (hSu v' hv' z hz)
  have hchi := fun (v' : HeightOneSpectrum (𝓞 E)) (hv' : v' ∉ SE) (u : HeightOneSpectrum (𝓞 E'))
      (hu : u.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = v'.asIdeal) =>
    GlobalTheory.T.artin_transport_algClosure_equiv E Ω E' Ω' φ hφ art art' ha ha' ρ hρ (Gab E Ω ⧸ U) χ v' u hu (hunitE v' hv')
  obtain ⟨TK, TE, hTK1, hTK2, hTE1, hTE2, hprod⟩ := GlobalTheory.T.prod_localValues_global_over_places_above E E' (Gab E Ω ⧸ U) ψ1 ψ2 SE hunitE
    (fun v' hv' u hu => (hchi v' hv' u hu).1) (fun v' hv' u hu => (hchi v' hv' u hu).2) au

  have hPK : (∏ u ∈ TK, ψ1 (locUnit E' u au)) * ψ1 (locUnit E' w' au) = 1 := by
    have hdisj : Disjoint TK TSK := by
      rw [Finset.disjoint_left]
      intro u h1 h2
      obtain ⟨v', hv', e⟩ := (hTSK u).mp h2
      exact hTK1 u h1 v' hv' e
    have h := GlobalTheory.T.prod_idele_character_eq_one_of_totallyPositive E' (Gab E Ω ⧸ U) ψ1 ho1 (fun k => by simp [ψ1, hdK]) (fun z hz => by simp [ψ1, hiK z hz])
      au (fun φ => hapos φ) (TK ∪ TSK) fun u hu => by
        rw [Finset.mem_union, not_or] at hu
        exact hTK2 u hu.1 fun v' hv' e => hu.2 ((hTSK u).mpr ⟨v', hv', e⟩)
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem w' hWT F3] at h
    exact h
  have hPE : (∏ v' ∈ TE, ψ2 (locUnit E v' (NK au))) * ψ2 (locUnit E w (NK au)) = 1 := by
    have hdisj : Disjoint TE SE := by
      rw [Finset.disjoint_left]
      intro v' h1 h2
      exact hTE1 v' h1 h2
    have h := GlobalTheory.T.prod_idele_character_eq_one_of_totallyPositive E (Gab E Ω ⧸ U) ψ2 ho2 (fun k => by simp [ψ2, hdE]) (fun z hz => by simp [ψ2, hiE z hz])
      (NK au) (fun φ => GlobalTheory.T.norm_totallyPositive_of_totallyPositive_ne_zero E E' a ha0 hapos φ) (TE ∪ SE) fun v' hv' => by
        rw [Finset.mem_union, not_or] at hv'
        exact hTE2 v' hv'.1 hv'.2
    rw [Finset.prod_union hdisj, Finset.prod_eq_single_of_mem w hwSE F4] at h
    exact h
  have key : ψ1 (locUnit E' w' au) = ψ2 (locUnit E w (NK au)) := by
    rw [← hprod] at hPE
    exact mul_left_cancel (hPK.trans hPE.symm)
  rw [← F1, key, F2]

theorem artin_of_placeIso : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (art' : Neutral.B1.Ideles E' →* GlobalTheory.HeckeGal.Gab E' Ω'), GlobalTheory.HeckeGal.IsGlobalArtin art → GlobalTheory.HeckeGal.IsGlobalArtin art' → ∀ (σ : Weil h) (σ' : Weil h') (x : (w.adicCompletion E)ˣ), WeilRel φ σ σ' → art' (Neutral.B1.localIdele E' w' (Units.map i.toRingHom.toMonoidHom x)) = GlobalTheory.HeckeGal.toAb E' Ω' σ' → art (Neutral.B1.localIdele E w x) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hPI art art' ha ha' σ σ' x hW hx
  letI : Algebra E E' := j.toAlgebra
  obtain ⟨ρ, hρc, hρ⟩ := GlobalTheory.T.exists_abelianizedGalois_hom_of_closureIso E Ω E' Ω' φ j hPI.ext
  have key := res_art_eq_art E Ω E' Ω' φ hPI.ext w w' i hPI.cont hPI.loc art art' ha ha' ρ hρc hρ x
  have hσ : ρ (toAb E' Ω' σ') = toAb E Ω σ := hρ σ' σ hW
  rw [← key, hx, hσ]

end GlobalTheory.LocDegOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoStatementStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyodo_statement : Hyodo := by
  first | exact @GlobalTheory.PMon.hyodo | exact GlobalTheory.PMon.hyodo | (intros; apply GlobalTheory.PMon.hyodo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorConvolutionEqCompStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_convolution_eq_comp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ f : GAf L n → W, (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.conv (Formalism.UG.KU Dv.σw n) h₁ h₂) f = heckeFunI L n U Dv h₁ (heckeFunI L n U Dv h₂ f) := by
  first | exact @GlobalTheory.InertConvMul.heckeFunI_conv_mul | exact GlobalTheory.InertConvMul.heckeFunI_conv_mul | (intros; apply GlobalTheory.InertConvMul.heckeFunI_conv_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertHeckeOperatorMaximalCompactIndicatorEqIdStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertHeckeOperator_maximalCompact_indicator_eq_id : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ U, NG.rt L n κ f = f) → heckeFunI L n U Dv (Formalism.UG.dosetInd ℂ (Formalism.UG.KU Dv.σw n) 1) f = f := by
  first | exact @GlobalTheory.InertHeckeOne.heckeFunI_one | exact GlobalTheory.InertHeckeOne.heckeFunI_one | (intros; apply GlobalTheory.InertHeckeOne.heckeFunI_one <;> assumption)
end

