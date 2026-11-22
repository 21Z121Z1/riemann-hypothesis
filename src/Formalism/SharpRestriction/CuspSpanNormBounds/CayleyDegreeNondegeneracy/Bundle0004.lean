import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.TraceInnerPosOfOrthonormalPair
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ExistsSmallMemFractionalIdeal
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ProdNormEmbeddingsEqAbsNorm
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory
import Formalism.HermitianLattices.FinalMass
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FamilyGenusBoundOfSiegelRatio
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

theorem second_orthogonal_vector_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : SecondOrthogonalVector K :=
  fun V _ _ _ _ h L _ hL M hlat hint huni x hx hx0 => exists_orthogonal_second_vector K hK V h L hL M hlat hint huni x hx hx0

theorem plane_class_count_holds (K : Type) [Field K] [NumberField K] [StarRing K] (hK : IsCMUnram K) : PlaneClassCount K :=
  fun V _ _ _ _ h L hs hL s hreps B₁ B₂ hint hshort => class_count_plane_bound K hK V h L hs hL s hreps B₁ B₂ hint hshort

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_le_height_pow (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hfin := Formalism.MainNotions.StandardLattice.finrank_host D
  have hrd : rootDiscriminant D.host.E = D.host.rdE := rfl
  have h19 : 1 ≤ D.host.v := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := hH
    exact h19
  have hrd0 : 0 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  refine plane_mass_bound_of_facts D large₂ C' Cl Cg cb Cu cT CT C _ (short_vector_every_place D.host.E hK)
    (second_orthogonal_vector_holds D.host.E hK) (plane_class_count_holds D.host.E hK) ?_ ?_ hC hH
  · rw [hrd]; positivity
  · rw [hrd, hfin]; push_cast; apply le_of_eq; ring

theorem plane_mass_bound_parameters (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) : UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C :=
  fun hH => plane_mass_le_height_pow D large₂ C' Cl Cg cb Cu cT CT C hC hH.1.1

theorem plane_mass_bound_K2 (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C : ℝ)
    (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2) : UnitaryVolumeMass.stMass2K D large₂ C' Cl Cg cb Cu cT CT C0 C :=
  fun hH => plane_mass_le_height_pow D large₂ C' Cl Cg cb Cu cT CT C hC hH.1.1

theorem plane_mass_constant_le_sq (Cl : ℝ) : 55 * max 1 (1 / Cl) ≤ (55 * max 1 (1 / Cl)) ^ 2 := by
  have h : (1 : ℝ) ≤ max 1 (1 / Cl) := le_max_left _ _
  nlinarith

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem family_plane_mass_admissible (Cg cb Cu cT CT C0 A : ℝ) : AuxiliaryNormPrimes.FamilyRankTwoMassBound Fm Cg cb Cu cT CT C0 A :=
  ⟨55 * max 1 (1 / sCl Fm), 0, fun _ _ _ u u' => plane_mass_bound_parameters _ _ u u' _ _ _ _ _ _ _ _ _ _ (plane_mass_constant_le_sq _)⟩

theorem family_plane_mass_admissible_alt (Cg cb Cu cT CT C0 A : ℝ) : VanishingOnXAndXPlus.FamilyRankTwoMassEstimate Fm Cg cb Cu cT CT C0 A :=
  ⟨55 * max 1 (1 / sCl Fm), 0, fun _ _ _ u u' => plane_mass_bound_parameters _ _ u u' _ _ _ _ _ _ _ _ _ _ (plane_mass_constant_le_sq _)⟩

theorem family_plane_mass_admissible_k2 : LatticeIndexAndWeightTheory.FamilyRankTwoMassHyp Fm := fun _ _ _ _ _ _ =>
  ⟨55 * max 1 (1 / sCl Fm), 0, fun _ _ _ => plane_mass_bound_K2 _ _ _ _ _ _ _ _ _ _ _ (plane_mass_constant_le_sq _)⟩

theorem family_genus_bound_of_mass_ratio (Cg cb Cu cT CT C0 A : ℝ) (h1 : VanishingOnXAndXPlusMass.familyUnitInput Fm) (hCl : 1 ≤ sCl Fm) :
    VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 A :=
  BridgeLemma.family_first_bound_of_mass_ratio Fm Cg cb Cu cT CT C0 A h1 (family_plane_mass_admissible Fm Cg cb Cu cT CT C0 A) hCl

theorem family_genus_bound_of_siegel_ratio (Cg cb Cu cT CT C0 A : ℝ) (hS : Formalism.HermitianLatticesTheory.SiegelMassRatio) (hCl : 1 ≤ sCl Fm) :
    VanishingOnXAndXPlusMass.Conclusion1Family Fm Cg cb Cu cT CT C0 A :=
  family_genus_bound_of_mass_ratio Fm Cg cb Cu cT CT C0 A (BridgeLemma.family_lattice_count_first_of_siegel Fm hS) hCl

end Family

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GluingMassOfFibreStructure
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Orbit

open MulAction

theorem sum_orbits_inv_card_stabilizer (A G : Type) [Group A] [MulAction A G] [Finite A] [Finite G] :
    ∑ᶠ ω : Quotient (orbitRel A G), ((Nat.card (stabilizer A ω.out) : ℕ) : ℝ)⁻¹ =
      (Nat.card G : ℝ) / (Nat.card A : ℝ) := by
  classical
  have := Fintype.ofFinite A
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (Quotient (orbitRel A G))
  rw [finsum_eq_sum_of_fintype]
  have hA : (0 : ℝ) < (Nat.card A : ℝ) := by exact_mod_cast Nat.card_pos
  have h1 : ∀ ω : Quotient (orbitRel A G),
      ((Nat.card (stabilizer A ω.out) : ℕ) : ℝ)⁻¹ = (Nat.card (orbit A ω.out) : ℝ) / (Nat.card A : ℝ) := by
    intro ω
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group A ω.out
    have h' : (Nat.card (orbit A ω.out) : ℝ) * (Nat.card (stabilizer A ω.out) : ℝ) = (Nat.card A : ℝ) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      exact_mod_cast h
    have hs : (0 : ℝ) < (Nat.card (stabilizer A ω.out) : ℝ) := by exact_mod_cast Nat.card_pos
    haveI : Nonempty (orbit A ω.out) := ⟨⟨_, mem_orbit_self _⟩⟩
    have ho : (0 : ℝ) < (Nat.card (orbit A ω.out) : ℝ) := by exact_mod_cast Nat.card_pos
    rw [← h']
    field_simp
  rw [Finset.sum_congr rfl fun ω _ => h1 ω, ← Finset.sum_div]
  congr 1
  have h2 : Nat.card G = ∑ ω : Quotient (orbitRel A G), Nat.card (orbit A ω.out) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits A G), Nat.card_sigma]
  rw [h2]
  push_cast
  rfl

end Orbit

theorem trace_inner_self_pos {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : IsPosDef h) (x : V) (hx : x ≠ 0) :
    0 < Algebra.trace ℚ K (h x x) := by
  have key : ((Algebra.trace ℚ K (h x x) : ℚ) : ℂ) = ∑ σ : K →ₐ[ℚ] ℂ, σ (h x x) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), trace_eq_sum_embeddings (E := ℂ)]
  have key' : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    have := congrArg Complex.re key
    rw [Complex.re_sum] at this
    rw [← this]
    simp
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    let σ0 : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
    exact Finset.sum_pos (fun σ _ => hp σ.toRingHom x hx) ⟨σ0, Finset.mem_univ _⟩
  exact_mod_cast key' ▸ hpos

section Rows

open Classical

def FibresOrthLatticeOneGenus (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ s : Finset (LatV D), IsRowReps D F0 s →
    (∀ Λ' ∈ s, L0X D Λ' (lf D F0) ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0))) ∧
    ∀ M ∈ Formalism.HermitianLatticesTheory.genus (D.sp.X 0).hT (L0X D Λ (lf D F0)),
      ∑ Λ' ∈ s.filter (fun Λ' => ∃ g ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, Formalism.HermitianLatticesTheory.gmap g M = L0X D Λ' (lf D F0)),
          wRow D F0 Λ' =
        ((Tu D u : ℝ) - 1) ^ D.R.f * ((Nat.card (Formalism.ThetaLiftIndependence.autL (D.sp.X 0).hT M) : ℕ) : ℝ)⁻¹

theorem sum_eq_sum_over_class_reps {K V α : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (reps : Finset (Submodule (𝓞 K) V)) (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L reps) (s : Finset α)
    (c : α → Submodule (𝓞 K) V) (hc : ∀ a ∈ s, c a ∈ Formalism.HermitianLatticesTheory.genus h L) (w : α → ℝ) :
    ∑ a ∈ s, w a = ∑ M ∈ reps, ∑ a ∈ s.filter (fun a => ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g M = c a), w a := by
  rw [← Finset.sum_biUnion]
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · intro ha
      obtain ⟨N, ⟨hN, hg⟩, _⟩ := hreps.2 (c a) (hc a ha)
      exact ⟨N, hN, ha, hg⟩
    · rintro ⟨N, _, ha, _⟩
      exact ha
  · intro M hM M' hM' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha ha'
    rw [Finset.mem_filter] at ha ha'
    obtain ⟨N, _, huniq⟩ := hreps.2 (c a) (hc a ha.1)
    exact hne ((huniq M ⟨hM, ha.2⟩).trans (huniq M' ⟨hM', ha'.2⟩).symm)

theorem gluing_mass_of_fibre_structure (D : D7) (u : D.what₂.Word) (hpos : IsPosDef (D.sp.X 0).hT)
    (hlat : ForPrimeFlagLattice D u fun F0 Λ => Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)))
    (hR : FibresOrthLatticeOneGenus D u) : WordRowsGluing D u := by
  intro hT h3 hsp F0 he hz Λ hΛ s hs
  obtain ⟨hgen, hfib⟩ := hR hT h3 hsp F0 he hz Λ hΛ s hs
  obtain ⟨⟨reps, hreps⟩, hmass, _⟩ := Formalism.HermitianLatticesTheory.final_massBasic D.host.E (D.sp.X 0).V (D.sp.X 0).hT (D.sp.X 0).herm
    (trace_inner_self_pos _ hpos) (L0X D Λ (lf D F0)) (hlat hT h3 hsp F0 he hz Λ hΛ)
  rw [hmass reps hreps]
  unfold massRows
  rw [sum_eq_sum_over_class_reps (D.sp.X 0).hT _ reps hreps s (fun Λ' => L0X D Λ' (lf D F0)) hgen,
    Finset.sum_congr rfl fun M hM => hfib M (hreps.1 M hM), ← Finset.mul_sum, mul_comm]

end Rows

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LatDetSqOfCyclicDualQuotient
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma
open Formalism.MainNotions.LatticeGluingRadicals

section Loc

variable {E : Type} [Field E] [NumberField E]

theorem exists_not_mem_mul_mem_span {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {t : 𝓞 E} (ht : t ∈ P) (ht2 : t ∉ P ^ 2) :
    ∃ c : 𝓞 E, c ∉ P ∧ ∀ x ∈ P, c * x ∈ Ideal.span {t} := by
  have hle : Ideal.span {t} ≤ P := (Ideal.span_singleton_le_iff_mem _).2 ht
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr hle
  have hIP : ¬ I ≤ P := by
    intro h
    apply ht2
    have h2 : Ideal.span {t} ≤ P ^ 2 := by
      rw [hI, pow_two]
      exact Ideal.mul_mono_right h
    exact h2 (Ideal.subset_span (Set.mem_singleton t))
  obtain ⟨c, hcI, hcP⟩ := SetLike.not_le_iff_exists.mp hIP
  refine ⟨c, hcP, fun x hx => ?_⟩
  rw [hI, mul_comm c x]
  exact Ideal.mul_mem_mul hx hcI

def quotientSpanToQuotientPrime (P : Ideal (𝓞 E)) (t : 𝓞 E) (ht : t ∈ P) : (𝓞 E ⧸ Ideal.span {t}) →ₗ[𝓞 E] (𝓞 E ⧸ P) :=
  Submodule.mapQ (Ideal.span {t}) P LinearMap.id ((Ideal.span_singleton_le_iff_mem _).2 ht)

theorem isLocalizedModule_quotient_prime {P : Ideal (𝓞 E)} (hP : P.IsMaximal) {t : 𝓞 E} (ht : t ∈ P) (ht2 : t ∉ P ^ 2) :
    haveI := hP.isPrime
    IsLocalizedModule P.primeCompl (quotientSpanToQuotientPrime P t ht) := by
  constructor
  · intro s
    have hs : (s : 𝓞 E) ∉ P := s.2
    rw [Module.End.isUnit_iff]
    constructor
    · intro y1 y2 h
      obtain ⟨a1, rfl⟩ := Submodule.Quotient.mk_surjective P y1
      obtain ⟨a2, rfl⟩ := Submodule.Quotient.mk_surjective P y2
      simp only [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at h ⊢
      rw [← smul_sub, smul_eq_mul] at h
      exact (hP.isPrime.mem_or_mem h).resolve_left hs
    · intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P y
      obtain ⟨b, i, hi, hb⟩ := hP.exists_inv hs
      refine ⟨Submodule.Quotient.mk (b * a), ?_⟩
      simp only [Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, smul_eq_mul]
      have e : (s : 𝓞 E) * (b * a) - a = -(i * a) := by linear_combination a * hb
      rw [e]
      exact P.neg_mem (P.mul_mem_right a hi)
  · intro y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P y
    exact ⟨(Submodule.Quotient.mk a, 1), by simp [quotientSpanToQuotientPrime]⟩
  · intro x1 x2 h
    obtain ⟨a1, rfl⟩ := Submodule.Quotient.mk_surjective _ x1
    obtain ⟨a2, rfl⟩ := Submodule.Quotient.mk_surjective _ x2
    simp only [quotientSpanToQuotientPrime, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq] at h
    obtain ⟨c, hcP, hc⟩ := exists_not_mem_mul_mem_span hP ht ht2
    refine ⟨⟨c, hcP⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def]
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← smul_sub, smul_eq_mul]
    exact hc _ h

end Loc

section Idx

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem localLength_cyclic_mem {A B : Submodule (𝓞 E) S.V} {t : 𝓞 E}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {t})) (P : Ideal (𝓞 E)) (hP : P.IsMaximal) (ht : t ∈ P)
    (ht2 : t ∉ P ^ 2) : haveI := hP.isPrime; Formalism.HermitianLatticesTheory.locLen P A B = 1 := by
  have := hP.isPrime
  unfold Formalism.HermitianLatticesTheory.locLen
  have := isLocalizedModule_quotient_prime hP ht ht2
  have eq := IsLocalizedModule.linearEquiv P.primeCompl (i_g P A B) (quotientSpanToQuotientPrime P t ht ∘ₗ e.toLinearMap)
  rw [eq.length_eq]
  have : IsSimpleModule (𝓞 E) (𝓞 E ⧸ P) := isSimpleModule_iff_isCoatom.2 hP.out
  rw [Module.length_eq_one]
  rfl

theorem localLength_cyclic_not_mem {A B : Submodule (𝓞 E) S.V} {t : 𝓞 E}
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {t})) (P : Ideal (𝓞 E)) [P.IsPrime] (ht : t ∉ P) :
    Formalism.HermitianLatticesTheory.locLen P A B = 0 := by
  have htA : ∀ x ∈ A, t • x ∈ B := by
    intro x hx
    have h1 : e (Submodule.Quotient.mk (t • (⟨x, hx⟩ : A))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (e (Submodule.Quotient.mk ⟨x, hx⟩))
      rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self t)
    have h2 := (LinearEquiv.map_eq_zero_iff e).mp h1
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h2
    exact h2
  have hsub : Subsingleton ((Formalism.HermitianLatticesTheory.localization₂ P A) ⧸ (Formalism.HermitianLatticesTheory.localization₂ P B).comap (Formalism.HermitianLatticesTheory.localization₂ P A).subtype) := by
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : ∃ s ∈ P.primeCompl, s • x ∈ A := hx
    obtain ⟨s, hs, hsx⟩ := hx'
    show ∃ s ∈ P.primeCompl, s • x ∈ B
    refine ⟨t * s, Ideal.mem_primeCompl_iff.mpr fun h => ?_, ?_⟩
    · rcases ‹P.IsPrime›.mem_or_mem h with h | h
      · exact ht h
      · exact Ideal.mem_primeCompl_iff.mp hs h
    · rw [mul_smul]
      exact htA _ hsx
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [Module.length_eq_zero_iff.mpr hsub]
  rfl

theorem genIdx_cyclic_split_prime {A B : Submodule (𝓞 E) S.V} (hBA : B ≤ A) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl E T)
    (e : (A ⧸ B.comap A.subtype) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {((T : ℕ) : 𝓞 E)})) :
    genIdxH A B = (T : ℝ) ^ finrank ℚ E := by
  unfold genIdxH
  have h1 : ∀ P : HeightOneSpectrum (𝓞 E),
      ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.lidx P.asIdeal A B) =
        ∏ᶠ (_ : P ∈ plOver E T), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) := by
    intro P
    classical
    have := P.isPrime
    rw [i_lidx_of_le P.asIdeal hBA]
    by_cases hP : P ∈ plOver E T
    · have hmax := P.isPrime.isMaximal P.ne_bot
      rw [finprod_eq_if, if_pos hP, localLength_cyclic_mem e P.asIdeal hmax hP (hs P.asIdeal hmax hP).2]
      simp
    · rw [finprod_eq_if, if_neg hP, localLength_cyclic_not_mem e P.asIdeal hP]
      simp
  rw [finprod_congr h1]
  exact finprod_plOver E hT hs id

theorem latDet_sq_of_cyclic_dual_quotient (M : Submodule (𝓞 E) S.V) (hl : Submodule.IsLattice E M)
    (hint : M ≤ Formalism.HermitianLatticesTheory.dual S.hT M) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl E T) (w₁ : S.V)
    (hw : w₁ ∈ Formalism.HermitianLatticesTheory.dual S.hT M) (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual S.hT M, ∃ a : 𝓞 E, w + a • w₁ ∈ M)
    (hker : ∀ a : 𝓞 E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 E) ∣ a) :
    latDetH S.hT M = Real.sqrt ((T : ℝ) ^ finrank ℚ E) := by
  have hA : Formalism.HermitianLatticesTheory.dual S.hT M ⊓ Submodule.restrictScalars (𝓞 E) (Submodule.span E (M : Set S.V)) =
      Formalism.HermitianLatticesTheory.dual S.hT M := by
    rw [hl.span_eq_top, Submodule.restrictScalars_top, inf_top_eq]
  have hφ : ∀ a : 𝓞 E, LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩) a =
      Submodule.Quotient.mk ⟨a • w₁, (Formalism.HermitianLatticesTheory.dual S.hT M).smul_mem a hw⟩ := by
    intro a
    rw [LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul]
    rfl
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩)) := by
    intro y
    obtain ⟨⟨w, hwA⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨a, ha⟩ := hgen w hwA
    refine ⟨-a, ?_⟩
    rw [hφ, Submodule.Quotient.eq, Submodule.mem_comap, map_sub, Submodule.subtype_apply,
      Submodule.subtype_apply]
    have h1 : -a • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
    rw [h1]
    exact M.neg_mem ha
  have hK : LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) _
      (Submodule.Quotient.mk (p := M.comap (Formalism.HermitianLatticesTheory.dual S.hT M).subtype) ⟨w₁, hw⟩)) =
      Ideal.span {((T : ℕ) : 𝓞 E)} := by
    ext a
    rw [LinearMap.mem_ker, hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Ideal.mem_span_singleton]
    exact hker a
  unfold latDetH dualInH
  rw [hA]
  congr 1
  exact genIdx_cyclic_split_prime hint hT hs
    ((Submodule.quotEquivOfEq _ _ hK).symm.trans (LinearMap.quotKerEquivOfSurjective _ hsurj)).symm

end Idx

section Record

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_rat_E_eq_two_f (D : D7) : finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  show 4 * D.R.toFrame.ord = 2 * (2 * D.R.toFrame.ord)
  ring

theorem latDet_of_cyclic_dual_quotient (D : D7) (M : Submodule (𝓞 D.host.E) (D.sp.X 0).V) (hl : Submodule.IsLattice D.host.E M)
    (hint : M ≤ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M) {T : ℕ} (hT : T.Prime) (hs : SplitsCompl D.host.E T)
    (w₁ : (D.sp.X 0).V) (hw : w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M)
    (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT M, ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ M)
    (hker : ∀ a : 𝓞 D.host.E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 D.host.E) ∣ a) :
    latDetH (D.sp.X 0).hT M = ((T ^ D.R.f : ℕ) : ℝ) := by
  rw [latDet_sq_of_cyclic_dual_quotient M hl hint hT hs w₁ hw hgen hker, finrank_rat_E_eq_two_f, pow_mul',
    Real.sqrt_sq (by positivity)]
  norm_cast

end Record

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeIsIntegralOfUnimodular
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Basic

variable (D : D7)

theorem orth_embedding_isometry (x y : (D.sp.X 0).V) :
    (D.sp.Y 0).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
  D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega) x y

theorem orth_embedding_injective : Function.Injective (D.sp.iXY 0) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  refine (D.sp.X 0).nondeg.1 x fun y => ?_
  rw [← orth_embedding_isometry, hx]; simp

theorem finrank_orth_space_eq_k : finrank D.host.E (D.sp.X 0).V = D.R.k := by
  rw [(D.sp.X 0).rank_eq, D.sp.X_rank 0 (Nat.zero_le _)]
  simp [Ranks.N]

variable {D} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

include he hz in
theorem orth_embedding_mem_orth_plus (x : (D.sp.X 0).V) : D.sp.iXY 0 x ∈ orth (hS D) (Xplus (lf D F0)) := by
  have h : Xplus (lf D F0) ≤ LinearMap.ker ((hS D).hT.flip (D.sp.iXY 0 x)) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨a, rfl⟩
      show (hS D).hT (F0.e a) (D.sp.iXY 0 x) = 0
      rw [he]
      exact c_symm0 (D.sp.hyp_orthX a x).1
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      show (hS D).hT F0.z (D.sp.iXY 0 x) = 0
      rw [hz]
      unfold D7.zmOf
      rw [map_smulₛₗ, LinearMap.smul_apply, c_symm0 (D.sp.zm_orth x), smul_zero]
  exact c_mem_orth.2 fun v hv => h hv

include he in
theorem eq_zero_of_embedding_mem_isotropic {x : (D.sp.X 0).V} (hx : D.sp.iXY 0 x ∈ Xsp (lf D F0)) : x = 0 := by
  have hx' : D.sp.iXY 0 x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by rw [← he]; exact hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx'
  have h0 : ∀ i, c i = 0 := by
    intro i
    have h1 := (D.sp.hyp_orthX i x).2
    rw [← hc, map_sum, LinearMap.sum_apply] at h1
    simp only [map_smulₛₗ, LinearMap.smul_apply, D.sp.hyp_ef, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    simpa using h1
  apply orth_embedding_injective D
  rw [← hc, map_zero]
  exact Finset.sum_eq_zero fun i _ => by rw [h0 i, zero_smul]

include he hz in

theorem orth_space_posDef_every_place (hT : 0 < Tu D u) : Cnt.IsPosDef (D.sp.X 0).hT := by
  intro τ x hx
  have h1 := p_posX D (Tu D u) hT (lf D F0) τ (D.sp.iXY 0 x) (orth_embedding_mem_orth_plus F0 he hz x)
    (fun h => hx (eq_zero_of_embedding_mem_isotropic F0 he h))
  unfold nrm at h1
  rwa [orth_embedding_isometry] at h1

end Basic

section Lat

variable {D : D7} {T : D.host.E} (Λ : LatV D) (F : LFlag (hS D) D.R.rS T)

theorem mem_orthLattice_iff_mem_sub {x : (D.sp.X 0).V} : x ∈ L0X D Λ F ↔ D.sp.iXY 0 x ∈ L0sub Λ F := Iff.rfl

theorem orthLattice_isIntegral_of_unimodular (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ F) := by
  intro x hx y hy
  obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_mem_sub Λ F).1 hx).1.1
  obtain ⟨l', hl', ξ', hξ', e'⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_mem_sub Λ F).1 hy).1.1
  rw [← orth_embedding_isometry, ← e, ← e']
  have h1 : (hS D).hT l ξ' = 0 := c_symm0 (c_mem_orth.1 hl.2 ξ' hξ')
  have h2 : (hS D).hT ξ l' = 0 := c_mem_orth.1 hl'.2 ξ hξ
  have h3 : (hS D).hT ξ ξ' = 0 := p_X_iso F hξ hξ'
  simp only [map_add, LinearMap.add_apply]
  rw [h1, h2, h3, add_zero, add_zero, add_zero]
  exact i_int Λ hu hl.1 hl'.1

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
end

