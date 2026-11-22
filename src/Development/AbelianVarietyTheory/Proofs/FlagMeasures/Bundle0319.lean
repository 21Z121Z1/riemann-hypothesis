import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalInnerLatticeEqOfInnerPreimageEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFundamentalDomainSmulIff
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.ClosedSubgroupCovol

section General

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K]
  [BorelSpace K] (Γ : Subgroup K) (μ : Measure K)

theorem measure_eq [Countable Γ] [μ.IsMulLeftInvariant] {s t : Set K}
    (hs : IsFundamentalDomain Γ s μ) (ht : IsFundamentalDomain Γ t μ) : μ s = μ t := hs.measure_eq ht

omit [IsTopologicalGroup K] [BorelSpace K] in

theorem measure_ne_zero [Countable Γ] [μ.IsHaarMeasure] {s : Set K}
    (hs : IsFundamentalDomain Γ s μ) : μ s ≠ 0 :=
  hs.measure_ne_zero (NeZero.ne μ)

theorem measure_le_of_cover [Countable Γ] [μ.IsMulLeftInvariant] {s : Set K}
    (hs : IsFundamentalDomain Γ s μ) {C : Set K}
    (hcov : ∀ m : K, ∃ γ ∈ Γ, ∃ k ∈ C, m = γ * k) : μ s ≤ μ C := by
  open Pointwise in
  calc μ s ≤ μ (⋃ g : Γ, g • toMeasurable μ C ∩ s) := by
          refine measure_mono fun m hm => ?_
          obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov m
          refine Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ?_, hm⟩
          exact ⟨k, subset_toMeasurable μ C hk, rfl⟩
      _ ≤ ∑' g : Γ, μ (g • toMeasurable μ C ∩ s) := measure_iUnion_le _
      _ = μ (toMeasurable μ C) := (hs.measure_eq_tsum _).symm
      _ = μ C := measure_toMeasurable C

omit [TopologicalSpace K] [IsTopologicalGroup K] [BorelSpace K] in

theorem isFundamentalDomain_smul_iff {c : NNReal} (hc : c ≠ 0) (s : Set K) :
    IsFundamentalDomain Γ s (c • μ) ↔ IsFundamentalDomain Γ s μ := by
  have hc' : (c : ENNReal) ≠ 0 := by exact_mod_cast hc
  constructor
  · intro h
    refine h.mono fun t ht => ?_
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at ht
    exact ht.resolve_left hc'
  · intro h
    refine h.mono fun t ht => ?_
    rw [Measure.smul_apply, ht, smul_zero]

private theorem exists_measurableSet_unique_smul_mem_of_discrete {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (Γ : Subgroup G) {V : Set G} (hV : IsOpen V) (h1 : (1 : G) ∈ V)
    (hΓV : ∀ γ ∈ Γ, γ ∈ V → γ = 1) :
    ∃ s : Set G, MeasurableSet s ∧ ∀ x : G, ∃! g : Γ, g • x ∈ s := by
  classical

  obtain ⟨U, hUo, hU1, hUV⟩ := exists_open_nhds_one_split (hV.mem_nhds h1)
  let W : Set G := U ∩ (fun u => u⁻¹) ⁻¹' U
  have hWo : IsOpen W := hUo.inter (hUo.preimage continuous_inv)
  have hW1 : (1 : G) ∈ W := ⟨hU1, by simp only [Set.mem_preimage, inv_one]; exact hU1⟩
  have hWW : ∀ a ∈ W, ∀ b ∈ W, a * b⁻¹ ∈ V := fun a ha b hb => hUV a ha.1 b⁻¹ hb.2

  let A : G → Set G := fun g => (fun x => x * g⁻¹) ⁻¹' W
  have hAo : ∀ g, IsOpen (A g) := fun g => hWo.preimage (continuous_mul_const _)
  have hcov : ⋃ g, A g = Set.univ := Set.eq_univ_of_forall fun x =>
    Set.mem_iUnion.2 ⟨x, by simp only [A, Set.mem_preimage, mul_inv_cancel]; exact hW1⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable A hAo
  have hmemT : ∀ x, ∃ g ∈ T, x ∈ A g := fun x => by
    have hx : x ∈ ⋃ g ∈ T, A g := by rw [hTU, hcov]; exact Set.mem_univ x
    obtain ⟨g, hg, hx'⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨g, hg, hx'⟩
  have hTne : T.Nonempty := by
    obtain ⟨g, hg, -⟩ := hmemT 1
    exact ⟨g, hg⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let B : ℕ → Set G := fun i => A (f i)
  have hBo : ∀ i, IsOpen (B i) := fun i => hAo _
  have hBcov : ∀ x, ∃ i, x ∈ B i := by
    intro x
    obtain ⟨g, hgT, hx⟩ := hmemT x
    rw [hf] at hgT
    obtain ⟨i, rfl⟩ := hgT
    exact ⟨i, hx⟩

  have hinj : ∀ i y (δ : Γ), y ∈ B i → δ • y ∈ B i → δ = 1 := by
    intro i y δ hy hδy
    have hm := hWW (δ • y * (f i)⁻¹) hδy (y * (f i)⁻¹) hy
    have he : δ • y * (f i)⁻¹ * (y * (f i)⁻¹)⁻¹ = (δ : G) := by
      simp only [Subgroup.smul_def, smul_eq_mul]
      group
    rw [he] at hm
    exact Subtype.ext (hΓV _ δ.2 hm)

  let E : ℕ → Set G := fun j => ⋃ γ : Γ, (fun x => γ • x) ⁻¹' B j
  have hEo : ∀ j, IsOpen (E j) := fun j => isOpen_iUnion fun γ => (hBo j).preimage
    (by simpa only [Subgroup.smul_def, smul_eq_mul] using continuous_const_mul (γ : G))
  have hE : ∀ j y, y ∈ E j ↔ ∃ δ : Γ, δ • y ∈ B j := fun j y => by
    simp only [E, Set.mem_iUnion, Set.mem_preimage]

  let s : Set G := ⋃ i, (B i \ ⋃ (j : ℕ) (_ : j < i), E j)
  have hs : ∀ y, y ∈ s ↔ ∃ i, y ∈ B i ∧ ∀ j < i, ∀ δ : Γ, δ • y ∉ B j := by
    intro y
    simp only [s, Set.mem_iUnion, Set.mem_sdiff, not_exists]
    constructor
    · rintro ⟨i, hi, hn⟩
      exact ⟨i, hi, fun j hj δ hδ => hn j hj ((hE j y).2 ⟨δ, hδ⟩)⟩
    · rintro ⟨i, hi, hn⟩
      refine ⟨i, hi, fun j hj hy => ?_⟩
      obtain ⟨δ, hδ⟩ := (hE j y).1 hy
      exact hn j hj δ hδ
  refine ⟨s, MeasurableSet.iUnion fun i => (hBo i).measurableSet.diff
    (isOpen_iUnion fun j => isOpen_iUnion fun _ => hEo j).measurableSet, fun x => ?_⟩
  have hP : ∃ i, ∃ γ : Γ, γ • x ∈ B i := by
    obtain ⟨i, hi⟩ := hBcov x
    exact ⟨i, 1, by simpa only [one_smul] using hi⟩
  obtain ⟨γ, hγ⟩ := Nat.find_spec hP
  refine ⟨γ, (hs _).2 ⟨_, hγ, fun j hj δ hδ => Nat.find_min hP hj ⟨δ * γ, by rwa [mul_smul]⟩⟩,
    fun γ' hγ' => ?_⟩
  obtain ⟨i', hi', hmin'⟩ := (hs _).1 hγ'
  have hle : Nat.find hP ≤ i' := Nat.find_min' hP ⟨γ', hi'⟩
  have hge : i' ≤ Nat.find hP := by
    by_contra hlt
    exact hmin' _ (not_le.1 hlt) (γ * γ'⁻¹) (by rw [mul_smul, inv_smul_smul]; exact hγ)
  rw [le_antisymm hge hle] at hi'
  have h1' := hinj _ (γ • x) (γ' * γ⁻¹) hγ (by rw [mul_smul, inv_smul_smul]; exact hi')
  exact mul_inv_eq_one.1 h1'

end General

theorem countable_and_exists_domain (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (K : Subgroup (HA (AF F) σ J)) :
    IsTopologicalGroup K ∧ BorelSpace K ∧
    Countable (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) ∧
    ∀ μ : Measure K, ∃ 𝓕 : Set K,
      IsFundamentalDomain (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) 𝓕 μ := by
  obtain ⟨hc, hd, -⟩ := GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts' F E σ n J
  change Countable (HFinIn (AF F) σ J) at hc
  change DiscreteTopology (HFinIn (AF F) σ J) at hd

  obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.1 (isOpen_discrete ({1} : Set (HFinIn (AF F) σ J)))
  have ht1 : (1 : HA (AF F) σ J) ∈ t := by
    have h : (1 : HFinIn (AF F) σ J) ∈ Subtype.val ⁻¹' t := by rw [hteq]; exact Set.mem_singleton _
    exact h
  have htone : ∀ h ∈ HFinIn (AF F) σ J, h ∈ t → h = 1 := by
    intro h hh hht
    have h' : (⟨h, hh⟩ : HFinIn (AF F) σ J) ∈ Subtype.val ⁻¹' t := hht
    rw [hteq] at h'
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 h')
  have hcnt : Countable (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K) := by
    refine Function.Injective.countable
      (f := fun x => (⟨((x : K) : HA (AF F) σ J), Subgroup.mem_subgroupOf.1 x.2⟩ :
        HFinIn (AF F) σ J)) ?_
    intro x y hxy
    have h2 := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext h2)

  have : SecondCountableTopology (AF F) := AdelicUnitaryTop.secondCountable_adele F
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isModTop
  obtain ⟨m, φ, hφ⟩ := Module.Finite.exists_fin' (AF F) (AF F ⊗[F] E)
  have hq := IsModuleTopology.isOpenQuotientMap_of_surjective hφ
  have : SecondCountableTopology (AF F ⊗[F] E) :=
    hq.isQuotientMap.secondCountableTopology hq.isOpenMap
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AF F ⊗[F] E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  have : SecondCountableTopology (GL (Fin n) (AF F ⊗[F] E)) :=
    Units.isInducing_embedProduct.secondCountableTopology
  have : SecondCountableTopology (HA (AF F) σ J) :=
    (Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val : HR (AF F) σ J → GL (Fin n) (AF F ⊗[F] E))).secondCountableTopology
  have : IsTopologicalGroup (HA (AF F) σ J) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have : BorelSpace (HA (AF F) σ J) := ⟨rfl⟩
  refine ⟨inferInstance, inferInstance, hcnt, fun μ => ?_⟩
  have hK1 : IsTopologicalGroup K := inferInstance
  have hK2 : SecondCountableTopology K := Topology.IsInducing.subtypeVal.secondCountableTopology
  have hK3 : OpensMeasurableSpace K := inferInstance
  obtain ⟨s, hs, hex⟩ := @exists_measurableSet_unique_smul_mem_of_discrete K _ _ hK1 hK2 _ hK3
    (Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K)
    ((Subtype.val : K → HA (AF F) σ J) ⁻¹' t) (ht.preimage continuous_subtype_val) ht1
    (fun γ hγ hγV => Subtype.ext (htone _ (Subgroup.mem_subgroupOf.1 hγ) hγV))
  exact ⟨s, IsFundamentalDomain.mk' hs.nullMeasurableSet hex⟩

theorem domains_and_covolume (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E)
    (K : Subgroup (HA (AF F) σ J)) (Γ : Subgroup K)
    (hΓ : Γ = Subgroup.subgroupOf (G := HA (AF F) σ J) (HFinIn (AF F) σ J) K)
    (cov : Measure K → ℝ)
    (hcov : ∀ ν : Measure K, (∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 ν) →
      ∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 ν ∧ cov ν = (ν 𝓕).toReal)
    (μ : Measure K) (hμ : μ.IsHaarMeasure) :
    (∃ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 μ) ∧
    (∀ 𝓕 : Set K, IsFundamentalDomain Γ 𝓕 μ → cov μ = (μ 𝓕).toReal ∧ μ 𝓕 ≠ 0 ∧
      ∀ C : Set K, MeasurableSet C → (∀ m : K, ∃ γ ∈ Γ, ∃ k ∈ C, m = γ * k) → μ 𝓕 ≤ μ C) ∧
    ∀ c : NNReal, c ≠ 0 → cov (c • μ) = (c : ℝ) * cov μ := by
  obtain ⟨hTG, hB, hcnt, hex⟩ := countable_and_exists_domain F E σ n J K
  rw [← hΓ] at hcnt hex
  have := hμ
  refine ⟨hex μ, fun 𝓕 h𝓕 => ?_, fun c hc => ?_⟩
  · obtain ⟨𝓕', h𝓕', hcv⟩ := hcov μ ⟨𝓕, h𝓕⟩
    refine ⟨?_, @GlobalTheory.ClosedSubgroupCovol.measure_ne_zero _ _ _ _ Γ μ hcnt _ _ h𝓕,
      fun C _ hC => @GlobalTheory.ClosedSubgroupCovol.measure_le_of_cover _ _ _ hTG _ hB Γ μ hcnt _ _ h𝓕 _ hC⟩
    rw [hcv, @GlobalTheory.ClosedSubgroupCovol.measure_eq _ _ _ hTG _ hB Γ μ hcnt _ _ _ h𝓕' h𝓕]
  · obtain ⟨𝓕, h𝓕⟩ := hex μ
    obtain ⟨𝓕', h𝓕', hcv⟩ := hcov μ ⟨𝓕, h𝓕⟩
    obtain ⟨𝓖, h𝓖, hcv'⟩ := hcov (c • μ) ⟨𝓕, (isFundamentalDomain_smul_iff Γ μ hc 𝓕).2 h𝓕⟩
    have h𝓖μ := (isFundamentalDomain_smul_iff Γ μ hc 𝓖).1 h𝓖
    rw [hcv', hcv, Measure.smul_apply,
      @GlobalTheory.ClosedSubgroupCovol.measure_eq _ _ _ hTG _ hB Γ μ hcnt _ _ _ h𝓖μ h𝓕', ENNReal.smul_def,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

end GlobalTheory.ClosedSubgroupCovol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryTransportsGenusOrbitSumStatement
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_transports_genus_orbitSum : ∀ (K V V' : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (e : V ≃ₗ[K] V'), (∀ x y, h' (e x) (e y) = h x y) → ∀ φ : Submodule (𝓞 K) V' → ℝ≥0∞, (∀ (s : Formalism.HermitianLatticesTheory.isom h') (M : Submodule (𝓞 K) V'), φ (s • M) = φ M) → ∀ L : Submodule (𝓞 K) V, (∀ (s : Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V), φ (GlobalTheory.Mass.Transp.img e (s • M)) = φ (GlobalTheory.Mass.Transp.img e M)) ∧ (∀ M : Submodule (𝓞 K) V, GlobalTheory.Mass.Transp.img e M ∈ Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L) ↔ M ∈ Formalism.HermitianLatticesTheory.genus h L) ∧ GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h') (Formalism.HermitianLatticesTheory.genus h' (GlobalTheory.Mass.Transp.img e L)) φ = GlobalTheory.Mass.orbSum (Formalism.HermitianLatticesTheory.isom h) (Formalism.HermitianLatticesTheory.genus h L) (fun M => φ (GlobalTheory.Mass.Transp.img e M)) := by
  first | exact @GlobalTheory.Mass.Transp.orbSum_img | exact GlobalTheory.Mass.Transp.orbSum_img | (intros; apply GlobalTheory.Mass.Transp.orbSum_img <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaFactorsNearOneGivenCompactFactor
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwNear

open GlobalTheory.FlagLeviGroup

variable {n : ℕ} {ε : Fin n → Bool}

theorem J_sq : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem nrm_J_conj (X : Matrix (Fin n) (Fin n) ℂ) : nrm (Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) = nrm X := by
  unfold nrm Formalism.REAL.hs
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  split_ifs <;> simp

private theorem uMat_inv_eq_Jm_conjTranspose_Jm (g : Formalism.REAL.UJ ε) :
    uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hg : (uMat g)ᴴ * (Formalism.REAL.Jm ε * uMat g) = Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc]
    exact g.2
  have h1 : uMat g * uMat g⁻¹ = 1 := by simp [uMat]
  have h2 : Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, J_sq]
  calc uMat g⁻¹ = (Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by
        rw [h2, Matrix.one_mul]
    _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := Matrix.mul_assoc _ _ _
    _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h1, Matrix.mul_one]

theorem nrm_inv (g : Formalism.REAL.UJ ε) : nrm (uMat g⁻¹ - 1) = nrm (uMat g - 1) := by
  have e : uMat g⁻¹ - 1 = Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε := by
    rw [uMat_inv_eq_Jm_conjTranspose_Jm, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, J_sq]
  rw [e, nrm_J_conj, nrm_conjTranspose]

theorem nrm_mul_sub_one (g h : Formalism.REAL.UJ ε) :
    nrm (uMat (g * h) - 1) ≤ nrm (uMat g - 1) * nrm (uMat h - 1) + nrm (uMat g - 1) + nrm (uMat h - 1) := by
  have e : uMat (g * h) - 1 = (uMat g - 1) * (uMat h - 1) + (uMat g - 1) + (uMat h - 1) := by
    rw [show uMat (g * h) = uMat g * uMat h from rfl]
    noncomm_ring
  rw [e]
  calc _ ≤ nrm ((uMat g - 1) * (uMat h - 1) + (uMat g - 1)) + nrm (uMat h - 1) := nrm_add_le _ _
    _ ≤ nrm ((uMat g - 1) * (uMat h - 1)) + nrm (uMat g - 1) + nrm (uMat h - 1) := by
        gcongr
        exact nrm_add_le _ _
    _ ≤ _ := by
        gcongr
        exact nrm_mul_le _ _

theorem nrm_levi_le {a : ℕ} {j : Fin a → ℕ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)} (hW : IsIsoFlag ε j W)
    {u m : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε W) (hm : m ∈ flagM ε W) :
    nrm (uMat m - 1) ≤ nrm (uMat (u * m) - 1) := by

  obtain ⟨hN, hM⟩ := GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps n ε a j W hW
  obtain ⟨htr, -, -, hmul⟩ := GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag n ε a j W hW
  have hX := hN u hu
  obtain ⟨hm1, hm2⟩ := hM m hm
  have hY : uMat m * (uMat m)ᴴ - uMat m ∈ keeps ε W := sub_mem (hmul _ hm1 _ hm2) hm1
  have e : uMat (u * m) - 1 = (uMat u - 1) * uMat m + (uMat m - 1) := by
    rw [show uMat (u * m) = uMat u * uMat m from rfl]
    noncomm_ring
  have key : ((((uMat u - 1) * uMat m) * (uMat m - 1)ᴴ).trace).re = 0 := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one,
      htr _ hX _ hY, Complex.zero_re]
  have hh : Formalism.REAL.hs (uMat m - 1) ≤ Formalism.REAL.hs (uMat (u * m) - 1) := by
    rw [e, hs_add, key]
    linarith [hs_nonneg ((uMat u - 1) * uMat m)]
  exact Real.sqrt_le_sqrt hh

theorem near : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k : Formalism.REAL.UJ ε, nrm (uMat (u * m * k) - 1) ≤ ρ → nrm (uMat k - 1) < ρ → nrm (uMat u - 1) < t ∧ nrm (uMat m - 1) < t ∧ nrm (uMat k - 1) < t := by
  intro n ε a j W hW t ht
  obtain ⟨ρ, hρ0, hρ1, hρt⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 3 ∧ ρ ≤ t / 10 :=
    ⟨min (1 / 3) (t / 10), lt_min (by norm_num) (by linarith), min_le_left _ _, min_le_right _ _⟩
  refine ⟨ρ, hρ0, ?_⟩
  intro u hu m hm k hx hk
  have hK0 := nrm_nonneg (uMat k - 1)

  have hA : nrm (uMat (u * m) - 1) ≤ ρ * ρ + 2 * ρ := by
    have h := nrm_mul_sub_one (u * m * k) k⁻¹
    rw [mul_inv_cancel_right, nrm_inv] at h
    have : nrm (uMat (u * m * k) - 1) * nrm (uMat k - 1) ≤ ρ * ρ := mul_le_mul hx hk.le hK0 hρ0.le
    linarith

  have hM : nrm (uMat m - 1) ≤ nrm (uMat (u * m) - 1) := nrm_levi_le hW hu hm
  have hM0 := nrm_nonneg (uMat m - 1)
  have hU : nrm (uMat u - 1) ≤
      nrm (uMat (u * m) - 1) * nrm (uMat m - 1) + nrm (uMat (u * m) - 1) + nrm (uMat m - 1) := by
    have h := nrm_mul_sub_one (u * m) m⁻¹
    rwa [mul_inv_cancel_right, nrm_inv] at h
  have hρρ : ρ * ρ ≤ ρ / 3 := by nlinarith
  have hs0 : 0 ≤ ρ * ρ + 2 * ρ := by positivity
  have hs1 : ρ * ρ + 2 * ρ ≤ 1 := by linarith
  have hprod : nrm (uMat (u * m) - 1) * nrm (uMat m - 1) ≤ ρ * ρ + 2 * ρ :=
    calc _ ≤ (ρ * ρ + 2 * ρ) * (ρ * ρ + 2 * ρ) := mul_le_mul hA (hM.trans hA) hM0 hs0
      _ ≤ ρ * ρ + 2 * ρ := mul_le_of_le_one_left hs0 hs1
  exact ⟨by linarith, by linarith, by linarith⟩

end GlobalTheory.IwNear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaGaugeDefiniteAndUnitBodyVolumeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawaGauge_definite_and_unitBody_volume : ∀ (n : ℕ), ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsON EN → IsON EM → IsON EK → IsON EL → LieRel EN EM EK EL → dK = dN + dL → (∀ v, gau EN EM EK EL v = 0 → v = 0) ∧ volume {v | gau EN EM EK EL v ≤ 1} = ENNReal.ofReal ((2 : ℝ) ^ ((dN : ℝ) / 2)) * ballVol (2 * dN + dM) * ballVol dL := by
  first | exact @GlobalTheory.IwConst.gau_definite_and_volume | exact GlobalTheory.IwConst.gau_definite_and_volume | (intros; apply GlobalTheory.IwConst.gau_definite_and_volume <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaLieAlgebrasRelativePosition
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst.LiePos

variable {n : ℕ} {ε : Fin n → Bool}

theorem J_mul_J : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem inG_conjTranspose {X : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X) : Formalism.REAL.inG ε Xᴴ := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := J_mul_J
  have hJ' : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y) = Y := fun Y => by
    rw [← mul_assoc, hJ, one_mul]
  unfold Formalism.REAL.inG at *
  rw [conjTranspose_conjTranspose]
  have e := congrArg (fun M => Formalism.REAL.Jm ε * M * Formalism.REAL.Jm ε) h
  simp only [mul_add, add_mul, mul_assoc, hJ, hJ', mul_one, mul_zero, zero_mul] at e
  rw [add_comm]
  exact e

theorem inG_sub {X Y : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X) (k : Formalism.REAL.inG ε Y) :
    Formalism.REAL.inG ε (X - Y) := by
  unfold Formalism.REAL.inG at *
  rw [conjTranspose_sub, sub_mul, mul_sub]
  rw [show Xᴴ * Formalism.REAL.Jm ε - Yᴴ * Formalism.REAL.Jm ε + (Formalism.REAL.Jm ε * X - Formalism.REAL.Jm ε * Y) =
      (Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X) - (Yᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Y) by abel, h, k, sub_zero]

theorem comm_of_maxK {g : Formalism.REAL.UJ ε} (hg : g ∈ maxK ε) :
    uMat g * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * uMat g := by
  have hU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g * (uMat g)ᴴ = 1 := mul_eq_one_comm.mp hg
  calc uMat g * Formalism.REAL.Jm ε = uMat g * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) := by rw [hU]
    _ = (uMat g * (uMat g)ᴴ) * Formalism.REAL.Jm ε * uMat g := by simp only [mul_assoc]
    _ = Formalism.REAL.Jm ε * uMat g := by rw [h1, one_mul]

theorem skew_of_comm {X : Matrix (Fin n) (Fin n) ℂ} (h : Formalism.REAL.inG ε X)
    (hc : X * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * X) : Xᴴ = -X := by
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := J_mul_J
  have h' : Xᴴ * Formalism.REAL.Jm ε = -(X * Formalism.REAL.Jm ε) := by
    rw [hc]; exact eq_neg_of_add_eq_zero_left h
  calc Xᴴ = Xᴴ * Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [mul_assoc, hJ, mul_one]
    _ = -(X * Formalism.REAL.Jm ε) * Formalism.REAL.Jm ε := by rw [h']
    _ = -X := by rw [neg_mul, mul_assoc, hJ, mul_one]

theorem exp_unitary {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Zᴴ = -Z) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Z))ᴴ * NormedSpace.exp ((t : ℂ) • Z) = 1 := by
  have hA : ((t : ℂ) • Z)ᴴ = -((t : ℂ) • Z) := by
    rw [conjTranspose_smul, hZ, smul_neg, Complex.star_def, Complex.conj_ofReal]
  have hc : Commute (-((t : ℂ) • Z)) ((t : ℂ) • Z) := (Commute.refl _).neg_left
  rw [← Matrix.exp_conjTranspose, hA, ← Matrix.exp_add_of_commute _ _ hc, neg_add_cancel, NormedSpace.exp_zero]

theorem mem_span_of_subset {S S' : Set (Formalism.REAL.UJ ε)} {d d' : ℕ} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}
    {E' : Fin d' → Matrix (Fin n) (Fin n) ℂ} (h : IsCut ε S E) (h' : IsCut ε S' E') (hS : S ⊆ S') (i : Fin d) :
    E i ∈ Submodule.span ℝ (Set.range E') := by
  obtain ⟨A', -, -, hA', hS'⟩ := h'
  have hT : E i ∈ A' := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε S d E h).2.1 A' (fun g hg => by
    have hg' : g ∈ S' := hS hg
    rw [hS'] at hg'
    exact hg') i
  exact (hA' _).1 ⟨hT, h.inG (Submodule.subset_span ⟨i, rfl⟩)⟩

theorem lieRel : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsCut ε (maxK ε ∩ flagM ε W) EL → LieRel EN EM EK EL := by
  intro n ε a j W hW dN dM dK dL EN EM EK EL hN hM hK hL
  obtain ⟨hlow, hkeep⟩ := GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps n ε a j W hW
  obtain ⟨htr, hle, hone, -⟩ := GlobalTheory.T.trace_lowering_mul_keeping_isotropicFlag n ε a j W hW
  have hENlow : ∀ i, EN i ∈ lowers ε W := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dN EN hN).2.1 (lowers ε W) hlow
  have hEMkeep : ∀ k, EM k ∈ keeps ε W :=
    (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dM EM hM).2.1 (keeps ε W) (fun m hm => sub_mem (hkeep m hm).1 hone)
  have hEMstar : ∀ k, (EM k)ᴴ ∈ keeps ε W := by
    let T2 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
      { carrier := {Y | Yᴴ ∈ keeps ε W}
        add_mem' := fun {A B} hA hB => by
          simp only [Set.mem_ofPred_eq, conjTranspose_add] at *
          exact add_mem hA hB
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, conjTranspose_zero]
          exact zero_mem _
        smul_mem' := fun c Y hY => by
          simp only [Set.mem_ofPred_eq] at *
          rw [conjTranspose_smul, star_trivial]
          exact Submodule.smul_mem _ c hY }
    exact (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dM EM hM).2.1 T2 (fun m hm => by
      change (uMat m - 1)ᴴ ∈ keeps ε W
      rw [conjTranspose_sub, conjTranspose_one]
      exact sub_mem (hkeep m hm).2 hone)
  let TC : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    { carrier := {Y | Y * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Y}
      add_mem' := fun {A B} hA hB => by
        simp only [Set.mem_ofPred_eq] at *
        rw [add_mul, mul_add, hA, hB]
      zero_mem' := by simp
      smul_mem' := fun c Y hY => by
        simp only [Set.mem_ofPred_eq] at *
        rw [smul_mul_assoc, mul_smul_comm, hY] }
  have hEK : ∀ i, EK i ∈ TC := (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dK EK hK).2.1 TC (fun g hg => by
    change (uMat g - 1) * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (uMat g - 1)
    rw [sub_mul, mul_sub, one_mul, mul_one, comm_of_maxK hg])
  have hspan : Submodule.span ℝ (Set.range EK) ≤ TC :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hEK i)
  have hELK : ∀ i, EL i ∈ Submodule.span ℝ (Set.range EK) :=
    mem_span_of_subset hL hK Set.inter_subset_left
  refine ⟨fun i k => htr _ (hENlow i) _ (hEMstar k), fun i k => htr _ (hENlow i) _ (hEMkeep k),
    fun i k => htr _ (hENlow i) _ (hle (hENlow k)), mem_span_of_subset hL hM Set.inter_subset_right, hELK,
    fun i => skew_of_comm (hK.inG (hELK i)) (hspan (hELK i)), fun i => ?_⟩
  have hG : Formalism.REAL.inG ε (EN i) := hN.inG (Submodule.subset_span ⟨i, rfl⟩)
  have hY : Formalism.REAL.inG ε (EN i - (EN i)ᴴ) := inG_sub hG (inG_conjTranspose hG)
  have hskew : (EN i - (EN i)ᴴ)ᴴ = -(EN i - (EN i)ᴴ) := by
    rw [conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]
  refine (GlobalTheory.T.lie_algebra_of_isCutOutByRealMatrixAlgebra n ε _ dK EK hK).2.2 _ hY (fun t g hg => ?_)
  change (uMat g)ᴴ * uMat g = 1
  rw [hg]
  exact exp_unitary hskew t

end GlobalTheory.IwConst.LiePos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalInnerLatticeEqOfInnerPreimageEqStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localInnerLattice_eq_of_innerPreimage_eq : ∀ (D : D7) (Z : LocDat D) (p : PlF D) {T : D.host.E} (G : LFlag (VS D) D.R.rS T) (Fr : LocNG.FrameD (locH Z p) D.R.rS), Fr.f = (fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ₁ Λ₂ : LV D, Submodule.IsLattice D.host.E Λ₁ → Submodule.IsLattice D.host.E Λ₂ → Lsub Λ₁ G = Lsub Λ₂ G → (locH Z p).Lset (lattice₂ D Z.M p Λ₁) Fr.f = (locH Z p).Lset (lattice₂ D Z.M p Λ₂) Fr.f := by
  first | exact @GlobalTheory.Unfold.InnerLoc.lset_eq_of_lsub_eq | exact GlobalTheory.Unfold.InnerLoc.lset_eq_of_lsub_eq | (intros; apply GlobalTheory.Unfold.InnerLoc.lset_eq_of_lsub_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrbitLatticesInfFrameSpanEqStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrbitLattices_inf_frameSpan_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → Λ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') = Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F') := by
  first | exact @GlobalTheory.FrameSpanLat.inf_span_eq | exact GlobalTheory.FrameSpanLat.inf_span_eq | (intros; apply GlobalTheory.FrameSpanLat.inf_span_eq <;> assumption)
end

