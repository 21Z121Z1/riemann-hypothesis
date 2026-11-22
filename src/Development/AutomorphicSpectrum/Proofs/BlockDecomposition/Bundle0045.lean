import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EncardSmulMemLeEncardSmulInterNonempty
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundFinitePlaces
section
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Wedge

theorem updateRow_submatrix_eq {K ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (U : Matrix ι κ K) (s : κ → ι) (k : κ) (i : ι) :
    (U.submatrix s id).updateRow k (U i) = U.submatrix (Function.update s k i) id := by
  ext j l
  by_cases h : j = k
  · subst h
    simp [Matrix.updateRow_apply, Function.update_self]
  · simp [Matrix.updateRow_apply, h, Function.update_of_ne h]

theorem eq_mul_of_det_ne_zero {K ι κ : Type} [Field K] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ K) (s : κ → ι) (hd : (U.submatrix s id).det ≠ 0) :
    U = (Matrix.of fun i k => (U.submatrix s id).det⁻¹ *
      (U.submatrix (Function.update s k i) id).det) * U.submatrix s id := by
  ext i l
  rw [Matrix.mul_apply]
  have key : ∀ k, (U.submatrix (Function.update s k i) id).det
      = Matrix.cramer (U.submatrix s id).transpose (U i) k := by
    intro k
    rw [← updateRow_submatrix_eq, Matrix.cramer_apply, Matrix.updateCol_transpose,
      Matrix.det_transpose]
  have hv := Matrix.mulVec_cramer (U.submatrix s id).transpose (U i)
  rw [Matrix.mulVec_transpose, Matrix.det_transpose] at hv
  have hl := congrFun hv l
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at hl
  simp only [Matrix.of_apply, key, mul_assoc]
  rw [← Finset.mul_sum, hl, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

theorem pairF_of_mulF : MulF → PairF := by
  intro hM
  unfold PairF
  intro K ι κ _ _ _ _ _ U W
  classical
  have hsz0 : ∀ {a b : Type} (g : Matrix a b K), 0 ≤ sz g := by
    intro a b g
    unfold sz
    exact Real.iSup_nonneg (fun p => norm_nonneg _)
  have hnF0 : ∀ (X : Matrix ι κ K), 0 ≤ nF X := by
    intro X
    unfold nF
    exact Real.iSup_nonneg (fun s => norm_nonneg _)
  have hdetT : (Uᵀ * W).det = (Wᵀ * U).det := by
    rw [← Matrix.det_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  by_cases h : ∃ s : κ → ι, (U.submatrix s id).det ≠ 0
  · haveI : Nonempty (κ → ι) := ⟨h.choose⟩
    obtain ⟨s₀, hs₀⟩ := Finite.exists_max (fun s : κ → ι => ‖(U.submatrix s id).det‖)
    have hd : (U.submatrix s₀ id).det ≠ 0 := by
      obtain ⟨s, hs⟩ := h
      intro h0
      have h1 := hs₀ s
      simp only [h0, norm_zero] at h1
      exact hs (norm_le_zero_iff.mp h1)
    have hnU : nF U = ‖(U.submatrix s₀ id).det‖ := by
      unfold nF
      apply le_antisymm
      · exact ciSup_le hs₀
      · exact le_ciSup (f := fun s : κ → ι => ‖(U.submatrix s id).det‖)
          (Set.finite_range _).bddAbove s₀
    set G : Matrix ι κ K := Matrix.of fun i k => (U.submatrix s₀ id).det⁻¹ *
      (U.submatrix (Function.update s₀ k i) id).det with hG
    have hUG : U = G * U.submatrix s₀ id := eq_mul_of_det_ne_zero U s₀ hd
    have hszG : sz Gᵀ ≤ 1 := by
      unfold sz
      apply Real.iSup_le ?_ zero_le_one
      intro p
      simp only [Matrix.transpose_apply, hG, Matrix.of_apply, norm_mul, norm_inv]
      rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hd), mul_one]
      exact hs₀ _
    have hmain : ‖(Gᵀ * W).det‖ ≤ nF W := by
      have h1 := (hM K ι κ κ W).1 Gᵀ
      have h2 := (hM K ι κ κ W).2.2 (Gᵀ * W)
      rw [h2] at h1
      calc ‖(Gᵀ * W).det‖ ≤ sz Gᵀ ^ Fintype.card κ * nF W := h1
        _ ≤ 1 * nF W := by
          apply mul_le_mul_of_nonneg_right _ (hnF0 W)
          exact pow_le_one₀ (hsz0 _) hszG
        _ = nF W := one_mul _
    have hfac : (Uᵀ * W).det = (U.submatrix s₀ id).det * (Gᵀ * W).det := by
      conv_lhs => rw [hUG]
      rw [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.det_mul, Matrix.det_transpose]
    rw [hfac, norm_mul, hnU]
    exact mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
  · simp only [not_exists, not_not] at h
    have hnU : nF U = 0 := by
      unfold nF
      simp only [h, norm_zero]
      first
        | exact Real.iSup_const_zero
        | simp
    have h1 := (hM K ι κ κ U).1 Wᵀ
    have h2 := (hM K ι κ κ U).2.2 (Wᵀ * U)
    rw [h2, hnU, mul_zero] at h1
    rw [hdetT, hnU, zero_mul]
    exact h1

end GlobalTheory.CompanionTheory.Wedge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundInfinitePlaces
section
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Wedge

open ComplexOrder in

theorem pairI_of_detMono : DetMono → PairI := by
  intro hD ι κ _ _ _ U W
  have hG : (Uᴴ * U).PosSemidef := posSemidef_conjTranspose_mul_self U
  have hH : (Wᴴ * W).PosSemidef := posSemidef_conjTranspose_mul_self W
  have hHn : 0 ≤ ((Wᴴ * W).det).re := (Complex.le_def.1 hH.det_nonneg).1
  have hGn : 0 ≤ ((Uᴴ * U).det).re := (Complex.le_def.1 hG.det_nonneg).1
  have hGim : ((Uᴴ * U).det).im = 0 := ((Complex.le_def.1 hG.det_nonneg).2).symm
  unfold nI
  by_cases hdet : (Uᴴ * U).det = 0
  ·
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hUv : U *ᵥ v = 0 := by
      have := (Matrix.conjTranspose_mul_self_mulVec_eq_zero U v).1 hv
      exact this
    have hM : ((Uᴴ * W)ᴴ) *ᵥ v = 0 := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec, hUv,
        Matrix.mulVec_zero]
    have hd : ((Uᴴ * W)ᴴ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, hM⟩
    have hd' : (Uᴴ * W).det = 0 := by
      rw [det_conjTranspose] at hd
      simpa using hd
    rw [hd', norm_zero]
    have : ((Uᴴ * U).det).re * ((Wᴴ * W).det).re ≥ 0 := mul_nonneg hGn hHn
    simpa using this
  · set G := Uᴴ * U with hGdef
    set M := Uᴴ * W with hMdef
    have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
    have hGi : G * G⁻¹ = 1 := mul_nonsing_inv _ hu
    have hiG : G⁻¹ * G = 1 := nonsing_inv_mul _ hu
    have hGh : Gᴴ = G := hG.isHermitian
    have hih : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hGh]
    have hMh : Mᴴ = Wᴴ * U := by
      rw [hMdef, conjTranspose_mul, conjTranspose_conjTranspose]
    set T := G⁻¹ * M with hT
    have hTh : Tᴴ = Mᴴ * G⁻¹ := by rw [hT, conjTranspose_mul, hih]
    have hGT : G * T = M := by rw [hT, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
    have hX : (Tᴴ * G * T).PosSemidef := hG.conjTranspose_mul_mul_same T
    have hXe : Tᴴ * G * T = Mᴴ * T := by
      rw [Matrix.mul_assoc, hGT, hTh, Matrix.mul_assoc, ← hT]
    have hXp : (Mᴴ * T).PosSemidef := hXe ▸ hX
    have e1 : Wᴴ * (U * T) = Mᴴ * T := by rw [hMh, Matrix.mul_assoc]
    have e2 : Tᴴ * Uᴴ * W = Mᴴ * T := by
      rw [Matrix.mul_assoc, ← hMdef, hTh, Matrix.mul_assoc, ← hT]
    have e3 : Tᴴ * Uᴴ * (U * T) = Mᴴ * T := by
      rw [← hXe, hGdef]
      simp only [Matrix.mul_assoc]

    have hZ : (W - U * T)ᴴ * (W - U * T) = Wᴴ * W - Mᴴ * T := by
      rw [conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
        e1, e2, e3]
      abel
    have hmono : ((Mᴴ * T).det).re ≤ ((Wᴴ * W).det).re :=
      hD κ _ _ hXp (hZ ▸ posSemidef_conjTranspose_mul_self (W - U * T))
    have hiGd : (G⁻¹).det * G.det = 1 := by rw [← det_mul, hiG, det_one]
    have hdX : (Mᴴ * T).det * G.det = ((‖M.det‖ ^ 2 : ℝ) : ℂ) := by
      have hc : (starRingEnd ℂ) M.det * M.det = ((‖M.det‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul']
        push_cast
        rfl
      rw [det_mul, hT, det_mul, det_conjTranspose, ← hc, Complex.star_def]
      linear_combination ((starRingEnd ℂ) M.det * M.det) * hiGd
    have hre : ((Mᴴ * T).det).re * G.det.re = ‖M.det‖ ^ 2 := by
      have := congrArg Complex.re hdX
      rw [Complex.mul_re, hGim, mul_zero, sub_zero, Complex.ofReal_re] at this
      exact this
    rw [← hre, mul_comm]
    exact mul_le_mul_of_nonneg_left hmono hGn

end GlobalTheory.CompanionTheory.Wedge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainSplit
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem exists_borel_section_ker :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) [Countable Γ], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ D : Set π.ker, MeasurableSet D ∧ (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) ∧ ∀ (ν : Measure π.ker) [ν.IsHaarMeasure], IsFundamentalDomain (Γ.subgroupOf π.ker) D ν ∧ ν D ≠ 0 ∧ ν D < ⊤ := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ _ hU hK
  obtain ⟨U, hU, hU1⟩ := hU
  obtain ⟨K, hKc, hK⟩ := hK
  have hcl : IsClosed (π.ker : Set P) := by
    have : (π.ker : Set P) = π ⁻¹' {1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hπ
  have hemb : IsClosedEmbedding (Subtype.val : π.ker → P) := hcl.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace π.ker := hemb.locallyCompactSpace
  haveI : SecondCountableTopology π.ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace π.ker := Subtype.borelSpace _
  haveI : Countable (Γ.subgroupOf π.ker) :=
    Function.Injective.countable (f := fun h : Γ.subgroupOf π.ker =>
      (⟨((h : π.ker) : P), h.2⟩ : Γ)) (fun a b hab => by
        have h1 : ((a : π.ker) : P) = ((b : π.ker) : P) := congrArg (fun x : Γ => (x : P)) hab
        exact Subtype.ext (Subtype.ext h1))
  haveI : DiscreteTopology (Γ.subgroupOf π.ker) := by
    refine discreteTopology_of_isOpen_singleton_one ?_
    have hc : Continuous fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P) :=
      continuous_subtype_val.comp continuous_subtype_val
    have : ({1} : Set (Γ.subgroupOf π.ker)) =
        (fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P)) ⁻¹' interior U := by
      ext h
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        exact mem_interior_iff_mem_nhds.2 hU
      · intro hh
        have h1 : ((h : π.ker) : P) = 1 :=
          hU1 _ (Subgroup.mem_subgroupOf.1 h.2) (interior_subset hh)
        exact Subtype.ext (Subtype.ext h1)
    rw [this]
    exact isOpen_interior.preimage hc
  obtain ⟨D, hDm, hDu, hDf⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Γ.subgroupOf π.ker)
  refine ⟨D, hDm, hDu, fun ν _ => ⟨hDf ν, (hDf ν).measure_ne_zero (NeZero.ne ν), ?_⟩⟩
  have hKc' : IsCompact ((Subtype.val : π.ker → P) ⁻¹' K) := hemb.isCompact_preimage hKc
  refine lt_of_le_of_lt
    (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers (hDf ν)
      (D' := (Subtype.val : π.ker → P) ⁻¹' K) (.of_forall fun m => ?_)) hKc'.measure_lt_top
  obtain ⟨γ, hγ, hπγ, hmem⟩ := hK m m.2
  have hγk : γ ∈ π.ker := hπγ
  refine ⟨⟨⟨γ, hγk⟩, Subgroup.mem_subgroupOf.2 hγ⟩, ?_⟩
  exact hmem

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicHaarDecomposition
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem conj_haar_character :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (D : Set π.ker), MeasurableSet D → IsFundamentalDomain (Γ.subgroupOf π.ker) D ν → ν D ≠ 0 → ν D < ⊤ → ∃ δ : G₁ →* ℝ≥0, Measurable δ ∧ (∀ γ ∈ Γ₁, δ γ = 1) ∧ ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = δ u • ν := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ _ hΓ ν _ D hDm hD hD0 hDtop
  classical
  have hKc : IsClosed (π.ker : Set P) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hKc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have hcont : ∀ g : P, Continuous (fun m : π.ker => MulAut.conjNormal g m) := by
    intro g
    apply continuous_induced_rng.2
    have h1 : (Subtype.val ∘ fun m : π.ker => MulAut.conjNormal g m) = fun m : π.ker => g * (m : P) * g⁻¹ := by
      funext m
      simp only [Function.comp_apply, MulAut.conjNormal_apply]
    rw [h1]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hsymm : ∀ g : P, ⇑(MulEquiv.symm (MulAut.conjNormal g : MulAut π.ker)) =
      fun m => MulAut.conjNormal g⁻¹ m := by
    intro g
    funext m
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    group
  have hex : ∀ u : G₁, ∃ c : ℝ≥0,
      Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = c • ν := by
    intro u
    haveI : (Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν).IsHaarMeasure :=
      MulEquiv.isHaarMeasure_map ν (MulAut.conjNormal (ι u) : MulAut π.ker) (hcont _)
        (by convert hcont (ι u)⁻¹ using 1; exact hsymm _)
    exact ⟨_, Measure.isMulLeftInvariant_eq_smul _ ν⟩
  choose a ha using hex
  have hcancel : ∀ b c : ℝ≥0, (b : ℝ≥0∞) * ν D = (c : ℝ≥0∞) * ν D → b = c := by
    intro b c h
    exact_mod_cast (ENNReal.mul_left_inj hD0 hDtop.ne).mp h
  have hpre : ∀ v (S : Set π.ker), MeasurableSet S →
      ν ((fun m : π.ker => MulAut.conjNormal (ι v) m) ⁻¹' S) = (a v : ℝ≥0∞) * ν S := by
    intro v S hS
    rw [← Measure.map_apply (hcont _).measurable hS, ha v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcomp : ∀ u v, (fun m : π.ker => MulAut.conjNormal (ι (u * v)) m) ⁻¹' D =
      (fun m : π.ker => MulAut.conjNormal (ι v) m) ⁻¹'
        ((fun m : π.ker => MulAut.conjNormal (ι u) m) ⁻¹' D) := by
    intro u v
    ext m
    simp only [Set.mem_preimage, map_mul, MulAut.mul_apply]
  have hmul : ∀ u v, a (u * v) = a u * a v := by
    intro u v
    apply hcancel
    rw [← hpre (u * v) D hDm, hcomp, hpre v _ ((hcont _).measurable hDm), hpre u D hDm,
      ENNReal.coe_mul]
    ring
  haveI : Countable (Γ.subgroupOf π.ker) := by
    have hinj : Function.Injective (fun x : Γ.subgroupOf π.ker =>
        (⟨((x : π.ker) : P), Subgroup.mem_subgroupOf.1 x.2⟩ : Γ)) := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subtype.mk.injEq] at h
      exact h
    exact hinj.countable
  haveI : MeasurableConstSMul (Γ.subgroupOf π.ker) π.ker :=
    ⟨fun c => by
      show Measurable (fun x : π.ker => (c : π.ker) * x)
      exact measurable_id'.const_mul _⟩
  haveI : SMulInvariantMeasure (Γ.subgroupOf π.ker) π.ker ν :=
    ⟨fun c s _ => by
      show ν ((fun x : π.ker => (c : π.ker) * x) ⁻¹' s) = ν s
      exact measure_preimage_mul ν _ s⟩
  have hΓ1 : ∀ γ ∈ Γ₁, a γ = 1 := by
    intro γ hγ
    have hg : ι γ ∈ Γ := hΓ γ hγ
    have hqmp : Measure.QuasiMeasurePreserving
        (fun m : π.ker => MulAut.conjNormal (ι γ) m) ν ν := by
      refine ⟨(hcont _).measurable, ?_⟩
      rw [ha γ]
      intro s hs
      rw [Measure.smul_apply, hs, smul_zero]
    obtain ⟨e, he⟩ : ∃ e : Γ.subgroupOf π.ker → Γ.subgroupOf π.ker,
        ∀ s, ((e s : π.ker) : P) = (ι γ)⁻¹ * ((s : π.ker) : P) * ι γ := by
      refine ⟨fun s => ⟨⟨(ι γ)⁻¹ * ((s : π.ker) : P) * ι γ, ?_⟩, ?_⟩, fun s => rfl⟩
      · rw [MonoidHom.mem_ker]
        simp [MonoidHom.mem_ker.1 (s : π.ker).2]
      · exact Subgroup.mem_subgroupOf.2
          (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) (Subgroup.mem_subgroupOf.1 s.2)) hg)
    have hebij : Function.Bijective e := by
      constructor
      · intro s t hst
        have h1 := congrArg (fun x : Γ.subgroupOf π.ker => ((x : π.ker) : P)) hst
        simp only [he, mul_left_inj, mul_right_inj] at h1
        apply Subtype.ext
        apply Subtype.ext
        exact h1
      · intro t
        obtain ⟨s, hs⟩ : ∃ s : Γ.subgroupOf π.ker,
            ((s : π.ker) : P) = ι γ * ((t : π.ker) : P) * (ι γ)⁻¹ := by
          refine ⟨⟨⟨ι γ * ((t : π.ker) : P) * (ι γ)⁻¹, ?_⟩, ?_⟩, rfl⟩
          · rw [MonoidHom.mem_ker]
            simp [MonoidHom.mem_ker.1 (t : π.ker).2]
          · exact Subgroup.mem_subgroupOf.2
              (Γ.mul_mem (Γ.mul_mem hg (Subgroup.mem_subgroupOf.1 t.2)) (Γ.inv_mem hg))
        refine ⟨s, Subtype.ext (Subtype.ext ?_)⟩
        rw [he, hs]
        group
    have hsemi : ∀ s : Γ.subgroupOf π.ker, Function.Semiconj
        (fun m : π.ker => MulAut.conjNormal (ι γ) m) (fun x => e s • x) (fun x => s • x) := by
      intro s x
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, he]
      group
    have hfd := hD.preimage_of_equiv hqmp hebij hsemi
    have hmeq : ν D = ν ((fun m : π.ker => MulAut.conjNormal (ι γ) m) ⁻¹' D) :=
      hD.measure_eq hfd
    apply hcancel
    rw [← hpre γ D hDm, ← hmeq, ENNReal.coe_one, one_mul]
  have hFc : Continuous (fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) := by
    apply continuous_induced_rng.2
    have h1 : (Subtype.val ∘ fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) =
        fun p => ι p.1 * (p.2 : P) * (ι p.1)⁻¹ := by
      funext p
      simp only [Function.comp_apply, MulAut.conjNormal_apply]
    rw [h1]
    exact ((hι.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
      (hι.comp continuous_fst).inv
  have hE : MeasurableSet ((fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) ⁻¹' D) :=
    hFc.measurable hDm
  have ha_eq : a = fun u =>
      (ν ((fun m : π.ker => MulAut.conjNormal (ι u) m) ⁻¹' D) / ν D).toNNReal := by
    funext u
    rw [hpre u D hDm, ENNReal.mul_div_cancel_right hD0 hDtop.ne, ENNReal.toNNReal_coe]
  have hmeas : Measurable a := by
    rw [ha_eq]
    exact ((measurable_measure_prodMk_left hE).div_const _).ennreal_toNNReal
  exact ⟨{ toFun := a, map_one' := hΓ1 1 Γ₁.one_mem, map_mul' := hmul }, hmeas, hΓ1,
    fun u => ha u⟩

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIntegralUnfolding
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem aedisjoint_smul_image_prod : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ γ : Γ, γ ≠ 1 → AEDisjoint (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) (γ • (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))) (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ hΓ ν _ μ₁ _ D 𝓕₁ hD h𝓕 γ hγ
  have hker : ∀ z : π.ker, π (z : P) = 1 := fun z => MonoidHom.mem_ker.1 z.2
  have hfa : ∀ z : π.ker × G₁, GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι z = (z.1 : P) * ι z.2 :=
    GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply ι π hι hπ hπι
  set f := GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι with hf
  have hπx : ∀ z : π.ker × G₁, π (f z) = z.2 := by
    intro z
    rw [hfa, map_mul, hker, one_mul, hπι]
  let g : Γ₁ := ⟨π γ, hΓ γ γ.2⟩
  have hsub : γ • (f '' (D ×ˢ 𝓕₁)) ∩ f '' (D ×ˢ 𝓕₁) ⊆ π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁) := by
    rintro x ⟨⟨y, ⟨z, ⟨-, hz⟩, rfl⟩, rfl⟩, ⟨z', ⟨-, hz'⟩, hzx⟩⟩
    dsimp only at hzx ⊢
    have hγπ : π (γ • f z) = π γ * z.2 := by
      rw [Subgroup.smul_def, smul_eq_mul, map_mul, hπx]
    refine ⟨⟨z.2, hz, ?_⟩, ?_⟩
    · dsimp only
      rw [hγπ, Subgroup.smul_def, smul_eq_mul]
    · rw [← hzx, hπx]
      exact hz'
  by_cases hg : g = 1
  · have hγk : (γ : P) ∈ π.ker := MonoidHom.mem_ker.2 (congrArg Subtype.val hg)
    suffices hempty : γ • (f '' (D ×ˢ 𝓕₁)) ∩ f '' (D ×ˢ 𝓕₁) = ∅ by
      show Measure.map f (ν.prod μ₁) _ = 0
      rw [hempty, measure_empty]
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨y, ⟨z, ⟨hz1, hz2⟩, rfl⟩, rfl⟩, ⟨z', ⟨hz1', hz2'⟩, hzx⟩⟩
    dsimp only at hzx
    have h2 : z'.2 = z.2 := by
      have := congrArg π hzx
      rw [hπx, Subgroup.smul_def, smul_eq_mul, map_mul, hπx, MonoidHom.mem_ker.1 hγk, one_mul] at this
      exact this
    have h1 : (z'.1 : P) = (γ : P) * z.1 := by
      have := hzx
      rw [hfa, Subgroup.smul_def, smul_eq_mul, hfa, h2, ← mul_assoc] at this
      exact mul_right_cancel this
    let γk : Γ.subgroupOf π.ker := ⟨⟨γ, hγk⟩, Subgroup.mem_subgroupOf.2 γ.2⟩
    obtain ⟨g₀, -, huniq⟩ := hD z.1
    have e1 : (1 : Γ.subgroupOf π.ker) = g₀ := huniq 1 (by show (1 : Γ.subgroupOf π.ker) • z.1 ∈ D; rw [one_smul]; exact hz1)
    have e2 : γk = g₀ := huniq γk (by
      show γk • z.1 ∈ D
      have : γk • z.1 = z'.1 := Subtype.ext (by rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]; exact h1.symm)
      rw [this]
      exact hz1')
    apply hγ
    have := congrArg (fun t : Γ.subgroupOf π.ker => ((t : π.ker) : P)) (e2.trans e1.symm)
    exact Subtype.ext this
  · have hN : μ₁ (g • 𝓕₁ ∩ 𝓕₁) = 0 := by
      have := h𝓕.aedisjoint hg
      simp only [Function.onFun, one_smul] at this
      exact this
    have hpre : f ⁻¹' (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = Set.univ ×ˢ (g • 𝓕₁ ∩ 𝓕₁) := by
      ext z
      simp only [Set.mem_preimage, hπx, Set.mem_prod, Set.mem_univ, true_and]
    have hmap : Measure.map f (ν.prod μ₁) (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = 0 := by
      rw [show Measure.map f (ν.prod μ₁) (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = (ν.prod μ₁) (f ⁻¹' (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁))) from
        f.toMeasurableEquiv.map_apply _, hpre, Measure.prod_prod, hN, mul_zero]
    exact measure_mono_null hsub hmap

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositiveOnSubspaceOpen
section
open scoped Matrix Topology

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem isOpen_posOn (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)) :
    IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} := by
  set K : Set (Fin n → ℂ) := (S : Set (Fin n → ℂ)) ∩ Metric.sphere 0 1 with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_left S.closed_of_finiteDimensional
  let F : Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → ℝ := fun Z w => ε * (star w ⬝ᵥ Z.mulVec w).re
  have hF : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) => F p.1 p.2) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_snd.star).dotProduct (continuous_fst.matrix_mulVec continuous_snd)))
  have hscale : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (c : ℝ),
      F Z ((c : ℂ) • w) = c ^ 2 * F Z w := by
    intro Z w c
    simp only [F, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
    ring
  have heq : {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} = {Z | ∀ w ∈ K, 0 < F Z w} := by
    ext Z
    constructor
    · rintro hZ w ⟨hwS, hw1⟩
      refine hZ w hwS ?_
      rintro rfl
      simp at hw1
    · intro hZ w hwS hw0
      have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hmem : ((‖w‖⁻¹ : ℝ) : ℂ) • w ∈ K := by
        refine ⟨S.smul_mem _ hwS, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
      have h2 := hZ _ hmem
      rw [hscale] at h2
      exact pos_of_mul_pos_right h2 (by positivity)
  rw [heq, isOpen_iff_mem_nhds]
  intro Z₀ hZ₀
  exact hKc.eventually_forall_of_forall_eventually fun w hw =>
    (hF.tendsto (Z₀, w)).eventually (lt_mem_nhds (hZ₀ w hw))

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end

