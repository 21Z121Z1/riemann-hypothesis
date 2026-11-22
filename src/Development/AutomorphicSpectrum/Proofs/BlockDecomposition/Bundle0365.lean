import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEpsilonCentralizerBound

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactConjTwistedCentralizer
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.LocVan.TNorm

variable {n : ℕ}

theorem uOf_zero' (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) : uOf (0 : nilrad W₁ W₂) = 1 :=
  Units.ext (by simp)

theorem uOf_mul_mem_nSet {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    (C : Set (GL (Fin n) ℂ)) (X : nilrad W₁ W₂) (x : GL (Fin n) ℂ) :
    uOf X * x ∈ nSet W₁ W₂ C ↔ x ∈ nSet W₁ W₂ C := by
  constructor
  · rintro ⟨Y, c, hc, h⟩
    refine ⟨nmul hW (ninv hW X) Y, c, hc, ?_⟩
    rw [uOf_nmul, uOf_ninv, mul_assoc, h, inv_mul_cancel_left]
  · rintro ⟨Y, c, hc, rfl⟩
    exact ⟨nmul hW X Y, c, hc, by rw [uOf_nmul, mul_assoc]⟩

theorem nSet_mono (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {C C' : Set (GL (Fin n) ℂ)} (h : C ⊆ C') :
    nSet W₁ W₂ C ⊆ nSet W₁ W₂ C' := by
  rintro _ ⟨X, c, hc, rfl⟩
  exact ⟨X, c, h hc, rfl⟩

theorem isOpen_nSet (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {U : Set (GL (Fin n) ℂ)} (hU : IsOpen U) :
    IsOpen (nSet W₁ W₂ U) := by
  have e : nSet W₁ W₂ U = ⋃ X : nilrad W₁ W₂, (fun g => (uOf X)⁻¹ * g) ⁻¹' U := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨X, c, hc, rfl⟩
      exact ⟨X, by simpa using hc⟩
    · rintro ⟨X, hX⟩
      exact ⟨X, _, hX, by simp⟩
  rw [e]
  exact isOpen_iUnion fun X => hU.preimage (continuous_const.mul continuous_id)

theorem measurableSet_nSet [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) {C : Set (GL (Fin n) ℂ)} (hC : IsCompact C) :
    MeasurableSet (nSet W₁ W₂ C) := by
  haveI := locallyCompact_nilrad W₁ W₂
  haveI := secondCountable_nilrad W₁ W₂
  let K := CompactExhaustion.choice (nilrad W₁ W₂)
  have hcont : Continuous fun p : nilrad W₁ W₂ × GL (Fin n) ℂ => uOf p.1 * p.2 :=
    (continuous_uOf.comp continuous_fst).mul continuous_snd
  have e : nSet W₁ W₂ C =
      ⋃ k, (fun p : nilrad W₁ W₂ × GL (Fin n) ℂ => uOf p.1 * p.2) '' (K k ×ˢ C) := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨X, c, hc, rfl⟩
      obtain ⟨k, hk⟩ := K.exists_mem X
      exact ⟨k, (X, c), ⟨hk, hc⟩, rfl⟩
    · rintro ⟨k, ⟨X, c⟩, ⟨_, hc⟩, rfl⟩
      exact ⟨X, c, hc, rfl⟩
  rw [e]
  exact MeasurableSet.iUnion fun k => (((K.isCompact k).prod hC).image hcont).measurableSet

def zSet (T : Subgroup (GL (Fin n) ℂ)) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    (U : Set (GL (Fin n) ℂ)) : Set (GL (Fin n) ℂ) :=
  {g | ∃ t ∈ T, ∃ X : nilrad W₁ W₂, ∃ c ∈ U, t * uOf X * c = g}

theorem isOpen_zSet (T : Subgroup (GL (Fin n) ℂ)) (W₁ W₂ : Submodule ℂ (Fin n → ℂ))
    {U : Set (GL (Fin n) ℂ)} (hU : IsOpen U) : IsOpen (zSet T W₁ W₂ U) := by
  have e : zSet T W₁ W₂ U =
      ⋃ t : T, ⋃ X : nilrad W₁ W₂, (fun g => ((t : GL (Fin n) ℂ) * uOf X)⁻¹ * g) ⁻¹' U := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨t, ht, X, c, hc, rfl⟩
      exact ⟨⟨t, ht⟩, X, by rwa [inv_mul_cancel_left]⟩
    · rintro ⟨t, X, hX⟩
      exact ⟨t, t.2, X, _, hX, mul_inv_cancel_left _ _⟩
  rw [e]
  exact isOpen_iUnion fun t => isOpen_iUnion fun X =>
    hU.preimage (continuous_const.mul continuous_id)

theorem mul_mem_zSet {T : Subgroup (GL (Fin n) ℂ)} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    {U : Set (GL (Fin n) ℂ)} {h : GL (Fin n) ℂ} (hh : h ∈ T) (x : GL (Fin n) ℂ) :
    h * x ∈ zSet T W₁ W₂ U ↔ x ∈ zSet T W₁ W₂ U := by
  constructor
  · rintro ⟨t, ht, X, c, hc, e⟩
    refine ⟨h⁻¹ * t, T.mul_mem (T.inv_mem hh) ht, X, c, hc, ?_⟩
    rw [mul_assoc, mul_assoc, ← mul_assoc t, e, inv_mul_cancel_left]
  · rintro ⟨t, ht, X, c, hc, rfl⟩
    exact ⟨h * t, T.mul_mem hh ht, X, c, hc, by simp only [mul_assoc]⟩

theorem exists_conj {T : Subgroup (GL (Fin n) ℂ)} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    (hconj : ∀ t ∈ T, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂)
    {t : GL (Fin n) ℂ} (ht : t ∈ T) (X : nilrad W₁ W₂) :
    ∃ X' : nilrad W₁ W₂, uOf X' = t * uOf X * t⁻¹ := by
  refine ⟨⟨t.val * X.1 * (t⁻¹ : GL (Fin n) ℂ).val, hconj t ht X.1 X.2⟩, Units.ext ?_⟩
  have h1 : t.val * (t⁻¹ : GL (Fin n) ℂ).val = 1 := by rw [← Units.val_mul]; simp
  simp only [uOf_val, Units.val_mul, mul_add, add_mul, mul_one, h1]

theorem uOf_mul_mem_zSet {T : Subgroup (GL (Fin n) ℂ)} {W₁ W₂ : Submodule ℂ (Fin n → ℂ)}
    (hW : W₁ ≤ W₂)
    (hconj : ∀ t ∈ T, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂)
    (U : Set (GL (Fin n) ℂ)) (X : nilrad W₁ W₂) (x : GL (Fin n) ℂ) :
    uOf X * x ∈ zSet T W₁ W₂ U ↔ x ∈ zSet T W₁ W₂ U := by
  have fwd : ∀ (X : nilrad W₁ W₂) (x : GL (Fin n) ℂ), x ∈ zSet T W₁ W₂ U →
      uOf X * x ∈ zSet T W₁ W₂ U := by
    rintro X _ ⟨t, ht, Y, c, hc, rfl⟩
    obtain ⟨X', hX'⟩ := exists_conj hconj (T.inv_mem ht) X
    refine ⟨t, ht, nmul hW X' Y, c, hc, ?_⟩
    rw [uOf_nmul, hX', inv_inv]
    group
  refine ⟨fun h => ?_, fwd X x⟩
  have := fwd (ninv hW X) _ h
  rwa [uOf_ninv, inv_mul_cancel_left] at this

end GlobalTheory.CompanionTheory.LocVan.TNorm

namespace GlobalTheory.CompanionTheory.LocVan

open TNorm in

theorem tNormaliser : ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)] (d : GL (Fin n) ℂ)
  (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] (W₁ W₂ : Submodule ℂ (Fin n → ℂ)), W₁ ≤ W₂ →
  (∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) →
  (∀ t ∈ twCent (thC n) d, ∀ X ∈ nilrad W₁ W₂, t.val * X * (t⁻¹ : GL (Fin n) ℂ).val ∈ nilrad W₁ W₂) →
  (∀ C : Set (GL (Fin n) ℂ), IsCompact C → ∀ g : GL (Fin n) ℂ,
    μd {t : twCent (thC n) d | (t : GL (Fin n) ℂ) * g ∈ nSet W₁ W₂ C} ≠ ⊤) →
  ∃ ρ : GL (Fin n) ℂ → ℝ≥0∞, IsQuotNormaliser (twCent (thC n) d) μd ρ ∧
    ∀ (X : nilrad W₁ W₂) (g : GL (Fin n) ℂ), ρ (uOf X * g) = ρ g := by
  intro n _ _ d μd _ W₁ W₂ hW hc hconj hfin
  haveI := secondCountable_GL n
  haveI := locallyCompact_GL n
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SFinite μd := by
    haveI := sigmaFinite_twCent d μd
    infer_instance
  obtain ⟨U, hUo, hUc, hUcov⟩ := exists_open_cover n
  have hact : Measurable fun p : twCent (thC n) d × GL (Fin n) ℂ =>
      (p.1 : GL (Fin n) ℂ) * p.2 :=
    (measurable_subtype_coe.comp measurable_fst).mul measurable_snd
  have hr : ∀ h₀ : twCent (thC n) d,
      MeasurePreserving (fun t : twCent (thC n) d => t * h₀) μd μd := by
    intro h₀
    have e : (fun t : twCent (thC n) d => t * h₀) = fun t => h₀ * t :=
      funext fun t => Subtype.ext (hc t t.2 h₀ h₀.2)
    rw [e]
    exact measurePreserving_mul_left μd h₀
  obtain ⟨ρ, hρm, hρ1, hρS⟩ := GlobalTheory.T.integral_fiber_decomposition_invariant μd
    (fun (t : twCent (thC n) d) (x : GL (Fin n) ℂ) => (t : GL (Fin n) ℂ) * x) hact
    (fun t₀ t => t * t₀) hr
    (fun h₀ h x => by simp only [Subgroup.coe_mul, mul_assoc])
    (fun i => nSet W₁ W₂ (closure (U i))) (fun i => zSet (twCent (thC n) d) W₁ W₂ (U i))
    (fun i => measurableSet_nSet W₁ W₂ (hUc i))
    (fun i => (isOpen_zSet _ W₁ W₂ (hUo i)).measurableSet)
    (fun i h x => mul_mem_zSet h.2 x)
    (fun x => by
      obtain ⟨i, hi⟩ := hUcov x
      exact ⟨i, 1, one_mem _, 0, x, hi, by simp [uOf_zero']⟩)
    (fun i x => hfin _ (hUc i) x)
    (fun i x hx => by
      obtain ⟨t₀, ht₀, X, c, hcU, rfl⟩ := hx
      have hopen : IsOpen {t : twCent (thC n) d |
          (t : GL (Fin n) ℂ) * (t₀ * uOf X * c) ∈ nSet W₁ W₂ (U i)} :=
        (isOpen_nSet W₁ W₂ (hUo i)).preimage (continuous_subtype_val.mul continuous_const)
      have hne : {t : twCent (thC n) d |
          (t : GL (Fin n) ℂ) * (t₀ * uOf X * c) ∈ nSet W₁ W₂ (U i)}.Nonempty :=
        ⟨⟨t₀⁻¹, inv_mem ht₀⟩, X, c, hcU, by simp [mul_assoc]⟩
      have hpos := hopen.measure_ne_zero μd hne
      intro h0
      exact hpos (measure_mono_null
        (fun t ht => nSet_mono W₁ W₂ subset_closure ht) h0))
    {s | ∃ X : nilrad W₁ W₂, s = fun g => uOf X * g}
    (by
      rintro _ ⟨X, rfl⟩ i x
      exact uOf_mul_mem_nSet hW _ X x)
    (by
      rintro _ ⟨X, rfl⟩ i x
      exact uOf_mul_mem_zSet hW hconj _ X x)
    (by
      rintro _ ⟨X, rfl⟩ h
      obtain ⟨X', hX'⟩ := exists_conj hconj h.2 X
      refine ⟨_, ⟨X', rfl⟩, fun x => ?_⟩
      simp only [hX']
      group)
  exact ⟨ρ, ⟨hρm, hρ1⟩, fun X g => hρS _ ⟨X, rfl⟩ g⟩

end GlobalTheory.CompanionTheory.LocVan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormula
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin

section Abstract

variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem setIntegral_comp_addEquiv_of_fundamentalDomain (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G)
    [μ.IsAddHaarMeasure] (𝓕 : Set G) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤)
    (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm) (hΓ : ∀ x, T x ∈ Γ ↔ x ∈ Γ)
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : G → X)
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) : ∫ x in 𝓕, f (T x) ∂μ = ∫ x in 𝓕, f x ∂μ := by
  have : MeasurableConstVAdd Γ G :=
    ⟨fun γ => (continuous_const.add continuous_id : Continuous fun x : G => (γ : G) + x).measurable⟩
  have : VAddInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_add μ (γ : G) s⟩
  let e : G ≃ᵐ G := (Homeomorph.mk T.toEquiv hc hc').toMeasurableEquiv
  have hH : (μ.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ T hc hc'
  have hmapE : μ.map T = μ.map e := rfl
  let eΓ : Γ ≃ Γ :=
    { toFun := fun γ => ⟨T.symm γ, (hΓ _).1 (by simp)⟩
      invFun := fun γ => ⟨T γ, (hΓ _).2 γ.2⟩
      left_inv := fun γ => by simp
      right_inv := fun γ => by simp }
  have hfd : IsAddFundamentalDomain Γ (T '' 𝓕) (μ.map T) := by
    refine IsAddFundamentalDomain.image_of_equiv h𝓕 T.toEquiv ?_ eΓ ?_
    · rw [hmapE]
      exact (MeasurePreserving.symm e (e.measurable.measurePreserving μ)).quasiMeasurePreserving
    · intro γ x
      change T ((T.symm (γ : G)) + x) = (γ : G) + T x
      simp
  obtain ⟨c, hc0, hcμ⟩ : ∃ c : NNReal, c ≠ 0 ∧ μ.map T = c • μ :=
    ⟨_, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map T) μ).ne',
      Measure.isAddLeftInvariant_eq_smul (μ.map T) μ⟩
  have hfd' : IsAddFundamentalDomain Γ (T '' 𝓕) μ := by
    refine hfd.mono ?_
    rw [hcμ]
    exact Measure.absolutelyContinuous_smul (ENNReal.coe_ne_zero.2 hc0)
  have hm : μ 𝓕 = μ (T '' 𝓕) := h𝓕.measure_eq hfd'
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hpre : e ⁻¹' (T '' 𝓕) = 𝓕 := by
    ext x
    exact T.injective.mem_set_image
  have h1 : (c : ENNReal) * μ 𝓕 = 1 * μ 𝓕 := by
    have h2 : (μ.map T) (T '' 𝓕) = μ 𝓕 := by rw [hmapE, e.map_apply, hpre]
    rw [hcμ, Measure.smul_apply, ← hm, ENNReal.smul_def, smul_eq_mul] at h2
    rw [h2, one_mul]
  have hc1 : c = 1 := by
    have h3 : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hne hfin.ne).1 h1
    exact_mod_cast h3
  have hmp : MeasurePreserving e μ μ := ⟨e.measurable, by rw [← hmapE, hcμ, hc1, one_smul]⟩
  have h4 := hmp.setIntegral_image_emb e.measurableEmbedding f 𝓕
  have h5 : ∫ y in T '' 𝓕, f y ∂μ = ∫ x in 𝓕, f x ∂μ :=
    hfd'.setIntegral_eq h𝓕 fun γ x => hf γ γ.2 x
  exact h4.symm.trans h5

end Abstract

section Block

variable {a r : ℕ} {R : Type} [CommRing R]

def BlockDiag (r : ℕ) (M : Matrix (Fin a) (Fin a) R) : Prop :=
  ∀ i j : Fin a, ¬ ((i : ℕ) < r ↔ (j : ℕ) < r) → M i j = 0

def upperRightBlockConj (B C : Matrix (Fin a) (Fin a) R) (x : BlockIx a r → R) : BlockIx a r → R :=
  fun p => (B * nilM x * C) p.1.1 p.1.2

theorem nilM_add' (x y : BlockIx a r → R) : nilM (x + y) = nilM x + nilM y := by
  ext i j
  simp only [nilM, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem nilM_injective : Function.Injective (nilM : (BlockIx a r → R) → Matrix (Fin a) (Fin a) R) := by
  intro x y h
  funext p
  have := congrFun (congrFun h p.1.1) p.1.2
  simpa only [nilM, Matrix.of_apply, dif_pos p.2] using this

theorem nil_matrix_conj_block {B C : Matrix (Fin a) (Fin a) R} (hB : BlockDiag r B) (hC : BlockDiag r C)
    (x : BlockIx a r → R) : nilM (upperRightBlockConj B C x) = B * nilM x * C := by
  ext i j
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · simp only [nilM, Matrix.of_apply, dif_pos h, upperRightBlockConj]
  · rw [nilM, Matrix.of_apply, dif_neg h, Matrix.mul_apply]
    refine (Finset.sum_eq_zero fun l _ => ?_).symm
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) < r ∧ r ≤ (l : ℕ)
    · by_cases hik : (i : ℕ) < r
      · rw [hC l j (by omega), mul_zero]
      · rw [hB i k (by omega), zero_mul, zero_mul]
    · simp [nilM, dif_neg hk]

theorem conj_block_add (B C : Matrix (Fin a) (Fin a) R) (x y : BlockIx a r → R) :
    upperRightBlockConj B C (x + y) = upperRightBlockConj B C x + upperRightBlockConj B C y := by
  funext p
  simp [upperRightBlockConj, nilM_add', mul_add, add_mul]

def conjE (m : GL (Fin a) R) (hm : BlockDiag r m.val) (hm' : BlockDiag r (m⁻¹).val) :
    (BlockIx a r → R) ≃+ (BlockIx a r → R) where
  toFun := upperRightBlockConj (m⁻¹).val m.val
  invFun := upperRightBlockConj m.val (m⁻¹).val
  left_inv x := nilM_injective <| by
    rw [nil_matrix_conj_block hm hm', nil_matrix_conj_block hm' hm]
    simp [Matrix.mul_assoc]
  right_inv x := nilM_injective <| by
    rw [nil_matrix_conj_block hm' hm, nil_matrix_conj_block hm hm']
    simp [Matrix.mul_assoc]
  map_add' := conj_block_add _ _

theorem unip_mul_eq (m : GL (Fin a) R) (hm : BlockDiag r m.val) (hm' : BlockDiag r (m⁻¹).val)
    (x : BlockIx a r → R) : unip x * m = m * unip (conjE m hm hm' x) := by
  apply Units.ext
  change (1 + nilM x) * m.val = m.val * (1 + nilM (upperRightBlockConj (m⁻¹).val m.val x))
  rw [nil_matrix_conj_block hm' hm]
  simp [mul_add, add_mul, Matrix.mul_assoc]

theorem continuous_nilM {S : Type} [CommRing S] [TopologicalSpace S] :
    Continuous (nilM : (BlockIx a r → S) → Matrix (Fin a) (Fin a) S) := by
  refine continuous_matrix fun i j => ?_
  by_cases h : (i : ℕ) < r ∧ r ≤ (j : ℕ)
  · simpa only [nilM, Matrix.of_apply, dif_pos h] using continuous_apply _
  · simpa only [nilM, Matrix.of_apply, dif_neg h] using continuous_const

theorem continuous_conj_block {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (B C : Matrix (Fin a) (Fin a) S) : Continuous (upperRightBlockConj B C : (BlockIx a r → S) → _) :=
  continuous_pi fun p =>
    ((continuous_const.matrix_mul continuous_nilM).matrix_mul continuous_const).matrix_elem _ _

theorem conj_block_map {S : Type} [CommRing S] (f : R →+* S) (B C : Matrix (Fin a) (Fin a) R)
    (q : BlockIx a r → R) :
    upperRightBlockConj (B.map f) (C.map f) (fun p => f (q p)) = fun p => f (upperRightBlockConj B C q p) := by
  have h : nilM (fun p => f (q p)) = (nilM q : Matrix (Fin a) (Fin a) R).map f := by
    ext i j
    simp only [nilM, Matrix.of_apply, Matrix.map_apply]
    split_ifs <;> simp
  funext p
  simp only [upperRightBlockConj, h]
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  rfl

end Block

section Levi

variable {R S : Type} [CommRing R] [CommRing S] {r s : ℕ}

theorem blockDiag_lev (g : GL (Fin r) R × GL (Fin s) R) : BlockDiag r (lev R r s g).val := by
  intro i j hij
  rw [lev, GlobalTheory.SmGL.val_emb₂]
  obtain ⟨u, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨v, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rcases u with u | u <;> rcases v with v | v
  · exact absurd (by simp [u.2, v.2]) hij
  · simp [Matrix.reindex_apply]
  · simp [Matrix.reindex_apply]
  · exact absurd (by simp) hij

theorem map_lev (f : R →+* S) (g : GL (Fin r) R × GL (Fin s) R) :
    lev S r s (Matrix.GeneralLinearGroup.map f g.1, Matrix.GeneralLinearGroup.map f g.2) =
      Matrix.GeneralLinearGroup.map f (lev R r s g) := by
  apply Units.ext
  rw [lev, GlobalTheory.SmGL.val_emb₂]
  change _ = (lev R r s g).val.map f
  rw [lev, GlobalTheory.SmGL.val_emb₂]
  ext i j
  obtain ⟨u, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨v, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rcases u with u | u <;> rcases v with v | v <;> simp [Matrix.reindex_apply]
  all_goals rfl

end Levi

section Main

variable {E : Type} [Field E] [NumberField E]

theorem conj_block_mem_rational_nilradical {a r : ℕ} (b c : Matrix (Fin a) (Fin a) E) {x : BlockIx a r → Ad E}
    (hx : x ∈ ratN E a r) :
    upperRightBlockConj (b.map (algebraMap E (Ad E))) (c.map (algebraMap E (Ad E))) x ∈ ratN E a r := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨upperRightBlockConj b c q, (conj_block_map (algebraMap E (Ad E)) b c q).symm⟩

end Main

theorem integral_unip_lev_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (φ : Sm E (r + s)), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ.1 (ratGL E (r + s) γ * g) = φ.1 g) → IsOpen {k | finRep E (r + s) k φ = φ} → ∀ [MeasurableSpace (BlockIx (r + s) r → Ad E)] [BorelSpace (BlockIx (r + s) r → Ad E)] (μ : Measure (BlockIx (r + s) r → Ad E)) (𝓕 : Set (BlockIx (r + s) r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E (r + s) r) 𝓕 μ → ∀ (γ : GL (Fin r) E × GL (Fin s) E) (g : GA E (r + s)), ∫ x in 𝓕, φ.1 (unip x * (lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) * g)) ∂μ = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  intro E _ _ _ r s φ hl _ _ _ μ 𝓕 hμ h𝓕 γ g
  haveI := hμ
  obtain ⟨t2, lc, sc⟩ := Formalism.IndefR.Eqv.G5.af_facts E
  haveI : T2Space (Ad E) := t2
  haveI : LocallyCompactSpace (Ad E) := lc
  haveI : SecondCountableTopology (Ad E) := sc
  haveI := countable_ratN (E := E) (a := r + s) r
  have hfin := covol_lt_top μ 𝓕 h𝓕
  set ℓ := lev E r s γ with hℓ
  set m := lev (Ad E) r s (ratGL E r γ.1, ratGL E s γ.2) with hmdef
  have hmℓ : m = ratGL E (r + s) ℓ := map_lev (algebraMap E (Ad E)) γ
  have hm : BlockDiag r m.val := blockDiag_lev _
  have hm' : BlockDiag r (m⁻¹).val := by
    have e : m⁻¹ = lev (Ad E) r s ((ratGL E r γ.1)⁻¹, (ratGL E s γ.2)⁻¹) := by
      rw [← Prod.inv_mk, map_inv]
    rw [e]
    exact blockDiag_lev _
  have hval : m.val = ℓ.val.map (algebraMap E (Ad E)) := by rw [hmℓ]; rfl
  have hval' : (m⁻¹).val = (ℓ⁻¹).val.map (algebraMap E (Ad E)) := by rw [hmℓ, ← map_inv]; rfl
  have hΓ : ∀ x, conjE m hm hm' x ∈ ratN E (r + s) r ↔ x ∈ ratN E (r + s) r := by
    intro x
    constructor
    · intro h
      have h1 := conj_block_mem_rational_nilradical ℓ.val (ℓ⁻¹).val h
      rw [← hval, ← hval'] at h1
      have h2 : (conjE m hm hm').symm (conjE m hm hm' x) ∈ ratN E (r + s) r := h1
      simpa using h2
    · intro h
      have h1 := conj_block_mem_rational_nilradical (ℓ⁻¹).val ℓ.val h
      rw [← hval, ← hval'] at h1
      exact h1
  have hper : ∀ y ∈ ratN E (r + s) r, ∀ x, φ.1 (unip (y + x) * g) = φ.1 (unip x * g) := by
    rintro _ ⟨q, rfl⟩ x
    change φ.1 (unip ((fun p => algebraMap E (Ad E) (q p)) + x) * g) = _
    rw [unip_add, unip_algebraMap, mul_assoc, hl]
  have key := setIntegral_comp_addEquiv_of_fundamentalDomain (ratN E (r + s) r) μ 𝓕 h𝓕 hfin (conjE m hm hm')
    (continuous_conj_block _ _) (continuous_conj_block _ _) hΓ (fun x => φ.1 (unip x * g)) hper
  have e : ∀ x, φ.1 (unip x * (m * g)) = φ.1 (unip (conjE m hm hm' x) * g) := by
    intro x
    rw [← mul_assoc, unip_mul_eq m hm hm' x, mul_assoc]
    have h := hl ℓ (unip (conjE m hm hm' x) * g)
    rwa [← hmℓ] at h
  simp only [e]
  exact key

end GlobalTheory.CompanionTheory.CTFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeMulIdempotentRangeStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_mul_idempotent_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), DegAdelic → ∀ (e : Matrix (Fin n) (Fin n) E), e * e = e → ∀ t x : GA E n, t.val * rm e = rm e * t.val → deg (t * x) (LinearMap.range (Matrix.toLin' e)) = deg x (LinearMap.range (Matrix.toLin' e)) + lam e t := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.DegLam.deg_lam | exact GlobalTheory.CompanionTheory.TorusCh.DegLam.deg_lam | (intros; apply GlobalTheory.CompanionTheory.TorusCh.DegLam.deg_lam <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCyclicVectorOfSeparableStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclic_vector_of_separable : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable → ∃ v : Fin n → K, ∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.CyclicVector.exists_cyclic_vector | exact GlobalTheory.CompanionTheory.TorusCh.CyclicVector.exists_cyclic_vector | (intros; apply GlobalTheory.CompanionTheory.TorusCh.CyclicVector.exists_cyclic_vector <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEpsilonCentralizerBoundStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_epsilon_centralizer_bound : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), (∀ y : Fin n → K, ∃ h : K[X], y = v ᵥ* aeval γ h) → ∀ e : Matrix (Fin n) (Fin n) K, IsPrim γ e → ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ g : GroundTheory.Automorphic.AdelicGLn.AdelicGL K n, g.val * γ.map (algebraMap K (AdeleRing (𝓞 K) K)) = γ.map (algebraMap K (AdeleRing (𝓞 K) K)) * g.val → ∀ s : (AdeleRing (𝓞 K) K)ˣ, (s : AdeleRing (𝓞 K) K) = (1 + e.map (algebraMap K (AdeleRing (𝓞 K) K)) * (g.val - 1)).det → c ≤ (GroundTheory.Global.IdeleGroup.ideleModule K s : ℝ) → ∀ x : Fin n → K, x ᵥ* e ≠ 0 → ε ≤ GroundTheory.Automorphic.Reduction.height g x := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height | exact GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height | (intros; apply GlobalTheory.CompanionTheory.TorusCh.HeightBound.exists_pos_le_height <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvolutionAdjoinNormStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_involution_adjoin_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (d : GL (Fin n) E), ∃ σ : Algebra.adjoin E {(nrm d).val} →+* Algebra.adjoin E {(nrm d).val}, (∀ x, ((σ x : Algebra.adjoin E {(nrm d).val}) : Matrix (Fin n) (Fin n) E) = sg d x) ∧ ∀ x, σ (σ x) = x := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing | exact GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing | (intros; apply GlobalTheory.CompanionTheory.TorusCh.SgRing.exists_sgRing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialProjectionInvariantStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_projection_invariant : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K) (v : Fin n → K), γ.charpoly.Separable → (∀ y : Fin n → K, ∃ h : K[X], y = aeval γ h *ᵥ v) → ∀ W : Submodule K (Fin n → K), W.map (Matrix.toLin' γ) ≤ W → ∃ π, IsPol γ π ∧ π * π = π ∧ LinearMap.range (Matrix.toLin' π) = W := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.exists_idem_pol_range_eq | exact GlobalTheory.CompanionTheory.TorusCh.exists_idem_pol_range_eq | (intros; apply GlobalTheory.CompanionTheory.TorusCh.exists_idem_pol_range_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveIdempotentsSeparatingStatement
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_idempotents_separating : ∀ (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable → ∃ S : Finset (Matrix (Fin n) (Fin n) K), (∀ e ∈ S, IsPrim γ e) ∧ ∀ x : Fin n → K, x ≠ 0 → ∃ e ∈ S, x ᵥ* e ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.exists_prim_cover | exact GlobalTheory.CompanionTheory.TorusCh.exists_prim_cover | (intros; apply GlobalTheory.CompanionTheory.TorusCh.exists_prim_cover <;> assumption)
end

