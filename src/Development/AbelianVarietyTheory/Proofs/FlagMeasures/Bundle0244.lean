import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariant
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SgInfDD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mat k r → (H →L[ℂ] H)}

theorem gg_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  Formalism.MainNotions.LowestKTypeMultiplicity.UH_mul ha hb

theorem gg_one : (1 : Mat k r) ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_one k r

theorem hasDeriv_dsig (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) v) (dsig σ Y v) 0 :=
  Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hσ hv [] (by simp) hY

theorem smooth_dsig (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) : IsSmoothVec (k := k) (r := r) σ (dsig σ Y v) := by
  have h2 := Formalism.MainNotions.LowestKTypeMultiplicity.psiD_smooth hσ hv [Y] (by simpa using hY)
  intro g₀ hg₀
  obtain ⟨U, F, hU, hp, hF, hE⟩ := h2 ((1 : Mat k r), g₀) (gg_one) hg₀
  have hc : ContDiff ℝ ∞ (fun g : Mat k r => (((1 : Mat k r), g) : Mat k r × Mat k r)) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨(fun g : Mat k r => (((1 : Mat k r), g) : Mat k r × Mat k r)) ⁻¹' U, fun g => F ((1 : Mat k r), g),
    hU.preimage hc.continuous, hp, hF.comp hc.contDiffOn (fun x hx => hx), ?_⟩
  intro g hgU hgH
  have := hE ((1 : Mat k r), g) hgU gg_one hgH
  simp only [hσ.1.1, ContinuousLinearMap.one_apply] at this
  exact this

theorem lie_conj {g Y : Mat k r} (hg : g ∈ GG k r) (hY : InLieHpk k r Y) :
    InLieHpk k r (g * Y * g⁻¹) := by
  have hd : IsUnit g.det := Formalism.MainNotions.LowestKTypeMultiplicity.UH_det hg
  have hM : g⁻¹ ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv hg
  have hgM : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hd
  have hMg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hd
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hM' : (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r := hM
  have e1 : gᴴ * Hpk k r = Hpk k r * g⁻¹ := by
    calc gᴴ * Hpk k r = gᴴ * Hpk k r * (g * g⁻¹) := by rw [hgM, Matrix.mul_one]
      _ = (gᴴ * Hpk k r * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * g⁻¹ := by rw [hg']
  have e2 : Hpk k r * g = (g⁻¹)ᴴ * Hpk k r := by
    calc Hpk k r * g = ((g⁻¹)ᴴ * Hpk k r * g⁻¹) * g := by rw [hM']
      _ = (g⁻¹)ᴴ * Hpk k r * (g⁻¹ * g) := by simp only [Matrix.mul_assoc]
      _ = (g⁻¹)ᴴ * Hpk k r := by rw [hMg, Matrix.mul_one]
  have hY' : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY
  show (g * Y * g⁻¹)ᴴ * Hpk k r + Hpk k r * (g * Y * g⁻¹) = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  calc (g⁻¹)ᴴ * (Yᴴ * gᴴ) * Hpk k r + Hpk k r * (g * Y * g⁻¹)
      = (g⁻¹)ᴴ * Yᴴ * (gᴴ * Hpk k r) + (Hpk k r * g) * Y * g⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (g⁻¹)ᴴ * Yᴴ * (Hpk k r * g⁻¹) + ((g⁻¹)ᴴ * Hpk k r) * Y * g⁻¹ := by rw [e1, e2]
    _ = (g⁻¹)ᴴ * (Yᴴ * Hpk k r + Hpk k r * Y) * g⁻¹ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY', Matrix.mul_zero, Matrix.zero_mul]

theorem dsig_conj (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {Y : Mat k r} (hY : InLieHpk k r Y) {g : Mat k r} (hg : g ∈ GG k r) :
    σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v) := by
  have hd : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (Formalism.MainNotions.LowestKTypeMultiplicity.UH_det hg)
  have hM : g⁻¹ ∈ GG k r := Formalism.MainNotions.LowestKTypeMultiplicity.UH_inv hg
  have hMg : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hd)
  have h1 := hasDeriv_dsig hσ hv hY
  have h2 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have e : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * Y * g⁻¹))) (σ g v)) =
      (⇑((σ g).restrictScalars ℝ) ∘ fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) v) := by
    funext t
    have hx := Formalism.MainNotions.LowestKTypeMultiplicity.exp_mem_UH hY t
    have hs : (t : ℂ) • (g * Y * g⁻¹) = g * ((t : ℂ) • Y) * g⁻¹ := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hs, Matrix.exp_conj _ _ hd]
    simp only [Function.comp, ContinuousLinearMap.coe_restrictScalars']
    have hc : g * NormedSpace.exp ((t : ℂ) • Y) ∈ GG k r := gg_mul hg hx
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ (gg_mul hc hM) g hg,
      ← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg _ hx]
    congr 2
    rw [Matrix.mul_assoc, hMg, Matrix.mul_one]
  show _ = deriv _ 0
  rw [e, h2.deriv]
  rfl

theorem smooth_dsigW (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v) :
    ∀ Ys : List (Mat k r), (∀ Y ∈ Ys, InLieHpk k r Y) → IsSmoothVec (k := k) (r := r) σ (dsigW σ Ys v) := by
  intro Ys
  induction Ys with
  | nil => intro _; exact hv
  | cons Y Ys ih =>
    intro h
    exact smooth_dsig hσ (ih fun X hX => h X (List.mem_cons_of_mem _ hX)) (h Y List.mem_cons_self)

theorem dsigW_conj (hσ : IsURepOn (GG k r) σ) {v : H} (hv : IsSmoothVec (k := k) (r := r) σ v)
    {g : Mat k r} (hg : g ∈ GG k r) :
    ∀ Ys : List (Mat k r), (∀ Y ∈ Ys, InLieHpk k r Y) →
      σ g (dsigW σ Ys v) = dsigW σ (Ys.map fun Y => g * Y * g⁻¹) (σ g v) := by
  intro Ys
  induction Ys with
  | nil => intro _; rfl
  | cons Y Ys ih =>
    intro h
    have h' : ∀ X ∈ Ys, InLieHpk k r X := fun X hX => h X (List.mem_cons_of_mem _ hX)
    show σ g (dsig σ Y (dsigW σ Ys v)) = dsig σ (g * Y * g⁻¹) (dsigW σ (Ys.map fun Y => g * Y * g⁻¹) (σ g v))
    rw [dsig_conj hσ (smooth_dsigW hσ hv Ys h') (h Y List.mem_cons_self) hg, ih h']

theorem dsig_zero (Y : Mat k r) : dsig σ Y (0 : H) = 0 := by
  simp [dsig]

theorem dsig_add (hσ : IsURepOn (GG k r) σ) {a b : H} (ha : IsSmoothVec (k := k) (r := r) σ a)
    (hb : IsSmoothVec (k := k) (r := r) σ b) {Y : Mat k r} (hY : InLieHpk k r Y) :
    dsig σ Y (a + b) = dsig σ Y a + dsig σ Y b := by
  have h := (hasDeriv_dsig hσ ha hY).add (hasDeriv_dsig hσ hb hY)
  show deriv _ 0 = _
  simp only [map_add]
  exact h.deriv

theorem dsig_smul (hσ : IsURepOn (GG k r) σ) {a : H} (ha : IsSmoothVec (k := k) (r := r) σ a)
    (c : ℂ) {Y : Mat k r} (hY : InLieHpk k r Y) :
    dsig σ Y (c • a) = c • dsig σ Y a := by
  have h := (hasDeriv_dsig hσ ha hY).const_smul c
  show deriv _ 0 = _
  simp only [map_smul]
  exact h.deriv

theorem DD_stable (hσ : IsURepOn (GG k r) σ) (w : H) {g : Mat k r} (hg : g ∈ GG k r) :
    DD σ w ≤ (DD σ w).comap (σ g : H →ₗ[ℂ] H) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨h, hh, rfl⟩
  show σ g (σ h w) ∈ DD σ w
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg h hh]
  exact mem_DD σ w (gg_mul hg hh)

theorem mem_DD_self (hσ : IsURepOn (GG k r) σ) (w : H) : w ∈ DD σ w := by
  have := mem_DD σ w (gg_one (k := k) (r := r))
  rwa [hσ.1.1, ContinuousLinearMap.one_apply] at this

theorem DD_dense (hσ : IsURepOn (GG k r) σ) (hirr : IsIrredOn (GG k r) σ) {w : H} (hw : w ≠ 0) :
    Dense (DD σ w : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  have hst : ∀ g ∈ GG k r, ∀ v ∈ (DD σ w).topologicalClosure, σ g v ∈ (DD σ w).topologicalClosure := by
    intro g hg v hv
    have hle : (DD σ w).topologicalClosure ≤ ((DD σ w).topologicalClosure).comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.topologicalClosure_minimal _ ?_ ?_
      · exact (DD_stable hσ w hg).trans (Submodule.comap_mono (DD σ w).le_topologicalClosure)
      · exact (DD σ w).isClosed_topologicalClosure.preimage (σ g).continuous
    exact hle hv
  rcases hirr (DD σ w).topologicalClosure (DD σ w).isClosed_topologicalClosure hst with h | h
  · exfalso
    have h1 : w ∈ (DD σ w).topologicalClosure := (DD σ w).le_topologicalClosure (mem_DD_self hσ w)
    rw [h, Submodule.mem_bot] at h1
    exact hw h1
  · exact h

theorem DD_le_Vinf (w : H) : DD σ w ≤ Vinf σ w := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.subset_span ⟨[], g, by simp, hg, rfl⟩

theorem Vinf_smooth (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w) :
    ∀ v ∈ Vinf σ w, IsSmoothVec (k := k) (r := r) σ v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Ys, g, hYs, hg, rfl⟩ := hx
    exact smooth_dsigW hσ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw hg) Ys hYs
  | zero => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_zero
  | add x y _ _ hx hy => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_add hx hy
  | smul a x _ hx => exact Formalism.MainNotions.LowestKTypeMultiplicity.smooth_smul a hx

theorem Vinf_stable (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w)
    {g : Mat k r} (hg : g ∈ GG k r) : Vinf σ w ≤ (Vinf σ w).comap (σ g : H →ₗ[ℂ] H) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨Ys, h, hYs, hh, rfl⟩
  show σ g (dsigW σ Ys (σ h w)) ∈ Vinf σ w
  rw [dsigW_conj hσ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw hh) hg Ys hYs,
    ← ContinuousLinearMap.comp_apply, ← hσ.1.2 g hg h hh]
  refine Submodule.subset_span ⟨Ys.map fun Y => g * Y * g⁻¹, g * h, ?_, gg_mul hg hh, rfl⟩
  intro Y hY
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
  exact lie_conj hg (hYs X hX)

theorem Vinf_dsig (hσ : IsURepOn (GG k r) σ) {w : H} (hw : IsSmoothVec (k := k) (r := r) σ w)
    {Y : Mat k r} (hY : InLieHpk k r Y) : ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Ys, g, hYs, hg, rfl⟩ := hx
    refine Submodule.subset_span ⟨Y :: Ys, g, ?_, hg, rfl⟩
    intro X hX
    rcases List.mem_cons.1 hX with rfl | hX
    · exact hY
    · exact hYs X hX
  | zero => rw [dsig_zero]; exact (Vinf σ w).zero_mem
  | add x y hx hy ihx ihy =>
    rw [dsig_add hσ (Vinf_smooth hσ hw x hx) (Vinf_smooth hσ hw y hy) hY]
    exact (Vinf σ w).add_mem ihx ihy
  | smul a x hx ihx =>
    rw [dsig_smul hσ (Vinf_smooth hσ hw x hx) a hY]
    exact (Vinf σ w).smul_mem a ihx

theorem DD_stable_dense : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H), IsURepOn (GG k r) σ →
    (∀ g ∈ GG k r, ∀ v ∈ DD σ w, σ g v ∈ DD σ w) ∧
    (IsIrredOn (GG k r) σ → w ≠ 0 → Dense (DD σ w : Set H)) ∧ DD σ w ≤ Vinf σ w ∧
    (∀ v, IsSmoothVec σ v → (∀ g ∈ GG k r, IsSmoothVec σ (σ g v)) ∧
      ∀ Y, InLieHpk k r Y → IsSmoothVec σ (dsig σ Y v) ∧
        ∀ g ∈ GG k r, InLieHpk k r (g * Y * g⁻¹) ∧ σ g (dsig σ Y v) = dsig σ (g * Y * g⁻¹) (σ g v)) ∧
    (IsSmoothVec σ w → (∀ v ∈ Vinf σ w, IsSmoothVec σ v) ∧ (∀ g ∈ GG k r, ∀ v ∈ Vinf σ w, σ g v ∈ Vinf σ w) ∧
      ∀ Y, InLieHpk k r Y → ∀ v ∈ Vinf σ w, dsig σ Y v ∈ Vinf σ w) := by
  intro k r H _ _ _ σ w hσ
  refine ⟨fun g hg v hv => DD_stable hσ w hg hv, fun hirr hw => DD_dense hσ hirr hw, DD_le_Vinf w,
    fun v hv => ⟨fun g hg => Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv hg, fun Y hY =>
      ⟨smooth_dsig hσ hv hY, fun g hg => ⟨lie_conj hg hY, dsig_conj hσ hv hY hg⟩⟩⟩,
    fun hw => ⟨Vinf_smooth hσ hw, fun g hg v hv => Vinf_stable hσ hw hg hv, fun Y hY => Vinf_dsig hσ hw hY⟩⟩

end GlobalTheory.SgInfDD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalDomainMeasureEq
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem strictFD_measure_eq_tsum {G X : Type} [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hmeas : ∀ g, Measurable (ρ g)) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = ∑' g, μ (D ∩ NN ∩ (ρ g)⁻¹' D') := by
  have h1 : μ D = μ (D ∩ NN) := by
    rw [← measure_inter_add_diff D hNN]
    have : μ (D \ NN) = 0 := measure_mono_null (fun x hx => hx.2) hnull
    rw [this, add_zero]
  rw [h1]
  have hU : D ∩ NN = ⋃ g, D ∩ NN ∩ (ρ g)⁻¹' D' := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hxD, hxN⟩
      obtain ⟨g, hg, -⟩ := hu' x hxN
      exact ⟨g, ⟨hxD, hxN⟩, hg⟩
    · rintro ⟨g, ⟨hxD, hxN⟩, -⟩
      exact ⟨hxD, hxN⟩
  conv_lhs => rw [hU]
  apply measure_iUnion
  · intro g h hgh
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨⟨-, hxN⟩, hg⟩ ⟨⟨-, -⟩, hh⟩
    exact hgh ((hu' x hxN).unique hg hh)
  · intro g
    exact (hD.inter hNN).inter (hmeas g hD')

theorem strictFD_measure_eq {G X : Type} [Group G] [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hone : ∀ x, ρ 1 x = x) (hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (hinv : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN) (hmp : ∀ g, MeasurePreserving (ρ g) μ μ)
    (hu : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = μ D' := by
  have hmeas : ∀ g, Measurable (ρ g) := fun g => (hmp g).measurable
  rw [strictFD_measure_eq_tsum μ ρ NN D D' hNN hnull hD hD' hmeas hu',
    strictFD_measure_eq_tsum μ ρ NN D' D hNN hnull hD' hD hmeas hu]
  conv_rhs => rw [← (Equiv.inv G).tsum_eq]
  refine tsum_congr fun g => ?_
  simp only [Equiv.inv_apply]
  have hS : MeasurableSet (D' ∩ NN ∩ (ρ g⁻¹)⁻¹' D) :=
    (hD'.inter hNN).inter (hmeas g⁻¹ hD)
  rw [← (hmp g).measure_preimage hS.nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  have hx : ρ g⁻¹ (ρ g x) = x := by rw [← hmul, inv_mul_cancel, hone]
  rw [hx]
  constructor
  · rintro ⟨⟨hxD, hxN⟩, hgx⟩
    exact ⟨⟨hgx, hinv g x hxN⟩, hxD⟩
  · rintro ⟨⟨hgx, hgxN⟩, hxD⟩
    refine ⟨⟨hxD, ?_⟩, hgx⟩
    have := hinv g⁻¹ _ hgxN
    rwa [hx] at this

example : ∀ {G X : Type} [Group G] [Countable G] [MeasurableSpace X] (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X), MeasurableSet NN → μ NNᶜ = 0 → MeasurableSet D → MeasurableSet D' → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ g, MeasurePreserving (ρ g) μ μ) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') → μ D = μ D' :=
  @strictFD_measure_eq

end GlobalTheory.SnMass.VolN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentBlockEntriesMulOfHasFlagDepthAtLeast
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LeftMul

theorem pos_eI (k r : ℕ) (a : Fin r) : pos k r (eI k r a) = a.val := by
  have := a.isLt
  unfold pos eI
  dsimp only
  split_ifs <;> omega

theorem pos_wI (k r : ℕ) (j : Fin (k + 1)) : pos k r (wI k r j) = r := by
  have := j.isLt
  unfold pos wI
  dsimp only
  split_ifs <;> omega

theorem pos_esI (k r : ℕ) (a : Fin r) : pos k r (esI k r a) = 2 * r - a.val := by
  have := a.isLt
  unfold pos esI
  dsimp only
  split_ifs <;> omega

theorem mul_apply_of_dep (k r d : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : Dep k r d (g - 1)) (hx : Dep k r 1 (x - 1)) (i j : Fin (2 * r + k + 1)) (hij : i ≠ j)
    (hp : pos k r j ≤ pos k r i + d) : (g * x) i j = g i j + x i j := by
  have h1 : g * x = (g - 1) * (x - 1) + (g - 1) + (x - 1) + 1 := by noncomm_ring
  have h2 : ((g - 1) * (x - 1)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : pos k r l < pos k r i + d
    · rw [hg i l hl, zero_mul]
    · rw [hx l j (by omega), mul_zero]
  rw [h1, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, h2, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.one_apply_ne hij]
  ring

end GlobalTheory.SnMass.VolN.LeftMul

namespace GlobalTheory.SnMass.VolN

open GlobalTheory.SnMass.VolN.LeftMul in

theorem cM_mul_of_dep : ∀ (k r : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ),
    Dep k r d (g - 1) → Dep k r 1 (x - 1) → ∀ β : Bk r, degB r β ≤ d →
      cM k r β (Matrix.of.symm (g * x)) = cM k r β (Matrix.of.symm x) + cM k r β (Matrix.of.symm g) := by
  intro k r g x d hg hx β hβ
  rcases β with p | a | p | a
  · have hlt : p.1.1.val < p.1.2.val := p.2
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (eI k r p.1.2) = x (eI k r p.1.1) (eI k r p.1.2) + g (eI k r p.1.1) (eI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI] at this; omega
    · rw [pos_eI, pos_eI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show (fun j => (g * x) (eI k r a) (wI k r j)) = (fun j => x (eI k r a) (wI k r j)) + (fun j => g (eI k r a) (wI k r j))
    funext l
    rw [Pi.add_apply, mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, wI] at this; omega
    · rw [pos_eI, pos_wI]; omega
  · have hlt : p.1.1.val < p.1.2.val := p.2
    have hb := p.1.2.isLt
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (esI k r p.1.2) = x (eI k r p.1.1) (esI k r p.1.2) + g (eI k r p.1.1) (esI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show ((g * x) (eI k r a) (esI k r a)).im = (x (eI k r a) (esI k r a)).im + (g (eI k r a) (esI k r a)).im
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, Complex.add_im, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega

end GlobalTheory.SnMass.VolN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentModelActionIsActionAndFaithful
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem det_embed_ne_zero {E : Type} [Field E] [NumberField E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0)
    (w : InfinitePlace E) : (J.map w.embedding).det ≠ 0 := by
  rw [show J.map w.embedding = w.embedding.mapMatrix J from rfl, ← RingHom.map_det]
  exact (map_ne_zero _).mpr hJ

theorem A_isUnit_det {E : Type} [Field E] [NumberField E] {k r : ℕ}
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hJ : J.det ≠ 0) (hA : IsModelAt J A) (w : InfinitePlace E) : IsUnit (A w).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h : ((A w)ᴴ * Hpk k r * A w).det = (J.map w.embedding).det := congrArg Matrix.det (hA w)
  rw [det_mul, det_mul, h0, mul_zero] at h
  exact det_embed_ne_zero J hJ w h.symm

theorem actLaws (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) :
    IsVolData σ J Λ P f T A s → (∀ x, actM A 1 x = x) ∧ (∀ γ γ' x, actM A (γ * γ') x = actM A γ (actM A γ' x)) ∧ ∀ γ, (∀ w, gM A γ w = 1) → γ = 1 := by
  intro h
  have hJ : J.det ≠ 0 := h.2.2.1.2
  have hA : IsModelAt J A := h.2.2.2.2.2.2.2.1
  have hu : ∀ w, IsUnit (A w).det := fun w => A_isUnit_det J A hJ hA w
  refine ⟨?_, ?_, ?_⟩
  · intro x
    funext w
    have e : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E).map w.embedding = 1 :=
      map_one w.embedding.mapMatrix
    simp only [actM, e, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hu w), Matrix.one_mul]
    rfl
  · intro γ γ' x
    funext w
    have e : (γ * γ').map w.embedding = γ.map w.embedding * γ'.map w.embedding :=
      map_mul w.embedding.mapMatrix γ γ'
    have m : A w * (γ.map w.embedding * γ'.map w.embedding) * (A w)⁻¹ * Matrix.of (x w) =
        A w * γ.map w.embedding * (A w)⁻¹ * (A w * γ'.map w.embedding * (A w)⁻¹ * Matrix.of (x w)) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
    show Matrix.of.symm (A w * (γ * γ').map w.embedding * (A w)⁻¹ * Matrix.of (x w)) =
      Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ *
        Matrix.of (Matrix.of.symm (A w * γ'.map w.embedding * (A w)⁻¹ * Matrix.of (x w))))
    rw [Equiv.apply_symm_apply, e, m]
  · intro γ hγ
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hi : (A w)⁻¹ * A w = 1 := Matrix.nonsing_inv_mul _ (hu w)
    have h1 : γ.map w.embedding = 1 := by
      have e : A w * γ.map w.embedding * (A w)⁻¹ = 1 := hγ w
      calc γ.map w.embedding = (A w)⁻¹ * (A w * γ.map w.embedding * (A w)⁻¹) * A w := by
            simp only [Matrix.mul_assoc, hi, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
        _ = 1 := by rw [e, Matrix.mul_one, hi]
    ext i j
    apply w.embedding.injective
    have := congrArg (fun M => M i j) h1
    simpa [Matrix.one_apply, apply_ite] using this

end GlobalTheory.SnMass.VolN
end
end

