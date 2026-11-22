import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilOrbitalMeasure
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductHaarMeasure
section
open MeasureTheory Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FactS.OpenFactor

section Generic

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_comap_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) : (μ.comap e).map e = μ := by
  rw [he.map_comap]
  exact Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hμ)

theorem comap_invariant {e : Y → X} (he : MeasurableEmbedding e) {a : X → X} {a' : Y → Y}
    (ha : Measurable a) (ha' : Measurable a') (hcomm : ∀ y, e (a' y) = a (e y)) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (hinv : μ.map a = μ) : (μ.comap e).map a' = μ.comap e := by
  have hν := map_comap_of_carried he hμ
  have h2 : ((μ.comap e).map a').map e = μ := by
    rw [Measure.map_map he.measurable ha']
    have h3 : e ∘ a' = a ∘ e := funext hcomm
    rw [h3, ← Measure.map_map ha he.measurable, hν, hinv]
  have h4 := he.comap_map ((μ.comap e).map a')
  rw [h2] at h4
  exact h4.symm

theorem lintegral_comap_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (G : X → ℝ≥0∞) :
    ∫⁻ y, G (e y) ∂(μ.comap e) = ∫⁻ x, G x ∂μ := by
  rw [← he.lintegral_map, map_comap_of_carried he hμ]

theorem comap_ne_zero_of_carried {e : Y → X} (he : MeasurableEmbedding e) {μ : Measure X}
    (hμ : μ (Set.range e)ᶜ = 0) (h0 : μ ≠ 0) : μ.comap e ≠ 0 := by
  intro h
  have h1 := map_comap_of_carried he hμ
  rw [h, Measure.map_zero] at h1
  exact h0 h1.symm

theorem comap_finite_compacts [TopologicalSpace X] [TopologicalSpace Y] {e : Y → X}
    (he : MeasurableEmbedding e) (hc : Continuous e) {S : Set X} (hS : ∀ y, e y ∈ S)
    {μ : Measure X} (hfin : ∀ K, IsCompact K → K ⊆ S → μ K < ⊤) :
    IsFiniteMeasureOnCompacts (μ.comap e) :=
  ⟨fun K hK => by
    rw [he.comap_apply]
    exact hfin _ (hK.image hc) (by rintro _ ⟨y, -, rfl⟩; exact hS y)⟩

end Generic

theorem prod_factor_open : ∀ {ι : Type} [Fintype ι]
  {G₀ : Type} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀] [T2Space G₀]
  [LocallyCompactSpace G₀] [SecondCountableTopology G₀]
  {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
  [∀ i, T2Space (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, SecondCountableTopology (G i)]
  {W₀ : Type} [TopologicalSpace W₀] [T2Space W₀] [LocallyCompactSpace W₀]
  [SecondCountableTopology W₀] [MeasurableSpace W₀] [BorelSpace W₀]
  {W : ι → Type} [∀ i, TopologicalSpace (W i)] [∀ i, T2Space (W i)] [∀ i, LocallyCompactSpace (W i)]
  [∀ i, SecondCountableTopology (W i)] [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]
  (a₀ : G₀ → W₀ → W₀) (a : ∀ i, G i → W i → W i),
  (Continuous fun p : G₀ × W₀ => a₀ p.1 p.2) → (∀ x, a₀ 1 x = x) →
  (∀ g h x, a₀ (g * h) x = a₀ g (a₀ h x)) →
  (∀ i, Continuous fun p : G i × W i => a i p.1 p.2) → (∀ i x, a i 1 x = x) →
  (∀ i g h x, a i (g * h) x = a i g (a i h x)) →
  ∀ (U₀ : Set W₀) (U : ∀ i, Set (W i)), IsOpen U₀ → (∀ i, IsOpen (U i)) →
  (∀ g, ∀ x ∈ U₀, a₀ g x ∈ U₀) → (∀ i g, ∀ x ∈ U i, a i g x ∈ U i) →
  ∀ (Z₀ : Set W₀) (Z : ∀ i, Set (W i)), IsClosed Z₀ → (∀ i, IsClosed (Z i)) →
  (∀ g, ∀ x ∈ Z₀, a₀ g x ∈ Z₀) → (∀ i g, ∀ x ∈ Z i, a i g x ∈ Z i) →
  (∀ x ∈ Z₀ ∩ U₀, ∀ y ∈ Z₀ ∩ U₀, ∃ g, a₀ g x = y) →
  (∀ i, ∀ x ∈ Z i ∩ U i, ∀ y ∈ Z i ∩ U i, ∃ g, a i g x = y) →
  ∀ (m₀ : Measure W₀) (m : ∀ i, Measure (W i)),
  (∀ K, IsCompact K → K ⊆ U₀ → m₀ K < ⊤) → (∀ i K, IsCompact K → K ⊆ U i → m i K < ⊤) →
  (∀ g, m₀.map (a₀ g) = m₀) → (∀ i g, (m i).map (a i g) = m i) →
  m₀ (Z₀ ∩ U₀)ᶜ = 0 → (∀ i, m i (Z i ∩ U i)ᶜ = 0) →
  ((Z₀ ∩ U₀).Nonempty → m₀ ≠ 0) → (∀ i, (Z i ∩ U i).Nonempty → m i ≠ 0) →
  ∀ (P : Measure (W₀ × ∀ i, W i)), IsFiniteMeasureOnCompacts P →
  (∀ (g₀ : G₀) (g : ∀ i, G i),
      P.map (fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i))) = P) →
  P ((Z₀ ∩ U₀) ×ˢ Set.univ.pi fun i => Z i ∩ U i)ᶜ = 0 →
  ∃ c : ℝ≥0, ∀ (f₀ : W₀ → ℝ≥0∞) (f : ∀ i, W i → ℝ≥0∞), Measurable f₀ →
      (∀ i, Measurable (f i)) →
      ∫⁻ x, f₀ x.1 * ∏ i, f i (x.2 i) ∂P =
        (c : ℝ≥0∞) * ((∫⁻ x, f₀ x ∂m₀) * ∏ i, ∫⁻ x, f i x ∂(m i)) := by
  intro ι _ G₀ _ _ _ _ _ _ G _ _ _ _ _ _ W₀ _ _ _ _ _ _ W _ _ _ _ _ _
    a₀ a hc₀ h1₀ hm₀ hc h1 hm U₀ U hU₀ hU hsU₀ hsU Z₀ Z hZ₀ hZ hs₀ hs ht₀ ht m₀ m hfin₀ hfin
    hi₀ hi hz₀ hz hn₀ hn P hPc hP hPZ
  classical
  haveI : LocallyCompactSpace ↥U₀ := hU₀.locallyCompactSpace
  haveI : ∀ i, LocallyCompactSpace ↥(U i) := fun i => (hU i).locallyCompactSpace
  have hmeas₀ : ∀ g, Measurable (a₀ g) := fun g =>
    (hc₀.comp (Continuous.prodMk_right g)).measurable
  have hmeas : ∀ i g, Measurable (a i g) := fun i g =>
    ((hc i).comp (Continuous.prodMk_right g)).measurable
  let b₀ : G₀ → ↥U₀ → ↥U₀ := fun g x => ⟨a₀ g x.1, hsU₀ g x.1 x.2⟩
  let b : ∀ i, G i → ↥(U i) → ↥(U i) := fun i g x => ⟨a i g x.1, hsU i g x.1 x.2⟩
  let E : (↥U₀ × ∀ i, ↥(U i)) → W₀ × ∀ i, W i := Prod.map Subtype.val fun z i => (z i).1
  have he₀ : MeasurableEmbedding (Subtype.val : ↥U₀ → W₀) :=
    MeasurableEmbedding.subtype_coe hU₀.measurableSet
  have he : ∀ i, MeasurableEmbedding (Subtype.val : ↥(U i) → W i) := fun i =>
    MeasurableEmbedding.subtype_coe (hU i).measurableSet
  have hEo : IsOpenEmbedding E :=
    hU₀.isOpenEmbedding_subtypeVal.prodMap
      (IsOpenEmbedding.piMap fun i => (hU i).isOpenEmbedding_subtypeVal)
  have hE : MeasurableEmbedding E := hEo.measurableEmbedding
  have hcar₀ : m₀ (Set.range (Subtype.val : ↥U₀ → W₀))ᶜ = 0 := by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hz₀
    rw [Subtype.range_coe]
    exact Set.inter_subset_right
  have hcar : ∀ i, m i (Set.range (Subtype.val : ↥(U i) → W i))ᶜ = 0 := fun i => by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) (hz i)
    rw [Subtype.range_coe]
    exact Set.inter_subset_right
  have hcarP : P (Set.range E)ᶜ = 0 := by
    refine measure_mono_null (Set.compl_subset_compl.mpr ?_) hPZ
    rintro ⟨x, z⟩ ⟨h₀, hz'⟩
    exact ⟨(⟨x, h₀.2⟩, fun i => ⟨z i, (hz' i (Set.mem_univ i)).2⟩), rfl⟩
  haveI : IsFiniteMeasureOnCompacts (m₀.comap (Subtype.val : ↥U₀ → W₀)) :=
    comap_finite_compacts he₀ continuous_subtype_val (fun y => y.2) (hfin₀)
  haveI : ∀ i, IsFiniteMeasureOnCompacts ((m i).comap (Subtype.val : ↥(U i) → W i)) := fun i =>
    comap_finite_compacts (he i) continuous_subtype_val (fun y => y.2) (hfin i)
  haveI : IsFiniteMeasureOnCompacts (P.comap E) :=
    comap_finite_compacts hE hEo.continuous (S := Set.univ) (fun _ => Set.mem_univ _)
      (fun K hK _ => hK.measure_lt_top)
  have hcb₀ : Continuous fun p : G₀ × ↥U₀ => b₀ p.1 p.2 :=
    Continuous.subtype_mk (hc₀.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))) _
  have hcb : ∀ i, Continuous fun p : G i × ↥(U i) => b i p.1 p.2 := fun i =>
    Continuous.subtype_mk ((hc i).comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))) _
  have hmb₀ : ∀ g, Measurable (b₀ g) := fun g =>
    (hcb₀.comp (Continuous.prodMk_right g)).measurable
  have hmb : ∀ i g, Measurable (b i g) := fun i g =>
    ((hcb i).comp (Continuous.prodMk_right g)).measurable
  obtain ⟨c, hcf⟩ := prod_factor (G₀ := G₀) (G := G) (W₀ := ↥U₀) (W := fun i => ↥(U i)) b₀ b
    hcb₀ (fun x => Subtype.ext (h1₀ x.1)) (fun g h x => Subtype.ext (hm₀ g h x.1))
    hcb (fun i x => Subtype.ext (h1 i x.1)) (fun i g h x => Subtype.ext (hm i g h x.1))
    (Subtype.val ⁻¹' Z₀) (fun i => Subtype.val ⁻¹' Z i)
    (hZ₀.preimage continuous_subtype_val) (fun i => (hZ i).preimage continuous_subtype_val)
    (fun g x hx => hs₀ g x.1 hx) (fun i g x hx => hs i g x.1 hx)
    (fun x hx y hy => by
      obtain ⟨g, hg⟩ := ht₀ x.1 ⟨hx, x.2⟩ y.1 ⟨hy, y.2⟩
      exact ⟨g, Subtype.ext hg⟩)
    (fun i x hx y hy => by
      obtain ⟨g, hg⟩ := ht i x.1 ⟨hx, x.2⟩ y.1 ⟨hy, y.2⟩
      exact ⟨g, Subtype.ext hg⟩)
    (m₀.comap Subtype.val) (fun i => (m i).comap Subtype.val)
    (fun g => comap_invariant he₀ (hmeas₀ g) (hmb₀ g) (fun _ => rfl) hcar₀ (hi₀ g))
    (fun i g => comap_invariant (he i) (hmeas i g) (hmb i g) (fun _ => rfl) (hcar i) (hi i g))
    (by
      rw [he₀.comap_apply]
      refine measure_mono_null ?_ hz₀
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy hmem.1)
    (fun i => by
      rw [(he i).comap_apply]
      refine measure_mono_null ?_ (hz i)
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy hmem.1)
    (fun ⟨x, hx⟩ => comap_ne_zero_of_carried he₀ hcar₀ (hn₀ ⟨x.1, hx, x.2⟩))
    (fun i ⟨x, hx⟩ => comap_ne_zero_of_carried (he i) (hcar i) (hn i ⟨x.1, hx, x.2⟩))
    (P.comap E)
    (fun g₀ g => comap_invariant hE
      (a := fun x => (a₀ g₀ x.1, fun i => a i (g i) (x.2 i)))
      ((hmeas₀ g₀).comp measurable_fst |>.prodMk (measurable_pi_lambda _ fun i =>
        (hmeas i (g i)).comp ((measurable_pi_apply i).comp measurable_snd)))
      ((hmb₀ g₀).comp measurable_fst |>.prodMk (measurable_pi_lambda _ fun i =>
        (hmb i (g i)).comp ((measurable_pi_apply i).comp measurable_snd)))
      (fun _ => rfl) hcarP (hP g₀ g))
    (by
      rw [hE.comap_apply]
      refine measure_mono_null ?_ hPZ
      rintro _ ⟨y, hy, rfl⟩ hmem
      exact hy ⟨hmem.1.1, fun i _ => (hmem.2 i (Set.mem_univ i)).1⟩)
  refine ⟨c, fun f₀ f hf₀ hf => ?_⟩
  have h := hcf (fun x => f₀ x.1) (fun i x => f i x.1) (hf₀.comp measurable_subtype_coe)
    (fun i => (hf i).comp measurable_subtype_coe)
  have hL := lintegral_comap_of_carried hE hcarP fun x => f₀ x.1 * ∏ i, f i (x.2 i)
  have hL₀ := lintegral_comap_of_carried he₀ hcar₀ f₀
  have hLi := fun i => lintegral_comap_of_carried (he i) (hcar i) (f i)
  rw [← hL, ← hL₀]
  simp only [← hLi]
  exact h

end GlobalTheory.CompanionTheory.SW.FactS.OpenFactor
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedComplexCohomology
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.ShiftCoh

variable {K : Type} [Field K]

def ev (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : (Sh ς k C).X n ≃ₗ[K] C.X m where
  toFun y := y ⟨m, h⟩
  invFun x := fun m' => (show m = m'.1 by have := m'.2; omega) ▸ x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    funext ⟨m', h'⟩
    obtain rfl : m' = m := by omega
    rfl
  right_inv _ := rfl

theorem ev_apply (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    ev ς k C h y = y ⟨m, h⟩ := rfl

theorem d_apply_succ (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) (h' : m + 1 + k = n + 1) :
    (Sh ς k C).d n y ⟨m + 1, h'⟩ = (ς : ℤ) • C.d m (y ⟨m, h⟩) := rfl

theorem d_apply_zero (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {n : ℕ} (y : (Sh ς k C).X n) (h' : 0 + k = n + 1) :
    (Sh ς k C).d n y ⟨0, h'⟩ = 0 := rfl

theorem unit_smul_eq_zero (ς : ℤˣ) {M : Type*} [AddCommGroup M] {x : M} : (ς : ℤ) • x = 0 ↔ x = 0 := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem unit_smul_smul (ς : ℤˣ) {M : Type*} [AddCommGroup M] (x : M) : (ς : ℤ) • (ς : ℤ) • x = x := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem ext_at (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) {y z : (Sh ς k C).X n}
    (e : y ⟨m, h⟩ = z ⟨m, h⟩) : y = z :=
  (ev ς k C h).injective e

theorem mem_Z_iff (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    (Sh ς k C).d n y = 0 ↔ C.d m (y ⟨m, h⟩) = 0 := by
  have h' : m + 1 + k = n + 1 := by omega
  constructor
  · intro e
    have := congrFun e ⟨m + 1, h'⟩
    rw [d_apply_succ ς k C h y h'] at this
    exact (unit_smul_eq_zero ς).1 this
  · intro e
    refine ext_at ς k C h' ?_
    rw [d_apply_succ ς k C h y h', e, smul_zero]
    rfl

theorem mem_B_iff (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    y ∈ (Sh ς k C).B n ↔ y ⟨m, h⟩ ∈ C.B m := by
  cases n with
  | zero =>
    obtain rfl : m = 0 := by omega
    constructor
    · intro e
      have e' : y = 0 := e
      rw [e']
      exact Submodule.zero_mem _
    · intro e
      have e' : y ⟨0, h⟩ = 0 := e
      have : y = 0 := ext_at ς k C h e'
      rw [this]
      exact Submodule.zero_mem _
  | succ n =>
    cases m with
    | zero =>
      constructor
      · rintro ⟨x, rfl⟩
        rw [d_apply_zero ς k C x h]
        exact Submodule.zero_mem _
      · intro e
        have e' : y ⟨0, h⟩ = 0 := e
        have : y = 0 := ext_at ς k C h e'
        rw [this]
        exact Submodule.zero_mem _
    | succ m =>
      have h0 : m + k = n := by omega
      constructor
      · rintro ⟨x, rfl⟩
        rw [d_apply_succ ς k C h0 x h]
        exact ⟨(ς : ℤ) • x ⟨m, h0⟩, by rw [map_zsmul]⟩
      · rintro ⟨z, hz⟩
        refine ⟨(ev ς k C h0).symm ((ς : ℤ) • z), ext_at ς k C h ?_⟩
        rw [d_apply_succ ς k C h0 _ h]
        change (ς : ℤ) • C.d m ((ev ς k C h0) ((ev ς k C h0).symm ((ς : ℤ) • z))) = _
        rw [LinearEquiv.apply_symm_apply, map_zsmul, unit_smul_smul, hz]

def evZ (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.Z m ≃ₗ[K] (Sh ς k C).Z n :=
  LinearEquiv.ofSubmodules (ev ς k C h).symm (C.Z m) ((Sh ς k C).Z n) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine (mem_Z_iff ς k C h _).2 ?_
      change C.d m ((ev ς k C h) ((ev ς k C h).symm x)) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hx
    · intro hy
      exact ⟨ev ς k C h y, (mem_Z_iff ς k C h y).1 hy, (ev ς k C h).symm_apply_apply y⟩)

theorem evZ_coe (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.Z m) :
    ev ς k C h (evZ ς k C h x).1 = x.1 :=
  (ev ς k C h).apply_symm_apply x.1

def evH (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.H m ≃ₗ[K] (Sh ς k C).H n :=
  Submodule.Quotient.equiv _ _ (evZ ς k C h) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x.1 ∈ C.B m := hx
      change (evZ ς k C h x).1 ∈ (Sh ς k C).B n
      refine (mem_B_iff ς k C h _).2 ?_
      have := evZ_coe ς k C h x
      rw [ev_apply] at this
      rw [this]
      exact hx'
    · intro hy
      have hy' : y.1 ∈ (Sh ς k C).B n := hy
      refine ⟨(evZ ς k C h).symm y, ?_, (evZ ς k C h).apply_symm_apply y⟩
      change ((evZ ς k C h).symm y).1 ∈ C.B m
      have := evZ_coe ς k C h ((evZ ς k C h).symm y)
      rw [LinearEquiv.apply_symm_apply, ev_apply] at this
      rw [← this]
      exact (mem_B_iff ς k C h _).1 hy')

theorem main : ∀ {K : Type} [Field K] (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) (n : ℕ), (n < k → Subsingleton ((Sh ς k C).H n)) ∧ ∀ (m : ℕ) (h : m + k = n), ∃ e : C.H m ≃ₗ[K] (Sh ς k C).H n, ∀ (y : (Sh ς k C).X n) (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0), e (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy := by
  intro K _ ς k C n
  refine ⟨fun hn => ?_, fun m h => ⟨evH ς k C h, fun y hy hy' => ?_⟩⟩
  · have : IsEmpty {m : ℕ // m + k = n} := ⟨fun x => by have := x.2; omega⟩
    have hX : Subsingleton ((Sh ς k C).X n) :=
      inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, C.X m.1))
    have hZ : Subsingleton ((Sh ς k C).Z n) := ⟨fun a b => Subtype.ext (hX.elim _ _)⟩
    exact Quotient.instSubsingletonQuotient _
  · refine congrArg (Submodule.Quotient.mk (p := ((Sh ς k C).B n).submoduleOf ((Sh ς k C).Z n))) (Subtype.ext ?_)
    exact (ev ς k C h).symm_apply_apply y

end GlobalTheory.CompanionTheory.KunGlue.ShiftCoh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedSystemDescends
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.ShDesc

universe w

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

def cechMap (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S) (n : ℕ) : P.cech.X n →ₗ[R] Q.cech.X n :=
  LinearMap.pi fun i => (e (ent i)).comp (LinearMap.proj i)

theorem cechMap_d (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (P.res h x) = Q.res h (e S x)) (n : ℕ) (x : P.cech.X n) :
    Q.cech.d n (cechMap P Q e n x) = cechMap P Q e (n + 1) (P.cech.d n x) := by
  rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  funext t
  exact (hn _ _).symm

theorem cechMap_aug (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (P.res h x) = Q.res h (e S x)) (x : P.M ∅) :
    Q.aug (e ∅ x) = cechMap P Q e 0 (P.aug x) := by
  funext t
  exact (hn _ _).symm

theorem ex_of_equiv (P Q : PM.{w} R ι) (e : ∀ S, Q.M S ≃ₗ[R] P.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (Q.res h x) = P.res h (e S x)) (hP : P.Ex) : Q.Ex := by
  have hn' : ∀ {S T : Finset ι} (h : S ⊆ T) x, (e T).symm (P.res h x) = Q.res h ((e S).symm x) := by
    intro S T h x
    apply (e T).injective
    rw [hn]
    simp
  let f : ∀ S, P.M S →ₗ[R] Q.M S := fun S => ((e S).symm : P.M S →ₗ[R] Q.M S)
  let g : ∀ S, Q.M S →ₗ[R] P.M S := fun S => ((e S) : Q.M S →ₗ[R] P.M S)
  have hf : ∀ {S T : Finset ι} (h : S ⊆ T) x, f T (P.res h x) = Q.res h (f S x) := hn'
  have hg : ∀ {S T : Finset ι} (h : S ⊆ T) x, g T (Q.res h x) = P.res h (g S x) := hn
  have fg : ∀ n (y : Q.cech.X n), cechMap P Q f n (cechMap Q P g n y) = y := by
    intro n y
    funext t
    exact (e _).symm_apply_apply _
  have gf0 : ∀ n (y : P.cech.X n), cechMap Q P g n (cechMap P Q f n y) = y := by
    intro n y
    funext t
    exact (e _).apply_symm_apply _
  obtain ⟨h0, h1, h2, h3⟩ := hP
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · have : Q.aug y = cechMap P Q f 0 (P.aug (g ∅ y)) := by
      rw [← cechMap_aug P Q f hf]
      congr 1
      exact ((e ∅).symm_apply_apply y).symm
    change Q.cech.d 0 (Q.aug y) = 0
    rw [this, cechMap_d P Q f hf, show P.cech.d 0 (P.aug (g ∅ y)) = 0 from h0 _, map_zero]
  · have h := h1 (g ∅ y) (by
      have := cechMap_aug Q P g hg y
      rw [this]
      change cechMap Q P g 0 (Q.aug y) = 0 at *
      rw [hy, map_zero])
    rw [one_smul] at h ⊢
    exact (e ∅).injective (by rw [map_zero]; exact h)
  · obtain ⟨x, hx⟩ := h2 (cechMap Q P g 0 y) (by
      change P.cech.d 0 _ = 0
      rw [cechMap_d Q P g hg]
      have hy' : Q.cech.d 0 y = 0 := hy
      rw [hy', map_zero])
    refine ⟨f ∅ x, ?_⟩
    rw [one_smul] at hx ⊢
    rw [cechMap_aug P Q f hf]
    have hx' : P.aug x = cechMap Q P g 0 y := hx
    rw [hx', fg]
  · obtain ⟨x, hx⟩ := h3 n (cechMap Q P g (n + 1) y) (by
      change P.cech.d (n + 1) _ = 0
      rw [cechMap_d Q P g hg]
      have hy' : Q.cech.d (n + 1) y = 0 := hy
      rw [hy', map_zero])
    refine ⟨cechMap P Q f n x, ?_⟩
    rw [one_smul] at hx ⊢
    change Q.cech.d n _ = y
    rw [cechMap_d P Q f hf]
    have hx' : P.cech.d n x = cechMap Q P g (n + 1) y := hx
    rw [hx', fg]

theorem ex_of_subsingleton (P : PM.{w} R ι) (h : ∀ S, Subsingleton (P.M S)) : P.Ex := by
  have hX : ∀ n, Subsingleton (P.cech.X n) := fun n =>
    inferInstanceAs (Subsingleton (∀ i : Fin (n + 1) → ι, P.M (ent i)))
  refine ⟨fun x => Subsingleton.elim (α := P.cech.X 1) _ _, fun x _ => Subsingleton.elim _ _,
    fun y _ => ⟨0, Subsingleton.elim (α := P.cech.X 0) _ _⟩, fun n y _ => ⟨0, Subsingleton.elim (α := P.cech.X (n + 1)) _ _⟩⟩

variable {K : Type} [Field K]

def shEv (ς : ℤˣ) (k : ℕ) (C : Cx.{w} K) {m n : ℕ} (h : m + k = n) : (Sh ς k C).X n ≃ₗ[K] C.X m :=
  LinearEquiv.ofBijective
    (LinearMap.proj (φ := fun p : {p : ℕ // p + k = n} => C.X p.1) ⟨m, h⟩) (by
    constructor
    · intro y y' hyy
      funext ⟨p, hp⟩
      obtain rfl : p = m := by omega
      exact hyy
    · intro x
      refine ⟨fun p => (show m = p.1 by have := p.2; omega) ▸ x, rfl⟩)

theorem shSy_desc {ς : ℤˣ} {k : ℕ} {A : Sy.{w} K ι} (hA : A.Desc) : (shSy ς k A).Desc := by
  intro n
  by_cases hk : k ≤ n
  · have h : n - k + k = n := by omega
    exact ex_of_equiv (A.term (n - k)) ((shSy ς k A).term n) (fun S => shEv ς k (A.K S) h)
      (fun _ _ => rfl) (hA (n - k))
  · refine ex_of_subsingleton _ fun S => ?_
    have : IsEmpty {m : ℕ // m + k = n} := ⟨fun p => hk (by have := p.2; omega)⟩
    exact inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, (A.K S).X m.1))

theorem sh_desc : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] (ς : ℤˣ) (k : ℕ) (A : Sy.{1} K ι),
    A.Desc → (shSy ς k A).Desc :=
  fun _ _ _ h => shSy_desc h

end GlobalTheory.CompanionTheory.KunGlue.ShDesc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorDirectSumBasisEquiv
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem tensBasis : ∀ {K : Type} [Field K] {J : Type} [DecidableEq J] (V W : J → Type 1) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)] (B : J → Type 1) [DecidableEq (Σ t, B t)] (b : ∀ t, Module.Basis (B t) K (V t)), ∃ e : (⨁ t, V t ⊗[K] W t) ≃ₗ[K] ⨁ u : (Σ t, B t), W u.1, ∀ (t : J) (β : B t) (x : W t), e (DirectSum.lof K J (fun t => V t ⊗[K] W t) t (b t β ⊗ₜ x)) = DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x := by
  classical
  intro K _ J _ V W _ _ _ _ B _ b
  let et : ∀ t, (V t ⊗[K] W t) ≃ₗ[K] (Π₀ _ : B t, W t) := fun t =>
    (TensorProduct.congr (b t).repr (LinearEquiv.refl K (W t))) ≪≫ₗ
      (TensorProduct.finsuppScalarLeft K (W t) (B t)) ≪≫ₗ (finsuppLequivDFinsupp K)
  have het : ∀ t (β : B t) (x : W t), et t (b t β ⊗ₜ x) = DFinsupp.single β x := by
    intro t β x
    simp [et, TensorProduct.finsuppScalarLeft_apply_tmul, Module.Basis.repr_self]
  let C : (⨁ u : (Σ t, B t), W u.1) ≃ₗ[K] (Π₀ t, Π₀ _ : B t, W t) :=
    DFinsupp.sigmaCurryLEquiv (R := K) (M := fun t (_ : B t) => W t)
  refine ⟨(DFinsupp.mapRange.linearEquiv et) ≪≫ₗ C.symm, ?_⟩
  intro t β x
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  have h1 : C (DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x)
      = DFinsupp.single t (DFinsupp.single β x) := by
    have : DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x
        = DFinsupp.single (⟨t, β⟩ : Σ t, B t) x := rfl
    rw [this]
    change DFinsupp.sigmaCurry (δ := fun t (_ : B t) => W t) (DFinsupp.single (⟨t, β⟩ : Σ t, B t) x) = _
    convert DFinsupp.sigmaCurry_single (δ := fun t (_ : B t) => W t) (⟨t, β⟩ : Σ t, B t) x
  rw [h1, ← het]
  exact DFinsupp.mapRange_single (hf := fun i => map_zero (et i))

end GlobalTheory.CompanionTheory.KunGlue
end

