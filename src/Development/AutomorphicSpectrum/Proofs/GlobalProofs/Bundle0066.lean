import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.FdSetIntegralCharEqZero
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart

open GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar

section Groups

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def ptStab (A : Submodule (AF F ⊗[F] E) (Fin n → AF F ⊗[F] E)) : Subgroup (GAd σ J) where
  carrier := {g | ∀ y ∈ A, (matHom _ σ J g).1 *ᵥ y = y}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {a b} ha hb y hy => by
    rw [map_mul, Units.val_mul, ← mulVec_mulVec, hb y hy, ha y hy]
  inv_mem' := fun {a} ha y hy => by
    conv_lhs => rw [← ha y hy]
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]

def block (T : Finset (Fin r)) (k : Fin r) : Set (Fin r) := {i | i ≤ k ∧ ∀ t ∈ T, t < k → t < i}

def upTo (T : Finset (Fin r)) : Set (Fin r) := {i | ∃ k ∈ T, i ≤ k}

variable (X Y : Matrix (Fin n) (Fin r) E) (T : Finset (Fin r))

def glPart (k : Fin r) : Subgroup (GAd σ J) :=
  levi σ J X Y T ⊓ ptStab σ J (colPerp σ J X (block T k) ⊓ colPerp σ J Y (block T k))

def uPart : Subgroup (GAd σ J) := ptStab σ J (colSpan F X (upTo T) ⊔ colSpan F Y (upTo T))

def part : Option {k // k ∈ T} → Subgroup (GAd σ J)
  | none => uPart σ J X Y T
  | some k => glPart σ J X Y T k.1

end Groups

def sliceSet {G : Type} [Group G] (𝓒 : Set (G → ℂ)) (H L : Subgroup G) (b : G) : Set (H → ℂ) :=
  {f | ∃ φ ∈ 𝓒, ∃ y ∈ L, (∀ t ∈ H, t * y = y * t) ∧ f = fun t : H => φ ((t : G) * y * b)}

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin in

def cuspOn {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) {m : ℕ}
    (X Y : Matrix (Fin V.rank) (Fin m) D.host.E) (T : Finset (Fin m)) (U : Subgroup (GA D V))
    (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    {W : D.what₂.Tau → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)]
    (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)) (c : D.what₂.Tau → ℕ → ℂ) : Set (GA D V → ℂ) :=
  {φ | φ ∈ formsOn θ V X Y T U ε fr ρ c ∧ ∀ T' : Finset (Fin m), T ⊂ T' → IsConstAlong D.sp.cm.sig V.gram X T' φ 0}

section Slices

theorem exists_finset_sep {X : Type} (A : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ A] :
    ∃ S : Finset X, ∀ f ∈ A, (∀ x ∈ S, f x = 0) → f = 0 := by
  classical
  let ev : X → Module.Dual ℂ A := fun x => (LinearMap.proj x).comp A.subtype
  have hfg : (Submodule.span ℂ (Set.range ev)).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, e⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  obtain ⟨s', -, rfl⟩ := Finset.subset_set_image_iff.1 (by rwa [Set.image_univ] : (s : Set (Module.Dual ℂ A)) ⊆ ev '' Set.univ)
  refine ⟨s', fun f hf h0 => ?_⟩
  have h1 : ∀ l ∈ Submodule.span ℂ ((s'.image ev : Finset _) : Set (Module.Dual ℂ A)), l ⟨f, hf⟩ = 0 := fun l hl => by
    induction hl using Submodule.span_induction with
    | mem l h =>
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 h
      exact h0 x hx
    | zero => rfl
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [hb]
  funext x
  exact h1 (ev x) (e ▸ Submodule.subset_span ⟨x, rfl⟩)

theorem finiteDimensional_of_slices {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule ℂ (X i → ℂ))
    [∀ i, FiniteDimensional ℂ (A i)] (𝓕 : Set ((∀ i, X i) → ℂ))
    (h : ∀ f ∈ 𝓕, ∀ i x, (fun t => f (Function.update x i t)) ∈ A i) :
    FiniteDimensional ℂ (Submodule.span ℂ 𝓕) := by
  let P : Submodule ℂ ((∀ i, X i) → ℂ) :=
    { carrier := {f | ∀ i x, (fun t => f (Function.update x i t)) ∈ A i}
      add_mem' := fun {a b} ha hb i x => (A i).add_mem (ha i x) (hb i x)
      zero_mem' := fun i _ => (A i).zero_mem
      smul_mem' := fun a f hf i x => (A i).smul_mem a (hf i x) }
  choose S hS using fun i => exists_finset_sep (A i)
  let ev : P →ₗ[ℂ] ((∀ i, S i) → ℂ) :=
    { toFun := fun f s => f.1 fun i => (s i).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have key : ∀ f : P, ev f = 0 → ∀ I : Finset ι, ∀ x : ∀ i, X i, (∀ i, i ∉ I → x i ∈ S i) → f.1 x = 0 := by
    intro f hf I
    induction I using Finset.induction_on with
    | empty =>
      intro x hx
      exact congrFun hf fun i => ⟨x i, hx i (by simp)⟩
    | insert a I _ ih =>
      intro x hx
      have := hS a _ (f.2 a x) fun t ht => ih _ fun i hi => by
        by_cases e : i = a
        · subst e; simpa using ht
        · rw [Function.update_of_ne e]
          exact hx i (by simp [e, hi])
      simpa using congrFun this (x a)
  have hinj : Function.Injective ev := (injective_iff_map_eq_zero ev).2 fun f hf =>
    Subtype.ext (funext fun x => key f hf Finset.univ x (by simp))
  haveI : FiniteDimensional ℂ P := FiniteDimensional.of_injective ev hinj
  exact Submodule.finiteDimensional_of_le (S₂ := P) (Submodule.span_le.2 fun f hf i x => h f hf i x)

end Slices

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralEqTsumFd
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs

section Gen

variable {V C : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
  [T2Space V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [AddCommGroup C] [Countable C]

def per (ι : C →+ V) (f : V → ℂ) (b : V) : ℂ := ∑' c, f (b + ι c)

def UnifSummable (ι : C →+ V) (f : V → ℂ) : Prop :=
  ∀ K : Set V, IsCompact K → ∃ u : C → ℝ, Summable u ∧ ∀ c : C, ∀ b ∈ K, ‖f (b + ι c)‖ ≤ u c

theorem continuous_per {ι : C →+ V} {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f) :
    Continuous (per ι f) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  obtain ⟨u, hu, hb⟩ := h K hK
  have : ContinuousOn (per ι f) K :=
    continuousOn_tsum (fun c => (hf.comp (continuous_id.add continuous_const)).continuousOn) hu
      (fun c b hb' => hb c b hb')
  exact this.continuousAt hxK

theorem per_add (ι : C →+ V) (f : V → ℂ) (x : V) (c : C) : per ι f (x + ι c) = per ι f x := by
  unfold per
  rw [← (Equiv.addLeft c).tsum_eq (fun d => f (x + ι d))]
  refine tsum_congr fun d => ?_
  simp [add_assoc]

theorem per_bounded {ι : C →+ V} {f : V → ℂ} (h : UnifSummable ι f) {K : Set V} (hK : IsCompact K)
    (hx : ∀ x, ∃ a, x - ι a ∈ K) : ∃ M, ∀ x, ‖per ι f x‖ ≤ M := by
  obtain ⟨u, hu, hb⟩ := h K hK
  refine ⟨∑' c, u c, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hx x
  have e : per ι f x = per ι f (x - ι a) := by
    rw [← per_add ι f (x - ι a) a, sub_add_cancel]
  rw [e]
  exact tsum_of_norm_bounded hu.hasSum fun c => hb c _ ha

theorem integrableOn_bdd {μ : Measure V} {D : Set V} (hD : μ D ≠ ∞) {g : V → ℂ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ x, ‖g x‖ ≤ M) : IntegrableOn g D μ :=
  Measure.integrableOn_of_bounded hD hg.aestronglyMeasurable (Filter.Eventually.of_forall hM)

theorem integrable_of_unif {ι : C →+ V} {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f)
    (μ : Measure V) [μ.IsAddHaarMeasure] {K : Set V} (hK : IsCompact K) (hx : ∀ x, ∃ a, x - ι a ∈ K) :
    Integrable f μ := by
  obtain ⟨u, hu, hb⟩ := h K hK
  obtain ⟨k, hk⟩ : K.Nonempty := by
    obtain ⟨a, ha⟩ := hx 0
    exact ⟨_, ha⟩
  have hu0 : ∀ a, 0 ≤ u a := fun a => (norm_nonneg _).trans (hb a k hk)
  let s : C → TopologicalSpace.Compacts V := fun a =>
    ⟨(fun y => y + ι a) '' K, hK.image (continuous_id.add continuous_const)⟩
  let G : C(V, ℂ) := ⟨f, hf⟩
  have hs : ⋃ a, (s a : Set V) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨a, ha⟩ := hx x
    exact ⟨a, x - ι a, ha, sub_add_cancel _ _⟩
  have hμ : ∀ a, μ.real (s a : Set V) = μ.real K := by
    intro a
    have : ((s a : TopologicalSpace.Compacts V) : Set V) = (fun y => y + -ι a) ⁻¹' K := by
      show (fun y => y + ι a) '' K = _
      rw [Set.image_add_right]
    rw [this, Measure.real, Measure.real, measure_preimage_add_right]
  have hn : ∀ a, ‖G.restrict (s a : Set V)‖ ≤ u a := by
    intro a
    rw [ContinuousMap.norm_le _ (hu0 a)]
    rintro ⟨y, b, hb', rfl⟩
    exact hb a b hb'
  refine integrable_of_summable_norm_restrict (f := G) (s := s) ?_ hs
  refine Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) measureReal_nonneg) (fun a => ?_)
    (hu.mul_right (μ.real K))
  rw [hμ]
  exact mul_le_mul_of_nonneg_right (hn a) measureReal_nonneg

theorem countable_range (ι : C →+ V) : Countable ι.range :=
  ι.rangeRestrict_surjective.countable

theorem summable_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    Summable fun c => ∫ x in D, ‖h (x + ι c)‖ ∂μ := by
  have := countable_range ι
  have hsum := hD.lintegral_eq_tsum'' (fun x => ‖h x‖ₑ)
  have hfin : ∑' g : ι.range, ∫⁻ x in D, ‖h (g +ᵥ x)‖ₑ ∂μ ≠ ∞ := by
    rw [← hsum]
    exact hh.2.ne
  have hs := ENNReal.summable_toReal hfin
  have h2 := ((ι.ofInjective hι).toEquiv.summable_iff).2 hs
  refine h2.congr fun c => ?_
  rw [integral_norm_eq_lintegral_enorm (hh.comp_add_right (ι c)).integrableOn.aestronglyMeasurable]
  have : ∀ x, ((ι.ofInjective hι).toEquiv c : ι.range) +ᵥ x = x + ι c := fun x => by
    show ι c + x = x + ι c
    exact add_comm _ _
  simp only [Function.comp, this]

theorem integral_eq_tsum_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    ∫ x, h x ∂μ = ∑' c, ∫ x in D, h (x + ι c) ∂μ := by
  have := countable_range ι
  rw [hD.integral_eq_tsum'' h hh, ← (ι.ofInjective hι).toEquiv.tsum_eq]
  refine tsum_congr fun c => ?_
  have : ∀ x, ((ι.ofInjective hι).toEquiv c : ι.range) +ᵥ x = x + ι c := fun x => by
    show ι c + x = x + ι c
    exact add_comm _ _
  simp only [this]

theorem setIntegral_tsum_fd {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {h : V → ℂ} (hh : Integrable h μ) :
    ∫ x in D, ∑' c, h (x + ι c) ∂μ = ∫ x, h x ∂μ := by
  have hs := hasSum_integral_of_summable_integral_norm (μ := μ.restrict D)
    (F := fun c x => h (x + ι c))
    (fun c => (hh.comp_add_right (ι c)).integrableOn) (summable_fd hι hD hh)
  rw [integral_eq_tsum_fd hι hD hh]
  exact hs.tsum_eq.symm

theorem per_unfold {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) {f e : V → ℂ} (hfi : Integrable f μ)
    (he : Continuous e) (hen : ∀ x, ‖e x‖ = 1) (hep : ∀ x c, e (x + ι c) = e x) :
    ∫ b in D, per ι f b * e b ∂μ = ∫ b, f b * e b ∂μ := by
  have hh : Integrable (fun b => f b * e b) μ :=
    hfi.mono (hfi.aestronglyMeasurable.mul he.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by simp [hen])
  rw [← setIntegral_tsum_fd hι hD hh]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show per ι f x * e x = ∑' c, f (x + ι c) * e (x + ι c)
  simp only [hep]
  exact tsum_mul_right.symm

def ser (a : C → ℂ) (E : C → V → ℂ) (b : V) : ℂ := ∑' t, a t * E t b

theorem continuous_ser {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) : Continuous (ser a E) :=
  continuous_tsum (fun t => continuous_const.mul (hEc t)) ha (fun t b => by simp [hEn])

theorem norm_ser_le {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEn : ∀ t b, ‖E t b‖ = 1) (b : V) : ‖ser a E b‖ ≤ ∑' t, ‖a t‖ :=
  tsum_of_norm_bounded ha.hasSum fun t => by simp [hEn]

theorem coef_ser {a : C → ℂ} (ha : Summable fun t => ‖a t‖) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) {μ : Measure V} {D : Set V}
    (hD1 : μ D = 1) (hself : ∀ t x, E t x * E (-t) x = 1)
    (horth : ∀ s t, t ≠ s → ∫ x in D, E t x * E (-s) x ∂μ = 0) (s : C) :
    ∫ x in D, ser a E x * E (-s) x ∂μ = a s := by
  classical
  have hDf : μ D ≠ ∞ := by rw [hD1]; exact ENNReal.one_ne_top
  have hr : μ.real D = 1 := by simp [Measure.real, hD1]
  have hint : ∀ t, IntegrableOn (fun x => a t * E t x * E (-s) x) D μ := fun t =>
    integrableOn_bdd hDf ((continuous_const.mul (hEc t)).mul (hEc (-s))) (M := ‖a t‖)
      (fun x => by simp [hEn])
  have hn : ∀ t, ∫ x in D, ‖a t * E t x * E (-s) x‖ ∂μ = ‖a t‖ := fun t => by
    simp [hEn, hr]
  have hs := hasSum_integral_of_summable_integral_norm (μ := μ.restrict D)
    (F := fun t x => a t * E t x * E (-s) x) hint (by simpa only [hn] using ha)
  have hval : ∀ t, t ≠ s → ∫ x in D, a t * E t x * E (-s) x ∂μ = 0 := fun t ht => by
    simp only [mul_assoc]
    rw [integral_const_mul, horth s t ht, mul_zero]
  have hs1 : ∫ x in D, a s * E s x * E (-s) x ∂μ = a s := by
    simp only [mul_assoc, hself]
    simp [hr]
  have h1 := hasSum_single (f := fun t => ∫ x in D, a t * E t x * E (-s) x ∂μ) s
    (fun t ht => hval t ht)
  have h2 := hs.unique h1
  rw [hs1] at h2
  rw [← h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ser a E x * E (-s) x = ∑' t, a t * E t x * E (-s) x
  simp only [ser, tsum_mul_right]

theorem poisson_gen {ι : C →+ V} (hι : Function.Injective ι) {μ : Measure V} [μ.IsAddHaarMeasure]
    {D : Set V} (hD : IsAddFundamentalDomain ι.range D μ) (hD1 : μ D = 1) {K : Set V}
    (hK : IsCompact K) (hx : ∀ x, ∃ a, x - ι a ∈ K) {E : C → V → ℂ}
    (hEc : ∀ t, Continuous (E t)) (hEn : ∀ t b, ‖E t b‖ = 1) (hEp : ∀ t x c, E t (x + ι c) = E t x)
    (hE0 : ∀ t, E t 0 = 1) (hself : ∀ t x, E t x * E (-t) x = 1)
    (horth : ∀ s t, t ≠ s → ∫ x in D, E t x * E (-s) x ∂μ = 0)
    (hcomp : ∀ g : V → ℂ, Continuous g → (∀ x c, g (x + ι c) = g x) →
      (∀ t, ∫ b in D, g b * E (-t) b ∂μ = 0) → ∀ x, g x = 0)
    {f : V → ℂ} (hf : Continuous f) (h : UnifSummable ι f) :
    Integrable f μ ∧ (Summable (fun t => ∫ b, f b * E (-t) b ∂μ) →
      ∑' c, f (ι c) = ∑' t, ∫ b, f b * E (-t) b ∂μ) := by
  have hfi := integrable_of_unif hf h μ hK hx
  refine ⟨hfi, fun hsum => ?_⟩
  have hDf : μ D ≠ ∞ := by rw [hD1]; exact ENNReal.one_ne_top
  set a : C → ℂ := fun t => ∫ b, f b * E (-t) b ∂μ with hadef
  have ha : Summable fun t => ‖a t‖ := hsum.norm
  have hP := continuous_per hf h
  have hS := continuous_ser ha hEc hEn
  obtain ⟨M, hM⟩ := per_bounded h hK hx
  have hperS : ∀ x c, ser a E (x + ι c) = ser a E x := fun x c => by
    simp only [ser, hEp]
  have hz := hcomp (fun x => per ι f x - ser a E x) (hP.sub hS)
    (fun x c => by simp only [per_add, hperS]) (fun t => ?_) 0
  · have e1 : per ι f 0 = ∑' c, f (ι c) := by simp [per]
    have e2 : ser a E 0 = ∑' t, a t := by simp [ser, hE0]
    rw [← e1, ← e2]
    exact sub_eq_zero.1 hz
  · have i1 : IntegrableOn (fun b => per ι f b * E (-t) b) D μ :=
      integrableOn_bdd hDf (hP.mul (hEc _)) (M := M) (fun x => by simpa [hEn] using hM x)
    have i2 : IntegrableOn (fun b => ser a E b * E (-t) b) D μ :=
      integrableOn_bdd hDf (hS.mul (hEc _)) (M := ∑' t, ‖a t‖)
        (fun x => by simpa [hEn] using norm_ser_le ha hEn x)
    simp only [sub_mul]
    rw [integral_sub i1 i2, per_unfold hι hD hfi (hEc _) (hEn _) (hEp _),
      coef_ser ha hEc hEn hD1 hself horth t, sub_eq_zero]

end Gen

section Adelic

end Adelic
end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiAbs
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.RationalUnipotentLeParabolic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin

open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev

theorem ratPts_unip_le_leftSub : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ S T : Finset (Fin m), S ⊆ T →
      GQ V ⊓ unip D.sp.cm.sig V.gram X T ≤ leftSub V X Y S := by
  intro D V m X Y hW S T hST
  have hCM := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hH := Orb.isHermND_gram V
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS
    intro g hg
    rw [Subgroup.mem_inf] at hg
    unfold leftSub
    apply Subgroup.mem_sup_right
    refine Subgroup.mem_inf.2 ⟨hg.1, ?_⟩
    simp [GlobalTheory.StdPar.levi]
  · have hkS : S.max' hS ∈ S := S.max'_mem hS
    have hle : ∀ j ∈ S, j ≤ S.max' hS := fun j hj => S.le_max' j hj
    have hs : ((S.max' hS : Fin m) : ℕ) + 1 ≤ m := (S.max' hS).isLt
    have hiff : ∀ i : Fin m, (i : ℕ) < (S.max' hS : ℕ) + 1 ↔ ∃ j ∈ S, i ≤ j := by
      intro i
      constructor
      · intro hi
        exact ⟨S.max' hS, hkS, Fin.le_iff_val_le_val.2 (Nat.lt_succ_iff.1 hi)⟩
      · rintro ⟨j, hj, hij⟩
        have h1 := Fin.le_iff_val_le_val.1 hij
        have h2 := Fin.le_iff_val_le_val.1 (hle j hj)
        omega
    obtain ⟨hU, hL, -⟩ := GlobalTheory.TieStd.stdPar_eq_flag _ _ D.sp.cm.sig hCM _ V.gram hH m X Y hW S _ hs hiff
      (fun i => ({x ∈ S | x < Fin.castLE hs i} : Finset (Fin m)).card) (fun _ => rfl)
    have hpar := GlobalTheory.ConstTrans.unip_le_parFlag _ _ D.sp.cm.sig hCM _ V.gram hH m X Y hW T S (S.max' hS) hST hkS hle
    have hxx : Formalism.UG.cT (↑D.sp.cm.sig) (X.submatrix id (Fin.castLE hs)) * V.gram * X.submatrix id (Fin.castLE hs) = 0 := by
      ext i j
      have := congrFun (congrFun hW.xx (Fin.castLE hs i)) (Fin.castLE hs j)
      simpa [Formalism.UG.cT, Matrix.mul_apply] using this
    have hyy : Formalism.UG.cT (↑D.sp.cm.sig) (Y.submatrix id (Fin.castLE hs)) * V.gram * Y.submatrix id (Fin.castLE hs) = 0 := by
      ext i j
      have := congrFun (congrFun hW.yy (Fin.castLE hs i)) (Fin.castLE hs j)
      simpa [Formalism.UG.cT, Matrix.mul_apply] using this
    have hxy : Formalism.UG.cT (↑D.sp.cm.sig) (X.submatrix id (Fin.castLE hs)) * V.gram * Y.submatrix id (Fin.castLE hs) = 1 := by
      ext i j
      have := congrFun (congrFun hW.xy (Fin.castLE hs i)) (Fin.castLE hs j)
      simpa [Formalism.UG.cT, Matrix.mul_apply, Matrix.one_apply, Fin.ext_iff] using this
    obtain ⟨hdec, -⟩ := GlobalTheory.LeviFlag.levi_decomposition _ _ D.sp.cm.sig hCM _ V.gram hH _
      (X.submatrix id (Fin.castLE hs)) (Y.submatrix id (Fin.castLE hs))
      (fun i => ({x ∈ S | x < Fin.castLE hs i} : Finset (Fin m)).card) hxx hyy hxy
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgQ, hgT⟩ := hg
    have hp := hpar hgT
    obtain ⟨u, hu, l, hl, rfl, hrat⟩ := hdec g hp
    unfold leftSub
    rw [hU, hL]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨hrat hgQ, hl⟩))

end GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin
end
end

