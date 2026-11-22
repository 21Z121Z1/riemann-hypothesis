import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0415
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0187
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0039
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0028
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0057
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0027
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFixedNonzero
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.SmInd

def bump {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] (P : Subgroup G)
    (σ : Representation ℂ P W) (K : Subgroup G) (x : W) (g : G) : W :=
  if h : ∃ p : P, (p : G)⁻¹ * g ∈ K then σ h.choose x else 0

variable {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W] {P : Subgroup G}
  {σ : Representation ℂ P W} {K : Subgroup G} {x : W}

theorem bump_eq (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) {p : P} {g : G}
    (hp : (p : G)⁻¹ * g ∈ K) : bump P σ K x g = σ p x := by
  have h : ∃ p : P, (p : G)⁻¹ * g ∈ K := ⟨p, hp⟩
  have hq := h.choose_spec
  rw [bump, dif_pos h]
  set q := h.choose
  have hm : ((q⁻¹ * p : P) : G) ∈ K := by
    have := K.mul_mem hq (K.inv_mem hp)
    have e : (q : G)⁻¹ * g * ((p : G)⁻¹ * g)⁻¹ = ((q⁻¹ * p : P) : G) := by
      simp [mul_assoc]
    rwa [e] at this
  have h2 := hx _ hm
  have h3 : σ p x = σ q (σ (q⁻¹ * p) x) := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  rw [h3, h2]

theorem bump_of_not {g : G} (h : ¬ ∃ p : P, (p : G)⁻¹ * g ∈ K) : bump P σ K x g = 0 := by
  rw [bump, dif_neg h]

theorem bump_mul_left (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) (p : P) (g : G) :
    bump P σ K x ((p : G) * g) = σ p (bump P σ K x g) := by
  by_cases h : ∃ q : P, (q : G)⁻¹ * g ∈ K
  · obtain ⟨q, hq⟩ := h
    have hq' : (((p * q : P) : G))⁻¹ * ((p : G) * g) ∈ K := by
      have e : (((p * q : P) : G))⁻¹ * ((p : G) * g) = (q : G)⁻¹ * g := by
        simp [mul_assoc]
      rwa [e]
    rw [bump_eq hx hq', bump_eq hx hq, map_mul, Module.End.mul_apply]
  · have h' : ¬ ∃ r : P, (r : G)⁻¹ * ((p : G) * g) ∈ K := by
      rintro ⟨r, hr⟩
      refine h ⟨p⁻¹ * r, ?_⟩
      have e : (((p⁻¹ * r : P) : G))⁻¹ * g = (r : G)⁻¹ * ((p : G) * g) := by
        simp [mul_assoc]
      rwa [e]
    rw [bump_of_not h, bump_of_not h', map_zero]

theorem bump_mul_right (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) (g : G) {k : G} (hk : k ∈ K) :
    bump P σ K x (g * k) = bump P σ K x g := by
  by_cases h : ∃ q : P, (q : G)⁻¹ * g ∈ K
  · obtain ⟨q, hq⟩ := h
    have hq' : (q : G)⁻¹ * (g * k) ∈ K := by
      rw [← mul_assoc]; exact K.mul_mem hq hk
    rw [bump_eq hx hq', bump_eq hx hq]
  · have h' : ¬ ∃ r : P, (r : G)⁻¹ * (g * k) ∈ K := by
      rintro ⟨r, hr⟩
      refine h ⟨r, ?_⟩
      have := K.mul_mem hr (K.inv_mem hk)
      have e : (r : G)⁻¹ * (g * k) * k⁻¹ = (r : G)⁻¹ * g := by simp [mul_assoc]
      rwa [e] at this
    rw [bump_of_not h, bump_of_not h']

theorem bump_one (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : bump P σ K x 1 = x := by
  have h : ((1 : P) : G)⁻¹ * 1 ∈ K := by simp [K.one_mem]
  rw [bump_eq hx h]; simp

def bumpInd (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : indSpace P σ :=
  ⟨bump P σ K x, fun p g => bump_mul_left hx p g⟩

theorem ind_bumpInd (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) {k : G} (hk : k ∈ K) :
    ind P σ k (bumpInd hx) = bumpInd hx := by
  apply Subtype.ext
  funext g
  exact bump_mul_right hx g hk

theorem fixed_smInd_ne_bot [TopologicalSpace G] [IsTopologicalGroup G] (hK : IsOpen (K : Set G))
    (hx0 : x ≠ 0) (hx : ∀ p : P, (p : G) ∈ K → σ p x = x) : fixed (smInd P σ) K ≠ ⊥ := by
  have hs : bumpInd hx ∈ smoothPart (ind P σ) :=
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      fun k hk => ind_bumpInd hx hk)
  refine (Submodule.ne_bot_iff _).2 ⟨⟨bumpInd hx, hs⟩, ?_, ?_⟩
  · intro k
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact Subtype.ext (ind_bumpInd hx k.2)
  · intro h
    apply hx0
    have h1 := congrFun (congrArg (fun φ : smoothPart (ind P σ) => (φ.1 : G → W)) h) 1
    rw [← bump_one hx]
    exact h1

theorem fixed_smInd_ne_bot_of_fixed : ∀ (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W] (P : Subgroup G) (σ : Representation ℂ P W) (K : Subgroup G), IsOpen (K : Set G) → ∀ x : W, x ≠ 0 → (∀ p : P, (p : G) ∈ K → σ p x = x) → fixed (smInd P σ) K ≠ ⊥ :=
  fun _ _ _ _ _ _ _ _ _ _ hK _ hx0 hx => fixed_smInd_ne_bot hK hx0 hx

end GlobalTheory.CompanionTheory.SmInd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterpolationLocalL2Bound
section
open MeasureTheory

namespace GlobalTheory.CompanionTheory.InterpLoc

theorem exists_finset_separating {Y : Type} (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ] :
    ∃ t : Finset Y, ∀ ψ ∈ Ψ, (∀ y ∈ t, ψ y = 0) → ψ = 0 := by
  classical
  let K : Finset Y → Submodule ℂ (Y → ℂ) := fun t =>
    { carrier := {ψ | ψ ∈ Ψ ∧ ∀ y ∈ t, ψ y = 0}
      add_mem' := fun {a b} ha hb =>
        ⟨Ψ.add_mem ha.1 hb.1, fun y hy => by simp [ha.2 y hy, hb.2 y hy]⟩
      zero_mem' := ⟨Ψ.zero_mem, fun _ _ => rfl⟩
      smul_mem' := fun c a ha =>
        ⟨Ψ.smul_mem c ha.1, fun y hy => by simp [ha.2 y hy]⟩ }
  have hKle : ∀ t, K t ≤ Ψ := fun t _ h => h.1
  haveI : ∀ t, FiniteDimensional ℂ (K t) := fun t => Submodule.finiteDimensional_of_le (hKle t)
  let f : Finset Y → ℕ := fun t => Module.finrank ℂ (K t)
  refine ⟨Function.argmin f, fun ψ hψ h0 => ?_⟩
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  set t := Function.argmin f with ht
  have hlt : K (insert y t) < K t := by
    refine lt_of_le_of_ne (fun a ha => ⟨ha.1, fun z hz => ha.2 z (Finset.mem_insert_of_mem hz)⟩) ?_
    intro heq
    have hmem : ψ ∈ K t := ⟨hψ, h0⟩
    rw [← heq] at hmem
    exact hy (hmem.2 y (Finset.mem_insert_self y t))
  have h1 : f (insert y t) < f t := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : f t ≤ f (insert y t) := Function.argmin_le f _
  omega

theorem bound_of_injective {Y : Type} [MeasurableSpace Y] (μ : Measure Y)
    (Ψ : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ Ψ]
    (hm : ∀ ψ ∈ Ψ, MemLp ψ 2 μ) (hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[μ] 0 → ψ = 0) (y₀ : Y) :
    ∃ C : NNReal, ∀ ψ ∈ Ψ, ‖ψ y₀‖ₑ ^ 2 ≤ C * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
  let T : Ψ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := fun ψ => (hm ψ.1 ψ.2).toLp ψ.1
      map_add' := fun a b => MemLp.toLp_add (hm a.1 a.2) (hm b.1 b.2)
      map_smul' := fun c a => MemLp.toLp_const_smul c (hm a.1 a.2) }
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ψ hψ
    have h0 : ψ.1 =ᵐ[μ] 0 := (MemLp.toLp_eq_toLp_iff (hm ψ.1 ψ.2) MemLp.zero).1 (by
      rw [MemLp.toLp_zero]; exact hψ)
    exact Subtype.ext (hinj ψ.1 ψ.2 h0)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hker
  let ev : Ψ →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => ψ.1 y₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ℓ : LinearMap.range T →ₗ[ℂ] ℂ := (ev ∘ₗ g).domRestrict (LinearMap.range T)
  let L : LinearMap.range T →L[ℂ] ℂ := ⟨ℓ, LinearMap.continuous_of_finiteDimensional ℓ⟩
  refine ⟨‖L‖₊ ^ 2, fun ψ hψ => ?_⟩
  let p : Ψ := ⟨ψ, hψ⟩
  have hL : L ⟨T p, LinearMap.mem_range_self T p⟩ = ψ y₀ := by
    change ev (g (T p)) = ψ y₀
    have : g (T p) = p := LinearMap.congr_fun hg p
    rw [this]; rfl
  have hb : ‖ψ y₀‖₊ ≤ ‖L‖₊ * ‖T p‖₊ := by
    rw [← hL]
    exact L.le_opNNNorm _
  have hen : ‖T p‖ₑ = eLpNorm ψ 2 μ := Lp.enorm_toLp (hm ψ hψ)
  have hb' : ‖ψ y₀‖ₑ ≤ (‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ := by
    rw [← hen]
    simp only [enorm_eq_nnnorm]
    exact_mod_cast hb
  have hsq : eLpNorm ψ 2 μ ^ 2 = ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
    have := eLpNorm_nnreal_pow_eq_lintegral (f := ψ) (μ := μ) (p := 2) (by norm_num)
    simpa using this
  calc ‖ψ y₀‖ₑ ^ 2 ≤ ((‖L‖₊ : ENNReal) * eLpNorm ψ 2 μ) ^ 2 := by gcongr
    _ = ((‖L‖₊ ^ 2 : NNReal) : ENNReal) * ∫⁻ y, ‖ψ y‖ₑ ^ 2 ∂μ := by
      rw [mul_pow, hsq]; push_cast; rfl

theorem interpolation_local_L2_bound : PositivityTheory.Rg.BcB.E.E3.InterpolationL2Bound := by
  intro X Y _ _ _ _ _ ν _ _ F hF hfin
  set Ψ : Submodule ℂ (Y → ℂ) := Submodule.span ℂ (Set.range F) with hΨ
  haveI : FiniteDimensional ℂ Ψ := hfin
  have hc : ∀ ψ ∈ Ψ, Continuous ψ := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; exact hF i
    | zero => exact continuous_const
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  obtain ⟨t, ht⟩ := exists_finset_separating Ψ
  choose N hNc hNn using fun y : Y => exists_compact_mem_nhds y
  have hΩ : IsCompact (⋃ y ∈ t, N y) := t.isCompact_biUnion fun y _ => hNc y
  set Ω : Set Y := ⋃ y ∈ t, N y with hΩdef
  refine ⟨Ω, hΩ, fun y₀ => ?_⟩
  haveI : IsFiniteMeasure (ν.restrict Ω) := ⟨by simpa using hΩ.measure_lt_top⟩
  have hm : ∀ ψ ∈ Ψ, MemLp ψ 2 (ν.restrict Ω) := by
    intro ψ hψ
    obtain ⟨B, hB⟩ := hΩ.exists_bound_of_continuousOn (hc ψ hψ).continuousOn
    refine MemLp.of_bound (hc ψ hψ).aestronglyMeasurable B ?_
    have hmeas : MeasurableSet Ω := hΩ.measurableSet
    exact (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall hB)
  have hinj : ∀ ψ ∈ Ψ, ψ =ᵐ[ν.restrict Ω] 0 → ψ = 0 := by
    intro ψ hψ h0
    refine ht ψ hψ fun y hy => ?_
    have hsub : interior (N y) ⊆ Ω := interior_subset.trans (Set.subset_biUnion_of_mem (u := N) hy)
    have h1 : ψ =ᵐ[ν.restrict (interior (N y))] 0 :=
      ae_mono (Measure.restrict_mono hsub le_rfl) h0
    have h2 := Measure.eqOn_open_of_ae_eq h1 isOpen_interior (hc ψ hψ).continuousOn
      continuousOn_const
    exact h2 (mem_interior_iff_mem_nhds.2 (hNn y))
  obtain ⟨C, hC⟩ := bound_of_injective (ν.restrict Ω) Ψ hm hinj y₀
  exact ⟨C, fun x => hC (F x) (Submodule.subset_span ⟨x, rfl⟩)⟩

end GlobalTheory.CompanionTheory.InterpLoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantIntertwinesDual
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG.Intertw

variable {n : ℕ}

theorem exp_mem (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s : ℝ) :
    NormedSpace.exp ((s : ℂ) • X) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose]
  have h : ((s : ℂ) • X)ᴴ = -((s : ℂ) • X) := by
    rw [conjTranspose_smul, hX]
    simp
  have hc : Commute ((s : ℂ) • X) (-((s : ℂ) • X)) := (Commute.refl _).neg_right
  rw [h, ← Matrix.exp_add_of_commute _ _ hc]
  simp

theorem sum_single {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → V) (a b : Fin n) (c : ℂ) :
    ∑ x, ∑ y, (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ) x y • F x y = c • F a b := by
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    rw [Matrix.single_apply, if_neg (fun hh => hy hh.2.symm), zero_smul]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Matrix.single_apply, if_neg (fun hh => hx hh.1.symm), zero_smul]
  · simp

theorem single_conjT (a b : Fin n) (c : ℂ) :
    (Matrix.single a b c : Matrix (Fin n) (Fin n) ℂ)ᴴ = Matrix.single b a (star c) := by
  ext i j
  simp only [conjTranspose_apply, Matrix.single_apply]
  by_cases h : a = j ∧ b = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
    simp

theorem single_neg' (a b : Fin n) (c : ℂ) :
    (Matrix.single a b (-c) : Matrix (Fin n) (Fin n) ℂ) = -Matrix.single a b c := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem family_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V] (F : Fin n → Fin n → V)
    (h : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∑ a, ∑ b, X a b • F a b = 0) (a b : Fin n) : F a b = 0 := by
  have h1 : (Matrix.single a b (1 : ℂ) - Matrix.single b a 1)ᴴ = -(Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    rw [conjTranspose_sub, single_conjT, single_conjT, star_one, neg_sub]
  have h2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
      -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
    rw [conjTranspose_add, single_conjT, single_conjT, Complex.star_def, Complex.conj_I, single_neg', single_neg', neg_add,
      add_comm]
  have m1 := h _ h1
  have m2 := h _ h2
  simp only [Matrix.sub_apply, Matrix.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_single, one_smul] at m1 m2
  have m3 : F a b + F b a = 0 := by
    have := congrArg (fun v => (-Complex.I) • v) m2
    simpa [smul_add, smul_smul] using this
  have m4 : (2 : ℂ) • F a b = 0 := by
    rw [two_smul]
    calc F a b + F a b = (F a b - F b a) + (F a b + F b a) := by abel
      _ = 0 := by rw [m1, m3, add_zero]
  exact (smul_eq_zero.1 m4).resolve_left two_ne_zero

theorem intertwines : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (Kf : Fin n → Fin n → Module.End ℂ V), IsDerivK σ Kf →
    ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G →
    ∀ t ∈ invA σ E, ∀ a b ξ, t (G a b ξ) = Kf a b (t ξ) := by
  intro n V _ _ σ Kf hK E G hG t ht a b ξ
  refine sub_eq_zero.1 (family_eq_zero (fun a b => t (G a b ξ) - Kf a b (t ξ)) (fun X hX => ?_) a b)
  let γ : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun s => ⟨NormedSpace.exp ((s : ℂ) • X), exp_mem X hX s⟩
  have h1 := hG.2 X γ hX (fun _ => rfl) ξ
  obtain ⟨S, _, hS, _, _, hd⟩ := hK.2 (t ξ)
  have h2 := hd X γ (fun _ => rfl) (t ξ) hS
  let tL : (E.V →L[ℂ] ℂ) →L[ℂ] V := LinearMap.toContinuousLinearMap t
  have h3 : HasDerivAt (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) (tL (∑ a, ∑ b, X a b • G a b ξ)) 0 :=
    (tL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
  have h4 : (fun s : ℝ => tL (ξ ∘L E.ρ (γ s)⁻¹)) = fun s : ℝ => σ (γ s) (t ξ) := by
    funext s
    exact ht (γ s) ξ
  rw [h4] at h3
  have h5 := h3.unique h2
  have h6 : tL (∑ a, ∑ b, X a b • G a b ξ) = ∑ a, ∑ b, X a b • t (G a b ξ) := by
    simp only [map_sum, map_smul]
    rfl
  rw [h6] at h5
  simp only [smul_sub, Finset.sum_sub_distrib, h5, sub_self]

end GlobalTheory.CompanionTheory.RealCountG.Intertw
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaOfLinearReductive
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.IwaGen

theorem exp_mem_unitaryGroup {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) :
    NormedSpace.exp X ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (NormedSpace.exp X)ᴴ * NormedSpace.exp X = 1
  rw [← Matrix.exp_conjTranspose, hX]
  exact (Matrix.exp_neg X ▸ Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp X)))

theorem frame {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ h : Fin n → ℝ, Antitone h ∧
      U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ ∈ 𝔤 ∧
      ∀ Y ∈ 𝔤, Yᴴ = Y → (U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ) * Y = Y * (U * Matrix.diagonal (fun i => (h i : ℂ)) * Uᴴ) →
        (Uᴴ * Y * U).IsDiag := by
  obtain ⟨𝔞, hle, hH, hC, hM⟩ := GlobalTheory.T.exists_maximal_abelian_hermitian 𝔤
  obtain ⟨U₀, hU₀, hD⟩ := GlobalTheory.T.commuting_hermitian_simultaneous_diag (𝔞 : Set (Matrix (Fin n) (Fin n) ℂ)) hH hC
  obtain ⟨H, hHa, hreg⟩ := GlobalTheory.T.exists_regular_element_abelian 𝔞 U₀
  have hU₀' : U₀ * U₀ᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU₀
  have hU₀'' : U₀ᴴ * U₀ = 1 := Matrix.mem_unitaryGroup_iff'.1 hU₀
  let d : Fin n → ℝ := fun i => ((U₀ᴴ * H * U₀) i i).re
  have hdd : Matrix.diagonal (fun i => (d i : ℂ)) = U₀ᴴ * H * U₀ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have : star ((U₀ᴴ * H * U₀) i i) = (U₀ᴴ * H * U₀) i i := by
        have h2 : (U₀ᴴ * H * U₀)ᴴ = U₀ᴴ * H * U₀ := by
          simp [Matrix.conjTranspose_mul, hH H hHa, Matrix.mul_assoc]
        exact congrFun (congrFun h2 i) i
      have h3 := Complex.conj_eq_iff_real.1 this
      obtain ⟨r, hr⟩ := h3
      simp [d, hr]
    · simp [Matrix.diagonal_apply_ne _ hij, hD H hHa hij]
  have hHd : U₀ * Matrix.diagonal (fun i => (d i : ℂ)) * U₀ᴴ = H := by
    rw [hdd]
    calc U₀ * (U₀ᴴ * H * U₀) * U₀ᴴ = (U₀ * U₀ᴴ) * H * (U₀ * U₀ᴴ) := by simp only [Matrix.mul_assoc]
      _ = H := by rw [hU₀']; simp
  obtain ⟨U, hU, h, hanti, heq, hdiag⟩ := GlobalTheory.T.antitone_diagonal_conjugate U₀ d hU₀
  refine ⟨U, hU, h, hanti, ?_, ?_⟩
  · rw [heq, hHd]; exact hle hHa
  · intro Y hY hYs hcomm
    rw [heq, hHd] at hcomm
    apply hdiag
    refine hD Y (hM Y hY hYs fun A hA => ?_)
    exact GlobalTheory.T.centralizer_regular_commutes U₀ H A Y hU₀ (hD H hHa) (hD A hA) (fun i j hij => hreg i j hij A hA) hcomm

theorem alg {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (hs : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤)
    (hb : ∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧
      (Uᴴ * B * U).BlockTriangular id := by
  obtain ⟨U, hU, h, hanti, hd, hreg⟩ := frame 𝔤
  have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have cj : ∀ Z : Matrix (Fin n) (Fin n) ℂ, U * (Uᴴ * Z * U) * Uᴴ = Z := fun Z => by
    calc U * (Uᴴ * Z * U) * Uᴴ = (U * Uᴴ) * Z * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [h1]; simp
  have cj' : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Uᴴ * (U * Z * Uᴴ) * U = Z := fun Z => by
    calc Uᴴ * (U * Z * Uᴴ) * U = (Uᴴ * U) * Z * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [h2]; simp
  let φ : (Matrix (Fin n) (Fin n) ℂ) →ₗ[ℝ] (Matrix (Fin n) (Fin n) ℂ) :=
    { toFun := fun Z => U * Z * Uᴴ
      map_add' := fun a b => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r a => by simp }
  let 𝔥 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤.comap φ
  have mem : ∀ Z, Z ∈ 𝔥 ↔ U * Z * Uᴴ ∈ 𝔤 := fun Z => Iff.rfl
  have mem' : ∀ Z ∈ 𝔤, Uᴴ * Z * U ∈ 𝔥 := fun Z hZ => by rw [mem, cj]; exact hZ
  have mulc : ∀ P Q : Matrix (Fin n) (Fin n) ℂ, (U * P * Uᴴ) * (U * Q * Uᴴ) = U * (P * Q) * Uᴴ := fun P Q => by
    calc (U * P * Uᴴ) * (U * Q * Uᴴ) = U * P * (Uᴴ * U) * Q * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp [Matrix.mul_assoc]
  have hs' : ∀ Z ∈ 𝔥, Zᴴ ∈ 𝔥 := fun Z hZ => by
    have := hs _ ((mem Z).1 hZ)
    rw [mem]
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using this
  have hb' : ∀ P ∈ 𝔥, ∀ Q ∈ 𝔥, P * Q - Q * P ∈ 𝔥 := fun P hP Q hQ => by
    have := hb _ ((mem P).1 hP) _ ((mem Q).1 hQ)
    rw [mulc, mulc] at this
    rw [mem, Matrix.mul_sub, Matrix.sub_mul]
    exact this
  have hreg' : ∀ Y ∈ 𝔥, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y = Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag := by
    intro Y hY hYs hc
    have := hreg _ ((mem Y).1 hY) (by simp [Matrix.conjTranspose_mul, hYs, Matrix.mul_assoc]) (by rw [mulc, mulc, hc])
    rwa [cj'] at this
  refine ⟨U, hU, fun X hX => ?_⟩
  obtain ⟨A, hA, B, hB, hAB, hAs, hBt⟩ := GlobalTheory.T.exists_skewHermitian_add_blockTriangular 𝔥 h hanti (GlobalTheory.T.lie_algebra_function_calculus 𝔥 h ((mem _).2 hd) hb') hs' hreg' _ (mem' X hX)
  refine ⟨U * A * Uᴴ, (mem _).1 hA, U * B * Uᴴ, (mem _).1 hB, ?_, ?_, ?_⟩
  · rw [← Matrix.add_mul, ← Matrix.mul_add, ← hAB, cj]
  · simp [Matrix.conjTranspose_mul, hAs, Matrix.mul_assoc]
  · rwa [cj']

theorem iwaOn_of_isLinRed : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G → PositivityTheory.Tls2.Iua.IwaOn G := by
  intro n G hG
  obtain ⟨𝔤, hiff, hV⟩ := GlobalTheory.T.lie_algebra_of_exp_local hG
  obtain ⟨hs, hb⟩ := GlobalTheory.T.lie_algebra_star_closed_bracket hG 𝔤 hiff
  obtain ⟨U, hU, hdec⟩ := alg 𝔤 hs hb
  have hexp : ∀ X ∈ 𝔤, NormedSpace.exp X ∈ G := fun X hX => by
    simpa using (hiff X).1 hX 1
  let 𝔨 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤 ⊓
    { carrier := {X | Xᴴ = -X}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.conjTranspose_add, ha, hb, neg_add]
      zero_mem' := by simp
      smul_mem' := fun r a ha => by
        simp only [Set.mem_setOf_eq] at *
        ext i j
        have := congrFun (congrFun ha i) j
        simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this
        simp [Matrix.conjTranspose_apply, this] }
  let 𝔟 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := 𝔤 ⊓
    { carrier := {X | (Uᴴ * X * U).BlockTriangular id}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [Matrix.mul_add, Matrix.add_mul]
        exact ha.add hb
      zero_mem' := by simp [Matrix.BlockTriangular]
      smul_mem' := fun r a ha => by
        simp only [Set.mem_setOf_eq] at *
        intro i j hij
        have := ha hij
        have e : Uᴴ * (r • a) * U = r • (Uᴴ * a * U) := by simp
        rw [e, Matrix.smul_apply, this, smul_zero] }
  have hloc := GlobalTheory.T.local_exp_product_decomposition hG 𝔤 𝔨 𝔟 hiff hV inf_le_left inf_le_left (fun X hX => by
    obtain ⟨A, hA, B, hB, hAB, hAs, hBt⟩ := hdec X hX
    rw [hAB]
    exact Submodule.add_mem_sup ⟨hA, hAs⟩ ⟨hB, hBt⟩)
  obtain h := GlobalTheory.T.cartan_local_to_global hG U hU (by
    filter_upwards [hloc] with g hg hgG
    obtain ⟨X, hX, Y, hY, rfl⟩ := hg hgG
    exact ⟨_, ⟨hexp X hX.1, exp_mem_unitaryGroup X hX.2⟩, _, hexp Y hY.1, rfl, GlobalTheory.T.exp_block_triangular U Y hU hY.2⟩)
  exact ⟨U, hU, h⟩

end GlobalTheory.CompanionTheory.IwaGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityDropZeroBlocksStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_drop_zero_blocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL k) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm y hd π = jm (fun a => y (o a)) hd' π := by
  first | exact @GlobalTheory.CompanionTheory.FineProd.JmDrop.jm_drop | exact GlobalTheory.CompanionTheory.FineProd.JmDrop.jm_drop | (intros; apply GlobalTheory.CompanionTheory.FineProd.JmDrop.jm_drop <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOrderEmbeddingStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_order_embedding : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (zz : Fin n → IrrGL k) (σ : Fin p ↪o Fin n) (c : Fin n → ℕ), (∀ a, c (σ a) = (zz (σ a)).1) → (∀ j, j ∉ Set.range σ → c j = 0) → ∀ (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N), jm (fun a => zz (σ a)) hz π ≠ 0 → jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (jac f π) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.WordProd.RowCell.jhMult_row | exact GlobalTheory.CompanionTheory.WordProd.RowCell.jhMult_row | (intros; apply GlobalTheory.CompanionTheory.WordProd.RowCell.jhMult_row <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisLeftStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_mayer_vietoris_left : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₂) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → U₁ (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun U₁ (capU V S) (capU W S) (h₁ S) (h₂ S)) → E.Kun U₁ (capU V ∅) (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_r | exact GlobalTheory.CompanionTheory.KunGlue.glue_r | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_r <;> assumption)
end

