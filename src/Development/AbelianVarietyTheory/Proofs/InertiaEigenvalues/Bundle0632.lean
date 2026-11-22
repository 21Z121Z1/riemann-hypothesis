import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0626
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0409
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0597
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0196
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0622
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionsLowAndPullback
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.LowLevel

section Series

variable {LL M : Type} [Field LL] [AddCommGroup M] [Module LL M]

theorem conv_one (f : ℤ → M) : conv (1 : PowerSeries LL) f = f := by
  funext k
  unfold conv
  rw [finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [PowerSeries.coeff_one, hj]

theorem mem_latSpan {ι : Type} (e : ι → ℤ → M) (x : ι) : e x ∈ latSpan (LL := LL) e :=
  Submodule.subset_span ⟨1, x, (conv_one _).symm⟩

theorem neg_eq_zero {ι : Type} {e : ι → ℤ → M} {D : Submodule LL M} (h : Std D (latSpan e))
    (x : ι) (k : ℤ) (hk : k < 0) : e x k = 0 :=
  ((h _).1 (mem_latSpan e x)).2 k hk

theorem span_const {ι : Type} {e : ι → ℤ → M} {D : Submodule LL M} (h : Std D (latSpan e)) :
    Submodule.span LL (Set.range fun x => e x 0) = D := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ((h _).1 (mem_latSpan e x)).1 0
  · intro d hd
    have key : ∀ f ∈ latSpan (LL := LL) e, f 0 ∈ Submodule.span LL (Set.range fun x => e x 0) := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨a, x, rfl⟩ := hf
        unfold conv
        rw [finsum_eq_single _ 0]
        · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, ?_⟩)
          simp
        · intro j hj
          rw [neg_eq_zero h x _ (by omega), smul_zero]
      | zero => exact Submodule.zero_mem _
      | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
      | smul c f _ hf => exact Submodule.smul_mem _ c hf
    have hmem : (Pi.single (0 : ℤ) d : ℤ → M) ∈ latSpan (LL := LL) e := by
      refine (h _).2 ⟨fun k => ?_, fun k hk => Pi.single_eq_of_ne hk.ne _⟩
      by_cases hk : k = 0
      · subst hk
        simpa using hd
      · rw [Pi.single_eq_of_ne hk]
        exact D.zero_mem
    simpa using key _ hmem

theorem span_const_map {M' ι : Type} [AddCommGroup M'] [Module LL M'] {e : ι → ℤ → M}
    {D : Submodule LL M} (h : Std D (latSpan e)) (L : M →ₗ[LL] M') (g : ι → M')
    (hg : ∀ x, g x = L (e x 0)) : Submodule.span LL (Set.range g) = D.map L := by
  rw [← span_const h, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext x
  exact hg x

theorem conv_low (w : PowerSeries LL) (k : ℕ) (f : ℤ → M) (hf : ∀ j < 0, f j = 0) (j : ℤ)
    (hj : j < k) : conv ((PowerSeries.X * w) ^ k) f j = 0 := by
  unfold conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m < k
  · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
  · rw [hf _ (by omega), smul_zero]

theorem conv_lead (w : PowerSeries LL) (k : ℕ) (f : ℤ → M) (hf : ∀ j < 0, f j = 0) :
    conv ((PowerSeries.X * w) ^ k) f k = PowerSeries.constantCoeff w ^ k • f 0 := by
  unfold conv
  rw [finsum_eq_single _ k]
  · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl]
    simp
  · intro m hmk
    by_cases hm : m < k
    · rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
    · rw [hf _ (by omega), smul_zero]

theorem pullback_span {M' ι : Type} [AddCommGroup M'] [Module LL M'] {P : ι → ℕ → Prop}
    (y : ∀ x k, P x k → ι) (lN : ι → ℤ → M') (e e' : ι → ℤ → M) {D D' : Submodule LL M}
    (L : M →ₗ[LL] M') (φ : M →ₗ[LL] M) (c : LL) (q : PowerSeries LL)
    (hq : ∃ w, IsUnit w ∧ q = PowerSeries.X * w)
    (hN : ∀ x k, lN x k = L (e x k)) (hmem : ∀ x k, e x k ∈ D) (hS : Std D' (latSpan e'))
    (hφ : ∀ x k hk j, e (y x k hk) j = conv (q ^ k) (fun j => c ^ j • φ (e' x j)) j)
    (hsurj : Set.SurjOn φ D' D) (hex : ∀ x, ∃ k, P x k) :
    (∀ x k hk (j : ℤ), lN (y x k hk) j ∈ D.map L ∧ (j < k → lN (y x k hk) j = 0)) ∧
      Submodule.span LL {z | ∃ x k hk, z = lN (y x k hk) (k : ℕ)} = D.map L := by
  obtain ⟨w, hw, rfl⟩ := hq
  have hm : ∀ x k, lN x k ∈ D.map L := fun x k => by
    rw [hN]
    exact Submodule.mem_map_of_mem (hmem x k)
  have hg0 : ∀ x, ∀ j < (0 : ℤ), c ^ j • φ (e' x j) = 0 := by
    intro x j hj
    rw [neg_eq_zero hS x j hj, map_zero, smul_zero]
  have hc : PowerSeries.constantCoeff w ≠ 0 := (hw.map PowerSeries.constantCoeff).ne_zero
  refine ⟨fun x k hk j => ⟨hm _ _, fun hj => ?_⟩, le_antisymm ?_ ?_⟩
  · rw [hN, hφ, conv_low w k _ (hg0 x) j hj, map_zero]
  · rw [Submodule.span_le]
    rintro _ ⟨x, k, hk, rfl⟩
    exact hm _ _
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨d', hd', rfl⟩ := hsurj hd
    have hd'' : d' ∈ Submodule.span LL (Set.range fun x => e' x 0) := by
      rw [span_const hS]
      exact hd'
    clear hd hd'
    induction hd'' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      obtain ⟨k, hk⟩ := hex x
      have h2 : L (φ (e' x 0)) = (PowerSeries.constantCoeff w ^ k)⁻¹ • lN (y x k hk) k := by
        rw [hN, hφ, conv_lead w k _ (hg0 x), map_smul, inv_smul_smul₀ (pow_ne_zero _ hc)]
        simp only [zpow_zero, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, k, hk, rfl⟩)
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c ha

theorem low_span {M' ι : Type} [AddCommGroup M'] [Module LL M'] (a : ι → ι) (lN : ι → ℤ → M')
    (e : ι → ℤ → M) {D : Submodule LL M} (L : M →ₗ[LL] M') (q : PowerSeries LL) (hq : q = 1)
    (ha : ∀ x k, lN (a x) k = conv q (lN x) k)
    (hN : ∀ x k, lN x k = L (e x k)) (hS : Std D (latSpan e)) :
    (∀ x (k : ℤ), lN (a x) k ∈ D.map L ∧ (k < 0 → lN x k = 0)) ∧
      Submodule.span LL (Set.range fun x => lN (a x) 0) = D.map L := by
  subst hq
  simp only [conv_one] at ha
  refine ⟨fun x k => ⟨?_, fun hk => ?_⟩, span_const_map hS L _ fun x => by rw [ha, hN]⟩
  · rw [hN]
    exact Submodule.mem_map_of_mem (((hS _).1 (mem_latSpan e _)).1 k)
  · rw [hN, neg_eq_zero hS x k hk, map_zero]

end Series

theorem exists_primitive {L : Type} [Field L] {l : ℕ} (hl : l.Prime) {ζ : L} {m : ℕ}
    (h : ζ ^ (l ^ m) = 1) : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).1 (orderOf_dvd_of_pow_eq_one h)
  exact ⟨j, hj ▸ IsPrimitiveRoot.orderOf ζ⟩

theorem pow_pow_pred {L : Type} [Field L] {l s : ℕ} (hs : 1 ≤ s) {ζ : L}
    (h : IsPrimitiveRoot ζ (l ^ s)) : (ζ ^ l) ^ (l ^ (s - 1)) = 1 := by
  rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hs]
  exact h.pow_eq_one

set_option maxHeartbeats 1000000 in

theorem expansions_low_and_pullback : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ (i : Let K) (ζ : ↥LL.1), (∃ m : ℕ, ζ ^ (((D.loc l).PD K).p ^ m) = 1) → PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 → (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : AA K LL) • x) k ∈ (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) ∧ (k < 0 → W.levN T i ζ x k = 0)) ∧ Submodule.span ↥LL.1 (Set.range fun x : ↥(W.N T) => W.levN T i ζ ((letE i : AA K LL) • x) 0) = (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))) ∧ ∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → (∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), W.levN T i ζ ⟨_, hk⟩ j ∈ (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧ Submodule.span ↥LL.1 {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T), w = W.levN T i ζ ⟨_, hk⟩ k} = (Di (HW l) h T i).map (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  intro D HW F Cm l _ K s LL h W E C T hT
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hstd : ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ (s - 1)) = 1 →
      Std (Di (HW l) h T i) (latSpan (ex C h T i ζ)) := GlobalTheory.T.wachLattice_expansions_std_below_level D HW F Cm l K s LL h T hT
  refine ⟨fun i ζ hζ hX => ?_, fun i ζ τ hτ => ?_⟩
  · have hm : ζ ^ (l ^ hζ.choose) = 1 := by
      have := hζ.choose_spec
      rwa [show ((D.loc l).PD K).p ^ hζ.choose = l ^ hζ.choose from congrArg (· ^ _) hp] at this
    have hl := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ (exists_primitive Fact.out hm)
    exact low_span (fun x => (letE i : AA K LL) • x) (W.levN T i ζ) (ex C h T i ζ) _
      (W.lev i ζ (letE i)) hl.2.1 (W.levN_smul T i ζ (letE i))
      ((C.C K s LL h).tie.levN_eq T i ζ) (hstd i ζ (hl.2.2.2.2.1.1 hX))
  · have hprim : IsPrimitiveRoot ζ (l ^ s) :=
      ((GlobalTheory.NL.Points.points D HW l K s LL h).2.1 i ζ τ hτ).1
    have hl := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hprim⟩
    have hφ : ∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ),
        ex C h T i ζ ⟨_, hk⟩ j = conv ((W.lev i ζ W.Q) ^ k) (fun j => (l : ↥LL.1) ^ j •
          φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) (ex C h T (i - 1) (ζ ^ l) x j)) j := by
      intro x k hk j
      have h1 := (C.C K s LL h).tie.levB_φ T hT i ζ ⟨s, by rw [hp]; exact hprim⟩ x k hk j
      rw [map_pow, hp] at h1
      exact h1
    exact pullback_span (P := fun (x : ↥(W.N T)) k => W.Q ^ k • W.φD T x ∈ W.N T)
      (fun _ _ hk => ⟨_, hk⟩) (W.levN T i ζ) (ex C h T i ζ) (ex C h T (i - 1) (ζ ^ l)) _ _ _ _
      (hl.2.2.2.1 hprim).1 ((C.C K s LL h).tie.levN_eq T i ζ) ((C.C K s LL h).tie.levB_mem T i ζ)
      (hstd (i - 1) (ζ ^ l) (pow_pow_pred h.1 hprim)) hφ
      ((GlobalTheory.T.crystallineFrobenius_bijOn_letters_directSum D HW l K s LL h T hT).1 i).surjOn (fun x => W.N_φ T x x.2)

end GlobalTheory.NL.LowLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAtAll
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAll

theorem split_equiv {G L V₀ V₁ V₂ : Type} [Group G] [Field L] [AddCommGroup V₀] [Module L V₀]
    [AddCommGroup V₁] [Module L V₁] [AddCommGroup V₂] [Module L V₂]
    (ρ₀ : Representation L G V₀) (ρ₁ : Representation L G V₁) (ρ₂ : Representation L G V₂)
    (ι : V₀ →ₗ[L] V₁) (π : V₁ →ₗ[L] V₂) (hι : ∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x))
    (hi : Function.Injective ι) (hk : LinearMap.range ι = LinearMap.ker π)
    (s : V₂ →ₗ[L] V₁) (hs : ∀ g x, s (ρ₂ g x) = ρ₁ g (s x)) (hps : ∀ x, π (s x) = x) :
    ∃ e : V₁ ≃ₗ[L] (V₀ × V₂), ∀ g v, e (ρ₁ g v) = (ρ₀ g (e v).1, ρ₂ g (e v).2) := by
  let f : V₀ × V₂ →ₗ[L] V₁ := ι.coprod s
  have hf : ∀ a b, f (a, b) = ι a + s b := fun a b => rfl
  have hπι : ∀ a, π (ι a) = 0 := fun a => by
    have : ι a ∈ LinearMap.ker π := hk ▸ LinearMap.mem_range_self ι a
    exact this
  have hbij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨a, b⟩ h
      rw [hf] at h
      have hb : b = 0 := by
        have := congrArg π h
        rwa [map_add, hπι, hps, zero_add, map_zero] at this
      subst hb
      rw [map_zero, add_zero] at h
      have ha : a = 0 := hi (by rw [h, map_zero])
      rw [ha]; rfl
    · intro z
      have hz : z - s (π z) ∈ LinearMap.range ι := by
        rw [hk, LinearMap.mem_ker, map_sub, hps, sub_self]
      obtain ⟨a, ha⟩ := hz
      exact ⟨(a, π z), by rw [hf, ha, sub_add_cancel]⟩
  let e := (LinearEquiv.ofBijective f hbij).symm
  refine ⟨e, fun g v => ?_⟩
  apply (LinearEquiv.ofBijective f hbij).injective
  change f (e (ρ₁ g v)) = f (ρ₀ g (e v).1, ρ₂ g (e v).2)
  have h1 : ∀ w, f (e w) = w := fun w => (LinearEquiv.ofBijective f hbij).apply_symm_apply w
  rw [h1, hf, hι, hs, ← map_add, ← hf]
  have : ((e v).1, (e v).2) = e v := rfl
  rw [this, h1]

theorem fontaineAt_all : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l),
    Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL) := by
  intro D l _ K LL
  have T := D.locT l
  unfold Formalism.MainNotions.TruncatedSeriesCountingIdentities.FontaineAt
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A₀ A₁ A₂ ι π hι hπ hi hs hk
    refine ⟨?_, ?_⟩
    · intro h1
      have c0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL A₀.V A₀.ρ A₁.V A₁.ρ ι hι).1 hi h1
      have c2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ A₂.V A₂.ρ π hπ).2 hs h1).1
      have d1 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ h1).1
      obtain ⟨-, -, hm⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) T K LL A₀.V A₀.ρ A₁.V A₁.ρ
        A₂.V A₂.ρ ι π hι hπ hi hs hk d1
      exact ⟨c0, c2, fun τ a => (hm τ a).2.1⟩
    · rintro ⟨s, hs', hps⟩ h0 h2
      obtain ⟨e, he⟩ := split_equiv A₀.ρ A₁.ρ A₂.ρ ι π hι hi hk s hs' hps
      exact ((GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l (D.loc l) (D.locA l) T K LL A₁.V A₁.ρ A₀.V A₀.ρ
        A₂.V A₂.ρ e he).2.1).2 ⟨h0, h2⟩
  · intro A A' χ htw hχ hA
    exact GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) T K LL A.V A.ρ A'.V A'.ρ χ htw hχ hA
  · intro A A' P hD hA
    exact GlobalTheory.DualOne.isCrys_of_isDual1 l (D.loc l) (D.locA l) T K LL A.V A.ρ A'.V A'.ρ P hD hA
  · intro A hA
    exact (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL A.V A.ρ hA).1

end GlobalTheory.FontaineAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCoboundaryFrobeniusFixed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.PhiFix

theorem frob_actB {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K]
    [Algebra O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (x : TW (OB l O) T) :
    TWmap (frobOB l O) T (actB (sQ l) T g x) = actB (sQ l) T g (TWmap (frobOB l O) T x) := by
  have hB : ∀ r : OB l O, frobOB l O (galOB O (sQ l g) r) = galOB O (sQ l g) (frobOB l O r) := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul o β =>
      simp only [frobOB, galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact congrArg (fun y : Per.Bcris l => o ⊗ₜ[ℤ_[l]] y) ((GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.1 _ β)
    | add r s hr hs => rw [map_add (galOB O (sQ l g)), map_add (frobOB l O), map_add (frobOB l O), map_add (galOB O (sQ l g)), hr, hs]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [actB, TWmap, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, hB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem frob_fixed_coboundary : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, ∀ b, R.IsPotential y b → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → TWmap (frobOB l O) T (actB (sQ l) T g b - b) = actB (sQ l) T g b - b := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hyY b hb g hg
  obtain ⟨hy, m₀, σ, b₀, hm₀, -, hconn, hb₀, rfl⟩ := hb
  haveI : CompleteSpace K := GlobalTheory.T.completeSpace_of_finite_padicInt_unitBall l O K
  obtain ⟨d, hd⟩ := GlobalTheory.T.phi_sub_sub_mem_xi_of_monodromy_eq O K l e a ι η H D y hyY σ.1 hconn
  obtain ⟨-, hall⟩ := GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I
  obtain ⟨hφ, huniq, hfrobv, -, -⟩ := hall R.jB R.cmp
  have hσφ : D.phi σ.1 ∈ D.MMl := GlobalTheory.T.phi_mem_invertedLattice O K l e a ι η H D σ.1 σ.2
  have hyφ : D.phi y ∈ D.MMl := GlobalTheory.T.phi_mem_invertedPrime_lattice_of_mem_eisensteinInvariants O K l e a ι η H D y hyY

  have hv1 := IsCrisVal.sub t ϖ (hfrobv _ _ hb₀) hb₀
  have hv2 := GlobalTheory.T.tensorBcris_value_frobenius_of_inverse_eisenstein_twist l a e O K t ϖ ι η H D T R.jB y hyY hy hyφ
  have hw : phiW t ϖ D.toPhiMod (phiW t ϖ D.toPhiMod m₀) - phiW t ϖ D.toPhiMod m₀ =
      phiW t ϖ D.toPhiMod (toW t ϖ D.toPhiMod ⟨y, hy⟩) := by rw [← hm₀, map_sub]
  rw [hw] at hv1
  have hb0 := huniq _ _ _ hv1 hv2
  have hs := hφ σ ⟨D.phi σ.1, hσφ⟩ rfl
  have hmem : D.xi d ∈ D.MMl := by
    rw [← hd]; exact sub_mem (sub_mem hσφ σ.2) hyφ
  have hkey : TWmap (frobOB l O) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₀) -
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₀) = R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi d, hmem⟩) := by
    have he : (⟨D.xi d, hmem⟩ : D.MMl) = ⟨D.phi σ.1, hσφ⟩ - σ - ⟨D.phi y, hyφ⟩ := Subtype.ext (by
      simp only [Submodule.coe_sub]; exact hd.symm)
    rw [he, map_sub, map_sub, map_sub, map_sub, map_sub, ← hs, ← hb0]
    abel
  have hfix := R.horiz g hg d hmem
  rw [← hkey, map_sub] at hfix
  rw [map_sub, frob_actB]
  exact sub_eq_sub_iff_sub_eq_sub.1 hfix

end GlobalTheory.BKGal.PhiFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisDividedTaylorExpansionFrobeniusBasis
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysGal

open GlobalTheory.Prism

theorem span_range_tr {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) {P P' : Obj l R}
    (f : GlobalTheory.Prism.Hom P P') : Submodule.span P'.A (Set.range (E.tr f)) = ⊤ := by
  have hu := (E.tr_bc f (E.M P' ⧸ Submodule.span P'.A (Set.range (E.tr f))) 0).unique
    (y₁ := Submodule.mkQ _) (y₂ := 0)
    (fun x => by
      show Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.subset_span ⟨x, rfl⟩)
    (fun x => rfl)
  rw [eq_top_iff]
  intro x _
  have := LinearMap.congr_fun hu x
  rwa [Submodule.mkQ_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this

theorem mem_span_tr {l : ℕ} {R : Type} [CommRing R] (E : FCrys l R) {P P' : Obj l R}
    (f : GlobalTheory.Prism.Hom P P') {O ι : Type} [Fintype ι] (oE : O → FHom E E) (b : ι → E.M P)
    (hgen : ∀ x : E.M P, ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → P.A),
      x = ∑ j, ∑ q, s j q • (oE (c j q)).u P (b j)) (x : E.M P') :
    x ∈ Submodule.span P'.A (Set.range fun p : O × ι => (oE p.1).u P' (E.tr f (b p.2))) := by
  have hx : x ∈ Submodule.span P'.A (Set.range (E.tr f)) := (span_range_tr E f) ▸ Submodule.mem_top
  refine (Submodule.span_le.2 ?_) hx
  rintro _ ⟨z, rfl⟩
  obtain ⟨N, c, s, hz⟩ := hgen z
  rw [hz, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [map_smulₛₗ, ← (oE (c j q)).u_tr]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(c j q, j), rfl⟩)

theorem exists_rep {A M O ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] [DecidableEq ι]
    (v : O → ι → M) (x : ι → M) (hx : ∀ j, x j ∈ Submodule.span A (Set.range fun p : O × ι => v p.1 p.2)) :
    ∃ (Q : Type) (_ : Fintype Q) (c : ι → ι → Q → O) (y : ι → ι → Q → A),
      ∀ j, x j = ∑ i, ∑ q, y i j q • v (c i j q) i := by
  choose n w gg hgg using fun j => Submodule.mem_span_set'.1 (hx j)
  choose pc hpc using fun j k => (gg j k).2
  refine ⟨Σ j', Fin (n j'), inferInstance, fun i j q => (pc q.1 q.2).1,
    fun i j q => if q.1 = j then (if (pc q.1 q.2).2 = i then w q.1 q.2 else 0) else 0, fun j => ?_⟩
  rw [Finset.sum_comm]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j (fun j' _ hj' => by simp [hj']) (by simp)]
  rw [← hgg j]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [if_true, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ]
  rw [← hpc j k]

theorem conv_comb {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (g : ↥(GK (ϖ.field a))) {Q : Type} [Fintype Q] (c : Q → O) (z : Q → Per.Acris l)
    (F : Q → ℕ → (ZMod a → S O K e)) (G : ℕ → (ZMod a → S O K e)) (hG : ∀ k, G k = ∑ q, c q • F q k)
    (r : ℕ) (hconv : ∀ q, ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      (1 : O) ⊗ₜ[ℤ_[l]] z q - ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (F q k))
    (w : OCr l O) (hw : w = ∑ q, c q ⊗ₜ[ℤ_[l]] z q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l O) ^ r ∣
      w - ∑ k ∈ Finset.range n, ϖ.muDiv a O g k * ϖ.iC t K (G k) := by
  subst hw
  choose n₀ hn₀ using hconv
  refine ⟨Finset.univ.sup n₀, fun n hn => ?_⟩
  simp_rw [hG, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro q _
  rw [← Finset.smul_sum, show c q ⊗ₜ[ℤ_[l]] z q = c q • ((1 : O) ⊗ₜ[ℤ_[l]] z q) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], ← smul_sub, Algebra.smul_def]
  exact Dvd.dvd.mul_left (hn₀ q n (le_trans (Finset.le_sup (Finset.mem_univ q)) hn)) _

theorem comb_S {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {a e : ℕ} {Q : Type} [Fintype Q] (c : Q → O) (w : ZMod a → Q → K⟦X⟧⟦X⟧)
    (G : ℕ → ZMod a → S O K e) (F : Q → ℕ → ZMod a → S O K e)
    (hG : ∀ k τ, (G k τ : K⟦X⟧) = (X : K⟦X⟧) ^ k * ((k.factorial : K⟦X⟧) * coeff k (∑ q, c q • w τ q)))
    (hF : ∀ q k τ, (F q k τ : K⟦X⟧) = (X : K⟦X⟧) ^ k * ((k.factorial : K⟦X⟧) * coeff k (w τ q))) :
    ∀ k, G k = ∑ q, c q • F q k := by
  intro k
  funext τ
  apply Subtype.ext
  rw [hG, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum, map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Pi.smul_apply, SetLike.val_smul, hF, PowerSeries.coeff_smul, mul_smul_comm, mul_smul_comm]

set_option maxHeartbeats 1000000 in

theorem galois_taylor_basis : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (hS : ∀ (τ : ZMod a) (j : ι) (k : ℕ) (i : ι), (X : (↥LL.1)⟦X⟧) ^ k * (P.mxInv τ *ᵥ (P.nabla ^ k) (P.phi (bas j)) τ) i ∈ S (↥(OL LL)) (↥LL.1) e) (g : ↥(GK (ϖ.field a))), ∃ Γ, (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)).IsLMat (g : GQ l) g Γ ∧ ∀ (i j : ι) (r : ℕ), ∃ n₀ : ℕ, ∀ n ≥ n₀, (l : OCr l ↥(OL LL)) ^ r ∣ toOCr l ↥(OL LL) (Γ i j) - ∑ k ∈ Finset.range n, ϖ.muDiv a ↥(OL LL) g k * ϖ.iC (thetaW a LL) ↥LL.1 (fun τ => ⟨_, hS τ j k i⟩) := by
  intro BS l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I hBK hS g
  letI := zlLat (resF T (ϖ.field a))
  obtain ⟨E, jA, hR, hIm⟩ := hBK
  have hO : ∀ c : ↥(OL LL), ∃ u : FHom E E, ∀ x, jA (u.u (ainfObj (ϖ.field a)) x) =
      (OfCrystal.mulZ (resF T (ϖ.field a)) c).lTensor (WCb l) (jA x) := fun c => by
    obtain ⟨u, hu, -⟩ := (BS l (ϖ.field a) (ainfObj (ϖ.field a)) (ainfId (ϖ.field a)) hR.ainf).2 _ _ _ _ E E jA jA hR hR
      (OfCrystal.mulZ (resF T (ϖ.field a)) c) fun g x => (((resF T (ϖ.field a)).actT g).map_smul c x).symm
    exact ⟨u, hu⟩
  choose oE hoE using hO
  obtain ⟨b, hb, hgen⟩ := GlobalTheory.T.breuilKisinPrism_crystal_basis_and_span l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE
  obtain ⟨sh, φ₂, hsh, hφC, hφsh⟩ := GlobalTheory.TaylorShift.shift_frob_exists l ↥LL.1
  obtain ⟨PP, S₀, p₀, p₁, δ, κ, κ₀, hPPI, hδ, hκ₀, hκp, hκφ, hSS, -, hev⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ hl2 sh φ₂ hsh hφC hφsh
  obtain ⟨Q, _, c, y, hε⟩ := GlobalTheory.CrysGal.exists_rep (A := PP.A)
    (fun c i => (oE c).u PP (E.tr p₀ (b i))) (fun j => E.tr p₁ (b j))
    (fun j => GlobalTheory.CrysGal.mem_span_tr E p₀ oE b hgen _)
  have hF := GlobalTheory.T.crystal_changeOfBasis_frobenius_compat l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb sh φ₂ hsh hφC PP p₀ p₁ κ hPPI hκp hκφ Q c y hε
  have hD := GlobalTheory.T.prismCrystal_changeOfBasis_constantCoeff_eq_one l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP S₀ p₀ p₁ δ κ κ₀ hδ hκ₀ (fun τ x => (hκp τ x).1) Q c y hε
  have hK := GlobalTheory.T.frobeniusStratification_coeff_eq_connection_pow ↥(OL LL) ↥LL.1 l e a ι P sh φ₂ hsh hφC hφsh _ hD hF
  obtain ⟨Cr, eC, h, hCrI, heCφ, heCh⟩ := GlobalTheory.AcrisPrism.main l (ϖ.field a)
  have hev' := hev Cr eC h hCrI heCφ heCh g
  obtain ⟨ev, hevs⟩ := hev'
  have hG := GlobalTheory.T.galoisMatrix_eq_crystal_changeOfBasis_value l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P (resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) E jA hR hIm oE hoE b hb PP p₀ p₁ Q c y hε Cr eC h heCh g ev hevs.1 hevs.2.1
  obtain ⟨Γ, hΓ, hΓeq⟩ := hG
  have hconv := hevs.2.2
  refine ⟨Γ, hΓ, fun i j r => ?_⟩
  have hG := GlobalTheory.CrysGal.comb_S (e := e) (c i j) (fun τ q => κ τ (y i j q))
    (fun k τ => ⟨_, hS τ j k i⟩) (fun q k τ => ⟨_, hSS τ (y i j q) k⟩)
    (fun k τ => (congrArg ((X : (↥LL.1)⟦X⟧) ^ k * ·) (hK τ k i j)).symm) (fun q k τ => rfl)
  exact GlobalTheory.CrysGal.conv_comb (thetaW a LL) ϖ g (c i j) (fun q => eC (ev.f (y i j q)))
    (fun q k τ => ⟨_, hSS τ (y i j q) k⟩) (fun k τ => ⟨_, hS τ j k i⟩) hG r (fun q => hconv (y i j q) r)
    _ (hΓeq i j)

end GlobalTheory.CrysGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H0VanishOfZeroMultiplicityStatement
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_vanish_of_zero_multiplicity : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), IsDR (P.PD K) ρ → multV (P.PD K) ρ τ 0 = 0 → H0V ρ = ⊥ := by
  first | exact @GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero | exact GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero | (intros; apply GlobalTheory.InvJump.h0V_eq_bot_of_multV_zero <;> assumption)
end

