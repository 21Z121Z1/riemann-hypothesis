import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0437
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysFrobCoord

theorem span_range_eq_top {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) :
    Submodule.span B (Set.range u) = ⊤ := by
  set S := Submodule.span B (Set.range u)
  obtain ⟨w, -, hu⟩ := h (N ⧸ S) 0
  have h1 := hu S.mkQ (fun x => by
    simpa using (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨x, rfl⟩))
  have h2 := hu 0 (fun x => by simp)
  rw [eq_top_iff]
  intro y _
  have : S.mkQ y = 0 := by rw [h1, ← h2]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 this

theorem frac_indep {A M B : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [IsDomain B]
    (d : A) (J : A →+* B) (hd : J d ≠ 0) (lam : M →+ B) (hlam : ∀ r y, lam (r • y) = J r * lam y)
    {z : LocalizedModule (Submonoid.powers d) M} {n n' : M} {k k' : ℕ} (h : IsFrac d z n k)
    (h' : IsFrac d z n' k') {b : B} (hb : lam n' = J d ^ k' * b) : lam n = J d ^ k * b := by
  unfold IsFrac at h h'
  obtain ⟨⟨_, s, rfl⟩, hs⟩ := LocalizedModule.mk_eq.1 (h.symm.trans h')
  have h2 := congrArg lam hs
  simp only [Submonoid.smul_def, hlam, map_pow, hb] at h2
  have h3 := mul_left_cancel₀ (pow_ne_zero s hd) h2
  refine mul_left_cancel₀ (pow_ne_zero k' hd) ?_
  rw [h3]; ring

theorem frac_formula {A M B : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [IsDomain B]
    (d : A) (φ : A →+* A)
    (Φ : M →ₛₗ[(algebraMap A (Localization.Away d)).comp φ] LocalizedModule (Submonoid.powers d) M)
    (J : A →+* B) (hd : J d ≠ 0) (lam : M →+ B) (hlam : ∀ r y, lam (r • y) = J r * lam y)
    (F : M →+ B) (hF : ∀ r y, F (r • y) = J (φ r) * F y) (S : Set M) (hS : Submodule.span A S = ⊤)
    (h0 : ∀ y ∈ S, ∀ n k, IsFrac d (Φ y) n k → lam n = J d ^ k * F y) (y n : M) (k : ℕ)
    (h : IsFrac d (Φ y) n k) : lam n = J d ^ k * F y := by
  have key : ∀ y ∈ Submodule.span A S, ∃ n k, IsFrac d (Φ y) n k ∧ lam n = J d ^ k * F y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, k, hn⟩ := exists_isFrac d (Φ y)
      exact ⟨n, k, hn, h0 y hy n k hn⟩
    | zero => exact ⟨0, 0, by simp [IsFrac], by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, k, hn, en⟩ := hx
      obtain ⟨m, j, hm, em⟩ := hy
      refine ⟨d ^ j • n + d ^ k • m, k + j, ?_, ?_⟩
      · unfold IsFrac at hn hm ⊢
        rw [map_add, hn, hm, LocalizedModule.mk_add_mk]
        congr 1
        exact Subtype.ext (pow_add d k j).symm
      · rw [map_add, hlam, hlam, en, em, map_add, map_pow, map_pow]; ring
    | smul r x _ hx =>
      obtain ⟨n, k, hn, en⟩ := hx
      refine ⟨φ r • n, k, ?_, ?_⟩
      · unfold IsFrac at hn ⊢
        rw [map_smulₛₗ, hn, RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk]
      · rw [hlam, hF, en]; ring
  obtain ⟨n', k', h', e'⟩ := key y (hS ▸ Submodule.mem_top)
  exact frac_indep d J hd lam hlam h h' e'

section Maps

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem frob_toAc (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem coe_toAc_eis (τ : ZMod a) : (toAc t K (eis l a e) τ : K⟦X⟧) = E K l e := by
  have hX : toAc t K X = fun _ => uIn (A O K) :=
    funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _))
  rw [eis, map_add, map_pow, hX, map_natCast]
  simp [E]

end Maps

theorem frob_in_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c _ hc PP hl p J g φ₂ hJp hJφ hφg hg lam hlam hlamtr y n k h τ i
  have hK : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := fun h => hl0 (by simpa using congrArg constantCoeff h)
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := fun h => hl1 (by simpa using congrArg constantCoeff h)
  have hE : E K l e ≠ 0 := fun h => hl0 (by
    simpa [E, NeZero.ne e] using congrArg constantCoeff h)
  have hJE : J τ (p.f (eis l a e)) = g (frob K l (E K l e)) := by
    rw [hJp, ← frob_toAc, coe_toAc_eis]
  have hJE0 : g (frob K l (E K l e)) ≠ 0 := by
    rw [map_ne_zero_iff _ hg, map_ne_zero_iff _ (frob_injective l)]; exact hE
  let lam' : EE.M PP →+ K⟦X⟧⟦X⟧ :=
    { toFun := fun y => lam y τ i, map_zero' := by simp, map_add' := by simp }
  let F : EE.M PP →+ K⟦X⟧⟦X⟧ :=
    { toFun := fun y => (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i
      map_zero' := by simp [Matrix.mulVec, dotProduct]
      map_add' := by simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib] }
  have hJl : J τ (l : PP.A) = l := map_natCast _ _
  have := frac_formula (l : PP.A) PP.D.φ (EE.Φ PP ⟨l, hl⟩) (J τ) (hJl ▸ hl2) lam'
    (fun r y => hlam r y τ i) F ?_ _ (span_range_eq_top (EE.tr_bc p)) ?_ y n k h
  · rw [hJl] at this; exact this
  · intro r y
    simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct, hlam, map_mul, hJφ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rintro _ ⟨x, rfl⟩ n k h
    obtain ⟨m', k', hm'⟩ := exists_isFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x)
    obtain ⟨r, hr⟩ := EE.Φ_nat p ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ ⟨l, hl⟩ x m' k' n k hm' h
    have h1 := congrArg (fun y => lam y τ i) hr
    simp only [hlam, map_sub, Pi.sub_apply, map_zero, Pi.zero_apply, map_pow, map_mul, hJl, hJE] at h1
    have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (mul_ne_zero hJE0 hl2)))
    rw [hlamtr, hc x m' k' hm'] at h2
    rw [hJl]
    refine mul_left_cancel₀ (pow_ne_zero k' hJE0) ?_
    change _ * lam n τ i = _
    rw [← h2]
    simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct, hlamtr, hφg,
      PhiMod.phi_apply, frobV_apply, map_mul, map_pow, map_sum, Matrix.map_apply]
    ring

end GlobalTheory.CrysFrobCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictness
section
noncomputable section

namespace GlobalTheory.DRSubQuot

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct GlobalTheory.DRFil

theorem mem_of_invariant {G K B M ι : Type} [Field K] [CommRing B] [Algebra K B] (hF : IsField B)
    [AddCommGroup M] [Module B M] [Module K M] [IsScalarTower K B M]
    (σ : G → B → B) (ρ : G → M →+ M) (hρ : ∀ g b w, ρ g (b • w) = σ g b • ρ g w)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * σ g b' = σ g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (hinv : ∀ b : B, (∀ g, σ g b = b) → ∃ c : K, algebraMap K B c = b)
    (F : ℤ → Submodule K B) (hFa : Antitone F) (h1 : (1 : B) ∉ F 1)
    (E : ℤ → AddSubgroup M) (hEa : Antitone E) (hEK : ∀ k (c : K) x, x ∈ E k → c • x ∈ E k)
    (k : ι → ℤ) (e : ι → M) (he : ∀ i, e i ∈ E (k i)) (hei : ∀ g i, ρ g (e i) = e i) (a : ℤ) (n : ℕ) :
    ∀ s : Finset ι, s.card = n → ∀ b : ι → B, (∀ i ∈ s, b i ∈ F (a - k i)) →
      (∀ g, ρ g (∑ i ∈ s, b i • e i) = ∑ i ∈ s, b i • e i) → ∑ i ∈ s, b i • e i ∈ E a := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn b hb hy
  by_cases hli : LinearIndepOn K e s
  · haveI := hF.isDomain
    haveI : Module.IsTorsionFree B M := ⟨fun r hr x y hxy => by
      obtain ⟨u, hu⟩ := hF.mul_inv_cancel hr.ne_zero
      have := congrArg (u • ·) hxy
      simpa only [smul_smul, mul_comm u r, hu, one_smul] using this⟩
    have hB := linearIndepOn_finset_iff.1
      (GlobalTheory.Per.FontaineBound.linearIndepOn_of_invariant σ ρ hρ hreg e hei s hli)
    refine (E a).sum_mem fun i hi => ?_
    obtain ⟨c, hc⟩ := hinv (b i) fun g => sub_eq_zero.1 (hB (fun j => σ g (b j) - b j) (by
      have := hy g
      simp only [map_sum, hρ, hei] at this
      simp only [sub_smul, Finset.sum_sub_distrib, this, sub_self]) i hi)
    by_cases hc0 : c = 0
    · rw [← hc, hc0, map_zero, zero_smul]
      exact (E a).zero_mem
    rw [← hc, algebraMap_smul]
    refine hEK _ _ _ (hEa ?_ (he i))
    by_contra hlt
    apply h1
    have h2 := (F _).smul_mem c⁻¹ (hb i hi)
    rw [← hc, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc0, map_one] at h2
    exact hFa (by omega) h2
  · rw [linearIndepOn_finset_iff] at hli
    push Not at hli
    obtain ⟨κ, hκ, i₀, hi₀, hκ₀⟩ := hli
    obtain ⟨i, hi, hmin⟩ := (s.filter fun j => κ j ≠ 0).exists_min_image k
      ⟨i₀, Finset.mem_filter.2 ⟨hi₀, hκ₀⟩⟩
    obtain ⟨his, hκi⟩ := Finset.mem_filter.1 hi
    have hrel : e i = - ∑ j ∈ s.erase i, ((κ i)⁻¹ * κ j) • e j := by
      rw [← Finset.add_sum_erase s _ his] at hκ
      have := congrArg ((κ i)⁻¹ • ·) hκ
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hκi, one_smul, Finset.smul_sum, smul_zero] at this
      exact eq_neg_of_add_eq_zero_left this
    have heq : ∑ j ∈ s, b j • e j = ∑ j ∈ s.erase i, (b j - ((κ i)⁻¹ * κ j) • b i) • e j := by
      rw [← Finset.add_sum_erase s _ his]
      conv_lhs => rw [hrel]
      simp only [smul_neg, Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, smul_assoc,
        smul_comm (b i)]
      abel
    rw [heq] at hy ⊢
    refine ih _ (hn ▸ Finset.card_erase_lt_of_mem his) _ rfl _ (fun j hj => ?_) hy
    have hjs := Finset.mem_of_mem_erase hj
    refine (F _).sub_mem (hb j hjs) ?_
    by_cases hj0 : κ j = 0
    · simp [hj0]
    · have := hmin j (Finset.mem_filter.2 ⟨hjs, hj0⟩)
      exact (F _).smul_mem _ (hFa (by omega) (hb i his))

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x))
include hf

theorem ext_mem_DdR {x : V ⊗[Qp] F} (hx : x ∈ DdR PD ρ) : ext Qp F f x ∈ DdR PD ρ' :=
  (mem_DdR PD _ _).2 fun g => by rw [act_ext PD ρ ρ' f hf, (mem_DdR PD _ _).1 hx]

theorem spans_of_surjective (hs : Function.Surjective f) (h : Spans PD ρ) : Spans PD ρ' := by
  intro y
  obtain ⟨a, ha⟩ := exists_mem_FilV PD (LL := LL) y
  obtain ⟨x, -, rfl⟩ := exists_ext_mem_FilV PD f hs ha
  obtain ⟨m, b, d, hd, rfl⟩ := h x
  exact ⟨m, b, fun i => ext Qp F f (d i), fun i => ext_mem_DdR PD ρ ρ' f hf (hd i), by
    simp only [map_sum, ext_mulR]⟩

theorem spans_of_injective [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    [FiniteDimensional LL V] [FiniteDimensional LL V'] (hF : IsField F)
    (hi : Function.Injective f) (h : Spans PD ρ') : Spans PD ρ := by
  have h1 : Spans PD ρ'.dual := spans_dual_of_spans PD ρ' ρ'.dual (Module.Dual.eval LL V') hF
    (fun g x y => by simp [Module.Dual.transpose_apply]) Function.bijective_id h
  have h2 : Spans PD ρ.dual := spans_of_surjective PD ρ'.dual ρ.dual f.dualMap
    (fun g x => by ext v; simp [Module.Dual.transpose_apply, hf]) (LinearMap.dualMap_surjective_of_injective hi) h1
  exact spans_dual_of_spans PD ρ.dual ρ LinearMap.id hF
    (fun g x y => by simp [Module.Dual.transpose_apply]) (Module.bijective_dual_eval LL V) h2

theorem strict_of_surjective (hF : IsField F) (hs : Function.Surjective f) (h : FilSpans PD ρ) (a : ℤ)
    (y : V' ⊗[Qp] F) (hy : y ∈ DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') a) :
    ∃ x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a, ext Qp F f x = y := by
  let φ : F →+* Module.End LL (V' ⊗[Qp] F) :=
    { toFun := fun b => mulR Qp F LL V' b
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul, tmul_add] }
  letI : Module F (V' ⊗[Qp] F) := Module.compHom _ φ
  letI : Module K (V' ⊗[Qp] F) := Module.compHom _ (algebraMap K F)
  haveI : IsScalarTower K F (V' ⊗[Qp] F) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsm : ∀ (b : F) (x : V' ⊗[Qp] F), b • x = mulR Qp F LL V' b x := fun _ _ => rfl
  obtain ⟨x, hx, rfl⟩ := exists_ext_mem_FilV PD f hs hy.2
  obtain ⟨m, k, b, d, hd, rfl⟩ := h a x hx
  have hsum : ext Qp F f (∑ i, mulR Qp F LL V (b i) (d i)) = ∑ i, b i • ext Qp F f (d i) := by
    simp only [map_sum, ext_mulR, hsm]
  have hinv := (mem_DdR PD _ _).1 hy.1
  rw [hsum] at hinv ⊢
  exact mem_of_invariant (K := K) hF (fun g b => PD.actdR g b) (fun g => (actVdR PD ρ' g).toAddMonoidHom)
    (fun g b w => by
      change actVdR PD ρ' g (mulR Qp F LL V' b w) = mulR Qp F LL V' _ (actVdR PD ρ' g w)
      rw [← sm_one_tmul, act_sm, ← sm_one_tmul]
      simp)
    (GlobalTheory.Per.FontaineBound.frac_dR PD hF) PD.invdR PD.Fil (fil_antitone PD) (one_notMem_fil_one PD)
    (fun c => ((DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) c).map (ext Qp F f)).toAddSubgroup)
    (fun c c' hc => Submodule.map_mono (inf_le_inf_left _ (FilV_antitone PD hc)))
    (by
      rintro c κ _ ⟨z, hz, rfl⟩
      refine ⟨mulR Qp F LL V (algebraMap K F κ) z, ⟨mulR_mem_DdR PD ρ κ hz.1, ?_⟩, ext_mulR f _ z⟩
      have h0 : algebraMap K F κ ∈ PD.Fil 0 := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ PD.one_mem
      have := mulR_mem_FilV PD (LL := LL) h0 hz.2
      rwa [zero_add] at this)
    k (fun i => ext Qp F f (d i)) (fun i => ⟨d i, ⟨(hd i).1, (hd i).2.1⟩, rfl⟩)
    (fun g i => (mem_DdR PD _ _).1 (ext_mem_DdR PD ρ ρ' f hf (hd i).1) g) a _ Finset.univ rfl b
    (fun i _ => (hd i).2.2) hinv

end Generic

theorem deRham_sub_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsDR (P.PD K) ρ' → IsDR (P.PD K) ρ) ∧ (Function.Surjective f → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (a : ℤ), ∀ y ∈ DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V') a, ∃ x ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' f hf
  have := K.2
  have := LL.2
  refine ⟨fun hi h => isDR_of_spans T K LL ρ (spans_of_injective (P.PD K) ρ ρ' f hf (isField_dR T) hi
    ((filSpans T K LL ρ' h).spans _)), fun hs h => ⟨isDR_of_spans T K LL ρ'
    (spans_of_surjective (P.PD K) ρ ρ' f hf hs ((filSpans T K LL ρ h).spans _)), fun a y hy => ?_⟩⟩
  exact strict_of_surjective (P.PD K) ρ ρ' f hf (isField_dR T) hs (filSpans T K LL ρ h) a y hy

end GlobalTheory.DRSubQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscBoundedFunctionIsPowerSeries
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem le_one_of_mul_pow_le_one (c : ℝ) (n : ℕ) (h : ∀ t : ℝ≥0, t < 1 → c * (t : ℝ) ^ n ≤ 1) : c ≤ 1 := by
  have ht : Filter.Tendsto (fun t : ℝ≥0 => c * (t : ℝ) ^ n) (nhdsWithin (1 : ℝ≥0) (Set.Iio 1)) (nhds (c * ((1 : ℝ≥0) : ℝ) ^ n)) :=
    ((continuous_const.mul ((NNReal.continuous_coe).pow n)).tendsto 1).mono_left nhdsWithin_le_nhds
  have : (nhdsWithin (1 : ℝ≥0) (Set.Iio 1)).NeBot := nhdsWithin_Iio_self_neBot' ⟨0, zero_lt_one⟩
  have h2 := le_of_tendsto ht (eventually_nhdsWithin_of_forall fun t (hti : t ∈ Set.Iio 1) => h t hti)
  simpa using h2

theorem disc_bdd_isSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ y : bk.DS ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : bk.DS ρ' →+* bk.DS ρ) (y' : bk.DS ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (RingHom.id bk.S) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (X : bk.S) ρ a = y := by
  intro l _ K bk ρ hρ hρ1 y hy
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  obtain ⟨a, ha1, ha2, ha3, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ hρ1
  obtain ⟨-, hk2, -, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk

  have hcont : ∀ (r : ℝ≥0), 0 < r → ∀ (b : ℕ → (bk.DS r →+ Disc l (0 : Wq l bk.a) 1)),
      (∀ n z, ‖b n z‖ * (r : ℝ) ^ n ≤ ‖z‖) → ∀ n, Continuous (b n) := by
    intro r hr b hb n
    refine AddMonoidHomClass.continuous_of_bound (b n) (((r : ℝ) ^ n)⁻¹) fun z => ?_
    have hp : (0 : ℝ) < (r : ℝ) ^ n := pow_pos (by exact_mod_cast hr) n
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    exact hb n z

  have htor : ∀ z : Disc l (0 : Wq l bk.a) 1, l • z = 0 → z = 0 := by
    intro z hz
    have h := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Wq l bk.a) (0 : Wq l bk.a) 1).2.1 z
    rw [← nsmul_eq_mul, hz, norm_zero] at h
    exact norm_eq_zero.1 (by
      have := (div_eq_zero_iff.1 h.symm).resolve_right hl0.ne'
      exact this)

  have hle : ∀ n, ‖a n y‖ ≤ 1 := by
    intro n
    refine le_one_of_mul_pow_le_one _ n fun t ht => ?_
    obtain ⟨ρ', R, y', h1, h2, h3, hR, hRy, hy'⟩ := hy t ht
    have hρ' : 0 < ρ' := hρ.trans_le h2
    obtain ⟨a', ha1', ha2', -, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ' hρ' h3
    have hRc : Continuous R := AddMonoidHomClass.continuous_of_bound R 1 fun z => (hR.norm_le z).trans (one_mul _).ge
    have e : ((a n).comp (R : bk.DS ρ' →+ bk.DS ρ)) = a' n :=
      (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ').2.2.1 _ htor _ _ ((hcont ρ hρ a ha2 n).comp hRc)
        (hcont ρ' hρ' a' ha2' n) fun x => by
          simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply]
          rw [hR.ext x, RingHom.id_apply, ha1, ha1']
    have e2 : a n y = a' n y' := by rw [← hRy, ← e]; rfl
    rw [e2]
    calc ‖a' n y'‖ * (t : ℝ) ^ n ≤ ‖a' n y'‖ * (ρ' : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ t.2 (by exact_mod_cast h1) n) (norm_nonneg _)
      _ ≤ ‖y'‖ := ha2' n y'
      _ ≤ 1 := hy'
  choose w hw using fun n => hk2 (a n y) (hle n)
  refine ⟨PowerSeries.mk w, ?_⟩
  have h0 : ‖y - toDisc l (X : bk.S) ρ (PowerSeries.mk w)‖ ≤ 0 :=
    ha3 _ 0 le_rfl fun n => by
      rw [map_sub, ha1, coeff_mk, ← hw, sub_self, norm_zero, zero_mul]
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h0)).symm

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormulaStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualExp_teichmuller_power_sum_formula : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (ι : Type) (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ℕ → ↥(K0 K)), (∀ i ∈ T, ‖(c i : Om l)‖ ≤ 1 ∧ ¬ l ∣ m i) → (∀ j ≤ e, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK (LT l) K (d j) = (frK (LT l) K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))⁻¹ * levSum (LT l) K s e T c m (d e)) := by
  first | exact @GlobalTheory.ExpImage.expStar_levSum | exact GlobalTheory.ExpImage.expStar_levSum | (intros; apply GlobalTheory.ExpImage.expStar_levSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualJumpRangeNegativeSignPlaceProof
section
noncomputable section

namespace GlobalTheory.Pass.JumpDualStep

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial TensorProduct
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem jumpDual_main : StepJumpDual := by
  intro D hD hP i r hr eta s S sg U hs hJ Xs w hw n hsg hF
  obtain ⟨hc, hj, hU⟩ := hJ w hw
  refine ⟨insert 0 ((U w).image fun b => -b - 1), ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · constructor <;> push_cast <;> omega
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨h, -, -⟩ := hU b hb
      have hs' : ((eta : ℚ) + D.R.t + 1) < s := by exact_mod_cast hs
      have hS : (0 : ℚ) ≤ S := by positivity
      have ht : (1 : ℚ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
      have he : (0 : ℚ) ≤ eta := by positivity
      have key : (b : ℚ) ≤ (eta : ℚ) + D.R.t ∧ -((s : ℚ) + S) - 1 ≤ b := by
        rcases h with ⟨h1, h2⟩ | h | h
        · have h1' : (0 : ℚ) ≤ b := by exact_mod_cast h1
          have h2' : (b : ℚ) < D.R.t := by exact_mod_cast h2
          constructor <;> linarith
        · rw [abs_le] at h; unfold cen at h
          constructor <;> linarith [h.1, h.2]
        · unfold cloud cen at h; rw [hsg] at h
          simp only [Bool.false_eq_true, if_false] at h; push_cast at h
          constructor <;> linarith [h.1, h.2]
      have k1 : b ≤ (eta : ℤ) + D.R.t := by exact_mod_cast key.1
      have k2 : -((s : ℤ) + S) - 1 ≤ b := by exact_mod_cast key.2
      constructor <;> push_cast <;> omega
  · exact (Finset.card_insert_le _ _).trans (by have := Finset.card_image_le (s := U w) (f := fun b : ℤ => -b - 1); omega)
  · intro x τ a ha
    have h1 := (GlobalTheory.JumpDual.jump_dual D hD hP i r hr Xs w hw n hF x τ a).1 ha
    refine Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-a - 1, hj x τ _ h1, by ring⟩))

end GlobalTheory.Pass.JumpDualStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallLetterTypeFunctionalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_forall_letterType_functional : ∀ {L U D F k : Type} [Field L] [Field U] [AddCommGroup D] [Module L D] (m : U →+* Module.End L D) [Field F] [Field k] [Algebra k L] [Algebra k U] [Algebra k F] [Algebra U F] [IsScalarTower k U F] [IsAlgClosed F] [FiniteDimensional k L] [Algebra.IsSeparable k L] [Module U D] [FiniteDimensional U D], (∀ (c : U) (x : D), c • x = m c x) → (∀ (c : k) (x : D), m (algebraMap k U c) x = algebraMap k L c • x) → ∀ x : D, (∀ s : L →ₐ[k] F, ∀ f ∈ GlobalTheory.Pst.LetterDim.letterHom m (s : L →+* F) (algebraMap U F), f x = 0) → x = 0 := by
  first | exact @GlobalTheory.LetterSep.eq_zero_of_forall_letterHom | exact GlobalTheory.LetterSep.eq_zero_of_forall_letterHom | (intros; apply GlobalTheory.LetterSep.eq_zero_of_forall_letterHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfIsNilpotentOfFinrankEqOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published

noncomputable section

namespace GlobalTheory.PotCrysRankOne

theorem eq_zero_of_isNilpotent_of_finrank_eq_one {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (h1 : Module.finrank k V = 1) {f : Module.End k V} (hf : IsNilpotent f) : f = 0 := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hc⟩ := hv (f v)
  obtain ⟨n, hn⟩ := hf
  have hp : ∀ m : ℕ, (f ^ m) v = c ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have h0 : c ^ n • v = 0 := by rw [← hp, hn]; rfl
  have hc0 : c = 0 := IsNilpotent.eq_zero ⟨n, (smul_eq_zero.mp h0).resolve_right hv0⟩
  ext x
  obtain ⟨a, rfl⟩ := hv x
  rw [map_smul, ← hc, hc0, zero_smul, smul_zero]; rfl

end GlobalTheory.PotCrysRankOne

theorem GlobalTheory.PotCrysRankOne.isPotCrystalline_of_deRham_character : DeRhamPotSemistable → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (μ : G E Ω →* (Qbar l)ˣ), Continuous μ → ∀ (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw → IsdRAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) → IsPotCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) := by
  intro hB E Ω _ _ _ _ _ l _ P AI hT μ hμ A O _ _ _ Bw _ hd
  obtain ⟨T⟩ := hT
  have hc : Continuous fun g : ↥(Dec (F := E) A) =>
      ((((rk1 μ).comp (Dec (F := E) A).subtype) g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) := by
    have e : (fun g : ↥(Dec (F := E) A) =>
        ((((rk1 μ).comp (Dec (F := E) A).subtype) g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) =
        fun g : ↥(Dec (F := E) A) => Matrix.diagonal fun _ : Fin 1 => ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l) := by
      funext g; rfl
    rw [e]
    exact Continuous.matrix_diagonal (continuous_pi fun _ => (Units.continuous_val.comp hμ).comp continuous_subtype_val)
  obtain ⟨LL', r', hm, hp⟩ := hB.isPstAt T Bw _ hc hd
  haveI := hp.finite
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  have h1 : Module.finrank ℂ (WDSpace P ι (Bw.repE LL' r')) = 1 := by
    rw [GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι _ LL' _ _ hp, Module.finrank_fin_fun]
  have hN : wdN P ι (Bw.repE LL' r') = 0 :=
    GlobalTheory.PotCrysRankOne.eq_zero_of_isNilpotent_of_finrank_eq_one h1 (isNilpotent_wdN P ι _)
  obtain ⟨K', hK, hcr⟩ := (GlobalTheory.PstLaws.isPotCrys_iff P _ hp).2 ((GlobalTheory.PstLaws.wdN_eq_zero_iff P _ ι).1 hN)
  exact ⟨LL', r', hm, K', hK, hcr⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobeniusStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_auxiliary_primes_prescribed_frobenius : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw), StepAB X i := by
  first | exact @GlobalTheory.ChosenPrimes.stepAB | exact GlobalTheory.ChosenPrimes.stepAB | (intros; apply GlobalTheory.ChosenPrimes.stepAB <;> assumption)
end

