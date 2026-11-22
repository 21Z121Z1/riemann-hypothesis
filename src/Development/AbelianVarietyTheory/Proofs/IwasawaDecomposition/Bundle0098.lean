import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0280
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalRingCardinality.Lemmas
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyIntegral
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Pst.KummerIndep

variable {l : ℕ} [Fact l.Prime]

theorem eventually_integral (x : ℚ_[l]) :
    ∀ᶠ N : ℕ in Filter.atTop, ∃ y : ℤ_[l], (y : ℚ_[l]) = (l : ℚ_[l]) ^ N * x := by
  have h : Filter.Tendsto (fun N : ℕ => ‖(l : ℚ_[l]) ^ N * x‖) Filter.atTop (nhds 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (Padic.norm_p_lt_one (p := l))).mul_const x).norm
    simpa using this
  filter_upwards [h.eventually (ge_mem_nhds zero_lt_one)] with N hN
  exact ⟨⟨_, hN⟩, rfl⟩

theorem exists_root (P : LocPrime l) (μ : ℕ → Om l) (d : GQ l → ℤ_[l])
    (hμ : ∀ m : ℕ, μ m ^ (l ^ m) = ((l + 1 : ℕ) : Om l))
    (hd : ∀ (g : GQ l) (m : ℕ), g (μ m) = P.ζQ m ^ (PadicInt.toZModPow m (d g)).val * μ m)
    (α β r : ℤ_[l])
    (h : ∀ g : GQ l, (α : ℚ_[l]) * (kummer P g : ℚ_[l]) + β * (d g : ℚ_[l]) =
      r * ((P.χQ g : ℚ_[l]) - 1))
    (k A B : ℕ) (hA : PadicInt.toZModPow k α = A) (hB : PadicInt.toZModPow k β = B) :
    ∃ q : ℚ_[l], q ^ (l ^ k) = (l : ℚ_[l]) ^ A * ((l + 1 : ℕ) : ℚ_[l]) ^ B := by
  have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : IsGalois ℚ_[l] (Om l) := {}
  obtain ⟨S, hS⟩ : ∃ S : ℕ, PadicInt.toZModPow k (-r) = S := ⟨_, (ZMod.natCast_zmod_val _).symm⟩
  obtain ⟨x, hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ_[l])
    (lRoot l k ^ A * μ k ^ B * P.ζQ k ^ S)).2 fun g => by
      have hx : ‖(P.χQ g : ℚ_[l])‖ ≤ 1 := by
        obtain ⟨a, ha, -⟩ := P.χQ_cyc g 0 1 (by simp)
        have e : (P.χQ g : ℚ_[l]) = ((P.χQ g : ℚ_[l]) - a) + a := by ring
        rw [e]
        refine (Padic.nonarchimedean _ _).trans (max_le (by simpa using ha) ?_)
        exact_mod_cast Padic.norm_int_le_one (p := l) (a : ℤ)
      let x : ℤ_[l] := ⟨P.χQ g, hx⟩
      obtain ⟨a, ha, hg⟩ := P.χQ_cyc g k (P.ζQ k) (isPrimitiveRoot_zeta P k).pow_eq_one
      have hxa : PadicInt.toZModPow k x = a := by
        rw [← sub_eq_zero, ← map_natCast (PadicInt.toZModPow k), ← map_sub, ← RingHom.mem_ker,
          PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
        exact ha
      have h1 : α * kummer P g + β * d g + (-r) * x = -r := by
        apply Subtype.ext
        have e : (x : ℚ_[l]) = P.χQ g := rfl
        have := h g
        push_cast
        rw [e]
        linear_combination this
      have h2 := congrArg (PadicInt.toZModPow k) h1
      rw [map_add, map_add, map_mul, map_mul, map_mul, hA, hB, hS, hxa] at h2
      have h3 : P.ζQ k ^ ((PadicInt.toZModPow k (kummer P g)).val * A +
          (PadicInt.toZModPow k (d g)).val * B + a * S) = P.ζQ k ^ S := by
        rw [zeta_pow_eq_iff]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        linear_combination h2
      rw [map_mul, map_mul, map_pow, map_pow, map_pow, hg, isKummer_kummer P g k, hd g k, ← h3]
      simp only [mul_pow, ← pow_mul, pow_add]
      ring
  refine ⟨x, (algebraMap ℚ_[l] (Om l)).injective ?_⟩
  rw [map_pow, hx, mul_pow, mul_pow, pow_right_comm (lRoot l k), pow_right_comm (μ k),
    pow_right_comm (P.ζQ k), lRoot_pow, hμ, (isPrimitiveRoot_zeta P k).pow_eq_one]
  simp

theorem norm_succ : ‖((l + 1 : ℕ) : ℚ_[l])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  simp

theorem dvd_of_root {k A B : ℕ} {q : ℚ_[l]}
    (h : q ^ (l ^ k) = (l : ℚ_[l]) ^ A * ((l + 1 : ℕ) : ℚ_[l]) ^ B) : l ^ k ∣ A := by
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hl1 : ((l + 1 : ℕ) : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hv : ((l + 1 : ℕ) : ℚ_[l]).valuation = 0 := by
    rw [Padic.valuation_natCast, padicValNat.eq_zero_of_not_dvd]
    · simp
    · rw [Nat.dvd_add_right dvd_rfl]
      exact (Fact.out : l.Prime).not_dvd_one
  have h2 := congrArg Padic.valuation h
  rw [Padic.valuation_mul (pow_ne_zero _ hl) (pow_ne_zero _ hl1), Padic.valuation_pow,
    Padic.valuation_pow, Padic.valuation_pow, Padic.valuation_p, hv, mul_one, mul_zero,
    add_zero] at h2
  exact Int.natCast_dvd_natCast.mp ⟨_, h2.symm⟩

theorem not_forall_root {B : ℕ} (hB : B ≠ 0)
    (h : ∀ k, ∃ q : ℚ_[l], q ^ (l ^ k) = ((l + 1 : ℕ) : ℚ_[l]) ^ B) : False := by
  have hp : l.Prime := Fact.out
  have key : ((((l + 1) ^ B) ^ (l - 1) : ℕ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    cases n with
    | zero =>
      have : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
      exact Subsingleton.elim _ _
    | succ k =>
      obtain ⟨q, hq⟩ := h k
      have hn : ‖q‖ ≤ 1 := by
        have := congrArg norm hq
        rw [norm_pow, norm_pow, norm_succ, one_pow] at this
        exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).mp this.le
      let y : ℤ_[l] := ⟨q, hn⟩
      have hy : y ^ (l ^ k) = (((l + 1) ^ B : ℕ) : ℤ_[l]) := by
        apply Subtype.ext
        have e : (y : ℚ_[l]) = q := rfl
        push_cast at hq ⊢
        rw [e, hq]
      have hu : IsUnit y := by
        rw [← isUnit_pow_iff (pow_ne_zero k hp.ne_zero), hy, PadicInt.isUnit_iff]
        have := norm_succ (l := l)
        rw [Nat.cast_pow, norm_pow]
        have e : ‖((l + 1 : ℕ) : ℤ_[l])‖ = 1 := by
          rw [PadicInt.norm_def, PadicInt.coe_natCast, this]
        rw [e, one_pow]
      obtain ⟨u, hu⟩ := hu.map (PadicInt.toZModPow (k + 1))
      have h1 := congrArg Units.val (ZMod.pow_totient u)
      rw [Nat.totient_prime_pow_succ hp, Units.val_pow_eq_pow_val, hu, pow_mul, ← map_pow, hy,
        ← map_pow] at h1
      rw [Nat.cast_pow, h1]
      simp
  have h2 : ((l + 1) ^ B) ^ (l - 1) = 1 := Nat.cast_injective key
  have := hp.two_le
  rw [← pow_mul, Nat.pow_eq_one] at h2
  rcases h2 with h2 | h2
  · omega
  · rcases Nat.mul_eq_zero.mp h2 with h3 | h3 <;> omega

theorem kummer_indep (l : ℕ) [Fact l.Prime] (P : LocPrime l) (μ : ℕ → Om l) (d : GQ l → ℤ_[l])
    (hμ : ∀ m : ℕ, μ m ^ (l ^ m) = ((l + 1 : ℕ) : Om l))
    (hd : ∀ (g : GQ l) (m : ℕ), g (μ m) = P.ζQ m ^ (PadicInt.toZModPow m (d g)).val * μ m)
    (α β r : ℚ_[l])
    (h : ∀ g : GQ l, α * (kummer P g : ℚ_[l]) + β * (d g : ℚ_[l]) =
      r * ((P.χQ g : ℚ_[l]) - 1)) : α = 0 ∧ β = 0 := by
  have hp : l.Prime := Fact.out
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hα : α = 0 := by
    obtain ⟨N, ⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := ((eventually_integral α).and
      ((eventually_integral β).and (eventually_integral r))).exists
    have h0 : a = 0 := by
      refine PadicInt.ext_of_toZModPow.mp fun k => ?_
      have : NeZero (l ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
      obtain ⟨q, hq⟩ := exists_root P μ d hμ hd a b c
        (fun g => by rw [ha, hb, hc]; linear_combination (l : ℚ_[l]) ^ N * h g) k _ _
        (ZMod.natCast_zmod_val _).symm (ZMod.natCast_zmod_val _).symm
      rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow k a), map_zero, ZMod.natCast_eq_zero_iff]
      exact dvd_of_root hq
    rw [h0] at ha
    exact (mul_eq_zero.mp ha.symm).resolve_left (pow_ne_zero _ hl)
  refine ⟨hα, by_contra fun hβ => ?_⟩
  obtain ⟨N, c, hc⟩ := (eventually_integral (r / β)).exists
  refine not_forall_root (l := l) (B := l ^ N) (pow_ne_zero _ hp.ne_zero) fun k => ?_
  have := exists_root P μ d hμ hd 0 ((l ^ N : ℕ) : ℤ_[l]) c (fun g => by
    have h1 := h g
    rw [hα] at h1
    rw [hc]
    push_cast
    field_simp
    linear_combination (l : ℚ_[l]) ^ N * h1) k 0 (l ^ N) (by simp) (map_natCast _ _)
  simpa only [pow_zero, one_mul] using this

end GlobalTheory.Pst.KummerIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexExtension
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.RamRational

section General

variable {K V W M N ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] {σ : K →+* ℂ}

theorem exists_complex_extension [Fintype ι] (e : V →ₛₗ[σ] M) (b : Module.Basis ι K V)
    (hli : LinearIndependent ℂ (fun i => e (b i))) (g : V →ₛₗ[σ] N) :
    ∃ G : M →ₗ[ℂ] N, ∀ x, G (e x) = g x := by
  obtain ⟨G, hG⟩ := LinearMap.exists_extend
    ((Finsupp.linearCombination ℂ (fun i => g (b i))) ∘ₗ hli.repr)
  have hb : ∀ i, G (e (b i)) = g (b i) := by
    intro i
    have hm : e (b i) ∈ Submodule.span ℂ (Set.range (fun i => e (b i))) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h1 := LinearMap.congr_fun hG ⟨e (b i), hm⟩
    have h2 : hli.repr ⟨e (b i), hm⟩ = Finsupp.single i 1 := hli.repr_eq_single i _ rfl
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, h2,
      Finsupp.linearCombination_single, one_smul] at h1
    exact h1
  refine ⟨G, fun x => ?_⟩
  rw [← b.sum_repr x]
  simp only [map_sum, LinearMap.map_smulₛₗ, hb, RingHom.id_apply]

theorem mem_span_of_kernel [Fintype ι] {J : Type} [Fintype J] (e : V →ₛₗ[σ] M)
    (b : Module.Basis ι K V) (hli : LinearIndependent ℂ (fun i => e (b i)))
    (F : J → M →ₗ[ℂ] M) (hF : ∀ j x, ∃ y, e y = F j (e x)) (m : M)
    (hm : m ∈ Submodule.span ℂ (Set.range (fun i => e (b i)))) (h0 : ∀ j, F j m = 0) :
    m ∈ Submodule.span ℂ (e '' {x | ∀ j, F j (e x) = 0}) := by
  classical
  have hinj := inj_of_li σ e b hli
  let f : J → V →ₗ[K] V := fun j => descend e e hinj (F j) (hF j)
  have hf : ∀ j x, e (f j x) = F j (e x) := fun j x => descend_spec e e hinj (F j) (hF j) x
  let g : V →ₗ[K] (J → V) := LinearMap.pi f
  obtain ⟨s, hs⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨h, hh⟩ := LinearMap.exists_extend s
  have hg : ∀ x, g (h (g x)) = g x := by
    intro x
    have h1 : h (g x) = s (g.rangeRestrict x) := LinearMap.congr_fun hh (g.rangeRestrict x)
    have h2 := LinearMap.congr_fun hs (g.rangeRestrict x)
    rw [h1]
    exact congrArg Subtype.val h2
  choose H hH using fun j : J =>
    exists_complex_extension e b hli (e.comp (h ∘ₗ LinearMap.single K (fun _ : J => V) j))
  let P : M →ₗ[ℂ] M := LinearMap.id - ∑ j, H j ∘ₗ F j
  have hP : ∀ x, P (e x) = e (x - h (g x)) := by
    intro x
    have h1 : g x = ∑ j, Pi.single j (f j x) := (Finset.univ_sum_single (g x)).symm
    rw [h1]
    simp only [P, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, map_sub, map_sum, ← hf, hH, LinearMap.coe_single]
  have hPm : P m = m := by
    simp [P, LinearMap.sum_apply, h0]
  rw [← hPm]
  have hle : Submodule.span ℂ (Set.range (fun i => e (b i))) ≤
      (Submodule.span ℂ (e '' {x | ∀ j, F j (e x) = 0})).comap P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Submodule.subset_span ⟨b i - h (g (b i)), fun j => ?_, (hP _).symm⟩
    have h1 : g (b i - h (g (b i))) = 0 := by rw [map_sub, hg, sub_self]
    have h2 : f j (b i - h (g (b i))) = 0 := congrFun h1 j
    rw [← hf, h2, map_zero]
  exact hle hm

theorem preserves_of_span (e : V →ₛₗ[σ] M) (S : Set V) (hS : Submodule.span K S = ⊤)
    (F : M →ₗ[ℂ] M) (hF : ∀ x ∈ S, ∃ y, e y = F (e x)) (x : V) : ∃ y, e y = F (e x) := by
  have hx : x ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact hF x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by simp [ha, hc]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c • a, by simp [LinearMap.map_smulₛₗ, ha]⟩

end General

theorem span_ramSub {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL]
    {embLL : LL →+* ℂ} {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
    {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
    (M : MemberForms LL embLL Pl Tau hc C A P) :
    Submodule.span ℂ (M.emb 0 '' (M.ramSub : Set (M.lat 0).V)) = A.Mram := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro m hm
    have hsp : Submodule.span ℂ (Set.range (fun a => M.emb 0 ((M.lat 0).b a))) = A.Mu0 :=
      (M.emb_basis 0).2.trans M.Fi_zero
    have hrho : ∀ v a x, ∃ y, M.emb 0 y = A.rhoT v a (M.emb 0 x) := fun v a =>
      preserves_of_span (M.emb 0) _ (M.lat_good 0).2.2 (A.rhoT v a) (fun x hx => by
        obtain ⟨y, -, hy⟩ := M.rhoT_lat v a x hx
        exact ⟨y, hy⟩)
    have hNm : ∀ v x, ∃ y, M.emb 0 y = A.Nm v (M.emb 0 x) := by
      intro v x
      choose y hy using fun a => hrho v a x
      exact ⟨∑ a, y a, by simp only [map_sum, hy, ColumnsAtT.Nm, LinearMap.sum_apply]⟩
    have hall : ∀ x, M.emb 0 x ∈ A.Mu0 := by
      intro x
      rw [← hsp, ← (M.lat 0).b.sum_repr x, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h := mem_span_of_kernel (M.emb 0) (M.lat 0).b (M.emb_basis 0).1 A.Nm hNm m
      (hsp ▸ hm.1) (fun v => (Submodule.mem_iInf _).1 hm.2 v)
    refine Submodule.span_mono (Set.image_mono ?_) h
    intro x hx
    exact ⟨hall x, (Submodule.mem_iInf _).2 hx⟩

theorem span_ramSub_cols : ∀ (B : Base) (C : Cols B) (u : B.Word),
    Submodule.span ℂ ((C.fm u).emb 0 '' ((C.fm u).ramSub : Set ((C.fm u).lat 0).V)) =
      (C.mem u).A.Mram :=
  fun _ C u => span_ramSub (C.fm u)

end GlobalTheory.RamRational
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGlobalMatrixApproximationModIntegral
section
noncomputable section

namespace GlobalTheory.GlobApx

open Formalism.MainNotions.G

theorem mulVec_mem_colSpan {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (w : Fin k → R) :
    g.mulVec (fun j => algebraMap R K (w j)) ∈ colSpan R g := by
  have : g.mulVec (fun j => algebraMap R K (w j)) = ∑ j, w j • fun i => g i j := by
    funext i
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem exists_pow_smul_ge {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π) {k : ℕ} (g : Matrix (Fin k) (Fin k) K) :
    ∃ a : ℕ, ∀ N, a ≤ N → ∃ g0 : Matrix (Fin k) (Fin k) R,
      algebraMap R K π ^ N • g = g0.map (algebraMap R K) := by
  obtain ⟨a, g0, h⟩ := GlobalTheory.GO.TupApx.exists_pow_smul (K := K) hπ g
  refine ⟨a, fun N hN => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨π ^ d • g0, ?_⟩
  rw [pow_add, mul_comm, mul_smul, h]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_pow]

theorem exists_glob_approx : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (W Q : ι → Type) [∀ q, CommRing (W q)] [∀ q, IsDomain (W q)] [∀ q, IsDiscreteValuationRing (W q)] [∀ q, Field (Q q)] [∀ q, Algebra (W q) (Q q)] [∀ q, IsFractionRing (W q) (Q q)] {F : Type} [Field F] (f : ∀ q, F →+* Q q) (π : ∀ q, W q), (∀ q, Irreducible (π q)) → ∀ (t : F), (∀ q, f q t = algebraMap (W q) (Q q) (π q)) → (∀ (y : ∀ q, W q) (N : ℕ), ∃ x : F, ∀ q, ∃ z : W q, f q x = algebraMap (W q) (Q q) (y q + π q ^ N * z)) → ∀ {n : ℕ} (g : ∀ q, Matrix (Fin n) (Fin n) (Q q)), (∀ q, IsUnit (g q).det) → ∀ (q0 : ι), ∃ (B : Matrix (Fin n) (Fin n) F) (u : Matrix (Fin n) (Fin n) (W q0)), IsUnit u.det ∧ B.map (f q0) = g q0 * u.map (algebraMap (W q0) (Q q0)) ∧ ∀ q, q ≠ q0 → ∀ c, (fun i => f q (B i c)) ∈ Formalism.MainNotions.G.colSpan (W q) (g q) := by
  intro ι _ _ W Q _ _ _ _ _ _ F _ f π hπ t ht hd n g hg q0
  have hp0 : ∀ q, algebraMap (W q) (Q q) (π q) ≠ 0 := fun q =>
    (map_ne_zero_iff _ (IsFractionRing.injective (W q) (Q q))).2 (hπ q).ne_zero
  choose a ha using fun q => exists_pow_smul_ge (hπ q) (g q)
  choose b hb using fun q => exists_pow_smul_ge (hπ q) (g q)⁻¹
  set M := Finset.univ.sup (fun q => a q + b q) with hMdef
  have hM : ∀ q, a q ≤ M ∧ b q ≤ M := fun q => by
    have := Finset.le_sup (f := fun q => a q + b q) (Finset.mem_univ q)
    constructor <;> omega
  choose G hG using fun q => ha q M (hM q).1
  choose H hH using fun q => hb q M (hM q).2
  choose x hx using fun i j => hd (Pi.single (M := W) q0 (G q0 i j)) (2 * M + 1)
  choose z hz using hx
  have hB : ∀ q i j, f q ((t ^ M)⁻¹ * x i j) = (algebraMap (W q) (Q q) (π q) ^ M)⁻¹ *
      (algebraMap (W q) (Q q) (Pi.single (M := W) q0 (G q0 i j) q) +
        algebraMap (W q) (Q q) (π q) ^ (2 * M + 1) * algebraMap (W q) (Q q) (z i j q)) := by
    intro q i j
    rw [map_mul, map_inv₀, map_pow, ht, hz, map_add, map_mul, map_pow]
  refine ⟨Matrix.of fun i j => (t ^ M)⁻¹ * x i j, 1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0), ?_, ?_, ?_⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    have hr : IsLocalRing.residue (W q0) (π q0) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]; exact (hπ q0).not_isUnit
    have : (IsLocalRing.residue (W q0)).mapMatrix (1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0)) = 1 := by
      rw [map_add, map_one]
      have : (IsLocalRing.residue (W q0)).mapMatrix (π q0 • (H q0 * Matrix.of fun i j => z i j q0)) = 0 := by
        ext i j; simp [hr]
      rw [this, add_zero]
    rw [this]; simp
  · have e1 : (1 + π q0 • (H q0 * Matrix.of fun i j => z i j q0)).map (algebraMap (W q0) (Q q0)) =
        1 + algebraMap (W q0) (Q q0) (π q0) • ((H q0).map (algebraMap (W q0) (Q q0)) *
          (Matrix.of fun i j => z i j q0).map (algebraMap (W q0) (Q q0))) := by
      rw [← Matrix.map_mul]
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
        Matrix.one_apply, apply_ite (algebraMap (W q0) (Q q0)), map_one, map_zero]
    rw [e1, ← hH q0, mul_add, mul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (hg q0), Matrix.one_mul]
    ext i j
    have h2 := congrFun (congrFun (hG q0) i) j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at h2
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hB, Pi.single_eq_same, ← h2]
    have := hp0 q0
    field_simp
    ring
  · intro q hq c
    set zc : Fin n → W q := fun i => z i c q
    have hv : (fun i => f q ((Matrix.of fun i j => (t ^ M)⁻¹ * x i j) i c)) =
        (g q).mulVec (fun j => algebraMap (W q) (Q q) ((π q • (H q).mulVec zc) j)) := by
      have e2 : (fun j => algebraMap (W q) (Q q) ((π q • (H q).mulVec zc) j)) =
          algebraMap (W q) (Q q) (π q) • ((H q).map (algebraMap (W q) (Q q))).mulVec
            (fun j => algebraMap (W q) (Q q) (zc j)) := by
        funext j
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [e2, ← hH q, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (hg q), Matrix.one_mulVec]
      funext i
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      rw [hB, Pi.single_eq_of_ne hq, map_zero, zero_add]
      have := hp0 q
      field_simp
      ring
    rw [hv]
    exact mulVec_mem_colSpan _ _

end GlobalTheory.GlobApx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveCharacterOfIsCyclic
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory

open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem (L : Type*) [Field L] [NumberField L] {p : ℕ}
    (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  have hP : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨Q, hQm, hQ⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (Ideal.span {(p : ℤ)})
      (by
        intro x hx
        rw [RingHom.mem_ker, (algebraMap ℤ (𝓞 L)).injective_int.eq_iff' (map_zero _)] at hx
        simp [hx])
  have hmem : ((p : ℕ) : 𝓞 L) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 L)) := hQ ▸ Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQm.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : (p : ℤ) ∈ (⊥ : Ideal (𝓞 L)).comap (algebraMap ℤ (𝓞 L)) := by simpa using hmem
  rw [Ideal.mem_comap, Ideal.mem_bot] at this
  exact hp.ne_zero (by simpa using this)

open NumberField IsDedekindDomain in
private theorem exists_injective_units_zmod_hom_units_complex (p : ℕ) [Fact p.Prime] :
    ∃ f : (ZMod p)ˣ →* ℂˣ, Function.Injective f := by
  set n := Nat.card (ZMod p)ˣ
  have hn : NeZero n := ⟨Nat.card_pos.ne'⟩
  have hc : Nat.card (ZMod p)ˣ = Nat.card (rootsOfUnity n ℂ) := by
    rw [Complex.card_rootsOfUnity]
  exact ⟨(rootsOfUnity n ℂ).subtype.comp (mulEquivOfCyclicCardEq hc).toMonoidHom,
    Subtype.val_injective.comp (mulEquivOfCyclicCardEq hc).injective⟩

open NumberField IsDedekindDomain in
open Classical in

theorem _root_.GlobalTheory.nonempty_piBar_and_omg :
    ∀ (R : _root_.Formalism.BasicNotions.Ranks) (H : _root_.Formalism.BasicNotions.Host R), Nonempty (_root_.Formalism.L2.Host.PiBar H) ∧ Nonempty (_root_.Formalism.L2.Host.Omg H) := by
  intro R H
  refine ⟨⟨⟨fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose,
    fun k => (_root_.GlobalTheory.exists_heightOneSpectrum_natCast_mem H.K (H.g_prime k)).choose_spec⟩⟩, ?_⟩
  have : ∀ k : Fin 2, ∃ f : (ZMod (H.g k))ˣ →* ℂˣ, Function.Injective f := fun k =>
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    exists_injective_units_zmod_hom_units_complex (H.g k)
  exact ⟨⟨fun k => (this k).choose, fun k => (this k).choose_spec⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBasisAdapted
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem exists_orthonormalBasis_adapted (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (I : Type) [Fintype I] [DecidableEq I] (p : I → Submodule ℂ E)
    (htop : (⨆ i, p i) = ⊤) (horth : ∀ i j, i ≠ j → p i ⟂ p j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (ty : Fin (Module.finrank ℂ E) → I),
      ∀ i, Submodule.span ℂ (b '' {σ | ty σ = i}) = p i := by
  classical
  have hV : OrthogonalFamily ℂ (fun i => p i) (fun i => (p i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise (fun i j h => horth i j h)
  have hint : DirectSum.IsInternal p :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top p).2 ⟨hV.independent, htop⟩
  let v : ∀ i, OrthonormalBasis (Fin (Module.finrank ℂ (p i))) ℂ (p i) :=
    fun i => stdOrthonormalBasis ℂ (p i)
  let c := hint.collectedOrthonormalBasis hV v
  have hc : ∀ a : (Σ i, Fin (Module.finrank ℂ (p i))), c a = (v a.1 a.2 : E) := by
    intro a
    simp [c, DirectSum.IsInternal.collectedOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe]
  have hcard : Fintype.card (Σ i, Fin (Module.finrank ℂ (p i))) = Module.finrank ℂ E :=
    (Module.finrank_eq_card_basis c.toBasis).symm
  let e : (Σ i, Fin (Module.finrank ℂ (p i))) ≃ Fin (Module.finrank ℂ E) :=
    Fintype.equivFinOfCardEq hcard
  refine ⟨c.reindex e, fun σ => (e.symm σ).1, fun i => ?_⟩
  have himg : (c.reindex e) '' {σ | (e.symm σ).1 = i}
      = (p i).subtype '' Set.range (v i).toBasis := by
    ext x
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      rw [OrthonormalBasis.reindex_apply, hc]
      simp only [Set.mem_ofPred_eq] at hσ
      generalize e.symm σ = a at hσ
      obtain ⟨j, k⟩ := a
      subst hσ
      exact ⟨v j k, ⟨k, by simp⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨e ⟨i, k⟩, by simp, ?_⟩
      rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hc]
      simp
  rw [himg, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.Mem
end

