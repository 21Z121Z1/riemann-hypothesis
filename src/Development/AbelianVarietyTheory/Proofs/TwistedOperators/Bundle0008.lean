import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumCosetsSmallerLevelRelIndexMul
section
namespace GlobalTheory

open QuotientGroup

theorem hasSum_comp_fst_card_mul_of_fintype {α β : Type} [Fintype β] (f : α → ℂ) (a : ℂ) (hf : HasSum f a) :
    HasSum (fun p : α × β => f p.1) ((Fintype.card β : ℂ) * a) := by
  classical
  have hdec : (fun p : α × β => f p.1) = fun p => ∑ b : β, (if p.2 = b then f p.1 else 0) := by
    funext p
    simp
  rw [hdec]
  have hterm : ∀ b ∈ (Finset.univ : Finset β),
      HasSum (fun p : α × β => if p.2 = b then f p.1 else 0) a := by
    intro b _
    have hinj : Function.Injective (fun x : α => (x, b)) := fun x y h => by
      simpa using congrArg Prod.fst h
    rw [← hinj.hasSum_iff]
    · simpa [Function.comp_def] using hf
    · intro p hp
      by_cases h : p.2 = b
      · exact absurd ⟨p.1, by ext <;> simp [h]⟩ hp
      · simp [h]
  have := hasSum_sum hterm
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this

theorem hasSum_cosets_smaller_level_relIndex_mul : ∀ {G : Type} [Group G] (K J H Γ : Subgroup G), K ≤ J → J ≤ H → H ≤ Γ → K.relIndex J ≠ 0 → ∀ (Ψ : G → ℂ) (z : ℂ), (∀ g ∈ Γ, g ∉ H → Ψ g = 0) → (∀ g ∈ Γ, ∀ k ∈ J, Ψ (g * k) = Ψ g) → HasSum (fun y : H ⧸ J.subgroupOf H => Ψ (y.out : H)) z → HasSum (fun y : Γ ⧸ K.subgroupOf Γ => Ψ (y.out : Γ)) ((K.relIndex J : ℂ) * z) := by
  intro G _ K J H Γ hKJ hJH hHΓ hidx Ψ z hvan hinv hsum
  classical

  set f : Γ ⧸ J.subgroupOf Γ → ℂ := fun x => Ψ (x.out : Γ) with hf
  have hfmk : ∀ g : Γ, f (mk g) = Ψ (g : G) := by
    intro g
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf Γ) g
    simp only [hf, hj, Subgroup.coe_mul]
    exact hinv _ g.2 _ (Subgroup.mem_subgroupOf.mp j.2)

  let ι : H ⧸ J.subgroupOf H → Γ ⧸ J.subgroupOf Γ := fun y => mk (Subgroup.inclusion hHΓ y.out)
  have hιmk : ∀ a : H, ι (mk a) = mk (Subgroup.inclusion hHΓ a) := by
    intro a
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf H) a
    show (mk (Subgroup.inclusion hHΓ (mk a : H ⧸ J.subgroupOf H).out) : Γ ⧸ J.subgroupOf Γ) = _
    rw [hj, QuotientGroup.eq]
    simp [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_subgroupOf.mp j.2
  have hιinj : Function.Injective ι := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    rw [hιmk, hιmk, QuotientGroup.eq] at hxy
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using hxy
  have h1 : HasSum f z := by
    rw [← hιinj.hasSum_iff]
    · convert hsum using 1
      funext y
      show f (mk (Subgroup.inclusion hHΓ y.out)) = _
      rw [hfmk]
      rfl
    · intro x hx
      show Ψ (x.out : G) = 0
      apply hvan _ x.out.2
      intro hH
      apply hx
      refine ⟨mk ⟨(x.out : G), hH⟩, ?_⟩
      rw [hιmk]
      conv_rhs => rw [← QuotientGroup.out_eq' x]
      rfl

  have hle : K.subgroupOf Γ ≤ J.subgroupOf Γ := fun x hx => by
    simpa [Subgroup.mem_subgroupOf] using hKJ (Subgroup.mem_subgroupOf.mp hx)
  let e := Subgroup.quotientEquivProdOfLE hle
  have hJΓ : J ≤ Γ := hJH.trans hHΓ
  have hrel : (K.subgroupOf Γ).relIndex (J.subgroupOf Γ) = K.relIndex J :=
    Subgroup.relIndex_subgroupOf hJΓ
  haveI : (((K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))).FiniteIndex := ⟨by
    rw [← Subgroup.relIndex, hrel]; exact hidx⟩
  haveI : Finite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) :=
    Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ))
  have hcard : (Fintype.card (J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) : ℂ)
      = (K.relIndex J : ℂ) := by
    rw [Fintype.card_eq_nat_card, ← Subgroup.index, ← Subgroup.relIndex, hrel]
  have h2 := hasSum_comp_fst_card_mul_of_fintype (β := J.subgroupOf Γ ⧸ (K.subgroupOf Γ).subgroupOf (J.subgroupOf Γ)) f z h1
  rw [hcard, ← e.hasSum_iff] at h2
  convert h2 using 1
  funext y
  have he1 : (e y).1 = mk y.out := by
    conv_lhs => rw [← QuotientGroup.out_eq' y]
    rfl
  simp only [Function.comp_apply, he1, hfmk]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumOfDominatedOfEqNearZero
section
open Metric Filter Topology

namespace GlobalTheory

theorem hasSum_of_dominated_of_eq_near_zero {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ)
    (hbc : ∀ i, ‖b i‖ ≤ c i)
    (hc : ∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hnear : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) :
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) := by
  intro z hz
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz
  have hbound : ∀ i (w : ℂ), ‖b i * w ^ n i‖ ≤ c i * ‖w‖ ^ n i := by
    intro i w
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hbc i) (pow_nonneg (norm_nonneg w) _)
  have hsum : ∀ w : ℂ, ‖w‖ < r → Summable (fun i => b i * w ^ n i) := by
    intro w hw
    exact Summable.of_norm_bounded (hc ‖w‖ (norm_nonneg w) hw) (fun i => hbound i w)
  let F : ℂ → ℂ := fun w => ∑' i, b i * w ^ n i
  have hFd : DifferentiableOn ℂ F (ball 0 r) := by
    intro w hw
    have hw' : ‖w‖ < r := by simpa using hw
    obtain ⟨s, hws, hsr⟩ := exists_between hw'
    have hs0 : 0 ≤ s := le_trans (norm_nonneg w) hws.le
    have hd : DifferentiableOn ℂ F (ball 0 s) := by
      refine Complex.differentiableOn_tsum_of_summable_norm (u := fun i => c i * s ^ n i) (hc s hs0 hsr)
        (fun i => ?_) isOpen_ball (fun i v hv => ?_)
      · exact ((differentiable_const _).mul (differentiable_id.pow _)).differentiableOn
      · refine (hbound i v).trans ?_
        have hv' : ‖v‖ < s := by simpa using hv
        have hci : 0 ≤ c i := (norm_nonneg _).trans (hbc i)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hv'.le _) hci
    exact (hd.differentiableAt (isOpen_ball.mem_nhds (by simpa using hws))).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F (ball 0 r) := hFd.analyticOnNhd isOpen_ball
  have hRa : AnalyticOnNhd ℂ R (ball 0 r) := hR.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ w in 𝓝[≠] (0:ℂ), F w = R w := by
    apply Eventually.frequently
    have h1 : ∀ᶠ w in 𝓝 (0:ℂ), w ∈ ball (0:ℂ) ε := isOpen_ball.mem_nhds (mem_ball_self hε)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with w hw hw0
    have hw0' : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hwε : ‖w‖ < ε := by simpa using hw
    exact (hnear w hw0' hwε).tsum_eq
  have heq := hFa.eqOn_of_preconnected_of_frequently_eq hRa (convex_ball (0:ℂ) r).isPreconnected
    (mem_ball_self hr) hfreq
  have hzb : z ∈ ball (0:ℂ) r := by simpa using hz
  rw [← heq hzb]
  exact (hsum z hz).hasSum

theorem hasSum_of_dominated_of_eq_near_zero' : ∀ {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ) (R : ℂ → ℂ) (r ε : ℝ), (∀ i, ‖b i‖ ≤ c i) →
    (∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) → 0 < ε →
    DifferentiableOn ℂ R (Metric.ball 0 r) →
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) →
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) :=
  fun b c n R r ε h1 h2 h3 h4 h5 => hasSum_of_dominated_of_eq_near_zero b c n R r ε h1 h2 h3 h4 h5

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermiteReductionUnipotent
section
namespace GlobalTheory

theorem hermite_reduction_column {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R)
    (r : Fin n → R → R) (hb : ∀ i j, j < i → b i j = 0) (hr : ∀ i y, b i i ∣ y - r i y)
    (j : Fin n) (m : ℕ) :
    ∃ x : Fin n → R, x j = 1 ∧ (∀ l, j < l → x l = 0) ∧
      ∀ i : Fin n, i < j → (j : ℕ) ≤ i + m → ∃ y, b.mulVec x i = r i y := by
  induction m with
  | zero =>
    refine ⟨Pi.single j 1, by simp, fun l hl => by simp [hl.ne'], fun i hi hj => ?_⟩
    exact absurd (Fin.lt_def.1 hi) (by omega)
  | succ m ih =>
    obtain ⟨x, hx1, hx0, hx⟩ := ih
    by_cases h : ∃ k : Fin n, (j : ℕ) = k + m + 1
    · obtain ⟨k, hk⟩ := h
      obtain ⟨z, hz⟩ := hr k (b.mulVec x k)
      have hkj : k < j := Fin.lt_def.2 (by omega)
      have key : ∀ i, b.mulVec (x - Pi.single k z) i = b.mulVec x i - b i k * z := by
        intro i
        rw [Matrix.mulVec_sub, Pi.sub_apply]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      refine ⟨x - Pi.single k z, ?_, fun l hl => ?_, fun i hi hj => ?_⟩
      · simp [hx1, hkj.ne']
      · simp [hx0 l hl, (hkj.trans hl).ne']
      · rw [key]
        by_cases hik : i = k
        · subst hik
          exact ⟨b.mulVec x i, by rw [← hz]; ring⟩
        · have hne : (i : ℕ) ≠ k := fun e => hik (Fin.ext e)
          have hki : k < i := Fin.lt_def.2 (by omega)
          rw [hb i k hki, zero_mul, sub_zero]
          exact hx i hi (by omega)
    · refine ⟨x, hx1, hx0, fun i hi hj => hx i hi ?_⟩
      by_contra hc
      exact h ⟨i, by omega⟩

theorem hermite_reduction_unipotent :
    ∀ (R : Type) [CommRing R] (n : ℕ) (b : Matrix (Fin n) (Fin n) R) (r : Fin n → R → R),
      (∀ i j, j < i → b i j = 0) → (∀ i y, b i i ∣ y - r i y) →
      ∃ u : Matrix (Fin n) (Fin n) R, (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧
        ∀ i j, i < j → ∃ y, (b * u) i j = r i y := by
  intro R _ n b r hb hr
  choose x hx1 hx0 hx using fun j : Fin n => hermite_reduction_column b r hb hr j n
  refine ⟨Matrix.of fun i j => x j i, fun i j h => hx0 j i h, fun i => hx1 i, fun i j h => ?_⟩
  obtain ⟨y, hy⟩ := hx j i h (by have := j.2; omega)
  exact ⟨y, by rw [← hy]; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.Imports
section
namespace GlobalTheory.SmulMemOfMemSpan

theorem exists_smul_mem_of_mem_span {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
    [IsScalarTower R K V] (M : Submodule R V) {v : V}
    (hv : v ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • v ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm a b, mul_smul]; exact M.smul_mem b hax
    · rw [mul_smul]; exact M.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors R) c
    dsimp only at hnd
    refine ⟨d * a, mul_ne_zero (nonZeroDivisors.ne_zero d.2) ha, ?_⟩
    have key : (d : R) • c • x = n • x := by
      rw [← algebraMap_smul K (d : R) (c • x), smul_smul, mul_comm, hnd, algebraMap_smul]
    rw [mul_comm (d : R) a, mul_smul, key, smul_comm a n x]
    exact M.smul_mem n hax

theorem main : ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : Module R V] [inst_7 : Module K V] [IsScalarTower R K V] (M : Submodule R V) {v : V}, v ∈ Submodule.span K (↑M : Set V) → ∃ (a : R), a ≠ (0 : R) ∧ a • v ∈ M :=
  by
  intro R K V _ _ _ _ _ _ _ _ _ M v hv
  exact exists_smul_mem_of_mem_span M hv

end GlobalTheory.SmulMemOfMemSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsFurther
section
namespace GlobalTheory.SmulMemOfMemSpanExists

theorem exists_smul_mem_of_mem_span {Oe K'' T : Type} [CommRing Oe] [IsDomain Oe] [Field K'']
    [Algebra Oe K''] [IsFractionRing Oe K''] [AddCommGroup T] [Module K'' T] [Module Oe T]
    [IsScalarTower Oe K'' T] (M : Submodule Oe T) {x : T}
    (hx : x ∈ Submodule.span K'' (↑M : Set T)) : ∃ c : Oe, c ≠ (0 : Oe) ∧ c • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hay
    · rw [mul_smul]; exact M.smul_mem _ hbz
  | smul k y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := Oe) k
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap Oe K'' d ≠ 0 := fun h =>
      hd0 (IsFractionRing.injective Oe K'' (by rw [h, map_zero]))
    refine ⟨a * d, mul_ne_zero ha hd0, ?_⟩
    have key : (a * d) • ((algebraMap Oe K'' n / algebraMap Oe K'' d) • y) = n • (a • y) := by
      rw [← algebraMap_smul K'' (a * d), ← algebraMap_smul K'' n, ← algebraMap_smul K'' a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [key]
    exact M.smul_mem _ hay

end GlobalTheory.SmulMemOfMemSpanExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsMore
section
namespace GlobalTheory.TargetStatementSixOneNinetySeven

open Module

theorem main {ι E : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (f : ι → Module.End ℂ E) (hc : ∀ i j, Commute (f i) (f j)) :
    ∃ x : E, x ≠ (0 : E) ∧ ∀ i, ∃ μ : ℂ, (f i : E → E) x = μ • x := by
  classical
  let P : Submodule ℂ E → Prop := fun p => p ≠ ⊥ ∧ ∀ i, ∀ x ∈ p, f i x ∈ p
  have hex : ∃ n, ∃ p : Submodule ℂ E, finrank ℂ p = n ∧ P p :=
    ⟨_, ⊤, rfl, top_ne_bot, fun i x _ => Submodule.mem_top⟩
  obtain ⟨p, hpn, hpb, hpi⟩ := Nat.find_spec hex
  have hmin : ∀ q : Submodule ℂ E, P q → finrank ℂ p ≤ finrank ℂ q := by
    intro q hq
    rw [hpn]
    exact Nat.find_min' hex ⟨q, rfl, hq⟩
  have hscal : ∀ i, ∃ μ : ℂ, ∀ x ∈ p, f i x = μ • x := by
    intro i
    haveI : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hpb
    let g : Module.End ℂ p := (f i).restrict (hpi i)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue g
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    refine ⟨μ, ?_⟩
    let q : Submodule ℂ E := p ⊓ Module.End.eigenspace (f i) μ
    have hvq : (v : E) ∈ q := by
      refine Submodule.mem_inf.mpr ⟨v.2, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      have h1 := Module.End.mem_eigenspace_iff.mp hv.1
      have h2 := congrArg Subtype.val h1
      simpa [g] using h2
    have hqb : q ≠ ⊥ := by
      intro h
      have h0 : (v : E) = 0 := by rw [h] at hvq; exact (Submodule.mem_bot ℂ).mp hvq
      exact hv.2 (Subtype.ext h0)
    have hqi : ∀ j, ∀ x ∈ q, f j x ∈ q := by
      intro j x hx
      refine Submodule.mem_inf.mpr ⟨hpi j x (Submodule.mem_inf.mp hx).1, ?_⟩
      rw [Module.End.mem_eigenspace_iff]
      have hx2 := Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hx).2
      have hcomm : f i (f j x) = f j (f i x) := by
        have h3 := (hc i j).eq
        exact congrArg (fun T : Module.End ℂ E => T x) h3
      rw [hcomm, hx2, map_smul]
    have hle : q ≤ p := inf_le_left
    have heq : q = p := Submodule.eq_of_le_of_finrank_le hle (hmin q ⟨hqb, hqi⟩)
    intro x hx
    rw [← heq] at hx
    exact Module.End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp hx).2
  obtain ⟨x, hxp, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpb
  refine ⟨x, hx0, fun i => ?_⟩
  obtain ⟨μ, hμ⟩ := hscal i
  exact ⟨μ, hμ x hxp⟩

end GlobalTheory.TargetStatementSixOneNinetySeven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsTer
section
namespace GlobalTheory.TargetStatementSixOneSixtyEight

open NumberField

theorem main {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (RingOfIntegers E) V] [IsScalarTower (RingOfIntegers E) E V]
    (L : Submodule (RingOfIntegers E) V) {y : V} (hy : y ∈ Submodule.span E (L : Set V)) :
    ∃ c : RingOfIntegers E, c ≠ 0 ∧ c • y ∈ L := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ h1 h2 =>
    obtain ⟨c1, hc1, h1⟩ := h1
    obtain ⟨c2, hc2, h2⟩ := h2
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    rw [smul_add, mul_comm c1 c2, mul_smul, mul_comm c2 c1, mul_smul]
    exact L.add_mem (L.smul_mem c2 h1) (L.smul_mem c1 h2)
  | smul a x _ h =>
    obtain ⟨c0, hc0, h0⟩ := h
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    refine ⟨c0 * (s : RingOfIntegers E), mul_ne_zero hc0 (nonZeroDivisors.coe_ne_zero s), ?_⟩
    have key : (s : RingOfIntegers E) • (a • x) = b • x := by
      rw [← algebraMap_smul E (s : RingOfIntegers E), smul_smul, mul_comm, hs, algebraMap_smul]
    rw [mul_smul, key, smul_comm c0 b x]
    exact L.smul_mem b h0

theorem target : ∀ {E : Type} [inst : Field E] [NumberField E] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module E V] [inst_4 : Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (L : Submodule (NumberField.RingOfIntegers E) V) {y : V},
    y ∈ Submodule.span E (↑L : Set V) →
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ L :=
  fun L _ hy => main L hy

end GlobalTheory.TargetStatementSixOneSixtyEight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveSumOfLinIndepIntertwiners
section
namespace GlobalTheory

open Representation

theorem intertwiner_sum_eq_zero_imp {G : Type} [Group G] {N X : Type} [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X)
    (hirr : π.IsIrreducible)
    (hschur : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) :
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
      ∀ w : Fin m → N, ∑ j, φ j (w j) = 0 → w = 0 := by
  intro m
  induction m with
  | zero => intro φ _ w _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro φ hφ
    let Φ : (Fin (m+1) → N) →ₗ[ℂ] X := ∑ j, (φ j).toLinearMap ∘ₗ LinearMap.proj j
    have hΦ : ∀ w, Φ w = ∑ j, φ j (w j) := by intro w; simp [Φ, LinearMap.sum_apply]
    let K := LinearMap.ker Φ
    have hK : ∀ w, w ∈ K ↔ ∑ j, φ j (w j) = 0 := by intro w; simp [K, hΦ]
    have hφ' : LinearIndependent ℂ (fun j : Fin m => φ j.castSucc) :=
      hφ.comp _ (Fin.castSucc_injective m)
    have claimA : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) = 0 → w = 0 := by
      intro w hw hl
      rw [Fin.sum_univ_castSucc, hl, map_zero, add_zero] at hw
      have := ih _ hφ' (fun j => w j.castSucc) hw
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hl
      · exact congrFun this j
    have hstable : ∀ (g : G) (w : Fin (m+1) → N), ∑ j, φ j (w j) = 0 →
        ∑ j, φ j (π g (w j)) = 0 := by
      intro g w hw
      simp_rw [IntertwiningMap.isIntertwining]
      rw [← map_sum, hw, map_zero]
    let P : Subrepresentation π :=
      { toSubmodule := K.map (LinearMap.proj (Fin.last m))
        apply_mem_toSubmodule := by
          rintro g _ ⟨w, hw, rfl⟩
          refine ⟨fun j => π g (w j), ?_, rfl⟩
          rw [SetLike.mem_coe, hK] at hw ⊢
          exact hstable g w hw }
    have hmemP : ∀ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → w (Fin.last m) ∈ P := fun w hw =>
      show w (Fin.last m) ∈ K.map (LinearMap.proj (Fin.last m)) from ⟨w, (hK w).2 hw, rfl⟩
    rcases hirr.eq_bot_or_eq_top P with hP | hP
    · intro w hw
      apply claimA w hw
      have := hmemP w hw
      rw [hP] at this
      exact (Submodule.mem_bot ℂ).mp this
    · exfalso
      have hsurj : ∀ n : N, ∃ w : Fin (m+1) → N, ∑ j, φ j (w j) = 0 ∧ w (Fin.last m) = n := by
        intro n
        have : n ∈ P := by rw [hP]; exact Submodule.mem_top
        obtain ⟨w, hw, rfl⟩ := (show n ∈ K.map (LinearMap.proj (Fin.last m)) from this)
        exact ⟨w, (hK w).1 hw, rfl⟩
      have huniq : ∀ w w' : Fin (m+1) → N, ∑ j, φ j (w j) = 0 → ∑ j, φ j (w' j) = 0 →
          w (Fin.last m) = w' (Fin.last m) → w = w' := by
        intro w w' hw hw' hl
        have := claimA (w - w') (by simp [map_sub, Finset.sum_sub_distrib, hw, hw'])
          (by simp [hl])
        exact sub_eq_zero.mp this
      let p : K →ₗ[ℂ] N := LinearMap.proj (Fin.last m) ∘ₗ K.subtype
      have hp : Function.Bijective p := by
        constructor
        · intro a b hab
          exact Subtype.ext (huniq a.1 b.1 ((hK _).1 a.2) ((hK _).1 b.2) hab)
        · intro n
          obtain ⟨w, hw, hl⟩ := hsurj n
          exact ⟨⟨w, (hK w).2 hw⟩, hl⟩
      let e := LinearEquiv.ofBijective p hp
      let s : N →ₗ[ℂ] (Fin (m+1) → N) := K.subtype ∘ₗ e.symm.toLinearMap
      have hsK : ∀ n, ∑ j, φ j (s n j) = 0 := fun n => (hK _).1 (e.symm n).2
      have hsl : ∀ n, s n (Fin.last m) = n := fun n => e.apply_symm_apply n
      have hsg : ∀ (g : G) (n : N), s (π g n) = fun j => π g (s n j) := by
        intro g n
        apply huniq _ _ (hsK _) (hstable g _ (hsK n))
        simp only [hsl]
      have hc : ∀ j : Fin m, ∃ c : ℂ, ∀ n, s n j.castSucc = c • n := by
        intro j
        let f : π.IntertwiningMap π :=
          { toLinearMap := LinearMap.proj j.castSucc ∘ₗ s
            isIntertwining' := by
              intro g; ext n; simp [hsg] }
        obtain ⟨c, hc⟩ := hschur f
        refine ⟨c, fun n => ?_⟩
        have := congrArg (fun L => L n) hc
        simpa [f] using this
      choose c hc using hc
      have hrel : ∑ j : Fin m, c j • φ j.castSucc + φ (Fin.last m) = 0 := by
        ext n
        have := hsK n
        rw [Fin.sum_univ_castSucc] at this
        simp only [hc, hsl, map_smul] at this
        simpa [IntertwiningMap.sum_apply] using this
      have := (Fintype.linearIndependent_iff.mp hφ) (Fin.snoc c 1) (by
        rw [Fin.sum_univ_castSucc]; simpa using hrel)
      have h1 := this (Fin.last m)
      simp at h1

theorem intertwiners_indep_injective : ∀ (G : Type) [Group G] (N X : Type) [AddCommGroup N] [Module ℂ N]
    [AddCommGroup X] [Module ℂ X] (π : Representation ℂ G N) (ρ : Representation ℂ G X), π.IsIrreducible →
    (∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id) →
    ∀ (m : ℕ) (φ : Fin m → π.IntertwiningMap ρ), LinearIndependent ℂ φ →
    Function.Injective (fun w : Fin m → N => ∑ j, φ j (w j)) := by
  intro G _ N X _ _ _ _ π ρ hirr hschur m φ hφ a b hab
  have := intertwiner_sum_eq_zero_imp π ρ hirr hschur m φ hφ (a - b)
    (by simpa [map_sub, Finset.sum_sub_distrib, sub_eq_zero] using hab)
  exact sub_eq_zero.mp this

end GlobalTheory
end

