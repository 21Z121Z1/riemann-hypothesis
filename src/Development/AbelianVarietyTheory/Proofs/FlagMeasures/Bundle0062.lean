import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0013
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0056
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
import Formalism.FlagUnipotentLattices.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousUnitriangularSection
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSublatticesQuotientProdDegreeOnePrimes
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.SublatCount

section Abstract

variable {O N : Type} [CommRing O] [AddCommGroup N] [Module O N]

def Ker (I : Ideal O) (N : Type) [AddCommGroup N] [Module O N] : Set (Submodule O N) :=
  {L | ∃ f : N →ₗ[O] O ⧸ I, Function.Surjective f ∧ LinearMap.ker f = L}

theorem encard_eq_of_bijOn {α β : Type} {s : Set α} {t : Set β} {f : α → β} (h : Set.BijOn f s t) :
    s.encard = t.encard := by
  rw [← h.image_eq, h.injOn.encard_image]

theorem mem_ker_iff (I : Ideal O) (L : Submodule O N) :
    L ∈ Ker I N ↔ Nonempty ((N ⧸ L) ≃ₗ[O] (O ⧸ I)) := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f.quotKerEquivOfSurjective hf⟩
  · rintro ⟨e⟩
    refine ⟨e.toLinearMap ∘ₗ L.mkQ, e.surjective.comp L.mkQ_surjective, ?_⟩
    rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

theorem smul_quot {I : Ideal O} {c : O} (hc : c ∈ I) (y : O ⧸ I) : c • y = 0 := by
  have : algebraMap O (O ⧸ I) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
  rw [Algebra.smul_def, this, zero_mul]

theorem smul_mem {I : Ideal O} {L : Submodule O N} (h : L ∈ Ker I N) {c : O} (hc : c ∈ I)
    (x : N) : c • x ∈ L := by
  obtain ⟨f, -, rfl⟩ := h
  rw [LinearMap.mem_ker, map_smul, smul_quot hc]

noncomputable def crt (I J : Ideal O) (h : IsCoprime I J) :
    (O ⧸ I * J) ≃ₗ[O] (O ⧸ I) × (O ⧸ J) :=
  { Ideal.quotientMulEquivQuotientProd I J h with
    map_smul' := fun c x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl }

theorem encard_mul (I J : Ideal O) (h : IsCoprime I J) :
    (Ker (I * J) N).encard = (Ker I N).encard * (Ker J N).encard := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  have key : ∀ {I J : Ideal O} {a b : O}, a ∈ I → b ∈ J → a + b = 1 →
      ∀ {L₁ L₂ L₁' L₂' : Submodule O N}, L₂ ∈ Ker J N → L₁' ∈ Ker I N →
      L₁ ⊓ L₂ = L₁' ⊓ L₂' → L₁ ≤ L₁' := by
    intro I J a b ha hb hab L₁ L₂ L₁' L₂' h2 h1' he x hx
    have h3 : b • x ∈ L₁ ⊓ L₂ := ⟨L₁.smul_mem b hx, smul_mem h2 hb x⟩
    rw [he] at h3
    have := L₁'.add_mem (smul_mem h1' ha x) h3.1
    rwa [← add_smul, hab, one_smul] at this
  rw [← Set.encard_prod]
  symm
  refine encard_eq_of_bijOn (f := fun p => p.1 ⊓ p.2) ⟨?_, ?_, ?_⟩
  · rintro ⟨_, _⟩ ⟨⟨f, hf, rfl⟩, ⟨g, hg, rfl⟩⟩
    refine ⟨(crt I J h).symm.toLinearMap ∘ₗ f.prod g, (crt I J h).symm.surjective.comp ?_, ?_⟩
    · rintro ⟨x, y⟩
      obtain ⟨u, rfl⟩ := hf x
      obtain ⟨v, rfl⟩ := hg y
      refine ⟨b • u + a • v, Prod.ext ?_ ?_⟩
      · change f (b • u + a • v) = f u
        rw [map_add, map_smul, map_smul, smul_quot ha, ← smul_quot ha (f u), ← add_smul,
          add_comm, hab, one_smul]
      · change g (b • u + a • v) = g v
        rw [map_add, map_smul, map_smul, smul_quot hb, ← smul_quot hb (g v), ← add_smul,
          add_comm, hab, one_smul]
    · rw [LinearEquiv.ker_comp, LinearMap.ker_prod]
  · rintro ⟨L₁, L₂⟩ ⟨h1, h2⟩ ⟨L₁', L₂'⟩ ⟨h1', h2'⟩ he
    have he : L₁ ⊓ L₂ = L₁' ⊓ L₂' := he
    have he' : L₂ ⊓ L₁ = L₂' ⊓ L₁' := by rw [inf_comm, he, inf_comm]
    have hba : b + a = 1 := by rw [add_comm, hab]
    exact Prod.ext (le_antisymm (key ha hb hab h2 h1' he) (key ha hb hab h2' h1 he.symm))
      (le_antisymm (key hb ha hba h1 h2' he') (key hb ha hba h1' h2 he'.symm))
  · rintro _ ⟨f, hf, rfl⟩
    let g := (crt I J h).toLinearMap ∘ₗ f
    have hg : Function.Surjective g := (crt I J h).surjective.comp hf
    refine ⟨(LinearMap.ker (LinearMap.fst O _ _ ∘ₗ g), LinearMap.ker (LinearMap.snd O _ _ ∘ₗ g)),
      ⟨⟨_, Prod.fst_surjective.comp hg, rfl⟩, ⟨_, Prod.snd_surjective.comp hg, rfl⟩⟩, ?_⟩
    change LinearMap.ker _ ⊓ LinearMap.ker _ = _
    rw [← LinearMap.ker_prod, ← LinearEquiv.ker_comp (crt I J h) f]
    rfl

theorem encard_top : (Ker (⊤ : Ideal O) N).encard = 1 := by
  rw [Set.encard_eq_one]
  refine ⟨⊤, Set.eq_singleton_iff_unique_mem.2 ⟨⟨0, fun y => ⟨0, Subsingleton.elim _ _⟩, by simp⟩, ?_⟩⟩
  intro L hL
  rw [eq_top_iff]
  intro x _
  simpa using smul_mem hL (c := 1) trivial x

theorem encard_max [IsDomain O] [Module.Finite O N] [Module.Projective O N] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] :
    (Ker P N).encard =
      ((∑ i ∈ Finset.range (Module.finrank O N), Nat.card (O ⧸ P) ^ i : ℕ) : ℕ∞) := by
  have : Nontrivial (O ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  have he : Ker P N = {L : Submodule O N | ∃ f : N →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = L} := by
    ext L
    refine exists_congr fun f => and_congr_left fun _ => ⟨fun hf h0 => ?_, fun hf y => ?_⟩
    · obtain ⟨v, hv⟩ := hf 1
      rw [h0] at hv
      exact zero_ne_one hv
    · obtain ⟨v, hv⟩ := GlobalTheory.SW.Hyper.surj_of_ne P f hf
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨c • v, by rw [map_smul, hv, Algebra.smul_def, mul_one]; rfl⟩
  obtain ⟨hf, hc⟩ := GlobalTheory.SW.Hyper.count (M := N) P
  rw [he, ← hf.cast_ncard_eq]
  congr 1
  have h1 : 1 < Nat.card (O ⧸ P) := Finite.one_lt_card
  refine Nat.eq_of_mul_eq_mul_right (m := Nat.card (O ⧸ P) - 1) (by omega) ?_
  rw [hc, geom_sum_mul_of_one_le h1.le]

theorem encard_prod [IsDomain O] [Module.Finite O N] [Module.Projective O N] (T : ℕ) (hT : T ≠ 0)
    (s : Finset (Ideal O)) (hs : ∀ P ∈ s, P.IsMaximal ∧ Nat.card (O ⧸ P) = T) :
    (Ker (∏ P ∈ s, P) N).encard =
      (((∑ i ∈ Finset.range (Module.finrank O N), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Ideal.one_eq_top, encard_top]; simp
  | insert P s hP ih =>
    obtain ⟨hm, hc⟩ := hs P (Finset.mem_insert_self _ _)
    have : Finite (O ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hT)
    have hco : IsCoprime P (∏ Q ∈ s, Q) := IsCoprime.prod_right fun Q hQ =>
      Ideal.isCoprime_iff_sup_eq.2 (hm.coprime_of_ne (hs Q (Finset.mem_insert_of_mem hQ)).1
        fun h => hP (h ▸ hQ))
    rw [Finset.prod_insert hP, encard_mul _ _ hco, ih fun Q hQ => hs Q (Finset.mem_insert_of_mem hQ),
      encard_max, hc, Finset.card_insert_of_notMem hP, pow_succ', Nat.cast_mul]

end Abstract

theorem finrank_lattice {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V)
    (hM : Submodule.IsLattice K M) : Module.finrank (𝓞 K) M = Module.finrank K V := by
  have hr : Module.rank (𝓞 K) V = Module.rank K V :=
    (IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl).symm
  have : Module.rank (𝓞 K) M = Module.rank K V := by
    apply le_antisymm
    · rw [← hr]; exact Submodule.rank_le M
    · obtain ⟨s, hsM, hspan, hli⟩ := exists_linearIndependent K (M : Set V)
      rw [hM.span_eq_top] at hspan
      have h1 : Module.rank K V = Cardinal.mk s := by
        rw [← rank_top, ← hspan, rank_span_set hli]
      have h2 : LinearIndependent (𝓞 K) (fun x : s => (⟨x.1, hsM x.2⟩ : M)) := by
        apply LinearIndependent.of_comp M.subtype
        exact (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr hli
      rw [h1]
      exact h2.cardinal_le_rank
  simp only [Module.finrank, this]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ (T : ℕ) (s : Finset (Ideal (𝓞 K))), T.Prime → (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) → {L : Submodule (𝓞 K) V | L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))}.encard = (((∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ M hM T s hT hs
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  rw [← finrank_lattice M hM, ← encard_prod (N := M) T hT.ne_zero s fun P hP =>
    ⟨(hs P hP).1, by rw [← (hs P hP).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]⟩]
  refine encard_eq_of_bijOn (f := fun L => L.comap M.subtype) ⟨?_, ?_, ?_⟩
  · intro L hL
    exact (mem_ker_iff _ _).2 hL.2
  · intro L hL L' hL' h
    have := congrArg (Submodule.map M.subtype) h
    rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hL.1,
      inf_eq_right.2 hL'.1] at this
  · intro L hL
    have h : (L.map M.subtype).comap M.subtype = L := Submodule.comap_map_eq_of_injective M.injective_subtype L
    refine ⟨L.map M.subtype, ⟨Submodule.map_subtype_le _ _, ?_⟩, h⟩
    rw [h]
    exact (mem_ker_iff _ _).1 hL

end GlobalTheory.SublatCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CharFnLocallyConstant
section
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CharIdem

section

variable {G : Type} [Group G]

open Classical in

noncomputable def charFn (K : Subgroup G) (χ : K →* Circle) (c : ℝ) : G → ℂ :=
  fun x => if h : x ∈ K then star ((χ ⟨x, h⟩ : Circle) : ℂ) / (c : ℂ) else 0

variable (K : Subgroup G) (χ : K →* Circle) (c : ℝ)

theorem sum_fiber_nonneg {ι Q : Type} [Fintype ι] [DecidableEq Q] (q : ι → Q) (a : ι → ℂ) :
    0 ≤ ∑ i, ∑ j, (if q i = q j then star (a i) * a j else 0) := by
  have h : ∑ i, ∑ j, (if q i = q j then star (a i) * a j else 0) =
      ∑ t ∈ Finset.univ.image q, star (∑ i, if q i = t then a i else 0) *
        (∑ j, if q j = t then a j else 0) := by
    simp only [star_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    symm
    rw [Finset.sum_comm]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun j i => if q i = q j then star (a i) * a j else 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (q i)]
    · by_cases hij : q i = q j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hb
      exact absurd (Finset.mem_image_of_mem q (Finset.mem_univ i)) hb
  rw [h]
  exact Finset.sum_nonneg fun t _ => star_mul_self_nonneg _

variable [TopologicalSpace G] [IsTopologicalGroup G]

variable [MeasurableSpace G] [BorelSpace G]

end

end GlobalTheory.CharIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContentThickenedTupleOrbitNormalSubgroup
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ThickSplit

theorem cont_iUnion_cosets {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) {Γ : Type} [Group Γ]
    (N H : Subgroup Γ) [N.Normal] (hN : N.index ≠ 0) (S : Γ → Set W) (c : ℝ)
    (hco : ∀ a, IsCO W0 (S a)) (hc : ∀ a, cont W0 (S a) = c)
    (heq : ∀ a b, a⁻¹ * b ∈ N ⊔ H → S a = S b)
    (hdis : ∀ a b, ¬ Disjoint (S a) (S b) → a⁻¹ * b ∈ N ⊔ H) :
    cont W0 (⋃ a, S a) * (N.relIndex H : ℝ) = (N.index : ℝ) * c := by
  have hidx : N.relIndex H * (N ⊔ H).index = N.index := by
    rw [← Subgroup.relIndex_sup_left H N]
    exact Subgroup.relIndex_mul_index le_sup_left
  have hJ : (N ⊔ H).index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hidx
    exact hN hidx.symm
  haveI : (N ⊔ H).FiniteIndex := ⟨hJ⟩
  haveI : Fintype (Γ ⧸ (N ⊔ H)) := Fintype.ofFinite _
  have hU : (⋃ a, S a) = ⋃ q ∈ (Finset.univ : Finset (Γ ⧸ (N ⊔ H))), S q.out := by
    ext w
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨(a : Γ ⧸ (N ⊔ H)), ?_⟩
      rw [heq _ a (QuotientGroup.eq.1 (QuotientGroup.out_eq' _))]
      exact ha
    · rintro ⟨q, hq⟩
      exact ⟨_, hq⟩
  rw [hU, (GlobalTheory.T.commensurableCosetUnionContent_biUnion W0 Finset.univ (fun q : Γ ⧸ (N ⊔ H) => S q.out) (fun q _ => hco _)).2]
  · simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← hidx, Subgroup.index, Nat.card_eq_fintype_card]
    push_cast
    ring
  · intro q _ r _ hqr
    by_contra h
    apply hqr
    have := QuotientGroup.eq.2 (hdis _ _ h)
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem rmul_rmul {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

theorem rmul_one {n m : ℕ} (x : Fin m → Fin n → E) : rmul x 1 = x := by
  funext j
  simp [rmul, Matrix.one_apply]

theorem map_rmul {n m : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x : Fin m → Fin n → E)
    (A : Matrix (Fin m) (Fin m) E) : (fun a => g (rmul x A a)) = rmul (fun a => g (x a)) A := by
  funext j
  simp [rmul]

theorem hf_sum_sum (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (u v : Fin m → E) :
    hf L Hm (∑ i, u i • x i) (∑ j, v j • x j) = ∑ i, ∑ j, u i * L.cj (v j) * hf L Hm (x i) (x j) := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  calc _ = ∑ p : Fin n × Fin n, ∑ q : Fin m × Fin m,
        u q.1 * L.cj (v q.2) * (x q.1 p.1 * Hm p.1 p.2 * L.cj (x q.2 p.2)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = _ := by
        rw [Finset.sum_comm, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [Fintype.sum_prod_type]

theorem gramT_rmul (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  ext a b
  simp only [gramT, rmul, Matrix.of_apply, hf_sum_sum, Matrix.mul_apply, cT, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem mem_fixG (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    g ∈ fixG L Hm (Submodule.span E (Set.range x)) ↔ g ∈ isomG L Hm ∧ ∀ a, g (x a) = x a := by
  constructor
  · rintro ⟨h1, _, h3⟩
    refine ⟨h1, fun a => ?_⟩
    have := h3 (x a) (Submodule.subset_span ⟨a, rfl⟩)
    exact sub_eq_zero.1 ((Submodule.mem_bot E).1 this)
  · rintro ⟨h1, h2⟩
    have key : ∀ v ∈ Submodule.span E (Set.range x), g v = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv => obtain ⟨a, rfl⟩ := hv; exact h2 a
      | zero => simp
      | add u v _ _ hu hv => rw [map_add, hu, hv]
      | smul c v _ hv => rw [map_smul, hv]
    refine ⟨h1, fun v => ⟨fun hv => ?_, fun hv => by rw [key v hv]; exact hv⟩, fun v hv => ?_⟩
    · have := g.injective (key _ hv)
      rwa [this] at hv
    · rw [key v hv, sub_self]
      exact Submodule.zero_mem _
end

end GlobalTheory.HL.ThickSplit

open GlobalTheory.HL.ThickSplit in

theorem GlobalTheory.HL.cont_thick_torb_normal : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ K K' : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), K ≤ isomG L Hm → K' ≤ K → (∀ a ∈ K, MulAut.conj a • K' = K') → K'.relIndex K ≠ 0 → ∀ i : ℕ, 1 ≤ i → (∀ y ∈ torb K' x, ∀ A ∈ congK L ϖ m i, cT L A * gramT L Hm x * A = gramT L Hm x → rmul y A ∈ torb K' x) → IsCO (tupLat L Λs m) (thick L ϖ (torb K' x) i) → cont (tupLat L Λs m) (thick L ϖ (torb K x) i) * ((fixG L Hm (Submodule.span E (Set.range x)) ⊓ K').relIndex (fixG L Hm (Submodule.span E (Set.range x)) ⊓ K) : ℝ) = (K'.relIndex K : ℝ) * cont (tupLat L Λs m) (thick L ϖ (torb K' x) i) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛ m x _ K K' hK hK' hnorm hidx i hi hstab hco
  obtain ⟨-, hgrp, -⟩ := GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i hi
  have hjac := (GlobalTheory.T.tuple_jacobian_rightMul_isometry L ϖ hϖ Hm hH Λs hΛ m).2
  have hconj : ∀ a ∈ K, ∀ k ∈ K', a * k * a⁻¹ ∈ K' := by
    intro a ha k hk
    rw [← hnorm a ha]
    exact Subgroup.smul_mem_pointwise_smul k (MulAut.conj a) K' hk
  haveI : (K'.subgroupOf K).Normal :=
    ⟨fun k hk a => hconj a a.2 k hk⟩
  set Fx := fixG L Hm (Submodule.span E (Set.range x)) with hFx
  have hsub : ∀ a b : K, a⁻¹ * b ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K →
      (fun x c => (b : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i ⊆
      (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i := by
    intro a b hab
    obtain ⟨k, hk, h, hh, hkh⟩ := Subgroup.mem_sup_of_normal_left.1 hab
    have hb : b = a * (k * h) := by rw [hkh]; group
    have hhx := ((mem_fixG L Hm x h).1 hh).2
    rintro _ ⟨_, ⟨_, ⟨k1, hk1, rfl⟩, A, hA, rfl⟩, rfl⟩
    refine ⟨_, ⟨_, ⟨k * (h * k1 * (h : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹),
      K'.mul_mem hk (hconj h h.2 k1 hk1), rfl⟩, A, hA, rfl⟩, ?_⟩
    simp only [map_rmul]
    congr 1
    funext c
    have : ((h : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹) (x c) = x c := by
      conv_lhs => rw [← hhx c]
      exact LinearEquiv.symm_apply_apply _ _
    rw [hb]
    simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, this]
  have main := cont_iUnion_cosets (tupLat L Λs m) (K'.subgroupOf K) (Fx.subgroupOf K) hidx
    (fun a : K => (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) '' thick L ϖ (torb K' x) i)
    (cont (tupLat L Λs m) (thick L ϖ (torb K' x) i))
    (fun a => (hjac a (hK a.2) _ hco).1) (fun a => (hjac a (hK a.2) _ hco).2)
    (fun a b hab => Set.Subset.antisymm
      (hsub b a (by simpa using Subgroup.inv_mem _ hab)) (hsub a b hab)) ?_
  · have hU : thick L ϖ (torb K x) i = ⋃ a : K, (fun x c => (a : (Fin n → E) ≃ₗ[E] (Fin n → E)) (x c)) ''
        thick L ϖ (torb K' x) i := by
      ext w
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, A, hA, rfl⟩
        exact ⟨⟨a, ha⟩, _, ⟨x, ⟨1, K'.one_mem, rfl⟩, A, hA, rfl⟩, map_rmul a x A⟩
      · rintro ⟨a, _, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩
        exact ⟨_, ⟨a * k, K.mul_mem a.2 (hK' hk), rfl⟩, A, hA, map_rmul _ _ A⟩
    have hI : (K'.subgroupOf K).relIndex (Fx.subgroupOf K) = (Fx ⊓ K').relIndex (Fx ⊓ K) := by
      rw [← Subgroup.inf_subgroupOf_right Fx K, Subgroup.relIndex_subgroupOf inf_le_right,
        ← Subgroup.inf_relIndex_right K' (Fx ⊓ K)]
      congr 1
      rw [inf_comm, inf_assoc, inf_eq_right.2 hK']
    rw [hU, ← hI]
    exact main
  · intro a b hab
    obtain ⟨w, ⟨_, ⟨_, ⟨k, hk, rfl⟩, A, hA, rfl⟩, rfl⟩, ⟨_, ⟨_, ⟨k', hk', rfl⟩, A', hA', rfl⟩, hw⟩⟩ :=
      Set.not_disjoint_iff.1 hab
    obtain ⟨-, hdet, -, hinv, -, -⟩ := hgrp A' hA'
    have hB : A * A'⁻¹ ∈ congK L ϖ m i := (hgrp A hA).2.2.2.2.1 _ hinv
    set g : (Fin n → E) ≃ₗ[E] (Fin n → E) := k⁻¹ * (a : (Fin n → E) ≃ₗ[E] (Fin n → E))⁻¹ * b * k' with hg
    have hgK : g ∈ K := K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem (hK' hk)) (K.inv_mem a.2)) b.2) (hK' hk')
    have h1 : rmul (fun c => g (x c)) A' = rmul x A := by
      rw [← map_rmul]
      funext c
      have h2 := congrFun hw c
      have h3 := congrFun (map_rmul k' x A') c
      have h4 := congrFun (map_rmul k x A) c
      simp only at h2 h3 h4
      rw [← h3, ← h4] at h2
      rw [hg]
      simp only [LinearEquiv.mul_apply]
      rw [h2]
      simp [LinearEquiv.coe_inv]
    have h2 : (fun c => g (x c)) = rmul x (A * A'⁻¹) := by
      rw [← rmul_rmul, ← h1, rmul_rmul, Matrix.mul_nonsing_inv _ hdet, rmul_one]
    have h3 : cT L (A * A'⁻¹) * gramT L Hm x * (A * A'⁻¹) = gramT L Hm x := by
      rw [← gramT_rmul, ← h2]
      ext c d
      exact hK hgK _ _
    obtain ⟨k'', hk'', h4⟩ := hstab x ⟨1, K'.one_mem, rfl⟩ _ hB h3
    rw [← h2] at h4
    have hfix : k''⁻¹ * g ∈ Fx := by
      refine (mem_fixG L Hm x _).2 ⟨hK (K.mul_mem (K.inv_mem (hK' hk'')) hgK), fun c => ?_⟩
      rw [LinearEquiv.mul_apply, congrFun h4 c]
      exact LinearEquiv.symm_apply_apply _ _
    have hmem : ∀ u (hu : u ∈ K'), (⟨u, hK' hu⟩ : K) ∈ K'.subgroupOf K ⊔ Fx.subgroupOf K :=
      fun u hu => Subgroup.mem_sup_left hu
    have hmem' : (⟨k''⁻¹ * g, K.mul_mem (K.inv_mem (hK' hk'')) hgK⟩ : K) ∈
        K'.subgroupOf K ⊔ Fx.subgroupOf K := Subgroup.mem_sup_right hfix
    have hfin := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem k hk) (hmem k'' hk''))
      hmem') (Subgroup.inv_mem _ (hmem k' hk'))
    convert hfin using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
    group
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesOfIndexLe
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem sublattice_count : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ i : ℕ, 1 ≤ i → (({N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K))) := by
  intro K V _ _ _ _ _ _ _ _ h _ _ _ M hM i hi
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM.fg
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.IsTorsionFree (𝓞 K) M := inferInstance
  have : Module.Flat (𝓞 K) M := inferInstance
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have hr : Module.finrank (𝓞 K) M ≤ Module.finrank K V := by
    have h1 : Module.rank (𝓞 K) M ≤ Module.rank K V := by
      rw [IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl]
      exact Submodule.rank_le M
    exact Cardinal.toNat_le_toNat h1 (Module.rank_lt_aleph0 K V)
  obtain ⟨hfin, hle⟩ := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.c2a K M (Module.finrank K V) i hi hr
  have hinj : Set.InjOn (fun N : Submodule (𝓞 K) V => N.comap M.subtype)
      {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i} := by
    intro N hN N' hN' e
    have := congrArg (Submodule.map M.subtype) e
    simpa [Submodule.map_comap_subtype, inf_eq_right.mpr hN.1, inf_eq_right.mpr hN'.1] using this
  have hmaps : Set.MapsTo (fun N : Submodule (𝓞 K) V => N.comap M.subtype)
      {N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}
      {N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i} := by
    intro N hN
    exact hN.2
  have h2 := Set.encard_le_encard_of_injOn hmaps hinj
  rw [← hfin.cast_ncard_eq] at h2
  calc _ ≤ (((({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i}.ncard : ℕ) : ℕ∞)) : ℝ≥0∞) := by
        exact_mod_cast h2
    _ = ENNReal.ofReal ({N : Submodule (𝓞 K) M | N.toAddSubgroup.index = i}.ncard : ℝ) := by
        simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal hle

end GlobalTheory.Mass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousUnitriangularSectionStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_unitriangular_section : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, Continuous t ∧ (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) := by
  first | exact @GlobalTheory.UnitriSection.unitri_section | exact GlobalTheory.UnitriSection.unitri_section | (intros; apply GlobalTheory.UnitriSection.unitri_section <;> assumption)
end

