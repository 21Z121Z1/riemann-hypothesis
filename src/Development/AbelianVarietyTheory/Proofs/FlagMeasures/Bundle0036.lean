import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIntegralIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NcardImageOfLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0021
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0022
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0027
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruentOneMatricesTransitiveNearHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AlgMem
section
open ValuativeRel Formalism.MainNotions.S.Loc

namespace GlobalTheory.PowMulMem

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem alg_mem (L : LocE F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ L.O := by
  rw [L.O_def]
  exact isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := a)

theorem exists_pow_mul_mem [IsNonarchimedeanLocalField F] (L : LocE F E) {ϖ : 𝒪[F]}
    (hϖ : Irreducible ϖ) (e : E) : ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * e ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have h1 : IsAlgebraic F e := Algebra.IsAlgebraic.isAlgebraic e
  have h2 : IsAlgebraic 𝒪[F] e := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1
  obtain ⟨c, hc0, hc⟩ := h2.exists_integral_multiple
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  refine ⟨k, ?_⟩
  have h3 : c • e ∈ L.O := (L.O_def _).2 hc
  have h4 := L.O.mul_mem (alg_mem L ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])) h3
  have h5 : ϖ ^ k = ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * c := by
    rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
  have h6 : (ϖ : F) ^ k = (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * (c : F) := by
    exact_mod_cast congrArg (fun x : 𝒪[F] => (x : F)) h5
  have h7 : c • e = algebraMap F E (c : F) * e := by
    rw [← Algebra.smul_def]; rfl
  rw [h6, map_mul, mul_assoc, ← h7]
  exact h4

theorem exists_pow_smul_mem [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E)
    {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ} {Λ : Submodule L.O (Fin n → E)}
    (hΛ : GlobalTheory.HL.IsLat L Λ) (v : Fin n → E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) • v ∈ Λ := by
  have hO : ∀ (x : E), x ∈ L.O → ∀ w ∈ Λ, x • w ∈ Λ := fun x hx w hw =>
    Λ.smul_mem (⟨x, hx⟩ : L.O) hw
  have hp : ∀ k : ℕ, algebraMap F E ((ϖ : F) ^ k) ∈ L.O := fun k => by
    rw [map_pow]; exact L.O.pow_mem (alg_mem L ϖ) k
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, hO _ (hp 0) _ hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · have := hO _ (hp b) _ ha
      rwa [smul_smul, ← map_mul, ← pow_add, add_comm b a] at this
    · have := hO _ (hp a) _ hb
      rwa [smul_smul, ← map_mul, ← pow_add] at this
  | smul e x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := exists_pow_mul_mem L hϖ e
    refine ⟨a + b, ?_⟩
    have := hO _ hb _ ha
    have h : algebraMap F E ((ϖ : F) ^ (a + b)) • e • x
        = (algebraMap F E ((ϖ : F) ^ b) * e) • algebraMap F E ((ϖ : F) ^ a) • x := by
      rw [smul_smul, smul_smul, pow_add, map_mul]
      congr 1
      ring
    rw [h]
    exact this

end GlobalTheory.PowMulMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cokernel_unramifiedOrder_matrix_of_det_base : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι L.O) (j : ℕ) (u : (𝒪[F])ˣ), ((A.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ j * ((u : 𝒪[F]) : F)) → Nat.card ((ι → L.O) ⧸ LinearMap.range A.mulVecLin) = resQ ϖ ^ (2 * j) := by
  first | exact @GlobalTheory.UnramOrder.card_coker_of_det_eq | exact GlobalTheory.UnramOrder.card_coker_of_det_eq | (intros; apply GlobalTheory.UnramOrder.card_coker_of_det_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardPrimitiveTupleExtensionsLe
section
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem ncard_extend_prim_one : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k + 1 ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B) (t : B), c t = t → |(Set.ncard {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} : ℝ) - (q : ℝ) ^ (2 * n - (2 * k + 1))| ≤ 3 * (q : ℝ) ^ n := by
  intro B _ _ c hc ω hω hf q hq hB k n hkn x hx g t ht
  obtain ⟨χ, hχ, hχc⟩ := GlobalTheory.T.exists_primitive_addChar_involution_invariant c hc ω hω hf
  have hZ := GlobalTheory.T.card_hermitianQuadric_affineSubspace_residueRing c hc ω hω hf q hq hB χ hχ hχc k n (by omega) x hx g t ht
  have hD := GlobalTheory.T.ncard_dependent_vectors_affine_gram_le c hc ω hω hf q hq hB k n (by omega) x hx g
  set S := {y : Fin n → B | Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B) ∧ (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hS
  set Z := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ip c y y = t} with hZd
  set D := {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} with hDd
  have h1 : S ⊆ Z := fun y hy => hy.2
  have h2 : Z ⊆ S ∪ D := by
    intro y hy
    by_cases hp : Prim c (Fin.cons y x : Fin (k + 1) → Fin n → B)
    · exact Or.inl ⟨hp, hy⟩
    · right
      have hne : ¬ ∀ s : Fin (k + 1) → B,
          ∑ a, s a • (Fin.cons y x : Fin (k + 1) → Fin n → B) a = 0 → s = 0 :=
        fun h => hp (GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring c hc χ hχ (k + 1) n _ h)
      push Not at hne
      obtain ⟨s, hs, hs0⟩ := hne
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      refine ⟨hy.1, s 0, ?_, fun i => -s i.succ, ?_⟩
      · intro h0
        apply hs0
        rw [h0, zero_smul, zero_add] at hs
        have h3 := hx.eq_zero c (fun i => s i.succ) hs
        funext i
        refine Fin.cases h0 (fun j => ?_) i
        exact congrFun h3 j
      · simp only [neg_smul, Finset.sum_neg_distrib]
        exact eq_neg_of_add_eq_zero_left hs
  have h3 : S.ncard ≤ Z.ncard := Set.ncard_le_ncard h1 (Set.toFinite _)
  have h4 : Z.ncard ≤ S.ncard + 2 * q ^ n :=
    (Set.ncard_le_ncard h2 (Set.toFinite _)).trans
      ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left hD _))
  have h3' : (S.ncard : ℝ) ≤ Z.ncard := by exact_mod_cast h3
  have h4' : (Z.ncard : ℝ) ≤ S.ncard + 2 * (q : ℝ) ^ n := by exact_mod_cast h4
  have h5 : (0 : ℝ) ≤ (q : ℝ) ^ n := by positivity
  rw [abs_le] at hZ ⊢
  constructor <;> linarith [hZ.1, hZ.2]

end GlobalTheory.GramCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardQuotEqPow
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramCard

theorem card_quot_mul {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (b : R) :
    Nat.card (R ⧸ Ideal.span {a * b}) =
      Nat.card (R ⧸ Ideal.span {a}) * Nat.card (R ⧸ Ideal.span {b}) := by
  have h : Ideal.span {a * b} = a • Ideal.span {b} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Submodule.ideal_span_singleton_smul,
      smul_eq_mul]
  rw [h]
  have hi := Ideal.mulQuot_injective (Ideal.span {b}) ha
  have hs := Ideal.quotOfMul_surjective (a := a) (Ideal.span {b})
  have he := Ideal.exact_mulQuot_quotOfMul (a := a) (Ideal.span {b})
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (Ideal.quotOfMul a (Ideal.span {b}))),
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hs).toEquiv, he.linearMap_ker_eq,
    ← Nat.card_congr (LinearEquiv.ofInjective _ hi).toEquiv, mul_comm]

theorem card_quot_map {R : Type*} [CommRing R] (c : R ≃+* R) (a : R) :
    Nat.card (R ⧸ Ideal.span {c a}) = Nat.card (R ⧸ Ideal.span {a}) := by
  refine (Nat.card_congr (Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {c a}) c ?_).toEquiv).symm
  rw [Ideal.map_span]
  simp

theorem card_quot_eq_pow : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ δ : L.O, IsUnit (δ : E) → 0 ≤ vE L ϖ ((δ : E) * L.cj δ) ∧ Nat.card (L.O ⧸ Ideal.span {δ}) = resQ ϖ ^ (vE L ϖ ((δ : E) * L.cj δ)).toNat := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ δ hδ
  obtain ⟨-, h2, -, -, h5, h6, -, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  obtain ⟨-, -, v3, v4⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨hcm, -, n, hn⟩ := h2 δ δ.2
  have hinj := GlobalTheory.UnramOrder.algebraMap_inj L
  have hE : Nontrivial E := hinj.nontrivial
  have hn0 : (n : F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hn
    exact (hδ.mul (hδ.map L.cj)).ne_zero hn
  rw [hn]
  have hv : 0 ≤ vE L ϖ (algebraMap F E (n : F)) := (v3 _ hn0).2 n.2
  refine ⟨hv, ?_⟩
  obtain ⟨u, hu⟩ := v4 _ hn0
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hv
  rw [hj, zpow_natCast] at hu
  rw [hj, Int.toNat_natCast]
  let c : L.O ≃+* L.O :=
    { toFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩
      invFun := fun x => ⟨L.cj x, GlobalTheory.UnramOrder.cj_mem L x.2⟩
      left_inv := fun x => Subtype.ext (L.cj_cj x)
      right_inv := fun x => Subtype.ext (L.cj_cj x)
      map_mul' := fun x y => Subtype.ext (map_mul L.cj (x : E) y)
      map_add' := fun x y => Subtype.ext (map_add L.cj (x : E) y) }
  have hnz : δ ∈ nonZeroDivisors L.O := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    have hx' : (x : E) * δ = 0 := by exact_mod_cast congrArg Subtype.val hx
    exact Subtype.ext (hδ.mul_left_eq_zero.1 hx')
  have hmul := card_quot_mul hnz (c δ)
  rw [card_quot_map] at hmul
  let ι : 𝒪[F] →+* L.O :=
    ((algebraMap F E).comp (𝒪[F]).subtype).codRestrict L.O (fun x => (h5 _).2 x.2)
  have hset : {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)} = {ι (ϖ ^ j)} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Subtype.ext_iff]
    rfl
  have hprod : δ * c δ = ι (ϖ ^ j) * ι u := by
    apply Subtype.ext
    change (δ : E) * L.cj δ = algebraMap F E ((ϖ : F) ^ j) * algebraMap F E ((u : 𝒪[F]) : F)
    rw [hn, ← map_mul, ← hu]
  have h7 := h6 j
  rw [hset] at h7
  rw [hprod, Ideal.span_singleton_mul_right_unit (u.isUnit.map ι), h7, two_mul, pow_add] at hmul
  exact (Nat.mul_self_inj.1 hmul).symm

end GlobalTheory.UnramCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommensurableCosetUnionContentIndependentNonnegStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commensurableCosetUnionContent_independent_nonneg : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (S : Set W), (∀ A, GoodSub W0 A S → cont W0 S = (((QuotientAddGroup.mk : W → W ⧸ A) '' S).ncard : ℝ) * relVol W0 A) ∧ (∀ A A', GoodSub W0 A S → A' ≤ A → A'.relIndex A ≠ 0 → GoodSub W0 A' S) ∧ 0 ≤ cont W0 S ∧ (IsCO W0 S → S.Nonempty → 0 < cont W0 S) := by
  first | exact @GlobalTheory.HL.cont_independent_pos | exact GlobalTheory.HL.cont_independent_pos | (intros; apply GlobalTheory.HL.cont_independent_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceSubgroupLatticeStabilizerStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_lattice_stabilizer : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Λ : Submodule L.O (Fin n → E)), IsLat L Λ → ∀ N : ℕ, (∃ K : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)), (∀ g, g ∈ K ↔ g ∈ stabL L Λ ∧ CongId L ϖ Λ N g) ∧ K.relIndex (stabL L Λ) ≠ 0 ∧ ∀ a ∈ stabL L Λ, MulAut.conj a • K = K) ∧ (1 ≤ N → ∀ g, CongId L ϖ Λ N g → g ∈ stabL L Λ) ∧ ∀ Λ', IsLat L Λ' → ∃ N' : ℕ, ∀ g, CongId L ϖ Λ N' g → CongId L ϖ Λ' N g := by
  first | exact @GlobalTheory.HL.congruence_subgroup_facts | exact GlobalTheory.HL.congruence_subgroup_facts | (intros; apply GlobalTheory.HL.congruence_subgroup_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruentOneMatricesTransitiveNearHermitianStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruentOneMatrices_transitive_near_hermitian : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsHerm L Γ → IsUnit Γ.det → ∀ i : ℕ, 1 ≤ i → ∃ j : ℕ, ∀ X ∈ horb L ϖ Γ i, ∀ D : Matrix (Fin m) (Fin m) E, IsHerm L D → IsIntM L D → ∃ A ∈ congK L ϖ m i, X + algebraMap F E ((ϖ : F) ^ j) • D = cT L A * X * A := by
  first | exact @GlobalTheory.CongTrans.congK_transitive | exact GlobalTheory.CongTrans.congK_transitive | (intros; apply GlobalTheory.CongTrans.congK_transitive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumStabilizerBetweenLatticeStabilizers
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DatumStab

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ}

theorem mem_smul_iff {n : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (A : Submodule L.O (Fin n → E))
    (x : Fin n → E) : x ∈ g • A ↔ g.symm x ∈ A := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [LinearEquiv.smul_def] using hy
  · intro h
    exact ⟨_, h, by simp [LinearEquiv.smul_def]⟩

theorem smul_eq_iff {n : ℕ} (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (A : Submodule L.O (Fin n → E)) :
    g • A = A ↔ ∀ x, g x ∈ A ↔ x ∈ A := by
  constructor
  · intro h x
    conv_lhs => rw [← h]
    simp [mem_smul_iff]
  · intro h
    ext x
    rw [mem_smul_iff, ← h]
    simp

theorem perp_iff {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hg : g ∈ isomG L Hm) {Y : Submodule E (Fin n → E)} (hY : ∀ y ∈ Y, g y = y) (x : Fin n → E) :
    g x ∈ perp L Hm Y ↔ x ∈ perp L Hm Y := by
  have h : ∀ y ∈ Y, hf L Hm (g x) y = hf L Hm x y := fun y hy => by
    conv_lhs => rw [← hY y hy]
    exact hg x y
  exact ⟨fun H y hy => (h y hy).symm.trans (H y hy), fun H y hy => (h y hy).trans (H y hy)⟩

theorem sub_iff {n : ℕ} {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    {Y : Submodule E (Fin n → E)} (hY : ∀ y ∈ Y, g y = y) (x : Fin n → E) : g x ∈ Y ↔ x ∈ Y := by
  constructor
  · intro h
    have := g.injective (hY _ h)
    rwa [← this]
  · intro h
    rwa [hY x h]

theorem complementGroup_fixes_frameSpan (S : Frames L r k) {h : S.GLV} (hh : h ∈ S.H0) : ∀ y ∈ S.ME, h y = y := fun y hy => by
  have := hh.2.2 y hy
  rwa [Submodule.mem_bot, sub_eq_zero] at this

theorem spanTo_mono (S : Frames L r k) (g : Fin (r + 1) → S.V) : S.spanTo g r ≤ S.spanTo g (r + 1) :=
  Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < r) => Nat.lt_succ_of_lt hi)

theorem X_le (S : Frames L r k) : S.spanTo S.f r ≤ S.ME := (spanTo_mono S _).trans le_sup_left

theorem X'_le (S : Frames L r k) : S.spanTo S.f' r ≤ S.ME := (spanTo_mono S _).trans le_sup_right

theorem inner_iff (S : Frames L r k) {g : Fin (r + 1) → S.V} {A Λ₀ : Submodule L.O S.V} {n : S.GLV}
    (hn : n ∈ S.Nof g)
    (hA : ∀ x, x ∈ A ↔ ∃ y ∈ Λ₀, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r) (x : S.V) :
    x ∈ A ↔ ∃ y ∈ n • Λ₀, y ∈ perp L S.Hm (S.spanTo g r) ∧ y - x ∈ S.spanTo g r := by
  obtain ⟨h1, h2⟩ := hn.2
  rw [hA]
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨n y, by simpa [mem_smul_iff] using hy, (h1 y).2 hp, ?_⟩
    have := Submodule.add_mem _ (h2 y hp) hx
    simpa using this
  · rintro ⟨y, hy, hp, hx⟩
    rw [mem_smul_iff] at hy
    have hp' : n.symm y ∈ perp L S.Hm (S.spanTo g r) := (h1 _).1 (by simpa using hp)
    refine ⟨_, hy, hp', ?_⟩
    have := Submodule.sub_mem _ hx (h2 _ hp')
    simpa using this

theorem stab_inner (S : Frames L r k) {A Λ : Submodule L.O S.V} {X : Submodule E S.V} (hX : X ≤ S.ME)
    (hA : ∀ x, x ∈ A ↔ ∃ y ∈ Λ, y ∈ perp L S.Hm X ∧ y - x ∈ X)
    {h : S.GLV} (hh : h ∈ S.H0) (hΛ : h • Λ = Λ) : h • A = A := by
  have hfix : ∀ y ∈ X, h y = y := fun y hy => complementGroup_fixes_frameSpan S hh y (hX hy)
  rw [smul_eq_iff] at hΛ ⊢
  intro x
  rw [hA, hA]
  constructor
  · rintro ⟨y, hy, hp, hx⟩
    obtain ⟨y, rfl⟩ := h.surjective y
    rw [← map_sub, sub_iff hfix] at hx
    exact ⟨y, (hΛ y).1 hy, (perp_iff hh.1 hfix y).1 hp, hx⟩
  · rintro ⟨y, hy, hp, hx⟩
    refine ⟨h y, (hΛ y).2 hy, (perp_iff hh.1 hfix y).2 hp, ?_⟩
    rwa [← map_sub, sub_iff hfix]

theorem stab_graph (S : Frames L r k) {Λ : Submodule L.O S.V}
    {h : S.GLV} (hh : h ∈ S.H0) (hΛ : h • Λ = Λ) : h • S.graphOf Λ = S.graphOf Λ := by
  have hfix : ∀ y ∈ S.X, h y = y := fun y hy => complementGroup_fixes_frameSpan S hh y (X_le S hy)
  have hfix' : ∀ y ∈ S.X', h y = y := fun y hy => complementGroup_fixes_frameSpan S hh y (X'_le S hy)
  rw [smul_eq_iff] at hΛ
  have hth : ∀ x, S.InTh Λ (h x) ↔ S.InTh Λ x := fun x => by
    constructor
    · rintro ⟨y, hy, hx⟩
      obtain ⟨y, rfl⟩ := h.surjective y
      rw [← map_smul] at hx
      exact ⟨y, (hΛ y).1 hy, h.injective hx⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨h y, (hΛ y).2 hy, map_smul _ _ _⟩
  have key : ∀ p : S.V × S.V, h • p ∈ S.graphOf Λ ↔ p ∈ S.graphOf Λ := by
    rintro ⟨a, b⟩
    change (h a, h b) ∈ _ ↔ _
    constructor
    · rintro ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩
      obtain ⟨y, rfl⟩ := h.surjective y
      obtain ⟨y', rfl⟩ := h.surjective y'
      simp only [← map_sub, sub_iff hfix, sub_iff hfix', hth] at h3 h4 h5
      exact ⟨y', (hΛ _).1 hy', y, (hΛ _).1 hy, (perp_iff hh.1 hfix' _).1 h1,
        (perp_iff hh.1 hfix _).1 h2, h3, h4, h5⟩
    · rintro ⟨y', hy', y, hy, h1, h2, h3, h4, h5⟩
      refine ⟨h y', (hΛ _).2 hy', h y, (hΛ _).2 hy, (perp_iff hh.1 hfix' _).2 h1,
        (perp_iff hh.1 hfix _).2 h2, ?_, ?_, ?_⟩
      · simpa only [← map_sub, sub_iff hfix'] using h3
      · simpa only [← map_sub, sub_iff hfix] using h4
      · simpa only [← map_sub, hth] using h5
  ext p
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← key, smul_inv_smul]

theorem exists_smul_mem {n : ℕ} {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) (w : Fin n → E) :
    ∃ c : F, c ≠ 0 ∧ c ∈ 𝒪[F] ∧ algebraMap F E c • w ∈ Λ := by
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hΛ.2]; trivial
  have hO : ∀ c : F, c ∈ 𝒪[F] → ∀ v ∈ Λ, algebraMap F E c • v ∈ Λ := fun c hc v hv =>
    Λ.smul_mem (⟨_, (UnramOrder.algebraMap_mem_iff L c).2 hc⟩ : L.O) hv
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, Subring.one_mem _, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, Subring.one_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨c, hc, hc', h⟩ := ha
    obtain ⟨d, hd, hd', h'⟩ := hb
    refine ⟨c * d, mul_ne_zero hc hd, Subring.mul_mem _ hc' hd', ?_⟩
    have := Λ.add_mem (hO d hd' _ h) (hO c hc' _ h')
    rwa [smul_smul, smul_smul, mul_comm (algebraMap F E d), ← smul_add, ← map_mul] at this
  | smul e a _ ha =>
    obtain ⟨c, hc, hc', h⟩ := ha
    obtain ⟨d, hd, hd', h'⟩ := StdLat.exists_mul_mem L {e}
    refine ⟨c * d, mul_ne_zero hc hd, Subring.mul_mem _ hc' hd', ?_⟩
    have := Λ.smul_mem (⟨_, h' e (by simp)⟩ : L.O) h
    have e1 : algebraMap F E (c * d) • e • a = (algebraMap F E d * e) • algebraMap F E c • a := by
      rw [smul_smul, smul_smul, map_mul]; congr 1; ring
    rw [e1]; exact this

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.H0 ⊓ stabL L Λ ≤ S.H0 ⊓ MulAction.stabilizer S.GLV d ∧ ∃ Λ₂ : Submodule L.O S.V, IsLat L Λ₂ ∧ S.H0 ⊓ MulAction.stabilizer S.GLV d ≤ S.H0 ⊓ stabL L Λ₂ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ ⟨⟨n, n'⟩, hI, hI', hn, hn', hΛ, hΛ', _, hg⟩
  obtain ⟨hsd, -, hA⟩ := StdLat.stdLat_spec L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) _ hI
  obtain ⟨-, -, hA'⟩ := StdLat.stdLat_spec L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) _ hI'
  have hc : IsCompl S.ME S.W0 := (FrameBasic.main L r k S).2.1
  have hP : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.2.2.1
  refine ⟨?_, ?_⟩
  · rintro h ⟨hh, hs⟩
    have hs' : h • Λ = Λ := hs
    refine ⟨hh, ?_⟩
    have h1 := inner_iff S hn hA
    have h2 := inner_iff S hn' hA'
    simp only at hΛ hΛ'
    rw [← hΛ] at h1
    rw [← hΛ'] at h2
    change h • d = d
    refine Prod.ext (stab_inner S (X_le S) h1 hh hs') (Prod.ext (stab_inner S (X'_le S) h2 hh hs') ?_)
    change h • d.2.2 = d.2.2
    rw [hg]
    exact stab_graph S hh hs'
  · set Λ₀ := S.stdLat S.f S.es d.1
    let P : S.V →ₗ[E] S.V := S.W0.subtype ∘ₗ Submodule.linearProjOfIsCompl S.W0 S.ME hc.symm
    have hP0 : ∀ x ∈ S.ME, P x = 0 := fun x hx => by
      have := (Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc.symm).2 hx
      exact congrArg Subtype.val this
    have hP1 : ∀ x ∈ S.W0, P x = x := fun x hx => by
      have := Submodule.linearProjOfIsCompl_apply_left hc.symm ⟨x, hx⟩
      exact congrArg Subtype.val this
    have hME : ∀ x ∈ Set.range S.f ∪ Set.range S.f', x ∈ S.ME := by
      rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, i.2, rfl⟩)
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, i.2, rfl⟩)
    refine ⟨(d.1 ⊓ S.W0.restrictScalars L.O) ⊔ Submodule.span L.O (Set.range S.f ∪ Set.range S.f'),
      ⟨Submodule.FG.sup ?_ (Submodule.fg_span ((Set.finite_range _).union (Set.finite_range _))), ?_⟩, ?_⟩
    · have hfg : (Λ₀.map (P.restrictScalars L.O)).FG := hsd.1.1.map _
      refine hfg.of_le ?_
      rintro x ⟨hx, hw⟩
      obtain ⟨y, hy, -, hyx⟩ := (hA x).1 hx
      refine ⟨y, hy, ?_⟩
      have := hP0 _ (X_le S hyx)
      rw [map_sub, sub_eq_zero, hP1 x hw] at this
      exact this
    · rw [eq_top_iff, ← hc.sup_eq_top]
      refine sup_le (sup_le ?_ ?_) fun w hw => ?_
      · refine Submodule.span_mono ?_
        rintro _ ⟨i, -, rfl⟩
        exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
      · refine Submodule.span_mono ?_
        rintro _ ⟨i, -, rfl⟩
        exact Submodule.mem_sup_right (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
      · obtain ⟨c, hc0, -, hcw⟩ := exists_smul_mem hsd.1 w
        have hw' := S.W0.smul_mem (algebraMap F E c) hw
        have h1 : algebraMap F E c • w ∈ d.1 :=
          (hA _).2 ⟨_, hcw, fun y hy => hw' y (X_le S hy), by simp⟩
        have h2 : w = algebraMap F E c⁻¹ • algebraMap F E c • w := by
          rw [smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
        rw [h2]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.mem_sup_left ⟨h1, hw'⟩))
    · rintro h ⟨hh, hs⟩
      have hs' : h • d = d := hs
      have h1 : h • d.1 = d.1 := congrArg Prod.fst hs'
      refine ⟨hh, ?_⟩
      change h • _ = _
      rw [Submodule.smul_sup']
      congr 1
      · rw [smul_eq_iff] at h1 ⊢
        intro x
        exact and_congr (h1 x) (perp_iff hh.1 (complementGroup_fixes_frameSpan S hh) x)
      · rw [smul_eq_iff]
        intro x
        have hsub : ∀ z ∈ Submodule.span L.O (Set.range S.f ∪ Set.range S.f'), h z = z := fun z hz =>
          complementGroup_fixes_frameSpan S hh z ((Submodule.span_le.2 hME : _ ≤ S.ME.restrictScalars L.O) hz)
        constructor
        · intro hx
          have := h.injective (hsub _ hx)
          rwa [← this]
        · intro hx
          rwa [hsub x hx]

end GlobalTheory.HL.DatumStab
end

