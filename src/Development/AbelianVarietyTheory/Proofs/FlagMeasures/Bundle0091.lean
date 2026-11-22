import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.HyperbolicPlaceProducts.SubgroupIndexCounts.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0089
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SymmetricFlagBasisVectorsApplyCentre
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0087
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardLatticesNearReferenceLatticeLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.NearCount

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem line_cyclic (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ u ∈ line (I : Submodule (𝓞 K) K) v,
      line (I : Submodule (𝓞 K) K) v ≤ n • line (I : Submodule (𝓞 K) K) v ⊔ Submodule.span (𝓞 K) {u} := by
  obtain ⟨a, J, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  let φ : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V ((algebraMap (𝓞 K) K a)⁻¹ • v)
  have hφ : line (I : Submodule (𝓞 K) K) v = Submodule.map φ J := by
    ext x
    simp only [line, Submodule.mem_map, hI, FractionalIdeal.mem_coe, FractionalIdeal.mem_singleton_mul,
      FractionalIdeal.mem_coeIdeal, φ, LinearMap.toSpanSingleton_apply, LinearMap.restrictScalars_apply]
    constructor
    · rintro ⟨y, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
    · rintro ⟨z, hz, rfl⟩
      refine ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      rw [mul_comm, mul_smul, algebraMap_smul]
  rw [hφ]
  by_cases hJ : J = ⊥
  · exact ⟨0, zero_mem _, by simp [hJ]⟩
  obtain ⟨b, hb⟩ := IsDedekindDomain.exists_sup_span_eq (I := n * J) (J := J) Ideal.mul_le_right
    (mul_ne_zero hn hJ)
  have hbJ : b ∈ J := by
    rw [← hb]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
  refine ⟨φ b, Submodule.mem_map_of_mem hbJ, ?_⟩
  conv_lhs => rw [← hb]
  rw [Submodule.map_sup, ← Ideal.smul_eq_mul, Submodule.map_smul'']
  refine sup_le_sup_left ?_ _
  rw [← Ideal.submodule_span_eq, Submodule.map_span, Set.image_singleton]

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem count_between (P : Submodule (𝓞 K) V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (e : ℕ) (v : Fin e → V)
    (hv : ∀ i, v i ∈ P) (hP : P ≤ n • P ⊔ Submodule.span (𝓞 K) (Set.range v)) :
    {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P}.encard ≤ ((Ideal.absNorm n ^ (e * e) : ℕ) : ℕ∞) := by
  let S : Submodule (𝓞 K) P := (n • P).comap P.subtype
  let w : Fin e → P ⧸ S := fun i => S.mkQ ⟨v i, hv i⟩
  have hS : ∀ a ∈ n, ∀ y : P ⧸ S, a • y = 0 := by
    intro a ha y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul ha x.2
  have hgen : ∀ y : P ⧸ S, ∃ c : Fin e → 𝓞 K, y = ∑ i, c i • w i := by
    intro y
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 (hP x.2)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 ht
    refine ⟨c, ?_⟩
    simp only [w, ← map_smul, ← map_sum]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    show ((x - ∑ i, c i • (⟨v i, hv i⟩ : P) : P) : V) ∈ n • P
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, ← hst, add_sub_cancel_right]
    exact hs
  haveI : Finite (𝓞 K ⧸ n) := Ideal.finiteQuotientOfFreeOfNeBot n hn
  let f : (Fin e → 𝓞 K ⧸ n) → P ⧸ S := fun c => ∑ i, (c i).out • w i
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨c, rfl⟩ := hgen y
    refine ⟨fun i => Ideal.Quotient.mk n (c i), Finset.sum_congr rfl fun i _ => ?_⟩
    rw [← sub_eq_zero, ← sub_smul]
    apply hS
    rw [← Ideal.Quotient.eq]
    exact Quotient.out_eq _
  haveI : Finite (P ⧸ S) := Finite.of_surjective f hf
  have hcard : Nat.card (P ⧸ S) ≤ Ideal.absNorm n ^ e := by
    refine (Nat.card_le_card_of_surjective f hf).trans (le_of_eq ?_)
    rw [Nat.card_fun, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    simp
  have hw : Submodule.span (𝓞 K) (Set.range w) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨c, rfl⟩ := hgen y
    exact (Submodule.mem_span_range_iff_exists_fun _).2 ⟨c, rfl⟩
  have hc := Formalism.SLP.P.card_submodules_le_of_dedekind (𝓞 K) (P ⧸ S) e w hw
  haveI : Finite (Submodule (𝓞 K) (P ⧸ S)) := Finite.of_injective _ SetLike.coe_injective
  have hinj : Set.InjOn (fun L : Submodule (𝓞 K) V => (L.comap P.subtype).map S.mkQ)
      {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P} := by
    have key : ∀ L : Submodule (𝓞 K) V, n • P ≤ L → L ≤ P →
        (((L.comap P.subtype).map S.mkQ).comap S.mkQ).map P.subtype = L := by
      intro L h1 h2
      rw [Submodule.comap_map_mkQ, sup_eq_right.2 (Submodule.comap_mono h1),
        Submodule.map_comap_subtype, inf_eq_right.2 h2]
    intro L hL L' hL' h
    rw [← key L hL.1 hL.2, ← key L' hL'.1 hL'.2]
    simp only at h
    rw [h]
  refine (Set.encard_le_encard_of_injOn (t := Set.univ) (Set.mapsTo_univ _ _) hinj).trans ?_
  rw [Set.encard_univ, ENat.card_eq_coe_natCard, Nat.cast_le, pow_mul]
  exact hc.trans (Nat.pow_le_pow_left hcard e)

theorem smul_injective (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Function.Injective fun P : Submodule (𝓞 K) V => m • P := by
  obtain ⟨a, ham, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨J, hJ⟩ : m ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ham)
  have key : ∀ P Q : Submodule (𝓞 K) V, m • P = m • Q → P ≤ Q := by
    intro P Q h x hx
    have h2 : Ideal.span {a} • P = Ideal.span {a} • Q := by
      rw [hJ, mul_comm, Submodule.mul_smul, Submodule.mul_smul, h]
    have h3 : a • x ∈ Ideal.span {a} • Q := h2 ▸ Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hx
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h3
    obtain ⟨y, hy, hxy⟩ := h3
    have ha' : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    rw [← algebraMap_smul K a y, ← algebraMap_smul K a x] at hxy
    rwa [← smul_right_injective V ha' hxy]
  intro P Q h
  exact le_antisymm (key P Q h) (key Q P h.symm)

theorem exists_gens [StarRing K] {H : HermSpace K V} {r : ℕ} (N : NF H r) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ v : Fin (2 * r + 1) → V, (∀ i, v i ∈ N.P0) ∧ N.P0 ≤ n • N.P0 ⊔ Submodule.span (𝓞 K) (Set.range v) := by
  choose u hu hu' using fun (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) => line_cyclic I v n hn
  let d : FractionalIdeal (𝓞 K)⁰ K := N.𝔡
  let I : Option (Fin r ⊕ Fin r) → FractionalIdeal (𝓞 K)⁰ K := fun o => o.elim 1
    (Sum.elim (fun a => d ^ (-((r : ℤ) - a.val)))
      fun a => if a.val < N.j then d ^ (-((r : ℤ) - a.val)) else d ^ ((r : ℤ) - a.val))
  let x : Option (Fin r ⊕ Fin r) → V := fun o => o.elim N.F.z
    (Sum.elim (fun a => N.F.e a.castSucc) fun a => if a.val < N.j then N.F'.e a.castSucc else N.ist a)
  have hP : N.P0 = ⨆ o, line (I o : Submodule (𝓞 K) K) (x o) := by
    apply le_antisymm
    · refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a h => ?_)) ?_) (iSup₂_le fun a h => ?_)
      · exact le_iSup_of_le (some (Sum.inl a)) le_rfl
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
        rfl
      · refine le_iSup_of_le none (le_of_eq ?_)
        simp only [I, x, Option.elim, FractionalIdeal.coe_one]
      · refine le_iSup_of_le (some (Sum.inr a)) (le_of_eq ?_)
        simp only [I, x, Option.elim, Sum.elim_inr, if_neg (not_lt.2 h)]
        rfl
    · refine iSup_le ?_
      rintro (_ | a | a)
      · simp only [I, x, Option.elim, FractionalIdeal.coe_one]
        exact le_sup_of_le_left le_sup_right
      · refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left ?_))
        exact le_iSup_of_le a le_rfl
      · by_cases h : a.val < N.j
        · simp only [I, x, Option.elim, Sum.elim_inr, if_pos h]
          refine le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right ?_))
          exact le_iSup₂_of_le a h le_rfl
        · simp only [I, x, Option.elim, Sum.elim_inr, if_neg h]
          refine le_sup_of_le_right ?_
          exact le_iSup₂_of_le a (not_lt.1 h) le_rfl
  have hle : ∀ o, line (I o : Submodule (𝓞 K) K) (x o) ≤ N.P0 := fun o => by
    rw [hP]; exact le_iSup (fun o => line (I o : Submodule (𝓞 K) K) (x o)) o
  let σ : Fin (2 * r + 1) ≃ Option (Fin r ⊕ Fin r) := Fintype.equivOfCardEq (by simp; ring)
  refine ⟨fun i => u (I (σ i)) (x (σ i)), fun i => hle _ (hu _ _), ?_⟩
  conv_lhs => rw [hP]
  refine iSup_le fun o => (hu' _ _).trans (sup_le_sup (Submodule.smul_mono le_rfl (hle o)) ?_)
  exact Submodule.span_mono (Set.singleton_subset_iff.2 ⟨σ.symm o, by simp⟩)

end GlobalTheory.DegCnt.NearCount

theorem GlobalTheory.DegCnt.NearCount.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ → ((({P : Submodule (𝓞 K) V | 𝔪 • N.P0 ≤ P ∧ 𝔪 • P ≤ N.P0}).encard : ℕ∞) : ℝ≥0∞) ≤ (Ideal.absNorm 𝔪 : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H _ r N m hm
  have hn : m * m ≠ ⊥ := mul_ne_zero hm hm
  obtain ⟨v, hv, hP⟩ := GlobalTheory.DegCnt.NearCount.exists_gens N (m * m) hn
  have h1 := GlobalTheory.DegCnt.NearCount.count_between N.P0 (m * m) hn _ v hv hP
  have h2 : ({P : Submodule (𝓞 K) V | m • N.P0 ≤ P ∧ m • P ≤ N.P0}).encard ≤
      {L : Submodule (𝓞 K) V | (m * m) • N.P0 ≤ L ∧ L ≤ N.P0}.encard := by
    refine Set.encard_le_encard_of_injOn (f := fun P => m • P) ?_
      (GlobalTheory.DegCnt.NearCount.smul_injective m hm).injOn
    rintro P ⟨h, h'⟩
    exact ⟨by rw [Submodule.mul_smul]; exact Submodule.smul_mono le_rfl h, h'⟩
  refine (ENat.toENNReal_le.2 (h2.trans h1)).trans (le_of_eq ?_)
  rw [map_mul, ← sq, ← pow_mul, ← sq]
  simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjInt
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.PrimScale

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sum_left (L : LocE F E) {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (x : Fin m → Fin n → E) (c : Fin m → E) (y : Fin n → E) :
    hf L Hm (∑ i, c i • x i) y = ∑ i, c i * hf L Hm (x i) y := by
  simp only [hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_comm

theorem hf_cj (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by
  simp only [hf, map_sum, map_mul, L.cj_cj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have : L.cj (Hm b a) = Hm a b := congrFun (congrFun h a) b
  rw [this]; ring

theorem gramT_rmul (L : LocE F E) {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x : Fin m → Fin n → E) (A : Matrix (Fin m) (Fin m) E) :
    gramT L Hm (rmul x A) = cT L A * gramT L Hm x * A := by
  ext a b
  have h1 : ∀ y, hf L Hm y (∑ i, A i a • x i) = ∑ i, L.cj (A i a) * hf L Hm y (x i) := by
    intro y
    rw [← hf_cj L h, hf_sum_left]
    simp only [map_sum, map_mul, hf_cj L h]
  simp only [gramT, rmul, Matrix.of_apply, hf_sum_left, h1, Matrix.mul_apply, cT]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem isHerm_gramT (L : LocE F E) {n m : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (x : Fin m → Fin n → E) : IsHerm L (gramT L Hm x) := by
  ext a b
  exact hf_cj L h _ _

theorem cT_mul (L : LocE F E) {m : ℕ} (A B : Matrix (Fin m) (Fin m) E) :
    cT L (A * B) = cT L B * cT L A := by
  ext a b
  simp only [cT, Matrix.mul_apply, map_sum, map_mul, mul_comm]

theorem cT_cT (L : LocE F E) {m : ℕ} (A : Matrix (Fin m) (Fin m) E) : cT L (cT L A) = A := by
  ext a b
  exact L.cj_cj _

theorem cT_one (L : LocE F E) {m : ℕ} : cT L (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  ext a b
  simp only [cT, Matrix.one_apply, eq_comm (a := b)]
  split_ifs <;> simp

theorem rmul_rmul {n m : ℕ} (x : Fin m → Fin n → E) (A B : Matrix (Fin m) (Fin m) E) :
    rmul (rmul x A) B = rmul x (A * B) := by
  funext j
  simp only [rmul, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]

theorem rmul_one {n m : ℕ} (x : Fin m → Fin n → E) : rmul x 1 = x := by
  funext j
  simp [rmul, Matrix.one_apply]

theorem isIntM_mul (L : LocE F E) {m : ℕ} {A B : Matrix (Fin m) (Fin m) E} (hA : IsIntM L A)
    (hB : IsIntM L B) : IsIntM L (A * B) := fun a b => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hA a i) (hB i b)

variable [IsNonarchimedeanLocalField F]

theorem exists_pow_mul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (e : E) :
    ∃ k : ℕ, ∀ i ≥ k, algebraMap F E ((ϖ : F) ^ i) * e ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  have he : IsIntegral F e := Algebra.IsIntegral.isIntegral e
  obtain ⟨⟨c, hc⟩, hce⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors 𝒪[F]) e he
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hc) hϖ
  refine ⟨k, fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [L.O_def]
  have h1 : IsIntegral 𝒪[F] (((u⁻¹ : (𝒪[F])ˣ) * ϖ ^ j : 𝒪[F]) • (((u : 𝒪[F]) * ϖ ^ k) • e)) :=
    IsIntegral.smul _ hce
  have h2 : ((u⁻¹ : (𝒪[F])ˣ) * ϖ ^ j : 𝒪[F]) * ((u : 𝒪[F]) * ϖ ^ k) = ϖ ^ (k + j) := by
    rw [pow_add]
    linear_combination (ϖ ^ j * ϖ ^ k) * u.inv_mul
  rw [smul_smul, h2, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E] at h1
  exact h1

theorem exists_conj_int (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) E) (hA : IsUnit A.det) :
    ∃ k : ℕ, ∀ i ≥ k, ∀ K ∈ congK L ϖ m i, IsIntM L (A * K * A⁻¹) := by
  choose k hk using fun p : Fin m × Fin m × Fin m × Fin m =>
    exists_pow_mul_mem L hϖ (A p.1 p.2.1 * A⁻¹ p.2.2.1 p.2.2.2)
  refine ⟨Finset.univ.sup k, fun i hi K hK a b => ?_⟩
  have h1 : A * K * A⁻¹ = 1 + A * (K - 1) * A⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hA]; abel
  rw [h1, Matrix.add_apply]
  refine Subring.add_mem _ ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun s _ => Subring.sum_mem _ fun r _ => ?_
    obtain ⟨c, hc, h⟩ := hK r s
    rw [Matrix.sub_apply, h]
    have := Subring.mul_mem _ (hk (a, r, s, b) i
      (le_trans (Finset.le_sup (Finset.mem_univ _)) hi)) hc
    convert this using 1
    ring

theorem cont_prim_scale : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λs, IsSD L Hm Λs → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → 2 * m + 3 ≤ n → ∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → IsIntM L (gramT L Hm (rmul x A⁻¹)) → ∃ i0 : ℕ, ∀ i ≥ i0, (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m))) * cont (hermLat L m) (horb L ϖ (gramT L Hm x) i) ≤ 2 * cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs (rmul z A⁻¹) ∧ gramT L Hm z ∈ horb L ϖ (gramT L Hm x) i} ∧ cont (tupLat L Λs m) {z : Fin m → Fin n → E | IsPrimT L Hm Λs (rmul z A⁻¹) ∧ gramT L Hm z ∈ horb L ϖ (gramT L Hm x) i} ≤ 2 * ((resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m))) * cont (hermLat L m) (horb L ϖ (gramT L Hm x) i)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λs hΛ m x hx hmn A hA hint
  obtain ⟨k, hk⟩ := exists_conj_int L hϖ A hA
  refine ⟨max k 1, fun i hi => ?_⟩
  have hO := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hq : (0 : ℝ) < resQ ϖ := by
    have := hO.2.2.2.2.2.2.1
    exact_mod_cast (by omega : 0 < resQ ϖ)
  have hAi : IsUnit (A⁻¹).det := Matrix.isUnit_nonsing_inv_det A hA
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have hAA' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  have hcA : cT L A * cT L A⁻¹ = 1 := by rw [← cT_mul, hAA', cT_one]
  have hcA' : cT L A⁻¹ * cT L A = 1 := by rw [← cT_mul, hAA, cT_one]
  have hΓ := isHerm_gramT L hH.1 x
  set O := horb L ϖ (gramT L Hm x) i with hOdef
  have hOco : IsCO (hermLat L m) O :=
    ((GlobalTheory.T.matrixCongruentOneModUniformizerPow_group_and_orbits L ϖ hϖ m i (le_of_max_le_right hi)).2.2 _ hΓ hx).1
  set B := (fun X => cT L A⁻¹ * X * A⁻¹) '' O with hBdef
  have hBco : IsCO (hermLat L m) B := ((GlobalTheory.T.hermitianMatrix_congruence_content_jacobian L ϖ hϖ m A⁻¹ hAi).2 O hOco).1
  have hback : ∀ X : Matrix (Fin m) (Fin m) E, cT L A * (cT L A⁻¹ * X * A⁻¹) * A = X := by
    intro X
    calc _ = (cT L A * cT L A⁻¹) * X * (A⁻¹ * A) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hcA, hAA', Matrix.one_mul, Matrix.mul_one]
  have hforth : ∀ X : Matrix (Fin m) (Fin m) E, cT L A⁻¹ * (cT L A * X * A) * A⁻¹ = X := by
    intro X
    calc _ = (cT L A⁻¹ * cT L A) * X * (A * A⁻¹) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hcA', hAA, Matrix.one_mul, Matrix.mul_one]
  have hOB : (fun X => cT L A * X * A) '' B = O := by
    rw [hBdef, Set.image_image]
    simp only [hback, Set.image_id']
  have hcO := ((GlobalTheory.T.hermitianMatrix_congruence_content_jacobian L ϖ hϖ m A hA).2 B hBco).2
  rw [hOB] at hcO
  have hBint : ∀ X ∈ B, X ∈ hermLat L m := by
    rintro _ ⟨_, ⟨K, hK, rfl⟩, rfl⟩
    have hK' := hk i (le_of_max_le_left hi) K hK
    have h1 : cT L A⁻¹ * (cT L K * gramT L Hm x * K) * A⁻¹
        = cT L (A * K * A⁻¹) * gramT L Hm (rmul x A⁻¹) * (A * K * A⁻¹) := by
      rw [gramT_rmul L hH.1, cT_mul, cT_mul]
      conv_lhs => rw [← hback (gramT L Hm x)]
      simp only [Matrix.mul_assoc]
    refine AddSubgroup.subset_closure ⟨?_, ?_⟩
    · change IsHerm L (cT L A⁻¹ * (cT L K * gramT L Hm x * K) * A⁻¹)
      rw [← gramT_rmul L hH.1, ← gramT_rmul L hH.1]
      exact isHerm_gramT L hH.1 _
    · change IsIntM L (cT L A⁻¹ * (cT L K * gramT L Hm x * K) * A⁻¹)
      rw [h1]
      exact isIntM_mul L (isIntM_mul L (fun a b => (hO.2.1 _ (hK' b a)).1) hint) hK'
  obtain ⟨hTco, hT1, hT2⟩ := GlobalTheory.T.primitiveTuples_hermitianGram_coset_content L ϖ hϖ Hm hH Λs hΛ m hmn B hBint hBco
  have hS : {z : Fin m → Fin n → E | IsPrimT L Hm Λs (rmul z A⁻¹) ∧ gramT L Hm z ∈ O}
      = (fun x => rmul x A) ''
        {z : Fin m → Fin n → E | IsPrimT L Hm Λs z ∧ gramT L Hm z ∈ B} := by
    ext z
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨rmul z A⁻¹, ⟨h1, _, h2, (gramT_rmul L hH.1 _ _).symm⟩, ?_⟩
      simp only [rmul_rmul, hAA', rmul_one]
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      refine ⟨by simpa only [rmul_rmul, hAA, rmul_one] using h1, ?_⟩
      rw [← hOB]
      exact ⟨_, h2, (gramT_rmul L hH.1 _ _).symm⟩
  have hcS := ((GlobalTheory.T.tuple_jacobian_rightMul_isometry L ϖ hϖ Hm hH Λs hΛ m).1 A hA _ hTco).2
  rw [hS, hcS, hcO, ← mul_assoc, ← zpow_add₀ hq.ne']
  have he : -(vE L ϖ (A.det * L.cj A.det) * ((n : ℤ) - m)) + -(vE L ϖ (A.det * L.cj A.det) * m)
      = -(vE L ϖ (A.det * L.cj A.det) * n) := by ring
  rw [he]
  have hp := (zpow_pos hq (-(vE L ϖ (A.det * L.cj A.det) * n))).le
  constructor
  · have := mul_le_mul_of_nonneg_left hT1 hp
    linarith
  · have := mul_le_mul_of_nonneg_left hT2 hp
    linarith

end GlobalTheory.PrimScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinrankLeFinrankInfPerpXPlus
section
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA

namespace GlobalTheory.SA

theorem finrank_le_finrank_inf_perp_xPlus {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ} (S : Submodule K V) (F : FlagD H r) :
    Module.finrank K S ≤ Module.finrank K ↥(S ⊓ perp H (xPlus F)) + (r + 1) := by
  let f : S →ₗ[K] (Fin (r + 1) → K) := (LinearMap.pi fun i => H.B.flip (F.e i)).comp S.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank K (LinearMap.range f) ≤ r + 1 :=
    (Submodule.finrank_le _).trans (by simp)
  have h3 : (LinearMap.ker f).map S.subtype = S ⊓ perp H (xPlus F) := by
    ext y
    rw [Submodule.mem_inf, xPlus_eq_span, mem_perp_span, Set.forall_mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, fun i => congrFun (LinearMap.mem_ker.1 hx) i⟩
    · rintro ⟨hy, h⟩
      exact ⟨⟨y, hy⟩, LinearMap.mem_ker.2 (funext h), rfl⟩
  rw [← h3, Submodule.finrank_map_subtype_eq]
  omega

theorem norLift_decomp : ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r), IsTransv F F' →
    Module.finrank K (norLift F F') = r + 1 ∧ norLift F F' ⊔ norLift F' F = V0 F F' ∧
    wSp F F' ⊔ norLift F F' = perp H (xPlus F) ∧ Disjoint (wSp F F') (norLift F F') ∧
    IsCompl (V0 F F') (wSp F F') := by
  intro K V _ _ _ _ _ H r F F' h
  have a1 : 2 * r + 2 ≤ Module.finrank K (norLift F F') + (r + 1) :=
    h.1.ge.trans (finrank_le_finrank_inf_perp_xPlus (V0 F F') F)
  have a2 : 2 * r + 2 ≤ Module.finrank K (norLift F' F) + (r + 1) :=
    h.symm.1.ge.trans (finrank_le_finrank_inf_perp_xPlus (V0 F' F) F')
  have hle : norLift F F' ⊔ norLift F' F ≤ V0 F F' :=
    sup_le inf_le_left (inf_le_left.trans (jointSpan_comm F F').le)
  have a3 := Submodule.finrank_sup_add_finrank_inf_eq (norLift F F') (norLift F' F)
  rw [h.disjoint_norLift.eq_bot, finrank_bot] at a3
  have a4 := Submodule.finrank_mono hle
  have a5 := h.1
  have hc : IsCompl (V0 F F') (wSp F F') := by
    have b1 := finrank_le_finrank_inf_perp_xPlus (⊤ : Submodule K V) F
    have b2 := finrank_le_finrank_inf_perp_xPlus (perp H (xPlus F)) F'
    rw [top_inf_eq, finrank_top] at b1
    rw [← wSp_eq] at b2
    have b3 := Submodule.finrank_sup_add_finrank_inf_eq (V0 F F') (wSp F F')
    rw [h.2.eq_bot, finrank_bot] at b3
    refine ⟨h.2, codisjoint_iff.2 (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_))⟩
    omega
  refine ⟨by omega, Submodule.eq_of_le_of_finrank_le hle (by omega), ?_,
    h.2.symm.mono_right inf_le_left, hc⟩
  have hw : wSp F F' ≤ perp H (xPlus F) := by rw [wSp_eq]; exact inf_le_left
  rw [norLift, ← sup_inf_assoc_of_le _ hw, hc.symm.sup_eq_top, top_inf_eq]

end GlobalTheory.SA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedLatticeInfEqAndPairingOfIsometry
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem trip_fixLat_inf_eq_and_pairing : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), ∀ p ∈ Trip H g L₀ j x x', fixLat p.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) = fixLat p.2.1.2 ⊓ rs (𝓞 K) (fixSp p.2.2) ∧ ∀ y ∈ fixLat p.1.2, ∀ y' ∈ fixLat p.2.1.2, ∃ t : 𝓞 K, H.B y (y' - p.2.2 y') = (g : K) * (t : K) := by
  intro K V _ _ _ _ _ _ _ _ H _ _ L₀ g j D₀ _ _ _ _ x x' p hp
  obtain ⟨h1, -, -, -, h5⟩ := hp
  have hmem : ∀ (Γ : Submodule (𝓞 K) (V × V)) (y : V), y ∈ fixLat Γ ↔ (y, y) ∈ Γ := fun _ _ => Iff.rfl
  refine ⟨?_, ?_⟩
  · ext y
    have hf : y ∈ rs (𝓞 K) (fixSp p.2.2) ↔ p.2.2 y = y := by
      simp [fixSp, sub_eq_zero]
    rw [Submodule.mem_inf, Submodule.mem_inf, hmem, hmem, hf, h5]
    refine and_congr_left fun h => ?_
    rw [h]
  · intro y hy y' hy'
    rw [hmem] at hy hy'
    rw [h5] at hy'
    obtain ⟨t, ht⟩ := h1.2.2.1.2.2.2.2.2.2 _ hy _ hy'
    refine ⟨-t, ?_⟩
    simp only [map_mul, map_natCast] at ht
    rw [map_sub]
    have : ((-t : 𝓞 K) : K) = -(algebraMap (𝓞 K) K t) := map_neg (algebraMap (𝓞 K) K) t
    rw [this]
    linear_combination -ht

end GlobalTheory.DegCnt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDataMassEqSumFrameClassesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDataMass_eq_sum_frameClasses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ P : S.Datum → Submodule L.O S.V → Prop, (∀ h ∈ S.St, ∀ d Λ, S.IsTerm d Λ → P d Λ → P d (h • Λ)) → (S.sumData fun d => S.mass d (P d)) = (S.sumCls fun C => S.sumData fun d => S.nT d C (P d)) ∧ ∀ h ∈ S.St, ∀ d C, S.nT d (h • C) (P d) = S.nT d C (P d) := by
  first | exact @GlobalTheory.HL.sumData_mass_eq_sumCls | exact GlobalTheory.HL.sumData_mass_eq_sumCls | (intros; apply GlobalTheory.HL.sumData_mass_eq_sumCls <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDefectClassMemTraceFirstFrameSpanStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDefectClass_mem_trace_firstFrameSpan : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → (∃ y ∈ Λ, y ∈ S.W0 ∧ S.h u y = 1) → ∀ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ x u s → ∀ y ∈ S.sat Λ₁, ∃ y₀ ∈ Λ, y₀ ∈ (S.spanTo S.f (j + 1) ⊔ S.spanTo S.f' (j + 1)) ∧ y - y₀ ∈ S.M d Λ₁ := by
  first | exact @GlobalTheory.HL.TraceRep.class_from_trace | exact GlobalTheory.HL.TraceRep.class_from_trace | (intros; apply GlobalTheory.HL.TraceRep.class_from_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermStabilizerCommensurableStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTerm_stabilizer_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → P.UW0 ⊓ LocNG.Aut τ.abelian₂ ≤ LocNG.Datum.Stab d ∧ (P.UW0 ⊓ LocNG.Aut τ.abelian₂).relIndex (LocNG.Datum.Stab d) ≠ 0 ∧ ∀ (d' : LocNG.Datum P) (τ' : Term V M r), LocNG.IsTermOver P d' τ' → (LocNG.Datum.Stab d).relIndex (LocNG.Datum.Stab d') ≠ 0 := by
  first | exact @GlobalTheory.HL.LocComm.stab_commensurable | exact GlobalTheory.HL.LocComm.stab_commensurable | (intros; apply GlobalTheory.HL.LocComm.stab_commensurable <;> assumption)
end

