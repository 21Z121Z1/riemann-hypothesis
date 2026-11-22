import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelGenB
section
noncomputable section

namespace Formalism.MainNotions.BridgeLevelGenB

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F]

theorem val_int (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) = v.intValuation a := by
  rw [PI.WAU.val_algebraMap_F, valuation_of_algebraMap]

theorem exists_int_close (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) (hx : Valued.v x ≤ 1)
    {g : 𝓞 F} (hg : g ≠ 0) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < v.intValuation g := by
  have hγ : v.intValuation g ≠ 0 := intValuation_ne_zero v g hg
  set w : v.adicCompletion F := algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F g) with hw
  have hwv : Valued.v w = v.intValuation g := val_int v g
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hwv
    exact hγ hwv.symm
  have hr0 : (Valued.v : Valuation (v.adicCompletion F) _).restrict w ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact hw0
  have hnhds : {y : v.adicCompletion F | Valued.v (y - x) < Valued.v w} ∈ 𝓝 x := by
    rw [Valued.mem_nhds]
    exact ⟨Units.mk0 _ hr0, fun y hy => (Valuation.restrict_lt_iff _).1 hy⟩
  obtain ⟨_, hy, ⟨k, rfl⟩⟩ :=
    mem_closure_iff_nhds.mp ((denseRange_algebraMap (R := 𝓞 F) F v) x) _ hnhds
  simp only [Set.mem_ofPred_eq] at hy
  rw [hwv] at hy
  have hg1 : v.intValuation g ≤ 1 := intValuation_le_one v g
  have hk : v.valuation F k ≤ 1 := by
    rw [← PI.WAU.val_algebraMap_F]
    calc Valued.v (algebraMap F (v.adicCompletion F) k)
        = Valued.v ((algebraMap F (v.adicCompletion F) k - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap F (v.adicCompletion F) k - x)) (Valued.v x) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le (hy.le.trans hg1) hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk (Units.mk0 _ hγ)
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) k -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < v.intValuation g := by
    rw [← map_sub, PI.WAU.val_algebraMap_F, ← Valuation.map_neg, neg_sub]
    simpa using ha
  calc Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
      = Valued.v ((x - algebraMap F (v.adicCompletion F) k) + (algebraMap F (v.adicCompletion F) k -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < _ := by
      refine max_lt ?_ h2
      rw [← Valuation.map_neg, neg_sub]; exact hy

theorem dense_mod (g : ℕ) (hg : 1 ≤ g) (y : FiniteAdeleRing (𝓞 F) F) (hy : y ∈ Formalism.UG.intAd F) :
    ∃ s : 𝓞 F, ∃ c ∈ Formalism.UG.intAd F,
      y = algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F s) + (g : FiniteAdeleRing (𝓞 F) F) * c := by
  classical
  set gO : 𝓞 F := (g : 𝓞 F) with hgO
  have hg0 : gO ≠ 0 := by rw [hgO]; exact Nat.cast_ne_zero.2 (by omega)
  have hI : Ideal.span {gO} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg0
  set T := (Ideal.finite_factors hI).toFinset with hT
  have hyv : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (y v) ≤ 1 :=
    fun v => (mem_adicCompletionIntegers (𝓞 F) F v).1 (hy v)
  choose a ha using fun v : HeightOneSpectrum (𝓞 F) => exists_int_close v (y v) (hyv v) hg0
  set k : HeightOneSpectrum (𝓞 F) → ℕ :=
    fun v => (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {gO})).factors with hk
  obtain ⟨s, hs⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) k
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a v.1)
  have hval : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) ≤ v.intValuation gO := by
    intro v
    by_cases hv : v ∈ T
    · have h1 := hs v hv
      have h2 : v.intValuation (s - a v) ≤ v.intValuation gO := by
        rw [intValuation_if_neg v hg0]
        exact (intValuation_le_pow_iff_mem v _ _).2 h1
      have h3 : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a v)) -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) ≤ v.intValuation gO := by
        rw [← map_sub, ← map_sub, val_int, ← Valuation.map_neg, neg_sub]
        exact h2
      calc Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))
          = Valued.v ((y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a v))) +
              (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a v)) -
                algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))) := by ring_nf
        _ ≤ max _ _ := Valuation.map_add _ _ _
        _ ≤ _ := max_le (ha v).le h3
    · have hgv : gO ∉ v.asIdeal := by
        intro hm
        apply hv
        rw [hT, Set.Finite.mem_toFinset]
        show v.asIdeal ∣ Ideal.span {gO}
        rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
        exact hm
      have h1 : v.intValuation gO = 1 :=
        le_antisymm (intValuation_le_one v gO) (not_lt.1 fun h => hgv ((intValuation_lt_one_iff_mem v gO).1 h))
      rw [h1]
      calc Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))
          ≤ max (Valued.v (y v)) (Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))) :=
            Valuation.map_sub _ _ _
        _ ≤ 1 := max_le (hyv v) (by rw [val_int]; exact intValuation_le_one v s)
  have hgF : algebraMap (𝓞 F) F gO ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]; exact hg0
  refine ⟨s, algebraMap F _ (algebraMap (𝓞 F) F gO)⁻¹ *
    (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F s)), ?_, ?_⟩
  · intro v
    show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F gO)⁻¹ *
      (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) ∈ _
    rw [mem_adicCompletionIntegers, map_mul, map_inv₀, map_inv₀, val_int]
    have hne : v.intValuation gO ≠ 0 := intValuation_ne_zero v gO hg0
    calc (v.intValuation gO)⁻¹ * Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))
        ≤ (v.intValuation gO)⁻¹ * v.intValuation gO := by gcongr; exact hval v
      _ = 1 := inv_mul_cancel₀ hne
  · have e : (g : FiniteAdeleRing (𝓞 F) F) = algebraMap F _ (algebraMap (𝓞 F) F gO) := by
      rw [hgO, map_natCast, map_natCast]
    rw [e, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hgF, map_one, one_mul]
    ring

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem dense_modE (g : ℕ) (hg : 1 ≤ g) (a : E ⊗[F] Af F) (ha : a ∈ IntAf F E) :
    ∃ b ∈ Formalism.UG.intOE E, ∃ c ∈ IntAf F E, a = b ⊗ₜ[F] (1 : Af F) + (g : E ⊗[F] Af F) * c := by
  have gen1 : ∀ b ∈ Formalism.UG.intOE E, b ⊗ₜ[F] (1 : Af F) ∈ IntAf F E := fun b hb =>
    Subring.subset_closure (Or.inl ⟨⟨b, hb⟩, rfl⟩)
  have gen2 : ∀ y ∈ Formalism.UG.intAd F, (1 : E) ⊗ₜ[F] y ∈ IntAf F E := fun y hy =>
    Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  have hgI : (g : E ⊗[F] Af F) ∈ IntAf F E := natCast_mem _ g
  induction ha using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨b, hb⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
    · exact ⟨b, hb, 0, zero_mem _, by simp⟩
    · obtain ⟨s, c, hc, e⟩ := dense_mod g hg y hy
      have hint : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F s)) :=
        (RingOfIntegers.isIntegral_coe s).algebraMap
      refine ⟨algebraMap F E (algebraMap (𝓞 F) F s), ⟨⟨_, hint⟩, rfl⟩, (1 : E) ⊗ₜ[F] c, gen2 c hc, ?_⟩
      have e1 : (g : E ⊗[F] Af F) = (1 : E) ⊗ₜ[F] (g : Af F) := by
        rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
      have e2 : algebraMap F E (algebraMap (𝓞 F) F s) ⊗ₜ[F] (1 : Af F) =
          (1 : E) ⊗ₜ[F] algebraMap F (Af F) (algebraMap (𝓞 F) F s) := by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := Af F), TensorProduct.smul_tmul]
      show (1 : E) ⊗ₜ[F] y = _
      rw [e1, e2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.tmul_add, ← e]
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | one => exact ⟨1, one_mem _, 0, zero_mem _, by simp [Algebra.TensorProduct.one_def]⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    obtain ⟨b', hb', c', hc', rfl⟩ := hy
    refine ⟨b + b', add_mem hb hb', c + c', add_mem hc hc', ?_⟩
    rw [TensorProduct.add_tmul]; ring
  | neg x _ hx =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    refine ⟨-b, neg_mem hb, -c, neg_mem hc, ?_⟩
    rw [TensorProduct.neg_tmul]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨b, hb, c, hc, rfl⟩ := hx
    obtain ⟨b', hb', c', hc', rfl⟩ := hy
    refine ⟨b * b', mul_mem hb hb',
      b ⊗ₜ[F] (1 : Af F) * c' + c * b' ⊗ₜ[F] (1 : Af F) + (g : E ⊗[F] Af F) * c * c', ?_, ?_⟩
    · exact add_mem (add_mem (mul_mem (gen1 b hb) hc') (mul_mem hc (gen1 b' hb'))) (mul_mem (mul_mem hgI hc) hc')
    · rw [show (b * b') ⊗ₜ[F] (1 : Af F) = b ⊗ₜ[F] (1 : Af F) * b' ⊗ₜ[F] (1 : Af F) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
      ring

end Formalism.MainNotions.BridgeLevelGenB

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLevelIdx
section
noncomputable section

namespace Formalism.MainNotions.BridgeLevelIdx

open MeasureTheory Formalism.MainNotions.S Matrix
open scoped ENNReal TensorProduct

variable (I : AutInst)

def LevelGen (g : ℕ) : Prop :=
  ∃ (m : ℕ) (l : Fin m → (Fin I.n → I.E ⊗[I.F] Af I.F)) (S : Finset (Fin I.n → I.E ⊗[I.F] Af I.F)),
    m ≤ I.n ∧ S.card ≤ g ^ (2 * I.f * I.n) ∧ (∀ j, l j ∈ I.Lf) ∧
    (∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • l j + (g : I.E ⊗[I.F] Af I.F) • z) ∧
    ∀ y ∈ I.Lf, ∃ s ∈ S, ∃ z ∈ I.Lf, y = s + (g : I.E ⊗[I.F] Af I.F) • z

variable {I}

theorem lf_csmul (a : IntAf I.F I.E) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ I.Lf) :
    (a : I.E ⊗[I.F] Af I.F) • z ∈ I.Lf :=
  I.Lf.smul_mem a hz

theorem kset_mulVec {x : I.Gf} (hx : x ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x *ᵥ y ∈ I.Lf :=
  (hx y).1 hy

theorem kset_inv_mulVec {x : I.Gf} (hx : x ∈ I.Kset) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x⁻¹ *ᵥ y ∈ I.Lf := by
  have h : x⁻¹ ∈ I.Kset := by
    show ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_inv]
    exact (Formalism.UG.stabGL I.Lf).inv_mem hx
  exact (h y).1 hy

theorem kset_mul {x x' : I.Gf} (hx : x ∈ I.Kset) (hx' : x' ∈ I.Kset) : x⁻¹ * x' ∈ I.Kset := by
  show ((x⁻¹ * x' : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf
  rw [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (Formalism.UG.stabGL I.Lf).mul_mem ((Formalism.UG.stabGL I.Lf).inv_mem hx) hx'

theorem kg_of_gen {g : ℕ} {m : ℕ} {l : Fin m → (Fin I.n → I.E ⊗[I.F] Af I.F)}
    (hgen : ∀ y ∈ I.Lf, ∃ (a : Fin m → IntAf I.F I.E) (z : Fin I.n → I.E ⊗[I.F] Af I.F), z ∈ I.Lf ∧
      y = ∑ j, (a j : I.E ⊗[I.F] Af I.F) • l j + (g : I.E ⊗[I.F] Af I.F) • z)
    {x x' : I.Gf} (hx : x ∈ I.Kset) (hx' : x' ∈ I.Kset)
    (hd : ∀ j, ∃ w ∈ I.Lf, (I.fmat x' - I.fmat x) *ᵥ l j = (g : I.E ⊗[I.F] Af I.F) • w) :
    x⁻¹ * x' ∈ I.Kg g := by
  refine ⟨kset_mul hx hx', fun y hy => ?_⟩
  set D := I.fmat x' - I.fmat x with hD

  have hDy : ∃ w ∈ I.Lf, D *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • w := by
    obtain ⟨a, z, hz, rfl⟩ := hgen y hy
    have hsum : ∀ s : Finset (Fin m), ∃ w ∈ I.Lf,
        D *ᵥ (∑ j ∈ s, (a j : I.E ⊗[I.F] Af I.F) • l j) = (g : I.E ⊗[I.F] Af I.F) • w := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨0, I.Lf.zero_mem, by simp⟩
      | insert j s hj ih =>
        obtain ⟨w, hw, e⟩ := ih
        obtain ⟨w', hw', e'⟩ := hd j
        refine ⟨(a j : I.E ⊗[I.F] Af I.F) • w' + w, I.Lf.add_mem (lf_csmul _ hw') hw, ?_⟩
        rw [Finset.sum_insert hj, Matrix.mulVec_add, Matrix.mulVec_smul, e, e', smul_add, smul_comm]
    obtain ⟨w, hw, e⟩ := hsum Finset.univ
    refine ⟨w + D *ᵥ z, I.Lf.add_mem hw ?_, ?_⟩
    · rw [hD, Matrix.sub_mulVec]
      exact I.Lf.sub_mem (kset_mulVec hx' hz) (kset_mulVec hx hz)
    · rw [Matrix.mulVec_add, e, Matrix.mulVec_smul, smul_add]
  obtain ⟨w, hw, e⟩ := hDy
  refine ⟨I.fmat x⁻¹ *ᵥ w, kset_inv_mulVec hx hw, ?_⟩
  have hm : I.fmat (x⁻¹ * x') - 1 = I.fmat x⁻¹ * D := by
    have h1 : I.fmat (x⁻¹ * x') = I.fmat x⁻¹ * I.fmat x' := by
      simp only [AutInst.fmat, Subgroup.coe_mul, Units.val_mul]
    have h2 : I.fmat x⁻¹ * I.fmat x = 1 := by
      simp only [AutInst.fmat, Subgroup.coe_inv, Units.inv_mul]
    rw [hD, Matrix.mul_sub, h1, h2]
  rw [hm, ← Matrix.mulVec_mulVec, e, Matrix.mulVec_smul]

theorem card_reduction {g : ℕ} (hg : 1 ≤ g) (hG : LevelGen I g) :
    ∃ (α : Type) (_ : Fintype α) (ρ : I.Gf → α), Fintype.card α ≤ g ^ (2 * I.n ^ 2 * I.f) ∧
      ∀ x ∈ I.Kset, ∀ x' ∈ I.Kset, ρ x = ρ x' → x⁻¹ * x' ∈ I.Kg g := by
  classical
  obtain ⟨m, l, S, hm, hS, hl, hgen, hrep⟩ := hG
  obtain ⟨s0, hs0, -⟩ := hrep 0 I.Lf.zero_mem
  let r : (Fin I.n → I.E ⊗[I.F] Af I.F) → S := fun v =>
    if h : v ∈ I.Lf then ⟨(hrep v h).choose, (hrep v h).choose_spec.1⟩ else ⟨s0, hs0⟩
  have hr : ∀ v ∈ I.Lf, ∃ z ∈ I.Lf, v = (r v : Fin I.n → I.E ⊗[I.F] Af I.F) + (g : I.E ⊗[I.F] Af I.F) • z := by
    intro v hv
    simp only [r, dif_pos hv]
    exact (hrep v hv).choose_spec.2
  refine ⟨Fin m → S, inferInstance, fun x j => r (I.fmat x *ᵥ l j), ?_, ?_⟩
  · rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    calc S.card ^ m ≤ (g ^ (2 * I.f * I.n)) ^ m := Nat.pow_le_pow_left hS m
      _ ≤ (g ^ (2 * I.f * I.n)) ^ I.n := Nat.pow_le_pow_right (pow_pos (by omega) _) hm
      _ = g ^ (2 * I.n ^ 2 * I.f) := by rw [← pow_mul]; congr 1; ring
  · intro x hx x' hx' hρ
    refine kg_of_gen hgen hx hx' fun j => ?_
    have e : r (I.fmat x *ᵥ l j) = r (I.fmat x' *ᵥ l j) := congrFun hρ j
    obtain ⟨z, hz, ez⟩ := hr _ (kset_mulVec hx (hl j))
    obtain ⟨z', hz', ez'⟩ := hr _ (kset_mulVec hx' (hl j))
    refine ⟨z' - z, I.Lf.sub_mem hz' hz, ?_⟩
    rw [Matrix.sub_mulVec, ez, ez', e, smul_sub]
    abel

theorem levelIdx_holds (μf : Measure I.Gf) [μf.IsMulLeftInvariant] {g : ℕ} (hg : 1 ≤ g) (hG : LevelGen I g) :
    μf I.Kset ≤ ((g ^ (2 * I.n ^ 2 * I.f) : ℕ) : ℝ≥0∞) * μf (I.Kg g) := by
  classical
  obtain ⟨α, _, ρ, hcard, hρ⟩ := card_reduction hg hG
  let rp : α → I.Gf := fun a => if h : ∃ x ∈ I.Kset, ρ x = a then h.choose else 1
  have hcov : I.Kset ⊆ ⋃ a, (fun h => rp a * h) '' I.Kg g := by
    intro x hx
    have hex : ∃ x₀ ∈ I.Kset, ρ x₀ = ρ x := ⟨x, hx, rfl⟩
    refine Set.mem_iUnion.2 ⟨ρ x, (rp (ρ x))⁻¹ * x, ?_, by simp⟩
    have e : rp (ρ x) = hex.choose := by simp only [rp, dif_pos hex]
    rw [e]
    exact hρ _ hex.choose_spec.1 x hx hex.choose_spec.2
  have hone : ∀ a, μf ((fun h => rp a * h) '' I.Kg g) = μf (I.Kg g) := by
    intro a
    rw [Set.image_mul_left]
    exact measure_preimage_mul μf _ _
  calc μf I.Kset ≤ μf (⋃ a, (fun h => rp a * h) '' I.Kg g) := measure_mono hcov
    _ ≤ ∑ a, μf ((fun h => rp a * h) '' I.Kg g) := measure_iUnion_fintype_le _ _
    _ = (Fintype.card α : ℝ≥0∞) * μf (I.Kg g) := by
        simp only [hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by gcongr

end Formalism.MainNotions.BridgeLevelIdx

end
end

