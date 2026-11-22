import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0232
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardFiniteSubgroupGLIntDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialAtPrimeAdelicGLSubgroup
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TrivSubgroup

variable {D : D7} {q : ℕ}

theorem zeroAt_zero : ZeroAt D q 0 := fun k =>
  ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

theorem zeroAt_add {x y : AE D} (hx : ZeroAt D q x) (hy : ZeroAt D q y) : ZeroAt D q (x + y) := by
  intro k
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx k
  obtain ⟨m', hm', hmq', s', hs', h'⟩ := hy k
  refine ⟨m * m', Nat.mul_pos hm hm', Nat.Coprime.mul_left hmq hmq', (m' : AE D) * s + (m : AE D) * s',
    add_mem (mul_mem (natCast_mem _ _) hs) (mul_mem (natCast_mem _ _) hs'), ?_⟩
  push_cast
  linear_combination (m' : AE D) * h + (m : AE D) * h'

theorem zeroAt_mul_left (hq : q.Prime) (y : AE D) {x : AE D} (hx : ZeroAt D q x) :
    ZeroAt D q (y * x) := by
  intro k
  obtain ⟨n, hn, hy⟩ := GlobalTheory.AdelicApprox.exists_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, hm, hmq, s, hs, h⟩ := hx (k + a)
  refine ⟨m * n', Nat.mul_pos hm (Nat.pos_of_ne_zero (by rintro rfl; simp at hn')),
    Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, _, mul_mem hs hy, ?_⟩
  push_cast
  linear_combination (n' : AE D) * y * h

def zeroIdeal (D : D7) (hq : q.Prime) : Ideal (AE D) where
  carrier := {x | ZeroAt D q x}
  add_mem' := zeroAt_add
  zero_mem' := zeroAt_zero
  smul_mem' := fun c _ hx => zeroAt_mul_left hq c hx

theorem entry_mul_mem {R : Type} [CommRing R] (I : Ideal R) {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (hB : ∀ i j, B i j ∈ I) (i j : Fin n) : (A * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact I.sum_mem fun k _ => I.mul_mem_left _ (hB k j)

theorem trivAt_subgroup : ∀ (D : D7) (n q : ℕ), q.Prime → TrivAt D q (1 : GL (Fin n) (AE D)) ∧
    (∀ g h : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q h → TrivAt D q (g * h)) ∧
    ∀ g : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q g⁻¹ := by
  intro D n q hq
  refine ⟨fun i j => ?_, fun g h hg hh i j => ?_, fun g hg i j => ?_⟩
  · rw [Units.val_one, sub_self]; exact zeroAt_zero
  · have e : ((g * h : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) - 1 =
        (g : Matrix (Fin n) (Fin n) (AE D)) * ((h : Matrix (Fin n) (Fin n) (AE D)) - 1) +
          ((g : Matrix (Fin n) (Fin n) (AE D)) - 1) := by
      rw [Units.val_mul, mul_sub, mul_one, sub_add_sub_cancel]
    rw [← Matrix.sub_apply, e, Matrix.add_apply]
    exact zeroAt_add (entry_mul_mem (zeroIdeal D hq) _ _ hh i j) (hg i j)
  · have e : ((g⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) - 1 =
        (-((g⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D))) *
          ((g : Matrix (Fin n) (Fin n) (AE D)) - 1) := by
      rw [neg_mul, mul_sub, mul_one, Units.inv_mul, neg_sub]
    rw [← Matrix.sub_apply, e]
    exact entry_mul_mem (zeroIdeal D hq) _ _ hg i j

end GlobalTheory.TrivSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem doubleCoset_surj_of_le {G : Type*} [Group G] (H K J : Subgroup G) :
    Function.Surjective (fun p : DoubleCoset.Quotient (H : Set G) (K : Set G) × (K ⧸ J.subgroupOf K) =>
      DoubleCoset.mk H J (p.1.out * (p.2.out : G))) := by
  intro c
  obtain ⟨h, k, hh, hk, e⟩ := DoubleCoset.mk_out_eq_mul H K c.out
  refine ⟨(DoubleCoset.mk H K c.out, QuotientGroup.mk (⟨k⁻¹, K.inv_mem hk⟩ : K)), ?_⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf K) (⟨k⁻¹, K.inv_mem hk⟩ : K)
  have hjJ : ((j : K) : G) ∈ J := Subgroup.mem_subgroupOf.mp j.2
  simp only
  rw [hj, e]
  conv_rhs => rw [← DoubleCoset.out_eq' H J c]
  rw [eq_comm, DoubleCoset.eq]
  refine ⟨h, hh, _, hjJ, ?_⟩
  simp [mul_assoc]

theorem doubleCoset_card_le {G : Type*} [Group G] (H K J : Subgroup G)
    [Finite (DoubleCoset.Quotient (H : Set G) (K : Set G))] (hJ : J.relIndex K ≠ 0) :
    Finite (DoubleCoset.Quotient (H : Set G) (J : Set G)) ∧
      Nat.card (DoubleCoset.Quotient (H : Set G) (J : Set G)) ≤
        Nat.card (DoubleCoset.Quotient (H : Set G) (K : Set G)) * J.relIndex K := by
  have : Finite (K ⧸ J.subgroupOf K) := Nat.finite_of_card_ne_zero hJ
  refine ⟨Finite.of_surjective _ (doubleCoset_surj_of_le H K J), ?_⟩
  have := Nat.card_le_card_of_surjective _ (doubleCoset_surj_of_le H K J)
  rwa [Nat.card_prod] at this

theorem cls_finite_card_le : ∀ (D : D7) (N : ℕ), Finite (Cls D N (intG D N)) ∧ (Nat.card (Cls D N (intG D N)) : ℝ) ≤ (12 * (fF D : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * fF D * N ^ 2) ∧ ∀ J : Subgroup (GA D N), J ≤ intG D N → J.relIndex (intG D N) ≠ 0 → Finite (Cls D N J) ∧ Nat.card (Cls D N J) ≤ Nat.card (Cls D N (intG D N)) * J.relIndex (intG D N) := by
  intro D N
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  have hconj : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x := by
    intro x
    apply D.host.φ₀.injective
    have h1 := IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
    have h2 := D.host.conjE_apply D.host.φ₀ x
    exact h1.trans h2.symm
  have hfr : Module.finrank ℚ D.host.E = 2 * fF D := by
    rw [D.host.finrank_cmField, fF, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  obtain ⟨R, hR, hcov⟩ := GlobalTheory.exists_finset_selfDual_classes_rootDiscr D.host.E N
  obtain ⟨hrat, -, hex, -, -⟩ := GlobalTheory.NormSum.mem_ratG_intG D N
  obtain ⟨Lt, hSD, -, hLt, hmv, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  have key : ∀ g : GA D N, ∃ L₀ ∈ R, ∃ h ∈ ratG D N, Lt (h⁻¹ * g) = L₀ := by
    intro g
    obtain ⟨h1, h2, h3⟩ := (hSD g).2
    obtain ⟨L₀, hL₀, γ, hγ, hx⟩ := hcov (Lt g) h1 h2 (by
      intro y
      rw [h3 y]
      refine forall_congr' fun x => forall_congr' fun _ => ?_
      constructor
      · rintro ⟨z, hz⟩
        have hz' : (z : D.host.E) = ∑ i, IsCMField.complexConj D.host.E (x i) * y i := hz
        rw [← hz']
        exact z.isIntegral_coe
      · intro hz
        exact ⟨⟨_, hz⟩, rfl⟩)
    have hm : γ.map (IsCMField.complexConj D.host.E) = γ.map D.host.conj := by
      ext i j
      simp only [Matrix.map_apply, hconj]
    rw [hm] at hγ
    obtain ⟨h, hh⟩ := hex γ hγ
    refine ⟨L₀, hL₀, h, (hrat h).2 ⟨γ, hh⟩, ?_⟩
    ext x
    rw [hmv h (h⁻¹ * g) γ hh x, mul_inv_cancel_left, hx]
  choose L₀ hL₀ h hh hL using key
  let f : Cls D N (intG D N) → R := fun c => ⟨L₀ c.out, hL₀ _⟩
  have hf : Function.Injective f := by
    intro c c' e
    have e' : L₀ c.out = L₀ c'.out := congrArg Subtype.val e
    rw [← hL, ← hL, hLt] at e'
    rw [← DoubleCoset.out_eq' _ _ c, ← DoubleCoset.out_eq' _ _ c', DoubleCoset.eq]
    refine ⟨h c'.out * (h c.out)⁻¹, Subgroup.mul_mem _ (hh _) (Subgroup.inv_mem _ (hh _)), _, e', ?_⟩
    group
  have hfin : Finite (Cls D N (intG D N)) := Finite.of_injective f hf
  refine ⟨hfin, ?_, fun J _ hJ => doubleCoset_card_le _ _ J hJ⟩
  have hc : Nat.card (Cls D N (intG D N)) ≤ R.card := by
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  refine le_trans (by exact_mod_cast hc) (hR.trans (le_of_eq ?_))
  have hrd : |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ D.host.E : ℝ)) = D.host.rdE := rfl
  rw [hrd, hfr]
  have : 3 * (2 * fF D) * N ^ 2 = 6 * fF D * N ^ 2 := by ring
  rw [this]
  congr 1
  push_cast
  ring

end GlobalTheory.NormSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators nonZeroDivisors

namespace GlobalTheory.StabOrder

section General

variable {E : Type} [Field E] [NumberField E] {N : ℕ}

theorem loc_int : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
  IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)

theorem exists_int_smul_mem (L : Submodule (𝓞 E) (Fin N → E))
    (hs : Submodule.span E (L : Set (Fin N → E)) = ⊤) (x : Fin N → E) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ L := by
  haveI := loc_int (E := E)
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
    (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E (L : Set (Fin N → E)) x (hs ▸ Submodule.mem_top)
  obtain ⟨t, n, hn, rfl⟩ := t
  refine ⟨n, nonZeroDivisors.ne_zero hn, ?_⟩
  rw [Submodule.span_eq] at ht
  simpa [Submonoid.smul_def, Int.cast_smul_eq_zsmul] using ht

theorem exists_int_denominator (L : Submodule (𝓞 E) (Fin N → E)) (hf : L.FG) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((n : E) * x i) := by
  haveI := loc_int (E := E)
  obtain ⟨s, rfl⟩ := hf
  obtain ⟨⟨t, n, hn, rfl⟩, ht⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) (fun p : s × Fin N => (p.1 : Fin N → E) p.2)
  refine ⟨n, nonZeroDivisors.ne_zero hn, ?_⟩
  intro x hx i
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := ht (⟨x, hx⟩, i)
    have : (n : E) * x i = algebraMap (𝓞 E) E y := by
      rw [hy]; simp [Algebra.smul_def]
    rw [this]; exact y.isIntegral_coe
  | zero => simpa using isIntegral_zero
  | add x y _ _ hx hy => simpa [mul_add] using hx.add hy
  | smul a x _ hx =>
    have : (n : E) * (a • x) i = (a : E) * ((n : E) * x i) := by
      simp [Algebra.smul_def]; ring
    rw [this]; exact a.isIntegral_coe.mul hx

theorem norm_entry_le (c : E → E) (hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x))
    (γ : Matrix (Fin N) (Fin N) E) (h : γ * (γ.map c).transpose = 1) (φ : E →+* ℂ) (i j : Fin N) :
    ‖φ (γ i j)‖ ≤ 1 := by
  have h1 := congrArg φ (congrFun (congrFun h i) i)
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hc,
    Matrix.one_apply_eq, map_one, Complex.mul_conj'] at h1
  have h2 : ∑ k, ‖φ (γ i k)‖ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : ‖φ (γ i j)‖ ^ 2 ≤ 1 := by
    rw [← h2]
    exact Finset.single_le_sum (f := fun k => ‖φ (γ i k)‖ ^ 2) (fun k _ => by positivity) (Finset.mem_univ j)
  nlinarith [norm_nonneg (φ (γ i j))]

theorem finite_stab (c : E → E) (hc : ∀ (φ : E →+* ℂ) x, φ (c x) = starRingEnd ℂ (φ x))
    (L : Submodule (𝓞 E) (Fin N → E)) (hf : L.FG)
    (hs : Submodule.span E (L : Set (Fin N → E)) = ⊤) :
    {γ : Matrix (Fin N) (Fin N) E | γ * (γ.map c).transpose = 1 ∧ ∀ x ∈ L, γ.mulVec x ∈ L}.Finite := by
  obtain ⟨b, hb, hbL⟩ := exists_int_denominator L hf
  choose a ha haL using fun j : Fin N => exists_int_smul_mem L hs (Pi.single j 1)
  have hS : ∀ j, {x : E | IsIntegral ℤ (((b * a j : ℤ) : E) * x) ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ 1}.Finite := by
    intro j
    have hne : ((b * a j : ℤ) : E) ≠ 0 := by exact_mod_cast mul_ne_zero hb (ha j)
    refine Set.Finite.of_finite_image (f := fun x => ((b * a j : ℤ) : E) * x) ?_
      (mul_right_injective₀ hne).injOn
    refine (Embeddings.finite_of_norm_le E ℂ ‖((b * a j : ℤ) : ℂ)‖).subset ?_
    rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
    refine ⟨h1, fun φ => ?_⟩
    rw [map_mul, map_intCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (h2 φ)
  refine (Set.Finite.pi' (fun _ : Fin N => Set.Finite.pi' hS)).subset ?_
  rintro (γ : Matrix (Fin N) (Fin N) E) ⟨h1, h2⟩ i j
  refine ⟨?_, fun φ => norm_entry_le c hc γ h1 φ i j⟩
  have := hbL _ (h2 _ (haL j)) i
  convert this using 1
  have h3 := Matrix.mulVec_smul γ (a j) (Pi.single j (1 : E))
  rw [h3]
  simp [mul_assoc]

theorem exists_faithful (L : Submodule (𝓞 E) (Fin N → E)) (hf : L.FG)
    (hs : Submodule.span E (L : Set (Fin N → E)) = ⊤) {H : Type} [Group H]
    (ρ : H →* Matrix (Fin N) (Fin N) E) (hρ : Function.Injective ρ)
    (hL : ∀ h, ∀ x ∈ L, (ρ h).mulVec x ∈ L) :
    ∃ ψ : H →* GL (Fin (Module.finrank ℚ E * N)) ℤ, Function.Injective ψ := by
  let L' : Submodule ℤ (Fin N → E) := L.restrictScalars ℤ
  have hf' : L'.FG := by
    haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hf
    haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    exact Module.Finite.iff_fg.mp (inferInstanceAs (Module.Finite ℤ L))
  haveI hlat : Submodule.IsLattice ℚ L' := by
    refine ⟨hf', ?_⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨n, hn, hx⟩ := exists_int_smul_mem L hs x
    have : x = (n : ℚ)⁻¹ • (n • x) := by
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  haveI : Module.Finite ℤ L' := Module.Finite.iff_fg.mpr hf'
  have hr : Module.finrank ℤ L' = Module.finrank ℚ E * N := by
    have h1 : Module.finrank ℤ L' = Module.finrank ℚ (Fin N → E) := by
      unfold Module.finrank
      rw [Submodule.IsLattice.rank' ℚ L']
    rw [h1, Module.finrank_pi_fintype]
    simp [mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ L' hr
  let θ : H →* Module.End ℤ L' :=
    { toFun := fun h => ((Matrix.toLin' (ρ h)).restrictScalars ℤ).restrict (p := L') (q := L')
        (fun x hx => hL h x hx)
      map_one' := by ext x i; simp
      map_mul' := by
        intro g h
        ext x i
        show Matrix.toLin' (ρ (g * h)) x i = Matrix.toLin' (ρ g) (Matrix.toLin' (ρ h) x) i
        simp }
  have hθ : Function.Injective θ := by
    intro g h hgh
    apply hρ
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    obtain ⟨n, hn, hx⟩ := exists_int_smul_mem L hs x
    have h1 : Matrix.toLin' (ρ g) (n • x) = Matrix.toLin' (ρ h) (n • x) :=
      congrArg Subtype.val (LinearMap.congr_fun hgh ⟨n • x, hx⟩)
    rw [map_zsmul, map_zsmul] at h1
    exact smul_right_injective _ hn h1
  refine ⟨(((LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp θ).toHomUnits, ?_⟩
  intro g h hgh
  apply hθ
  apply (LinearMap.toMatrixAlgEquiv b).injective
  exact congrArg Units.val hgh

end General

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * fF D := by
  have h := D.host.finrank_cmField
  rw [show Module.finrank ℚ D.host.E = _ from h]
  simp only [fF, Ranks.f, Ranks.n]
  ring

theorem gam_ne_zero_dvd_invariant : ∀ (D : D7) (N : ℕ) (J : Subgroup (GA D N)), J ≤ intG D N → ∀ g, gam D J g ≠ 0 ∧ gam D J g ∣ 8 ^ (2 * fF D * N) * (2 * (2 * fF D * N)).factorial ∧ ∀ γ ∈ ratG D N, ∀ j ∈ J, gam D J (γ * g * j) = gam D J g := by
  intro D N J hJ g
  obtain ⟨hrat, -, -, huni, hinc⟩ := GlobalTheory.NormSum.mem_ratG_intG D N
  obtain ⟨Lt, hSD, -, hEq, hmv, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
  let H : Subgroup (GA D N) := ratG D N ⊓ J.comap (MulAut.conj g⁻¹).toMonoidHom
  have hH : ∀ x, x ∈ H ↔ x ∈ ratG D N ∧ g⁻¹ * x * g ∈ J := by
    intro x; simp [H]
  have hcard : gam D J g = Nat.card H :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hH x).symm)
  choose r hr using fun h : H => (hrat h).1 ((hH h).1 h.2).1
  have hmap : Function.Injective (fun M : Matrix (Fin N) (Fin N) D.host.E => M.map (inc D)) :=
    Matrix.map_injective hinc
  let ρ : H →* Matrix (Fin N) (Fin N) D.host.E :=
    { toFun := r
      map_one' := by
        apply hmap
        have := hr 1
        unfold IsRat at this
        simp only [← this]
        simp
      map_mul' := by
        intro x y
        apply hmap
        have h1 := hr x
        have h2 := hr y
        have h3 := hr (x * y)
        unfold IsRat at h1 h2 h3
        simp only [Matrix.map_mul, ← h1, ← h2, ← h3]
        simp }
  have hρ : Function.Injective ρ := by
    intro x y hxy
    have h1 := hr x
    have h2 := hr y
    unfold IsRat at h1 h2
    have h3 : r x = r y := hxy
    rw [h3, ← h2] at h1
    exact Subtype.ext (Subtype.ext (Units.ext h1))
  have hL : ∀ h : H, ∀ x ∈ Lt g, (ρ h).mulVec x ∈ Lt g := by
    intro h x hx
    have h1 : Lt g = Lt (h * g) := (hEq _ _).2 (by
      rw [← mul_assoc]; exact hJ ((hH h).1 h.2).2)
    have := (hmv h g (r h) (hr h) x).1 hx
    rwa [← h1] at this
  obtain ⟨hfg, hspan, -⟩ := (hSD g).2
  have hfin : Finite H := by
    have := (finite_stab D.host.conj
      (fun φ x => D.host.conjE_apply φ x) (Lt g) hfg hspan).to_subtype
    exact Finite.of_injective (β := {γ : Matrix (Fin N) (Fin N) D.host.E |
        γ * (γ.map D.host.conj).transpose = 1 ∧ ∀ x ∈ Lt g, γ.mulVec x ∈ Lt g})
      (fun h => ⟨ρ h, huni h _ (hr h), hL h⟩) (fun x y hxy => hρ (congrArg Subtype.val hxy))
  refine ⟨?_, ?_, ?_⟩
  · rw [hcard]; exact Nat.card_pos.ne'
  · obtain ⟨ψ, hψ⟩ := exists_faithful (Lt g) hfg hspan ρ hρ hL
    have e := (MonoidHom.ofInjective hψ).toEquiv
    have := GlobalTheory.card_finite_subgroup_GL_int_dvd _ ψ.range (Finite.of_equiv _ e)
    rw [← Nat.card_congr e, finrank_host] at this
    rw [hcard]; exact this
  · intro γ hγ j hj
    unfold gam
    refine Nat.card_congr ((MulAut.conj γ⁻¹).toEquiv.subtypeEquiv fun x => ?_)
    have e1 : (MulAut.conj γ⁻¹).toEquiv x = γ⁻¹ * x * γ := by simp
    rw [e1]
    have e2 : (γ * g * j)⁻¹ * x * (γ * g * j) = j⁻¹ * (g⁻¹ * (γ⁻¹ * x * γ) * g) * j := by group
    rw [e2, Subgroup.mul_mem_cancel_right _ hj, Subgroup.mul_mem_cancel_left _ (J.inv_mem hj),
      Subgroup.mul_mem_cancel_right _ hγ, Subgroup.mul_mem_cancel_left _ ((ratG D N).inv_mem hγ)]

end GlobalTheory.StabOrder
end

