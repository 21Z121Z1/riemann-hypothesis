import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem ConeTrdeg.mConeMap_of_isMultiHomog (y : (Σ k, ι k) → Ω) {g : Geo.MRing ι} {d : K → ℕ}
    (hg : Geo.IsMultiHomog g d) :
    Geo.mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  simp only [Geo.mConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  rw [mul_assoc]
  congr 2
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← hg m hm k, ← Finset.prod_pow_eq_pow_sum]

theorem ConeTrdeg.proof : ConeTrdeg.Statement := by
  intro K _ ι _ Ω _ y hbir hnz hhor
  classical

  have hinjΩ : Function.Injective (algebraMap ℤ Ω) := by
    rw [injective_iff_map_eq_zero]
    intro n hn
    have hmem : (MvPolynomial.C n : Geo.MRing ι) ∈ Geo.mCoordIdeal y := by
      rw [Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_apply, hn, map_zero]
    have h2 : n ∈ (Geo.mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* Geo.MRing ι) := hmem
    simp only [Geo.IsHorizontal] at hhor
    rw [hhor] at h2
    exact (Ideal.mem_bot).1 h2
  have : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr hinjΩ
  have : FaithfulSMul Ω (MvPolynomial K Ω) :=
    (faithfulSMul_iff_algebraMap_injective Ω (MvPolynomial K Ω)).mpr (MvPolynomial.C_injective K Ω)
  have hB : Algebra.trdeg ℤ (MvPolynomial K Ω) = Algebra.trdeg ℤ Ω + Fintype.card K := by
    rw [← trdeg_add_eq ℤ Ω (A := MvPolynomial K Ω), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype]
  have hZB : Function.Injective (algebraMap ℤ (MvPolynomial K Ω)) := by
    rw [IsScalarTower.algebraMap_eq ℤ Ω (MvPolynomial K Ω), RingHom.coe_comp]
    exact (MvPolynomial.C_injective K Ω).comp hinjΩ
  let S := (Geo.mConeMap y).range
  have hA : Algebra.trdeg ℤ (Geo.MRing ι ⧸ Geo.mCoordIdeal y) = Algebra.trdeg ℤ S :=
    (Ideal.quotientKerEquivRange (Geo.mConeMap y)).trdeg_eq
  have : FaithfulSMul ℤ S := (faithfulSMul_iff_algebraMap_injective ℤ S).mpr
    (Function.Injective.of_comp (f := algebraMap S (MvPolynomial K Ω))
      (by rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]))
  have : FaithfulSMul S (MvPolynomial K Ω) :=
    (faithfulSMul_iff_algebraMap_injective S (MvPolynomial K Ω)).mpr Subtype.val_injective

  have halgC : ∀ a : Ω, IsAlgebraic S (MvPolynomial.C a : MvPolynomial K Ω) := by
    intro a
    obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir a
    have hgS : Geo.mConeMap y g ∈ S := AlgHom.mem_range_self _ _
    have hhS : Geo.mConeMap y h ∈ S := AlgHom.mem_range_self _ _
    have hne : Geo.mConeMap y h ≠ 0 := by
      rw [ConeTrdeg.mConeMap_of_isMultiHomog y hh]
      exact mul_ne_zero (MvPolynomial.C_ne_zero.2 hh0)
        (Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k))
    refine IsAlgebraic.of_mul (y := Geo.mConeMap y h) (mem_nonZeroDivisors_of_ne_zero hne)
      (isAlgebraic_algebraMap (⟨_, hhS⟩ : S)) ?_
    have hmul : Geo.mConeMap y h * MvPolynomial.C a = Geo.mConeMap y g := by
      rw [ConeTrdeg.mConeMap_of_isMultiHomog y hh, ConeTrdeg.mConeMap_of_isMultiHomog y hg, hgh, map_mul]
      ring
    rw [hmul]
    exact isAlgebraic_algebraMap (⟨_, hgS⟩ : S)

  choose c hc using hnz
  have halgX : ∀ k, IsAlgebraic S (X k : MvPolynomial K Ω) := by
    intro k
    have hS : Geo.mConeMap y (X ⟨k, c k⟩) ∈ S := AlgHom.mem_range_self _ _
    refine IsAlgebraic.of_mul (y := MvPolynomial.C (y ⟨k, c k⟩))
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.C_ne_zero.2 (hc k))) (halgC _) ?_
    have hmul : (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) = Geo.mConeMap y (X ⟨k, c k⟩) := by
      simp [Geo.mConeMap]
    rw [hmul]
    exact isAlgebraic_algebraMap (⟨_, hS⟩ : S)
  have : Algebra.IsAlgebraic S (MvPolynomial K Ω) := ⟨fun p ↦ by
    induction p using MvPolynomial.induction_on with
    | C a => exact halgC a
    | add p q hp hq => exact hp.add hq
    | mul_X p k hp => exact hp.mul (halgX k)⟩
  have hSB := trdeg_add_eq ℤ S (A := MvPolynomial K Ω)
  rw [trdeg_eq_zero (R := S) (A := MvPolynomial K Ω), add_zero] at hSB
  rw [hA, hSB, hB]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PDualBasisExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

theorem latticeDual_int_fg {K : Type*} [Field K] [NumberField K] {r : ℕ} (F : HermLattice K (r + 1)) :
    ((latticeDual F.lattice).restrictScalars ℤ).FG := by
  classical
  obtain ⟨s, hs⟩ := F.fg

  let ev : (Fin (r + 1) → K) →ₗ[ℤ] (s → K) :=
    { toFun := fun φ v ↦ φ ⬝ᵥ (v : Fin (r + 1) → K)
      map_add' := by
        intro φ ψ
        funext v
        simp [add_dotProduct]
      map_smul' := by
        intro c φ
        funext v
        exact smul_dotProduct c φ (v : Fin (r + 1) → K) }
  have hspan : Submodule.span K (s : Set (Fin (r + 1) → K)) = ⊤ := by
    rw [← Submodule.span_span_of_tower (R := 𝓞 K), hs, F.span_eq]
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    have h0 : ∀ w ∈ Submodule.span K (s : Set (Fin (r + 1) → K)), φ ⬝ᵥ w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact congrFun hφ ⟨x, hx⟩
      | zero => simp
      | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
      | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]
    funext j
    have := h0 (Pi.single j 1) (by rw [hspan]; exact Submodule.mem_top)
    simpa using this

  let T : Submodule ℤ (s → K) :=
    LinearMap.range (LinearMap.compLeft ((Algebra.linearMap (𝓞 K) K).restrictScalars ℤ) s)
  have hle : ((latticeDual F.lattice).restrictScalars ℤ).map ev ≤ T := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hv : ∀ v : s, (v : Fin (r + 1) → K) ∈ F.lattice := by
      intro v
      rw [← hs]
      exact Submodule.subset_span v.2
    refine ⟨fun v ↦ (hφ v (hv v)).choose, ?_⟩
    funext v
    exact (hφ v (hv v)).choose_spec
  have : IsNoetherian ℤ T := isNoetherian_of_isNoetherianRing_of_finite ℤ T
  exact Submodule.fg_of_fg_map_injective ev hinj (isNoetherian_submodule.mp inferInstance _ hle)

theorem latticeDual_ne_bot {K : Type*} [Field K] [NumberField K] {r : ℕ} (F : HermLattice K (r + 1)) :
    ∃ ψ ∈ latticeDual F.lattice, ψ ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := F.fg
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (s.image fun v ↦ v 0)
  have hbne : algebraMap (𝓞 K) K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  refine ⟨Pi.single 0 (algebraMap (𝓞 K) K b), ?_, fun h ↦ hbne (by simpa using congrFun h 0)⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hb (x 0) (Finset.mem_image_of_mem _ hx)
    refine ⟨a, ?_⟩
    rw [ha, Algebra.smul_def]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by rw [map_add, ha, hc, dotProduct_add]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ha, dotProduct_smul, Algebra.smul_def]⟩

theorem DualBasisExists.proof : DualBasisExists.Statement := by
  intro K _ _ r F
  classical
  let M : Submodule ℤ (Fin (r + 1) → K) := (latticeDual F.lattice).restrictScalars ℤ
  have : Module.Finite ℤ M := Module.Finite.iff_fg.mpr (latticeDual_int_fg F)
  have : Module.Free ℤ M := inferInstance
  obtain ⟨ψ, hψ, hψ0⟩ := latticeDual_ne_bot F
  have : Nontrivial M := ⟨⟨⟨ψ, hψ⟩, 0, fun h ↦ hψ0 (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank ℤ M := Module.finrank_pos
  obtain ⟨N, hN⟩ : ∃ N, Module.finrank ℤ M = N + 1 :=
    ⟨Module.finrank ℤ M - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  let bas := Module.finBasisOfFinrankEq ℤ M hN
  refine ⟨N, fun i ↦ (bas i : Fin (r + 1) → K), ?_, ?_⟩
  · exact bas.linearIndependent.map' M.subtype (Submodule.ker_subtype _)
  · have : Set.range (fun i ↦ (bas i : Fin (r + 1) → K)) = M.subtype '' Set.range bas := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, bas.span_eq, Submodule.map_top, Submodule.range_subtype]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockStandard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField Matrix

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem standard_coord_integral {m : ℕ} {v : Fin m → K}
    (hv : v ∈ (HermLattice.standard K m).lattice) (i : Fin m) :
    ∃ b : 𝓞 K, v i = algebraMap (𝓞 K) K b := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨if i = j then 1 else 0, ?_⟩
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ← ha, ← hb, Pi.add_apply]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [map_mul, ← ha, Pi.smul_apply, Algebra.smul_def]⟩

omit [NumberField K] in

theorem oneBlockForms_symm_apply {e r : ℕ} (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K))
    (a : Fin (e + 1)) (j : Fin (r + 1)) :
    oneBlockForms om ((oneBlockIndex e r).symm (a, j)) = Pi.single j ((om a : 𝓞 K) : K) := by
  simp [oneBlockForms]

omit [NumberField K] in

theorem oneBlockForms_linearIndependent {e r : ℕ} (om : Module.Basis (Fin (e + 1)) ℤ (𝓞 K)) :
    LinearIndependent ℤ (oneBlockForms (r := r) om) := by
  rw [← linearIndependent_equiv (oneBlockIndex e r).symm]
  have hψ : oneBlockForms (r := r) om ∘ (oneBlockIndex e r).symm =
      fun p : Fin (e + 1) × Fin (r + 1) ↦ (Pi.single p.2 ((om p.1 : 𝓞 K) : K) : Fin (r + 1) → K) := by
    funext p
    exact oneBlockForms_symm_apply om p.1 p.2
  rw [hψ, Fintype.linearIndependent_iff]
  rintro g hg ⟨a, j⟩
  have hj := congrFun hg j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Fintype.sum_prod_type, Pi.single_apply,
    smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hj
  have h2 : ∑ a', g (a', j) • om a' = 0 := by
    apply RingOfIntegers.coe_injective
    push_cast
    simpa using hj
  exact Fintype.linearIndependent_iff.mp om.linearIndependent _ h2 a

theorem OneBlockStandard.proof : OneBlockStandard.Statement := by
  intro K _ _ e r om
  refine ⟨⟨oneBlockForms_linearIndependent om, le_antisymm ?_ ?_⟩, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩ v hv
    obtain ⟨b, hb⟩ := standard_coord_integral hv (oneBlockIndex e r p).2
    refine ⟨om (oneBlockIndex e r p).1 * b, ?_⟩
    simp only [oneBlockForms, single_dotProduct, map_mul, hb]
  · intro ψ hψ
    have hj : ∀ j, ∃ b : 𝓞 K, ψ j = algebraMap (𝓞 K) K b := by
      intro j
      obtain ⟨b, hb⟩ := hψ (Pi.single j 1) (Submodule.subset_span ⟨j, rfl⟩)
      exact ⟨b, by rw [hb, dotProduct_single, mul_one]⟩
    choose b hb using hj
    have hsum : ψ = ∑ j, ∑ a, om.repr (b j) a •
        oneBlockForms (r := r) om ((oneBlockIndex e r).symm (a, j)) := by
      funext i
      simp only [oneBlockForms_symm_apply, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite,
        smul_zero]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [hb i]
      conv_lhs => rw [← om.sum_repr (b i)]
      push_cast
      rfl
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.sum_mem _ fun a _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have hmap : latticeMap (oneBlockForms (r := r) om) = oneBlockMap om := by
      apply MvPolynomial.ringHom_ext
      · intro n
        simp [latticeMap, oneBlockMap]
      · intro v
        simp only [latticeMap, oneBlockMap, coe_eval₂Hom, eval₂_X, oneBlockForms, latticeForm]
        rw [Finset.sum_eq_single (oneBlockIndex e r v.2).2]
        · simp
        · intro i _ hi
          simp [hi]
        · simp
    unfold latticeIdeal oneBlockIdeal
    rw [hmap]
  · intro σ w
    funext _ p
    simp only [latticePoint, oneBlockPoint, oneBlockForms]
    rw [Finset.sum_eq_single (oneBlockIndex e r p).2]
    · simp
    · intro i _ hi
      simp [hi]
    · simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PReadsMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace ReadsMul

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem mConeMap_of_homog {Ω : Type} [Field Ω] (y : Coord n → Ω) {g : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g d) :
    Geo.mConeMap (ι := blockIdx n) y g = C (aeval y g) * ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by
  have hg' := (geoMultiHomog_iff g d).mpr hg
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : Coord n, (X p.1 : MvPolynomial ι Ω) ^ m p = ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (X k : MvPolynomial ι Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg' m hm k]
  simp only [Geo.mConeMap, aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun i => by simp), Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mem_mCoordIdeal {Ω : Type} [Field Ω] (y : Coord n → Ω) {g : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g d) (h0 : aeval y g = 0) :
    g ∈ Geo.mCoordIdeal (ι := blockIdx n) y := by
  rw [Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_homog y hg, h0, map_zero, zero_mul]

theorem proof : ReadsMul.Statement := by
  intro ι _ _ n Ω _ y P a b s s' t t' hP ⟨f, q, δf, δq, hf, hq, hfq, hqP, ht⟩ _ hR hR'
  subst ht
  have hqy : aeval y q ≠ 0 := fun h0 ↦ hqP (hP ▸ mem_mCoordIdeal y hq h0)
  have hqF : P.mkF q ≠ 0 := fun h0 ↦ hqP ((P.mkF_eq_zero_iff q).mp h0)
  have hfy : aeval y f = s * aeval y q :=
    (hR f q δf δq hf hq (fun k ↦ by have := hfq k; omega)).mpr (div_mul_cancel₀ _ hqF).symm
  intro g h δg δh hg hh hd
  have key := hR' (g * q) (f * h) (δg + δq) (δf + δh) (hg.mul hq) (hf.mul hh) (fun k ↦ by
    have h1 := hfq k
    have h2 := hd k
    simp only [Pi.add_apply, Nat.cast_add] at h1 h2 ⊢
    omega)
  rw [map_mul, map_mul, map_mul, map_mul] at key
  have e1 : (aeval y g = s * s' * aeval y h) ↔
      (aeval y g * aeval y q = s' * (aeval y f * aeval y h)) := by
    rw [← mul_left_inj' hqy, hfy, show s * s' * aeval y h * aeval y q =
      s' * (s * aeval y q * aeval y h) by ring]
  have e2 : (P.mkF g = P.mkF f / P.mkF q * t' * P.mkF h) ↔
      (P.mkF g * P.mkF q = t' * (P.mkF f * P.mkF h)) := by
    rw [← mul_left_inj' hqF, show P.mkF f / P.mkF q * t' * P.mkF h * P.mkF q =
      t' * (P.mkF f * P.mkF h) by field_simp]
  exact e1.trans (key.trans e2.symm)

end ReadsMul

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PSectionSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace SectionSmall

theorem mkF_den_ne_zero {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a) :
    P.mkF s.den ≠ 0 := fun h ↦ s.den_not_mem ((P.mkF_eq_zero_iff _).mp h)

theorem den_mul_sub_mem {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {p q : MvPolynomial (Coord n) ℤ} (h : P.mkF p = s.toFun * P.mkF q) :
    s.den * p - s.num * q ∈ P.ideal := by
  have hG := mkF_den_ne_zero s
  rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, h, IntegralSection.toFun]
  field_simp
  ring

theorem mkF_eq_of_mem {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {e m : MvPolynomial (Coord n) ℤ} (h : s.den * e - s.num * m ∈ P.ideal) :
    P.mkF e = s.toFun * P.mkF m := by
  have hG := mkF_den_ne_zero s
  have h' := (P.mkF_eq_zero_iff _).mpr h
  rw [map_sub, map_mul, map_mul] at h'
  rw [IntegralSection.toFun, div_mul_eq_mul_div, eq_div_iff hG]
  linear_combination h'

omit [Fintype ι] in

theorem live_of_ne {P : ArithVariety n} {F : Type*} [CommRing F] {z : Cone n F} (hz : z ∈ P.points F)
    {c : (k : ι) → Fin (n k + 1)} (hc : ∀ k, z k (c k) ≠ 0) :
    ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ P.ideal := fun k hk ↦
  hc k (by simpa [evalCone] using hz.2 _ hk)

omit [Fintype ι] in

theorem exists_chart {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, z k (c k) ≠ 0 := by
  have h : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hz.1 k)
  choose c hc using h
  exact ⟨c, hc⟩

omit [DecidableEq ι] in

theorem evalCone_chartMonomial_ne_zero {z : Cone n ℂ} {c : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, z k (c k) ≠ 0) (d : ι → ℕ) : evalCone z (chartMonomial c d) ≠ 0 := by
  simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
  exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)

theorem eval_cross {P : ArithVariety n} {a : ι → ℤ} (s : IntegralSection P a)
    {p q e m : MvPolynomial (Coord n) ℤ} (hpq : s.den * p - s.num * q ∈ P.ideal)
    (hem : s.den * e - s.num * m ∈ P.ideal) {z : Cone n ℂ} (hz : z ∈ P.points ℂ) :
    evalCone z e * evalCone z q = evalCone z p * evalCone z m := by
  have hmul : s.den * (e * q - p * m) ∈ P.ideal := by
    have h := P.ideal.sub_mem (P.ideal.mul_mem_right q hem) (P.ideal.mul_mem_right m hpq)
    convert h using 1
    ring
  have hmem : e * q - p * m ∈ P.ideal :=
    (P.isPrime.mem_or_mem hmul).resolve_left s.den_not_mem
  have h0 := hz.2 _ hmem
  simp only [evalCone, eval₂_sub, eval₂_mul] at h0 ⊢
  exact sub_eq_zero.mp h0

theorem proof : SectionSmall.Statement := by
  intro ι _ _ n P A s
  have bound : ∀ C : ℝ, s.SupNormLE A C → ∀ p q : MvPolynomial (Coord n) ℤ,
      P.mkF p = s.toFun * P.mkF q →
      ∀ z ∈ P.points ℂ, ‖evalCone z p‖ ≤ Real.exp C * (‖evalCone z q‖ * A.metric z) := by
    intro C hC p q hpq z hz
    obtain ⟨c, hc⟩ := exists_chart hz
    obtain ⟨d, e, he⟩ := s.regular c (live_of_ne hz hc)
    have hcross := eval_cross s (den_mul_sub_mem s hpq) he.2 hz
    have hm : 0 < ‖evalCone z (chartMonomial c d)‖ :=
      norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hc d)
    have hh : 0 < A.metric z := A.metric_pos z hz.1
    have hb := hC z hz c d e he hc
    rw [div_le_iff₀ (mul_pos hm hh)] at hb
    have hnorm : ‖evalCone z e‖ * ‖evalCone z q‖ =
        ‖evalCone z p‖ * ‖evalCone z (chartMonomial c d)‖ := by
      rw [← norm_mul, ← norm_mul, hcross]
    refine le_of_mul_le_mul_right ?_ hm
    calc ‖evalCone z p‖ * ‖evalCone z (chartMonomial c d)‖
        = ‖evalCone z e‖ * ‖evalCone z q‖ := hnorm.symm
      _ ≤ Real.exp C * (‖evalCone z (chartMonomial c d)‖ * A.metric z) * ‖evalCone z q‖ :=
          mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = Real.exp C * (‖evalCone z q‖ * A.metric z) * ‖evalCone z (chartMonomial c d)‖ := by ring
  refine ⟨bound, ⟨fun hs p q δp δq _ _ _ hpq z hz ↦ ?_, fun hsm z hz c d e he hc ↦ ?_⟩⟩
  · simpa [Real.exp_zero] using bound 0 hs p q hpq z hz
  · obtain ⟨⟨δ, hδ, hδd⟩, hmem⟩ := he
    have hm : 0 < ‖evalCone z (chartMonomial c d)‖ :=
      norm_pos_iff.mpr (evalCone_chartMonomial_ne_zero hc d)
    have hh : 0 < A.metric z := A.metric_pos z hz.1
    have hsmall := hsm e (chartMonomial c d) δ d hδ (isWeightedHomogeneous_chartMonomial c d)
      (fun k ↦ by rw [hδd k]; ring) (mkF_eq_of_mem s hmem) z hz
    rw [Real.exp_zero, div_le_one (mul_pos hm hh)]
    exact hsmall

end SectionSmall

end

end GroundTheory.Heights₂.Heights
end

