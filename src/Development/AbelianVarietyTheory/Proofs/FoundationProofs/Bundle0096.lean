import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ModularJExpansionAndPolynomialAndIsIntegral
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralCuspExpansionJInvariant
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FNExpJ

variable {Ω : Type} [Field Ω]

theorem ofPowerSeries_coeff_of_ne (P : PowerSeries Ω) {r : ℚ} (hr : ∀ n : ℕ, (n : ℚ) ≠ r) :
    (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨n, -, hn⟩
  exact hr n (by simpa using hn)

theorem expansion_j : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω,
    IsExp ε jT h ∧ h.coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → h.coeff r = 0) ∧
      ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  intro Ω _ ε
  obtain ⟨c, hc⟩ := GlobalTheory.exists_hasSum_modularJ_sub_inv
  set P : PowerSeries Ω := PowerSeries.mk fun n => (c n : Ω) with hPdef
  have hP : ∀ n : ℕ, (HahnSeries.ofPowerSeries ℚ Ω P).coeff (n : ℚ) = (c n : Ω) := fun n => by
    rw [HahnSeries.ofPowerSeries_apply_coeff, hPdef, PowerSeries.coeff_mk]
  have h0 : ∀ r : ℚ, (∀ n : ℕ, (n : ℚ) ≠ r) → (HahnSeries.ofPowerSeries ℚ Ω P).coeff r = 0 :=
    fun r hr => ofPowerSeries_coeff_of_ne P hr
  have hneg : ∀ r : ℚ, r < 0 → ∀ n : ℕ, (n : ℚ) ≠ r := fun r hr n hn => by
    have : (0 : ℚ) ≤ n := n.cast_nonneg
    linarith
  refine ⟨HahnSeries.single (-1 : ℚ) (1 : Ω) + HahnSeries.ofPowerSeries ℚ Ω P,
    ⟨?_, 0, ?_⟩, ?_, ?_, ?_⟩
  · refine ⟨1, one_pos, fun r hr => ?_⟩
    by_cases h1 : r = -1
    · exact ⟨-1, by simp [h1]⟩
    by_cases h2 : ∃ n : ℕ, (n : ℚ) = r
    · obtain ⟨n, rfl⟩ := h2
      exact ⟨n, by simp⟩
    · push_neg at h2
      exfalso
      apply hr
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2, add_zero]
  · intro z hz
    set τ : ℍ := ⟨z, hz⟩ with hτ
    have hup : up jT z = GlobalTheory.modularJ τ := by
      simp only [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
      rfl
    have hq : Function.Periodic.qParam 1 (τ : ℂ) = Complex.exp (2 * Real.pi * Complex.I * z) := by
      simp [Function.Periodic.qParam, hτ]
    have H1 : HasSum (fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (Function.Periodic.qParam 1 (τ : ℂ))⁻¹ := by
      have := hasSum_single (f := fun r : ℚ => ε ((HahnSeries.single (-1 : ℚ) (1 : Ω)).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (-1) (fun r hr => by
          simp [HahnSeries.coeff_single_of_ne hr])
      convert this using 1
      rw [hq, HahnSeries.coeff_single_same, map_one, one_mul, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    have H2 : HasSum (fun r : ℚ => ε ((HahnSeries.ofPowerSeries ℚ Ω P).coeff r) *
        Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z))
        (GlobalTheory.modularJ τ - (Function.Periodic.qParam 1 (τ : ℂ))⁻¹) := by
      refine (Function.Injective.hasSum_iff (g := fun n : ℕ => (n : ℚ)) Nat.cast_injective
        (fun r hr => ?_)).mp ?_
      · rw [h0 r (fun n hn => hr ⟨n, hn⟩), map_zero, zero_mul]
      · convert hc τ using 1
        funext n
        simp only [Function.comp_apply, hP, map_intCast, hq, ← Complex.exp_nat_mul]
        congr 2
        push_cast
        ring
    convert H1.add H2 using 1
    · funext r
      rw [HahnSeries.coeff_add, map_add, add_mul]
    · rw [hup]
      ring
  · rw [HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num)), add_zero]
  · intro r hr
    rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne hr.ne, h0 r (hneg r (by linarith)),
      add_zero]
  · intro r
    by_cases h1 : r = -1
    · subst h1
      refine ⟨1, ?_⟩
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_same, h0 _ (hneg _ (by norm_num))]
      simp
    by_cases h2 : ∃ n : ℕ, (n : ℚ) = r
    · obtain ⟨n, rfl⟩ := h2
      refine ⟨c n, ?_⟩
      rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, hP, zero_add]
    · push_neg at h2
      exact ⟨0, by rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne h1, h0 r h2]; simp⟩

end GlobalTheory.FNExpJ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJointGenEigenspaceIdempotentPoly
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.GenEigIdem

open Polynomial Module

section SlopeTestRemainingChoices

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def stabAlg (Z B : Submodule K V) : Subalgebra K (Module.End K V) where
  carrier := {f | (∀ z ∈ Z, f z ∈ Z) ∧ ∀ z ∈ B, f z ∈ B}
  mul_mem' := fun {f g} hf hg =>
    ⟨fun z hz => hf.1 _ (hg.1 z hz), fun z hz => hf.2 _ (hg.2 z hz)⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun z hz => Z.add_mem (hf.1 z hz) (hg.1 z hz),
     fun z hz => B.add_mem (hf.2 z hz) (hg.2 z hz)⟩
  algebraMap_mem' := fun c =>
    ⟨fun z hz => by simpa [Module.algebraMap_end_apply] using Z.smul_mem c hz,
     fun z hz => by simpa [Module.algebraMap_end_apply] using B.smul_mem c hz⟩

def quotAlgHom (Z B : Submodule K V) :
    stabAlg Z B →ₐ[K] Module.End K (Z ⧸ B.comap Z.subtype) where
  toFun f := (B.comap Z.subtype).mapQ (B.comap Z.subtype)
    ((f : Module.End K V).restrict f.2.1) (fun z hz => f.2.2 _ hz)
  map_one' := by ext z; rfl
  map_mul' f g := by ext z; rfl
  map_zero' := by ext z; rfl
  map_add' f g := by ext z; rfl
  commutes' c := by ext z; rfl

theorem quotAlgHom_mk (Z B : Submodule K V) (f : stabAlg Z B) (z : Z) :
    quotAlgHom Z B f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨(f : Module.End K V) z, f.2.1 z z.2⟩ := rfl

theorem quotAlgHom_mk_eq_zero (Z B : Submodule K V) (f : stabAlg Z B) (z : Z) :
    quotAlgHom Z B f (Submodule.Quotient.mk z) = 0 ↔ (f : Module.End K V) z ∈ B := by
  rw [quotAlgHom_mk, Submodule.Quotient.mk_eq_zero]; rfl

theorem exists_poly_genEig (M : Type) [AddCommGroup M] [Module K M] [FiniteDimensional K M]
    (A : Module.End K M) (c : K) :
    ∃ p : K[X], p.eval c = 1 ∧
      ∀ w, aeval A ((X - C c) ^ finrank K M) (aeval A p w) = 0 := by
  set χ := A.charpoly with hχdef
  have hχ : χ ≠ 0 := (LinearMap.charpoly_monic A).ne_zero
  set a := χ.rootMultiplicity c
  set r := χ /ₘ (X - C c) ^ a
  have hr : r.eval c ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero c hχ
  have hfac : (X - C c) ^ a * r = χ := pow_mul_divByMonic_rootMultiplicity_eq χ c
  have ha : a ≤ finrank K M := by
    have h1 : (X - C c) ^ a ∣ χ := ⟨r, hfac.symm⟩
    have h2 := natDegree_le_of_dvd h1 hχ
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one, hχdef, LinearMap.charpoly_natDegree] at h2
  refine ⟨C (r.eval c)⁻¹ * r, by simp [hr], fun w => ?_⟩
  rw [← Module.End.mul_apply, ← map_mul]
  have : (X - C c) ^ finrank K M * (C (r.eval c)⁻¹ * r) =
      C (r.eval c)⁻¹ * (X - C c) ^ (finrank K M - a) * χ := by
    rw [← hfac]
    conv_lhs => rw [← Nat.sub_add_cancel ha, pow_add]
    ring
  rw [this, map_mul, LinearMap.aeval_self_charpoly, mul_zero, LinearMap.zero_apply]

end SlopeTestRemainingChoices

end GlobalTheory.GenEigIdem

namespace GlobalTheory

open Polynomial Module GlobalTheory.GenEigIdem

theorem exists_genEig_idem_poly : ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] (Z B : Submodule K V) (ι : Type) (S : ι → Prop) (T : ι → Module.End K V) (lam : ι → K), B ≤ Z → FiniteDimensional K Z → (∀ t, S t → ∀ z ∈ Z, T t z ∈ Z) → (∀ t, S t → ∀ z ∈ B, T t z ∈ B) → (∀ t t', S t → S t' → ∀ z ∈ Z, T t (T t' z) - T t' (T t z) ∈ B) → (∀ z ∈ Z, ∀ n : ℕ, (∀ t, S t → ((T t - lam t • 1) ^ n) z ∈ B) → ∀ t, S t → (T t - lam t • 1) z ∈ B) → ∃ P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}), FreeAlgebra.lift K lam P = 1 ∧ ∀ z ∈ Z, ∀ t, S t → (T t - lam t • 1) (FreeAlgebra.lift K T P z) ∈ B := by
  intro K _ V _ _ Z B ι S T lam _hBZ hfd hZ hB hcomm hgen
  let Tg : {t // S t} → stabAlg Z B := fun t => ⟨T t.1, hZ t.1 t.2, hB t.1 t.2⟩
  let φ := quotAlgHom Z B
  let d := finrank K (Z ⧸ B.comap Z.subtype)
  have hex : ∀ t : {t // S t}, ∃ p : K[X], p.eval (lam t.1) = 1 ∧
      ∀ w, aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d) (aeval (φ (Tg t)) p w) = 0 :=
    fun t => exists_poly_genEig _ _ _
  choose p hp1 hp2 using hex
  let N : {t // S t} → Submodule K (Z ⧸ B.comap Z.subtype) := fun t =>
    LinearMap.ker (aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d))
  let Ninf : Finset {t // S t} → Submodule K (Z ⧸ B.comap Z.subtype) := fun F => ⨅ t ∈ F, N t
  obtain ⟨F, -, hF⟩ := (measure fun F : Finset {t // S t} => finrank K (Ninf F)).wf.has_min
    Set.univ ⟨∅, trivial⟩
  classical
  have hFle : ∀ s, Ninf F ≤ N s := by
    intro s
    have hins : Ninf (insert s F) = N s ⊓ Ninf F := Finset.iInf_insert _ _ _
    have hmin : ¬ finrank K (Ninf (insert s F)) < finrank K (Ninf F) := hF (insert s F) trivial
    have heq : Ninf (insert s F) = Ninf F := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [hins]; exact inf_le_right
      · exact not_lt.mp hmin
    rw [← heq, hins]; exact inf_le_left
  have hinv : ∀ (s t : {t // S t}) (q : K[X]) (w : Z ⧸ B.comap Z.subtype), w ∈ N t →
      aeval (φ (Tg s)) q w ∈ N t := by
    intro s t q w hw
    have hc : Commute (φ (Tg s)) (φ (Tg t)) := by
      refine LinearMap.ext fun w => Submodule.Quotient.induction_on _ w fun z => ?_
      rw [Module.End.mul_apply, Module.End.mul_apply, quotAlgHom_mk, quotAlgHom_mk, quotAlgHom_mk,
        quotAlgHom_mk, Submodule.Quotient.eq]
      exact hcomm s.1 t.1 s.2 t.2 z z.2
    have hc2 : Commute (aeval (φ (Tg s)) q) (aeval (φ (Tg t)) ((X - C (lam t.1)) ^ d)) :=
      Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K _)
        (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton K _)
          hc.symm).symm
    have hw' := LinearMap.mem_ker.mp hw
    refine LinearMap.mem_ker.mpr ?_
    rw [← Module.End.mul_apply, ← hc2.eq, Module.End.mul_apply, hw', map_zero]
  have hprod : ∀ (l : List {t // S t}) (w : Z ⧸ B.comap Z.subtype) (t : {t // S t}), t ∈ l →
      φ (l.map fun s => aeval (Tg s) (p s)).prod w ∈ N t := by
    intro l
    induction l with
    | nil => intro w t ht; simp at ht
    | cons a l ih =>
      intro w t ht
      rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply, ← aeval_algHom_apply]
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact LinearMap.mem_ker.mpr (hp2 _ _)
      · exact hinv _ _ _ _ (ih _ _ ht')
  let P : FreeAlgebra K ι := (F.toList.map fun t => aeval (FreeAlgebra.ι K t.1) (p t)).prod
  let Q : stabAlg Z B := (F.toList.map fun t => aeval (Tg t) (p t)).prod
  have hPQ : FreeAlgebra.lift K T P = (Q : Module.End K V) := by
    rw [show (Q : Module.End K V) = (stabAlg Z B).val Q from rfl]
    simp only [P, Q, map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply]
    rw [← aeval_algHom_apply, ← aeval_algHom_apply, FreeAlgebra.lift_ι_apply]
    rfl
  have hPmem : P ∈ Algebra.adjoin K (FreeAlgebra.ι K '' {t | S t}) := by
    refine Subalgebra.list_prod_mem _ fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image_of_mem (FreeAlgebra.ι K) (show t.1 ∈ {t | S t} from t.2)))
      (aeval_mem_adjoin_singleton K _)
  have hPlam : FreeAlgebra.lift K lam P = 1 := by
    simp only [P, map_list_prod, List.map_map]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hx
    simp only [Function.comp_apply]
    rw [← aeval_algHom_apply, FreeAlgebra.lift_ι_apply, coe_aeval_eq_eval, hp1]
  refine ⟨P, hPmem, hPlam, fun z hz s hs => ?_⟩
  rw [hPQ]
  have hQz : (Q : Module.End K V) z ∈ Z := Q.2.1 z hz
  refine hgen _ hQz d (fun t ht => ?_) s hs
  let U : stabAlg Z B := (Tg ⟨t, ht⟩ - algebraMap K (stabAlg Z B) (lam t)) ^ d
  have hU : (U : Module.End K V) = (T t - lam t • 1) ^ d := by
    simp [U, Tg, Algebra.algebraMap_eq_smul_one]
  rw [← hU]
  have key : φ U (Submodule.Quotient.mk ⟨(Q : Module.End K V) z, hQz⟩) = 0 := by
    have h1 : φ Q (Submodule.Quotient.mk ⟨z, hz⟩) =
        Submodule.Quotient.mk ⟨(Q : Module.End K V) z, hQz⟩ := quotAlgHom_mk _ _ _ _
    rw [← h1]
    have hφU : φ U = aeval (φ (Tg ⟨t, ht⟩)) ((X - C (lam t)) ^ d) := by
      simp [U]
    rw [hφU]
    refine LinearMap.mem_ker.mp (hFle ⟨t, ht⟩ ?_)
    simp only [Ninf, Submodule.mem_iInf]
    intro s' hs'
    exact hprod _ _ _ (Finset.mem_toList.mpr hs')
  exact (quotAlgHom_mk_eq_zero Z B U _).mp key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelMulPowOfInvariantModPow
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.CongruenceDescent

theorem mem_Gamma_iff_exists {N : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ CongruenceSubgroup.Gamma N ↔ ∃ B : Matrix (Fin 2) (Fin 2) ℤ, (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 + (N : ℤ) • B := by
  rw [CongruenceSubgroup.Gamma_mem]
  constructor
  · rintro ⟨h00, h01, h10, h11⟩
    have d00 : (N : ℤ) ∣ γ 0 0 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h00]; ring
    have d01 : (N : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h01
    have d10 : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10
    have d11 : (N : ℤ) ∣ γ 1 1 - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11]; ring
    obtain ⟨a, ha⟩ := d00; obtain ⟨b, hb⟩ := d01; obtain ⟨c, hc⟩ := d10; obtain ⟨d, hd⟩ := d11
    refine ⟨!![a, b; c, d], ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  · rintro ⟨B, hB⟩
    have e : ∀ i j, γ i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j + N * B i j := fun i j => by
      rw [show γ i j = (γ : Matrix (Fin 2) (Fin 2) ℤ) i j from rfl, hB, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> simp

theorem Gamma_le_of_dvd {N M : ℕ} (h : N ∣ M) : CongruenceSubgroup.Gamma M ≤ CongruenceSubgroup.Gamma N := by
  intro γ hγ
  obtain ⟨B, hB⟩ := mem_Gamma_iff_exists.1 hγ
  obtain ⟨c, rfl⟩ := h
  exact mem_Gamma_iff_exists.2 ⟨(c : ℤ) • B, by rw [hB, smul_smul]; push_cast; ring_nf⟩

theorem pow_mem_Gamma_mul {L q : ℕ} (hq : q ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma L) :
    γ ^ q ∈ CongruenceSubgroup.Gamma (L * q) := by
  obtain ⟨B, hB⟩ := mem_Gamma_iff_exists.1 hγ
  have key : ∀ m : ℕ, ∃ Y : Matrix (Fin 2) (Fin 2) ℤ,
      (γ : Matrix (Fin 2) (Fin 2) ℤ) ^ m = 1 + ((m : ℤ) * L) • B + ((L : ℤ) * L) • (B * B * Y) := by
    intro m
    induction m with
    | zero => exact ⟨0, by simp⟩
    | succ m ih =>
      obtain ⟨Y, hY⟩ := ih
      refine ⟨(m : ℤ) • 1 + Y + Y * ((L : ℤ) • B), ?_⟩
      rw [pow_succ, hY, hB]
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_add, smul_smul, Matrix.mul_assoc]
      push_cast
      module
  obtain ⟨Y, hY⟩ := key q
  obtain ⟨c, rfl⟩ := hq
  refine mem_Gamma_iff_exists.2 ⟨B + (c : ℤ) • (B * B * Y), ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_pow, hY, smul_add, smul_smul]
  push_cast
  module

theorem pow_pow_mem_Gamma_mul {L q : ℕ} (hq : q ∣ L) {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma L) (j : ℕ) :
    γ ^ (q ^ j) ∈ CongruenceSubgroup.Gamma (L * q ^ j) := by
  induction j with
  | zero => simpa only [pow_zero, pow_one, mul_one] using hγ
  | succ j ih =>
    rw [pow_succ, pow_mul, ← mul_assoc]
    exact pow_mem_Gamma_mul (hq.mul_right _) ih

theorem coprime_card_of_pow_eq_one {Q : Type} [Group Q] [Finite Q] {l m : ℕ} (hl : l.Prime) (hm : l.Coprime m)
    (h : ∀ x : Q, x ^ m = 1) : l.Coprime (Nat.card Q) := by
  rw [hl.coprime_iff_not_dvd]
  intro hd
  haveI := Fact.mk hl
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hd
  have := orderOf_dvd_of_pow_eq_one (h x)
  rw [hx] at this
  exact (hl.coprime_iff_not_dvd.1 hm) this

theorem exists_invariant {H A : Type} [Group H] [CommGroup A] (s : H → A →* A)
    (hs : ∀ g h a, s (g * h) a = s h (s g a)) (D : Subgroup H) [D.Normal] [Finite (H ⧸ D)] {m : ℕ}
    (hm : m.Coprime (Nat.card (H ⧸ D))) (f : A) (hD : ∀ δ ∈ D, s δ f = f) (hf : ∀ γ, ∃ g : A, s γ f = f * g ^ m) :
    ∃ h : A, ∀ γ, s γ (f * h ^ m) = f * h ^ m := by
  classical
  haveI := Fintype.ofFinite (H ⧸ D)
  choose g hg using hf
  have hwd : ∀ a b : H, (a : H ⧸ D) = b → s a f = s b f := by
    intro a b hab
    have h1 : a * (a⁻¹ * b) * a⁻¹ ∈ D := Subgroup.Normal.conj_mem ‹_› _ (QuotientGroup.eq.1 hab) a
    have h2 : b = (a * (a⁻¹ * b) * a⁻¹) * a := by group
    conv_rhs => rw [h2, hs, hD _ h1]
  set F : A := ∏ x : H ⧸ D, s x.out f with hF
  have hinv : ∀ γ, s γ F = F := by
    intro γ
    rw [hF, map_prod]
    refine Fintype.prod_equiv (Equiv.mulRight (γ : H ⧸ D)) _ _ fun x => ?_
    rw [← hs]
    apply hwd
    simp
  have hFeq : F = f ^ Nat.card (H ⧸ D) * (∏ x : H ⧸ D, g x.out) ^ m := by
    rw [hF]
    simp only [hg, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hm
  refine ⟨f ^ (-u) * (∏ x : H ⧸ D, g x.out) ^ v, fun γ => ?_⟩
  have e : f * (f ^ (-u) * (∏ x : H ⧸ D, g x.out) ^ v) ^ m = F ^ v := by
    have e1 : f * f ^ (-u * (m : ℤ)) = f ^ ((Nat.card (H ⧸ D) : ℤ) * v) := by
      rw [← _root_.zpow_one_add]
      congr 1
      linear_combination -huv
    rw [hFeq, mul_pow, _root_.mul_zpow, ← _root_.zpow_natCast, ← _root_.zpow_natCast, ← _root_.zpow_natCast,
      ← _root_.zpow_natCast]
    simp only [← _root_.zpow_mul]
    rw [← mul_assoc, e1, mul_comm v]
  rw [e, map_zpow, hinv]

end GlobalTheory.KZ.ES.CongruenceDescent

namespace GlobalTheory.KZ.ES

open CongruenceDescent CongruenceSubgroup in

theorem exists_lev_mul_pow_of_invariant_mod_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (l n M e : ℕ), l.Prime → 0 < M → ∀ f : X.Kˣ, Lev X (M ^ e) f → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) → ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) * (h : X.K) ^ (l ^ n)) := by
  intro Ω _ _ _ ε X l n M e hl hM f hlev hf
  obtain ⟨a, q, hq, hMq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.ne_one
  have hlq : l.Coprime q := hl.coprime_iff_not_dvd.2 hq
  let H : Subgroup SL(2, ℤ) := Gamma (M * l ^ (a * e))
  haveI := Gamma_normal (M ^ e)
  haveI : NeZero (M ^ e) := ⟨(pow_pos hM e).ne'⟩
  let D : Subgroup H := (Gamma (M ^ e)).subgroupOf H
  haveI : D.FiniteIndex := inferInstance
  have hcard : l.Coprime (Nat.card (H ⧸ D)) := by
    refine coprime_card_of_pow_eq_one hl (hlq.pow_right e) fun x => ?_
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    refine Gamma_le_of_dvd ?_ (pow_pow_mem_Gamma_mul (q := q) ?_ γ.2 e)
    · exact ⟨M, by rw [hMq]; ring⟩
    · exact ⟨l ^ a * l ^ (a * e), by rw [hMq]; ring⟩
  obtain ⟨h, hh⟩ := exists_invariant (H := H) (A := X.Kˣ)
    (fun γ => Units.map (X.sl (ofSL γ) : X.K →* X.K))
    (fun g h a => Units.ext (by simp [X.sl_mul])) D (hcard.pow_left n) f
    (fun δ hδ => Units.ext (by simpa using hlev δ hδ))
    (fun γ => by
      obtain ⟨g, hg⟩ := hf γ (Gamma_le_of_dvd (dvd_mul_right _ _) γ.2)
      exact ⟨g, Units.ext (by simpa using hg)⟩)
  refine ⟨a * e, h, fun γ hγ => ?_⟩
  have := congrArg Units.val (hh ⟨γ, hγ⟩)
  simpa using this

end GlobalTheory.KZ.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevel
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FamOfLevel

theorem redGL_mul (N : ℕ) (γ δ : SL(2, ℤ)) : redGL N (γ * δ) = redGL N γ * redGL N δ := by
  simp [redGL]

theorem redGL_eq_one_iff (N : ℕ) (γ : SL(2, ℤ)) : redGL N γ = 1 ↔ γ ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem', redGL]
  constructor
  · intro h
    apply Matrix.SpecialLinearGroup.toGL_injective
    simpa using h
  · intro h
    rw [h]; simp

theorem slash_eq_of_redGL_eq (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) {γ δ : SL(2, ℤ)}
    (h : redGL N γ = redGL N δ) : f ∣[k] γ = f ∣[k] δ := by
  have hη : γ * δ⁻¹ ∈ CongruenceSubgroup.Gamma N := by
    rw [← redGL_eq_one_iff, redGL_mul, h, ← redGL_mul, mul_inv_cancel]
    simp [redGL]
  have : γ = (γ * δ⁻¹) * δ := by group
  rw [this, SlashAction.slash_mul, hf _ hη]

theorem exists_family (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma N, f ∣[k] γ = f) :
    ∃ F : GL (Fin 2) (ZMod N) → ℍ → ℂ, IsFam (gact N 1) k F ∧
      (∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ) ∧
      ∀ α, (∃ γ : SL(2, ℤ), α = redGL N γ) ∨ F α = 0 := by
  classical
  let F : GL (Fin 2) (ZMod N) → ℍ → ℂ := fun α =>
    if h : ∃ γ : SL(2, ℤ), α = redGL N γ then f ∣[k] h.choose else 0
  have hF : ∀ γ : SL(2, ℤ), F (redGL N γ) = f ∣[k] γ := by
    intro γ
    have h : ∃ δ : SL(2, ℤ), redGL N γ = redGL N δ := ⟨γ, rfl⟩
    simp only [F, dif_pos h]
    exact slash_eq_of_redGL_eq N k f hf h.choose_spec.symm
  refine ⟨F, ?_, hF, ?_⟩
  · intro α γ
    rw [gact_one]
    by_cases h : ∃ δ : SL(2, ℤ), α = redGL N δ
    · obtain ⟨δ, rfl⟩ := h
      rw [hF, ← redGL_mul, hF, SlashAction.slash_mul]
    · have h' : ¬ ∃ δ : SL(2, ℤ), α * redGL N γ = redGL N δ := by
        rintro ⟨δ, hδ⟩
        apply h
        refine ⟨δ * γ⁻¹, ?_⟩
        rw [redGL_mul, ← hδ, mul_assoc, ← redGL_mul, mul_inv_cancel]
        simp [redGL]
      simp only [F, dif_neg h, dif_neg h']
      exact SlashAction.zero_slash _ _
  · intro α
    by_cases h : ∃ γ : SL(2, ℤ), α = redGL N γ
    · exact Or.inl h
    · right; simp only [F, dif_neg h]

end GlobalTheory.FamOfLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerPlaceAtUpperHalfPlanePointStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tower_place_at_upperHalfPlane_point : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ τ ∈ Hs, ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ f : X.K, f ∈ W ↔ ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  first | exact @GlobalTheory.KZ.H3.exists_place_at_point | exact GlobalTheory.KZ.H3.exists_place_at_point | (intros; apply GlobalTheory.KZ.H3.exists_place_at_point <;> assumption)
end

