import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExpEqOfPeriodsOfMarking

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlacePer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem exists_extend {M V E : Type} [AddCommGroup M] [AddCommGroup V] [AddCommGroup E] [Module ℚ E]
    (j : M →+ V) (hj : Function.Injective j) (hd : ∀ w, ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • w = j u) (P : M →+ E) :
    ∃ Q : V →+ E, ∀ u, Q (j u) = P u := by
  choose m u hm h using hd
  have key : ∀ w (n : ℕ) (v : M), n ≠ 0 → n • w = j v →
      ((m w : ℚ)⁻¹) • P (u w) = ((n : ℚ)⁻¹) • P v := by
    intro w n v hn hv
    have h1 : n • u w = m w • v := hj (by
      rw [map_nsmul, map_nsmul, ← h w, ← hv, smul_comm])
    have h2 : n • P (u w) = m w • P v := by rw [← map_nsmul, ← map_nsmul, h1]
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hm' : (m w : ℚ) ≠ 0 := by exact_mod_cast hm w
    have h3 : (n : ℚ) • P (u w) = (m w : ℚ) • P v := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h2]
    calc ((m w : ℚ)⁻¹) • P (u w) = ((m w : ℚ)⁻¹ * (n : ℚ)⁻¹) • ((n : ℚ) • P (u w)) := by
          rw [smul_smul]; congr 1; field_simp
      _ = ((n : ℚ)⁻¹) • P v := by rw [h3, smul_smul]; congr 1; field_simp
  refine ⟨AddMonoidHom.mk' (fun w => ((m w : ℚ)⁻¹) • P (u w)) ?_, ?_⟩
  · intro a b
    have hab : (m a * m b) • (a + b) = j (m b • u a + m a • u b) := by
      rw [map_add, map_nsmul, map_nsmul, ← h a, ← h b, smul_add, mul_smul, mul_smul,
        smul_comm (m a) (m b) a]
    have hk := key (a + b) (m a * m b) _ (mul_ne_zero (hm a) (hm b)) hab
    have hma : (m a : ℚ) ≠ 0 := by exact_mod_cast hm a
    have hmb : (m b : ℚ) ≠ 0 := by exact_mod_cast hm b
    rw [hk, map_add, map_nsmul, map_nsmul, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, smul_smul]
    push_cast
    congr 2 <;> field_simp
  · intro v
    have hk := key (j v) 1 v one_ne_zero (by simp)
    simpa using hk

private theorem finrank_eq_of_place {M V : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    [AddCommGroup V] [Module ℚ V] (j : M →+ V) (hj : Function.Injective j)
    (hd : ∀ w, ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • w = j u) :
    Module.finrank ℤ M = Module.finrank ℚ V :=
  _root_.UpperTheory.Reformulated.B.FinrankIntEqFinrankRat.finrank_eq_of_place j hj hd

private theorem period_of_basis {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {g : ℕ}
    (P : M →+ (Fin g → ℂ)) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hc : Module.finrank ℤ M = 2 * g) :
    Function.Injective P ∧ DiscreteTopology P.range := by
  let b := Module.finBasis ℤ M
  let v : Fin (Module.finrank ℤ M) → (Fin g → ℂ) := fun i => P (b i)
  have hPx : ∀ x, P x = ∑ i, (b.repr x i) • v i := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hs]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    rw [hPx]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  have hfr : Fintype.card (Fin (Module.finrank ℤ M)) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Fintype.card_fin, hc, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have li : LinearIndependent ℝ v := linearIndependent_of_top_le_span_of_card_eq_finrank hsp hfr
  refine ⟨(injective_iff_map_eq_zero P).mpr fun x hx => ?_, ?_⟩
  · have h0 : ∑ i, ((b.repr x i : ℤ) : ℝ) • v i = 0 := by
      rw [← hx, hPx]
      exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ _ _
    have h1 := Fintype.linearIndependent_iff.mp li _ h0
    apply b.repr.injective
    ext i
    simpa using h1 i
  · let bb : Module.Basis (Fin (Module.finrank ℤ M)) ℝ (Fin g → ℂ) := Module.Basis.mk li hsp
    have hset : (P.range : Set (Fin g → ℂ)) = (Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ)) := by
      have hb : Set.range bb = Set.range v := by
        rw [Module.Basis.coe_mk]
      rw [hb]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        show P x ∈ Submodule.span ℤ (Set.range v)
        rw [hPx]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · intro hy
        have hy' : y ∈ Submodule.span ℤ (Set.range v) := hy
        induction hy' using Submodule.span_induction with
        | mem a ha => obtain ⟨i, rfl⟩ := ha; exact ⟨b i, rfl⟩
        | zero => exact zero_mem P.range
        | add a c _ _ h1 h2 => exact add_mem (h1 (by assumption)) (h2 (by assumption))
        | smul r a _ h1 => exact zsmul_mem (h1 (by assumption)) r
    have hd : DiscreteTopology (Submodule.span ℤ (Set.range bb)) := inferInstance
    have hd' : DiscreteTopology ((Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ))) := hd
    rw [← hset] at hd'
    exact hd'

private theorem herm_smul_mat {g : ℕ} (r : ℂ) (H : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    hermForm (r • H) x y = r * hermForm H x y := by
  simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]

private theorem herm_nsmul {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (m n : ℕ) (x y : Fin g → ℂ) :
    hermForm H (m • x) (n • y) = ((m : ℂ) * n) * hermForm H x y := by
  simp only [hermForm]
  rw [← Nat.cast_smul_eq_nsmul ℂ m x, ← Nat.cast_smul_eq_nsmul ℂ n y, star_smul, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, star_natCast]
  ring

private theorem herm_scale {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) • Hm).IsHermitian ∧ ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm ((r : ℂ) • Hm) z z).re := by
  refine ⟨?_, fun z hz => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq]
    simp
  · rw [herm_smul_mat, Complex.re_ofReal_mul]
    exact mul_pos hr (hpos z hz)

theorem UpperTheory.Gal.W2.placePer_of :
    UpperTheory.Gal.W2.PlacePer := by
  intro p _ D G L β ρ D' j hpl
  obtain ⟨hinj, hact, hden, s, hs, hEF⟩ := hpl
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hform : ∀ (m n : ℕ) (u w : VQ D),
      formB L β (m • u) (n • w) = (m : ℚ) * n * formB L β u w := by
    intro m n u w
    simp only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  refine ⟨fun P hP => ?_, fun Q hQ hrk => ?_⟩
  · obtain ⟨hPa, -, -, hPs, Hm, hH, hpos, hIm⟩ := hP
    obtain ⟨Q, hQ⟩ := exists_extend j hinj hden P
    have hsc := herm_scale hH hpos (inv_pos.mpr hsR)
    refine ⟨Q, ⟨fun c w => ?_, ?_, ((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun u w => ?_⟩, hQ⟩
    · obtain ⟨m, a, hm, h⟩ := hden w
      apply IsAddTorsionFree.nsmul_right_injective hm
      show m • Q (actQ D c w) = m • (ρ c *ᵥ Q w)
      have e1 : m • Q (actQ D c w) = P (c • a) := by
        rw [← map_nsmul, ← map_nsmul (actQ D c), h, ← hact, hQ]
      have e2 : m • (ρ c *ᵥ Q w) = ρ c *ᵥ P a := by
        rw [← hQ, ← h, map_nsmul, Matrix.mulVec_smul]
      rw [e1, e2, hPa]
    · rw [eq_top_iff, ← hPs]
      apply Submodule.span_mono
      rintro _ ⟨x, rfl⟩
      exact ⟨j x, hQ x⟩
    · obtain ⟨m, a, hm, ha⟩ := hden u
      obtain ⟨n, b, hn, hb⟩ := hden w
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have h1 : hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b)) =
          (((m : ℝ) * n : ℝ) : ℂ) * hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w) := by
        rw [← ha, ← hb, map_nsmul, map_nsmul, herm_nsmul]
        push_cast
        rfl
      have h2 : (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b))).im =
          ((s : ℝ))⁻¹ * (D'.EF a b : ℝ) := by
        rw [herm_smul_mat, hQ, hQ, Complex.im_ofReal_mul, hIm]
      have h3 : (D'.EF a b : ℝ) = (s : ℝ) * ((m : ℝ) * n * (formB L β u w : ℚ)) := by
        have h4 := hEF a b
        rw [← ha, ← hb, hform] at h4
        exact_mod_cast h4
      rw [h1, Complex.im_ofReal_mul, h3] at h2
      have hs0 : (s : ℝ) ≠ 0 := hsR.ne'
      have h5 : ((m : ℝ) * n) * (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w)).im =
          ((m : ℝ) * n) * (formB L β u w : ℚ) := by
        rw [h2]
        field_simp
      exact mul_left_cancel₀ (mul_ne_zero hmR hnR) h5
  · obtain ⟨hQa, hQs, Hm, hH, hpos, hIm⟩ := hQ
    have hc : Module.finrank ℤ D'.La = 2 * D.g := by
      rw [finrank_eq_of_place j hinj hden, hrk]
      haveI : Module.Free ℤ D.La := D.freeLa
      exact Module.finrank_baseChange
    have hs' : Submodule.span ℝ (Set.range (Q.comp j)) = ⊤ := by
      rw [eq_top_iff, ← hQs]
      apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      obtain ⟨m, a, hm, h⟩ := hden w
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have e : Q w = (m : ℝ)⁻¹ • Q (j a) := by
        rw [← h, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨hi, hdisc⟩ := period_of_basis (Q.comp j) hs' hc
    have hsc := herm_scale hH hpos hsR
    refine ⟨fun c u => ?_, hi, hdisc, hs', ((s : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun x y => ?_⟩
    · simp only [AddMonoidHom.comp_apply]
      rw [hact, hQa]
    · simp only [AddMonoidHom.comp_apply]
      rw [herm_smul_mat, Complex.im_ofReal_mul, hIm]
      have h4 := hEF x y
      exact_mod_cast h4.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRhoSig
section
noncomputable section

open NumberField
open scoped TensorProduct Matrix Classical
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory.Gal.W2

private theorem tens_inj (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] :
    Function.Injective (fun x : O => x ⊗ₜ[ℤ] (1 : ℤ_[p])) := by
  have hinj : Function.Injective (Algebra.linearMap ℤ ℤ_[p]) := by
    intro a b h
    exact RingHom.injective_int (algebraMap ℤ ℤ_[p]) h
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := O) (Algebra.linearMap ℤ ℤ_[p]) hinj
  intro x y hxy
  have h2 : x ⊗ₜ[ℤ] (1 : ℤ) = y ⊗ₜ[ℤ] (1 : ℤ) := h1 (by simpa using hxy)
  have h3 := congrArg (TensorProduct.rid ℤ O) h2
  simpa using h3

private theorem comm_of_split (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] {R : Type} [CommRing R]
    {m : ℕ} (hm : m = 1) (f : (O ⊗[ℤ] ℤ_[p]) ≃+* Matrix (Fin m) (Fin m) R) (x y : O) : x * y = y * x := by
  subst hm
  apply tens_inj p
  have hc : ∀ A B : Matrix (Fin 1) (Fin 1) R, A * B = B * A := by
    intro A B
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  have := hc (f (x ⊗ₜ[ℤ] (1 : ℤ_[p]))) (f (y ⊗ₜ[ℤ] (1 : ℤ_[p])))
  rw [← map_mul, ← map_mul] at this
  have h2 := f.injective this
  simpa using h2

private theorem a_inj {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] : Function.Injective (algebraMap (𝓞 F) O) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hI : RingHom.ker (algebraMap (𝓞 F) O) ≠ ⊥ := fun h => h0 (by
    have h1 : c ∈ RingHom.ker (algebraMap (𝓞 F) O) := hc
    rw [h] at h1
    simpa using h1)
  have hN := Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) O))
  have hN0 : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hI
  rw [RingHom.mem_ker, map_natCast] at hN
  have h1 : (Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) : ℤ) • (1 : O) = 0 := by
    rw [zsmul_one]
    exact_mod_cast hN
  rcases smul_eq_zero.mp h1 with h | h
  · exact hN0 (by exact_mod_cast h)
  · exact one_ne_zero h

private theorem a_onto {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hcomm : ∀ x y : O, x * y = y * x)
    (hc : ∀ x : O, ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  intro x
  obtain ⟨c, e, he, hx⟩ := hc x
  letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }
  obtain ⟨P, hP, hPx⟩ : IsIntegral ℤ x := IsIntegral.of_finite ℤ x
  have hQ : Polynomial.eval₂ (algebraMap ℤ O) (algebraMap ℤ O e * x) (P.scaleRoots e) = 0 := by
    rw [Polynomial.scaleRoots_eval₂_mul, hPx, mul_zero]
  have hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c := by
    rw [← hx]; simp [zsmul_eq_mul]
  have hQ2 : Polynomial.eval₂ (algebraMap ℤ (𝓞 F)) c (P.scaleRoots e) = 0 := by
    apply a_inj (O := O)
    rw [map_zero, Polynomial.hom_eval₂, ← hex, ← hQ]
    congr 1
    exact RingHom.ext_int _ _
  have hQ3 : Polynomial.eval₂ (algebraMap ℤ F) (c : F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 F) F) hQ2
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [← this]
    congr 1
  have heF : (algebraMap ℤ F e) ≠ 0 := by simpa using he
  have hcF : (c : F) = algebraMap ℤ F e * ((c : F) / algebraMap ℤ F e) := by field_simp
  rw [hcF, Polynomial.scaleRoots_eval₂_mul] at hQ3
  have hint : IsIntegral ℤ ((c : F) / algebraMap ℤ F e) :=
    ⟨P, hP, (mul_eq_zero.mp hQ3).resolve_left (pow_ne_zero _ heF)⟩
  obtain ⟨c', hc'⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint
  refine ⟨c', ?_⟩
  have hcc : c = e • c' := by
    apply RingOfIntegers.ext
    rw [hcF, ← hc']
    simp [zsmul_eq_mul]
  have h3 : e • (algebraMap (𝓞 F) O c' - x) = 0 := by
    rw [smul_sub, hx, hcc, zsmul_eq_mul, zsmul_eq_mul]
    simp
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h he
  · exact sub_eq_zero.mp h

private theorem root_cases (tr nm : ℤ) (hd : tr ^ 2 - 4 * nm < 0) (r z : ℂ) (hr : r ^ 2 - tr * r + nm = 0)
    (hz : z ^ 2 - tr * z + nm = 0) : (starRingEnd ℂ) r ≠ r ∧ (z = r ∨ z = (starRingEnd ℂ) r) := by
  have hne : (starRingEnd ℂ) r ≠ r := by
    intro h
    obtain ⟨t, rfl⟩ := Complex.conj_eq_iff_real.mp h
    have h1 : (t : ℂ) ^ 2 - (tr : ℝ) * t + (nm : ℝ) = 0 := by simpa using hr
    have h2 : t ^ 2 - (tr : ℝ) * t + (nm : ℝ) = 0 := by exact_mod_cast h1
    have h3 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * t - tr)]
  refine ⟨hne, ?_⟩
  have hr' : ((starRingEnd ℂ) r) ^ 2 - tr * (starRingEnd ℂ) r + nm = 0 := by
    have := congrArg (starRingEnd ℂ) hr
    simpa using this
  have hs : r + (starRingEnd ℂ) r = tr := by
    have h1 : (r - (starRingEnd ℂ) r) * (r + (starRingEnd ℂ) r - tr) = 0 := by
      linear_combination hr - hr'
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact sub_eq_zero.mp h
  have h2 : (z - r) * (z - (starRingEnd ℂ) r) = 0 := by
    rw [← hs] at hz hr
    linear_combination hz - hr
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem sum_mult {F : Type} [Field F] [NumberField F] (n : ℕ) (hn : 1 ≤ n) (t₀ : F →+* ℂ)
    (ε : (F →+* ℂ) → ℕ) (cx : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ)
    (eps : ∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ → ε τ + ε (ComplexEmbedding.conjugate τ) = 1) :
    2 * ∑ τ : F →+* ℂ, typeMult n t₀ ε τ = n * Module.finrank ℚ F := by
  have hinv : ∀ σ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    ComplexEmbedding.involutive_conjugate F
  have hc0 : ComplexEmbedding.conjugate t₀ ≠ t₀ := cx t₀
  have hw : ∀ τ, typeMult n t₀ ε τ + typeMult n t₀ ε (ComplexEmbedding.conjugate τ) = n := by
    intro τ
    by_cases h1 : τ = t₀
    · subst h1
      simp only [typeMult, if_true, if_neg hc0]
      omega
    by_cases h2 : τ = ComplexEmbedding.conjugate t₀
    · subst h2
      simp only [typeMult, hinv, if_neg hc0, if_true]
      omega
    have h3 : ComplexEmbedding.conjugate τ ≠ t₀ := fun h => h2 (by rw [← h, hinv])
    have h4 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀ := fun h =>
      h1 ((ComplexEmbedding.involutive_conjugate F).injective h)
    simp only [typeMult, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
    rw [← Nat.mul_add, eps τ h1 h2, Nat.mul_one]
  have hs : ∑ τ : F →+* ℂ, typeMult n t₀ ε (ComplexEmbedding.conjugate τ) = ∑ τ : F →+* ℂ, typeMult n t₀ ε τ :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate F)) (typeMult n t₀ ε)
  have h2 : ∑ τ : F →+* ℂ, (typeMult n t₀ ε τ + typeMult n t₀ ε (ComplexEmbedding.conjugate τ)) =
      n * Module.finrank ℚ F := by
    simp only [hw, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Embeddings.card F ℂ, mul_comm]
  rw [Finset.sum_add_distrib, hs] at h2
  omega

theorem rhoSig_of : RhoSig := by
  intro p _ D ha hm t₀ ht
  haveI := D.freeO
  haveI := D.finO
  have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]
    simpa using hd
  obtain ⟨f⟩ := D.splitP
  have hcomm : ∀ x y : D.O, x * y = y * x := comm_of_split p hm f.toRingEquiv
  have hinj : Function.Injective (algebraMap (𝓞 D.F) D.O) := a_inj
  have honto : Function.Surjective (algebraMap (𝓞 D.F) D.O) :=
    a_onto hcomm fun x => D.central x (hcomm x)
  let e : 𝓞 D.F ≃+* D.O := RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) ⟨hinj, honto⟩
  have he : ∀ c : 𝓞 D.F, e.symm (algebraMap (𝓞 D.F) D.O c) = c := fun c => e.symm_apply_apply c
  have h0 : 0 < D.a := by omega
  have ht0 : t₀ (D.ω : D.F) = D.ρc := by
    rw [← ht ⟨0, h0⟩]
    exact D.tau_ω _
  have hroot : ∀ τ : D.F →+* ℂ, (τ (D.ω : D.F)) ^ 2 - D.tr * τ (D.ω : D.F) + D.nm = 0 := by
    intro τ
    have h1 := congrArg (fun x : 𝓞 D.F => τ (x : D.F)) D.tr_eq
    have h2 := congrArg (fun x : 𝓞 D.F => τ (x : D.F)) D.nm_eq
    simp only [map_add, map_mul, map_intCast] at h1 h2
    rw [← h1, ← h2]
    ring
  have hcx : ∀ τ : D.F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ := by
    intro τ h
    have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
    exact (InfinitePlace.isComplex_mk_iff.mp hc) (ComplexEmbedding.isReal_iff.mpr h)
  have heps : ∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ →
      epsD D τ + epsD D (ComplexEmbedding.conjugate τ) = 1 := by
    intro τ _ _
    obtain ⟨hne, hcase⟩ := root_cases D.tr D.nm D.disc_neg D.ρc (τ (D.ω : D.F)) D.ρc_root (hroot τ)
    unfold epsD
    rw [ComplexEmbedding.conjugate_coe_eq]
    rcases hcase with h | h
    · rw [h, if_pos rfl, if_neg hne]
    · rw [h, if_neg hne, Complex.conj_conj, if_pos rfl]
  have hsum : ∑ τ : D.F →+* ℂ, typeMult D.n t₀ (epsD D) τ = D.g := by
    have h2 := sum_mult D.n D.n_pos t₀ (epsD D) hcx heps
    unfold Datum.g
    rw [hm, one_mul, ← h2]
    simp
  obtain ⟨E⟩ : Nonempty (Fin D.g ≃ Σ τ : D.F →+* ℂ, Fin (typeMult D.n t₀ (epsD D) τ)) :=
    ⟨(Fintype.equivFinOfCardEq (by simp [hsum])).symm⟩
  let ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ :=
    (Matrix.diagonalRingHom (Fin D.g) ℂ).comp
      ((Pi.ringHom fun i => ((E i).1).comp (algebraMap (𝓞 D.F) D.F)).comp (e.symm : D.O →+* 𝓞 D.F))
  have hρ : ∀ c : 𝓞 D.F, ρ (algebraMap (𝓞 D.F) D.O c) = Matrix.diagonal fun i => (E i).1 (c : D.F) := by
    intro c
    simp only [ρ, RingHom.comp_apply, RingHom.coe_coe, he]
    rfl
  refine ⟨ρ, ⟨honto, fun c => ⟨D.bar c, ?_, fun τ => ?_⟩, hcx, D.n_pos, heps, fun c => ?_⟩⟩
  · show (D.star (algebraMap (𝓞 D.F) D.O c)).unop = _
    rw [D.star_F]
    rfl
  · rw [D.bar_eq, IsCMField.complexEmbedding_complexConj]
  · rw [hρ, Matrix.trace_diagonal,
      Equiv.sum_comp E (fun s : (Σ τ : D.F →+* ℂ, Fin (typeMult D.n t₀ (epsD D) τ)) => s.1 (c : D.F)),
      Fintype.sum_sigma]
    simp

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRigid
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.rigid_of :
    UpperTheory.Gal.W2.Rigid := by
  intro O _ bar g ρ Λ N D' t P w h hN hfull hper ⟨hiso, hmark⟩ hPw
  obtain ⟨-, hinj, hd, hspan, Hm, -, hpos, hIm⟩ := hper
  let σw : Module.End ℤ D'.La := (w.toLinearMap.toAddMonoidHom).toIntLinearMap
  have hσ : ∀ a, σw a = w a := fun _ => rfl
  let hR : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := h.toLinearMap.restrictScalars ℝ
  let B : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun u v => (hermForm Hm u v).im)
    (fun a b c => by simp [hermForm]) (fun r a b => by simp [hermForm])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add]) (fun r a b => by simp [hermForm, Matrix.mulVec_smul])
  have hB : B.compl₁₂ hR hR = B := by
    refine LinearMap.ext_on_range hspan fun a => LinearMap.ext_on_range hspan fun b => ?_
    show (hermForm Hm (h (P a)) (h (P b))).im = (hermForm Hm (P a) (P b)).im
    rw [← hPw, ← hPw, hIm, hIm, hiso]
  have hq : ∀ u, (hermForm Hm u u).re = B (Complex.I • u) u := fun u => by
    show _ = (hermForm Hm (Complex.I • u) u).im
    simp [hermForm]
  have hbd := GlobalTheory.ExpUnique.isBounded_sublevel (q := fun u => (hermForm Hm u u).re)
    (by unfold hermForm; fun_prop) (fun r u => by
      simp only [hq]
      rw [smul_comm, map_smul, map_smul, LinearMap.smul_apply, smul_smul, sq, smul_eq_mul]) hpos
  have key : σw = 1 := by
    refine GlobalTheory.ExpUnique.end_eq_one_of_invariant D'.La σw (fun a b hab => w.injective hab)
      (fun a => (hermForm Hm (P a) (P a)).re) (fun c => ?_) (fun a => ?_) N hN fun a => ?_
    · refine Set.Finite.of_finite_image (f := P) ((Metric.finite_isBounded_inter_isClosed
        (s := P.range) DiscreteTopology.isDiscrete (hbd c) AddSubgroup.isClosed_of_discrete).subset ?_) hinj.injOn
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨ha, a, rfl⟩
    · have h1 : h (Complex.I • P a) = Complex.I • h (P a) := map_smul h _ _
      simp only [hq, hσ, hPw]
      rw [← h1]
      have h2 := LinearMap.congr_fun₂ hB (Complex.I • P a) (P a)
      rw [LinearMap.compl₁₂_apply] at h2
      exact h2
    · obtain ⟨i, f, rfl⟩ := hfull a
      obtain ⟨e₀, he₀⟩ := hmark i
      refine ⟨e₀ + w f - f, ?_⟩
      have h3 : w (t i + N • f) = w (t i) + N • w f := by rw [map_add, map_nsmul]
      rw [hσ, h3, he₀, smul_sub, smul_add]
      abel
  intro u
  rw [← hσ, key]
  rfl
end

