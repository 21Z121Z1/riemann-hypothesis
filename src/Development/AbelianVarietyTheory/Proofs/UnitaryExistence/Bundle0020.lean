import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TwoDvdMultiplierOfThetaZActEqUnitMul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximationStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCompletion_rational_points_and_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ v, fv F v ∈ (hat F (L : Set (Fin n → E))) ↔ v ∈ L) ∧ (∀ N : ℕ, 0 < N → ∀ z ∈ (hat F (L : Set (Fin n → E))), ∃ x ∈ L, ∃ w ∈ (hat F (L : Set (Fin n → E))), z = fv F x + N • w) ∧ (∀ z : Fin n → RA F E, ∃ x : Fin n → E, z - fv F x ∈ (hat F (L : Set (Fin n → E)))) ∧ ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ (hat F (L : Set (Fin n → E))) := by
  first | exact @GlobalTheory.AdLat.hat_rational_points_and_approx | exact GlobalTheory.AdLat.hat_rational_points_and_approx | (intros; apply GlobalTheory.AdLat.hat_rational_points_and_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCompatibleNormTowerProfinite
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.NormTower

theorem exists_eventually_dvd_sub {E : Type} [Field E] [NumberField E] (U : Ultrafilter ℕ) (s : ℕ → 𝓞 E)
    (n : ℕ) (hn : 0 < n) : ∃ t : 𝓞 E, ∀ᶠ j in (U : Filter ℕ), (n : 𝓞 E) ∣ s j - t := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  haveI : Finite (𝓞 E ⧸ Ideal.span {(n : 𝓞 E)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  obtain ⟨c, hc⟩ := Ultrafilter.eq_pure_of_finite
    (U.map fun j => Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (s j))
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨t, ?_⟩
  have h : {Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) t} ∈
      U.map fun j => Ideal.Quotient.mk (Ideal.span {(n : 𝓞 E)}) (s j) := by
    rw [hc]; exact Ultrafilter.mem_pure.2 rfl
  rw [Ultrafilter.mem_map] at h
  filter_upwards [h] with j hj
  exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hj)

theorem exists_norm_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (ν : ℕ → ℤ), (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) → (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) → ∃ t : ℕ → 𝓞 E, (∀ n : ℕ, 0 < n → (n : 𝓞 E) ∣ t n * H.bar (t n) - (ν n : 𝓞 E)) ∧ (∀ n m : ℕ, 0 < n → 0 < m → (n : 𝓞 E) ∣ t (n * m) - t n) ∧ t l.M - 1 ∈ l.Mb := by
  intro E _ _ _ H l ν hcop hcomp
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hs : ∀ j : ℕ, ∃ t : 𝓞 E, ((j.factorial : ℕ) : 𝓞 E) ∣ t * H.bar t - (ν j.factorial : 𝓞 E) ∧
      (l.M ∣ j.factorial → t - 1 ∈ l.Mb) := fun j =>
    GlobalTheory.T.exists_hostNorm_mod_coprime_level_half E H l j.factorial (ν j.factorial) j.factorial_pos (hcop _ j.factorial_pos)
  choose s hs1 hs2 using hs
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : ∀ n : ℕ, 0 < n → ∀ᶠ j in (U : Filter ℕ), n ∣ j.factorial := by
    intro n hn
    have h : ∀ᶠ j : ℕ in Filter.cofinite, n ∣ j.factorial := by
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop n] with j hj
      exact Nat.dvd_factorial hn hj
    exact h.filter_mono Filter.hyperfilter_le_cofinite
  have ht : ∀ n : ℕ, ∃ t : 𝓞 E, 0 < n → ∀ᶠ j in (U : Filter ℕ), (n : 𝓞 E) ∣ s j - t := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨t, h⟩ := exists_eventually_dvd_sub U s n hn
      exact ⟨t, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose t ht using ht
  refine ⟨t, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨j, ⟨a, ha⟩, m, hm⟩ := ((ht n hn).and (hU n hn)).exists
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [hm, h, mul_zero]) j.factorial_ne_zero
      · exact h
    obtain ⟨b, hb⟩ := hs1 j
    obtain ⟨c, hc⟩ := hcomp n m hn hm0
    rw [hm] at hb
    have hc' : ((ν (n * m) : ℤ) : 𝓞 E) - (ν n : 𝓞 E) = (n : 𝓞 E) * (c : 𝓞 E) := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hc
    have hsj : s j = t n + n * a := by rw [← ha]; ring
    rw [hsj, map_add, map_mul, map_natCast] at hb
    push_cast at hb
    exact ⟨m * b + c - (a * H.bar (t n) + t n * H.bar a + n * a * H.bar a), by linear_combination hb + hc'⟩
  · intro n m hn hm
    obtain ⟨j, h1, h2⟩ := ((ht n hn).and (ht (n * m) (Nat.mul_pos hn hm))).exists
    have h3 : (n : 𝓞 E) ∣ s j - t (n * m) := dvd_trans ⟨(m : 𝓞 E), by push_cast; rfl⟩ h2
    have := dvd_sub h1 h3
    convert this using 1
    ring
  · obtain ⟨j, ⟨a, ha⟩, h2⟩ := ((ht l.M hM).and (hU l.M hM)).exists
    have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
      have : (l.M : 𝓞 E) ∈ Ideal.span {(l.M : 𝓞 E)} := Ideal.mem_span_singleton_self _
      rw [← l.prod] at this
      exact Ideal.mul_le_left this
    have h3 : (l.M : 𝓞 E) * a ∈ l.Mb := Ideal.mul_mem_right a _ hMb
    have h4 : t l.M - 1 = (s j - 1) - (l.M : 𝓞 E) * a := by rw [← ha]; ring
    rw [h4]
    exact Ideal.sub_mem _ (hs2 j h2) h3

end GlobalTheory.NormTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Translate

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

lemma fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  ext i; simp [fv, TensorProduct.tmul_add]

lemma fv_zero : fv F (0 : Fin n → E) = 0 := by
  ext i; simp [fv]

lemma fv_nsmul (d : ℕ) (x : Fin n → E) : fv F (d • x) = d • fv F x := by
  induction d with
  | zero => simp [fv_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, fv_add, ih]

lemma fv_smul (b : E) (x : Fin n → E) :
    fv F (b • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b : RA F E) • fv F x := by
  ext i; simp [fv]

lemma gen_eq (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (a ⊗ₜ[F] x i : RA F E)) = (a ⊗ₜ[F] (1 : E) : RA F E) • fv F x := by
  ext i; simp [fv]

lemma fv_mem_hat {S : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ S) : fv F x ∈ hat F S :=
  AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

lemma hat_smul_int {S : Set (Fin n → E)} {a : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → RA F E} (hz : z ∈ hat F S) :
    (a ⊗ₜ[F] (1 : E) : RA F E) • z ∈ hat F S := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * a', fun v => mul_mem (ha v) (ha' v), x, hx, ?_⟩
    ext i; simp
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma hat_smul_ring (L : Submodule (𝓞 E) (Fin n → E)) (b : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a', ha', b • x, L.smul_mem b hx, ?_⟩
    ext i; simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def pre (M : Matrix (Fin n) (Fin n) (RA F E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) where
  carrier := {v | M.mulVec (fv F v) ∈ hat F (L : Set (Fin n → E))}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [fv_add, Matrix.mulVec_add]; exact add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [fv_zero, Matrix.mulVec_zero]; exact zero_mem _
  smul_mem' := by
    intro b x hx
    simp only [Set.mem_ofPred_eq] at *
    have : b • x = (b : E) • x := rfl
    rw [this, fv_smul, Matrix.mulVec_smul]
    exact hat_smul_ring L b hx

lemma mem_pre {M : Matrix (Fin n) (Fin n) (RA F E)} {L : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E} :
    v ∈ pre M L ↔ M.mulVec (fv F v) ∈ hat F (L : Set (Fin n → E)) := Iff.rfl

lemma mulVec_mem_hat {M : Matrix (Fin n) (Fin n) (RA F E)} {L : Submodule (𝓞 E) (Fin n → E)}
    {S : Set (Fin n → E)} (hS : S ⊆ pre M L) {z : Fin n → RA F E} (hz : z ∈ hat F S) :
    M.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    rw [gen_eq, Matrix.mulVec_smul]
    exact hat_smul_int ha' (hS hx)
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

lemma exists_bound (M : Matrix (Fin n) (Fin n) (RA F E)) {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (h : ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ hat F (L : Set (Fin n → E))) :
    ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), d • M.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
  classical
  choose f hf0 hf using h
  obtain ⟨s, hs⟩ := hL
  refine ⟨∏ x ∈ s, f (M.mulVec (fv F x)), Finset.prod_pos fun _ _ => hf0 _, fun z hz => ?_⟩
  rw [← Matrix.smul_mulVec]
  refine mulVec_mem_hat ?_ hz
  have : L ≤ pre ((∏ x ∈ s, f (M.mulVec (fv F x))) • M) L := by
    conv_lhs => rw [← hs]
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec (fv F x))) (Finset.mem_coe.1 hx)
    rw [SetLike.mem_coe, mem_pre, Matrix.smul_mulVec, hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) _
  exact this

lemma nsmul_mem_hat {S S' : Set (Fin n → E)} {d : ℕ} (h : ∀ x ∈ S, d • x ∈ S') {z : Fin n → RA F E}
    (hz : z ∈ hat F S) : d • z ∈ hat F S' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    rw [gen_eq, smul_comm, ← fv_nsmul]
    exact hat_smul_int ha' (fv_mem_hat (h x hx))
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma nsmul_cancel {d : ℕ} (hd : 0 < d) {x y : Fin n → RA F E} (h : d • x = d • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd.ne'
  have := congrArg (fun z => (d : F)⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hd'] using this

end GlobalTheory.AdLat.Translate

open GlobalTheory.AdLat.Translate in

theorem GlobalTheory.AdLat.exists_lattice_latOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∃ Λ : Submodule (𝓞 E) (Fin n → E), (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L ∧ Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧ (hat F (Λ : Set (Fin n → E)) : Set (Fin n → RA F E)) = (g : Matrix (Fin n) (Fin n) (RA F E)).mulVec '' (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L g hL hspan
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hspan
  set G : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hG
  set H : Matrix (Fin n) (Fin n) (RA F E) := ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E))
    with hH
  have hGH : ∀ z, G.mulVec (H.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hG, hH, Units.mul_inv, Matrix.one_mulVec]
  have hHG : ∀ z, H.mulVec (G.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hG, hH, Units.inv_mul, Matrix.one_mulVec]
  have him : ∀ z, z ∈ G.mulVec '' (hat F (L : Set (Fin n → E)) : Set (Fin n → RA F E)) ↔
      H.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩; rw [hHG]; exact hu
    · intro h; exact ⟨_, h, hGH z⟩
  obtain ⟨d, hd, hdG⟩ := exists_bound G hL h4
  obtain ⟨e, he, heH⟩ := exists_bound H hL h4
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : E) ≠ 0 := by exact_mod_cast he.ne'
  have hlow : ∀ x ∈ L, e • x ∈ pre H L := by
    intro x hx
    rw [mem_pre, fv_nsmul, Matrix.mulVec_smul]
    exact heH _ (fv_mem_hat hx)
  have hup : ∀ x ∈ pre H L, d • x ∈ L := by
    intro x hx
    rw [← h1, fv_nsmul, ← hGH (fv F x)]
    exact hdG _ hx
  refine ⟨pre H L, ?_, ?_, ?_, ?_⟩
  · ext v
    exact (him _).symm
  · have hinj : Function.Injective (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) := by
      intro x y hxy
      simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
      rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at hxy
      exact smul_right_injective _ hd' hxy
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hle : (pre H L).map (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) ≤ L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hup x hx
    have : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian _ hL
    exact (isNoetherian_submodule.1 this) _ hle
  · rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro x hx
    have hx' : x = (e : E)⁻¹ • (e • x) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ he', one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hlow x hx))
  · ext z
    rw [him]
    constructor
    · intro hz
      exact mulVec_mem_hat subset_rfl hz
    · intro hz
      have hdz : d • z ∈ hat F (L : Set (Fin n → E)) := by
        rw [← hGH z]; exact hdG _ hz
      obtain ⟨x, -, w, hw, hxw⟩ := h2 (d * e) (Nat.mul_pos hd he) _ hdz
      have hx' : x = d • ((d : E)⁻¹ • x) := by
        rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hd', one_smul]
      have hz' : z = fv F ((d : E)⁻¹ • x) + e • w := by
        apply nsmul_cancel hd
        rw [smul_add, ← fv_nsmul, ← hx', smul_smul, hxw]
      have hy : (d : E)⁻¹ • x ∈ pre H L := by
        rw [mem_pre, eq_sub_of_add_eq hz'.symm, Matrix.mulVec_sub, Matrix.mulVec_smul]
        exact sub_mem hz (heH _ hw)
      rw [hz']
      exact add_mem (fv_mem_hat hy) (nsmul_mem_hat hlow hw)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrimeLeNotMemRingKrullDimEqOne
section
namespace GlobalTheory

theorem exists_prime_le_notMem_ringKrullDim_eq_one :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (m : Ideal B) (h : B), m.IsMaximal → h ≠ 0 → h ∈ m →
      ∃ p : Ideal B, p.IsPrime ∧ p ≤ m ∧ h ∉ p ∧ ringKrullDim (B ⧸ p) = 1 := by
  intro k _ _ B _ _ _ _ m h hm h0 hhm
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨q, hq, hqm, h1⟩ := exists_mem_height_map_le_one m
    (PrimeSpectrum.basicOpen h).isOpen ⟨⟨⊥, inferInstance⟩, by simpa using h0, bot_le⟩
  have hq' : h ∉ q.asIdeal := hq
  refine ⟨q.asIdeal, q.isPrime, hqm, hq', ?_⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hmax : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj (by simpa using hqm)
  have h2 : (m.map (Ideal.Quotient.mk q.asIdeal)).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot,
      Set.mem_singleton_iff]
    intro e
    have := Ideal.mem_map_of_mem (Ideal.Quotient.mk q.asIdeal) hhm
    rw [e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hq' this
  have h3 := le_antisymm h1 (Order.one_le_iff_ne_zero.2 h2)
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := B ⧸ q.asIdeal)
  have h4 := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field s hs2
    (m.map (Ideal.Quotient.mk q.asIdeal))
  rw [h3] at h4
  have h5 : s = 1 := by exact_mod_cast h4.symm
  rw [hs1, h5]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelActionOverlapLeSourceChart
section
noncomputable section

namespace GlobalTheory.LevActCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem levelAction_overlap_le_source_chart {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) (x : Sp S ⟶ Xo.X)
    (i j : Xo.univ.t.PP.L.ι) :
    (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U ((fun _ => i), j)) ≤
      (PPx x).U (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hz.2

theorem overlap_le_tgt {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) {x x' : Sp S ⟶ Xo.X}
    (pm : Gx x ⟶ Gx x')
    (hp : pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ φ)
    (i j : Xo.univ.t.PP.L.ι) :
    (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U ((fun _ => i), j)) ≤
      pm ⁻¹ᵁ (PPx x').U (fun _ => i) := by
  intro z hz
  have h1 : ((snd (Over.mk x) Xo.univ.t.G).left ≫ φ).base z ∈ (Xo.univ.t.PP.L.U i : Set _) :=
    Set.mem_iInter.1 hz.1 PUnit.unit
  rw [← hp] at h1
  exact Set.mem_iInter.2 fun _ => h1

end GlobalTheory.LevActCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RatioSqEqDetJAut
section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaRatio

theorem thetaChar_ofRealVec {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ)
    (z : Fin g → ℂ) : thetaChar τ (ofRealVec a) (ofRealVec b) z = theta a b z τ := by
  refine tsum_congr fun l => ?_
  have e : ((fun i => (l i : ℂ)) + ofRealVec a) = shiftVec a l := rfl
  rw [e, thetaTerm, eC]
  congr 1
  ring

theorem exists_eq_halfVec {g : ℕ} {c : Fin g → ℂ} (h : ∀ k, c k = 0 ∨ c k = 1 / 2) :
    ∃ n : Fin g → ℤ, c = ofRealVec (halfVec n) := by
  have : ∀ k, ∃ m : ℤ, c k = (((m : ℝ) / 2 : ℝ) : ℂ) := fun k => by
    rcases h k with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  choose n hn using this
  exact ⟨n, funext hn⟩

theorem ratio_sq_eq_det_jAut : ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 = 1 * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) → ∀ (c₁ c₂ : Fin g → ℂ), (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → ∀ τ ∈ SiegelH (Fin g), ∀ (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ), Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) → ρ 0 = 1 → κ ≠ 0 → (∀ z, thetaChar (spAct γ τ) c₁ c₂ (zAct γ τ z) * ρ z = κ * thetaChar τ c₁ c₂ z) → κ ^ 2 = (jAut γ τ).det := by
  intro g γ hγ h8 h0 c₁ c₂ h₁ h₂ τ hτ ρ κ hρ hρ0 hρ1 hκ h
  obtain ⟨n, rfl⟩ := exists_eq_halfVec h₁
  obtain ⟨n', rfl⟩ := exists_eq_halfVec h₂
  simp only [thetaChar_ofRealVec] at h
  have hfix := halfChar_fixed_of_theta_transform_unit g γ hγ h8 1 n n' one_ne_zero h0 τ hτ
    (fun z => κ / ρ z) (by simpa only [div_eq_mul_inv] using (hρ.fun_inv hρ0).const_mul κ) (fun z => div_ne_zero hκ (hρ0 z))
    (fun z => by rw [div_mul_eq_mul_div, ← h z, mul_div_cancel_right₀ _ (hρ0 z)])
  have hlaw := ThetaCharMult.theta_sq_law_of_zero g γ hγ h8 1 n n' h0 hfix τ hτ
  have hE : Differentiable ℂ fun z => eC (expArg γ τ z) := by
    simp only [eC, expArg, dotProduct, mulVec]
    fun_prop
  have hθ : (fun z => theta (halfVec n) (halfVec n') z τ ^ 2) ≠ 0 := fun hz =>
    theta_ne_zero hτ (halfVec n) (halfVec n')
      (funext fun z => pow_eq_zero_iff (two_ne_zero) |>.1 (congrFun hz z))
  have key := entire_eq_zero_of_mul_continuous_eq_zero
    (f := fun z => (jAut γ τ).det * eC (expArg γ τ z) * ρ z ^ 2 - κ ^ 2)
    (((hE.const_mul _).mul (hρ.pow 2)).sub_const _)
    ((differentiable_theta hτ (halfVec n) (halfVec n')).continuous.pow 2) hθ
    (fun z => by
      have h1 := hlaw z
      have h2 : (theta (halfVec n) (halfVec n') (zAct γ τ z) (spAct γ τ) * ρ z) ^ 2 =
          (κ * theta (halfVec n) (halfVec n') z τ) ^ 2 := by rw [h z]
      show _ * theta (halfVec n) (halfVec n') z τ ^ 2 = 0
      linear_combination h2 - ρ z ^ 2 * h1) 0
  have e0 : eC (expArg γ τ 0) = 1 := by simp [expArg, eC]
  simp only [e0, hρ1] at key
  linear_combination -key

end GlobalTheory.ThetaRatio
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqTransformLevelEight
section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem theta_sq_transform_level_eight :
    ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ),
      γ ∈ Matrix.symplecticGroup (Fin g) ℤ →
      (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) →
      (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ,
        theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 =
          ((ZMod.χ₄ ((γ.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) * (jAut γ τ).det *
            eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) := by
  intro g γ hγ h τ hτ z
  have h48 : (4 : ℤ) ∣ 8 := by norm_num
  exact theta_halfVec_sq_transform hγ (fun i j => h48.trans (h i j).1)
    (fun i j => h48.trans (h i j).2) (k := 0) (k' := 0) (m := 0) (m' := 0)
    (fun i => by rw [mulVec_zero]) (fun i => by rw [mulVec_zero]) hτ z

end GlobalTheory
end

