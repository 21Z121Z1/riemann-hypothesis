import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0048
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseOneAddPreservingAdelicCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCountPlacesNotLocalPowerLeIndex
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AevalSumElimEqZeroOfMemPtsStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_sum_elim_eq_zero_of_mem_pts' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ F : MvPolynomial ((ι × ι) ⊕ (ι × ι)) ℚ, (∀ g ∈ Γ, ∀ h ∈ Γ, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => g ij.1 ij.2) (fun ij : ι × ι => h ij.1 ij.2)) F = (0 : ℂ)) → ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ x ∈ pts Γ R, ∀ y ∈ pts Γ R, MvPolynomial.aeval (Sum.elim (fun ij : ι × ι => x ij.1 ij.2) (fun ij : ι × ι => y ij.1 ij.2)) F = (0 : R) := by
  first | exact @GlobalTheory.ClassFin.aeval_sum_elim_eq_zero_of_mem_pts | exact GlobalTheory.ClassFin.aeval_sum_elim_eq_zero_of_mem_pts | (intros; apply GlobalTheory.ClassFin.aeval_sum_elim_eq_zero_of_mem_pts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnitStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F), p.Prime → v.valuation F (p : F) = 1 → Valued.v x = 1 → Valued.v y = 1 → (∀ r : v.adicCompletion F, r ^ p ≠ x) → ∃ (k : ℕ) (r : v.adicCompletion F), y = x ^ k * r ^ p := by
  first | exact @GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit | exact GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit | (intros; apply GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseOneAddPreservingAdelicCompletionStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inverse_one_add_preserving_adelicCompletion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (N : ℕ) (e : FiniteAdeleRing (𝓞 F) F), (∀ v, e v ∈ v.adicCompletionIntegers F) → (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0) → ∀ X : Matrix (Fin n) (Fin n) (RA F E), (∀ z ∈ hat F (L : Set (Fin n → E)), X *ᵥ z ∈ hat F (L : Set (Fin n → E))) → ∃ W : Matrix (Fin n) (Fin n) (RA F E), (1 + (e ⊗ₜ[F] (1 : E) : RA F E) • (N • X)) * W = 1 ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), W *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat | exact GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat | (intros; apply GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatrices
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.SmallMat

open GlobalTheory.AdLat.Translate

theorem exists_dvd_pow_mul_coprime (N m : ℕ) (hm : m ≠ 0) :
    ∃ t k : ℕ, t.Coprime N ∧ m ∣ N ^ k * t := by
  induction m using induction_on_primes with
  | zero => exact absurd rfl hm
  | one => exact ⟨1, 0, by simp, by simp⟩
  | prime_mul p a hp ih =>
    obtain ⟨t, k, ht, h⟩ := ih (right_ne_zero_of_mul hm)
    by_cases hpN : p ∣ N
    · refine ⟨t, k + 1, ht, ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_dvd_mul hpN h
    · refine ⟨p * t, k, Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN) ht, ?_⟩
      rw [mul_left_comm]
      exact mul_dvd_mul_left p h

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem exists_indicator (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v ∈ S, e v = 1) ∧ ∀ v ∉ S, e v = 0 := by
  classical
  refine ⟨⟨fun v => if v ∈ S then 1 else 0, Filter.Eventually.of_forall fun v => ?_⟩,
    fun v hv => if_pos hv, fun v hv => if_neg hv⟩
  beta_reduce
  split_ifs
  · exact one_mem (v.adicCompletionIntegers F)
  · exact zero_mem (v.adicCompletionIntegers F)

theorem exists_nsmul_integral (b : FiniteAdeleRing (𝓞 F) F) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ v, (m • b) v ∈ v.adicCompletionIntegers F := by
  obtain ⟨x, a, ha, rfl⟩ := exists_eq_algebraMap_add_nsmul F 1 one_pos b
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset F)
  have hc : IsIntegral ℤ (y • x) := hy x (by simp)
  have hc' : IsIntegral ℤ (y.natAbs • x) := by
    rcases Int.natAbs_eq y with h | h
    · have : y.natAbs • x = y • x := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hc
    · have : y.natAbs • x = -(y • x) := by
        conv_rhs => rw [h]
        simp
      rw [this]; exact hc.neg
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, fun v => ?_⟩
  rw [smul_add, ← map_nsmul]
  refine add_mem ?_ (nsmul_mem (nsmul_mem (ha v) 1) _)
  exact v.coe_mem_adicCompletionIntegers (K := F) (⟨y.natAbs • x, hc'⟩ : 𝓞 F)

theorem exists_coprime_nsmul_integral (N : ℕ) (b : FiniteAdeleRing (𝓞 F) F)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → b v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ v, (t • b) v ∈ v.adicCompletionIntegers F := by
  obtain ⟨m, hm, h⟩ := exists_nsmul_integral b
  obtain ⟨t, k, ht, c, hc⟩ := exists_dvd_pow_mul_coprime N m hm
  refine ⟨t, ht, fun v => ?_⟩
  change t • b v ∈ _
  by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
  · rw [hb v hv, smul_zero]; exact zero_mem _
  · have h1 : c • (m • b v) ∈ v.adicCompletionIntegers F := nsmul_mem (h v) c
    rw [smul_smul, mul_comm, ← hc, mul_smul, nsmul_eq_mul,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Nat.cast_pow, map_pow] at h1
    have hN : Valued.v ((N : ℕ) : v.adicCompletion F) = 1 := by
      have h1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr hv
      have h2 := v.valuedAdicCompletion_eq_valuation' (K := F) ((N : ℕ) : F)
      have h3 : (algebraMap F (v.adicCompletion F)) ((N : ℕ) : F) =
        ((N : ℕ) : v.adicCompletion F) := map_natCast _ _
      rw [← h3]
      have h4 : (((N : ℕ) : 𝓞 F) : F) = ((N : ℕ) : F) :=
        map_natCast (algebraMap (𝓞 F) F) _
      exact h2.trans (h4 ▸ h1)
    rw [hN, one_pow, one_mul] at h1
    exact h1

theorem fm_add (A B : Matrix (Fin n) (Fin n) E) : fm F (A + B) = fm F A + fm F B := by
  ext i j
  simp [fm, TensorProduct.tmul_add]

theorem fm_zero : fm F (0 : Matrix (Fin n) (Fin n) E) = 0 := by
  ext i j
  simp [fm]

theorem nsmul_tmul_one (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) :
    ((d • a) ⊗ₜ[F] (1 : E) : RA F E) = d • (a ⊗ₜ[F] (1 : E) : RA F E) := by
  induction d with
  | zero => simp
  | succ d ih => rw [succ_nsmul, succ_nsmul, TensorProduct.add_tmul, ih]

theorem exists_approx (S : Set (Fin n → E))
    (hS : ∀ M : Matrix (Fin n) (Fin n) (RA F E), ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ) (hD : 0 < D) :
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F S, ∃ w ∈ hat F S, (M - fm F M₀) *ᵥ z = D • w := by
  let P : Matrix (Fin n) (Fin n) (RA F E) → Prop := fun M =>
    ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F S, ∃ w ∈ hat F S, (M - fm F M₀) *ᵥ z = D • w
  have hadd : ∀ A B, P A → P B → P (A + B) := by
    rintro A B ⟨A₀, hA⟩ ⟨B₀, hB⟩
    refine ⟨A₀ + B₀, fun z hz => ?_⟩
    obtain ⟨u, hu, hu'⟩ := hA z hz
    obtain ⟨w, hw, hw'⟩ := hB z hz
    refine ⟨u + w, add_mem hu hw, ?_⟩
    rw [smul_add, ← hu', ← hw', ← Matrix.add_mulVec, fm_add, add_sub_add_comm]
  have hzero : P 0 := ⟨0, fun z _ => ⟨0, zero_mem _, by simp [fm_zero]⟩⟩
  have hgen : ∀ (a : FiniteAdeleRing (𝓞 F) F) (B : Matrix (Fin n) (Fin n) E),
      P ((a ⊗ₜ[F] (1 : E) : RA F E) • fm F B) := by
    intro a B
    obtain ⟨d, hd, hB⟩ := hS (fm F B)
    obtain ⟨r, a', ha', rfl⟩ := exists_eq_algebraMap_add_nsmul F (D * d) (Nat.mul_pos hD hd) a
    refine ⟨r • B, fun z hz => ⟨_, hat_smul_int ha' (hB z hz), ?_⟩⟩
    have h1 : fm F (r • B) =
        (algebraMap F (FiniteAdeleRing (𝓞 F) F) r ⊗ₜ[F] (1 : E) : RA F E) • fm F B := by
      ext i j
      simp only [fm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [h1, TensorProduct.add_tmul, add_smul, add_sub_cancel_left, Matrix.smul_mulVec,
      nsmul_tmul_one, smul_assoc, mul_smul, smul_comm d]
  have hsingle : ∀ i j (t : RA F E), P (Matrix.single i j t) := by
    intro i j t
    induction t using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact hzero
    | tmul a y =>
      have := hgen a (Matrix.single i j y)
      convert this using 1
      ext k l
      simp only [fm, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, Matrix.single_apply]
      split_ifs <;> simp
    | add s t hs ht => rw [Matrix.single_add]; exact hadd _ _ hs ht
  change P M
  rw [Matrix.matrix_eq_sum_single M]
  exact Finset.sum_induction _ P hadd hzero fun i _ =>
    Finset.sum_induction _ P hadd hzero fun j _ => hsingle i j _

theorem exists_coprime_small (S : Set (Fin n → E)) (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F)
    (M : Matrix (Fin n) (Fin n) (RA F E)) (hD : 0 < D)
    (hM : ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F S, d • (M *ᵥ z) ∈ hat F S)
    (he : ∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F S, ∃ w ∈ hat F S,
      t • (((e ⊗ₜ[F] (1 : E) : RA F E) • M) *ᵥ z) = D • w := by
  obtain ⟨d, hd, hM⟩ := hM
  have hK : ((D * d : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hD hd).ne'
  set b : FiniteAdeleRing (𝓞 F) F :=
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ((D * d : ℕ) : F)⁻¹ * e with hb
  have hbe : e = (D * d) • b := by
    rw [hb, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
      ← map_mul, mul_inv_cancel₀ hK, map_one, one_mul]
  obtain ⟨t, ht, h⟩ := exists_coprime_nsmul_integral N b fun v hv => by
    change _ * e v = 0
    rw [he v hv, mul_zero]
  refine ⟨t, ht, fun z hz => ⟨_, hat_smul_int h (hM z hz), ?_⟩⟩
  rw [hbe, Matrix.smul_mulVec, nsmul_tmul_one, nsmul_tmul_one, smul_assoc, smul_assoc, mul_smul,
    smul_comm t D, smul_comm d]

end GlobalTheory.UnRep.SmallMat

open GlobalTheory.UnRep.SmallMat GlobalTheory.AdLat.Translate in

theorem GlobalTheory.UnRep.idempotent_adeles_small_matrices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ), ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v ∈ S, e v = 1) ∧ ∀ v ∉ S, e v = 0) ∧ (∀ M : Matrix (Fin n) (Fin n) (RA F E), ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), d • (M *ᵥ z) ∈ hat F (L : Set (Fin n → E))) ∧ (∀ (M : Matrix (Fin n) (Fin n) (RA F E)) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) E, ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), (M - fm F M₀) *ᵥ z = D • w) ∧ (∀ (N D : ℕ) (e : FiniteAdeleRing (𝓞 F) F) (M : Matrix (Fin n) (Fin n) (RA F E)), 0 < D → (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∈ v.asIdeal → e v = 0) → ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), t • (((e ⊗ₜ[F] (1 : E)) • M) *ᵥ z) = D • w) ∧ ∀ (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ z ∈ hat F (L : Set (Fin n → E)), (a ⊗ₜ[F] (1 : E)) • z ∈ hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n L hL hsp
  have h4 := (GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hsp).2.2.2
  have h2 := fun M : Matrix (Fin n) (Fin n) (RA F E) => exists_bound M hL h4
  exact ⟨exists_indicator, h2, exists_approx _ h2,
    fun N D e M hD he => exists_coprime_small _ N D e M hD (h2 M) he,
    fun a ha z hz => hat_smul_int ha hz⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

section
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} in

theorem _root_.GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom (σ : Subrepresentation ρ) (h : IsAtom σ) :
    σ.toRepresentation.IsIrreducible := by
  let F : Subrepresentation σ.toRepresentation → Subrepresentation ρ := fun τ =>
    ⟨τ.toSubmodule.map σ.toSubmodule.subtype, by
      rintro g _ ⟨w, hw, rfl⟩
      exact ⟨σ.toRepresentation g w, τ.apply_mem_toSubmodule g hw, rfl⟩⟩
  have hinj : Function.Injective (Submodule.map σ.toSubmodule.subtype) :=
    Submodule.map_injective_of_injective σ.toSubmodule.injective_subtype
  have hle : ∀ τ, F τ ≤ σ := by
    intro τ
    show τ.toSubmodule.map σ.toSubmodule.subtype ≤ σ.toSubmodule
    rw [Submodule.map_le_iff_le_comap]
    intro w _
    exact w.2
  have hF : ∀ τ, F τ = ⊥ ∨ F τ = σ := fun τ => h.le_iff.mp (hle τ)
  have hbot : ∀ τ, F τ = ⊥ → τ = ⊥ := by
    intro τ hτ
    apply Subrepresentation.ext
    apply hinj
    have := congrArg Subrepresentation.toSubmodule hτ
    change _ = Submodule.map _ ⊥
    rw [Submodule.map_bot]
    exact this
  have htop : ∀ τ, F τ = σ → τ = ⊤ := by
    intro τ hτ
    apply Subrepresentation.ext
    apply hinj
    have := congrArg Subrepresentation.toSubmodule hτ
    simp only [F] at this
    rw [this]
    exact (Submodule.map_subtype_top σ.toSubmodule).symm
  have hne : (⊥ : Subrepresentation σ.toRepresentation) ≠ ⊤ := by
    intro he
    apply h.1
    have h1 : F ⊤ = σ := by
      apply Subrepresentation.ext
      exact Submodule.map_subtype_top σ.toSubmodule
    have h2 : F ⊥ = ⊥ := by
      apply Subrepresentation.ext
      exact Submodule.map_bot _
    rw [← h1, ← he, h2]
  haveI : Nontrivial (Subrepresentation σ.toRepresentation) := ⟨⟨⊥, ⊤, hne⟩⟩
  exact ⟨fun τ => (hF τ).imp (hbot τ) (htop τ)⟩

theorem iSup_atoms_eq_top [FiniteDimensional ℂ V] (h : ρ.IsSemisimpleRepresentation) :
    (⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule) = ⊤ := by
  let S : Subrepresentation ρ :=
    ⟨⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule, by
      intro g v hv
      have : (⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule) ≤
          (⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule).comap (ρ g) :=
        iSup_le fun σ w hw =>
          Submodule.mem_iSup_of_mem σ (σ.1.apply_mem_toSubmodule g hw)
      exact this hv⟩
  haveI : WellFoundedLT (Subrepresentation ρ) :=
    StrictMono.wellFoundedLT (f := Subrepresentation.toSubmodule) (fun _ _ hab => hab)
  haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  obtain ⟨T, hT⟩ := exists_isCompl S
  rcases eq_bot_or_exists_atom_le T with h0 | ⟨a, ha, haT⟩
  · subst h0
    have : S = ⊤ := by simpa using hT.sup_eq_top
    exact congrArg Subrepresentation.toSubmodule this
  · exfalso
    have haS : a ≤ S := fun w hw =>
      Submodule.mem_iSup_of_mem (⟨a, ha⟩ : {σ : Subrepresentation ρ // IsAtom σ}) hw
    exact ha.1 (hT.disjoint haS haT |> le_bot_iff.mp)

end

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private theorem iSup_atoms_toSubmodule_eq_whole_of_semisimple {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hρ : ρ.IsSemisimpleRepresentation) :
    ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule = ⊤ := by
  haveI : ComplementedLattice (Subrepresentation ρ) := hρ
  haveI : WellFoundedLT (Subrepresentation ρ) :=
    StrictMono.wellFoundedLT (f := Subrepresentation.toSubmodule) fun a b hab =>
      lt_of_le_of_ne hab.le fun he => hab.ne (Subrepresentation.toSubmodule_injective he)
  haveI : IsAtomic (Subrepresentation ρ) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  set A := ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule with hA
  let α : Subrepresentation ρ := ⟨A, by
    intro g v hv
    refine Submodule.iSup_induction _ (motive := fun v => ρ g v ∈ A) hv ?_ ?_ ?_
    · intro σ w hw
      exact (le_iSup (fun σ : {σ : Subrepresentation ρ // IsAtom σ} => σ.1.toSubmodule) σ)
        (σ.1.apply_mem_toSubmodule g hw)
    · simp
    · intro x y hx hy
      simpa using A.add_mem hx hy⟩
  obtain ⟨β, hβ⟩ := exists_isCompl α
  have hβbot : β = ⊥ := by
    rcases eq_bot_or_exists_atom_le β with h | ⟨τ, hτ, hτβ⟩
    · exact h
    · exfalso
      have hτα : τ ≤ α := fun v hv =>
        (le_iSup (fun σ : {σ : Subrepresentation ρ // IsAtom σ} => σ.1.toSubmodule) ⟨τ, hτ⟩) hv
      exact hτ.1 (le_bot_iff.mp (hβ.1 hτα hτβ))
  have hαtop : α = ⊤ := by
    have := hβ.2.eq_top
    rwa [hβbot, sup_bot_eq] at this
  exact congrArg Subrepresentation.toSubmodule hαtop

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsSemisimpleRepresentation → ρ'.IsSemisimpleRepresentation → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  intro G _ V _ _ ρ W _ _ ρ' _ _ hρ hρ'
  let J := {σ : Subrepresentation ρ // IsAtom σ} × {τ : Subrepresentation ρ' // IsAtom τ}
  let p : (j : J) → j.1.1.toSubmodule ⊗[ℂ] j.2.1.toSubmodule →ₗ[ℂ] V ⊗[ℂ] W := fun j =>
    TensorProduct.map j.1.1.toSubmodule.subtype j.2.1.toSubmodule.subtype
  refine _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range G (V ⊗[ℂ] W) (ρ.tprod ρ') J
    (fun j => j.1.1.toSubmodule ⊗[ℂ] j.2.1.toSubmodule)
    (fun j => j.1.1.toRepresentation.tprod j.2.1.toRepresentation) p ?_ ?_ ?_
  · intro j
    exact _root_.GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod_of_isIrreducible G _ _ _ _
      (_root_.GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom j.1.1 j.1.2)
      (_root_.GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom j.2.1 j.2.2)
  · intro j g v
    simp only [p]
    rw [Representation.tprod_apply, Representation.tprod_apply, ← LinearMap.comp_apply,
      ← LinearMap.comp_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
    rfl
  · rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨v, w, rfl⟩
    have hv : v ∈ ⨆ σ : {σ : Subrepresentation ρ // IsAtom σ}, σ.1.toSubmodule := by
      rw [iSup_atoms_toSubmodule_eq_whole_of_semisimple ρ hρ]; trivial
    have hw : w ∈ ⨆ τ : {τ : Subrepresentation ρ' // IsAtom τ}, τ.1.toSubmodule := by
      rw [iSup_atoms_toSubmodule_eq_whole_of_semisimple ρ' hρ']; trivial
    refine Submodule.iSup_induction _ (motive := fun v => ∀ w,
      w ∈ ⨆ τ : {τ : Subrepresentation ρ' // IsAtom τ}, τ.1.toSubmodule →
        v ⊗ₜ[ℂ] w ∈ ⨆ j, LinearMap.range (p j)) hv ?_ ?_ ?_ w hw
    · intro σ x hx w hw
      refine Submodule.iSup_induction _
        (motive := fun w => x ⊗ₜ[ℂ] w ∈ ⨆ j, LinearMap.range (p j)) hw ?_ ?_ ?_
      · intro τ y hy
        exact (le_iSup (fun j => LinearMap.range (p j)) (σ, τ))
          ⟨(⟨x, hx⟩ : σ.1.toSubmodule) ⊗ₜ[ℂ] (⟨y, hy⟩ : τ.1.toSubmodule), rfl⟩
      · simp
      · intro a b ha hb
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ha hb
    · intro w _
      simp
    · intro a b ha hb w hw
      rw [TensorProduct.add_tmul]
      exact Submodule.add_mem _ (ha w hw) (hb w hw)

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCountPlacesNotLocalPowerLeIndexStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_countPlacesNotLocalPower_le_index : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → (finNorm p F δ S).index ≠ 0 ∧ p ^ tNon p F δ S ≤ (finNorm p F δ S).index := by
  first | exact @GlobalTheory.CNorm.pow_tNon_le_index_finNorm | exact GlobalTheory.CNorm.pow_tNon_le_index_finNorm | (intros; apply GlobalTheory.CNorm.pow_tNon_le_index_finNorm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTopStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → sUnits F S ⊔ locNorm F δ S ≠ ⊤ := by
  first | exact @GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top | exact GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top | (intros; apply GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsUnionSupLocalSquaresEqTop
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem sUnits_union_sup_finSq_eq_top :
    ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → Disjoint S T → (∀ A : Finset (HeightOneSpectrum (𝓞 F)), ∃ u ∈ sUnits F S, ∀ v ∈ T, (IsSquare (algebraMap F (v.adicCompletion F) (u : F)) ↔ v ∉ A)) → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ := by
  intro F _ _ _ S T hS hST hA
  classical
  have hval : ∀ (v : HeightOneSpectrum (𝓞 F)) (z : F),
      Valued.v (algebraMap F (v.adicCompletion F) z) = v.valuation F z :=
    fun v z => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z
  have hTS : ∀ v ∈ T, v ∉ S := fun v hv h => Finset.disjoint_left.1 hST h hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S T
    (fun v => if v ∈ T then -WithZero.log (v.valuation F (x : F)) else 0) hS
    (fun v hv => by simp [hv])
  have haU : a ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits]
    intro v hv
    rw [Finset.mem_union, not_or] at hv
    rw [ha v hv.1]
    simp [hv.2]
  have hy : ∀ v ∈ T, v.valuation F ((a * x : Fˣ) : F) = 1 := by
    intro v hv
    have hx0 : v.valuation F (x : F) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, ha v (hTS v hv), if_pos hv, WithZero.exp_neg,
      WithZero.exp_log hx0, inv_mul_cancel₀ hx0]
  obtain ⟨u, hu, huA⟩ := hA (T.filter fun v =>
    ¬ IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F)))
  have huU : u ∈ sUnits F (S ∪ T) := by
    rw [mem_sUnits] at hu ⊢
    intro v hv
    exact hu v fun h => hv (Finset.mem_union_left _ h)
  have hsq : u * (a * x) ∈ finSq F T := by
    simp only [finSq, Subgroup.mem_iInf]
    intro v hv
    rw [mem_sqSub, Units.val_mul, map_mul]
    have h := huA v hv
    rw [Finset.mem_filter] at h
    by_cases hs : IsSquare (algebraMap F (v.adicCompletion F) ((a * x : Fˣ) : F))
    · exact (h.2 fun hh => hh.2 hs).mul hs
    · refine isSquare_mul_of_nonsquare_units F v ?_ _ _ ?_ ?_ (fun hh => h.1 hh ⟨hv, hs⟩) hs
      · rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2, hval]
        exact (hS v (hTS v hv)).1
      · rw [hval]
        exact (mem_sUnits F S u).1 hu v (hTS v hv)
      · rw [hval]
        exact hy v hv
  have hx : x = (u * a)⁻¹ * (u * (a * x)) := by group
  rw [hx]
  exact Subgroup.mul_mem_sup (inv_mem (mul_mem huU haU)) hsq

end GlobalTheory.QNorm
end

