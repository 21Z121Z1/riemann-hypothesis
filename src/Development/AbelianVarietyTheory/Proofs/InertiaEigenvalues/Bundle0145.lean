import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0130
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Formalism.GaloisCohomology.Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0135
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0136
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0137
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianTraceDualIntegersEqUniformizerPow
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DualLattice

variable {R : Type} [CommRing R]

theorem eq_zpow_mul_unit (O : Subring R) (p : Rˣ)
    (hdich : ∀ y ∈ O, (∃ z ∈ O, y = (p : R) * z) ∨ ∃ z ∈ O, y * z = 1)
    (hsep : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∀ z ∈ O, (p : R) ^ n * z ≠ x)
    (hex : ∀ y : R, ∃ n : ℕ, (p : R) ^ n * y ∈ O) :
    ∀ y : R, y ≠ 0 → ∃ v : ℤ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ y = ((p ^ v : Rˣ) : R) * u := by
  classical
  have hO : ∀ x ∈ O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ x = (p : R) ^ k * u := by
    intro x hxO hx0
    have hex' : ∃ k : ℕ, ¬ ∃ z ∈ O, x = (p : R) ^ k * z := by
      obtain ⟨n, hn⟩ := hsep x hx0
      exact ⟨n, fun ⟨z, hz, hzx⟩ => hn z hz hzx.symm⟩
    obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, (¬ ∃ z ∈ O, x = (p : R) ^ m * z) ∧
        ∀ j < m, ∃ z ∈ O, x = (p : R) ^ j * z :=
      ⟨Nat.find hex', Nat.find_spec hex', fun j hj => by simpa using Nat.find_min hex' hj⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hm ⟨x, hxO, by simp⟩
    obtain ⟨z, hz, hxz⟩ := hmin (m - 1) (by omega)
    rcases hdich z hz with ⟨w, hw, hzw⟩ | hu
    · exfalso
      apply hm
      refine ⟨w, hw, ?_⟩
      rw [hxz, hzw, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
    · exact ⟨_, z, hz, hu, hxz⟩
  intro y hy
  obtain ⟨n, hn⟩ := hex y
  have hne : (p : R) ^ n * y ≠ 0 := by
    intro h
    apply hy
    have := congrArg (fun t => ((p⁻¹ : Rˣ) : R) ^ n * t) h
    simpa [← mul_assoc, ← mul_pow] using this
  obtain ⟨k, u, hu, hunit, hk⟩ := hO _ hn hne
  refine ⟨(k : ℤ) - n, u, hu, hunit, ?_⟩
  have e1 : ((p ^ ((k : ℤ) - n) : Rˣ) : R) = ((p⁻¹ : Rˣ) : R) ^ n * (p : R) ^ k := by
    rw [_root_.zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, mul_comm]
  rw [e1, mul_assoc, ← hk, ← mul_assoc, ← mul_pow]
  simp

theorem eq_zpow_smul (O : Subring R) (p : Rˣ) (D : Set R) (hpO : (p : R) ∈ O)
    (hmul : ∀ y ∈ D, ∀ r ∈ O, r * y ∈ D)
    (hbig : ∃ n : ℕ, ∀ z ∈ O, (p : R) ^ n * z ∈ D)
    (hne : ∃ y, y ∉ D)
    (hex : ∀ y : R, ∃ n : ℕ, (p : R) ^ n * y ∈ O)
    (hunit : ∀ y : R, y ≠ 0 → ∃ v : ℤ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ y = ((p ^ v : Rˣ) : R) * u) :
    ∃ e : ℤ, D = {y | ∃ z ∈ O, y = ((p ^ e : Rˣ) : R) * z} := by
  classical
  have hup : ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D → ∀ k : ℕ, ((p ^ (v + k) : Rˣ) : R) ∈ D := by
    intro v hv k
    have : ((p ^ (v + k) : Rˣ) : R) = (p : R) ^ k * ((p ^ v : Rˣ) : R) := by
      rw [_root_.zpow_add, zpow_natCast, mul_comm, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [this]
    exact hmul _ hv _ (pow_mem hpO k)
  obtain ⟨n, hn⟩ := hbig
  have hinh : ∃ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D := ⟨n, by simpa using hn 1 (one_mem O)⟩
  have hbdd : ∃ b : ℤ, ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D → b ≤ v := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D := by
      intro v
      obtain ⟨w, hw, hwv⟩ := hcon v
      have := hup w hw (v - w).toNat
      rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this
    obtain ⟨y, hy⟩ := hne
    obtain ⟨m, hm⟩ := hex y
    apply hy
    have h1 := hmul _ (hall (-(m : ℤ))) _ hm
    have hq : ((p ^ (-(m : ℤ)) : Rˣ) : R) * (p : R) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add,
        neg_add_cancel, zpow_zero, Units.val_one]
    have h2 : (p : R) ^ m * y * ((p ^ (-(m : ℤ)) : Rˣ) : R) = y := by
      linear_combination y * hq
    rwa [h2] at h1
  obtain ⟨e, he, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨e, Set.ext fun y => ⟨fun hy => ?_, fun ⟨z, hz, hyz⟩ => ?_⟩⟩
  · by_cases hy0 : y = 0
    · exact ⟨0, zero_mem O, by simp [hy0]⟩
    obtain ⟨v, u, hu, ⟨w, hw, huw⟩, hyv⟩ := hunit y hy0
    have hv : ((p ^ v : Rˣ) : R) ∈ D := by
      have := hmul y hy w hw
      have e2 : w * y = ((p ^ v : Rˣ) : R) := by rw [hyv, mul_comm, mul_assoc, huw, mul_one]
      rwa [e2] at this
    have hev := hmin v hv
    refine ⟨(p : R) ^ (v - e).toNat * u, O.mul_mem (pow_mem hpO _) hu, ?_⟩
    rw [hyv, ← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add,
      Int.toNat_of_nonneg (by omega), add_sub_cancel]
  · rw [hyz, mul_comm]
    exact hmul _ he _ hz

end GlobalTheory.JR.DualLattice

namespace GlobalTheory.JR.DualLattice

set_option maxHeartbeats 1000000 in

theorem dual_eq_zpow : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → IsField A.L → ∀ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) → (∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O) → ∀ a : A.Kˣ, ∃ e : ℤ, {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} = {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((ϖ ^ e : A.Kˣ) : A.K) * z} := by
  intro F E _ _ _ _ U A ψ hψ hK hL ϖ O hOo hOc hOstar hpO hpnu hdich hnbhd hex a
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hLnt : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  have hKnt : Nontrivial A.K := ⟨hK.exists_pair_ne⟩
  let p : A.Lˣ := Units.map (algebraMap A.K A.L).toMonoidHom ϖ
  have hp : (p : A.L) = algebraMap A.K A.L (ϖ : A.K) := rfl
  have hpz : ∀ v : ℤ, ((p ^ v : A.Lˣ) : A.L) = algebraMap A.K A.L ((ϖ ^ v : A.Kˣ) : A.K) := by
    intro v
    rw [show p ^ v = Units.map (algebraMap A.K A.L).toMonoidHom (ϖ ^ v) from (map_zpow _ ϖ v).symm]
    rfl
  have hpn : ∀ n : ℕ, (p : A.L) ^ n = algebraMap A.K A.L ((ϖ : A.K) ^ n) := by
    intro n; rw [hp, map_pow]

  have hmul : ∀ y ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1}, ∀ r ∈ O,
      r * y ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    intro y hy r hr m hm
    have e1 : star (r * y) * m = star y * (star r * m) := by rw [star_mul']; ring
    simp only [Et.kerL, Set.mem_setOf_eq] at hy ⊢
    rw [e1]
    exact hy _ (O.mul_mem (hOstar r hr) hm)

  have hψl : IsLocallyConstant (fun x => ψ x) := ((GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).1
  have hg : Continuous (fun q : A.L × A.L =>
      Algebra.trace F A.K ((a : A.K) * Algebra.trace A.K A.L (star q.1 * q.2))) := by
    have hs : Continuous (star : A.L → A.L) := IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)
    have ht : Continuous (Algebra.trace A.K A.L) :=
      IsModuleTopology.continuous_of_linearMap ((Algebra.trace A.K A.L).restrictScalars F)
    have htF : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact htF.comp (continuous_const.mul (ht.comp ((hs.comp continuous_fst).mul continuous_snd)))
  have hW : IsOpen {q : A.L × A.L | A.kerL ψ (a : A.K) q.1 q.2 = 1} :=
    (hψl.isOpen_fiber 1).preimage hg
  obtain ⟨u, v, hu, -, h0u, hOv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : A.L))) hOc hW
    (by
      rintro ⟨y, m⟩ ⟨hy, -⟩
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      simp [Et.kerL, Et.psiK])
  obtain ⟨n, hn⟩ := hnbhd u (hu.mem_nhds (h0u rfl))
  have hbig : ∃ n : ℕ, ∀ z ∈ O, (p : A.L) ^ n * z ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    refine ⟨n, fun z hz m hm => ?_⟩
    have : ((p : A.L) ^ n * z, m) ∈ u ×ˢ v := ⟨by rw [hpn]; exact hn z hz, hOv hm⟩
    exact huv this

  have hinj : ∀ k₁ k₂ : A.K, algebraMap A.K A.L k₁ = algebraMap A.K A.L k₂ → k₁ = k₂ := by
    intro k₁ k₂ h
    by_contra hne
    obtain ⟨k', hk'⟩ := hK.mul_inv_cancel (sub_ne_zero.2 hne)
    have : algebraMap A.K A.L ((k₁ - k₂) * k') = 0 := by rw [map_mul, map_sub, h, sub_self, zero_mul]
    rw [hk', map_one] at this
    exact one_ne_zero this
  have hne : ∃ y, y ∉ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    obtain ⟨-, x, hx, -⟩ := hψ
    have hd : (Module.finrank F A.K : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    set t : F := x / (2 * (Module.finrank F A.K : F)) with ht
    set c : A.K := ((a⁻¹ : A.Kˣ) : A.K) * algebraMap F A.K t with hc
    refine ⟨algebraMap A.K A.L c, fun h => hx ?_⟩
    have h1 := h 1 (one_mem O)
    have htr : Algebra.trace A.K A.L (star (algebraMap A.K A.L c) * 1) = 2 * c := by
      apply hinj
      rw [mul_one, A.star_K, (GlobalTheory.JR.EtFacts.main F E A).2.1, A.star_K, two_mul, map_add]
    have hac : (a : A.K) * (2 * c) = algebraMap F A.K (2 * t) := by
      rw [hc, map_mul, map_ofNat, ← mul_assoc, mul_comm (a : A.K) 2, mul_assoc 2, ← mul_assoc (a : A.K),
        Units.mul_inv, one_mul]
    simp only [Et.kerL, Et.psiK, htr, hac, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
    rw [← h1, ht]
    congr 1
    field_simp

  have hsep : ∀ x : A.L, x ≠ 0 → ∃ n : ℕ, ∀ z ∈ O, (p : A.L) ^ n * z ≠ x := by
    intro x hx
    obtain ⟨n, hn⟩ := hnbhd {x}ᶜ (isOpen_compl_singleton.mem_nhds (Ne.symm hx))
    exact ⟨n, fun z hz => by rw [hpn]; exact hn z hz⟩
  have hex' : ∀ y : A.L, ∃ n : ℕ, (p : A.L) ^ n * y ∈ O := by
    intro y
    obtain ⟨n, hn⟩ := hex y
    exact ⟨n, by rw [hpn]; exact hn⟩
  have hdich' : ∀ y ∈ O, (∃ z ∈ O, y = (p : A.L) * z) ∨ ∃ z ∈ O, y * z = 1 := by
    rw [hp]; exact hdich
  have hunit := eq_zpow_mul_unit O p hdich' hsep hex'
  obtain ⟨e, he⟩ := eq_zpow_smul O p _ (by rw [hp]; exact hpO) hmul hbig hne hex' hunit
  refine ⟨e, ?_⟩
  rw [he]
  simp only [hpz]

end GlobalTheory.JR.DualLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralUnitaryGroupTransitiveNormOneVectors
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.UnitaryTransitive

variable {E : Type} [NormedField E] [StarRing E]

theorem nsub [IsUltrametricDist E] (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]; simpa using IsUltrametricDist.norm_add_le_max a (-b)

def ext0 {r : ℕ} (x : Fin r → E) : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) x 0

@[simp] theorem snocZeroLastCoordinate_castSucc {r : ℕ} (x : Fin r → E) (j : Fin r) : ext0 x j.castSucc = x j := by
  simp [ext0]
@[simp] theorem snocZeroLastCoordinate_last {r : ℕ} (x : Fin r → E) : ext0 x (Fin.last r) = 0 := by
  simp [ext0]

theorem star_snocZeroLastCoordinate_dotProduct {r : ℕ} (x : Fin r → E) (f : Fin (r + 1) → E) :
    star (ext0 x) ⬝ᵥ f = star x ⬝ᵥ (fun j => f j.castSucc) := by
  simp [dotProduct, Fin.sum_univ_castSucc]

theorem dotProduct_snocZeroLastCoordinate {r : ℕ} (x : Fin r → E) (f : Fin (r + 1) → E) :
    f ⬝ᵥ ext0 x = (fun j => f j.castSucc) ⬝ᵥ x := by
  simp [dotProduct, Fin.sum_univ_castSucc]

end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive
variable {E : Type} [Field E] [StarRing E]
theorem rank_one_entry {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (a b : Fin r → E) (m m' : Fin r) :
    (gᴴ * (replicateCol Unit a * replicateRow Unit b) * g) m m' = (gᴴ *ᵥ a) m * (b ᵥ* g) m' := by
  have e : gᴴ * (replicateCol Unit a * replicateRow Unit b) * g =
      replicateCol Unit (gᴴ *ᵥ a) * replicateRow Unit (b ᵥ* g) := by
    rw [Matrix.replicateCol_mulVec, Matrix.replicateRow_vecMul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e]; simp [Matrix.mul_apply]

theorem star_dot_col {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (w : Fin r → E) (m : Fin r) :
    star (star w ⬝ᵥ (fun j => g j m)) = (gᴴ *ᵥ w) m := by
  simp [dotProduct, Matrix.mulVec, star_sum, mul_comm]

theorem dot_col {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (b : Fin r → E) (m : Fin r) :
    b ⬝ᵥ (fun j => g j m) = (b ᵥ* g) m := by
  simp [dotProduct, Matrix.vecMul]
end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive

theorem uO_transitive_of_last_unit (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E) (hv : ∀ i, ‖v i‖ ≤ 1) (h1 : star v ⬝ᵥ v = 1)
    (hn : ‖v (Fin.last r)‖ = 1) : ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  haveI := Unram.ultraE (F := F) (E := E)
  have hst : ∀ x : E, ‖star x‖ = ‖x‖ := Unram.norm_star (F := F)
  set w : Fin r → E := fun j => v j.castSucc with hw
  set G : Matrix (Fin r) (Fin r) E := 1 + replicateCol Unit (-w) * replicateRow Unit (star w) with hG
  have hGe : ∀ i j, G i j = (1 : Matrix (Fin r) (Fin r) E) i j - w i * star (w j) := by
    intro i j; simp [G, Matrix.mul_apply, sub_eq_add_neg]
  have hGh : G.IsHermitian := by
    apply Matrix.IsHermitian.ext; intro i j; rw [hGe, hGe]
    by_cases h : i = j
    · subst h; simp [mul_comm]
    · simp [Matrix.one_apply, h, Ne.symm h, mul_comm]
  have hGi : ∀ i j, ‖G i j‖ ≤ 1 := by
    intro i j; rw [hGe]; refine (nsub _ _).trans (max_le ?_ ?_)
    · by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · rw [norm_mul, hst]; exact mul_le_one₀ (hv _) (norm_nonneg _) (hv _)
  have hsplit : star v ⬝ᵥ v = star w ⬝ᵥ w + star (v (Fin.last r)) * v (Fin.last r) := by
    simp [dotProduct, Fin.sum_univ_castSucc, w]
  have hGd : ‖G.det‖ = 1 := by
    rw [hG, det_one_add_replicateCol_mul_replicateRow, dotProduct_neg]
    have : 1 + -(star w ⬝ᵥ w) = star (v (Fin.last r)) * v (Fin.last r) := by
      linear_combination h1.symm + hsplit
    rw [this, norm_mul, hst, hn]; norm_num
  obtain ⟨g, hgi, -, hg⟩ := GlobalTheory.T.unimodular_hermitian_matrix_congruent_one F E r G hGh hGi hGd
  set c : Fin r → E := fun m => star w ⬝ᵥ (fun j => g j m) with hc
  have hg' : ∀ m m', star (fun j => g j m) ⬝ᵥ (fun j => g j m') - star (c m) * c m' = (1 : Matrix (Fin r) (Fin r) E) m m' := by
    intro m m'
    have := congrFun (congrFun hg m) m'
    rw [← this, hG, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.add_apply, rank_one_entry,
      hc, star_dot_col, dot_col, Matrix.mulVec_neg]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, sub_eq_add_neg]
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun i l =>
    Fin.lastCases (motive := fun _ => E) (v i) (fun m => ext0 (fun j => g j m) i - c m * v i) l
  have cl : (fun i => K i (Fin.last r)) = v := by funext i; simp [K]
  have cs : ∀ m, (fun i => K i m.castSucc) = ext0 (fun j => g j m) - c m • v := by
    intro m; funext i; simp [K]
  have key : ∀ a b, (star K * K) a b = star (fun i => K i a) ⬝ᵥ (fun i => K i b) := by
    intro a b; rfl
  have d2 : ∀ m, star v ⬝ᵥ ext0 (fun j => g j m) = c m := by
    intro m; rw [dotProduct_snocZeroLastCoordinate]; rfl
  have d3 : ∀ m, star (ext0 (fun j => g j m)) ⬝ᵥ v = star (c m) := by
    intro m; rw [star_snocZeroLastCoordinate_dotProduct, hc, star_dot_col]; rfl
  have d4 : ∀ m m', star (ext0 (fun j => g j m)) ⬝ᵥ ext0 (fun j => g j m') =
      star (fun j => g j m) ⬝ᵥ (fun j => g j m') := by
    intro m m'; rw [star_snocZeroLastCoordinate_dotProduct]; simp
  have hU : star K * K = 1 := by
    ext a b
    rw [key]
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rw [cl, h1]; simp
      | cast m' =>
        rw [cl, cs, dotProduct_sub, dotProduct_smul, d2, h1, smul_eq_mul, mul_one, sub_self,
          Matrix.one_apply_ne (Fin.castSucc_ne_last m').symm]
    | cast m =>
      induction b using Fin.lastCases with
      | last =>
        rw [cl, cs, star_sub, star_smul, sub_dotProduct, smul_dotProduct, d3, h1]
        simp [Matrix.one_apply, (Fin.castSucc_ne_last m)]
      | cast m' =>
        rw [cs, cs, star_sub, star_smul, sub_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_sub,
          dotProduct_smul, dotProduct_smul, d2, d3, d4, h1]
        have e1 : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) m.castSucc m'.castSucc =
            (1 : Matrix (Fin r) (Fin r) E) m m' := by
          simp [Matrix.one_apply, Fin.castSucc_inj]
        rw [e1, ← hg' m m']
        simp only [smul_eq_mul]
        ring
  refine ⟨⟨K, Matrix.mem_unitaryGroup_iff'.2 hU⟩, ?_, ?_⟩
  · intro i l
    show ‖K i l‖ ≤ 1
    induction l using Fin.lastCases with
    | last => simpa [K] using hv i
    | cast m =>
      simp only [K, Matrix.of_apply, Fin.lastCases_castSucc]
      have hcm : ‖c m‖ ≤ 1 := by
        rw [hc]
        exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun j _ => by
          rw [norm_mul, Pi.star_apply, hst]; exact mul_le_one₀ (hv _) (norm_nonneg _) (hgi _ _))
      refine (nsub _ _).trans (max_le ?_ ?_)
      · induction i using Fin.lastCases with
        | last => simp
        | cast j => simpa using hgi j m
      · rw [norm_mul]; exact mul_le_one₀ hcm (norm_nonneg _) (hv _)
  · show K *ᵥ Pi.single (Fin.last r) 1 = v
    rw [Matrix.mulVec_single_one]; exact cl

end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive

theorem uO_transitive : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 →
    ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  intro F E _ _ _ _ _ r v hv h1
  haveI := Unram.ultraE (F := F) (E := E)
  have hst : ∀ x : E, ‖star x‖ = ‖x‖ := Unram.norm_star (F := F)
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le (Finset.univ : Finset (Fin (r + 1)))
    (fun i => star (v i) * v i)
  have hs : (∑ j, star (v j) * v j) = 1 := h1
  rw [hs, norm_one, norm_mul, hst] at hi
  have hvi : ‖v i‖ = 1 := by nlinarith [hv i, norm_nonneg (v i)]
  set σ : Equiv.Perm (Fin (r + 1)) := Equiv.swap i (Fin.last r) with hσ
  have hσσ : ∀ j, σ (σ j) = j := fun j => Equiv.swap_apply_self _ _ _
  have h1' : star (v ∘ σ) ⬝ᵥ (v ∘ σ) = 1 := by
    rw [← hs]; exact Equiv.sum_comp σ (fun j => star (v j) * v j)
  have hn' : ‖(v ∘ σ) (Fin.last r)‖ = 1 := by simp [hσ, hvi]
  obtain ⟨k, hk, hkv⟩ := uO_transitive_of_last_unit F E r (v ∘ σ) (fun j => hv _) h1' hn'
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) E := k.1.submatrix σ id
  have hU : star K * K = 1 := by
    have hk1 : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
    ext a b
    rw [← hk1]
    simp only [K, Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, id]
    exact Equiv.sum_comp σ (fun j => star (k.1 j a) * k.1 j b)
  refine ⟨⟨K, Matrix.mem_unitaryGroup_iff'.2 hU⟩, fun a b => hk (σ a) b, ?_⟩
  show K *ᵥ Pi.single (Fin.last r) 1 = v
  funext j
  have := congrFun hkv (σ j)
  rw [Matrix.mulVec_single_one] at this ⊢
  simpa [K, hσσ] using this

end GlobalTheory.UnitaryTransitive
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvCupPairingOfInvCupCharacters
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory

private lemma pairing_smul_left' {p : ℕ} [NeZero p] {M M' : Type} [AddCommGroup M] [AddCommGroup M']
    [Module (ZMod p) M] (β : M →+ M' →+ ZMod p) (a : ZMod p) (v : M) (m' : M') :
    β (a • v) m' = a * β v m' := by
  have h : a • v = a.val • v := by
    conv_lhs => rw [← ZMod.natCast_zmod_val a]
    exact Nat.cast_smul_eq_nsmul (ZMod p) a.val v
  rw [h, map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]

theorem exists_sum_mul_of_finite_torsion (l : ℕ) [Fact l.Prime] (M M' : Type) [AddCommGroup M]
    [AddCommGroup M'] [Module (ZMod l) M] (β : M →+ M' →+ ZMod l) (S : Set M)
    (hS : S.Finite) :
    ∃ (ι : Type) (s : Finset ι) (c : ι → M →+ ZMod l) (d : ι → M' →+ ZMod l),
      ∀ m ∈ S, ∀ m' : M', β m m' = ∑ k ∈ s, c k m * d k m' := by
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  let b := Module.Basis.ofVectorSpace (ZMod l) M
  refine ⟨_, hS.toFinset.biUnion (fun m => (b.repr m).support),
    fun i => (b.coord i).toAddMonoidHom, fun i => β (b i), ?_⟩
  intro m hm m'
  have hsub : (b.repr m).support ⊆ hS.toFinset.biUnion (fun m => (b.repr m).support) :=
    Finset.subset_biUnion_of_mem (fun m => (b.repr m).support) (hS.mem_toFinset.2 hm)
  have hm' : m = ∑ i ∈ (b.repr m).support, b.repr m i • b i := by
    conv_lhs => rw [← b.linearCombination_repr m]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  conv_lhs => rw [hm']
  rw [map_sum, AddMonoidHom.finset_sum_apply]
  simp only [pairing_smul_left', LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply]
  refine Finset.sum_subset hsub ?_
  intro k _ hk
  have hz : b.repr m k = 0 := by
    by_contra h
    exact hk (Finsupp.mem_support_iff.2 h)
  rw [hz, zero_mul]

theorem inv_cup_pairing_of_inv_cup_characters : ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (l : ℕ) [Fact l.Prime] (μ : Representation (ZMod (l ^ 1)) Γ (ZMod (l ^ 1))), (∀ g m, μ g m = m) → ∀ (e : H2 μ →ₗ[ZMod (l ^ 1)] ZMod (l ^ 1)) (I : Γ → Prop) (u : ZMod (l ^ 1)) (γ φ : Γ), (∀ z y : Γ → ZMod (l ^ 1), Continuous z → Continuous y → (∀ g h, z (g * h) = z g + z h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = z g * y h) → e (Submodule.Quotient.mk w) = u * (z γ * y φ)) → ∀ (M M' : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M'], (∀ m : M, l • m = 0) → ∀ (β : M →+ M' →+ ZMod (l ^ 1)) (x : Γ → M) (y : Γ → M'), Continuous x → Continuous y → (∀ g h, x (g * h) = x g + x h) → (∀ g h, y (g * h) = y g + y h) → (∀ g, I g → y g = 0) → ∀ w : Z2 μ, (∀ g h, w.1 (g, h) = β (x g) (y h)) → e (Submodule.Quotient.mk w) = u * β (x γ) (y φ) := by
  intro Γ _ _ _ _ l _ μ hμ e I u γ φ hchar M M' _ _ _ _ _ _ hl β x y hxc hyc hxa hya hyI w hw
  classical
  haveI hp : Fact (l ^ 1).Prime := ⟨by rw [pow_one]; exact Fact.out⟩
  haveI : NeZero (l ^ 1) := ⟨hp.out.ne_zero⟩
  letI : Module (ZMod (l ^ 1)) M :=
    AddCommGroup.zmodModule (fun m => by rw [pow_one]; exact hl m)
  have hfin : (Set.range x).Finite := (isCompact_range hxc).finite_of_discrete
  obtain ⟨ι, s, c, d, hdec⟩ :=
    exists_sum_mul_of_finite_torsion (l ^ 1) M M' β (Set.range x) hfin
  have hmem : ∀ k, (fun q : Γ × Γ => c k (x q.1) * d k (y q.2)) ∈ Z2 μ := by
    intro k
    rw [mem_cocycles2]
    refine ⟨?_, ?_⟩
    · exact ((continuous_of_discreteTopology.comp hxc).comp continuous_fst).mul
        ((continuous_of_discreteTopology.comp hyc).comp continuous_snd)
    · intro g h k'
      simp only [hμ, hxa, hya, map_add]
      ring
  let W : ι → Z2 μ := fun k => ⟨_, hmem k⟩
  have hWsum : w = ∑ k ∈ s, W k := by
    apply Subtype.ext
    funext q
    rcases q with ⟨g, h⟩
    rw [Submodule.coe_sum, Finset.sum_apply, hw g h]
    exact hdec (x g) ⟨g, rfl⟩ (y h)
  have hW : ∀ k, e (Submodule.Quotient.mk (W k)) = u * (c k (x γ) * d k (y φ)) := fun k =>
    hchar (fun g => c k (x g)) (fun g => d k (y g))
      (continuous_of_discreteTopology.comp hxc) (continuous_of_discreteTopology.comp hyc)
      (fun g h => by simp only [hxa, map_add]) (fun g h => by simp only [hya, map_add])
      (fun g hg => by simp only [hyI g hg, map_zero]) (W k) (fun g h => rfl)
  have hq : (Submodule.Quotient.mk (∑ k ∈ s, W k) : H2 μ) =
      ∑ k ∈ s, (Submodule.Quotient.mk (W k) : H2 μ) :=
    map_sum (Submodule.mkQ _) W s
  rw [hWsum, hq, map_sum]
  simp only [hW]
  rw [← Finset.mul_sum, ← hdec (x γ) ⟨γ, rfl⟩ (y φ)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralUnramifiedExtIffIsIntegralBaseStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_unramifiedExt_iff_isIntegral_base : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (a : B.A), @IsIntegral K'.O (overExt φ B ψ hψ hσ).A _ _ _ a ↔ IsIntegral K.O a := by
  first | exact @GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff | exact GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff | (intros; apply GlobalTheory.UnitLemma.Unr.isIntegral_overExt_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportMixedModelPartialStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_mixedModelPartialFourierColumn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ f : Gl r F → ℂ, IsTest f → IsTest (WeilMix.ptrB M ψ f) := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_isTest | exact GlobalTheory.JR.WeilMix.ptrB_isTest | (intros; apply GlobalTheory.JR.WeilMix.ptrB_isTest <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearDescentPartialFourierEqFourierDescentStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearDescent_partialFourier_eq_fourier_descent : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c)) → ∀ x : A.K × A.K, LinDesc.desc A M hG lam α (fourG M ψ f') x = A.fourK μK ψ (LinDesc.desc A M hG lam α f') x := by
  first | exact @GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc | exact GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc | (intros; apply GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MixedModelPartialFourierLinearStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelPartialFourier_linear : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (c : ℂ) (f f' : Gl r F → ℂ), IsTest f → IsTest f' → WeilMix.ptrB M ψ (c • f + f') = c • WeilMix.ptrB M ψ f + WeilMix.ptrB M ψ f' := by
  first | exact @GlobalTheory.JR.WeilMix.ptrB_linear | exact GlobalTheory.JR.WeilMix.ptrB_linear | (intros; apply GlobalTheory.JR.WeilMix.ptrB_linear <;> assumption)
end

