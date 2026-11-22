import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLeOne
section
noncomputable section

open Formalism.ConjugateSelfDual
open scoped Matrix

namespace GlobalTheory.SmallMat

variable {l : ℕ} [Fact l.Prime]

def Sm (ε : ℝ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) : Prop := ∀ i j, ‖M i j‖ ≤ ε

theorem Sm.mono {ε δ : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (h : Sm ε M) (hεδ : ε ≤ δ) : Sm δ M :=
  fun i j => (h i j).trans hεδ

theorem Sm.add {ε : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm ε N) : Sm ε (M + N) := fun i j => by
  simp only [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hM i j) (hN i j))

theorem Sm.neg {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) : Sm ε (-M) := fun i j => by
  simpa using hM i j

theorem Sm.sub {ε : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm ε N) : Sm ε (M - N) := by
  rw [sub_eq_add_neg]; exact hM.add hN.neg

theorem sm_zero {ε : ℝ} (hε : 0 ≤ ε) : Sm (l := l) ε 0 := fun i j => by simpa using hε

theorem Sm.mul {ε δ : ℝ} {M N : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hN : Sm δ N) (hε : 0 ≤ ε) :
    Sm (ε * δ) (M * N) := fun i j => by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> rw [norm_mul] <;>
    exact mul_le_mul (hM _ _) (hN _ _) (norm_nonneg _) hε

theorem Sm.smul {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (a : Qbar l) : Sm (‖a‖ * ε) (a • M) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul]; exact mul_le_mul_of_nonneg_left (hM i j) (norm_nonneg _)

theorem Sm.smul_le {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hε : 0 ≤ ε) {a : Qbar l} (ha : ‖a‖ ≤ 1) :
    Sm ε (a • M) :=
  (hM.smul a).mono (by simpa using mul_le_mul_of_nonneg_right ha hε)

theorem sm_scalar {ε : ℝ} {a : Qbar l} (ha : ‖a‖ ≤ ε) (hε : 0 ≤ ε) : Sm ε (a • (1 : Matrix (Fin 2) (Fin 2) (Qbar l))) :=
  fun i j => by
    by_cases h : i = j
    · subst h; simpa using ha
    · simpa [Matrix.one_apply_ne h] using hε

theorem Sm.sum {ι : Type*} (s : Finset ι) {ε : ℝ} (hε : 0 ≤ ε) (M : ι → Matrix (Fin 2) (Fin 2) (Qbar l))
    (h : ∀ i ∈ s, Sm ε (M i)) : Sm ε (∑ i ∈ s, M i) := fun a b => by
  rw [Matrix.sum_apply]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun i hi => h i hi a b

theorem norm_natCast_le_one (b : ℕ) : ‖(b : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ b

theorem Sm.det {ε : ℝ} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : Sm ε M) (hε : 0 ≤ ε) : ‖M.det‖ ≤ ε ^ 2 := by
  rw [Matrix.det_fin_two, sq, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;> simp only [norm_neg, norm_mul] <;>
    exact mul_le_mul (hM _ _) (hM _ _) (norm_nonneg _) hε

end GlobalTheory.SmallMat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NsmulMemSpanOfCardLe
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.CycIndex

theorem nsmul_mem_span_of_card_le : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (C r : ℕ), ∃ m : ℕ, 0 < m ∧ ∀ (n : ℕ) (H : Type) [AddCommGroup H] [Module c.O H] [Finite H], (∀ h : H, ((l : ℕ) : c.O) ^ n • h = 0) → Nat.card H ≤ C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ n)) → ∀ z : H, (∀ x : c.O, x • z = 0 → ((l : ℕ) : c.O) ^ (n - r) ∣ x) → ∀ h : H, ∃ x : c.O, m • h = x • z := by
  intro l _ c C r
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h0
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h0]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hfin : ∀ k : ℕ, Finite (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ k)) := fun k =>
    (UpperTheory.V.X.So.levFacts l c.O _ (pow_ne_zero k hl0) _ ⟨LinearEquiv.refl _ _⟩).1
  refine ⟨(C * Nat.card (UpperTheory.V.X.Lev (((l : ℕ) : c.O) ^ r))).factorial, Nat.factorial_pos _, ?_⟩
  intro n H _ _ _ hkill hcard z hann h
  set L : c.O := ((l : ℕ) : c.O) with hL
  haveI := hfin n
  haveI := hfin r
  let f : UpperTheory.V.X.Lev (L ^ n) →ₗ[c.O] H :=
    (Ideal.span {L ^ n}).liftQ (LinearMap.toSpanSingleton c.O H z) (by
      rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hkill z)
  have hf : ∀ x : c.O, f (UpperTheory.V.X.Lev.mk (L ^ n) x) = x • z := fun x => rfl
  let g : UpperTheory.V.X.Lev (L ^ r) →ₗ[c.O] UpperTheory.V.X.Lev (L ^ n) :=
    (Ideal.span {L ^ r}).liftQ ((L ^ (n - r)) • UpperTheory.V.X.Lev.mk (L ^ n)) (by
      rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul,
        UpperTheory.V.X.Lev.mk_eq_zero, smul_eq_mul, ← pow_add]
      exact pow_dvd_pow _ (by omega))
  have hg : ∀ w : c.O, g (UpperTheory.V.X.Lev.mk (L ^ r) w) = UpperTheory.V.X.Lev.mk (L ^ n) (L ^ (n - r) * w) := by
    intro w
    show (L ^ (n - r)) • UpperTheory.V.X.Lev.mk (L ^ n) w = _
    rw [← map_smul, smul_eq_mul]
  have hker : LinearMap.ker f ≤ LinearMap.range g := by
    intro y hy
    obtain ⟨x, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective (L ^ n) y
    rw [LinearMap.mem_ker, hf] at hy
    obtain ⟨w, rfl⟩ := hann x hy
    exact ⟨UpperTheory.V.X.Lev.mk (L ^ r) w, hg w⟩
  have hK : Nat.card (LinearMap.ker f) ≤ Nat.card (UpperTheory.V.X.Lev (L ^ r)) :=
    (Nat.card_le_card_of_injective _ (Submodule.inclusion_injective hker)).trans
      (Nat.card_le_card_of_surjective _ g.surjective_rangeRestrict)
  have h1 : Nat.card (UpperTheory.V.X.Lev (L ^ n)) =
      Nat.card (LinearMap.ker f) * Nat.card (UpperTheory.V.X.Lev (L ^ n) ⧸ LinearMap.ker f) :=
    Submodule.card_eq_card_quotient_mul_card _
  rw [Nat.card_congr f.quotKerEquivRange.toEquiv] at h1
  have h2 : Nat.card H = Nat.card (LinearMap.range f) * Nat.card (H ⧸ LinearMap.range f) :=
    Submodule.card_eq_card_quotient_mul_card _
  have hSpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  have hQ : Nat.card (H ⧸ LinearMap.range f) ≤ C * Nat.card (UpperTheory.V.X.Lev (L ^ r)) := by
    have : Nat.card (H ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) ≤
        (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))) * Nat.card (LinearMap.range f) := by
      calc Nat.card (H ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) = Nat.card H := by
              rw [h2, mul_comm]
        _ ≤ C * Nat.card (UpperTheory.V.X.Lev (L ^ n)) := hcard
        _ = C * (Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f)) := by rw [h1]
        _ ≤ C * (Nat.card (UpperTheory.V.X.Lev (L ^ r)) * Nat.card (LinearMap.range f)) := by gcongr
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this hSpos
  haveI : Finite (H ⧸ LinearMap.range f) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hdvd : Nat.card (H ⧸ LinearMap.range f) ∣ (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))).factorial :=
    Nat.dvd_factorial Nat.card_pos hQ
  obtain ⟨k, hk⟩ := hdvd
  have hmem : (C * Nat.card (UpperTheory.V.X.Lev (L ^ r))).factorial • h ∈ LinearMap.range f := by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_nsmul, hk, mul_comm, mul_nsmul,
      card_nsmul_eq_zero']
  obtain ⟨y, hy⟩ := hmem
  obtain ⟨x, rfl⟩ := UpperTheory.V.X.Lev.mk_surjective (L ^ n) y
  exact ⟨x, by rw [← hy, hf]⟩

end GlobalTheory.CycIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicHomSmallOnDeepCongruenceSubgroups
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.lam_small_of_deep_congruence : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → Continuous lam → r.ker ≤ lam.ker → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g : Γ, (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖) → ‖(lam g).toAdd‖ ≤ ε := by
  intro l _ Γ _ _ _ r lam hr hlam hker ε hε
  have hl : ‖((l:ℕ) : Qbar l)‖ = (l:ℝ)⁻¹ := by
    have : ((l:ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    simp [Padic.norm_p]
  have hl1 : ‖((l:ℕ) : Qbar l)‖ < 1 := by
    rw [hl]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  by_contra hcon
  push_neg at hcon
  set F : ℕ → Set Γ := fun N => {g | ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} ∩ {g | ε ≤ ‖(lam g).toAdd‖} with hF
  have hcm : Continuous fun g => ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) := (Units.continuous_val.comp hr).sub continuous_const
  have hclosed : ∀ N, IsClosed (F N) := by
    intro N
    refine IsClosed.inter ?_ ?_
    · have : {g | ∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} = ⋂ i, ⋂ j, {g | ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ N‖} := by
        ext g; simp
      rw [this]
      refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
      exact isClosed_le (continuous_norm.comp ((continuous_apply j).comp ((continuous_apply i).comp hcm))) continuous_const
    · exact isClosed_le continuous_const (continuous_norm.comp (continuous_toAdd.comp hlam))
  have hmono : ∀ N, F (N+1) ⊆ F N := by
    intro N g hg
    refine ⟨fun i j => (hg.1 i j).trans ?_, hg.2⟩
    rw [norm_pow, norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ N)
  have hne : ∀ N, (F N).Nonempty := by
    intro N
    obtain ⟨g, hg1, hg2⟩ := hcon N
    exact ⟨g, hg1, hg2.le⟩
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F hmono hne (hclosed 0).isCompact hclosed
  rw [Set.mem_iInter] at hg
  have hzero : ∀ i j, ((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j = 0 := by
    intro i j
    by_contra hx
    have hpos : 0 < ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ := norm_pos_iff.mpr hx
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hpos hl1
    have := (hg N).1 i j
    rw [norm_pow] at this
    linarith
  have hrg : r g = 1 := by
    apply Units.ext
    have : (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1 = 0 := by
      ext i j; exact hzero i j
    simpa [sub_eq_zero] using this
  have hlg : lam g = 1 := hker (MonoidHom.mem_ker.mpr hrg)
  have h2 : ε ≤ ‖(lam g).toAdd‖ := (hg 0).2
  rw [hlg] at h2
  simp at h2
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def MemE (c : Coef l) (x : Qbar l) : Prop := ∃ k : ℕ, (l : Qbar l) ^ k * x ∈ c.O

def VecE (c : Coef l) (y : Fin 2 → Qbar l) : Prop := ∃ k : ℕ, ∀ i, (l : Qbar l) ^ k * y i ∈ c.O

theorem natPow_mem (c : Coef l) (k : ℕ) : (l : Qbar l) ^ k ∈ c.O :=
  c.O.pow_mem (c.O.natCast_mem l) k

theorem pow_mul_mem_add (c : Coef l) {x : Qbar l} {k : ℕ} (h : (l : Qbar l) ^ k * x ∈ c.O) (j : ℕ) :
    (l : Qbar l) ^ (k + j) * x ∈ c.O := by
  rw [pow_add, mul_comm ((l : Qbar l) ^ k), mul_assoc]
  exact c.O.mul_mem (natPow_mem c j) h

theorem memE_add {c : Coef l} {x y : Qbar l} (hx : MemE c x) (hy : MemE c y) : MemE c (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨k + j, ?_⟩
  have h2 := pow_mul_mem_add c hj k
  rw [add_comm j k] at h2
  rw [mul_add]
  exact c.O.add_mem (pow_mul_mem_add c hk j) h2

theorem memE_neg {c : Coef l} {x : Qbar l} (hx : MemE c x) : MemE c (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [mul_neg]; exact c.O.neg_mem hk⟩

theorem vecE_add {c : Coef l} {x y : Fin 2 → Qbar l} (hx : VecE c x) (hy : VecE c y) : VecE c (x + y) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨j, hj⟩ := hy
  refine ⟨k + j, fun i => ?_⟩
  have h2 := pow_mul_mem_add c (hj i) k
  rw [add_comm j k] at h2
  rw [Pi.add_apply, mul_add]
  exact c.O.add_mem (pow_mul_mem_add c (hk i) j) h2

theorem vecE_neg {c : Coef l} {x : Fin 2 → Qbar l} (hx : VecE c x) : VecE c (-x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, fun i => by rw [Pi.neg_apply, mul_neg]; exact c.O.neg_mem (hk i)⟩

def divSelCoc (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) :
    AddSubgroup (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | (∃ k : ℕ, ∀ s i, (l : Qbar l) ^ k * z s i ∈ c.O) ∧
    (∀ s t i, z (s * t) i - z s i - (mat W s *ᵥ z t) i ∈ c.O) ∧
    (∀ s, ∀ᶠ t in nhds s, ∀ i, z t i - z s i ∈ c.O) ∧
    (∀ a ∈ (toGS Ω (S : Set Pl)).ker, ∀ i, z a i ∈ c.O) ∧
    (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q →
      ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, ∀ i, z s i - (mat W s *ᵥ y - y) i ∈ c.O) ∧
    (∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, z s 1 - (mat W s 1 1 * y - y) ∈ c.O)}
  add_mem' := by
    rintro z w ⟨⟨k, hk⟩, h2, h3, h4, h5, ⟨y, hy, h6⟩⟩ ⟨⟨k', hk'⟩, h2', h3', h4', h5', ⟨y', hy', h6'⟩⟩
    refine ⟨⟨k + k', fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B hB => ?_,
      ⟨y + y', memE_add hy hy', fun s hs => ?_⟩⟩
    · have h := pow_mul_mem_add c (hk' s i) k
      rw [add_comm k' k] at h
      rw [Pi.add_apply, Pi.add_apply, mul_add]
      exact c.O.add_mem (pow_mul_mem_add c (hk s i) k') h
    · have e : (z + w) (s * t) i - (z + w) s i - (mat W s *ᵥ (z + w) t) i =
          (z (s * t) i - z s i - (mat W s *ᵥ z t) i) + (w (s * t) i - w s i - (mat W s *ᵥ w t) i) := by
        simp only [Pi.add_apply, Matrix.mulVec_add]; ring
      rw [e]; exact c.O.add_mem (h2 s t i) (h2' s t i)
    · filter_upwards [h3 s, h3' s] with t ht ht' i
      have e : (z + w) t i - (z + w) s i = (z t i - z s i) + (w t i - w s i) := by
        simp only [Pi.add_apply]; ring
      rw [e]; exact c.O.add_mem (ht i) (ht' i)
    · rw [Pi.add_apply, Pi.add_apply]; exact c.O.add_mem (h4 a ha i) (h4' a ha i)
    · obtain ⟨u, hu, hu'⟩ := h5 q hq hl B hB
      obtain ⟨u', hv, hv'⟩ := h5' q hq hl B hB
      refine ⟨u + u', vecE_add hu hv, fun s hs i => ?_⟩
      have e : (z + w) s i - (mat W s *ᵥ (u + u') - (u + u')) i =
          (z s i - (mat W s *ᵥ u - u) i) + (w s i - (mat W s *ᵥ u' - u') i) := by
        simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add]; ring
      rw [e]; exact c.O.add_mem (hu' s hs i) (hv' s hs i)
    · have e : (z + w) s 1 - (mat W s 1 1 * (y + y') - (y + y')) =
          (z s 1 - (mat W s 1 1 * y - y)) + (w s 1 - (mat W s 1 1 * y' - y')) := by
        simp only [Pi.add_apply]; ring
      rw [e]; exact c.O.add_mem (h6 s hs) (h6' s hs)
  zero_mem' := by
    refine ⟨⟨0, fun s i => by simp⟩, fun s t i => by simp, fun s => Filter.Eventually.of_forall fun t i => by simp,
      fun a _ i => by simp, fun q _ _ B _ => ⟨0, ⟨0, fun i => by simp⟩, fun s _ i => by simp⟩, ⟨0, ⟨0, by simp⟩, fun s _ => by simp⟩⟩
  neg_mem' := by
    rintro z ⟨⟨k, hk⟩, h2, h3, h4, h5, ⟨y, hy, h6⟩⟩
    refine ⟨⟨k, fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B hB => ?_,
      ⟨-y, memE_neg hy, fun s hs => ?_⟩⟩
    · rw [Pi.neg_apply, Pi.neg_apply, mul_neg]; exact c.O.neg_mem (hk s i)
    · have e : (-z) (s * t) i - (-z) s i - (mat W s *ᵥ (-z) t) i = -(z (s * t) i - z s i - (mat W s *ᵥ z t) i) := by
        simp only [Pi.neg_apply, Matrix.mulVec_neg]; ring
      rw [e]; exact c.O.neg_mem (h2 s t i)
    · filter_upwards [h3 s] with t ht i
      have e : (-z) t i - (-z) s i = -(z t i - z s i) := by simp only [Pi.neg_apply]; ring
      rw [e]; exact c.O.neg_mem (ht i)
    · rw [Pi.neg_apply, Pi.neg_apply]; exact c.O.neg_mem (h4 a ha i)
    · obtain ⟨u, hu, hu'⟩ := h5 q hq hl B hB
      refine ⟨-u, vecE_neg hu, fun s hs i => ?_⟩
      have e : (-z) s i - (mat W s *ᵥ (-u) - (-u)) i = -(z s i - (mat W s *ᵥ u - u) i) := by
        simp only [Pi.neg_apply, Pi.sub_apply, Matrix.mulVec_neg]; ring
      rw [e]; exact c.O.neg_mem (hu' s hs i)
    · have e : (-z) s 1 - (mat W s 1 1 * (-y) - (-y)) = -(z s 1 - (mat W s 1 1 * y - y)) := by
        simp only [Pi.neg_apply]; ring
      rw [e]; exact c.O.neg_mem (h6 s hs)

def divCob (c : Coef l) (W : R2 Ω l) : AddSubgroup (G ℚ Ω → Fin 2 → Qbar l) where
  carrier := {z | ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s i, z s i - (mat W s *ᵥ y - y) i ∈ c.O}
  add_mem' := by
    rintro z w ⟨u, hu, hu'⟩ ⟨u', hv, hv'⟩
    refine ⟨u + u', vecE_add hu hv, fun s i => ?_⟩
    have e : (z + w) s i - (mat W s *ᵥ (u + u') - (u + u')) i =
        (z s i - (mat W s *ᵥ u - u) i) + (w s i - (mat W s *ᵥ u' - u') i) := by
      simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_add]; ring
    rw [e]; exact c.O.add_mem (hu' s i) (hv' s i)
  zero_mem' := ⟨0, ⟨0, fun i => by simp⟩, fun s i => by simp⟩
  neg_mem' := by
    rintro z ⟨u, hu, hu'⟩
    refine ⟨-u, vecE_neg hu, fun s i => ?_⟩
    have e : (-z) s i - (mat W s *ᵥ (-u) - (-u)) i = -(z s i - (mat W s *ᵥ u - u) i) := by
      simp only [Pi.neg_apply, Pi.sub_apply, Matrix.mulVec_neg]; ring
    rw [e]; exact c.O.neg_mem (hu' s i)

abbrev DivSel (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) : Type :=
  ↥(divSelCoc c W S A) ⧸ (divCob c W).addSubgroupOf (divSelCoc c W S A)

theorem divSel_torsion (c : Coef l) (W : R2 Ω l) (S : Finset Pl) (A : ValuationSubring Ω) :
    ∀ x : DivSel c W S A, ∃ n : ℕ, l ^ n • x = 0 := by
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    obtain ⟨k, hk⟩ := z.2.1
    refine ⟨k, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine ⟨0, ⟨0, fun i => by simp⟩, fun s i => ?_⟩
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul, Matrix.mulVec_zero, sub_zero, Pi.zero_apply]
    push_cast
    exact hk s i

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2AdjointNoInvariantOfIrreducible
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open GlobalTheory.Sl2Ad

namespace GlobalTheory

theorem ad_invariant_eq_zero_of_isIrr {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ]
    (ρ : Γ →* GL (Fin 2) K) (hρ : IsIrr ρ) (v : Fin 3 → K) (hv : ∀ g, ad (ρ g) *ᵥ v = v) : v = 0 := by
  set Y : Matrix (Fin 2) (Fin 2) K := ofCoord v with hY

  have hcomm : ∀ g, ((ρ g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
    intro g
    have h1 : coord ((ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = coord Y := by
      rw [coord_conj_ofCoord, hv g, coord_ofCoord]
    have h2 : (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = Y := by
      have := congrArg ofCoord h1
      rwa [ofCoord_coord (by rw [trace_conj, trace_ofCoord]), ofCoord_coord (trace_ofCoord v)] at this
    calc (ρ g : Matrix (Fin 2) (Fin 2) K) * Y
        = (ρ g : Matrix (Fin 2) (Fin 2) K) * Y * (((ρ g)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (ρ g : Matrix (Fin 2) (Fin 2) K) := by
          rw [Matrix.mul_assoc _ _ (ρ g : Matrix (Fin 2) (Fin 2) K), ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = Y * (ρ g : Matrix (Fin 2) (Fin 2) K) := by rw [h2]
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' Y)
  set W := Module.End.eigenspace (Matrix.toLin' Y) μ with hW
  have hWne : W ≠ ⊥ := Module.End.hasEigenvalue_iff.mp hμ
  have hWinv : IsInv ρ W := by
    intro g x hx
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx ⊢
    rw [Matrix.mulVec_mulVec, ← hcomm g, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
  have hWtop : W = ⊤ := by
    rcases hρ.2.2 W le_top hWinv with h | h
    · exact absurd h hWne
    · exact h
  have hYμ : Y = μ • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    have hx : (Pi.single j 1 : Fin 2 → K) ∈ W := by rw [hWtop]; trivial
    rw [hW, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.mulVec_single_one] at hx
    have := congrFun hx i
    simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Pi.single_apply, Ne.symm hij]
  have htr : (2 : K) * μ = 0 := by
    have := trace_ofCoord v
    rw [← hY, hYμ, Matrix.trace_smul, Matrix.trace_one] at this
    simpa [mul_comm] using this
  have hμ0 : μ = 0 := by
    rcases mul_eq_zero.mp htr with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hY0 : Y = 0 := by rw [hYμ, hμ0, zero_smul]
  rw [← coord_ofCoord v, ← hY, hY0]
  ext i; fin_cases i <;> simp [coord]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SrcOfRepIso
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SrcConj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

theorem tw_conj (r r' : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (g : GL (Fin n) k)
    (h : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) : tw r' χ s = g * tw r χ s * g⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, tw_val, tw_val, h s, Units.val_mul, Units.val_mul,
    Matrix.mul_smul, Matrix.smul_mul]

theorem isSSRep_conj (r r' : Γ →* GL (Fin n) k) (g : GL (Fin n) k) (h : ∀ s, r' s = g * r s * g⁻¹)
    (hr : IsSSRep r) : IsSSRep r' := by
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ?_ ?_ hr
  · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · intro s
    rw [h s, ← Units.val_mul, ← Units.val_mul]
    congr 1
    group

theorem att_conj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {k' : ℕ}
    (f : Newform k') (V V' : G ℚ Ω →* GL (Fin 2) (Qbar l)) (g : GL (Fin 2) (Qbar l))
    (h : ∀ s, V' s = g * V s * g⁻¹) (hV : f.Att ι V) : f.Att ι V' := by
  refine ⟨isSSRep_conj V V' g h hV.1, hV.2.mono fun w hw A hA => ?_⟩
  obtain ⟨hI, hF⟩ := hw A hA
  refine ⟨fun s hs => by rw [h s, hI s hs, mul_one, mul_inv_cancel], fun σ hσ => ?_⟩
  rw [← hF σ hσ, h σ⁻¹, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

end GlobalTheory.Ord2.SrcConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedOfLevelAwayInertiaCharacters
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem unramified_of_levelAway : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (M : ℕ), 1 ≤ M → LevelAway l M W → ∃ S : Finset Pl, ContainsAbove S l ∧ ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker := by
  intro l _ Ω _ _ _ W M hM hL
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hne : Ideal.span {((l * M : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hl0 (by omega))
  have hfin := Ideal.finite_factors hne
  have hmem : ∀ v : Pl, v ∈ hfin.toFinset ↔ ((l * M : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro v
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro v hv
    rw [hmem, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hv
  · intro w hw B hB s hs
    rw [hmem, Nat.cast_mul] at hw
    have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (w.asIdeal.mul_mem_right _ h)
    have hMw : ((M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (w.asIdeal.mul_mem_left _ h)
    obtain ⟨A, hA, χ, hχ, g, hg⟩ := hL w hlw
    have hMA : ¬ A.valuation (M : Ω) < 1 := by
      intro h
      apply hMw
      apply (hA (M : 𝓞 ℚ)).1
      simpa using h
    have key : ∀ u ∈ Ine (F := ℚ) A, W u = 1 := by
      intro u hu
      have h1 : ∀ i, χ i u = 1 := fun i => hχ i u fun ζ hζ => GlobalTheory.TameTau.ine_fix_root hu M hMA hζ
      have h2 := hg u hu
      have h3 : g * W u * g⁻¹ = 1 := by
        apply Units.ext
        rw [h2]
        simp [h1]
      have h4 : W u = g⁻¹ * (g * W u * g⁻¹) * g := by group
      rw [h4, h3]; group
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver hA hB
    have h5 := key _ (GlobalTheory.ParamRepCompare.conj_mem_Ine_of_smul_eq hσ hs)
    have h6 : s = σ * (σ⁻¹ * s * σ) * σ⁻¹ := by group
    rw [MonoidHom.mem_ker, h6, map_mul, map_mul, h5, mul_one, ← map_mul, mul_inv_cancel, map_one]

end GlobalTheory.Ord2
end

