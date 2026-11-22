import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0372
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0378
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0382
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0389
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0385
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0390
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivCoboundaryOfReducedCocyclesCohomologousStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divCoboundary_of_reducedCocycles_cohomologous : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (z z' : G ℚ Ω → Fin 2 → Qbar l) (y y' : Fin 2 → Qbar l), VecE c y → VecE c y' → (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) → (∀ s i, (l : Qbar l) * z' s i - (mat W s *ᵥ y' - y') i ∈ c.O) → (∃ m : ResPlane c, ∀ s, resCoc c W z y s - resCoc c W z' y' s = resAct c W hO s m - m) → z - z' ∈ divCob c W := by
  first | exact @GlobalTheory.Ord2.divCob_of_resCoc_cohom | exact GlobalTheory.Ord2.divCob_of_resCoc_cohom | (intros; apply GlobalTheory.Ord2.divCob_of_resCoc_cohom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisibleOrdinarySelmerChainExistsIntegralRepresStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisibleOrdinarySelmerChain_exists_integral_representatives : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → (∀ s ∈ Dec (F := ℚ) A, mat W s 1 0 = 0) → ∀ x : ℕ → DivSel c W S A, x 0 ≠ 0 → (∀ n, l • x (n + 1) = x n) → ∃ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (N : ℕ), (∀ n s i, a n s i ∈ c.O) ∧ (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) ∧ (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) ∧ (∀ n s, Cv n (a (n + 1) s) (a n s)) ∧ (∀ n, ∀ b ∈ (toGS Ω (S : Set Pl)).ker, Cv n (a n b) 0) ∧ (∀ n, ∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s ∈ Ine (F := ℚ) B, Cv n (a n s) (mat W s *ᵥ y - y)) ∧ (∀ n, ∃ y : Qbar l, MemE c y ∧ ∀ s ∈ Dec (F := ℚ) A, Cg n (a n s 1) (mat W s 1 1 * y - y)) ∧ ¬ ∃ y : Fin 2 → Qbar l, VecE c y ∧ ∀ s, Cv N (a N s) (mat W s *ᵥ y - y) := by
  first | exact @GlobalTheory.Ord2.DivChain.representatives | exact GlobalTheory.Ord2.DivChain.representatives | (intros; apply GlobalTheory.Ord2.DivChain.representatives <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelPerp

variable {l : ℕ} [Fact l.Prime]

def tau (c : Coef l) : c.O →ₗ[ℤ_[l]] ℤ_[l] := Classical.choose (coef_dual_free_rank_one l c)

theorem tau_spec (c : Coef l) : ∀ f : c.O →ₗ[ℤ_[l]] ℤ_[l], ∃! a : c.O, ∀ x, f x = tau c (a * x) :=
  Classical.choose_spec (coef_dual_free_rank_one l c)

theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : Qbar l)‖ = 1 := by
  have h1 := CupCob.norm_le_one_of_mem c (u : c.O).2
  have h2 := CupCob.norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h3 : ((u : c.O) : Qbar l) * (((u⁻¹ : c.Oˣ) : c.O) : Qbar l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have h4 := congrArg norm h3
  rw [norm_mul, norm_one] at h4
  nlinarith [norm_nonneg ((u : c.O) : Qbar l), norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : Qbar l)]

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((l : ℕ) : ℚ_[l]) := by simp
  rw [e, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem dvd_of_mem_Ik (c : Coef l) (n : ℕ) {x : c.O} (hx : x ∈ Ik c n) : ∃ y : c.O, x = (l : c.O) ^ n * y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hl0 : (l : c.O) ≠ 0 := by
    intro h
    have : ((l : c.O) : Qbar l) = 0 := by rw [h]; rfl
    rw [SubringClass.coe_natCast] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have nl : ‖((l : c.O) : Qbar l)‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ e := by
    rw [hw, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have nx : ‖((x : c.O) : Qbar l)‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ k := by
    rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have hlt : ‖((l : c.O) : Qbar l)‖ < 1 := by rw [SubringClass.coe_natCast]; exact norm_l_lt_one
  have hϖ1 : ‖((ϖ : c.O) : Qbar l)‖ ≤ 1 := CupCob.norm_le_one_of_mem c ϖ.2
  have he : e ≠ 0 := by
    rintro rfl
    rw [nl, pow_zero] at hlt
    exact lt_irrefl _ hlt
  have hϖlt : ‖((ϖ : c.O) : Qbar l)‖ < 1 := by
    rcases hϖ1.lt_or_eq with h | h
    · exact h
    · rw [nl, h, one_pow] at hlt; exact absurd hlt (lt_irrefl _)
  have hϖ0 : 0 < ‖((ϖ : c.O) : Qbar l)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hle : e * n ≤ k := by
    have h := (mem_Ik.1 hx)
    have e2 : ‖((l : ℕ) : Qbar l) ^ n‖ = ‖((ϖ : c.O) : Qbar l)‖ ^ (e * n) := by
      rw [norm_pow, ← SubringClass.coe_natCast c.O, nl, pow_mul]
    rw [nx, e2] at h
    exact (pow_le_pow_iff_right_of_lt_one₀ hϖ0 hϖlt).1 h
  refine ⟨(u : c.O) * ϖ ^ (k - e * n) * ((w⁻¹ : c.Oˣ) : c.O) ^ n, ?_⟩
  rw [hu, hw]
  have hk : k = e * n + (k - e * n) := by omega
  conv_lhs => rw [hk]
  calc (u : c.O) * ϖ ^ (e * n + (k - e * n))
      = (u : c.O) * ϖ ^ (k - e * n) * (((w : c.O) * ((w⁻¹ : c.Oˣ) : c.O)) ^ n * ϖ ^ (e * n)) := by
        rw [Units.mul_inv, one_pow, one_mul, pow_add]; ring
    _ = _ := by ring

theorem tau_red_zero (c : Coef l) (n : ℕ) {x : c.O} (hx : x ∈ Ik c n) :
    PadicInt.toZModPow n (tau c x) = 0 := by
  obtain ⟨y, rfl⟩ := dvd_of_mem_Ik c n hx
  have e : (l : c.O) ^ n * y = ((l : ℤ_[l]) ^ n) • y := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [e, map_smul, smul_eq_mul, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_mul]

def lft (c : Coef l) (n : ℕ) : Qn c n → c.O := Function.surjInv (red_surjective c n)

theorem red_lft (c : Coef l) (n : ℕ) (b : Qn c n) : red c n (lft c n b) = b :=
  Function.surjInv_eq (red_surjective c n) b

theorem tau_congr (c : Coef l) (n : ℕ) {x y : c.O} (h : red c n x = red c n y) :
    PadicInt.toZModPow n (tau c x) = PadicInt.toZModPow n (tau c y) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  refine tau_red_zero c n ?_
  rw [← red_eq_zero_iff_mem, map_sub, h, sub_self]

def tbA (c : Coef l) (n : ℕ) : Qn c n →+ ZMod (l ^ n) where
  toFun b := PadicInt.toZModPow n (tau c (lft c n b))
  map_zero' := by
    rw [← map_zero (red c n), tau_congr c n (red_lft c n _), map_zero, map_zero]
  map_add' a b := by
    obtain ⟨x, rfl⟩ := red_surjective c n a
    obtain ⟨y, rfl⟩ := red_surjective c n b
    rw [← map_add, tau_congr c n (red_lft c n _), tau_congr c n (red_lft c n _),
      tau_congr c n (red_lft c n _), map_add, map_add]

theorem tbA_red (c : Coef l) (n : ℕ) (x : c.O) : tbA c n (red c n x) = PadicInt.toZModPow n (tau c x) :=
  tau_congr c n (red_lft c n _)

def pairA (c : Coef l) (n : ℕ) (y : Mn c n) : Mn c n →+ ZMod (l ^ n) where
  toFun x := tbA c n (x 0 * y 1 - x 1 * y 0)
  map_zero' := by simp
  map_add' a b := by
    rw [← map_add]; congr 1; simp only [Pi.add_apply]; ring

def Phi (c : Coef l) (n : ℕ) : Mn c n →ₗ[ZMod (l ^ n)] TDual (ZMod (l ^ n)) (Mn c n) :=
  (AddMonoidHom.mk' (fun y => TDual.mk ((pairA c n y).toZModLinearMap (l ^ n))) (fun a b => by
    ext x
    show tbA c n _ = tbA c n _ + tbA c n _
    rw [← map_add]; congr 1; simp only [Pi.add_apply]; ring)).toZModLinearMap (l ^ n)

theorem Phi_apply (c : Coef l) (n : ℕ) (y x : Mn c n) : Phi c n y x = tbA c n (x 0 * y 1 - x 1 * y 0) := rfl

theorem red_mulVec (c : Coef l) (n : ℕ) (M : Matrix (Fin 2) (Fin 2) (Qbar l)) (hM : ∀ i j, M i j ∈ c.O)
    (v : Fin 2 → Qbar l) (hv : ∀ i, v i ∈ c.O) (i : Fin 2) :
    red c n ⟨(M *ᵥ v) i, CupCob.mulVec_mem c M v hM hv i⟩ =
      ((Matrix.of fun i j => red c n ⟨M i j, hM i j⟩) *ᵥ fun j => red c n ⟨v j, hv j⟩) i := by
  have e : (⟨(M *ᵥ v) i, CupCob.mulVec_mem c M v hM hv i⟩ : c.O) =
      (⟨M i 0, hM i 0⟩ : c.O) * ⟨v 0, hv 0⟩ + (⟨M i 1, hM i 1⟩ : c.O) * ⟨v 1, hv 1⟩ := by
    apply Subtype.ext
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Subalgebra.coe_add, Subalgebra.coe_mul]
  rw [e, map_add, map_mul, map_mul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]

def lftV (c : Coef l) (n : ℕ) (y : Mn c n) : Fin 2 → Qbar l := fun i => (lft c n (y i) : Qbar l)

theorem lftV_mem (c : Coef l) (n : ℕ) (y : Mn c n) (i : Fin 2) : lftV c n y i ∈ c.O := (lft c n (y i)).2

theorem red_lftV (c : Coef l) (n : ℕ) (y : Mn c n) (i : Fin 2) : red c n ⟨lftV c n y i, lftV_mem c n y i⟩ = y i :=
  red_lft c n (y i)

theorem cg_of_red {c : Coef l} {n : ℕ} {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O)
    (h : red c n ⟨a, ha⟩ = red c n ⟨b, hb⟩) : Cg n a b := (red_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).1 h

theorem red_of_cg {c : Coef l} {n : ℕ} {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O)
    (h : Cg n a b) : red c n ⟨a, ha⟩ = red c n ⟨b, hb⟩ := (red_eq_iff ⟨a, ha⟩ ⟨b, hb⟩).2 h

end GlobalTheory.Ord2.SelPerp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationCombinationEqIdTracelessIrreduStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_augmentation_combination_eq_id_traceless_irreducible : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] (r : Γ →* GL (Fin 2) (Qbar l)), (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → IsIrr r → ∃ (n : ℕ) (γ : Fin n → Γ) (a : Fin n → ℚ_[l]), ∀ X : Matrix (Fin 2) (Fin 2) (Qbar l), X.trace = 0 → X = ∑ i, a i • ((r (γ i) : Matrix (Fin 2) (Fin 2) (Qbar l)) * X * ((r (γ i))⁻¹ : GL (Fin 2) (Qbar l)) - X) := by
  first | exact @GlobalTheory.Sl2Ad.augmentation_contains_one | exact GlobalTheory.Sl2Ad.augmentation_contains_one | (intros; apply GlobalTheory.Sl2Ad.augmentation_contains_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleLocalConditions
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.Unbounded

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem
  | exact _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem
  | (apply _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralElementNorm.norm_le_one_of_mem ..)

theorem mulVec_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {x : Fin 2 → Qbar l}
    (hM : ∀ i j, M i j ∈ c.O) (hx : ∀ j, x j ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM i 0) (hx 0)) (c.O.mul_mem (hM i 1) (hx 1))

theorem lpow_ne_zero (n : ℕ) : ((l : ℕ) : Qbar l) ^ n ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

theorem inv_mul_sub_mem (c : Coef l) (n : ℕ) {a b : Qbar l} (ha : a ∈ c.O) (hb : b ∈ c.O) (h : Cg n a b) :
    (((l : ℕ) : Qbar l) ^ n)⁻¹ * (a - b) ∈ c.O := by
  refine GlobalTheory.T.mem_integers_of_norm_le_one l c _ ⟨n, ?_⟩ ?_
  · rw [← mul_assoc, mul_inv_cancel₀ (lpow_ne_zero n), one_mul]
    exact c.O.sub_mem ha hb
  · rw [norm_mul, norm_inv]
    have hp : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := norm_pos_iff.2 (lpow_ne_zero n)
    rw [inv_mul_le_iff₀ hp, mul_one]
    exact h

end GlobalTheory.Ord2.Unbounded

namespace GlobalTheory.Ord2.Unbounded

theorem divSel_unbounded : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) →
    (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n W ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧
      (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n W (Ine (F := ℚ) B) z) ∧
      (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat W s 1 1 * x - x)) ∧
      ¬ Cob1 c n W ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) →
    ∀ m : ℕ, ∃ x : DivSel c W S A, l ^ m • x ≠ 0 := by
  intro l _ Ω _ _ _ S A W c hW hg H m
  obtain ⟨r, hr⟩ := GlobalTheory.T.cohomologyKernel_modPrimePower_killed_by_fixed_pow l Ω W c hW hg
  obtain ⟨n, z, hcoc, hker, hine, hdec, hnot⟩ := H (m + r)
  have hz : ∀ s i, z s i ∈ c.O := hcoc.2.1
  have hL0 : ((l : ℕ) : Qbar l) ^ n ≠ 0 := lpow_ne_zero n
  set L : Qbar l := ((l : ℕ) : Qbar l) ^ n with hL
  have hLO : L ∈ c.O := natPow_mem c n
  let ζ : G ℚ Ω → Fin 2 → Qbar l := fun s => L⁻¹ • z s
  have hζ : ∀ s i, ζ s i = L⁻¹ * z s i := fun s i => rfl
  have hmem : ζ ∈ divSelCoc c W S A := by
    refine ⟨⟨n, fun s i => ?_⟩, fun s t i => ?_, fun s => ?_, fun a ha i => ?_, fun q hq hl B' hB' => ?_, ?_⟩
    · rw [hζ, ← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hz s i
    · have e : ζ (s * t) i - ζ s i - (mat W s *ᵥ ζ t) i = L⁻¹ * (z (s * t) i - (z s + mat W s *ᵥ z t) i) := by
        simp only [ζ, Matrix.mulVec_smul, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
      rw [e]
      exact inv_mul_sub_mem c n (hz _ _) (c.O.add_mem (hz s i) (mulVec_mem c (hW s) (hz t) i))
        (hcoc.2.2 s trivial t trivial i)
    · have hc : Continuous z := by
        have := hcoc.1
        rw [Subgroup.coe_top, continuousOn_univ] at this
        exact this
      have hp : 0 < ‖L‖ := norm_pos_iff.2 hL0
      filter_upwards [Metric.tendsto_nhds.1 (hc.tendsto s) _ hp] with t ht i
      have e : ζ t i - ζ s i = L⁻¹ * (z t i - z s i) := by
        simp only [ζ, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      refine inv_mul_sub_mem c n (hz t i) (hz s i) ?_
      unfold Cg
      rw [dist_eq_norm] at ht
      exact le_trans (norm_le_pi_norm (z t - z s) i) ht.le
    · have e : ζ a i = L⁻¹ * (z a i - 0) := by rw [sub_zero, hζ]
      rw [e]
      exact inv_mul_sub_mem c n (hz a i) c.O.zero_mem (hker a ha i)
    · obtain ⟨B, hB, hcob⟩ := hine q hq hl
      obtain ⟨x, hx, hxs⟩ := GlobalTheory.T.coboundary_inertia_independent l Ω W c n z q B B' hW hcoc hB hB' hcob
      refine ⟨L⁻¹ • x, ⟨n, fun i => ?_⟩, fun s hs i => ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hx i
      · have e : ζ s i - (mat W s *ᵥ (L⁻¹ • x) - L⁻¹ • x) i = L⁻¹ * (z s i - (mat W s *ᵥ x - x) i) := by
          simp only [ζ, Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
        rw [e]
        exact inv_mul_sub_mem c n (hz s i) (c.O.sub_mem (mulVec_mem c (hW s) hx i) (hx i)) (hxs s hs i)
    · obtain ⟨x, hx, hxs⟩ := hdec
      refine ⟨L⁻¹ * x, ⟨n, ?_⟩, fun s hs => ?_⟩
      · rw [← mul_assoc, ← hL, mul_inv_cancel₀ hL0, one_mul]; exact hx
      · have e : ζ s 1 - (mat W s 1 1 * (L⁻¹ * x) - L⁻¹ * x) = L⁻¹ * (z s 1 - (mat W s 1 1 * x - x)) := by
          rw [hζ]; ring
        rw [e]
        exact inv_mul_sub_mem c n (hz s 1) (c.O.sub_mem (c.O.mul_mem (hW s 1 1) hx) hx) (hxs s hs)
  refine ⟨QuotientAddGroup.mk ⟨ζ, hmem⟩, fun h0 => hnot ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
  obtain ⟨y, ⟨k, hk⟩, hy⟩ := h0
  have hy' : ∀ s i, ((l : ℕ) : Qbar l) ^ m * ζ s i - (mat W s *ᵥ y - y) i ∈ c.O := by
    intro s i
    have := hy s i
    simp only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] at this
    push_cast at this
    exact this
  have key := hr n (fun s => ((l : ℕ) : Qbar l) ^ m • z s) (L • y)
    (fun s i => by rw [Pi.smul_apply, smul_eq_mul]; exact c.O.mul_mem (natPow_mem c m) (hz s i))
    ⟨k, fun i => by
      rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]; exact c.O.mul_mem hLO (hk i)⟩
    (fun s i => by
      have e : (((l : ℕ) : Qbar l) ^ m • z s) i - (mat W s *ᵥ (L • y) - L • y) i =
          L * (((l : ℕ) : Qbar l) ^ m * ζ s i - (mat W s *ᵥ y - y) i) := by
        rw [hζ]
        simp only [Matrix.mulVec_smul, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        rw [mul_sub L, mul_sub L, mul_left_comm L, mul_inv_cancel_left₀ hL0]
      unfold Cg
      rw [e, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one_of_mem c (hy' s i)))
  have hf : (fun s => ((l : ℕ) : Qbar l) ^ r • (fun s => ((l : ℕ) : Qbar l) ^ m • z s) s) =
      fun s => ((l : ℕ) : Qbar l) ^ (m + r) • z s := by
    funext s; rw [smul_smul, ← pow_add, add_comm]
  rw [hf] at key
  exact key

end GlobalTheory.Ord2.Unbounded

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDotProductEqOfPrimePowApproxQbarLStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dotProduct_eq_of_primePow_approx_qbarL : ∀ (l : ℕ) [Fact l.Prime] (X : Type) (m : ℕ) (M : X → Fin m → Qbar l) (z : X → Qbar l), (∀ n : ℕ, ∃ y : Fin m → Qbar l, ∀ x, ‖z x - M x ⬝ᵥ y‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖) → ∃ y : Fin m → Qbar l, ∀ x, z x = M x ⬝ᵥ y := by
  first | exact @GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow | exact GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow | (intros; apply GlobalTheory.exists_dotProduct_eq_of_approx_prime_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInertiaFixedNearAlmostFixedCoefficients
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2

namespace GlobalTheory.PerFix

variable {l : ℕ} [Fact l.Prime]

theorem norm_aut (σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l) (y : Qbar l) : ‖σ y‖ = ‖y‖ :=
  (spectralNorm_eq_of_equiv σ y).symm

def inertiaC (c : Coef l) : Subgroup (Qbar l ≃ₐ[ℚ_[l]] Qbar l) where
  carrier := {σ | (∀ b ∈ c.O, σ b = b) ∧ ∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1}
  one_mem' := ⟨fun b _ => rfl, fun y _ => by simp⟩
  mul_mem' := by
    rintro σ τ ⟨hσ1, hσ2⟩ ⟨hτ1, hτ2⟩
    refine ⟨fun b hb => ?_, fun y hy => ?_⟩
    · show σ (τ b) = b
      rw [hτ1 b hb, hσ1 b hb]
    · show ‖σ (τ y) - y‖ < 1
      have e : σ (τ y) - y = (σ (τ y) - τ y) + (τ y - y) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hσ2 _ ((norm_aut τ y).le.trans hy)) (hτ2 y hy))
  inv_mem' := by
    rintro σ ⟨hσ1, hσ2⟩
    refine ⟨fun b hb => ?_, fun y hy => ?_⟩
    · show σ.symm b = b
      exact σ.symm_apply_eq.2 (hσ1 b hb).symm
    · show ‖σ.symm y - y‖ < 1
      have e : σ.symm y - y = σ.symm (y - σ y) := by simp
      rw [e, norm_aut, norm_sub_rev]
      exact hσ2 y hy

theorem exists_fixed_near : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l), ∃ c₁ : ℕ, ∀ (k : ℕ) (x : Qbar l), ‖x‖ ≤ 1 →
  (∀ σ : Qbar l ≃ₐ[ℚ_[l]] Qbar l, (∀ b ∈ c.O, σ b = b) → (∀ y : Qbar l, ‖y‖ ≤ 1 → ‖σ y - y‖ < 1) → Cg k (σ x) x) →
  ∃ x' : Qbar l, ‖x'‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c x' ∧ Cg (k - c₁) x x' := by
  intro l _ c
  obtain ⟨C, -, hC⟩ := GlobalTheory.AxLemma.ax_lemma l
  have hl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
    rw [show ((l : ℕ) : Qbar l) = (((l : ℕ) : ℚ_[l]) : Qbar l) from (map_natCast _ _).symm,
      PadicAlgCl.norm_extends, Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt C hl1
  refine ⟨c₁, fun k x hx hfix => ?_⟩
  by_cases hk : k ≤ c₁
  · refine ⟨0, by simp, fun σ _ _ => map_zero σ, ?_⟩
    have h0 : k - c₁ = 0 := by omega
    simpa [Cg, h0] using hx
  · obtain ⟨y, hyH, hxy⟩ := hC (inertiaC c) x ‖((l : ℕ) : Qbar l) ^ k‖ (fun g hg => hfix g hg.1 hg.2)
    have hlpos : (0 : ℝ) < l := by linarith
    have key : C * ‖((l : ℕ) : Qbar l) ^ k‖ ≤ ‖((l : ℕ) : Qbar l) ^ (k - c₁)‖ := by
      rw [norm_pow, norm_pow, hl]
      have e : (l : ℝ)⁻¹ ^ k = (l : ℝ)⁻¹ ^ (k - c₁) * (l : ℝ)⁻¹ ^ c₁ := by
        rw [← pow_add]; congr 1; omega
      rw [e, mul_comm, mul_assoc]
      apply mul_le_of_le_one_right (by positivity)
      rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
      linarith
    have hxy' := hxy.trans key
    have hle1 : ‖((l : ℕ) : Qbar l) ^ (k - c₁)‖ ≤ 1 := by
      rw [norm_pow, hl]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hl1.le)
    refine ⟨y, ?_, fun σ h1 h2 => hyH σ ⟨h1, h2⟩, hxy'⟩
    have e : y = x + (y - x) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx ((norm_sub_rev y x).le.trans (hxy'.trans hle1)))

end GlobalTheory.PerFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralCoboundaryWildInertiaAwayFromLStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_coboundary_wildInertia_away_from_l : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) (q : Pl), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ z ∈ coc W c (Ine (F := ℚ) B), ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = mat W σ *ᵥ v - v := by
  first | exact @GlobalTheory.WildCob.main | exact GlobalTheory.WildCob.main | (intros; apply GlobalTheory.WildCob.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralLimitCompatibleModPrimePowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_limit_compatible_modPrimePow : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (X : Type) (a : ℕ → X → Qbar l), (∀ n x, a n x ∈ c.O) → (∀ n x, Cg n (a (n + 1) x) (a n x)) → ∃ z : X → Qbar l, (∀ x, z x ∈ c.O) ∧ ∀ n x, Cg n (z x) (a n x) := by
  first | exact @GlobalTheory.Ord2.exists_limit_coef | exact GlobalTheory.Ord2.exists_limit_coef | (intros; apply GlobalTheory.Ord2.exists_limit_coef <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulScalarClassEqSmulAddCoboundaryModPrimePStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_scalarClass_eq_smul_add_coboundary_modPrimePow : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → (∃ g, θ' g ≠ 1) → (∃ g, θ' g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∀ r : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 1 ≤ n → ∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → (∀ x y : c.O, (∀ s, ((l : ℕ) : c.O) ^ n ∣ x * a s - (((θ' s : c.Oˣ) : c.O) * y - y)) → ((l : ℕ) : c.O) ^ (n - r) ∣ x) → ∀ a' : ↥(Dec (F := ℚ) A) → c.O, Continuous a' → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a' (s * t) - (a' s + ((θ' s : c.Oˣ) : c.O) * a' t)) → ∃ x y : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ (m : c.O) * a' s - (x * a s + (((θ' s : c.Oˣ) : c.O) * y - y)) := by
  first | exact @GlobalTheory.LocCharSpan.span | exact GlobalTheory.LocCharSpan.span | (intros; apply GlobalTheory.LocCharSpan.span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FgInertiaCocyclesModCoboundariesCoefRingStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fg_inertiaCocycles_mod_coboundaries_coefRing : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) (P : Set (G ℚ Ω)) (γ : G ℚ Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ z ∈ coc W c I, ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ ∈ P, z σ = mat W σ *ᵥ v - v) → (∀ z ∈ coc W c I, (∀ σ ∈ P, z σ = 0) → z γ = 0 → ∀ s ∈ I, z s = 0) → ((coc W c I).map (cob W c I).mkQ).FG := by
  first | exact @GlobalTheory.InertCoh.fg_coc_mod_cob | exact GlobalTheory.InertCoh.fg_coc_mod_cob | (intros; apply GlobalTheory.InertCoh.fg_coc_mod_cob <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActCommGamma0CapGamma0LevelShimuraReciprocitStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b) = X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) := by
  first | exact @GlobalTheory.KZ.GammaZeroComm.galB_act_comm | exact GlobalTheory.KZ.GammaZeroComm.galB_act_comm | (intros; apply GlobalTheory.KZ.GammaZeroComm.galB_act_comm <;> assumption)
end

