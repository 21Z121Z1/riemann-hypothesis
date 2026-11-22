import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryAdelicSupportedAtBadPrimePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0479
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryFiniteAdelicPointAsMatrixMemFlagIwahori
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0328
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0476
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPDivOfUnit

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.OnePrime

section Local

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem exists_bound {m : ℕ} (A : Matrix (Fin m) (Fin m) K) :
    ∃ k : ℕ, ∀ r s, Valued.v (A r s) ≤ WithZero.exp (k : ℤ) := by
  first
  | exact @_root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp
  | exact _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp
  | (apply _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntriesExpBound.exists_entries_le_exp ..)

theorem mul_bound {m : ℕ} {A C : Matrix (Fin m) (Fin m) K} {a c : WithZero (Multiplicative ℤ)}
    (hA : ∀ r s, Valued.v (A r s) ≤ a) (hC : ∀ r s, Valued.v (C r s) ≤ c) (r s : Fin m) :
    Valued.v ((A * C) r s) ≤ a * c := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hA r j) (hC j s)

end Local

theorem exists_root_rat (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (m n N : ℕ) (hn : 0 < n)
    (q : P.adicCompletion E) (hq : Valued.v q = WithZero.exp (-1 : ℤ)) (G₁ G₂ : GL (Fin m) (P.adicCompletion E)) :
    ∃ (M : GL (Fin m) (P.adicCompletion E)) (γ : GL (Fin m) E),
      (∀ r s, Valued.v (M.1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      (∀ r s, Valued.v ((M ^ n).1 r s - (1 : Matrix (Fin m) (Fin m) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))) ∧
      G₁ * M ^ n * G₂ = Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ := by
  haveI : CharZero (P.adicCompletion E) := algebraRat.charZero _
  have hc : Valued.v (q ^ (N + 1)) = WithZero.exp (-((N : ℤ) + 1)) := by
    rw [map_pow, hq, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hn1 : Valued.v (n : P.adicCompletion E) ≤ 1 := by
    clear hn
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ]
      exact Valuation.map_add_le _ ih (by simp)
  have hcN : Valued.v (q ^ (N + 1)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [hc]
    exact WithZero.exp_le_exp.2 (by omega)
  have hε : Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1)) ≠ 0 := by
    rw [map_mul, hc]
    refine mul_ne_zero ?_ WithZero.exp_ne_zero
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨k₁, hk₁⟩ := exists_bound G₂.1
  obtain ⟨k₂, hk₂⟩ := exists_bound (G₂⁻¹).1
  set e := WithZero.log (Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1))) with he
  obtain ⟨γ, hγ⟩ := GlobalTheory.DenseGL.dense_two_sided E P m (k₁ + k₂ + (-e).toNat) (G₁ * G₂)
  let γ' : GL (Fin m) (P.adicCompletion E) := Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ
  have hγ' : γ'.1 = γ.1.map (algebraMap E (P.adicCompletion E)) := rfl
  let B₀ : GL (Fin m) (P.adicCompletion E) := G₁⁻¹ * γ' * G₂⁻¹
  have hB : B₀.1 - 1 = G₂.1 * (((G₁ * G₂)⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) * (G₂⁻¹).1 := by
    rw [← hγ', mul_sub, _root_.sub_mul, mul_one, Units.mul_inv, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
    congr 2
    simp only [B₀]
    group
  have hB2 : ∀ r s, Valued.v ((B₀.1 - 1) r s) ≤ Valued.v ((n : P.adicCompletion E) ^ 2 * q ^ (N + 1)) := fun r s => by
    rw [hB]
    refine (mul_bound (mul_bound hk₁ fun r s => (hγ r s).1) hk₂ r s).trans ?_
    rw [← WithZero.exp_log hε, ← he, ← WithZero.exp_add, ← WithZero.exp_add]
    refine WithZero.exp_le_exp.2 ?_
    push_cast
    omega
  obtain ⟨M, hM1, hM2⟩ := GlobalTheory.MatNthRoot.exists_nthRoot E P m n (q ^ (N + 1)) B₀.1 hn
    (by rw [hc, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)) hB2
  have hu : IsUnit M := (isUnit_pow_iff hn.ne').1 (hM2 ▸ B₀.isUnit)
  obtain ⟨M, rfl⟩ := hu
  have hM3 : M ^ n = B₀ := Units.ext (by rw [Units.val_pow_eq_pow_val, hM2])
  refine ⟨M, γ, fun r s => (hM1 r s).trans ?_, fun r s => ?_, ?_⟩
  · rw [map_mul]
    exact (mul_le_of_le_one_left' hn1).trans hcN
  · rw [hM3]
    refine (hB2 r s).trans ?_
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_left' (pow_le_one' hn1 2)).trans hcN
  · rw [hM3]
    show _ = γ'
    simp only [B₀]
    group

set_option maxHeartbeats 2000000 in

theorem exists_level_elt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (T i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) T (I.rec7 l Z).R.f bad), ChiFin I l Z S → ∀ (P : SBof I a), P.1 ∈ I.Q a → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ (N : ℕ) (g₁ g₂ : GA B (B.R.N i)), ∃ z : S.U, S.chi z = 1 ∧ (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') z.1 = 1) ∧ GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z.1 ∧ ∃ γ : GL (Fin (B.R.N i)) B.fields.E, ∀ r s, adAt B.host.F P.1 (((g₁ * (show GA B (B.R.N i) from z.1) * g₂ : GA B (B.R.N i)) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) (AfE B.host.F B.host.E)) r s) = algebraMap B.fields.E (P.1.adicCompletion B.fields.E) ((γ : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.fields.E) r s) := by
  intro B X I hI hPin l Z a T i hi bad S hS P hP v hv N g₁ g₂
  obtain ⟨n, hn, hchi⟩ := hS
  obtain ⟨N₀, hN₀⟩ := GlobalTheory.Mem.Col2.AdT.Opn.level_contains_deep I hI hPin l Z a T i hi bad S P v hv
  have hd := fun N z => GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hI l Z a ((I.rec7 l Z).R.N i) N P z
  obtain ⟨hs, hq, -⟩ := hd 0 1
  let φ : AfE B.host.F B.host.E →+* P.1.adicCompletion B.fields.E := adAt B.host.F P.1
  obtain ⟨M, γ, hM1, hM2, hM3⟩ := exists_root_rat B.fields.E P.1 (B.R.N i) n (N + N₀) hn _ hq
    (Matrix.GeneralLinearGroup.map φ g₁) (Matrix.GeneralLinearGroup.map φ g₂)
  obtain ⟨w, hwU, hwv, hwP⟩ := GlobalTheory.Mem.Col2.AdLift.exists_lift I hI hPin l Z a i hi P v hv M
  have hw : w ∈ S.U := hN₀ w hwU hwv (((hd N₀ w).2.2).2 fun r s => by
    rw [hwP]
    exact (hM1 r s).trans (WithZero.exp_le_exp.2 (by omega)))
  let w' : GA B (B.R.N i) := w
  have hw' : Matrix.GeneralLinearGroup.map φ w' = M := Units.ext (Matrix.ext hwP)
  have hz : Matrix.GeneralLinearGroup.map φ (w' ^ n) = M ^ n := by rw [map_pow, hw']
  have hz' : ∀ r s, φ ((w' ^ n).1 r s) = (M ^ n).1 r s := fun r s =>
    congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) hz
  have hbad : v ∉ badG (I.rec7 l Z) := by
    have key : ∀ j : Fin 2, (((B.primes X).g j : ℕ) : 𝓞 B.fields.E) ∉ P.1.asIdeal := fun j =>
      GlobalTheory.Proof.NarrowJetMoments.notMem_of_mem_QE hI.sel_ok hP ((base_fields_primes_ok B X).2.1.g_prime j) (hI.g_mem j)
    rw [hs] at hv
    have key2 : ∀ j : Fin 2, (((B.primes X).g j : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal := fun j h => by
      rw [hv, Ideal.mem_comap, map_natCast] at h
      exact key j h
    rintro (h | h)
    · exact key2 0 h
    · exact key2 1 h
  refine ⟨⟨w, hw⟩ ^ n, ?_, fun v' hv' => ?_, ((hd N _).2.2).2 fun r s => ?_, γ, fun r s => ?_⟩
  · rw [map_pow]
    exact hchi ⟨w, hw⟩ fun v' hv' => hwv v' fun e => hbad (e ▸ hv')
  · show bc (prV (E := (I.rec7 l Z).host.E) v') (w ^ n) = 1
    rw [map_pow, hwv v' hv', one_pow]
  · have e := hz' r s
    have h2 := hM2 r s
    rw [← e] at h2
    exact h2.trans (WithZero.exp_le_exp.2 (by omega))
  · have e : Matrix.GeneralLinearGroup.map φ (g₁ * w' ^ n * g₂) =
        Matrix.GeneralLinearGroup.map φ g₁ * M ^ n * Matrix.GeneralLinearGroup.map φ g₂ := by
      rw [map_mul, map_mul, hz]
    exact congrArg (fun g : GL (Fin (B.R.N i)) (P.1.adicCompletion B.fields.E) => g.1 r s) (e.trans hM3)

end GlobalTheory.Mem.Col2.AdT.OnePrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMiddleStepLevelInverseLiftsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_middleStep_level_inverse_lifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g z, MidAt I hi b P g z ∧ LiftsInv I κ P g := by
  first | exact @GlobalTheory.Mem.Col2.AdT.exists_midAt_liftsInv | exact GlobalTheory.Mem.Col2.AdT.exists_midAt_liftsInv | (intros; apply GlobalTheory.Mem.Col2.AdT.exists_midAt_liftsInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatSmulMem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PrincLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_nat_mul_mem (c : E) : ∃ m : ℕ, 0 < m ∧ (m : E) * c ∈ intOE E := by
  obtain ⟨y, hy, hint'⟩ := exists_integral_multiples ℤ ℚ ({c} : Finset E)
  have hint := hint' c (Finset.mem_singleton_self c)
  have key : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : E) * c) := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
    · refine ⟨n, by rintro rfl; simp at hy, ?_⟩
      have e : ((n : E) * c) = ((n : ℤ) • c) := by rw [zsmul_eq_mul]; push_cast; ring
      rw [e]; exact hint
    · refine ⟨n, by rintro rfl; simp at hy, ?_⟩
      have e : ((n : E) * c) = -((-(n : ℤ)) • c) := by rw [zsmul_eq_mul]; push_cast; ring
      rw [e]; exact hint.neg
  obtain ⟨n, hn, h2⟩ := key
  refine ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).1 h2
  exact ⟨a, ha⟩

theorem exists_nat_smul_mem {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E))
    (hsp : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (w : Fin r → E) :
    ∃ k : ℕ, 0 < k ∧ (k : E) • w ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegralExists.main
  | exact _root_.GlobalTheory.NatMulIntegralExists.main
  | (apply _root_.GlobalTheory.NatMulIntegralExists.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegralExists.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegralExists.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegralExists.main ..)

theorem exists_nat_den {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG) :
    ∃ d : ℕ, 0 < d ∧ ∀ w ∈ Λ, ∀ i, (d : E) * w i ∈ intOE E := by
  classical
  obtain ⟨s, rfl⟩ := hfg
  choose m hm hmem using fun (p : (Fin r → E) × Fin r) => exists_nat_mul_mem (E := E) (p.1 p.2)
  refine ⟨∏ p ∈ s ×ˢ Finset.univ, m p, Finset.prod_pos fun p _ => hm p, ?_⟩
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    intro i
    obtain ⟨k, hk⟩ : m (x, i) ∣ ∏ p ∈ s ×ˢ Finset.univ, m p :=
      Finset.dvd_prod_of_mem _ (Finset.mem_product.2 ⟨hx, Finset.mem_univ _⟩)
    have e : ((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * x i = (k : E) * ((m (x, i) : E) * x i) := by
      rw [hk]; push_cast; ring
    rw [e]
    exact mul_mem (natCast_mem _ k) (hmem (x, i))
  | zero => intro i; simp
  | add x y _ _ hx hy =>
    intro i
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    have e : ((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * (a • x) i =
        algebraMap (𝓞 E) E a * (((∏ p ∈ s ×ˢ Finset.univ, m p : ℕ) : E) * x i) := by
      rw [Pi.smul_apply, Algebra.smul_def]; ring
    rw [e]
    exact mul_mem ⟨a, rfl⟩ (hx i)

theorem den_locL (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) {d : ℕ}
    (hd : ∀ w ∈ Λ, ∀ i, (d : E) * w i ∈ intOE E) {y : Fin r → E ⊗[F] v.adicCompletion F}
    (hy : y ∈ Formalism.L2.Herm.locL v Λ) :
    ∀ i, (d : E ⊗[F] v.adicCompletion F) * y i ∈ intV E v := by
  unfold Formalism.L2.Herm.locL latS at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    intro i
    have e : (d : E ⊗[F] v.adicCompletion F) * inclE (F := F) (v.adicCompletion F) (w i) =
        inclE (F := F) (v.adicCompletion F) ((d : E) * w i) := by
      rw [map_mul, map_natCast]
    rw [e]
    exact Subring.subset_closure (Or.inl ⟨⟨_, hd w hw i⟩, rfl⟩)
  | zero => intro i; simp
  | add x y _ _ hx hy =>
    intro i
    rw [Pi.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem a.2 (hx i)

theorem princ_lat : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {r : ℕ} (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ d : ℕ, 0 < d ∧ ∀ (M : ℕ) (x : Matrix (Fin r) (Fin r) (E ⊗[F] v.adicCompletion F)), (∀ y ∈ Formalism.L2.Herm.locL v Λ, ∃ z ∈ Formalism.L2.Herm.locL v Λ, x *ᵥ y - y = ((M * d : ℕ) : E ⊗[F] v.adicCompletion F) • z) → ∀ a b, ∃ c ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring, (x - 1) a b = (M : E ⊗[F] v.adicCompletion F) * c := by
  intro F E _ _ _ _ _ r v Λ hfg hsp
  classical
  choose k hk hkmem using fun b : Fin r => exists_nat_smul_mem Λ hsp (Pi.single b 1)
  obtain ⟨d₂, hd₂, hden⟩ := exists_nat_den Λ hfg
  have hd₁ : 0 < ∏ b, k b := Finset.prod_pos fun b _ => hk b
  have hmem : ∀ b, ((∏ b, k b : ℕ) : E) • (Pi.single b 1 : Fin r → E) ∈ Λ := fun b => by
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ b)
    have e : ((∏ b, k b : ℕ) : E) • (Pi.single b 1 : Fin r → E) = t • ((k b : E) • (Pi.single b 1 : Fin r → E)) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, ht, Nat.cast_mul, mul_comm]
    rw [e]
    exact Λ.toAddSubmonoid.nsmul_mem (hkmem b) t
  refine ⟨(∏ b, k b) * d₂, Nat.mul_pos hd₁ hd₂, fun M x hx a b => ?_⟩
  set d₁ := ∏ b, k b with hd₁def
  let y : Fin r → E ⊗[F] v.adicCompletion F :=
    fun i => inclE (F := F) (v.adicCompletion F) (((d₁ : E) • (Pi.single b 1 : Fin r → E)) i)
  have hy : y ∈ Formalism.L2.Herm.locL v Λ := Submodule.subset_span ⟨_, hmem b, rfl⟩
  obtain ⟨z, hz, hxz⟩ := hx y hy
  have hy' : y = (d₁ : E ⊗[F] v.adicCompletion F) • (Pi.single b 1 : Fin r → E ⊗[F] v.adicCompletion F) := by
    funext i
    simp only [y, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
    by_cases h : i = b
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hcol : x *ᵥ y - y = (d₁ : E ⊗[F] v.adicCompletion F) • ((x - 1) *ᵥ Pi.single b 1) := by
    rw [hy', Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub]
  have h1 := congrFun hxz a
  rw [hcol, Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_single_one, Matrix.col_apply, smul_eq_mul,
    smul_eq_mul] at h1
  have hu : IsUnit (d₁ : E ⊗[F] v.adicCompletion F) := by
    have := (IsUnit.mk0 (d₁ : F) (Nat.cast_ne_zero.2 hd₁.ne')).map (algebraMap F (E ⊗[F] v.adicCompletion F))
    rwa [map_natCast] at this
  refine ⟨(d₂ : E ⊗[F] v.adicCompletion F) * z a, den_locL v Λ hden hz a, ?_⟩
  apply hu.mul_left_cancel
  rw [h1]
  push_cast
  ring

end GlobalTheory.PrincLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincLocStep
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.Opn

theorem exists_princ_loc_step : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n T f : ℕ} {J : Matrix (Fin n) (Fin n) E} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)), J = 1 → ∃ M : ℕ, 0 < M ∧ ∀ y ∈ UPts σ J (v.adicCompletion F), (∀ a b, ∃ c ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring, ((y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) a b = (M : E ⊗[F] v.adicCompletion F) * c) → y ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n T f J bad S v hJ
  subst hJ
  obtain ⟨M, hM, hMU⟩ := GlobalTheory.Mem.Col2.AdT.Opn.exists_princ σ S.U S.U_open
  refine ⟨M, Nat.pos_of_ne_zero hM, fun y hy hc => ?_⟩
  choose C hC hyC using hc
  have hz := Formalism.UG.P.afsplitU_mem v σ 1 y 1 hy (one_mem _)
  have hzU : Formalism.UG.P.afsplitU v y 1 ∈ S.U := by
    refine hMU _ hz fun a b => ?_
    have hyab : (y : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b + M • C a b := by
      rw [nsmul_eq_mul, ← hyC a b, Matrix.sub_apply, add_sub_cancel]
    have e : (((Formalism.UG.P.afsplitU v y 1 : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b =
        (M : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * Formalism.UG.P.afsplitIE v (C a b) := by
      rw [Matrix.sub_apply, Formalism.UG.P.afsplitU_coe, Formalism.UG.P.afsplitC_apply, Units.val_one, hyab, map_add, map_nsmul,
        nsmul_eq_mul]
      by_cases hab : a = b
      · subst hab
        simp only [Matrix.one_apply_eq, Formalism.UG.P.afsplitEps]
        ring
      · simp [Matrix.one_apply_ne hab]
    rw [e, ← mul_assoc, ← map_natCast (Formalism.L2.Col.iA F E), ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one, one_mul]
    exact Formalism.UG.P.afsplit_IE_int v _ (hC a b)
  have h := ((S.U_eq _).1 hzU).2 v
  rwa [Formalism.UG.P.afsplit_right1] at h

end GlobalTheory.Mem.Col2.AdT.Opn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRationalUnitaryEquivRowStageCompatStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_unitary_equiv_rowStage_compat : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok →
    ∀ (e : Formalism.L2.Col.UAd X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* Bridge.Gf X.toD7.sp.X'),
    (∀ x, RowAd.ptE X (e x) = x.1) →
    ∃ eΓ : Formalism.L2.Col.URat X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ≃* GQ X.toD7.sp.X',
      (∀ γ, Bridge.ratF X.toD7.sp.X' (eΓ γ) = e (Formalism.L2.Col.ratIn X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) γ)) ∧
      ∀ γ, ∃ γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E, Bridge.IsRatMat X.toD7.sp.X' (eΓ γ) γE ∧
        MatEq γE γ.1 := by
  first | exact @GlobalTheory.Mem.R3.RowStdRat.stdRat_equiv | exact GlobalTheory.Mem.R3.RowStdRat.stdRat_equiv | (intros; apply GlobalTheory.Mem.R3.RowStdRat.stdRat_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceClassMatchingCouplingCoset
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw.Match

theorem mem_image_units {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) (y : GL (Fin n) κ) (w : Fin n → κ) :
    w ∈ (fun v => y.1 *ᵥ v) '' C ↔ (y⁻¹).1 *ᵥ w ∈ C := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · intro h
    refine ⟨_, h, ?_⟩
    show y.1 *ᵥ ((y⁻¹).1 *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem conj_mem_setStab_image {κ : Type} [CommRing κ] {n : ℕ} (C : Set (Fin n → κ)) (y h : GL (Fin n) κ) :
    y * h * y⁻¹ ∈ MemChart.setStab ((fun v => y.1 *ᵥ v) '' C) ↔ h ∈ MemChart.setStab C := by
  have e1 : ∀ w : Fin n → κ, (y⁻¹).1 *ᵥ ((y * h * y⁻¹).1 *ᵥ w) = h.1 *ᵥ ((y⁻¹).1 *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, show y⁻¹ * (y * h * y⁻¹) = h * y⁻¹ by group, Units.val_mul, ← Matrix.mulVec_mulVec]
  have e2 : ∀ v : Fin n → κ, (y⁻¹).1 *ᵥ (y.1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  show (∀ w, (y * h * y⁻¹).1 *ᵥ w ∈ (fun v => y.1 *ᵥ v) '' C ↔ w ∈ (fun v => y.1 *ᵥ v) '' C) ↔ ∀ v, h.1 *ᵥ v ∈ C ↔ v ∈ C
  simp only [mem_image_units, e1]
  constructor
  · intro H v
    have := H (y.1 *ᵥ v)
    rwa [e2] at this
  · intro H w
    exact H _

set_option maxHeartbeats 1000000 in

theorem coset_match : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ (c : (I.stp u a i).Cl) (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i), ∃ c0 : (I.stp u I.mu0 i).Cl, c0.1 = b0 ∧
      ∃ y : GLG B.fields.E (B.R.N i) (B.primes X).vGs, y ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp ∧
      ∀ (κ : (I.stp u a i).G c.1) (κ0 : (I.stp u I.mu0 i).G c0.1), (I.stp u a i).gam c.1 κ = 1 → (I.stp u I.mu0 i).gam c0.1 κ0 = 1 →
        κ.2.2 = 1 → (i + 1 = B.R.m → ∀ w, κ0.2.1.1 w = y w * κ.2.1.1 w * (y w)⁻¹) →
        (cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ↔
          cosetIn ((I.stp u I.mu0 i).act c0.1 κ0 ((I.stp u I.mu0 i).rep c0)) = cosetIn ((I.stp u I.mu0 i).rep c0)) := by
  intro B X I hI l u a i h1 hm c b0
  classical
  haveI : NeZero (B.R.N i) := ⟨(B.R.N_pos i).ne'⟩
  by_cases hl : i + 1 = B.R.m
  · have hq : ∀ w ∈ (B.primes X).vGs, ((qOf w : ℕ) : 𝓞 B.fields.E) ∉ w.asIdeal ^ 2 :=
      fun _ hw => GlobalTheory.TopStep.qOf_notMem_sq (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr hw
    set r : PtAt B.R I.sel (I.tup a) (I.cst a) u i := (I.stp u a i).rep c with hr
    obtain ⟨y, hy, hy0, hY⟩ := ChEx.ptAt_cosetG r hl
    have hGs : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P => by
      rcases Finset.mem_union.1 P.2 with h | h
      · exact h
      · have h' : P.1 ∈ I.Q I.mu0 := h
        rw [I.twistPrimes_reference_tuple_eq_empty] at h'
        exact absurd h' (Finset.notMem_empty _)
    let Y0 : Set (Sp B.fields.E (B.R.N i)) := {z | z - y ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) r.1.1.deco.1.N
        (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ))}
    have hY0 : Y0 ∈ (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) i).ys
        (extTo (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K)) r.1.1).deco.1.N := by
      rw [ysAt_ys_of_eq _ _ _ hl]
      refine ⟨y, (mem_locLat _ _ _ _).2 fun P => ?_, rfl⟩
      rw [if_pos (hGs P), _root_.zpow_neg_one, inv_inv]
      exact hy P.1 (hGs P)
    let q0 : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i := ⟨(extTo _ r.1.1, Y0), hY0⟩
    have hbar : MemChart.bar q0 = MemChart.bar r := by
      funext w
      have hy' : ∀ w ∈ (B.primes X).vGs, ((qOf w : ℕ) : B.fields.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q0.1.1.deco.1.N := hy
      have hy0' : y ∈ q0.1.2 := by
        change y - y ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) r.1.1.deco.1.N
          (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ))
        rw [sub_self]
        exact zero_mem _
      have hY' : ∀ z ∈ q0.1.2, ∀ w ∈ (B.primes X).vGs, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal q0.1.1.deco.1.N := by
        intro z hz w hw
        have h2 := (mem_locLat _ _ _ _).1 hz ⟨w, Finset.mem_union_left _ hw⟩
        exact (by simpa [hw] using h2 : z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal r.1.1.deco.1.N)
      rw [ChEx.bar_eqG q0 hy' hy0' hY' w, ChEx.bar_eqG r hy hy0 hY w]
      rfl
    refine ⟨(I.stp u I.mu0 i).cl b0 q0, rfl, ?_⟩
    obtain ⟨g0, hg0⟩ := (I.stp u I.mu0 i).exists_mv b0 q0
    refine ⟨(g0.2.1.1)⁻¹, inv_mem g0.2.1.2, ?_⟩
    intro κ κ0 _ _ hθ hκ
    have hκ' := hκ hl
    set r0 : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i := (I.stp u I.mu0 i).rep ((I.stp u I.mu0 i).cl b0 q0) with hr0
    have hb0 : ∀ w, MemChart.bar q0 w = (fun v => (g0.2.1.1 w).1 *ᵥ v) '' MemChart.bar r0 w := by
      intro w
      have e : MemChart.ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) g0 r0 = q0 := hg0
      have h3 := MemChart.bar_ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) g0 r0 w
      rw [e] at h3
      exact h3
    have hb0' : ∀ w, MemChart.bar r0 w = (fun v => (((g0.2.1.1)⁻¹ : GLG B.fields.E (B.R.N i) (B.primes X).vGs) w).1 *ᵥ v) '' MemChart.bar r w := by
      intro w
      have e : ∀ v, ((g0.2.1.1 w)⁻¹).1 *ᵥ ((g0.2.1.1 w).1 *ᵥ v) = v := fun v => by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [← hbar, hb0 w, Set.image_image]
      show MemChart.bar r0 w = (fun v => ((g0.2.1.1 w)⁻¹).1 *ᵥ ((g0.2.1.1 w).1 *ᵥ v)) '' MemChart.bar r0 w
      simp only [e, Set.image_id']
    have hL : cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ↔
        ∀ w, κ.2.1.1 w ∈ MemChart.setStab (MemChart.bar r w) := by
      show cosetIn (MemChart.ya (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
          (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) κ r) = cosetIn r ↔ _
      rw [ChEx.cosetIn_eq_iff_bar_cq (ChEx.q_disj I hI a) hq, MemChart.bar_ya_eq_iff]
      have hcq : ChEx.cqOf (MemChart.ya (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1)
          (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) i c.1) κ r) = ChEx.cqOf r := by
        funext P
        rw [ChEx.invActs_cqOf (ChEx.q_disj I hI a) _ _ κ r P, hθ]
        ext v
        simp
      rw [hcq]
      simp
    have hR : cosetIn ((I.stp u I.mu0 i).act ((I.stp u I.mu0 i).cl b0 q0).1 κ0 r0) = cosetIn r0 ↔
        ∀ w, κ0.2.1.1 w ∈ MemChart.setStab (MemChart.bar r0 w) := by
      show cosetIn (MemChart.ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) κ0 r0) = cosetIn r0 ↔ _
      rw [ChEx.cosetIn_eq_iff_bar_cq (ChEx.q_disj I hI I.mu0) hq, MemChart.bar_ya_eq_iff]
      have hcq : ChEx.cqOf (MemChart.ya (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0)
          (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0) κ0 r0) = ChEx.cqOf r0 := by
        funext P
        have h' : P.1 ∈ I.Q I.mu0 := P.2
        rw [I.twistPrimes_reference_tuple_eq_empty] at h'
        exact absurd h' (Finset.notMem_empty _)
      rw [hcq]
      simp
    rw [hL, hR]
    refine forall_congr' fun w => ?_
    rw [hκ' w, hb0' w]
    exact (conj_mem_setStab_image _ _ _).symm
  · let q0 : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i :=
      ⟨(DecoF.base _ _ _ _ _, ∅), by rw [ysAt_ys_of_ne I.sel (I.tup I.mu0) (I.cst I.mu0) hl]; rfl⟩
    refine ⟨(I.stp u I.mu0 i).cl b0 q0, rfl, 1, one_mem _, fun κ κ0 _ _ _ _ => ?_⟩
    exact iff_of_true (ChEx.cos_of_neT I hl _ _) (ChEx.cos_of_neT I hl _ _)

end GlobalTheory.Mem.Col2.TC.ChTw.Match
end
end

