import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SndDualLiftAlgebraMap
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.Laurent
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQDerivationCompletionZp
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.QDer

variable (p : ℕ) [Fact p.Prime]

abbrev qL : Lau p := HahnSeries.single (1 : ℤ) (1 : ℤ_[p])

def thetaFun (f : Lau p) : Lau p := qL p * Formalism.L2.Th1.A.dL f

theorem thetaFun_qL : thetaFun p (qL p) = qL p := by
  have h := Formalism.L2.Th1.A.dL_uPow (R := ℤ_[p]) 1
  simp only [Formalism.L2.Th1.A.uPow] at h
  simp [thetaFun, h, HahnSeries.single_zero_one]

theorem dL_algebraMap (r : ℤ_[p]) : Formalism.L2.Th1.A.dL (algebraMap ℤ_[p] (Lau p) r) = 0 :=
  (Formalism.L2.Th1.A.dLDR ℤ_[p]).map_algebraMap r

def thetaO :=
  letI : Module ℤ_[p] (Lau p) := Algebra.toModule
  GlobalTheory.BK.complDer (k := ℤ_[p]) (pI p)
    { toFun := thetaFun p
      map_add' := fun a b => by simp only [thetaFun, map_add, mul_add]
      map_smul' := fun r f => by
        simp only [thetaFun, Algebra.smul_def, RingHom.id_apply]
        rw [Formalism.L2.Th1.A.dL_mul, dL_algebraMap p r]
        ring
      map_one_eq_zero' := by
        show thetaFun p 1 = 0
        simp [thetaFun, Formalism.L2.Th1.A.dL_one]
      leibniz' := fun a b => by
        show thetaFun p (a * b) = a • thetaFun p b + b • thetaFun p a
        simp only [thetaFun, smul_eq_mul, Formalism.L2.Th1.A.dL_mul]
        ring }

theorem thetaO_qO : thetaO p (qO p) = qO p := by
  rw [thetaO, qO, GlobalTheory.BK.complDer_algebraMap]
  exact congrArg _ (thetaFun_qL p)

theorem thetaO_algebraMap (r : ℤ_[p]) : thetaO p (algebraMap ℤ_[p] (O0 p) r) = 0 :=
  (thetaO p).map_algebraMap r

def thetaZ : Derivation ℤ (O0 p) (O0 p) where
  toFun := thetaO p
  map_add' := map_add _
  map_smul' := fun r x => by
    simp [Algebra.smul_def, Derivation.leibniz]
  map_one_eq_zero' := (thetaO p).map_one_eq_zero
  leibniz' := (thetaO p).leibniz

theorem exists_qDer : ∀ (p : ℕ) [Fact p.Prime], ∃ D : Derivation ℤ (O0 p) (O0 p), D (qO p) = qO p ∧
    ∀ r : ℤ_[p], D (algebraMap ℤ_[p] (O0 p) r) = 0 := fun p _ =>
  ⟨thetaZ p, thetaO_qO p, thetaO_algebraMap p⟩

end GlobalTheory.K5.QDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionQDerivationModIntegralClosure
section
noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt.QDer

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem isDerOn_mono {B B' : Subalgebra A S} {D : S → M} (h : IsDerOn B D) (hle : B' ≤ B) :
    IsDerOn B' D :=
  ⟨fun x hx y hy => h.add x (hle hx) y (hle hy), fun x hx y hy => h.mul x (hle hx) y (hle hy),
    h.alg⟩

theorem isDerOn_sub {B : Subalgebra A S} {D₁ D₂ : S → M} (h₁ : IsDerOn B D₁) (h₂ : IsDerOn B D₂) :
    IsDerOn B (fun x => D₁ x - D₂ x) where
  add x hx y hy := by simp only [h₁.add x hx y hy, h₂.add x hx y hy]; abel
  mul x hx y hy := by simp only [h₁.mul x hx y hy, h₂.mul x hx y hy, smul_sub]; abel
  alg a := by simp [h₁.alg a, h₂.alg a]

theorem isDerOn_pow {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B)
    {n : ℕ} (hn : 1 ≤ n) : D (x ^ n) = ((n : S) * x ^ (n - 1)) • D x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, h.mul _ (pow_mem hx _) _ hx, ih (by omega), smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

end General

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_succ_pow (T : Tower p Ω) (m : ℕ) : zS T (m + 1) ^ p = zS T m :=
  Subtype.ext (by simp [zS, T.ζpow])

theorem qS_succ_pow (T : Tower p Ω) (m : ℕ) : qS T (m + 1) ^ p = qS T m :=
  Subtype.ext (by simp [qS, T.qpow])

theorem zS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem qS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

theorem levelAlg_le_succ (T : Tower p Ω) (m : ℕ) : levelAlg T m ≤ levelAlg T (m + 1) := by
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · rw [← zS_succ_pow]; exact pow_mem (zS_mem_levelAlg T _) _
  · rw [← qS_succ_pow]; exact pow_mem (qS_mem_levelAlg T _) _

theorem towerAlg_le_iSup (T : Tower p Ω) : towerAlg T ≤ ⨆ m, levelAlg T (m + 1) := by
  refine Algebra.adjoin_le ?_
  rintro x ((⟨m, rfl⟩ | ⟨m, rfl⟩))
  · exact le_iSup (fun k => levelAlg T (k + 1)) m (levelAlg_le_succ T m (zS_mem_levelAlg T m))
  · exact le_iSup (fun k => levelAlg T (k + 1)) m (levelAlg_le_succ T m (qS_mem_levelAlg T m))

theorem exists_level (hC : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) :
    ∃ D : integralClosure (O0 p) Ω → Frac p Ω, IsDerOn (levelAlg T n) D ∧ D (zS T n) = 0 ∧
      D (qS T n) = Submodule.Quotient.mk (T.qq n / (p : Ω) ^ n) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap hC.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  refine GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed p Ω hC T n hn (Frac p Ω) 0 _ (smul_zero _) ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p), ?_⟩
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  rw [Algebra.linearMap_apply, ← IsScalarTower.algebraMap_apply, Subalgebra.smul_def, smul_eq_mul]
  have key : (((p : integralClosure (O0 p) Ω) ^ n * qS T n ^ (p ^ n - 1) :
      integralClosure (O0 p) Ω) : Ω) = (p : Ω) ^ n * T.qq n ^ (p ^ n - 1) := by
    simp [qS]
  rw [key, ← GlobalTheory.AlmostEt.qq_pow T n]
  field_simp
  rw [pow_sub_one_mul hpn]

theorem smul_mk_eq (hC : IsClo p Ω) (T : Tower p Ω) (m : ℕ) :
    ((p : integralClosure (O0 p) Ω) * qS T (m + 1) ^ (p - 1)) •
        (Submodule.Quotient.mk (T.qq (m + 1) / (p : Ω) ^ (m + 1)) : Frac p Ω) =
      Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap hC.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpn : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  rw [Subalgebra.smul_def, smul_eq_mul]
  have key : (((p : integralClosure (O0 p) Ω) * qS T (m + 1) ^ (p - 1) :
      integralClosure (O0 p) Ω) : Ω) = (p : Ω) * T.qq (m + 1) ^ (p - 1) := by
    simp [qS]
  rw [key, ← T.qpow m, ← pow_sub_one_mul hpn (T.qq (m + 1)), pow_succ]
  field_simp

theorem exists_qDer (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (hC : IsClo p Ω) (T : Tower p Ω) :
    ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧
      ∀ m : ℕ, D (zS T m) = 0 ∧ D (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  choose Dl hDl hz hq using fun m : ℕ => exists_level hC T (m + 1) (by omega)

  have hz' : ∀ m, Dl m (zS T m) = 0 := fun m => by
    rw [← zS_succ_pow, isDerOn_pow (hDl m) (zS_mem_levelAlg T _) hp1, hz, smul_zero]
  have hq' : ∀ m, Dl m (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := fun m => by
    rw [← qS_succ_pow, isDerOn_pow (hDl m) (qS_mem_levelAlg T _) hp1, hq, smul_mk_eq hC T m]

  have hcomp : ∀ m, ∀ x ∈ levelAlg T (m + 1), Dl (m + 1) x = Dl m x := by
    intro m x hx
    have hE := isDerOn_sub (isDerOn_mono (hDl (m + 1)) (levelAlg_le_succ T (m + 1))) (hDl m)
    have hspan := GlobalTheory.T.derivationOn_adjoin_mem_span_image (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω) {zS T (m + 1), qS T (m + 1)}
      _ hE x hx
    have h1 : Dl (m + 1) (zS T (m + 1)) - Dl m (zS T (m + 1)) = 0 := by rw [hz' (m + 1), hz m, sub_zero]
    have h2 : Dl (m + 1) (qS T (m + 1)) - Dl m (qS T (m + 1)) = 0 := by rw [hq' (m + 1), hq m, sub_self]
    simp only [Set.image_insert_eq, Set.image_singleton, h1, h2, Set.insert_eq_of_mem,
      Set.mem_singleton_iff, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hspan
    exact sub_eq_zero.1 hspan
  have hmono : Monotone (fun m => levelAlg T (m + 1)) :=
    monotone_nat_of_le_succ fun m => levelAlg_le_succ T (m + 1)
  obtain ⟨D, hD, hag⟩ := GlobalTheory.T.exists_derivationOn_iSup_of_compatible (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
    (fun m => levelAlg T (m + 1)) hmono Dl hDl hcomp
  refine ⟨D, isDerOn_mono hD (towerAlg_le_iSup T), fun m => ⟨?_, ?_⟩⟩
  · rw [hag m _ (levelAlg_le_succ T m (zS_mem_levelAlg T m)), hz']
  · rw [hag m _ (levelAlg_le_succ T m (qS_mem_levelAlg T m)), hq']

end GlobalTheory.AlmostEt.QDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerUnionZetaDerivationModIntegralClosure
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.AlmostEt

section DerLemmas

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem IsDerOn.mono' {B C : Subalgebra A S} {D : S → M} (h : IsDerOn C D) (hBC : B ≤ C) :
    IsDerOn B D :=
  ⟨fun x hx y hy => h.add x (hBC hx) y (hBC hy), fun x hx y hy => h.mul x (hBC hx) y (hBC hy), h.alg⟩

theorem IsDerOn.pow_succ_der {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B)
    (k : ℕ) : D (x ^ (k + 1)) = (((k + 1 : ℕ) : S) * x ^ k) • D x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ' x (k + 1), h.mul x hx _ (pow_mem hx _), ih, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

theorem IsDerOn.eq_on_adjoin {s : Set S} {D₁ D₂ : S → M} (h₁ : IsDerOn (Algebra.adjoin A s) D₁)
    (h₂ : IsDerOn (Algebra.adjoin A s) D₂) (hs : ∀ x ∈ s, D₁ x = D₂ x) :
    ∀ x ∈ Algebra.adjoin A s, D₁ x = D₂ x := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap a => rw [h₁.alg, h₂.alg]
  | add x y hx hy ihx ihy => rw [h₁.add x hx y hy, h₂.add x hx y hy, ihx, ihy]
  | mul x y hx hy ihx ihy => rw [h₁.mul x hx y hy, h₂.mul x hx y hy, ihx, ihy]

end DerLemmas

section TowerDer

open GlobalTheory.K5 Polynomial

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_succ_pow_p (T : Tower p Ω) (m : ℕ) : zS T (m + 1) ^ p = zS T m :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact T.ζpow m)

theorem qS_succ_pow_p (T : Tower p Ω) (m : ℕ) : qS T (m + 1) ^ p = qS T m :=
  Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact T.qpow m)

theorem zS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert (zS T m) {qS T m})

theorem qS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ (Set.mem_singleton (qS T m)))

theorem zS_mem_levelAlg_succ (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T (m + 1) := by
  rw [← zS_succ_pow_p]; exact pow_mem (zS_mem_levelAlg T (m + 1)) _

theorem qS_mem_levelAlg_succ (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T (m + 1) := by
  rw [← qS_succ_pow_p]; exact pow_mem (qS_mem_levelAlg T (m + 1)) _

theorem levelAlg_le_succ (T : Tower p Ω) (m : ℕ) : levelAlg T m ≤ levelAlg T (m + 1) :=
  Algebra.adjoin_le (Set.insert_subset_iff.2 ⟨zS_mem_levelAlg_succ T m,
    Set.singleton_subset_iff.2 (qS_mem_levelAlg_succ T m)⟩)

theorem frac_smul_mk (s : integralClosure (O0 p) Ω) (x : Ω) :
    s • (Submodule.Quotient.mk x : Frac p Ω) = Submodule.Quotient.mk ((s : Ω) * x) := by
  rw [← Submodule.Quotient.mk_smul]; rfl

theorem frac_mk_eq_zero (s : integralClosure (O0 p) Ω) :
    (Submodule.Quotient.mk (s : Ω) : Frac p Ω) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨s, rfl⟩

theorem cyc_relation (hc : CharZero Ω) (T : Tower p Ω) (m : ℕ) :
    (Polynomial.aeval (zS T (m + 1)) (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)))) •
      (Submodule.Quotient.mk (T.ζ (m + 1) * p / (p : Ω) ^ (m + 1)) : Frac p Ω) = 0 := by
  set z := zS T (m + 1)
  set ζ := T.ζ (m + 1)
  have hp1 : 1 < p := hp.out.one_lt
  have hpos : 0 < p ^ (m + 1) := pow_pos hp.out.pos _
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero

  have hξ : IsPrimitiveRoot (ζ ^ p ^ m) p := by
    have := (T.prim (m + 1)).pow_of_dvd (pow_ne_zero m hp.out.ne_zero) (pow_dvd_pow p (Nat.le_succ m))
    simpa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hp.out.pos m)] using this

  set gS : integralClosure (O0 p) Ω := ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (z ^ p ^ m) ^ j
  have hgval : (gS : Ω) = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range i, (ζ ^ p ^ m) ^ j := by
    simp [gS, z, ζ, zS]
  have hg : (gS : Ω) * (ζ ^ p ^ m - 1) = - p := by
    rw [hgval, Finset.sum_mul]
    simp_rw [geom_sum_mul]
    rw [Finset.sum_sub_distrib, hξ.geom_sum_eq_zero hp1]
    simp

  have hroot : Polynomial.aeval ζ (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (T.prim (m + 1)).isRoot_cyclotomic hpos
  have hid := congrArg (fun f => Polynomial.aeval ζ (Polynomial.derivative f))
    (cyclotomic_prime_pow_mul_X_pow_sub_one (O0 p) p m)
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, map_add, map_mul,
    map_sub, hroot, zero_mul, add_zero, sub_zero] at hid
  have hzval : (Polynomial.aeval z (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p))) : Ω)
      = Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p))) := by
    exact (Polynomial.aeval_algHom_apply (integralClosure (O0 p) Ω).val z _).symm
  rw [frac_smul_mk, hzval]
  set F := Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic (p ^ (m + 1)) (O0 p)))
  have hζ1 : ζ ^ p ^ (m + 1) = 1 := (T.prim (m + 1)).pow_eq_one
  have hF : F * (ζ ^ p ^ m - 1) * ζ = (p : Ω) ^ (m + 1) := by
    have h2 : F * (ζ ^ p ^ m - 1) = (p : Ω) ^ (m + 1) * ζ ^ (p ^ (m + 1) - 1) := by
      simpa [map_natCast] using hid
    rw [h2, mul_assoc, pow_sub_one_mul (pow_ne_zero _ hp.out.ne_zero), hζ1, mul_one]
  have hξ1 : ζ ^ p ^ m - 1 ≠ 0 := sub_ne_zero.2 (hξ.ne_one hp1)
  have key : F * (ζ * p / (p : Ω) ^ (m + 1)) = ((-gS : integralClosure (O0 p) Ω) : Ω) := by
    apply mul_right_cancel₀ hξ1
    push_cast
    rw [neg_mul, hg, neg_neg]
    have hpm : (p : Ω) ^ (m + 1) ≠ 0 := pow_ne_zero _ hp0
    rw [div_eq_mul_inv]
    linear_combination ((p : Ω) * ((p : Ω) ^ (m + 1))⁻¹) * hF + (p : Ω) * mul_inv_cancel₀ hpm
  rw [key, frac_mk_eq_zero]

end TowerDer

end GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

open GlobalTheory.K5

theorem IsDerOn.pow_der {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B) {n : ℕ}
    (hn : 0 < n) : D (x ^ n) = ((n : S) * x ^ (n - 1)) • D x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using h.pow_succ_der hx k

theorem zeta_derivation : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω,
      IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧
        D (qS T m) = 0 := by
  intro p hp Ω _ _ hc T
  haveI : CharZero Ω := GlobalTheory.K5.Basic.charZero_of_isClo hc
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hlev : ∀ m : ℕ, ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω,
      IsDerOn (levelAlg T (m + 1)) D ∧
        D (zS T (m + 1)) = Submodule.Quotient.mk (T.ζ (m + 1) * p / (p : Ω) ^ (m + 1)) ∧
        D (qS T (m + 1)) = 0 := fun m =>
    GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed p Ω hc T (m + 1) (Nat.succ_pos m) (Frac p Ω) _ 0
      (cyc_relation inferInstance T m) (smul_zero _)
  choose D hD hDz hDq using hlev
  have hval : ∀ m, D m (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧
      D m (qS T m) = 0 := by
    intro m
    constructor
    · rw [← zS_succ_pow_p, (hD m).pow_der (zS_mem_levelAlg T (m + 1)) hp.out.pos, hDz m, frac_smul_mk]
      congr 1
      have hc1 : ((zS T (m + 1) : integralClosure (O0 p) Ω) : Ω) = T.ζ (m + 1) := rfl
      push_cast
      rw [hc1, ← T.ζpow m, ← pow_sub_one_mul hp.out.ne_zero (T.ζ (m + 1))]
      field_simp
      ring
    · rw [← qS_succ_pow_p, (hD m).pow_der (qS_mem_levelAlg T (m + 1)) hp.out.pos, hDq m, smul_zero]
  have hcompat : ∀ m, ∀ x ∈ levelAlg T (m + 1), D (m + 1) x = D m x := by
    intro m
    refine IsDerOn.eq_on_adjoin (s := {zS T (m + 1), qS T (m + 1)})
      ((hD (m + 1)).mono' (levelAlg_le_succ T (m + 1))) (hD m) ?_
    rintro x (rfl | hx)
    · rw [(hval (m + 1)).1, hDz m]
    · rw [Set.mem_singleton_iff.1 hx, (hval (m + 1)).2, hDq m]
  have hmono : Monotone (fun m => levelAlg T (m + 1)) :=
    monotone_nat_of_le_succ fun m => levelAlg_le_succ T (m + 1)
  obtain ⟨D', hD', hD'eq⟩ := isDerOn_iSup_glue (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
    (fun m => levelAlg T (m + 1)) hmono D hD hcompat
  have hle : towerAlg T ≤ ⨆ m, levelAlg T (m + 1) := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨m, rfl⟩ | ⟨m, rfl⟩)
    · exact (le_iSup (fun m => levelAlg T (m + 1)) m) (zS_mem_levelAlg_succ T m)
    · exact (le_iSup (fun m => levelAlg T (m + 1)) m) (qS_mem_levelAlg_succ T m)
  refine ⟨D', hD'.mono' hle, fun m => ⟨?_, ?_⟩⟩
  · rw [hD'eq m _ (zS_mem_levelAlg_succ T m), (hval m).1]
  · rw [hD'eq m _ (qS_mem_levelAlg_succ T m), (hval m).2]

end GlobalTheory.AlmostEt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpNormProductLeOne
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
namespace GlobalTheory.EisM

theorem locineq_log_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i j, ‖z i * conj (z j) * T‖ < 1) :
    T * ‖∑ i, z i‖ ^ 2 ≤ - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖ := by
  have hs : ∀ i j, HasSum (fun n : ℕ => (z i * conj (z j) * T) ^ n / n)
      (-Complex.log (1 - z i * conj (z j) * T)) := fun i j =>
    Complex.hasSum_taylorSeries_neg_log (h i j)
  have H := hasSum_sum (s := Finset.univ) (fun i _ => hasSum_sum (s := Finset.univ) (fun j _ => hs i j))
  have H2 := ((Complex.hasSum_iff _ _).mp H).1
  have hterm : ∀ n : ℕ, (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ)).re
      = T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n := by
    intro n
    have e : (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ))
        = (((T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n : ℝ)) : ℂ) := by
      have e1 : ∀ i j, (z i * conj (z j) * T) ^ n / (n : ℂ)
          = z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n) := by
        intro i j; rw [map_pow]; ring
      simp_rw [e1]
      have e2 : ∑ i, ∑ j, z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n)
          = (∑ i, z i ^ n) * conj (∑ j, z j ^ n) * ((T : ℂ) ^ n / n) := by
        rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
        simp_rw [Finset.sum_mul]
      rw [e2, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [e, Complex.ofReal_re]
  have hre : (∑ i, ∑ j, -Complex.log (1 - z i * conj (z j) * T)).re
      = - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖ := by
    simp [Complex.re_sum, Complex.log_re]
  rw [hre] at H2
  simp_rw [hterm] at H2
  have := le_hasSum H2 1 (fun n _ => by positivity)
  simpa using this

theorem locineq_exp_prod {ι : Type*} [Fintype ι] (z : ι → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i j, ‖z i * conj (z j) * T‖ < 1) :
    Real.exp (‖∑ i, z i‖ ^ 2 * T) * ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖ ≤ 1 := by
  have hpos : ∀ i j, 0 < ‖1 - z i * conj (z j) * T‖ := by
    intro i j
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun e => ?_)
    have := h i j
    rw [← e, norm_one] at this
    exact lt_irrefl _ this
  have hP : ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖
      = Real.exp (∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_log (hpos i j)).symm
  rw [hP, ← Real.exp_add, Real.exp_le_one_iff]
  have := locineq_log_sum z T hT h
  linarith

theorem locineq : ∀ (x y : ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 →
    Real.exp (‖1 + x + y‖ ^ 2 * T) * ((1 - T) * ‖(1 - x * T) * (1 - y * T)‖ ^ 2 *
      ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2)) ≤ 1 := by
  intro x y T hT0 hT1 hx hy
  have hxT : ‖x‖ * T < 1 := by
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg x, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg x) (norm_nonneg x))]
  have hyT : ‖y‖ * T < 1 := by
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg y) (norm_nonneg y))]
  have hxy : ‖x‖ * ‖y‖ * T < 1 := by
    nlinarith [mul_nonneg (sq_nonneg (‖x‖ - ‖y‖)) hT0]
  let z : Fin 3 → ℂ := ![1, x, y]
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_of_nonneg hT0]
  have h : ∀ i j, ‖z i * conj (z j) * T‖ < 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [z, hnT, Complex.norm_conj, abs_of_nonneg hT0] <;> nlinarith
  have key := locineq_exp_prod z T hT0 h
  have c1 : ‖1 - conj x * T‖ = ‖1 - x * T‖ := by
    rw [← Complex.norm_conj (1 - x * T)]; simp
  have c2 : ‖1 - conj y * T‖ = ‖1 - y * T‖ := by
    rw [← Complex.norm_conj (1 - y * T)]; simp
  have c3 : ‖1 - y * conj x * T‖ = ‖1 - x * conj y * T‖ := by
    rw [← Complex.norm_conj (1 - x * conj y * T)]; simp; ring_nf
  have d0 : ‖1 - (T : ℂ)‖ = 1 - T := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have dx : ‖1 - x * conj x * T‖ = 1 - ‖x‖ ^ 2 * T := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have dy : ‖1 - y * conj y * T‖ = 1 - ‖y‖ ^ 2 * T := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  simp only [z, Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_one, one_mul, mul_one] at key
  rw [c1, c2, c3, d0, dx, dy] at key
  rw [norm_mul]
  calc _ = Real.exp (‖1 + x + y‖ ^ 2 * T) * ((1 - T) * ‖1 - x * T‖ * ‖1 - y * T‖ *
        (‖1 - x * T‖ * (1 - ‖x‖ ^ 2 * T) * ‖1 - x * conj y * T‖) *
        (‖1 - y * T‖ * ‖1 - x * conj y * T‖ * (1 - ‖y‖ ^ 2 * T))) := by ring
    _ ≤ 1 := key

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassNotRootsAvoidLeStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_not_rootsAvoid_le' : ∀ (g : ℕ) [Fact g.Prime], ∀ (N q d : ℕ) (c : (ZMod g)ˣ), (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → (mass g N fun f => ¬ RootsAvoid g c f) ≤ 1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1) := by
  first | exact @GlobalTheory.BadShare.mass_not_rootsAvoid_le | exact GlobalTheory.BadShare.mass_not_rootsAvoid_le | (intros; apply GlobalTheory.BadShare.mass_not_rootsAvoid_le <;> assumption)
end

