import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0450
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0449
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRootOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneReductionFrobeniusPullbackEqShift
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicValNatFactorialBound
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_eq_l_mul_of_natCast {A : Type} [CommRing A] (htf : ∀ x : A, (l : A) * x = 0 → x = 0)
    {m k : ℕ} (hm : m ≠ 0) (hv : padicValNat l m < padicValNat l k) {y z : A}
    (h : (m : A) * y = (k : A) * z) : ∃ w, y = l * w := by
  have hp := hl.out
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hv
  have htf' : ∀ (j : ℕ) (x : A), (l : A) ^ j * x = 0 → x = 0 := fun j => by
    induction j with
    | zero => simp
    | succ j ih => exact fun x hx => htf x (ih _ (by linear_combination hx))
  rw [← Nat.factorization_def m hp, ← Nat.factorization_def k hp] at hv
  have hm' := Nat.ordProj_mul_ordCompl_eq_self m l
  have hk' := Nat.ordProj_mul_ordCompl_eq_self k l
  have hcop := Nat.coprime_ordCompl hp hm
  generalize m / l ^ m.factorization l = m' at hm' hcop
  generalize k / l ^ k.factorization l = k' at hk'
  generalize m.factorization l = a at hm' hv
  generalize k.factorization l = b at hk' hv
  subst hm' hk'
  push_cast at h
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have huv' : (u : A) * l + (v : A) * m' = 1 := by
    have := congrArg (Int.cast : ℤ → A) huv
    push_cast at this
    exact this
  have e : (l : A) ^ b = (l : A) ^ a * ((l : A) ^ (b - a - 1) * l) := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  have h1 : (m' : A) * y = (l : A) ^ (b - a - 1) * l * k' * z := by
    apply sub_eq_zero.1
    apply htf' a
    rw [e] at h
    linear_combination h
  exact ⟨u * y + v * (l : A) ^ (b - a - 1) * k' * z, by linear_combination (-y) * huv' + (v : A) * h1⟩

theorem cong_add {A : Type} [CommRing A] (φ : A →+* A) {a b : A} (ha : ∃ w, φ a = a ^ l + (l : A) * w)
    (hb : ∃ w, φ b = b ^ l + (l : A) * w) : ∃ w, φ (a + b) = (a + b) ^ l + (l : A) * w := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨w', hw'⟩ := hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out a b
  exact ⟨w + w' - a * b * r, by rw [map_add, hw, hw', hr]; ring⟩

theorem cong_mul {A : Type} [CommRing A] (φ : A →+* A) {a b : A} (ha : ∃ w, φ a = a ^ l + (l : A) * w)
    (hb : ∃ w, φ b = b ^ l + (l : A) * w) : ∃ w, φ (a * b) = (a * b) ^ l + (l : A) * w := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨w', hw'⟩ := hb
  exact ⟨a ^ l * w' + w * b ^ l + (l : A) * w * w', by rw [map_mul, hw, hw']; ring⟩

theorem frobC_ainfToAcris (b : Ainf l) :
    frobC l (ainfToAcris l b) = ainfToAcris l (WittVector.frobenius b) := by
  rw [← GlobalTheory.RingBasics.φA_apply]
  exact (GlobalTheory.CrisMaps.phiA_extends l).alg b

theorem cong_ainf (b : Ainf l) :
    ∃ w, frobC l (ainfToAcris l b) = ainfToAcris l b ^ l + (l : Per.Acris l) * w := by
  obtain ⟨c, hc⟩ := frobenius_eq_pow_add b
  exact ⟨ainfToAcris l c, by rw [frobC_ainfToAcris, hc, map_add, map_pow, map_mul, map_natCast]⟩

theorem frob_mem_of_theta {x : Ainf l} (hx : Per.θ l x = 0) :
    ∃ u, ainfToAcris l (WittVector.frobenius x) = (l : Per.Acris l) * u := by
  obtain ⟨c, hc⟩ := frobenius_eq_pow_add x
  obtain ⟨d, hd⟩ := exists_dpow hx l
  have hf : (l.factorial : Per.Acris l) = (l : Per.Acris l) * ((l - 1).factorial : Per.Acris l) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hl.out.ne_zero]
  refine ⟨((l - 1).factorial : Per.Acris l) * d + ainfToAcris l c, ?_⟩
  rw [hc, map_add, map_pow, ← hd, map_mul, map_natCast, hf]
  ring

theorem padicValNat_factorial_bound {n : ℕ} (hn : n ≠ 0) :
    l * padicValNat l n.factorial < padicValNat l n.factorial + n := by
  have h := sub_one_mul_padicValNat_factorial (p := l) n
  have hlast := Nat.getLast_digit_ne_zero l hn
  have hpos : 0 < (l.digits n).sum :=
    lt_of_lt_of_le (Nat.pos_of_ne_zero hlast) (List.le_sum_of_mem (List.getLast_mem _))
  have h2 : 2 ≤ l := hl.out.two_le
  generalize padicValNat l n.factorial = v at h ⊢
  generalize (l.digits n).sum = s at h hpos
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  have e : (k + 1) * v = k * v + v := by ring
  rw [e]
  generalize k * v = t at h ⊢
  omega

theorem cong_gen {x : Ainf l} (hx : Per.θ l x = 0) {n : ℕ} {Y : Per.Acris l}
    (hY : (n.factorial : Per.Acris l) * Y = ainfToAcris l x ^ n) :
    ∃ w, frobC l Y = Y ^ l + (l : Per.Acris l) * w := by
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Y = 1 := by simpa using hY
    exact ⟨0, by rw [this]; simp⟩
  obtain ⟨u, hu⟩ := frob_mem_of_theta hx
  obtain ⟨w1, hw1⟩ : ∃ w, frobC l Y = (l : Per.Acris l) * w := by
    have h1 := congrArg (frobC l) hY
    rw [map_mul, map_natCast, map_pow, frobC_ainfToAcris, hu, mul_pow] at h1
    refine exists_eq_l_mul_of_natCast htf (Nat.factorial_ne_zero n) (k := l ^ n) (z := u ^ n) ?_ ?_
    · rw [padicValNat.prime_pow]
      exact padicValNat_factorial_lt_of_ne_zero l hn.ne'
    · rw [h1]; push_cast; rfl
  obtain ⟨w2, hw2⟩ : ∃ w, Y ^ l = (l : Per.Acris l) * w := by
    obtain ⟨d, hd⟩ := exists_dpow hx (l * n)
    have h2 : ((n.factorial ^ l : ℕ) : Per.Acris l) * Y ^ l = ((l * n).factorial : ℕ) * d := by
      rw [hd, Nat.cast_pow, ← mul_pow, hY, ← pow_mul, mul_comm n l]
    refine exists_eq_l_mul_of_natCast htf (pow_ne_zero _ (Nat.factorial_ne_zero n)) ?_ h2
    rw [padicValNat.pow n.factorial l, padicValNat_factorial_mul]
    exact padicValNat_factorial_bound hn.ne'
  exact ⟨w1 - w2, by rw [hw1, hw2]; ring⟩

theorem cong_acris0 : ∀ (s : Per.AinfP l) (hs : s ∈ Per.Acris0 l),
    ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) ⟨s, hs⟩) =
      (algebraMap (Per.Acris0 l) (Per.Acris l) ⟨s, hs⟩) ^ l + (l : Per.Acris l) * w := by
  intro s hs
  let S : Subalgebra (Per.Ainf l) (Per.Acris0 l) :=
    { carrier := {t | ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) t) =
        (algebraMap (Per.Acris0 l) (Per.Acris l) t) ^ l + (l : Per.Acris l) * w}
      mul_mem' := fun {x y} hx hy => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (x * y)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (x * y)) ^ l + (l : Per.Acris l) * w
        rw [map_mul]
        exact cong_mul (frobC l).toRingHom hx hy
      add_mem' := fun {x y} hx hy => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (x + y)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (x + y)) ^ l + (l : Per.Acris l) * w
        rw [map_add]
        exact cong_add (frobC l).toRingHom hx hy
      algebraMap_mem' := fun r => by
        change ∃ w, frobC l (algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) r)) =
          (algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) r)) ^ l +
            (l : Per.Acris l) * w
        rw [← GlobalTheory.RingIface.tower]
        exact cong_ainf r }
  have hle : Per.Acris0 l ≤ S.map (Per.Acris0 l).val := by
    refine GlobalTheory.RingIface.acris0_le_3 l _ fun x hx n y hy hn => ?_
    refine Subalgebra.mem_map.2 ⟨⟨y, hy⟩, ?_, rfl⟩
    refine cong_gen hx (n := n) ?_
    have h1 : ((n.factorial : ℕ) : Per.Acris0 l) * ⟨y, hy⟩ =
        algebraMap (Per.Ainf l) (Per.Acris0 l) x ^ n := Subtype.ext (by simpa using hn)
    have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) h1
    rw [map_mul, map_natCast, map_pow, ← GlobalTheory.RingIface.tower] at h2
    exact h2
  obtain ⟨t, ht, e⟩ := Subalgebra.mem_map.1 (hle hs)
  have e' : (⟨s, hs⟩ : Per.Acris0 l) = t := Subtype.ext e.symm
  rw [e']
  exact ht

theorem frobC_cong (y : Per.Acris l) : ∃ w, frobC l y = y ^ l + (l : Per.Acris l) * w := by
  obtain ⟨s, z, rfl⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 y 1
  obtain ⟨w, hw⟩ := cong_acris0 s.1 s.2
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (algebraMap (Per.Acris0 l) (Per.Acris l) s + (l : Per.Acris l) ^ 1 * z)
    (algebraMap (Per.Acris0 l) (Per.Acris l) s) l
  refine ⟨w + frobC l z - z * c, ?_⟩
  rw [map_add, map_mul, map_pow, map_natCast, hw]
  linear_combination -hc

end GlobalTheory.AcrisPrism

namespace GlobalTheory.AcrisPrism

variable (l : ℕ) [hl : Fact l.Prime]

def acrisDelta : Delta l (Per.Acris l) :=
  Delta.ofLift l (frobC l).toRingHom (GlobalTheory.MemLoc.acris_basic l).2.1 fun a => frobC_cong a

theorem isUnit_delta_l : IsUnit ((acrisDelta l).δ (l : Per.Acris l)) := by
  have h := (acrisDelta l).φ_eq (l : Per.Acris l)
  have h1 : (acrisDelta l).φ (l : Per.Acris l) = l := map_natCast _ _
  rw [h1] at h
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  have e : (l : Per.Acris l) ^ l = (l : Per.Acris l) ^ 2 * (l : Per.Acris l) ^ (l - 2) := by
    rw [← pow_add]
    congr 1
    have := hl.out.two_le
    omega
  have h2 : (acrisDelta l).δ (l : Per.Acris l) = (l : Per.Acris l) * (-(l : Per.Acris l) ^ (l - 2)) + 1 := by
    apply sub_eq_zero.1
    apply htf
    linear_combination -h - e
  haveI := (GlobalTheory.MemLoc.acris_basic l).1
  rw [h2]
  exact Ideal.mem_jacobson_bot.1
    (IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self (l : Per.Acris l))) _

theorem l_mem_nonZeroDivisors : (l : Per.Acris l) ∈ nonZeroDivisors (Per.Acris l) := by
  have htf := (GlobalTheory.MemLoc.acris_basic l).2.1
  exact mem_nonZeroDivisors_iff.2 ⟨htf, fun x hx => htf x (by rw [mul_comm, hx])⟩

def ainfPhiToAcris : Ainf l →+* Per.Acris l := (ainfToAcris l).toRingHom.comp WittVector.frobenius

theorem ainfPhiToAcris_le (F : FinExt l) :
    (ainfObj F).I ≤ (Ideal.span {(l : Per.Acris l)}).comap (ainfPhiToAcris l) := by
  intro a ha
  have hx : Per.θ l a = 0 := RingHom.mem_ker.1 ha
  obtain ⟨u, hu⟩ := frob_mem_of_theta hx
  exact Ideal.mem_span_singleton'.2 ⟨u, by rw [mul_comm]; exact hu.symm⟩

def acrisObj (F : FinExt l) : Obj l ↥(OL F) :=
  Obj.ofDistinguished hl.out.pos (acrisDelta l) (l : Per.Acris l) (l_mem_nonZeroDivisors l)
    (isUnit_delta_l l) (by rw [sup_idem]; exact (GlobalTheory.MemLoc.acris_basic l).1)
    ⟨1, fun x _ => by
      have : ((l : ℕ) : Per.Acris l ⧸ Ideal.span {(l : Per.Acris l)}) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_span_singleton_self _
      simp [this]⟩
    ((Ideal.quotientMap (I := RingHom.ker (Per.θ l)) (Ideal.span {(l : Per.Acris l)}) (ainfPhiToAcris l) (ainfPhiToAcris_le l F)).comp
      (ainfObj F).str)

def acrisHom (F : FinExt l) : Hom (ainfObj F) (acrisObj l F) where
  f := ainfPhiToAcris l
  f_δ := Delta.map_δ_of_map_φ (ainfObj F).D (acrisDelta l) (GlobalTheory.MemLoc.acris_basic l).2.1 _
    fun a => (frobC_ainfToAcris (WittVector.frobenius a)).symm
  f_I := fun a ha => ainfPhiToAcris_le l F ha
  f_str := fun r a h => by
    change Ideal.Quotient.mk _ (ainfPhiToAcris l a) =
      Ideal.quotientMap (I := RingHom.ker (Per.θ l)) (Ideal.span {(l : Per.Acris l)}) (ainfPhiToAcris l)
        (ainfPhiToAcris_le l F) ((ainfObj F).str r)
    rw [← h]
    rfl

theorem main : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ (C : Obj l ↥(OL F)) (eC : C.A ≃+* Per.Acris l) (h : GlobalTheory.Prism.Hom (ainfObj F) C), C.I = Ideal.span {(l : C.A)} ∧ (∀ x, eC (C.D.φ x) = frobC l (eC x)) ∧ ∀ x : Ainf l, eC (h.f x) = ainfToAcris l (WittVector.frobenius x) :=
  fun l _ F => ⟨acrisObj l F, RingEquiv.refl _, acrisHom l F, rfl, fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.AcrisPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiSTmul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.HodgeAt

variable {l : ℕ} [Fact l.Prime]

def emb (P : LocPrime l) (σ : GQ l) (L : FinExt l) : ↥L.1 →ₐ[ℚ_[l]] P.R.BdR :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp (σ.toAlgHom.comp L.1.val)

def phiS (P : LocPrime l) (σ : GQ l) (L : FinExt l) : ↥L.1 ⊗[ℚ_[l]] P.R.BdR →ₐ[ℚ_[l]] P.R.BdR :=
  Algebra.TensorProduct.lift (emb P σ L) (AlgHom.id ℚ_[l] P.R.BdR) (fun _ _ => Commute.all _ _)

def PhiS (P : LocPrime l) (σ : GQ l) (L : FinExt l) (a : ℕ) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    Fin a → P.R.BdR :=
  fun i => phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1) x)

variable (P : LocPrime l) (σ : GQ l) (L : FinExt l) (a : ℕ)

theorem emb_apply (c : ↥L.1) : emb P σ L c = algebraMap (Om l) P.R.BdR (σ (c : Om l)) := rfl

theorem phiS_tmul (c : ↥L.1) (b : P.R.BdR) :
    phiS P σ L (c ⊗ₜ b) = algebraMap (Om l) P.R.BdR (σ (c : Om l)) * b := by
  simp [phiS, emb]

theorem PhiS_tmul (v : Fin a → ↥L.1) (b : P.R.BdR) :
    PhiS P σ L a (v ⊗ₜ b) = fun i => algebraMap (Om l) P.R.BdR (σ (v i : Om l)) * b := by
  funext i
  simp [PhiS, phiS_tmul]

theorem PhiS_add (x y : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (x + y) = PhiS P σ L a x + PhiS P σ L a y := by
  funext i
  simp [PhiS]

theorem PhiS_zero : PhiS P σ L a 0 = 0 := by
  funext i
  simp [PhiS]

theorem PhiS_sum {ι : Type} (s : Finset ι) (x : ι → (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (∑ i ∈ s, x i) = ∑ i ∈ s, PhiS P σ L a (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [PhiS_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, PhiS_add, ih]

theorem PhiS_sm (r : ↥L.1 ⊗[ℚ_[l]] P.R.BdR) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) r x) = fun i => phiS P σ L r * PhiS P σ L a x i := by
  funext i
  simp only [PhiS]
  rw [GlobalTheory.DRFil.ext_sm, GlobalTheory.DRFil.sm_self, map_mul]

theorem PhiS_mulR (b : P.R.BdR) (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) :
    PhiS P σ L a (GlobalTheory.DRFil.mulR ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) b x) = fun i => b * PhiS P σ L a x i := by
  rw [← GlobalTheory.DRFil.sm_one_tmul, PhiS_sm, phiS_tmul]
  funext i
  simp

end GlobalTheory.HodgeAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiWInclLEPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKReal

theorem phiW_inclL_E_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (Y : Matrix ι ι (OA l O)), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) → ∀ c : ι → OA l O, inclO l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • phiW t ϖ P (inclL t ϖ P c) = inclL t ϖ P (Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α Y hY c
  set s0 : OW l O := inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) with hs0

  have key : Y.map (inclO l O) = s0 ^ α • frobMat t ϖ P := by
    ext i j
    obtain ⟨f, hf, hYij⟩ := hY i j
    rw [Matrix.map_apply, hYij, ← ϖ.iW_of_mem t K, Matrix.smul_apply, smul_eq_mul, hs0, ← ϖ.iTot_E t K,
      ← ϖ.iW_of_mem t K, ← map_pow, frobMat, Matrix.map_apply, Matrix.of_apply, ← map_mul]
    congr 1
    funext τ
    apply Subtype.ext
    simp only [Pi.mul_apply, Pi.pow_apply, Subalgebra.coe_mul, Subalgebra.coe_pow, hf τ]
    rfl
  have key2 : (Y.map (frobOA l O)).map (inclO l O) =
      inclO l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) ^ α • (frobMat t ϖ P).map (frobOW l O) := by
    have h1 : (Y.map (frobOA l O)).map (inclO l O) = (Y.map (inclO l O)).map (frobOW l O) := by
      ext i j; simp only [Matrix.map_apply, frobOW_inclO]
    rw [h1, key]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hs0, frobOW_inclO]
  rw [inclL_apply, phiW_apply, inclL_apply]
  have h2 : (fun i => frobOW l O ((frobMat t ϖ P *ᵥ fun i => inclO l O (c i)) i)) =
      (frobMat t ϖ P).map (frobOW l O) *ᵥ fun i => inclO l O (frobOA l O (c i)) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, frobOW_inclO]
  have h3 : (fun i => inclO l O ((Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i)) i)) =
      (Y.map (frobOA l O)).map (inclO l O) *ᵥ fun i => inclO l O (frobOA l O (c i)) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [h2, h3, key2, Matrix.smul_mulVec, Matrix.mulVec_smul]

end GlobalTheory.BKReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointConditionsOfPointGaloisRepFamiliesStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointConditions_of_pointGaloisRepFamilies : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → ∀ (i : D.nd.Loc), ∀ π ∈ D.nd.Z i, IsRhoOf D.nd i π (ρ i π) ∧ IsSSRep (rhoChiK D i (ρ i π)) ∧ EmbeddingTypes.ambBlock i (r i) (ρ i) π ∧ TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (r i) (ρ i) π := by
  first | exact @GlobalTheory.PointConditions.main | exact GlobalTheory.PointConditions.main | (intros; apply GlobalTheory.PointConditions.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupRealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_real : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e : ℕ) (v : ℝ), 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M v, σ ^ p ∈ upperRamificationGroup F ↥M (min (2 * v) (v + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_real | exact GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_real | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_real <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescentStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_cover_injective_and_descent : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C), Cover h → Function.Injective h.f ∧ ∀ (D : Obj l R) (p q : Hom C D), IsPO h h p q → ∀ c, p.f c = q.f c → c ∈ h.f.range := by
  first | exact @GlobalTheory.BSP.cover_injective_and_descent | exact GlobalTheory.BSP.cover_injective_and_descent | (intros; apply GlobalTheory.BSP.cover_injective_and_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_hom_map_ideal_eq : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B'), B.I.map f.f = B'.I := by
  first | exact @GlobalTheory.Prism.Rigid.map_I_eq | exact GlobalTheory.Prism.Rigid.map_I_eq | (intros; apply GlobalTheory.Prism.Rigid.map_I_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticEnvelopeRelationTriangularStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticEnvelopeRelation_triangular : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A) (d p : A), (l : A) ∈ J → d ∈ J → IsUnit (D.δ d) → ∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ envRel D d p i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A) := by
  first | exact @GlobalTheory.EnvShape.envRel_triangular | exact GlobalTheory.EnvShape.envRel_triangular | (intros; apply GlobalTheory.EnvShape.envRel_triangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiUnitOnRescaleUniformizerOfQVal
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

noncomputable section

namespace GlobalTheory.TauTwist

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out

theorem psiUnitOn_rescale_of_qVal : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V) (ϖ : T.V), Irreducible ϖ → ∀ (y : D.X) (n : ℤ), QVal D ϖ y n → ∀ q : D.X → (FractionRing T.V)ˣ, (q y : FractionRing T.V) = algebraMap T.V (FractionRing T.V) ϖ ^ (-n) → PsiUnitOn (GlobalTheory.TauTwist.rescale D q) y Set.univ := by
  intro T D ϖ hϖ y n hQ q hq j V hV hU hc h
  obtain ⟨e, -, c, ⟨u, hu⟩, hC⟩ := genHasVal_units _ _ _ _ _ _ hQ
  obtain ⟨C, hCv, hCt⟩ := hC j
  have hW : V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c y).left) j :=
    fun x hx => Set.mem_iInter.2 fun k => by cases k; exact hc hx
  have hπ : algebraMap T.V (FractionRing T.V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).mpr hϖ.ne_zero
  have hqc : (q y : FractionRing T.V) * c = algebraMap T.V (FractionRing T.V) (u : T.V) := by
    rw [hq, hu, ← _root_.mul_assoc, ← zpow_add₀ hπ, neg_add_cancel, zpow_zero, _root_.one_mul]
  have hconst : (res (X := Spec (CommRingCat.of (FractionRing T.V)))
      (le_top : LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j ≤ ⊤) (unitOn (q y))).val * C.val =
      (res (X := Spec (CommRingCat.of (FractionRing T.V))) le_top
        (unitOn (Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom u))).val := by
    rw [hCv]
    show ((Spec (CommRingCat.of (FractionRing T.V))).presheaf.map (homOfLE le_top).op).hom _ *
      ((Spec (CommRingCat.of (FractionRing T.V))).presheaf.map (homOfLE le_top).op).hom _ =
      ((Spec (CommRingCat.of (FractionRing T.V))).presheaf.map (homOfLE le_top).op).hom _
    rw [← map_mul]
    congr 1
    simp only [scal, unitOn, Units.coe_map, MonoidHom.coe_coe, Scheme.Hom.id_appTop]
    change (Scheme.ΓSpecIso (CommRingCat.of (FractionRing T.V))).inv.hom (q y : FractionRing T.V) *
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing T.V))).inv.hom c =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing T.V))).inv.hom (algebraMap T.V (FractionRing T.V) (u : T.V))
    rw [← map_mul, hqc]
  refine ⟨(res (le_top : V ≤ ⊤) (unitOn u)).val * (res hW (e.s j)).val, (Units.isUnit _).mul (Units.isUnit _), ?_⟩
  have hval : (((rescale D q).psi y).s j).val = (res (X := Spec (CommRingCat.of (FractionRing T.V)))
      (le_top : LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j ≤ ⊤)
        (unitOn (Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom u))).val *
      (res (wchart_le_preimage D.P.L (jK T.V) (fun _ => (D.c y).left) (fun _ => ptK (D.c y))
        (fun _ => QForm.ptK_eq D y) j) (pullU (jK T.V) _ (e.s j))).val := by
    show (HMul.hMul (α := (Γ(Spec (CommRingCat.of (FractionRing T.V)), LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j))ˣ)
      (β := (Γ(Spec (CommRingCat.of (FractionRing T.V)), LB.wchart D.P.L (K := PUnit) (fun _ => ptK (D.c y)) j))ˣ)
      (res le_top (unitOn (q y))) ((D.psi y).s j)).val = _
    rw [hCt, ← _root_.mul_assoc, Units.val_mul, Units.val_mul, hconst]
  rw [hval]
  refine fn_ext fun x hx => ?_
  refine (gs_pull (𝟙 _) (jK T.V) x V hx _).trans (Eq.trans ?_ (gs_res (𝟙 _) x h hx _).symm)
  rw [gs_mul (𝟙 _ ≫ jK T.V) x V hx]
  refine Eq.trans (congrArg₂ (· * ·) ?_ ?_) (gs_mul (𝟙 _) x _ (h hx) _ _).symm
  · refine (gs_res _ x le_top hx _).trans (Eq.trans ?_ (gs_res _ x le_top (h hx) _).symm)
    exact (unitAt_val (𝟙 _ ≫ jK T.V) x u).symm.trans ((congrArg Units.val
      (unitAt_spMap (𝟙 _) (algebraMap T.V (FractionRing T.V)) x u)).trans (unitAt_val _ x _))
  · refine (gs_res _ x hW hx _).trans (Eq.trans ?_ (gs_res _ x _ (h hx) _).symm)
    exact (gs_pull (𝟙 _) (jK T.V) x _ (hW hx) _).symm

end GlobalTheory.TauTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneReductionFrobeniusPullbackEqShiftStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankOne_reduction_frobeniusPullback_eq_shift : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ N : Lats k S.n A.m, (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → ∀ a : ZMod S.n → ℤ, A.m = 1 → (∀ i, U i = {a i}) → ∀ i, pull ((F.D A).φ i) (N (i - 1)) = sh (a i) (N i) := by
  first | exact @GlobalTheory.RankOneReduction.pull_eq_sh | exact GlobalTheory.RankOneReduction.pull_eq_sh | (intros; apply GlobalTheory.RankOneReduction.pull_eq_sh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualBoundOfComponentsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_bound_of_components : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), (∀ i, StepAB X i) → (∀ i, ChooseH bkP i) → (∀ i s, GalHyp bkP i s → ResBound bkP i s) → ResidualBoundOddPrimes bkP := by
  first | exact @GlobalTheory.ResSel.OddBound.residual_bound_of_parts | exact GlobalTheory.ResSel.OddBound.residual_bound_of_parts | (intros; apply GlobalTheory.ResSel.OddBound.residual_bound_of_parts <;> assumption)
end

