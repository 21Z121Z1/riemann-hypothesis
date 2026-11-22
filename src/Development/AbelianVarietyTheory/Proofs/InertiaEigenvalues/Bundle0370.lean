import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0365
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0097
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0347

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisDiscRingHomExtOfAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_disc_ringHom_ext_of_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (γ γ' : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = γ' (algebraMap (Ainf l) (Per.Acris l) a)) → (∀ x, ‖γ x‖ ≤ 1) → (∀ x, ‖γ' x‖ ≤ 1) → γ = γ' := by
  first | exact @GlobalTheory.AcrisDiscExt.acris_disc_ext | exact GlobalTheory.AcrisDiscExt.acris_disc_ext | (intros; apply GlobalTheory.AcrisDiscExt.acris_disc_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisMulEqZeroStatement
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l), x * y = 0 → x = 0 ∨ y = 0 := by
  first | exact @GlobalTheory.PMon.Gauss.acris_mul_eq_zero | exact GlobalTheory.PMon.Gauss.acris_mul_eq_zero | (intros; apply GlobalTheory.PMon.Gauss.acris_mul_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusProperties
section
attribute [local irreducible] Formalism.Per.σC Formalism.Per.σO Formalism.Per.φA Formalism.Per.zA Formalism.Per.AinfP Formalism.Per.zP Formalism.Per.toC Formalism.Per.θP Formalism.Per.kerP Formalism.Per.ev Formalism.Per.FilP Formalism.Per.θD Formalism.Per.pD Formalism.Per.zD Formalism.Per.FilD Formalism.Per.Acris0 Formalism.Per.Acris Formalism.Per.Bcris Formalism.Per.aB Formalism.Per.a0B Formalism.Per.zB Formalism.Per.φB Formalism.Per.σF Formalism.Per.σA Formalism.Per.extP Formalism.Per.σDp Formalism.Per.σD Formalism.Per.σB Formalism.Per.IsLog

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisFrobE

open scoped Nat

theorem pow_mul_factorial_dvd (l : ℕ) (hl : 0 < l) : ∀ n : ℕ, l ^ n * n ! ∣ (l * n)!
  | 0 => by simp
  | n + 1 => by
    have ih := pow_mul_factorial_dvd l hl n
    have e : l * (n + 1) = (l * n + (l - 1)) + 1 := by rw [Nat.mul_succ]; omega
    have h2 : (l * n)! ∣ (l * n + (l - 1))! := Nat.factorial_dvd_factorial (by omega)
    have e2 : l ^ (n + 1) * (n + 1)! = (l * n + (l - 1) + 1) * (l ^ n * n !) := by
      rw [← e, Nat.factorial_succ, pow_succ]; ring
    rw [e2, e, Nat.factorial_succ]
    exact Nat.mul_dvd_mul_left _ (ih.trans h2)

theorem pow_succ_dvd_factorial (l : ℕ) (hl : 0 < l) : l ^ (l + 1) ∣ (l * l)! := by
  refine dvd_trans ?_ (pow_mul_factorial_dvd l hl l)
  rw [pow_succ]
  exact Nat.mul_dvd_mul_left _ (Nat.dvd_factorial hl le_rfl)

variable (l : ℕ) [Fact l.Prime]

theorem isUnit_natCast_ainfP (n : ℕ) (hn : n ≠ 0) : IsUnit (n : Formalism.Per.AinfP l) :=
  GlobalTheory.AcrisDiscExt.isUnit_natCast_of (l := l) ((algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)).comp (Formalism.Per.zA l))
    (by
      have := IsLocalization.Away.algebraMap_isUnit (S := Formalism.Per.AinfP l) (l : Formalism.Per.Ainf l)
      simpa using this) n hn

end GlobalTheory.AcrisFrobE

namespace GlobalTheory.AcrisFrobE
open scoped Nat
variable (l : ℕ) [Fact l.Prime]

theorem coe_natCast0 (k : ℕ) : ((k : Formalism.Per.Acris0 l) : Formalism.Per.AinfP l) = k :=
  map_natCast (Formalism.Per.Acris0 l).val k

theorem exists_dpow (x : Formalism.Per.Ainf l) (hx : Formalism.Per.θ l x = 0) (n : ℕ) :
    ∃ d : Formalism.Per.Acris0 l, ((n ! : ℕ) : Formalism.Per.AinfP l) * (d : Formalism.Per.AinfP l) =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n := by
  obtain ⟨u, hu⟩ := isUnit_natCast_ainfP l (n !) (Nat.factorial_ne_zero n)
  have key : ((n ! : ℕ) : Formalism.Per.AinfP l) *
      (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n * ((u⁻¹ : (Formalism.Per.AinfP l)ˣ) : Formalism.Per.AinfP l)) =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n := by
    rw [← hu, mul_comm, mul_assoc, Units.inv_mul, mul_one]
  exact ⟨⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l x n _ hx key⟩, key⟩

theorem exists_div_l (x : Formalism.Per.Ainf l) (hx : Formalism.Per.θ l x = 0) :
    ∃ y w : Formalism.Per.Acris0 l, (l : Formalism.Per.Acris0 l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) x ^ l ∧
      y ^ l = (l : Formalism.Per.Acris0 l) * w := by
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  set X := algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x with hX
  obtain ⟨g, hg⟩ := exists_dpow l x hx l
  obtain ⟨d, hd⟩ := exists_dpow l x hx (l * l)
  obtain ⟨m, hm⟩ := pow_succ_dvd_factorial l hl0
  have e : l * (l - 1)! = l ! := Nat.mul_factorial_pred hl0.ne'
  refine ⟨(((l - 1)! : ℕ) : Formalism.Per.Acris0 l) * g, (m : Formalism.Per.Acris0 l) * d, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, coe_natCast0,
      coe_natCast0, ← hX, ← hg, ← mul_assoc, ← Nat.cast_mul, e]
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_mul, coe_natCast0,
      coe_natCast0, coe_natCast0]
    refine ((isUnit_natCast_ainfP l (l ^ l) (pow_ne_zero _ hl0.ne')).mul_right_inj).1 ?_
    have h1 : ((l ^ l : ℕ) : Formalism.Per.AinfP l) * ((((l - 1)! : ℕ) : Formalism.Per.AinfP l) * (g : Formalism.Per.AinfP l)) ^ l =
        X ^ (l * l) := by
      rw [pow_mul, ← hg, ← e, Nat.cast_mul, Nat.cast_pow, ← mul_pow]; ring
    rw [h1, ← hd, hm]
    push_cast; ring

end GlobalTheory.AcrisFrobE

namespace GlobalTheory.AcrisFrobE

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ x : Per.Acris l, (l : Per.Acris l) * x = 0 → x = 0) ∧ IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) ∧ (∃ v : (Per.Acris l)ˣ, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a bk.E) = (l : Per.Acris l) * v) ∧ (∀ a : Ainf l, phiA l ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (WittVector.frobenius a)) ∧ ∀ (g : GQ l) (a : Ainf l), sigA g ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (Per.σA g a) := by
  intro l _ K bk
  obtain ⟨htor, hcomp, -, -⟩ := GlobalTheory.Per.acris_basic l
  haveI := hcomp
  refine ⟨htor, hcomp, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := bk.isUnit_δ
    have hφ : frobS l bk.a bk.E = bk.E ^ l + (l : bk.S) * (u : bk.S) := by
      rw [hu]; exact (deltaS l bk.a).φ_eq bk.E
    have hx : Formalism.Per.θ l (bk.ev bk.E) = 0 := by
      have h : bk.ev bk.E ∈ RingHom.ker (Formalism.Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact h
    obtain ⟨y, w, hy, hw⟩ := exists_div_l l _ hx
    set j := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) with hj
    set a := algebraMap (Ainf l) (Formalism.Per.Acris l) with ha_def
    have ha : ∀ t, a t = j (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) t) :=
      fun t => GlobalTheory.RingIface.tower l t
    set A : Formalism.Per.Acris l := a (bk.ev (u : bk.S)) with hA
    have hAu : IsUnit A := (u.isUnit.map bk.ev).map a
    obtain ⟨U, hU⟩ := hAu
    set Y := j y with hY
    set z := ((U⁻¹ : (Formalism.Per.Acris l)ˣ) : Formalism.Per.Acris l) * Y with hz_def
    have hz : z ^ l ∈ Ideal.span {(l : Formalism.Per.Acris l)} := by
      rw [hz_def, mul_pow, show Y ^ l = (l : Formalism.Per.Acris l) * j w by rw [hY, ← map_pow, hw, map_mul, map_natCast]]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    have hJ : (-z) ^ l ∈ (⊥ : Ideal (Formalism.Per.Acris l)).jacobson := by
      refine IsAdicComplete.le_jacobson_bot (Ideal.span {(l : Formalism.Per.Acris l)}) ?_
      rw [neg_pow]; exact Ideal.mul_mem_left _ _ hz
    have h1 : IsUnit (1 - (-z) ^ l) := by
      have := Ideal.mem_jacobson_bot.1 hJ (-1)
      rwa [mul_neg_one, neg_add_eq_sub] at this
    have h2 : IsUnit (1 + z) := by
      rw [← mul_neg_geom_sum, sub_neg_eq_add] at h1
      exact isUnit_of_mul_isUnit_left h1
    obtain ⟨V, hV⟩ := h2
    refine ⟨U * V, ?_⟩
    have hUU : (U : Formalism.Per.Acris l) * ((U⁻¹ : (Formalism.Per.Acris l)ˣ) : Formalism.Per.Acris l) = 1 := U.mul_inv
    have hxl : a (bk.ev bk.E) ^ l = (l : Formalism.Per.Acris l) * Y := by
      rw [ha, ← map_pow, ← hy, map_mul, map_natCast]
    rw [RingHom.comp_apply, hφ, map_add, map_mul, map_pow, map_natCast, map_add, map_pow, map_mul, map_natCast, hxl,
      Units.val_mul, hV, hU, hz_def]
    rw [← hA]
    rw [hU] at hUU
    linear_combination (-(l : Formalism.Per.Acris l) * Y) * hUU
  · intro a
    rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
    congr 1
    ext n
    rw [GlobalTheory.RingIface.phiA_coeff l a n, WittVector.coeff_frobenius_charP]
  · intro g a
    rw [(GlobalTheory.CrisMaps.sigA_extends g).alg]

end GlobalTheory.AcrisFrobE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationRadiusLawsStatement
section
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisValuation_radius_laws : ∀ (l : ℕ) [Fact l.Prime] (r : ℝ), 0 < r → r ≤ 1 → (∀ x y : Formalism.Per.Acris l, x ≠ 0 → y ≠ 0 → vr l r (x * y) = vr l r x + vr l r y) ∧ (∀ x : Formalism.Per.Acris l, x ≠ 0 → φc l x ≠ 0 ∧ vr l r (φc l x) = l * vr l (r / l) x) ∧ (∀ (x : Formalism.Per.Acris l) (n : ℕ), x ≠ 0 → vr l r ((l : Formalism.Per.Acris l) ^ n * x) = n * r + vr l r x) ∧ ∀ x : Formalism.Per.Acris l, x ≠ 0 → vr l r x = -Real.logb l (gC l ((l : ℝ) ^ (-r)) x) := by
  first | exact @GlobalTheory.PMon.Gauss.vr_laws | exact GlobalTheory.PMon.Gauss.vr_laws | (intros; apply GlobalTheory.PMon.Gauss.vr_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisBasisModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

private theorem TopBasis.c_mem_of_mem_map_pow {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (tb : TopBasis s I ι) (m : ℕ) (j : ι) {y : A} (hy : y ∈ (I ^ m).map s) : tb.c j y ∈ I ^ m := by
  suffices h : ∀ r : A, tb.c j (r * y) ∈ I ^ m by simpa using h 1
  refine Submodule.span_induction (p := fun y _ => ∀ r : A, tb.c j (r * y) ∈ I ^ m) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, ha, rfl⟩ r
    rw [mul_comm, tb.c_mul]
    exact Ideal.mul_mem_right _ _ ha
  · intro r; simp
  · intro x y _ _ hx hy r
    rw [mul_add, map_add]
    exact Ideal.add_mem _ (hx r) (hy r)
  · intro a x _ hx r
    rw [smul_eq_mul, ← mul_assoc]
    exact hx (r * a)

theorem TopBasis.basis_mod_pow : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type)
    (tb : TopBasis s I ι) (m : ℕ), letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra;
    ∃ b : Module.Basis ι (S ⧸ I ^ m) (A ⧸ (I ^ m).map s), ∀ i, b i = Ideal.Quotient.mk _ (tb.b i) := by
  intro S A _ _ s I ι tb m
  letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra
  have hsmul : ∀ (a : S) (x : A), (Ideal.Quotient.mk (I ^ m) a) • (Ideal.Quotient.mk ((I ^ m).map s) x)
      = Ideal.Quotient.mk ((I ^ m).map s) (s a * x) := by
    intro a x
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk, map_mul]
  have hli : LinearIndependent (S ⧸ I ^ m) (fun i => Ideal.Quotient.mk ((I ^ m).map s) (tb.b i)) := by
    rw [linearIndependent_iff']
    intro F g hg j hj
    choose h hh using fun i => Ideal.Quotient.mk_surjective (I := I ^ m) (g i)
    have hsum : (∑ i ∈ F, s (h i) * tb.b i) ∈ (I ^ m).map s := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hg]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hh i, hsmul]
    have hc := tb.c_mem_of_mem_map_pow m j hsum
    rw [map_sum, Finset.sum_eq_single j] at hc
    · rw [tb.c_mul, tb.c_self, mul_one] at hc
      rw [← hh j]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
    · intro i _ hij
      rw [tb.c_mul, tb.c_ne j i (Ne.symm hij), mul_zero]
    · intro h'; exact (h' hj).elim
  have hsp : ⊤ ≤ Submodule.span (S ⧸ I ^ m) (Set.range fun i => Ideal.Quotient.mk ((I ^ m).map s) (tb.b i)) := by
    rintro x -
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hF : ∀ i, i ∉ (tb.fin y m).toFinset → tb.c i y ∈ I ^ m := by
      intro i hi
      simpa using hi
    have hx := tb.approx y m (tb.fin y m).toFinset hF
    have : Ideal.Quotient.mk ((I ^ m).map s) y = ∑ i ∈ (tb.fin y m).toFinset,
        (Ideal.Quotient.mk (I ^ m) (tb.c i y)) • Ideal.Quotient.mk ((I ^ m).map s) (tb.b i) := by
      simp_rw [hsmul, ← map_sum]
      exact Ideal.Quotient.eq.mpr hx
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => by simp⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisExistsCompStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicTopologicalBasis_exists_comp : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι) (A' : Type) [CommRing A'] (t : A →+* A') (I' : Ideal A) (κ : Type) (TB' : TopBasis t I' κ), I' = I.map s → ∃ TC : TopBasis (t.comp s) I (ι × κ), (∀ i j, TC.b (i, j) = t (TB.b i) * TB'.b j) ∧ ∀ i j x, TC.c (i, j) x = TB.c i (TB'.c j x) := by
  first | exact @GlobalTheory.BSP.topBasis_comp_exists | exact GlobalTheory.BSP.topBasis_comp_exists | (intros; apply GlobalTheory.BSP.topBasis_comp_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDecompIffDecomp
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DecompForms

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π ↔ ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := by
  intro D i r ρ π
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun g u => he g u⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun g u => he g u⟩

end GlobalTheory.DecompForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmIntOfSupLaws
section
noncomputable section

namespace GlobalTheory.IntSup

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem mall_map_le (i : X.Tw) (j : ℕ) (b : Bool) (φ : Module.End (FractionRing (X.O i)) (Y.Fm i j b))
    (hφ : ∀ f ∈ Y.Bsup i j b, φ f ∈ Y.Bsup i j b)
    (hc : ∀ g, (Y.actG i j b g).toLinearMap ∘ₗ φ = φ ∘ₗ (Y.actG i j b g).toLinearMap) :
    (IntegralHeckeForms.Mall Y i j b).map (φ.restrictScalars (X.O i)) ≤ IntegralHeckeForms.Mall Y i j b := by
  rintro _ ⟨f, ⟨hf, hf0⟩, rfl⟩
  refine ⟨hφ f hf, ?_⟩
  change φ f ∈ IntegralHeckeForms.Fm0 Y i j b
  replace hf0 : f ∈ IntegralHeckeForms.Fm0 Y i j b := hf0
  simp only [IntegralHeckeForms.Fm0, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hf0 ⊢
  intro u
  have h := LinearMap.congr_fun (hc u) f
  simp only [LinearMap.comp_apply] at h
  rw [h, hf0 u, map_smul]

theorem admInt_of_sup : ∀ (D : D7) (E : IntegralHeckeForms.XD D), SupG D → SupFull D → SupHk D → UnivSup D E → TypeKept E → CommG D →
    IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E := by
  intro D E hG hF hH hU hT hC i hi j hj b
  obtain ⟨hfg, hsp⟩ := hF i hi j hj b
  refine ⟨fun g => ?_, ?_,
    GlobalTheory.IntRestBall.span_inf_of_span_top _ hsp _ _ (fun _ => Iff.rfl),
    fun k P hk => mall_map_le D.nexp i j b _ (hH i hi j hj b k P hk) (fun g => hC i hi b j hj g k P hk),
    ?_, hT i hi j hj b⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact hG i hi j hj b g f hf
  · exact hfg.of_le (fun f hf => hf.1)
  · intro a ha
    obtain ⟨c, hc⟩ := hU i hi j hj b a ha
    refine ⟨c, fun Q M h1 h2 h3 h4 => ?_⟩
    obtain ⟨Xi, hXi, hδ⟩ := hc Q M h1 h2 h3 h4
    rw [hXi, Finsupp.sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun δ _ => ?_
    have hm : ((D.ntw.l i : D.ntw.O i) ^ c) • Xi δ ∈ IntegralHeckeForms.Mall D.nexp i j b :=
      ⟨(hδ δ).2, ((IntegralHeckeForms.Fm0 D.nexp i j b).restrictScalars (D.ntw.O i)).smul_mem _ (hδ δ).1⟩
    exact ⟨(⟨_, hm⟩ : IntegralHeckeForms.Mall D.nexp i j b) ⊗ₜ AddMonoidAlgebra.single δ (1 : D.ntw.O i), by
      simp [TensorProduct.smul_tmul']⟩

end GlobalTheory.IntSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT3OfHeckeSemisimple
section
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.EigRed

open Formalism.MainNotions.IntegralHeckeForms

theorem admT3_of_semisimple_good : ∀ (D : D7) (E : IntegralHeckeForms.XD D), IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → D.nexp.sig_all → HkSS D → IntegralHeckeForms.GoodLatticePoints D.nexp := by
  intro D E hI hA hS hss i hi j hj b x hxB hxm ev hev
  by_contra hno
  apply hxm
  have hcomm := ((hA i hi b).2 j hj).1
  have hM := (hI i hi j hj b).2.2.2.1
  have hx := hss i hi j hj b hxB.2
  obtain ⟨f, hf, hfx⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx
  refine mem_smul_of_sum_eigenvectors (ι := {p : ℕ × PlE D.host // HkIdx i p.1 p.2}) _ _
    (fun p => hkO D.nexp i j b p.1.1 p.1.2) (fun p z hz => ?_) (fun p => ev p.1.1 p.1.2) f.support
    (fun a => f a) x (fun a _ => ?_) ?_ hxB (fun p => hev _ _ p.2)
  · exact ⟨hM _ _ p.2 ⟨z, hz.1, rfl⟩, idempotentImage_stable_of_equivariant D.nexp i j b _ (fun g => hcomm g _ _ p.2) z hz.2⟩
  · by_cases h0 : f a = 0
    · exact Or.inl h0
    right
    have hex : eG D.nexp i j b (f a) = f a := by
      obtain ⟨y, -, hy⟩ := (hf a).2
      rw [← hy, eG_idem]
    have heig : ∀ k P, HkIdx i k P → D.nexp.hkF i j b k P (f a) = a k P • f a := by
      intro k P hk
      have h1 := (hf a).1
      simp only [Eigsp, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h1
      exact h1 k P hk
    obtain ⟨s, hs1, hs2, hs3⟩ := hS i j b _ a h0 hex
      (fun k P h1 h2 h3 h4 => heig k P ⟨h1, h2, h3, h4⟩)
    refine ⟨fun p => D.ntw.hEig i s p.1.1 p.1.2, fun p => ?_, ?_⟩
    · change D.nexp.hkF i j b _ _ _ = _
      rw [heig _ _ p.2, ← hs3 _ _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, algebraMap_smul]
    · by_contra hu
      refine hno ⟨s, hs1, hs2, fun k P hk => ?_⟩
      exact fun h => hu ⟨⟨(k, P), hk⟩, h⟩
  · exact hfx.symm

end GlobalTheory.EigRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleCocycleNegCharPowerMemCoboundaries
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.CharSplit

theorem admissibleCocycle_negCharPower_mem_coboundaries : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 1 ≤ e → e < Dt.t → ∀ z ∈ M.twistedModelAdmissibleCocycles (chr (M.ω ^ (-e))), z ∈ cob (chr (M.ω ^ (-e))) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 e he1 het z hz
  obtain ⟨N, b, g, hmod, hrep, hzz⟩ := GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 _ z hz
  have hN : N = M.Nχ e := GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 e (by omega) het N hmod
  subst hN
  apply GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F _ z b g hrep

  have hlat := fun i => M.χ_lat e (by omega) het i

  set J : ZMod n → ℕ := fun i =>
    if Dt.ty i = LType.G then (Dt.w i).toNat else (Dt.wst i - e).toNat with hJ
  have hJG : ∀ i, Dt.ty i = LType.G → J i = (Dt.w i).toNat := fun i h => by simp [hJ, h]
  have hJB : ∀ i, Dt.ty i = LType.Bd → J i = (Dt.wst i - e).toNat := fun i h => by simp [hJ, h]

  have hsmall : ∀ i (j : ℕ), j ≤ J i → e + (j : ℤ) < l := by
    intro i j hj
    have hT := h1 i
    have hw := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
    cases hty : Dt.ty i with
    | G =>
      obtain ⟨-, -, hw1, hw2⟩ := hw.2.2.1 hty
      rw [hJG i hty] at hj
      omega
    | Bd =>
      obtain ⟨-, -, hb1, hb2⟩ := hw.2.2.2 hty
      rw [hJB i hty] at hj
      omega
  obtain ⟨m, -, hm⟩ := GlobalTheory.PhiGam.cocycle_split_of_contracting R (F.D (chr (M.ω ^ (-e)))) (M.Nχ e) J
    (fun i => (hlat i).1) (fun i => (hlat i).2.1)
    (fun i => by rw [(hlat i).2.2.1]; exact sh_le_sh_of_le he1 _)
    (fun i j hj1 hjJ => by
      rw [(hlat i).2.2.2]
      unfold resCount
      classical
      simp only [Multiset.card_eq_zero, Multiset.filter_eq_nil, Multiset.mem_singleton, forall_eq]
      intro hcast
      have h0 : ((e + (j : ℤ) : ℤ) : k) = 0 := by
        push_cast at hcast ⊢
        linear_combination hcast
      rw [CharP.intCast_eq_zero_iff k l] at h0
      have hle := Int.le_of_dvd (by omega) h0
      have := hsmall i j hjJ
      omega)
    b g (fun i => (hzz i).1) (fun i => (hzz i).2.1)
    (fun i => by
      have hw := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
      cases hty : Dt.ty i with
      | G =>
        have hb := (hzz i).2.2.1 hty
        have h := (hw.2.2.1 hty).2.2.1
        have hJi : ((J i : ℕ) : ℤ) = Dt.w i := by
          rw [hJG i hty]
          omega
        rw [hJi]
        exact hb
      | Bd =>
        have hb := ((hzz i).2.2.2 hty).1
        have h := (hw.2.2.2 hty).2.2.1
        rw [(hlat i).2.2.1, sh_sh_eq] at hb
        have hJi : -((J i : ℕ) : ℤ) = -Dt.wst i + e := by
          rw [hJB i hty]
          omega
        rw [hJi]
        exact hb)
  rw [herrB_eq_range]
  refine ⟨m, ?_⟩
  rw [herrD_apply]
  exact Prod.ext (funext fun i => ((hm i).1).symm) (funext fun i => ((hm i).2).symm)

end GlobalTheory.CharSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroLowCoeffThreeNilpotentsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_eq_zero_low_coeff_three_nilpotents : ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t x y : B) (K m : ℕ) (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → x * x = 0 → y ^ m = 0 → (∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) → (∀ u : ι →₀ ℕ, u.degree < K + m → algebraMap O B (F.coeff u) = 0) → MvPolynomial.aeval ξ F = 0 := by
  first | exact @GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent | exact GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent | (intros; apply GlobalTheory.NewPrime.aeval_eq_zero_of_low_coeff_of_three_nilpotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDivisibilityBreuilKisinFactsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_divisibility_breuilKisin_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ (n : ℕ) (y : Ainf l), ((l : ℕ) : Ainf l) * y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ (2 * n + 2) → y ∈ (Ideal.span {((l : ℕ) : Ainf l)} ⊔ RingHom.ker (Per.θ l)) ^ n) ∧ (∀ y : Ainf l, ((l : ℕ) : Ainf l) ∣ bk.ev X * y → ((l : ℕ) : Ainf l) ∣ y) ∧ (∀ y : Ainf l, (∀ m : ℕ, ∃ z, ((l : ℕ) : Ainf l) ∣ y - bk.ev X ^ m * z) → ((l : ℕ) : Ainf l) ∣ y) ∧ bk.flat ≠ 0 ∧ ¬ IsUnit bk.flat ∧ IsAdicComplete (Ideal.span {bk.flat}) (OCb l) ∧ ((l : ℕ) : Ainf l) ∣ bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree := by
  first | exact @GlobalTheory.BSP.AinfDiv.main | exact GlobalTheory.BSP.AinfDiv.main | (intros; apply GlobalTheory.BSP.AinfDiv.main <;> assumption)
end

