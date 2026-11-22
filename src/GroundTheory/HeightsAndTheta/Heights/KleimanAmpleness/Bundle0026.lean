import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0019

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltKernel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SectionCount.Drop.Filt.Kernel

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_secs_iff' {F : SubSystem S x Ω} {y : Ω} : y ∈ F.secs ↔ ∀ I, y ∈ F.sub I := by
  simp [SubSystem.secs, Submodule.mem_iInf]

def ratioPow (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (j : Fin (N + 1)) (b : ℕ) :
    chartRing S x I :=
  ⟨x j ^ b / x i ^ b, X j ^ b, X i ^ b, b, pow_mem (X_mem_monos hi) b, isHomogeneous_X_pow _ _,
    isHomogeneous_X_pow _ _, by simp⟩

theorem aeval_div_mem_chartRing (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) (f : Poly S N) :
    aeval (fun l => x l / x i) f ∈ chartRing S x I := by
  have h : (aeval (fun l => x l / x i) : Poly S N →ₐ[S] Ω).range ≤ chartRing S x I := by
    rw [← Algebra.adjoin_range_eq_range_aeval, Algebra.adjoin_le_iff]
    rintro _ ⟨l, rfl⟩
    exact ⟨X l, X i, 1, X_mem_monos hi, isHomogeneous_X _ _, isHomogeneous_X _ _, by simp⟩
  exact h ⟨f, rfl⟩

theorem idealMod_le (j : Fin (N + 1)) (b : ℕ) (I : Chart x) {i : Fin (N + 1)} (hi : i ∈ I.1) :
    idealMod (primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b)) I ≤
      Submodule.span (chartRing S x I) {x j ^ b / x i ^ b} := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  set M := Submodule.span (chartRing S x I) {x j ^ b / x i ^ b}
  let K : Ideal (Poly S N) :=
    { carrier := {f | aeval (fun l => x l / x i) f ∈ M}
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq, map_add] at *; exact M.add_mem hf hg
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact M.zero_mem
      smul_mem' := fun r f hf => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
        exact M.smul_mem ⟨_, aeval_div_mem_chartRing I hi r⟩ hf }
  have hK : primeOf (S := S) x ⊔ zeroIdeal (twistSys S x (b : ℤ)) (x j ^ b) ≤ K := by
    refine sup_le (fun f hf => ?_) (Ideal.span_le.mpr ?_)
    · change aeval (fun l => x l / x i) f ∈ M
      rw [← sum_homogeneousComponent f, map_sum]
      convert M.zero_mem
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [aeval_div_of_isHomogeneous (homogeneousComponent_isHomogeneous d f) i,
        (mem_primeOf_of_isHomogeneous x (homogeneousComponent_isHomogeneous d f)).mp
          (homogeneousComponent_mem_primeOf x hf d), zero_div]
    · rintro g ⟨c, hg, hz⟩
      have hδ : x i ^ b ∈ (twistSys S x (b : ℤ)).sub I := by
        change x i ^ b ∈ twistMod S x (b : ℤ) I
        rw [twistMod_eq_span _ I hi, zpow_natCast]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨o, ho, he⟩ := hz I _ hδ
      rw [twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton] at ho
      obtain ⟨a, rfl⟩ := ho
      change aeval (fun l => x l / x i) g ∈ M
      rw [aeval_div_of_isHomogeneous hg i, Submodule.mem_span_singleton]
      refine ⟨a, ?_⟩
      rw [chartRing_smul_def] at he ⊢
      field_simp
      linear_combination -he
  rw [idealMod, Submodule.span_le]
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hm : aeval (fun l => x l / x i) f ∈ M := hK hf
  rw [aeval_div_of_isHomogeneous hfe i] at hm
  have h := M.smul_mem (⟨x i ^ e / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow _ _, hse,
    by simp⟩ : chartRing S x I) hm
  rw [chartRing_smul_def] at h
  rw [SetLike.mem_coe]
  convert h using 1
  change _ = x i ^ e / aeval x s * (aeval x f / x i ^ e)
  have : x i ^ e ≠ 0 := pow_ne_zero _ hxi
  field_simp

theorem proof : SectionCount.Drop.Filt.Kernel.Statement.{u, w} := by
  intro S _ Ω _ _ N x j b F hj
  have hjb : x j ^ b ≠ 0 := pow_ne_zero _ hj
  constructor
  · intro t ht
    refine mem_secs_iff'.mpr fun I => ?_
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hI := mem_secs_iff'.mp ht I
    rw [SubSystem.twist_sub_eq_mul_of_line] at hI
    refine Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)
    · change q ∈ twistMod S x (-(b : ℤ)) I at hq
      rw [twistMod_eq_span _ I hi, Submodule.mem_span_singleton] at hq
      obtain ⟨a, rfl⟩ := hq
      have h := (F.sub I).smul_mem (a * ratioPow I hi j b) hy
      rw [chartRing_smul_def] at h ⊢
      convert h using 1
      simp only [ratioPow, Subalgebra.coe_mul, zpow_neg, zpow_natCast]
      field_simp
    · rw [mul_add]; exact (F.sub I).add_mem hu hv
  · intro s hs
    refine ⟨(x j ^ b)⁻¹ * s, mem_secs_iff'.mpr fun I => ?_, by field_simp⟩
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    have hI := mem_secs_iff'.mp hs I
    rw [SubSystem.twist_sub_eq_mul_of_line] at hI
    rw [SubSystem.twist_sub_eq_mul_of_line]
    refine Submodule.mul_induction_on hI (fun q hq y hy => ?_) (fun u v hu hv => ?_)
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (idealMod_le j b I hi hq)
      have hq' : (a : Ω) * x i ^ (-(b : ℤ)) ∈ (twistSys S x (-(b : ℤ))).sub I := by
        change _ ∈ twistMod S x (-(b : ℤ)) I
        rw [twistMod_eq_span _ I hi]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)
      convert Submodule.mul_mem_mul hq' hy using 1
      rw [chartRing_smul_def]
      simp only [zpow_neg, zpow_natCast]
      field_simp
    · rw [mul_add]; exact add_mem hu hv

end SectionCount.Drop.Filt.Kernel

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropHilbW
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}

theorem hilbW_X_mem_primeOf (x : Fin (N + 1) → Ω) {i : Fin (N + 1)} (hi : x i = 0) :
    (X i : Poly S N) ∈ primeOf (S := S) x := by
  rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X S i), aeval_X, hi]

theorem hilbW_ne_zero {x : Fin (N + 1) → Ω} {pp : Ideal (Poly S N)} {e : ℕ} (h : IsSubvar x pp e) :
    x ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  intro hx
  exact hi (h.le (hilbW_X_mem_primeOf x (by rw [hx, Pi.zero_apply])))

end

theorem SectionCount.Drop.HilbW.proof
    (hPt : PrimeFiltration.Point.Statement.{u, w})
    (hRes : Restriction.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hLT : LineTwist.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w})
    (hIR : InterNumRestrict.Statement.{u, w})
    (hES : VeryAmpleEmbed.Sections.Statement.{u, w})
    (hEN : VeryAmpleEmbed.Numbers.Statement.{u, w})
    (hH0 : CechZerothCohomologySections.Statement.{u, w, w})
    (hHP : HilbertPositive.Statement.{u, w})
    (hHPt : HilbertPoint.Statement.{u, w})
    (hTie : InterNumTie.Statement.{u, w})
    (hIP : InterNumPoint.Statement.{u, w}) :
    SectionCount.Drop.HilbW.Statement.{u, w} := by
  intro k _ Ω _ _ N x Nb pp e hVA hW
  obtain ⟨r, h, hVh⟩ := hVA
  obtain ⟨j, hj'⟩ := hW.relevant
  have hj : x j ≠ 0 := fun h0 => hj' (hW.le (hilbW_X_mem_primeOf x h0))
  have hPtj := hPt k Ω N x pp hW.isPrime hW.homog hW.le j hj hj'

  obtain ⟨K', _, _, ψ, hker⟩ : ∃ (K' : Type w) (_ : Field K') (_ : Algebra k K')
      (ψ : chartRing k x (singleChart hj) →ₐ[k] K'), RingHom.ker ψ = chartPrime pp hj := by
    have : (chartPrime pp hj).IsPrime := hPtj.1
    have : IsDomain (chartRing k x (singleChart hj) ⧸ chartPrime pp hj) := Ideal.Quotient.isDomain _
    refine ⟨FractionRing (chartRing k x (singleChart hj) ⧸ chartPrime pp hj), inferInstance, inferInstance,
      (IsScalarTower.toAlgHom k _ _).comp (Ideal.Quotient.mkₐ k (chartPrime pp hj)), ?_⟩
    ext a
    rw [RingHom.mem_ker]
    change algebraMap _ (FractionRing (chartRing k x (singleChart hj) ⧸ chartPrime pp hj))
      (Ideal.Quotient.mk (chartPrime pp hj) a) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i hi h0
    apply hi
    have : ratio (S := k) hj i = 0 := Subtype.ext (show x i / x j = 0 by rw [h0, zero_div])
    rw [this, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hPtj.2 K' ψ hker
  have hle : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := by
    rw [hpy]; exact hW.le
  have hWy : IsSubvar (fun i => ψ (ratio hj i)) pp e := ⟨hW.isPrime, hW.homog, hpy.le, hW.relevant, hW.dim⟩
  have hWy' : IsSubvar (fun i => ψ (ratio hj i)) (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]; exact hWy

  obtain ⟨Q', ρ, hRD, hVA', -⟩ := hRes k Ω N x Nb r h hVh pp hW.isPrime hW.homog hW.le j hj hj' K' ψ hker hxy
  obtain ⟨hWh, hnum⟩ := hEN k K' N _ Q' r (ρ ∘ h) hVA' e hWy'

  have hpow : ∀ m : ℕ, ∃ (Nm : LineBundle k x) (Qm : LineBundle k (fun i => ψ (ratio hj i))) (rm : Ω → K'),
      Nm.toSubSystem = Nb.toSubSystem.pow m ∧ Qm.toSubSystem = Q'.toSubSystem.pow m ∧
        RestrictData Nm.toSubSystem hxy Qm.toSubSystem rm := by
    intro m
    induction m with
    | zero =>
      obtain ⟨r0, hr0⟩ := hRT.1 k Ω N x K' _ hxy hle 0
      exact ⟨twistBundle k x 0, twistBundle k _ 0, r0, rfl, rfl, hr0⟩
    | succ m ih =>
      obtain ⟨Nm, Qm, rm, hN, hQ, hr⟩ := ih
      obtain ⟨N1, hN1⟩ := hLT k Ω N x Nm Nb
      obtain ⟨Q1, hQ1⟩ := hLT k K' N _ Qm Q'
      obtain ⟨r1, hr1⟩ := hRT.2 k Ω N x K' _ hxy Nm Nb Qm Q' rm ρ hr hRD
      refine ⟨N1, Q1, r1, ?_, ?_, ?_⟩
      · rw [hN1, hN]; rfl
      · rw [hQ1, hQ]; rfl
      · rw [hN1, hQ1]; exact hr1

  have hdim : ∀ m : ℕ, Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem m 0)
      ((twistMul Nb.toSubSystem m 0).twist (idealSys x pp)) 0) =
        Module.finrank k (twistSys k (ρ ∘ h) (m : ℤ)).secs := by
    intro m
    obtain ⟨Nm, Qm, rm, hN, hQ, hr⟩ := hpow m
    obtain ⟨E1⟩ := hRQ k Ω N x pp hW.isPrime hW.homog hW.le j hj hj' K' ψ hker hxy Nm Qm rm hr 0 0
    obtain ⟨E2⟩ := hH0 k K' N _ K' (Q'.toSubSystem.pow m) (hilbW_ne_zero hWy)
    have e1 : Nm.toSubSystem.twist (twistSys k x 0) = twistMul Nb.toSubSystem m 0 := by rw [hN]; rfl
    have e2 : Qm.toSubSystem.twist (twistSys k (fun i => ψ (ratio hj i)) 0) = Q'.toSubSystem.pow m := by
      rw [hQ, SubSystem.twist_twistSys_zero]
    rw [← hES k K' N _ Q' r (ρ ∘ h) (hilbW_ne_zero hWy) hVA' m, ← e1, ← E2.finrank_eq, ← e2]
    exact E1.finrank_eq

  have hI : interNum pp (fun _ : Fin e => Nb.toSubSystem) =
      interNum (primeOf (S := k) (ρ ∘ h)) (fun _ : Fin e => twistSys k (ρ ∘ h) 1) := by
    have h1 : interNum pp (fun _ : Fin e => Q'.toSubSystem) = interNum pp (fun _ : Fin e => Nb.toSubSystem) :=
      hIR k Ω N x K' _ hxy hle pp e hWy (fun _ => Nb) (fun _ => Q') (fun _ => ρ) (fun _ => hRD)
    rw [← h1, ← hnum, hpy]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · obtain ⟨-, hpc, hsecs⟩ := hHPt k K' r (ρ ∘ h) hWh
    have hI0 : interNum pp (fun _ : Fin 0 => Nb.toSubSystem) =
        (Module.finrank k (funField (k := k) (ρ ∘ h)) : ℤ) := by
      rw [hI]; exact hIP k K' r (ρ ∘ h) hWh _
    refine ⟨0, ?_⟩
    filter_upwards [hpc, hsecs] with m h1 h2
    rw [hdim m, h2, h1, hI0]
    simp
  · obtain ⟨⟨C, hC⟩, -, hsecs⟩ := hHP k K' r (ρ ∘ h) e he hWh
    have hc : (primeOf (S := k) (ρ ∘ h)).comap (oneBlock (S := k) (N := r)).toRingHom =
        primeOfOne (S := k) (ρ ∘ h) := Ideal.ext fun _ => Iff.rfl
    have hIe : interNum pp (fun _ : Fin e => Nb.toSubSystem) =
        NumbersDVR.intNum k (primeOfOne (S := k) (ρ ∘ h)) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) := by
      rw [hI, ← hc]
      exact hTie k K' r (ρ ∘ h) e (primeOf (S := k) (ρ ∘ h)) (fun _ => 1) hWh
    refine ⟨C, ?_⟩
    filter_upwards [hC, hsecs, eventually_ge_atTop 1] with m h1 h2 hm
    rw [hdim m, h2, hIe]
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hpow' : (m : ℝ) ^ e / m = (m : ℝ) ^ (e - 1) := by
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      rw [pow_succ, mul_div_assoc, div_self hm0, mul_one, Nat.add_sub_cancel]
    have hCm : C * (m : ℝ) ^ e / m = C * (m : ℝ) ^ (e - 1) := by rw [mul_div_assoc, hpow']
    rw [hCm]
    exact h1

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Sections

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem mul_mem_pow_succ (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) : a * q ∈ (Q.pow (m + 1)).sub I :=
  Submodule.subset_span ⟨q, hq, a, ha, by rw [smul_eq_mul, mul_comm]⟩

theorem mul_pow_mem_pow (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) (j : ℕ) : a * q ^ j ∈ (Q.pow (m + j)).sub I := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact mul_mem_pow_succ Q I ih hq

theorem aeval_mem_pow (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (I : Chart x) {f : MvPolynomial (Fin (r + 1)) k} {n : ℕ} (hf : f.IsHomogeneous n) :
    aeval h f ∈ (Q.pow n).sub I := by
  have hI : ∀ l, h l ∈ Q.sub I := fun l =>
    (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp (hh l) I)
  have hprod : ∀ (α : Fin (r + 1) →₀ ℕ) (s : Finset (Fin (r + 1))),
      ∏ i ∈ s, h i ^ α i ∈ (Q.pow (∑ i ∈ s, α i)).sub I := by
    intro α s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact one_mem_twistMod_zero (S := k) I
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, mul_comm, add_comm]
      exact mul_pow_mem_pow Q I ih (hI j) (α j)
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [aeval_monomial]
  have hdeg : ∑ i ∈ α.support, α i = n := by
    have := hf (mem_support_iff.mp hα)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  have hmem := hprod α α.support
  rw [hdeg] at hmem
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact Submodule.smul_of_tower_mem _ _ hmem

theorem coordGraded_le_secs (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (n : ℕ) : (coordGraded k h).piece (n : ℤ) ≤ (twistMul Q n 0).secs := by
  rw [twistMul, SubSystem.twist_twistSys_zero]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, e, hf, he, rfl⟩
  have hen : e = n := by exact_mod_cast he
  subst hen
  exact (Submodule.mem_iInf _).mpr fun I =>
    (Submodule.restrictScalars_mem k _ _).mpr (aeval_mem_pow Q hh I hf)

theorem finite_secs_twistMul (hTF : TwistFinite.Statement.{u, w}) (Nb : LineBundle k x) {r : ℕ}
    {h : Fin (r + 1) → Ω} (hx : x ≠ 0) (hV : IsVeryAmpleBy Nb.toSubSystem h) (n : ℕ) :
    Module.Finite k (twistMul Nb.toSubSystem n 0).secs := by
  obtain ⟨m, deg, gen, -, hspan⟩ :=
    hTF k Ω N x (twistBundle k x 0) Nb r h hx hV.mem_secs hV.generates
  have e1 : (twistBundle k x 0).toSubSystem.twist (Nb.toSubSystem.pow n) =
      twistMul Nb.toSubSystem n 0 := by
    rw [twistMul, SubSystem.twist_twistSys_zero]
    exact twistSys_zero_twist _
  have hle := hspan n
  rw [e1] at hle
  let T : Submodule k Ω := ⨆ j : Fin m, (homogeneousSubmodule (Fin (r + 1)) k (n - deg j)).map
    ((LinearMap.mulRight k (gen j)).comp (aeval h).toLinearMap)
  have hT : T.FG := Submodule.fg_iSup _ fun j => (homogeneousSubmodule_fg (Fin (r + 1)) k (n - deg j)).map _
  have hle' : Submodule.span k {z | ∃ (j : Fin m) (f : MvPolynomial (Fin (r + 1)) k) (e : ℕ),
      f.IsHomogeneous e ∧ e + deg j = n ∧ z = aeval h f * gen j} ≤ T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, f, e, hf, hed, rfl⟩
    refine Submodule.mem_iSup_of_mem j ⟨f, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule]
    convert hf using 1
    omega
  have : FiniteDimensional k T := Module.Finite.iff_fg.mpr hT
  exact Submodule.finiteDimensional_of_le (hle.trans hle')

end Sections

theorem SectionCount.Top.proof (hHP : HilbertPositive.Statement.{u, w})
    (hTie : InterNumTie.Statement.{u, w}) (hTF : TwistFinite.Statement.{u, w})
    (hDim : VeryAmpleDim.Statement.{u, w}) (hDeg : VeryAmpleDegree.Statement.{u, w}) :
    SectionCount.Top.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb hZ hN
  obtain ⟨r, h, hV⟩ := hN
  have hx : x ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hZ.relevant
    exact hi ((mem_primeOf_of_isHomogeneous _ (isHomogeneous_X k i)).mpr (by simp))
  have hZh := hDim k Ω N x (d + 1) Nb r h hZ hV
  obtain ⟨⟨C, hC⟩, -, -⟩ := hHP k Ω r h (d + 1) (Nat.le_add_left 1 d) hZh
  have hnum : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
      NumbersDVR.intNum k (primeOfOne (S := k) h) (fun _ : Fin (d + 1) => fun _ : Unit => (1 : ℤ)) := by
    rw [hDeg k Ω N x (d + 1) Nb r h hZ hV]
    exact hTie k Ω r h (d + 1) (primeOf (S := k) h) (fun _ => 1) hZh
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  have hle : (Module.finrank k ((coordGraded k h).piece (n : ℤ)) : ℝ) ≤
      (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) := by
    have := finite_secs_twistMul hTF Nb hx hV n
    exact_mod_cast Submodule.finrank_mono (coordGraded_le_secs Nb.toSubSystem hV.mem_secs n)
  rw [hnum]
  rw [Nat.add_sub_cancel] at hn
  have := (abs_le.mp hn).1
  linarith

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperHyperplaneMidSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SnapperHyperplaneMid.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ i : Fin (N + 1), (X i : Poly k N) ∉ pp →
    ∀ (a : ℤ) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
      eulerCharQuot k
          ((((twistSys k x (a + 1)).twist (idealSys x (pp ⊔ Ideal.span {(X i : Poly k N)}))).twistPows t
            (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a + 1)).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)) =
        pieceChar k pp a L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotAddSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotAdd.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ F₃ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    (∀ I, F₃.sub I ≤ F₂.sub I) →
    eulerCharQuot k F₁.toSubSystem F₃.toSubSystem =
      eulerCharQuot k F₁.toSubSystem F₂.toSubSystem + eulerCharQuot k F₂.toSubSystem F₃.toSubSystem

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotDevissageSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperQuotDevissage.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubFamily k x E), (∀ I, (F₁.sub I).FG) → (∀ I, F₂.sub I ≤ F₁.sub I) →
    ∀ J : Ideal (Poly k N), (∀ f ∈ J, ∀ d : ℕ, homogeneousComponent d f ∈ J) → primeOf (S := k) x ≤ J →
    (∀ I, (F₁.toSubSystem.twist (idealSys x J)).sub I ≤ F₂.sub I) →
    ∃ (r : ℕ) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧ J ≤ pp m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        eulerCharQuot k
            ((F₁.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
            ((F₂.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          ∑ m, pieceChar k (pp m) (a m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

