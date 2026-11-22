import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2516
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfPiNeZero
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
open scoped Topology

namespace GlobalTheory.LatJet.An.HolLiftProof

theorem ker_nil (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n) : IsNilpotent (RingHom.ker J.π) := by
  classical
  haveI : Finite (Idx I n) := by
    refine Finite.of_injective (fun ν : Idx I n ↦ fun i ↦ (⟨ν.1 i, Nat.lt_succ_of_le (le_trans
      (Finset.single_le_sum (fun l _ ↦ Nat.zero_le (ν.1 l)) (Finset.mem_univ i)) ν.2)⟩ : Fin (n + 2))) ?_
    intro a b h
    exact Subtype.ext (funext fun i ↦ by simpa using congrFun h i)
  haveI : Module.Finite ℂ J.B := Module.Finite.of_basis J.b
  haveI : IsNoetherian ℂ J.B := IsNoetherian.iff_fg.2 inferInstance
  haveI : IsNoetherianRing J.B := isNoetherian_of_tower ℂ inferInstance
  rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian (RingHom.ker J.π))]
  intro x hx
  obtain ⟨N, hN⟩ := J.nil
  refine mem_nilradical.2 ⟨N, ?_⟩
  have := hN (List.replicate N (1, x)) (fun p hp ↦ by rw [List.eq_of_mem_replicate hp]; exact hx) (by simp)
  simpa [List.map_replicate, J.κ.dpow_one hx] using this

theorem adjoin_top (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n) :
    Algebra.adjoin ℂ (Set.range J.t) = ⊤ := by
  classical
  set A := Algebra.adjoin ℂ (Set.range J.t)
  have key : ∀ k, ∀ ν : Idx I n, ∑ i, ν.1 i = k → J.b ν ∈ A := by
    intro k
    induction k with
    | zero =>
      intro ν hν
      have : ν = ⟨0, by simp⟩ :=
        Subtype.ext (funext fun i ↦ (Finset.sum_eq_zero_iff.1 hν) i (Finset.mem_univ i))
      rw [this, J.one]; exact A.one_mem
    | succ k ih =>
      intro ν hν
      obtain ⟨i, hi⟩ : ∃ i, ν.1 i ≠ 0 := by
        by_contra h; push_neg at h; simp [h] at hν
      let ν' : Idx I n := ⟨ν.1 - Pi.single i 1,
        le_trans (Finset.sum_le_sum fun l _ ↦ Nat.sub_le (ν.1 l) _) ν.2⟩
      have hsum : ν.1 = Pi.single i 1 + ν'.1 := by
        funext l
        by_cases hl : l = i
        · subst hl; simp [ν']; omega
        · simp [ν', hl]
      have hν' : ∑ l, ν'.1 l = k := by
        have : ∑ l, ν.1 l = ∑ l, (Pi.single i 1 : I → ℕ) l + ∑ l, ν'.1 l := by
          rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun l _ ↦ congrFun hsum l
        simp at this; omega
      have hmul := J.mul ⟨Pi.single i 1, by simp⟩ ν'
      have hle : ∑ l, ((Pi.single i 1 : I → ℕ) + ν'.1) l ≤ n + 1 := by rw [← hsum]; exact ν.2
      rw [dif_pos hle] at hmul
      have hprod : ∏ l, (((Pi.single i 1 : I → ℕ) l + ν'.1 l).choose ((Pi.single i 1 : I → ℕ) l)) = ν.1 i := by
        rw [Finset.prod_eq_single i]
        · simp [ν']; omega
        · intro l _ hl; simp [hl]
        · simp
      have hb : J.b ⟨(Pi.single i 1 : I → ℕ) + ν'.1, hle⟩ = J.b ν := congrArg J.b (Subtype.ext hsum.symm)
      simp only [Pi.add_apply] at hmul
      rw [hprod, hb] at hmul
      have hne : (ν.1 i : ℂ) ≠ 0 := by exact_mod_cast hi
      have : J.b ν = (ν.1 i : ℂ)⁻¹ • (J.t i * J.b ν') := by
        rw [JetRing.t, hmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact A.smul_mem (A.mul_mem (Algebra.subset_adjoin ⟨i, rfl⟩) (ih ν' hν')) _
  rw [eq_top_iff]
  intro x _
  have hle : Submodule.span ℂ (Set.range J.b) ≤ Subalgebra.toSubmodule A :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun ν ↦ key _ ν rfl)
  exact hle (J.b.mem_span x)

theorem analyticAt_eval {I : Type} [Fintype I] (Q : MvPolynomial I ℂ) (x : I → ℂ) :
    AnalyticAt ℂ (fun z ↦ MvPolynomial.eval z Q) x := by
  induction Q using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => exact (hp.add hq).congr (Filter.Eventually.of_forall fun z ↦ by simp)
  | mul_X p i hp =>
    exact (hp.mul ((ContinuousLinearMap.proj i : (I → ℂ) →L[ℂ] ℂ).analyticAt x)).congr
      (Filter.Eventually.of_forall fun z ↦ by simp)

variable {I : Type} [Fintype I] {n : ℕ}

theorem pi_jet (hC : JetCalc) (J : JetRing ℂ I n) (f : (I → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    J.π (jet J f) = f 0 := by
  rw [J.π_eq]
  exact (hC I n J).1 f hf ⟨0, by simp⟩ [] (by simp)

theorem jet_eval (hC : JetCalc) (J : JetRing ℂ I n) (Q : MvPolynomial I ℂ) :
    jet J (fun z ↦ MvPolynomial.eval z Q) = MvPolynomial.aeval J.t Q := by
  obtain ⟨-, h2, -, h4, h5, -⟩ := hC I n J
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, ← h4 a]
    congr 1; funext z; simp
  | add p q hp hq =>
    rw [map_add, ← hp, ← hq, ← (h2 _ _ (analyticAt_eval p 0) (analyticAt_eval q 0)).2]
    congr 1; funext z; simp
  | mul_X p i hp =>
    rw [map_mul, ← hp, MvPolynomial.aeval_X, ← h5 i,
      ← (h2 _ (fun z ↦ z i) (analyticAt_eval p 0)
        ((ContinuousLinearMap.proj i : (I → ℂ) →L[ℂ] ℂ).analyticAt 0)).1]
    congr 1; funext z; simp

def piAlg (hC : JetCalc) (J : JetRing ℂ I n) : J.B →ₐ[ℂ] ℂ :=
  { J.π with
    commutes' := fun a ↦ by
      show J.π (algebraMap ℂ J.B a) = a
      rw [← (hC I n J).2.2.2.1 a]
      exact pi_jet hC J _ analyticAt_const }

end GlobalTheory.LatJet.An.HolLiftProof

namespace GlobalTheory.LatJet.An.HolLiftProof

open GlobalTheory.AffinePoints

variable {I : Type} [Fintype I] {n : ℕ}

theorem isUnit_of_pi_ne_zero (J : JetRing ℂ I n) (x : J.B) (hx : J.π x ≠ 0) : IsUnit x := by
  obtain ⟨N, hN⟩ := ker_nil I n J
  set a := J.π x
  have hr : algebraMap ℂ J.B a⁻¹ * x - 1 ∈ RingHom.ker J.π := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_one]
    have : J.π (algebraMap ℂ J.B a⁻¹) = a⁻¹ := by
      rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, J.b.repr_self]
      simp
    rw [this, inv_mul_cancel₀ hx, sub_self]
  have hnil : IsNilpotent (algebraMap ℂ J.B a⁻¹ * x - 1) := by
    refine ⟨N, ?_⟩
    have := Ideal.pow_mem_pow hr N
    rw [hN] at this
    simpa using this
  have hx' : x = algebraMap ℂ J.B a * (1 + (algebraMap ℂ J.B a⁻¹ * x - 1)) := by
    rw [add_sub_cancel, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx, map_one, one_mul]
  rw [hx']
  exact ((IsUnit.mk0 a hx).map (algebraMap ℂ J.B)).mul hnil.isUnit_one_add

theorem holLift_std (hC : JetCalc) (B : Type) [CommRing B] [Algebra ℂ B] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d ℂ B] (J : JetRing ℂ I n) (j : B →ₐ[ℂ] J.B) :
    ∃ (U : Set (I → ℂ)) (y : (I → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen U ∧ 0 ∈ U ∧
      (∀ b, DifferentiableOn ℂ (fun z ↦ y z b) U) ∧ ∀ b, j b = jet J fun z ↦ y z b := by
  classical
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d ℂ B
  let p : B →ₐ[ℂ] ℂ := (piAlg hC J).comp j
  obtain ⟨e, hp, he, han⟩ := GlobalTheory.AffinePoints.exists_chart_of_etale g hg p
  have hsurj : ∀ c : J.B, ∃ Q : MvPolynomial I ℂ, MvPolynomial.aeval J.t Q = c := fun c ↦ by
    have : c ∈ Algebra.adjoin ℂ (Set.range J.t) := by rw [adjoin_top]; trivial
    rw [Algebra.adjoin_range_eq_range_aeval] at this
    exact this
  choose Q hQ using fun k : Fin d ↦ hsurj (j (g (MvPolynomial.X k)))
  let w : (I → ℂ) → Fin d → ℂ := fun z k ↦ MvPolynomial.eval z (Q k)
  have hwan : ∀ x, AnalyticAt ℂ w x := fun x ↦ analyticAt_pi_iff.2 fun k ↦ analyticAt_eval (Q k) x
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun x ↦ (hwan x).continuousAt
  have hw0 : w 0 = e p := by
    funext k
    rw [he, GlobalTheory.AffinePoints.coords_apply]
    show MvPolynomial.eval 0 (Q k) = J.π (j (g (MvPolynomial.X k)))
    rw [← hQ k, ← jet_eval hC J, pi_jet hC J _ (analyticAt_eval _ 0)]
  let U : Set (I → ℂ) := w ⁻¹' e.target
  have hU : IsOpen U := e.open_target.preimage hwc
  have h0U : (0 : I → ℂ) ∈ U := by
    show w 0 ∈ e.target
    rw [hw0]; exact e.map_source hp
  let y : (I → ℂ) → (B →ₐ[ℂ] ℂ) := fun z ↦ e.symm (w z)
  have hyan : ∀ b, ∀ z ∈ U, AnalyticAt ℂ (fun z ↦ y z b) z := fun b z hz ↦
    (han b (w z) hz).comp (hwan z)
  obtain ⟨-, hmul, hloc, hconst, -⟩ := hC I n J
  let ψ : B →ₐ[ℂ] J.B :=
    { toFun := fun b ↦ jet J fun z ↦ y z b
      map_one' := by
        show (jet J fun z ↦ y z 1) = 1
        rw [show (fun z ↦ y z 1) = fun _ ↦ (1 : ℂ) from funext fun z ↦ map_one _, hconst, map_one]
      map_mul' := fun a b ↦ by
        show (jet J fun z ↦ y z (a * b)) = (jet J fun z ↦ y z a) * jet J fun z ↦ y z b
        rw [show (fun z ↦ y z (a * b)) = (fun z ↦ y z a) * (fun z ↦ y z b) from
          funext fun z ↦ map_mul _ _ _]
        exact (hmul _ _ (hyan a 0 h0U) (hyan b 0 h0U)).1
      map_zero' := by
        show (jet J fun z ↦ y z 0) = 0
        rw [show (fun z ↦ y z 0) = fun _ ↦ (0 : ℂ) from funext fun z ↦ map_zero _, hconst, map_zero]
      map_add' := fun a b ↦ by
        show (jet J fun z ↦ y z (a + b)) = (jet J fun z ↦ y z a) + jet J fun z ↦ y z b
        rw [show (fun z ↦ y z (a + b)) = (fun z ↦ y z a) + (fun z ↦ y z b) from
          funext fun z ↦ map_add _ _ _]
        exact (hmul _ _ (hyan a 0 h0U) (hyan b 0 h0U)).2
      commutes' := fun c ↦ by
        show (jet J fun z ↦ y z (algebraMap ℂ B c)) = algebraMap ℂ J.B c
        rw [show (fun z ↦ y z (algebraMap ℂ B c)) = fun _ ↦ c from
          funext fun z ↦ AlgHom.commutes _ _, hconst] }
  have hψ : ∀ b, ψ b = jet J fun z ↦ y z b := fun b ↦ rfl
  have hcoord : ψ.comp g = j.comp g := by
    apply MvPolynomial.algHom_ext
    intro k
    show (jet J fun z ↦ y z (g (MvPolynomial.X k))) = j (g (MvPolynomial.X k))
    rw [← hQ k, ← jet_eval hC J]
    apply hloc
    filter_upwards [hU.mem_nhds h0U] with z hz
    have := congrFun (e.right_inv hz) k
    rw [he, GlobalTheory.AffinePoints.coords_apply] at this
    exact this
  have hres : ∀ b, J.π (j b) = J.π (ψ b) := fun b ↦ by
    rw [hψ, pi_jet hC J _ (hyan b 0 h0U)]
    show J.π (j b) = e.symm (w 0) b
    rw [hw0, e.left_inv hp]
    rfl
  letI : Algebra (MvPolynomial (Fin d) ℂ) B := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) ℂ) B := hg
  letI : Algebra (MvPolynomial (Fin d) ℂ) J.B := (j.comp g).toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin d) ℂ] J.B := { j.toRingHom with commutes' := fun _ ↦ rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin d) ℂ] J.B :=
    { ψ.toRingHom with commutes' := fun q ↦ AlgHom.congr_fun hcoord q }
  have h12 : ψ₁ = ψ₂ := Algebra.FormallyUnramified.ext' J.π (ker_nil I n J) ψ₁ ψ₂ hres
  refine ⟨U, y, hU, h0U, fun b z hz ↦ (hyan b z hz).differentiableAt.differentiableWithinAt, fun b ↦ ?_⟩
  exact AlgHom.congr_fun h12 b

theorem holLift (hC : JetCalc) : HolLift := by
  intro B _ _ _ I _ n J j
  classical
  let p : B →ₐ[ℂ] ℂ := (piAlg hC J).comp j
  haveI := RingHom.ker_isPrime p
  obtain ⟨s, hs, ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth ℂ (RingHom.ker p)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension ℂ (Localization.Away s) :=
    P.isStandardSmoothOfRelativeDimension rfl
  have hu : IsUnit (j s) := isUnit_of_pi_ne_zero J _ hs
  let j' : Localization.Away s →ₐ[ℂ] J.B := IsLocalization.Away.liftAlgHom s hu
  obtain ⟨U, y', hU, h0U, hd, hj⟩ := holLift_std hC (Localization.Away s) P.dimension J j'
  refine ⟨U, fun z ↦ (y' z).comp (IsScalarTower.toAlgHom ℂ B (Localization.Away s)), hU, h0U,
    fun b ↦ hd _, fun b ↦ ?_⟩
  show j b = jet J fun z ↦ y' z (algebraMap B (Localization.Away s) b)
  rw [← hj]
  simp [j']

end GlobalTheory.LatJet.An.HolLiftProof

theorem GlobalTheory.LatJet.An.holLift_of_jetCalc : JetCalc → HolLift := GlobalTheory.LatJet.An.HolLiftProof.holLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyTorsionGeneratorPowerStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_torsion_generator_power : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB →
    ∀ (P : Out.PolAV (Sp ℂ)) (ψ : A ⟶ P.A) (ρ : P.A ⟶ A) (N : ℕ), IsMonHom ψ → IsMonHom ρ →
      ψ ≫ ρ = (𝟙 A) ^ N → ρ ≫ ψ = (𝟙 P.A) ^ N →
      LBIso (abelian₂ A M) ((abelian₂ P.A P.L).pull (lift (fst A A ≫ ψ) (snd A A ≫ ψ)).left) →
    ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), HasGen ((abelian₂ A M).pull (lift (fst A T) (snd A T ≫ x)).left) → x ^ (N * N) = 1 := by
  first | exact @GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial | exact GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial | (intros; apply GlobalTheory.KillSquare.pow_sq_eq_one_of_lam_trivial <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedFDerivCompCongr
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical Topology ContDiff

namespace GlobalTheory.LatJet.An.Chain

variable {I : Type} [Fintype I]

theorem iterD_ofFn {f : (I → ℂ) → ℂ} {U : Set (I → ℂ)} (hU : IsOpen U) (hf : ContDiffOn ℂ ω f U) :
    ∀ (k : ℕ) (s : Fin k → I), ∀ z ∈ U,
      iterD (List.ofFn s) f z = iteratedFDeriv ℂ k f z (fun a => Pi.single (s a) 1) := by
  intro k
  induction k with
  | zero => intro s z _; simp [iterD]
  | succ k ih =>
    intro s z hz
    have hev : iterD (List.ofFn (Fin.tail s)) f =ᶠ[𝓝 z]
        fun w => iteratedFDeriv ℂ k f w (fun a => Pi.single (Fin.tail s a) 1) :=
      Filter.eventually_of_mem (hU.mem_nhds hz) (ih (Fin.tail s))
    have hd : DifferentiableAt ℂ (iteratedFDeriv ℂ k f) z :=
      (((hf.contDiffAt (hU.mem_nhds hz)).iteratedFDeriv_right (m := 1) (i := k) le_top)).differentiableAt one_ne_zero
    have e1 : iterD (List.ofFn s) f z = partialD (s 0) (iterD (List.ofFn (Fin.tail s)) f) z := by
      rw [List.ofFn_succ]; rfl
    rw [e1, partialD, hev.lineDeriv_eq, (hd.continuousMultilinear_apply_const _).lineDeriv_eq_fderiv,
      fderiv_continuousMultilinear_apply_const_apply hd, iteratedFDeriv_succ_apply_left]
    rfl

theorem iterD_ofFn_zero {f : (I → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (k : ℕ) (s : Fin k → I) :
    iterD (List.ofFn s) f 0 = iteratedFDeriv ℂ k f 0 (fun a => Pi.single (s a) 1) := by
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd
  exact iterD_ofFn Metric.isOpen_ball (hfr.contDiffOn Metric.isOpen_ball.uniqueDiffOn) k s 0
    (Metric.mem_ball_self hr)

theorem sum_count (l : List I) : ∑ i, l.count i = l.length := by
  induction l with
  | nil => simp
  | cons j l ih => simp [List.count_cons, Finset.sum_add_distrib, ih]

theorem prod_get (a : I → ℂ) (l : List I) : ∏ b : Fin l.length, a (l.get b) = ∏ i, a i ^ l.count i := by
  rw [show (∏ b : Fin l.length, a (l.get b)) = (l.map a).prod by simpa using Fin.prod_univ_fun_getElem l a]
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    simp only [List.count_cons, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_eq_single j (fun b _ hb => by simp [beq_iff_eq, Ne.symm hb]) (by simp)]
    simp

theorem iteratedFDeriv_coord {f : (I → ℂ) → I → ℂ} (hf : ContDiffAt ℂ ω f 0) (k : ℕ) (i : I)
    (m : Fin k → I → ℂ) : iteratedFDeriv ℂ k (fun z => f z i) 0 m = iteratedFDeriv ℂ k f 0 m i := by
  have h := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).iteratedFDeriv_comp_left hf
    (i := k) le_top
  exact congrArg (fun L => L m) h

theorem iteratedFDeriv_comp_clm {f : (I → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (A : (I → ℂ) →L[ℂ] (I → ℂ))
    (k : ℕ) : iteratedFDeriv ℂ k (f ∘ A) 0 = (iteratedFDeriv ℂ k f 0).compContinuousLinearMap fun _ => A := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn (m := (k : WithTop ℕ∞)) le_top (fun _ => rfl)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hs : IsOpen (Metric.ball (0 : I → ℂ) r) := Metric.isOpen_ball
  have h0 : (0 : I → ℂ) ∈ Metric.ball (0 : I → ℂ) r := Metric.mem_ball_self hr
  have hpre : IsOpen (A ⁻¹' Metric.ball (0 : I → ℂ) r) := hs.preimage A.continuous
  have h0' : (0 : I → ℂ) ∈ A ⁻¹' Metric.ball (0 : I → ℂ) r := by simpa using h0
  have key := A.iteratedFDerivWithin_comp_right (hfu.mono hball) hs.uniqueDiffOn hpre.uniqueDiffOn h0'
    (i := k) le_rfl
  rw [iteratedFDerivWithin_of_isOpen k hpre h0', map_zero, iteratedFDerivWithin_of_isOpen k hs h0] at key
  exact key

theorem iteratedFDeriv_comp_congr {g : (I → ℂ) → ℂ} {f₁ f₂ : (I → ℂ) → I → ℂ}
    (hg : ContDiffAt ℂ ω g 0) (h₁ : ContDiffAt ℂ ω f₁ 0) (h₂ : ContDiffAt ℂ ω f₂ 0)
    (e₁ : f₁ 0 = 0) (e₂ : f₂ 0 = 0) (N : ℕ)
    (h : ∀ k ≤ N, iteratedFDeriv ℂ k f₁ 0 = iteratedFDeriv ℂ k f₂ 0) :
    ∀ k ≤ N, iteratedFDeriv ℂ k (g ∘ f₁) 0 = iteratedFDeriv ℂ k (g ∘ f₂) 0 := by
  intro k hk
  rw [iteratedFDeriv_comp (by rw [e₁]; exact hg) h₁ le_top, iteratedFDeriv_comp (by rw [e₂]; exact hg) h₂ le_top, e₁, e₂]
  unfold FormalMultilinearSeries.taylorComp
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : (fun m => ftaylorSeries ℂ f₁ 0 (c.partSize m)) = fun m => ftaylorSeries ℂ f₂ 0 (c.partSize m) :=
    funext fun m => h _ ((c.partSize_le m).trans hk)
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition, hc]

theorem jetChain_of_jetCalc : JetCalc → JetChain := by
  intro hC I _ n J ζ a g hζ hζ0 hg hjet ν u hu
  obtain ⟨h1, h2, -, h4, h5, -, -⟩ := hC I n J
  let Λ : (I → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i => a i • ContinuousLinearMap.proj i
  have hΛ : ∀ z i, Λ z i = a i * z i := fun z i => by simp [Λ]
  have hpr : ∀ i, AnalyticAt ℂ (fun z : I → ℂ => z i) 0 := fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt 0
  have hΛjet : ∀ i, jet J (fun z => Λ z i) = a i • J.t i := by
    intro i
    have e : (fun z : I → ℂ => Λ z i) = (fun _ => a i) * (fun z => z i) := by funext z; simp [hΛ]
    rw [e, (h2 _ _ analyticAt_const (hpr i)).1, h4, h5, Algebra.smul_def]
  have hζi : ∀ i, AnalyticAt ℂ (fun z => ζ z i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt (ζ 0)).comp hζ
  have hΛi : ∀ i, AnalyticAt ℂ (fun z => Λ z i) 0 := fun i =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i).analyticAt (Λ 0)).comp (Λ.analyticAt 0)
  have hD : ∀ i k, k ≤ n + 1 → iteratedFDeriv ℂ k (fun z => ζ z i) 0 = iteratedFDeriv ℂ k (fun z => Λ z i) 0 := by
    intro i k hk
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    refine Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ I) fun s => ?_
    simp only [ContinuousMultilinearMap.coe_coe, Pi.basisFun_apply]
    rw [← iterD_ofFn_zero (hζi i) k s, ← iterD_ofFn_zero (hΛi i) k s]
    have hν : ∑ j, (List.ofFn s).count j ≤ n + 1 := by rw [sum_count, List.length_ofFn]; exact hk
    rw [← h1 _ (hζi i) ⟨_, hν⟩ _ (fun _ => rfl), ← h1 _ (hΛi i) ⟨_, hν⟩ _ (fun _ => rfl), hjet i, hΛjet i]
  have hDv : ∀ k ≤ n + 1, iteratedFDeriv ℂ k ζ 0 = iteratedFDeriv ℂ k Λ 0 := by
    intro k hk
    ext m i
    rw [← iteratedFDeriv_coord hζ.contDiffAt, ← iteratedFDeriv_coord (Λ.analyticAt 0).contDiffAt, hD i k hk]
  have hk : u.length ≤ n + 1 := by
    rw [← sum_count u]; simp only [hu]; exact ν.2
  have hgz : AnalyticAt ℂ (g ∘ ζ) 0 := by
    refine AnalyticAt.comp ?_ hζ
    rw [hζ0]; exact hg
  rw [h1 _ hgz ν u hu]
  have e : ∀ f, iterD u f 0 = iterD (List.ofFn u.get) f 0 := by intro f; rw [List.ofFn_get]
  rw [e, e, iterD_ofFn_zero hgz, iterD_ofFn_zero hg,
    iteratedFDeriv_comp_congr hg.contDiffAt hζ.contDiffAt (Λ.analyticAt 0).contDiffAt hζ0 (map_zero Λ) (n + 1)
      hDv _ hk, iteratedFDeriv_comp_clm hg.contDiffAt]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hv : (fun b : Fin u.length => Λ (Pi.single (u.get b) 1)) = fun b => a (u.get b) • Pi.single (u.get b) 1 := by
    funext b; ext i; rw [hΛ]
    by_cases h : i = u.get b
    · subst h; simp
    · simp only [List.get_eq_getElem] at h; simp [Pi.single_apply, h]
  rw [hv, ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, prod_get, mul_comm]
  simp only [hu]

end GlobalTheory.LatJet.An.Chain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetFiniteLength
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.BirigidLift

theorem lift_div : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ Q₀ S₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → S₀.IsLB → LBIso Q₀ (LB.div S₀ P₀) →
    ∀ (P Q S : LB (A ⊗ A).left), P.IsLB → Q.IsLB → S.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (S.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (S.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso (S.pull l) S₀ → LBIso Q (LB.div S P) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL P₀ Q₀ S₀ hP₀ hQ₀ hS₀ eQ₀ P Q S hP hQ hS
    tP₁ tP₂ tQ₁ tQ₂ tS₁ tS₂ eP eQ eS
  have hd : (LB.div S P).IsLB := LB.isLB_div hS hP
  have triv : ∀ (a b : A ⟶ A), HasGen (S.pull (lift a b).left) → HasGen (P.pull (lift a b).left) →
      GlobalTheory.AbLaw.Triv (ev (LB.div S P) a b) := by
    intro a b t₁ t₂
    rw [triv_ev_iff hd, evc, cls_div hS hP hd, map_sub]
    have z₁ := (cls_eq_zero_iff (pull_isLB hS (lift a b).left)).2 t₁
    have z₂ := (cls_eq_zero_iff (pull_isLB hP (lift a b).left)).2 t₂
    rw [cls_pull hS] at z₁
    rw [cls_pull hP] at z₂
    rw [z₁, z₂, sub_zero]
  have red : LBIso ((LB.div S P).pull l) Q₀ := by
    refine (cls_eq_iff (pull_isLB hd l) hQ₀).1 ?_
    rw [cls_pull hd, cls_div hS hP hd, map_sub, ← cls_pull hS l (pull_isLB hS l), ← cls_pull hP l (pull_isLB hP l),
      (cls_eq_iff (pull_isLB hS l) hS₀).2 eS, (cls_eq_iff (pull_isLB hP l) hP₀).2 eP,
      (cls_eq_iff hQ₀ (LB.isLB_div hS₀ hP₀)).2 eQ₀, cls_div hS₀ hP₀]
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h hl.1 hl.2 hL aL hL aL hQ₀ hQ tQ₁ tQ₂ eQ hd
    (triv _ _ tS₁ tP₁) (triv _ _ tS₂ tP₂) red

end GlobalTheory.BirigidLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_group_morphism_base_change : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))), m.IsBC := by
  first | exact @GlobalTheory.LatJet.isBC_jetRing | exact GlobalTheory.LatJet.isBC_jetRing | (intros; apply GlobalTheory.LatJet.isBC_jetRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingProdEqFactorialSmulStatement
section
open GlobalTheory.LatJet
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_prod_eq_factorial_smul : ∀ {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (l : List I) (hc : ∑ i, l.count i ≤ n + 1), (l.map J.t).prod = ((∏ i, (l.count i).factorial : ℕ) : R) • J.b ⟨fun i => l.count i, hc⟩ := by
  first | exact @GlobalTheory.LatJet.prod_map_t_eq_smul_b | exact GlobalTheory.LatJet.prod_map_t_eq_smul_b | (intros; apply GlobalTheory.LatJet.prod_map_t_eq_smul_b <;> assumption)
end

