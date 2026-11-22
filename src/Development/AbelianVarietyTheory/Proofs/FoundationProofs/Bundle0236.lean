import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.GenusOneDatum

open PowerSeries in

theorem exists_fixed_of_contract {R : Type*} [CommRing R] (T : PowerSeries R → PowerSeries R)
    (hT : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ x - y → X ^ (n + 1) ∣ T x - T y) :
    ∃ x, T x = x := by
  have hit : ∀ (n : ℕ) (x y : PowerSeries R), X ^ n ∣ T^[n] x - T^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x y
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hT n _ _ (ih x y)
  let L : PowerSeries R := PowerSeries.mk fun n => coeff n (T^[n + 1] 0)
  have hL : ∀ n, X ^ n ∣ L - T^[n] 0 := by
    intro n
    rw [X_pow_dvd_iff]
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, n = (m + 1) + k := ⟨n - (m + 1), by omega⟩
    have := X_pow_dvd_iff.1 (hit (m + 1) 0 (T^[k] 0)) m (by omega)
    rw [← Function.iterate_add_apply] at this
    simpa [L] using this
  refine ⟨L, ?_⟩
  ext n
  have h1 := hT n _ _ (hL n)
  have h2 := hL (n + 1)
  rw [Function.iterate_succ_apply'] at h2
  have h3 := dvd_sub h1 h2
  have h4 := X_pow_dvd_iff.1 h3 n (by omega)
  rw [sub_sub_sub_cancel_right, map_sub, sub_eq_zero] at h4
  exact h4

theorem exists_isWq {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) : ∃ wq, IsWq W wq := by
  let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
  let X := (PowerSeries.X : PowerSeries ℂ_[p])
  obtain ⟨w, hw⟩ := exists_fixed_of_contract (fun wq : PowerSeries ℂ_[p] =>
    1 + c W.a₁ * X * wq + c W.a₂ * X ^ 2 * wq + c W.a₃ * X ^ 3 * wq ^ 2 +
    c W.a₄ * X ^ 4 * wq ^ 2 + c W.a₆ * X ^ 6 * wq ^ 3) (by
      rintro n x y ⟨z, hz⟩
      refine ⟨z * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2)), ?_⟩
      have hz' : x - y = X ^ n * z := hz
      change _ = X ^ (n + 1) * _
      linear_combination (X * (c W.a₁ + c W.a₂ * X + (c W.a₃ * X ^ 2 + c W.a₄ * X ^ 3) * (x + y) +
        c W.a₆ * X ^ 5 * (x ^ 2 + x * y + y ^ 2))) * hz')
  exact ⟨w, hw.symm⟩

theorem constantCoeff_of_isWq {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.constantCoeff wq = 1 := by
  have h' := congrArg PowerSeries.constantCoeff h
  simpa using h'

theorem coeff_one_flog {p : ℕ} [Fact p.Prime] {W : WeierstrassCurve ℂ_[p]}
    {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) : PowerSeries.coeff 1 (flog W wq) = 1 := by
  have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  simp [flog, omegaW, PowerSeries.constantCoeff_inv, constantCoeff_of_isWq h, h2]

theorem constantCoeff_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : PowerSeries.constantCoeff (flog W wq) = 0 := by
  simp [flog]

theorem exists_subst_eq_X {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1) :
    ∃ ex : PowerSeries R, PowerSeries.constantCoeff ex = 0 ∧
      PowerSeries.subst ex l = PowerSeries.X := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, -⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h ()⟩

theorem exists_genusOne_datum : ∀ (D : D7), GL3Theta.modelEx D → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → Nat.Coprime (Ideal.absNorm cc) p → ∃ g : GL3Theta.G1 p, GL3Theta.At D cc δ g ∧ g.lam = lam ∧ ‖((g.C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1 := by
  intro D hm p _ lam cc δ hc hcop
  obtain ⟨⟨C, hC⟩, -, hu⟩ := hm p lam cc δ hc.1 hcop hc.2
  obtain ⟨wq, hwq⟩ := exists_isWq (C • wModel lam (lamOf D cc δ))
  obtain ⟨ex, he0, he⟩ := exists_subst_eq_X _ (constantCoeff_flog _ wq) (coeff_one_flog hwq)
  exact ⟨⟨lam, lamOf D cc δ, C, wq, ex⟩, ⟨hc.1, hcop, hc.2, rfl, hC, hwq, he0, he⟩, rfl, hu C hC⟩

end GlobalTheory.GenusOneDatum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGeneratorPowFractionalIdealNonarchSize
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem nonarch_le_pow_of_mem_ideal_pow {K : Type} [Field K] [NumberField K] (J : Ideal (𝓞 K))
    (v : K →*₀ ℝ) (h0 : ∀ x, 0 ≤ v x) (hadd : ∀ x y, v (x + y) ≤ max (v x) (v y))
    (hint : ∀ c : 𝓞 K, v (c : K) ≤ 1) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ J, v (y : K) ≤ M) (k : ℕ) : ∀ y ∈ J ^ k, v (y : K) ≤ M ^ k := by
  induction k with
  | zero => intro y _; simpa using hint y
  | succ k ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      have : ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := by simp
      rw [this, map_mul, pow_succ]
      exact mul_le_mul (ih a ha) (hM b hb) (h0 _) (pow_nonneg hM0 _)
    · intro a b ha hb
      have : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
      rw [this]
      exact (hadd _ _).trans (max_le ha hb)

theorem exists_generator_pow_fractional_size : ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K), I ≠ ⊥ → (∃ n : ℕ, 0 < n ∧ ∀ x ∈ I, (n : K) * x ∈ (algebraMap (𝓞 K) K).range) → ∃ (h : ℕ) (α : K), 0 < h ∧ α ≠ 0 ∧ ∀ v : K →*₀ ℝ, (∀ x, 0 ≤ v x) → (∀ x y, v (x + y) ≤ max (v x) (v y)) → (∀ c : 𝓞 K, v (c : K) ≤ 1) → ∀ x₀ ∈ I, (∀ x ∈ I, v x ≤ v x₀) → v α = v x₀ ^ h := by
  intro K _ _ I hI ⟨n, hn, hnI⟩
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let J : Ideal (𝓞 K) :=
    { carrier := {c | ∃ x ∈ I, (c : K) = (n : K) * x}
      zero_mem' := ⟨0, I.zero_mem, by simp⟩
      add_mem' := by
        rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        refine ⟨x + y, I.add_mem hx hy, ?_⟩
        have : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by simp
        rw [this, ha, hb]; ring
      smul_mem' := by
        rintro c a ⟨x, hx, ha⟩
        refine ⟨c • x, I.smul_mem c hx, ?_⟩
        have : ((c • a : 𝓞 K) : K) = (c : K) * (a : K) := by simp
        have h2 : c • x = (c : K) * x := Algebra.smul_def c x
        rw [this, ha, h2]; ring }
  have hmem : ∀ x ∈ I, ∃ c ∈ J, (c : K) = (n : K) * x := by
    intro x hx
    obtain ⟨c, hc⟩ := hnI x hx
    exact ⟨c, ⟨x, hx, hc⟩, hc⟩
  have hJ : J ≠ 0 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨c, hc, hcx⟩ := hmem x hx
    intro h
    rw [h] at hc
    have : c = 0 := by simpa using hc
    rw [this] at hcx
    exact mul_ne_zero hnK hx0 (by simpa using hcx.symm)
  have hJ' : J ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hJ
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hpos : 0 < h := Fintype.card_pos
  have hprin : (J ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨J, hJ'⟩ ^ h : nonZeroDivisors (Ideal (𝓞 K))) = 1 := by
      rw [map_pow]; exact pow_card_eq_one
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hJ' h)).mp h1
  obtain ⟨a, ha⟩ := hprin
  have ha0 : a ≠ 0 := by
    intro h0
    apply pow_ne_zero h hJ
    rw [ha, h0]; simp
  have haK : (a : K) ≠ 0 := by simpa using ha0
  refine ⟨h, (a : K) / (n : K) ^ h, hpos, div_ne_zero haK (pow_ne_zero _ hnK), ?_⟩
  intro v h0 hadd hint x₀ hx₀ hmax
  have hvn : v (n : K) ≠ 0 := (map_ne_zero v).mpr hnK
  have hM : ∀ y ∈ J, v (y : K) ≤ v (n : K) * v x₀ := by
    rintro y ⟨x, hx, hy⟩
    rw [hy, map_mul]
    exact mul_le_mul_of_nonneg_left (hmax x hx) (h0 _)
  have h1 : v (a : K) ≤ (v (n : K) * v x₀) ^ h :=
    nonarch_le_pow_of_mem_ideal_pow J v h0 hadd hint _ (mul_nonneg (h0 _) (h0 _)) hM h a
      (by rw [ha]; exact Submodule.mem_span_singleton_self a)
  have h2 : (v (n : K) * v x₀) ^ h ≤ v (a : K) := by
    obtain ⟨c, hc, hcx⟩ := hmem x₀ hx₀
    have hch : c ^ h ∈ J ^ h := Ideal.pow_mem_pow hc h
    rw [ha] at hch
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hch
    have hd' : (d : K) * (a : K) = (c : K) ^ h := by
      have := congrArg (algebraMap (𝓞 K) K) hd
      simpa using this
    rw [← map_mul, ← hcx, ← map_pow, ← hd', map_mul]
    exact mul_le_of_le_one_left (h0 _) (hint d)
  rw [map_div₀, map_pow, le_antisymm h1 h2, mul_pow]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHighestWeightVectorOfKStable
section
open Formalism.BasicNotions.TH

namespace GlobalTheory.ExistsHW

open GlobalTheory.TensorHW

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma inf_eig_ne_bot_iff (f : Module.End ℂ V) (N : Submodule ℂ V) (hf : ∀ x ∈ N, f x ∈ N) (t : ℂ) :
    N ⊓ f.eigenspace t ≠ ⊥ ↔ Module.End.HasEigenvalue (f.restrict hf) t := by
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, hx0⟩
    refine ⟨⟨x, hx1⟩, ?_, fun h => hx0 (congrArg Subtype.val h)⟩
    rw [Module.End.mem_eigenspace_iff]
    exact Subtype.ext (Module.End.mem_eigenspace_iff.1 hx2)
  · rintro ⟨x, hx, hx0⟩
    refine ⟨x, ⟨x.2, ?_⟩, fun h => hx0 (Subtype.ext h)⟩
    rw [Module.End.mem_eigenspace_iff] at hx
    exact Module.End.mem_eigenspace_iff.2 (congrArg Subtype.val hx)

lemma exists_eig (f : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N] (hN : N ≠ ⊥)
    (hf : ∀ x ∈ N, f x ∈ N) : ∃ t, N ⊓ f.eigenspace t ≠ ⊥ := by
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue (f.restrict hf)
  exact ⟨t, (inf_eig_ne_bot_iff f N hf t).2 ht⟩

lemma finite_eig (f : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N]
    (hf : ∀ x ∈ N, f x ∈ N) : {t | N ⊓ f.eigenspace t ≠ ⊥}.Finite := by
  simp only [inf_eig_ne_bot_iff f N hf]
  exact Module.End.finite_hasEigenvalue _

lemma exists_common {ι : Type*} (E : ι → Module.End ℂ V) (hE : ∀ a b x, E a (E b x) = E b (E a x))
    (N : Submodule ℂ V) [FiniteDimensional ℂ N] (hN : N ≠ ⊥) (hst : ∀ a, ∀ x ∈ N, E a x ∈ N)
    (s : Finset ι) : ∃ N' : Submodule ℂ V, N' ≤ N ∧ N' ≠ ⊥ ∧ (∀ a, ∀ x ∈ N', E a x ∈ N') ∧
      ∀ a ∈ s, ∃ t, N' ≤ (E a).eigenspace t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨N, le_rfl, hN, hst, by simp⟩
  | insert b s _ ih =>
    obtain ⟨N', h1, h2, h3, h4⟩ := ih
    haveI : FiniteDimensional ℂ N' := Submodule.finiteDimensional_of_le h1
    obtain ⟨t, ht⟩ := exists_eig (E b) N' h2 (h3 b)
    refine ⟨N' ⊓ (E b).eigenspace t, inf_le_left.trans h1, ht, ?_, ?_⟩
    · rintro a x ⟨hx1, hx2⟩
      refine ⟨h3 a x hx1, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [hE, Module.End.mem_eigenspace_iff.1 hx2, map_smul]
    · intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact ⟨t, inf_le_right⟩
      · obtain ⟨u, hu⟩ := h4 a ha
        exact ⟨u, inf_le_left.trans hu⟩

end General

lemma eig_rat {p q : ℕ} (M : GKMod p q) (a : Ix p q) {t : ℂ} {v : M.V} (hv0 : v ≠ 0)
    (hv : v ∈ (M.act (Eab a a)).eigenspace t) : ∃ r : ℚ, (r : ℂ) = t := by
  by_contra hr
  have hd := Module.End.eigenspaces_iSupIndep (M.act (Eab a a)) t
  have hle : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
      ⨆ (j : ℂ) (_ : j ≠ t), (M.act (Eab a a)).eigenspace j := by
    refine iSup_le fun μ => le_iSup₂_of_le ((μ a : ℚ) : ℂ) (fun h => hr ⟨μ a, h⟩) fun x hx => ?_
    exact Module.End.mem_eigenspace_iff.2 (mem_wt.1 hx a)
  exact hv0 (Submodule.disjoint_def.1 hd v hv (hle (M.wts v)))

theorem exists_highestWeight (p q : ℕ) (M : GKMod p q) (W : Submodule ℂ M.V)
    (hfd : FiniteDimensional ℂ W) (hW : KStable M.act W) (h0 : W ≠ ⊥) :
    ∃ (μ : Ix p q → ℚ) (v : M.V), v ∈ W ∧ IsHW M.act μ v := by
  have hL : Formalism.MainNotions.SchurIrreducible.IsKLieAct M.act := fun X Y _ _ => M.lie X Y
  set c : Ix p q → ℂ := fun a => (grad p q a : ℂ) with hc
  set H : Module.End ℂ M.V := M.act (Matrix.diagonal c) with hH
  have hHW : ∀ x ∈ W, H x ∈ W := hW _ (isKC_diag c)
  obtain ⟨t, ht, hmax⟩ := Set.exists_max_image _ Complex.re (finite_eig H W hHW)
    (exists_eig H W h0 hHW)
  set N := W ⊓ H.eigenspace t with hN
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le inf_le_left
  have hkill : ∀ a b, posC a b → ∀ x ∈ N, M.act (Eab a b) x = 0 := by
    intro a b hab x hx
    by_contra hne
    have := hmax (t + (c a - c b)) ((Submodule.ne_bot_iff _).2 ⟨_,
      ⟨hW _ (isKC_Eab (same_of_pos hab)) x hx.1, eig_shift hL c (same_of_pos hab) hx.2⟩, hne⟩)
    simp only [hc, Complex.add_re, Complex.sub_re, Complex.ofReal_re] at this
    linarith [grad_lt hab]
  have hst : ∀ a, ∀ x ∈ N, M.act (Eab a a) x ∈ N := by
    intro a x hx
    refine ⟨hW _ (isKC_Eab (same_refl a)) x hx.1, ?_⟩
    have := eig_shift hL c (same_refl a) hx.2
    rwa [sub_self, add_zero] at this
  have hcomm : ∀ a b x, M.act (Eab a a) (M.act (Eab b b) x) = M.act (Eab b b) (M.act (Eab a a) x) := by
    intro a b x
    rw [lie_apply hL (isKC_Eab (same_refl a)) (isKC_Eab (same_refl b))]
    have : (Eab a a * Eab b b - Eab b b * Eab a a : Mat p q) = 0 := by
      by_cases hab : a = b
      · rw [hab, sub_self]
      · rw [Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ hab,
          Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hab), sub_self]
    rw [this, map_zero, LinearMap.zero_apply, add_zero]
  obtain ⟨N', h1, h2, -, h4⟩ := exists_common (fun a => M.act (Eab a a)) hcomm N ht hst Finset.univ
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h2
  have : ∀ a, ∃ r : ℚ, M.act (Eab a a) v = (r : ℂ) • v := by
    intro a
    obtain ⟨u, hu⟩ := h4 a (Finset.mem_univ a)
    obtain ⟨r, rfl⟩ := eig_rat M a hv0 (hu hv)
    exact ⟨r, Module.End.mem_eigenspace_iff.1 (hu hv)⟩
  choose μ hμ using this
  exact ⟨μ, v, (h1 hv).1, hv0, mem_hw.2 ⟨hμ, fun a b hab => hkill a b hab v (h1 hv)⟩⟩

end GlobalTheory.ExistsHW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMatrixUnitStableSubspaceOfExtremal
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.ExtremalGen

open GlobalTheory.TensorHW (mem_wt diag_comm)

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def Supp (S : Ix p q → Ix p q → Prop) (Z : Mat p q) : Prop := ∀ a b, ¬ S a b → Z a b = 0

lemma supp_Eab {S : Ix p q → Ix p q → Prop} {a b : Ix p q} (h : S a b) : Supp S (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd h

lemma supp_mul {S : Ix p q → Ix p q → Prop} (hS : Equivalence S) {Y Z : Mat p q}
    (hY : Supp S Y) (hZ : Supp S Z) : Supp S (Y * Z) := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hac : S a c
  · rw [hZ c b (fun hcb => hab (hS.trans hac hcb)), mul_zero]
  · rw [hY a c hac, zero_mul]

lemma supp_comm {S : Ix p q → Ix p q → Prop} (hS : Equivalence S) {Y Z : Mat p q}
    (hY : Supp S Y) (hZ : Supp S Z) : Supp S (Y * Z - Z * Y) := by
  intro a b hab
  rw [Matrix.sub_apply, supp_mul hS hY hZ a b hab, supp_mul hS hZ hY a b hab, sub_zero]

lemma supp_ind {S : Ix p q → Ix p q → Prop} (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (N : Submodule ℂ V) (y : V)
    (h : ∀ a b, S a b → act (Eab a b) y ∈ N) {Z : Mat p q} (hZ : Supp S Z) : act Z y ∈ N := by
  rw [Matrix.matrix_eq_sum_single Z]
  simp only [map_sum, LinearMap.sum_apply]
  refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
  by_cases hab : S a b
  · have : (Matrix.single a b (Z a b) : Mat p q) = Z a b • Eab a b := by
      rw [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (h a b hab)
  · rw [hZ a b hab]
    simp

lemma lie_apply {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (Y Z : Mat p q) (y : V) :
    act Y (act Z y) = act Z (act Y y) + act (Y * Z - Z * Y) y := by
  rw [hL Y Z]
  simp

lemma eig_shift {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (hL : IsLieAct act) (c : Ix p q → ℂ)
    (a b : Ix p q) {t : ℂ} {y : V}
    (hy : y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) t) :
    act (Eab a b) y ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (t + (c a - c b)) := by
  rw [Module.End.mem_eigenspace_iff] at hy ⊢
  rw [lie_apply hL, diag_comm, hy, map_smul, map_smul, LinearMap.smul_apply, add_smul]

lemma eig_of_wt {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (c : Ix p q → ℂ) {μ : Ix p q → ℚ} {v : V}
    (hv : v ∈ wtSub act μ) :
    v ∈ Module.End.eigenspace (act (Matrix.diagonal c)) (∑ a, c a * ((μ a : ℚ) : ℂ)) := by
  rw [mem_wt] at hv
  rw [Module.End.mem_eigenspace_iff]
  have : (Matrix.diagonal c : Mat p q) = ∑ a, c a • Eab a a := by
    ext i j
    simp only [Matrix.sum_apply, Eab, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [this]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hv, Finset.sum_smul,
    mul_smul]

theorem exists_generated :
    ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (r : Ix p q → ℕ), Function.Injective r → ∀ (μ : Ix p q → ℚ) (v : V), v ∈ wtSub act μ → (∀ a b, S a b → r a < r b → act (Eab a b) v = 0) → ∃ U : Submodule ℂ V, v ∈ U ∧ (∀ a b, S a b → ∀ x ∈ U, act (Eab a b) x ∈ U) ∧ (∀ U' : Submodule ℂ V, v ∈ U' → (∀ a b, S a b → r a < r b → ∀ x ∈ U', act (Eab b a) x ∈ U') → U ≤ U') ∧ (∀ x ∈ U, x ∈ wtSub act μ → ∃ c : ℂ, x = c • v) ∧ ∀ (ν : Ix p q → ℚ), ∀ x ∈ U, x ≠ 0 → x ∈ wtSub act ν → ν = μ ∨ ∑ a, (r a : ℚ) * μ a < ∑ a, (r a : ℚ) * ν a := by
  intro p q V _ _ act hL S hS r hr μ v hv hup
  have hv' := mem_wt.1 hv
  set F : Set (Submodule ℂ V) :=
    {N | v ∈ N ∧ ∀ a b, S a b → r a < r b → ∀ y ∈ N, act (Eab b a) y ∈ N} with hF
  have hG : sInf F ∈ F := by
    refine ⟨Submodule.mem_sInf.2 fun M hM => hM.1, fun a b hab hlt y hy => ?_⟩
    exact Submodule.mem_sInf.2 fun M hM => hM.2 a b hab hlt y (Submodule.mem_sInf.1 hy M hM)
  have hG' : (sInf F ⊓ ⨅ (Z : Mat p q) (_ : Supp S Z), (sInf F).comap (act Z)) ∈ F := by
    constructor
    · simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
      refine ⟨hG.1, fun Z hZ => supp_ind act _ v (fun a b hab => ?_) hZ⟩
      rcases lt_trichotomy (r a) (r b) with h | h | h
      · rw [hup a b hab h]; exact Submodule.zero_mem _
      · obtain rfl := hr h
        rw [hv']; exact Submodule.smul_mem _ _ hG.1
      · exact hG.2 b a (hS.symm hab) h v hG.1
    · intro a b hab hlt y hy
      simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hy ⊢
      refine ⟨hG.2 a b hab hlt y hy.1, fun Z hZ => ?_⟩
      have hE := supp_Eab (hS.symm hab)
      rw [lie_apply hL]
      exact Submodule.add_mem _ (hG.2 a b hab hlt _ (hy.2 Z hZ)) (hy.2 _ (supp_comm hS hZ hE))
  set c : Ix p q → ℂ := fun a => (r a : ℂ) with hc
  set h : Module.End ℂ V := act (Matrix.diagonal c) with hh
  have hcast : ∀ ν : Ix p q → ℚ,
      ∑ a, c a * ((ν a : ℚ) : ℂ) = ((∑ a, (r a : ℚ) * ν a : ℚ) : ℂ) := by
    intro ν; simp [hc]
  have heig : ∀ (ν : Ix p q → ℚ) (x : V), x ∈ wtSub act ν →
      x ∈ h.eigenspace ((∑ a, (r a : ℚ) * ν a : ℚ) : ℂ) := by
    intro ν x hx
    rw [← hcast]; exact eig_of_wt c hx
  set m : ℚ := ∑ a, (r a : ℚ) * μ a with hm
  have hvm : v ∈ h.eigenspace (m : ℂ) := heig μ v hv
  set Q : Submodule ℂ V := ⨆ (t : ℚ) (_ : m < t), h.eigenspace (t : ℂ) with hQ
  have hshift : ∀ a b, r a < r b → ∀ t : ℚ, m ≤ t →
      ∀ y ∈ h.eigenspace (t : ℂ), act (Eab b a) y ∈ Q := by
    intro a b hab t ht y hy
    have h1 := eig_shift hL c b a hy
    have h2 : (t : ℂ) + (c b - c a) = ((t + ((r b : ℚ) - (r a : ℚ)) : ℚ) : ℂ) := by simp [hc]
    rw [h2] at h1
    have h3 : (r a : ℚ) < r b := by exact_mod_cast hab
    exact (le_iSup₂_of_le (f := fun (t : ℚ) (_ : m < t) => h.eigenspace (t : ℂ)) _
      (by linarith) le_rfl : _ ≤ Q) h1
  have hlow : ∀ a b, r a < r b → ∀ y ∈ (ℂ ∙ v) ⊔ Q, act (Eab b a) y ∈ Q := by
    intro a b hab
    have : (ℂ ∙ v) ⊔ Q ≤ Q.comap (act (Eab b a)) := by
      refine sup_le ?_ (iSup₂_le fun t ht y hy => hshift a b hab t ht.le y hy)
      rw [Submodule.span_singleton_le_iff_mem]
      exact hshift a b hab m le_rfl v hvm
    exact this
  have hle : sInf F ≤ (ℂ ∙ v) ⊔ Q :=
    sInf_le ⟨Submodule.mem_sup_left (Submodule.mem_span_singleton_self v),
      fun a b _ hab y hy => Submodule.mem_sup_right (hlow a b hab y hy)⟩
  have hQle : ∀ n : ℚ, n ≤ m → Q ≤ ⨆ (j : ℂ) (_ : j ≠ (n : ℂ)), h.eigenspace j := by
    intro n hn
    refine iSup₂_le fun t ht => le_iSup₂_of_le (t : ℂ) ?_ le_rfl
    intro he
    have : t = n := by exact_mod_cast he
    linarith
  have hline : ∀ x ∈ sInf F, x ∈ h.eigenspace (m : ℂ) → ∃ s : ℂ, x = s • v := by
    intro x hx hxm
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hzm : z ∈ h.eigenspace (m : ℂ) := by
      have := Submodule.sub_mem _ hxm (Submodule.smul_mem _ s hvm)
      simpa using this
    have hz0 : z = 0 :=
      Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep h (m : ℂ)) z hzm
        (hQle m le_rfl hz)
    exact ⟨s, by rw [hz0, add_zero]⟩
  refine ⟨sInf F, hG.1, fun a b hab x hx => ?_, fun U' h1 h2 => sInf_le ⟨h1, h2⟩,
    fun x hx hxμ => hline x hx (heig μ x hxμ), fun ν x hx hx0 hxν => ?_⟩
  · have := sInf_le hG' hx
    simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at this
    exact this.2 _ (supp_Eab hab)
  · have hxn := heig ν x hxν
    set n : ℚ := ∑ a, (r a : ℚ) * ν a with hn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact Or.inr hlt
    · left
      rw [← heq] at hxn
      obtain ⟨s, hs⟩ := hline x hx hxn
      have hxμ : x ∈ wtSub act μ := hs ▸ Submodule.smul_mem _ s hv
      funext a
      have h1 := mem_wt.1 hxν a
      rw [mem_wt.1 hxμ a] at h1
      have h2 := smul_left_injective ℂ hx0 h1
      exact_mod_cast h2.symm
    · exfalso
      apply hx0
      refine Submodule.disjoint_def.1 (Module.End.eigenspaces_iSupIndep h (n : ℂ)) x hxn ?_
      refine (sup_le ?_ (hQle n hgt.le) : (ℂ ∙ v) ⊔ Q ≤ _) (hle hx)
      rw [Submodule.span_singleton_le_iff_mem]
      have hne : (m : ℂ) ≠ (n : ℂ) := by exact_mod_cast hgt.ne'
      exact (le_iSup₂_of_le (f := fun (j : ℂ) (_ : j ≠ (n : ℂ)) => h.eigenspace j) (m : ℂ) hne
        le_rfl : _ ≤ _) hvm

end GlobalTheory.ExtremalGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDualStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonalSumCoefficientLattice_isLattice_and_dual : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (C : Type) [Nonempty C] (N : ℕ) (e : Fin N ≃ C × VVIdx lam) (T : C → Submodule (𝓞 K) (VV K lam)), (∀ c, Submodule.IsLattice K (T c)) → Submodule.IsLattice K (sumLat lam e T) ∧ 0 < N ∧ ∀ (G : ι → Matrix (Fin n) (Fin n) K), (∀ τ, (G τ)ᴴ = G τ) → hdualFr (sumGram lam e G) (sumLat lam e T) = sumLat lam e fun c => Formalism.HermitianLatticesTheory.dual (pairK lam G) (T c) := by
  first | exact @GlobalTheory.TestLat.SumLat.sumLat_lattice_dual | exact GlobalTheory.TestLat.SumLat.sumLat_lattice_dual | (intros; apply GlobalTheory.TestLat.SumLat.sumLat_lattice_dual <;> assumption)
end

