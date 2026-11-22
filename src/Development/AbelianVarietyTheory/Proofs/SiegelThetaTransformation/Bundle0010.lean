import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CanonicalThetaExponentSymplecticInvariantStatement
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalThetaExponent_symplectic_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ Siegel ι, ∀ ζ : ι → ℂ, (ζ ᵥ* (spDen σ τ)⁻¹) ⬝ᵥ ((spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* (spDen σ τ)⁻¹) + 2 * I * (ζ ⬝ᵥ ((spDen σ τ)⁻¹ * qm σ.toBlocks₂₁) *ᵥ ζ) = ζ ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ := by
  first | exact @GlobalTheory.SW.canon_exponent_invariant | exact GlobalTheory.SW.canon_exponent_invariant | (intros; apply GlobalTheory.SW.canon_exponent_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HeisenbergOperatorRationalPointLaws
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

theorem heisS_exists_den {κ ι : Type} [Fintype κ] [Fintype ι] (a : Matrix κ ι ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ k i, IsIntegral ℤ ((D : ℚ) * a k i) := by
  classical
  refine ⟨∏ p : κ × ι, (a p.1 p.2).den, Finset.prod_pos fun p _ => (a p.1 p.2).den_pos, ?_⟩
  intro k i
  obtain ⟨c, hc⟩ : (a k i).den ∣ ∏ p : κ × ι, (a p.1 p.2).den :=
    Finset.dvd_prod_of_mem (fun p : κ × ι => (a p.1 p.2).den) (Finset.mem_univ (k, i))
  have : ((∏ p : κ × ι, (a p.1 p.2).den : ℕ) : ℚ) * a k i
      = algebraMap ℤ ℚ ((c : ℤ) * (a k i).num) := by
    rw [hc]
    have h := Rat.mul_den_eq_num (a k i)
    simp only [eq_intCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
    rw [← h]; ring
  rw [this]
  exact isIntegral_algebraMap

theorem isSB_mul_char {κ ι : Type} [Fintype κ] [Fintype ι] (a b : Matrix κ ι ℚ)
    (ψ : Matrix κ ι ℚ → ℂ) (h : IsSB ψ) :
    IsSB (fun x : Matrix κ ι ℚ => ψ x *
      cexp (Real.pi * I * ((∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) : ℂ))) := by
  obtain ⟨R, hR, hs, hp⟩ := h
  obtain ⟨D, hD, ha⟩ := heisS_exists_den a
  have hn : ∀ n : ℕ, IsIntegral ℤ (n : ℚ) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := (n : ℤ)))
  refine ⟨R * D, Nat.mul_pos hR hD, ?_, ?_⟩
  · intro x hx k i
    have h1 := hs x (left_ne_zero_of_mul hx) k i
    have : (((R * D : ℕ) : ℚ) • x) k i = (D : ℚ) * ((R : ℚ) • x) k i := by
      simp only [Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
    rw [this]; exact (hn D).mul h1
  · intro x y hy
    have e1 : x + ((R * D : ℕ) : ℚ) • y = x + (R : ℚ) • ((D : ℚ) • y) := by
      rw [smul_smul, Nat.cast_mul]
    have hy' : IntM ((D : ℚ) • y) := fun k i => by
      simpa using (hn D).mul (hy k i)
    have hint : IsIntegral ℤ (∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i))) :=
      IsIntegral.sum _ fun k _ => IsIntegral.sum _ fun i _ => (hn R).mul ((hy k i).mul (ha k i))
    obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have e2 : (∑ k, (2 * ((x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ)
        = (∑ k, (2 * (x k ⬝ᵥ a k) - a k ⬝ᵥ b k) : ℚ) + 2 * n := by
      have : (n : ℚ) = ∑ k, ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)) := by simpa using hn'
      rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have : (x + ((R * D : ℕ) : ℚ) • y) k ⬝ᵥ a k
          = x k ⬝ᵥ a k + ∑ i, (R : ℚ) * (y k i * ((D : ℚ) * a k i)) := by
        simp only [dotProduct, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Nat.cast_mul]; ring
      rw [this]; ring
    simp only []
    rw [e2, e1, hp x _ hy']
    congr 1
    rw [Rat.cast_add, mul_add, Complex.exp_add]
    have : (π : ℂ) * I * ((2 * n : ℚ) : ℂ) = n * (2 * π * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem heisS_laws : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (a b : Matrix κ ι ℚ) (φ : Matrix κ ι ℚ → ℂ), IsSB φ → IsSB (heisS a b φ) ∧ (∀ τ ∈ Siegel ι, ∀ ζ, thS (heisS a b φ) τ ζ = cexp (π * I * ∑ k, (qv (b k) ⬝ᵥ τ *ᵥ qv (b k) + 2 * (qv (b k) ⬝ᵥ ζ k) + qv (a k) ⬝ᵥ qv (b k))) * thS φ τ (fun k => ζ k + qv (a k) + τ *ᵥ qv (b k))) ∧ (∀ a' b', heisS a b (heisS a' b' φ) = cexp (π * I * ((∑ k, (a k ⬝ᵥ b' k - a' k ⬝ᵥ b k) : ℚ) : ℂ)) • heisS (a + a') (b + b') φ) ∧ heisS 0 0 φ = φ ∧ ∀ ψ, IsSB ψ → ip (heisS a b φ) (heisS a b ψ) = ip φ ψ := by
  intro κ ι _ _ _ a b φ hφ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isSB_mul_char a b _ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ φ hφ hφ).2.2.2.2.2.2.2 b).1
  · intro τ hτ ζ
    unfold thS
    rw [← tsum_mul_left, ← (Equiv.addRight b).tsum_eq]
    refine tsum_congr fun y => ?_
    simp only [Equiv.coe_addRight, heisS, add_sub_cancel_right]
    rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
    congr 2
    rw [← mul_add, ← mul_add, Rat.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hq : ∀ u v : ι → ℚ, ((u ⬝ᵥ v : ℚ) : ℂ) = qv u ⬝ᵥ qv v := fun u v => by
      simp [dotProduct, qv]
    have hadd : qv ((y + b) k) = qv (y k) + qv (b k) := by
      ext i; simp [qv]
    have hsym : qv (b k) ⬝ᵥ τ *ᵥ qv (y k) = qv (y k) ⬝ᵥ τ *ᵥ qv (b k) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hτ.1.eq, dotProduct_comm]
    rw [Rat.cast_sub, Rat.cast_mul, hq, hq, hadd]
    simp only [add_dotProduct, dotProduct_add, mulVec_add, hsym, dotProduct_comm (qv (b k)) (qv (a k))]
    push_cast; ring
  · intro a' b'
    funext x
    simp only [heisS, Pi.smul_apply, smul_eq_mul]
    rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, sub_sub]
    congr 2
    rw [← mul_add, ← mul_add, ← Rat.cast_add, ← Rat.cast_add, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.add_apply, Matrix.sub_apply]; ring
  · funext x
    simp [heisS, dotProduct]
  · intro ψ hψ
    have h1 : IsSB (fun x : Matrix κ ι ℚ => conj (ψ x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι ψ ψ hψ hψ).2.2.2.1
    have h2 := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι φ _ hφ h1).2.2.1
    have h3 := ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ κ ι _ _ h2 h2).2.2.2.2.2.2.2 b).2
    unfold ip
    refine Eq.trans ?_ h3
    congr 1
    funext x
    simp only [heisS, Pi.mul_apply, map_mul]
    rw [← Complex.exp_conj, mul_mul_mul_comm, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ratCast]
    simp

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsCosetQuadraticPhaseTestFunctionConjCharacterMuStatement
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCosetQuadraticPhaseTestFunction_conj_character_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Shape (fun x => conj (φ x)) ∧ (∀ y, Shape (fun x => φ x * chr y x)) ∧ ∀ ψ, Shape ψ → Shape (fun x => φ x * ψ x) := by
  first | exact @GlobalTheory.Phase.shape_conj_chr_mul | exact GlobalTheory.Phase.shape_conj_chr_mul | (intros; apply GlobalTheory.Phase.shape_conj_chr_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PoissonSummationThetaSeriesRowTermCosetStatement
section
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_thetaSeriesRowTerm_coset : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : ℕ), 0 < R → ∀ τ ∈ Siegel ι, -τ⁻¹ ∈ Siegel ι → IsUnit τ.det → ∃ c : ℂ, c ^ 2 * (((-I) * (R : ℂ) ^ 2) ^ Fintype.card ι * τ.det) = 1 ∧ ∀ (a : ι → ℚ) (ζ : ι → ℂ), (Summable fun m : ι → ℤ => ‖gs τ ζ (a + (R : ℚ) • zv m)‖) ∧ (Summable fun m : ι → ℤ => ‖gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • zv m)‖) ∧ cexp (π * I * (ζ ⬝ᵥ τ⁻¹ *ᵥ ζ)) * ∑' m : ι → ℤ, gs τ ζ (a + (R : ℚ) • zv m) = c * ∑' m : ι → ℤ, ech (a ⬝ᵥ ((R : ℚ)⁻¹ • zv m)) * gs (-τ⁻¹) (ζ ᵥ* τ⁻¹) ((R : ℚ)⁻¹ • zv m) := by
  first | exact @GlobalTheory.SW.FourierJ.Row.poisson_class | exact GlobalTheory.SW.FourierJ.Row.poisson_class | (intros; apply GlobalTheory.SW.FourierJ.Row.poisson_class <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralGaussianShapeRootOfUnityPh
section
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real

namespace GlobalTheory.Phase

private theorem quotient_out_sub_mem' {G : Type} [AddCommGroup G] (N : AddSubgroup G) (x : G) :
    (x : G ⧸ N).out - x ∈ N := by
  have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (x : G ⧸ N)).symm
  rwa [neg_add_eq_sub] at h

open Classical in

theorem ph_finsum_quotient {A : Type} [AddCommGroup A] (P S : AddSubgroup A) (φ f : A → ℂ) (c : ℂ) (a : A)
    (hper : ∀ x, ∀ y ∈ P, φ (x + y) = φ x)
    (hfin : (Function.support fun q : A ⧸ P => φ q.out).Finite)
    (hc : Ph c) (hf : Quad S f) (hφ : ∀ x, φ x = if x - a ∈ S then c * f (x - a) else 0) :
    Ph (∑ᶠ q : A ⧸ P, φ q.out) := by
  by_cases hc0 : c = 0
  · have h0 : ∀ x, φ x = 0 := fun x => by rw [hφ x]; split_ifs <;> simp [hc0]
    simp only [h0, finsum_zero]
    exact ph_zero

  have hfper : ∀ s ∈ S, ∀ t ∈ S, t ∈ P → f (s + t) = f s := by
    intro s hs t htS htP
    have h1 := hφ (a + (s + t))
    have h2 := hφ (a + s)
    rw [add_sub_cancel_left, if_pos (S.add_mem hs htS)] at h1
    rw [add_sub_cancel_left, if_pos hs] at h2
    have h3 : φ (a + (s + t)) = φ (a + s) := by rw [← add_assoc]; exact hper _ t htP
    exact mul_left_cancel₀ hc0 (h1.symm.trans (h3.trans h2))

  let ψ : S →+ A ⧸ P := (QuotientAddGroup.mk' P).comp S.subtype
  have hker : ∀ u : S, u ∈ ψ.ker ↔ (u : A) ∈ P := fun u => by
    simp [ψ, AddMonoidHom.mem_ker, QuotientAddGroup.eq_zero_iff]
  let ι' : S ⧸ ψ.ker →+ A ⧸ P := QuotientAddGroup.kerLift ψ
  have hι : Function.Injective ι' := QuotientAddGroup.kerLift_injective ψ
  let j : S ⧸ ψ.ker → A ⧸ P := fun m => (a : A ⧸ P) + ι' m
  have hj : Function.Injective j := fun m m' h => hι (add_left_cancel h)
  have hjmk : ∀ u : S, j (u : S ⧸ ψ.ker) = ((a + u : A) : A ⧸ P) := fun u => by
    simp [j, ι', ψ]
  let fb : S ⧸ ψ.ker → ℂ := fun m => f (m.out : A)
  have hfb : ∀ u : S, fb (u : S ⧸ ψ.ker) = f u := by
    intro u
    have hk := (hker _).mp (quotient_out_sub_mem' ψ.ker u)
    have e : (((u : S ⧸ ψ.ker).out : S) : A) = u + (((u : S ⧸ ψ.ker).out - u : S) : A) := by simp
    show f (((u : S ⧸ ψ.ker).out : S) : A) = f u
    rw [e]
    exact hfper _ u.2 _ ((u : S ⧸ ψ.ker).out - u).2 hk
  have hval : ∀ m, φ (j m).out = c * fb m := by
    intro m
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective m
    rw [hjmk, hfb]
    have hk := quotient_out_sub_mem' P (a + (u : A))
    have e : ((a + (u : A) : A) : A ⧸ P).out =
        (a + u) + (((a + (u : A) : A) : A ⧸ P).out - (a + u)) := by abel
    rw [e, hper _ _ hk, hφ, add_sub_cancel_left, if_pos u.2]
  have hfbne : ∀ m, fb m ≠ 0 := fun m h => by
    have h1 := (hf.1 _ (m.out).2).norm_eq_one
    simp [fb] at h
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hrange : Set.range j ⊆ Function.support (fun q : A ⧸ P => φ q.out) := by
    rintro _ ⟨m, rfl⟩
    rw [Function.mem_support, hval]
    exact mul_ne_zero hc0 (hfbne m)
  have : Finite (S ⧸ ψ.ker) := by
    have := hfin.to_subtype
    exact Finite.of_injective
      (fun m => (⟨j m, hrange ⟨m, rfl⟩⟩ : Function.support (fun q : A ⧸ P => φ q.out)))
      (fun m m' h => hj (congrArg Subtype.val h))
  haveI := Fintype.ofFinite (S ⧸ ψ.ker)

  have hsupp : Function.support (fun q : A ⧸ P => φ q.out) ⊆ Set.range j := by
    intro q hq
    rw [Function.mem_support, hφ] at hq
    split_ifs at hq with hmem
    · refine ⟨((⟨q.out - a, hmem⟩ : S) : S ⧸ ψ.ker), ?_⟩
      rw [hjmk]
      simp
    · exact absurd rfl hq
  have hsum : ∑ᶠ q : A ⧸ P, φ q.out = c * ∑ m : S ⧸ ψ.ker, fb m := by
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ Set.univ (Set.range j)
        (fun q hq => ⟨fun _ => hsupp hq, fun _ => Set.mem_univ q⟩), finsum_mem_range hj,
      finsum_eq_sum_of_fintype, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => hval m
  rw [hsum]
  refine Ph.mul hc (GlobalTheory.T.isZeroOrPosMulRootOfUnity_finite_gaussSum (S ⧸ ψ.ker) fb ⟨fun x _ => hf.1 _ (x.out).2, fun x _ y _ z _ => ?_⟩)
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  have h0 : fb 0 = f 0 := by simpa using hfb 0
  have e2 : ∀ x y : S, ((x : S ⧸ ψ.ker) + y) = ((x + y : S) : S ⧸ ψ.ker) := fun x y => rfl
  rw [e2 u v, e2 (u + v) w, e2 v w, e2 u w, h0]
  simp only [hfb]
  simpa using hf.2 _ u.2 _ v.2 _ w.2

theorem ph_haar_of_shape : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι],
    ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Ph (haar φ) := by
  intro κ ι _ _ _ φ hφ
  obtain ⟨hsb, c, a, S, f, hc, hf, hφx⟩ := hφ
  have hR := hsb.choose_spec
  unfold haar
  rw [dif_pos hsb]
  unfold haarAt
  refine Ph.mul ?_ (ph_finsum_quotient (perSub ℚ κ ι hsb.choose) S φ f c a
    (GlobalTheory.SW.HaarLevel.periodic hR.2) (GlobalTheory.SW.HaarLevel.finite_support hR.1 hR.2) hc hf hφx)

  have h := GlobalTheory.T.complex_phase_calculus_rootOfUnity.2.2.1
    (((hsb.choose : ℝ) ^ (Module.finrank ℚ ℚ * (Fintype.card κ * Fintype.card ι)))⁻¹)
  convert h using 1
  push_cast
  rfl

end GlobalTheory.Phase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SiegelThetaTransformationLawMulStatement
section
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelThetaTransformationLaw_mul : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ σ' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → σ' ∈ Matrix.symplecticGroup ι ℚ → ∀ φ ψ χ : Matrix κ ι ℚ → ℂ, TransS σ φ ψ → TransS σ' ψ χ → TransS (σ' * σ) φ χ := by
  first | exact @GlobalTheory.SW.transS_comp | exact GlobalTheory.SW.transS_comp | (intros; apply GlobalTheory.SW.transS_comp <;> assumption)
end

