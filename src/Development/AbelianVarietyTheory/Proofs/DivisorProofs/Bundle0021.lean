import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimes
section
open IsLocalRing

namespace GlobalTheory.PurityDisc
open TensorProduct

theorem trace_one_tmul (R A S : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing S]
    [Algebra R S] [Module.Free R A] [Module.Finite R A] (a : A) :
    Algebra.trace S (S ⊗[R] A) (1 ⊗ₜ a) = algebraMap R S (Algebra.trace R A a) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]

theorem discr_baseChange (R A S : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing S]
    [Algebra R S] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) :
    Algebra.discr S (Algebra.TensorProduct.basis S b) = algebraMap R S (Algebra.discr R b) := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, trace_one_tmul]

theorem trace_pi (K σ : Type) [Field K] [Fintype σ] [DecidableEq σ] (z : σ → K) :
    Algebra.trace K (σ → K) z = ∑ i, z i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun K σ), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Pi.single_apply]

theorem traceForm_pi_nondegenerate (K σ : Type) [Field K] [Fintype σ] [DecidableEq σ] :
    (Algebra.traceForm K (σ → K)).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · funext i
    have h := hx (Pi.single i 1)
    rw [Algebra.traceForm_apply, trace_pi] at h
    simpa [Pi.single_apply] using h
  · funext i
    have h := hx (Pi.single i 1)
    rw [Algebra.traceForm_apply, trace_pi] at h
    simpa [Pi.single_apply] using h

theorem discr_ne_zero_of_etale (K A : Type) [Field K] [CommRing A] [Algebra K A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K A) [Algebra.Etale K A] :
    Algebra.discr K b ≠ 0 := by
  classical
  let L := AlgebraicClosure K
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[K] A)
  haveI : Module.Finite L (L ⊗[K] A) := Module.Finite.of_basis (Algebra.TensorProduct.basis L b)
  haveI : IsArtinianRing (L ⊗[K] A) := isArtinian_of_tower L inferInstance
  haveI : Fintype (PrimeSpectrum (L ⊗[K] A)) := Fintype.ofFinite _
  let c := (Algebra.TensorProduct.basis L b).map e.toLinearEquiv
  have hc : Algebra.discr L c ≠ 0 := by
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mp
      (traceForm_pi_nondegenerate L (PrimeSpectrum (L ⊗[K] A)))
    rw [Algebra.discr_def]
    convert h using 2
    ext i j
    rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have h2 : Algebra.discr L c = Algebra.discr L (Algebra.TensorProduct.basis L b) := by
    rw [Algebra.discr_eq_discr_of_algEquiv (Algebra.TensorProduct.basis L b) e]
    rfl
  rw [h2, discr_baseChange] at hc
  intro h
  exact hc (by rw [h, map_zero])

theorem exists_dual (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (h : IsUnit (Algebra.discr R b)) :
    ∃ d : ι → A, ∀ i j, Algebra.trace R A (b i * d j) = if i = j then 1 else 0 := by
  classical
  set M := Algebra.traceMatrix R b
  have hM : IsUnit M.det := by rwa [Algebra.discr_def] at h
  refine ⟨fun j => ∑ k, M⁻¹ k j • b k, fun i j => ?_⟩
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have := congrFun (congrFun h1 i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  rw [← this, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_comm]
  simp [M, Algebra.traceMatrix_apply, Algebra.traceForm_apply]

theorem formallyUnramified_of_dual (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (d : ι → A)
    (hd : ∀ i j, Algebra.trace R A (b i * d j) = if i = j then 1 else 0) :
    Algebra.FormallyUnramified R A := by
  classical
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  set T := Algebra.trace R A

  have hrepr : ∀ (z : A) (i : ι), b.repr z i = T (z * d i) := by
    intro z i
    conv_rhs => rw [← b.sum_repr z]
    rw [Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, LinearMap.map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp

  have hnd : ∀ u : A, (∀ k, T (u * b k) = 0) → u = 0 := by
    intro u hu
    rw [← b.sum_repr u]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hrepr, ← b.sum_repr (d j), Finset.mul_sum, map_sum]
    simp_rw [mul_smul_comm, LinearMap.map_smul, hu, smul_zero, Finset.sum_const_zero, zero_smul]

  have hexp : ∀ z : A, ∑ i, T (z * b i) • d i = z := by
    intro z
    rw [← sub_eq_zero]
    refine hnd _ fun k => ?_
    rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, LinearMap.map_smul, mul_comm (d _) (b k), hd, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    simp
  rw [Algebra.FormallyUnramified.iff_exists_tensorProduct]
  refine ⟨∑ i, b i ⊗ₜ[R] d i, fun s => ?_, ?_⟩
  · rw [sub_mul, sub_eq_zero, Finset.mul_sum, Finset.mul_sum]
    simp_rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    symm
    calc ∑ i, (s * b i) ⊗ₜ[R] d i
        = ∑ i, ∑ j, (T (s * b i * d j) • b j) ⊗ₜ[R] d i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (s * b i)]
          rw [TensorProduct.sum_tmul]
          simp_rw [hrepr]
      _ = ∑ j, b j ⊗ₜ[R] (∑ i, T ((s * d j) * b i) • d i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [TensorProduct.tmul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.smul_tmul]
          congr 2
          ring_nf
      _ = ∑ j, b j ⊗ₜ[R] (s * d j) := by simp_rw [hexp]
  · rw [map_sum]
    simp_rw [Algebra.TensorProduct.lmul'_apply_tmul]
    rw [← sub_eq_zero]
    refine hnd _ fun k => ?_
    rw [sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum]
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hrepr]
    congr 1
    ring

theorem etale_of_isUnit_discr (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (h : IsUnit (Algebra.discr R b)) :
    Algebra.Etale R A := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  obtain ⟨d, hd⟩ := exists_dual R A b h
  haveI := formallyUnramified_of_dual R A b d hd
  haveI : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  haveI : Algebra.FinitePresentation R A := inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

theorem exists_height_one_mem (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {x : R}
    (hx : x ≠ 0) (hu : ¬ IsUnit x) : ∃ P : Ideal R, P.IsPrime ∧ P.height = 1 ∧ x ∈ P := by
  have hne : Ideal.span {x} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨P, hmin, -⟩ := Ideal.exists_minimalPrimes_le hxM
  have hP : P.IsPrime := hmin.1.1
  have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hmin.1.2
  have : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have h1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
  have hP0 : P ≠ ⊥ := fun h => hx (by rw [h] at hxP; exact hxP)
  have h0 : P.height ≠ 0 := fun h => hP0 (Ideal.height_eq_zero_iff_eq_bot.mp h)
  exact ⟨P, hP, le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0), hxP⟩

theorem etale_of_etale_height_one : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A],
    ¬ IsField R →
    (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p)
      (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro R A _ _ _ _ _ _ _ _ hR hp
  classical
  let b := Module.Free.chooseBasis R A
  have key : ∀ p : Ideal R, p.IsPrime → p.height = 1 → Algebra.discr R b ∉ p := by
    intro p hp' h1
    haveI := hp'
    haveI := hp p h1
    let Rp := Localization.AtPrime p
    let κ := ResidueField Rp
    have h := discr_ne_zero_of_etale κ (κ ⊗[Rp] (Rp ⊗[R] A))
      (Algebra.TensorProduct.basis κ (Algebra.TensorProduct.basis Rp b))
    rw [discr_baseChange, discr_baseChange] at h
    have hu : IsUnit (algebraMap R Rp (Algebra.discr R b)) := by
      by_contra hn
      exact h ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff Rp p _).mp hu
  have hd : IsUnit (Algebra.discr R b) := by
    by_contra hn
    by_cases h0 : Algebra.discr R b = 0
    · obtain ⟨y, hy0, hyu⟩ : ∃ y : R, y ≠ 0 ∧ ¬ IsUnit y := by
        by_contra H
        push_neg at H
        exact hR ⟨exists_pair_ne R, mul_comm, fun {a} ha => (H a ha).exists_right_inv⟩
      obtain ⟨P, hP, h1, hyP⟩ := exists_height_one_mem R hy0 hyu
      exact key P hP h1 (h0 ▸ P.zero_mem)
    · obtain ⟨P, hP, h1, hdP⟩ := exists_height_one_mem R h0 hn
      exact key P hP h1 hdP
  exact etale_of_isUnit_discr R A b hd

end GlobalTheory.PurityDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitution
section
namespace GlobalTheory

open MvPolynomial in

theorem _root_.GlobalTheory.etale_mvPolynomial_map_of_etale {B A N : Type} [CommRing B] [CommRing A] (g : B →+* A)
    (hg : g.Etale) : (MvPolynomial.map (σ := N) g).Etale := by
  letI := g.toAlgebra
  letI : Algebra (MvPolynomial N B) (MvPolynomial N A) := MvPolynomial.algebraMvPolynomial
  exact RingHom.Etale.isStableUnderBaseChange B A (MvPolynomial N B) (MvPolynomial N A) hg

open MvPolynomial in

theorem etale_eval₂Hom_option_of_bijective {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : A) (f : A →+* R) (n : N → R) {d : ℕ} (e : Fin (d + 1) ≃ Option N)
    (hg : (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t)).Etale) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom f n)) : (MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n)).Etale := by
  let ι : MvPolynomial (Fin (d+1)) k →+* MvPolynomial N (MvPolynomial (Fin 1) k) :=
    eval₂Hom (C.comp C) (fun j => (e j).elim (C (X 0)) X)
  let κ : MvPolynomial N (MvPolynomial (Fin 1) k) →+* MvPolynomial (Fin (d+1)) k :=
    eval₂Hom (eval₂Hom C (fun _ => X (e.symm none))) (fun i => X (e.symm (some i)))
  have h1 : κ.comp ι = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι, κ]
    · intro j
      obtain ⟨o, rfl⟩ := e.symm.surjective j
      cases o <;> simp [ι, κ]
  have h2 : ι.comp κ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [ι, κ]
      · intro j
        obtain rfl : j = 0 := Subsingleton.elim _ _
        simp [ι, κ]
    · intro j
      simp [ι, κ]
  have hι : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩
  have key : MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n) =
      (MvPolynomial.eval₂Hom f n).comp ((MvPolynomial.map (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t))).comp ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι]
    · intro j
      obtain ⟨o, rfl⟩ := e.symm.surjective j
      cases o <;> simp [ι]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι) (etale_mvPolynomial_map_of_etale _ hg))
    (RingHom.Etale.of_bijective hΦ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeAtNearbyIndices
section
open Filter Topology

namespace GlobalTheory

theorem tendsto_comp_div_pow_of_ratio (d : ℕ) (h : ℕ → ℝ) (L r : ℝ) (u : ℕ → ℕ) (hr : 0 < r)
    (hh : Tendsto (fun j : ℕ => h j / (j : ℝ) ^ d) atTop (𝓝 L))
    (hu : Tendsto (fun M : ℕ => (u M : ℝ) / M) atTop (𝓝 r)) :
    Tendsto (fun M : ℕ => h (u M) / (M : ℝ) ^ d) atTop (𝓝 (L * r ^ d)) ∧
      Tendsto u atTop atTop := by
  have hu' : Tendsto (fun M : ℕ => (u M : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun M : ℕ => (u M : ℝ) / M * M) atTop atTop :=
      Tendsto.pos_mul_atTop hr hu tendsto_natCast_atTop_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM
    have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  have huN : Tendsto u atTop atTop := tendsto_natCast_atTop_iff.1 hu'
  refine ⟨?_, huN⟩
  have h2 := (hh.comp huN).mul (hu.pow d)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0, huN.eventually (eventually_gt_atTop 0)] with M hM huM
  have a : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have b : (u M : ℝ) ≠ 0 := by exact_mod_cast huM.ne'
  simp only [Function.comp]
  rw [div_pow]
  field_simp

theorem tendsto_natDiv_div_self (n : ℕ) (hn : 0 < n) :
    Tendsto (fun M : ℕ => ((M / n : ℕ) : ℝ) / M) atTop (𝓝 (1 / n)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n)) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_sub (1 / (n:ℝ))
    rwa [sub_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hMR : (0:ℝ) < M := by exact_mod_cast hM
    have key : (M:ℝ) / n - 1 ≤ ((M / n : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one ((M:ℝ) / n)
      rw [Nat.floor_div_eq_div] at this
      linarith
    rw [le_div_iff₀ hMR]
    have : (1 / (n:ℝ) - 1 / M) * M = M / n - 1 := by field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hMR : (0:ℝ) < M := by exact_mod_cast hM
    rw [div_le_iff₀ hMR]
    have := Nat.cast_div_le (α := ℝ) (m := M) (n := n)
    have e : 1 / (n:ℝ) * M = M / n := by ring
    linarith

theorem eventually_le_at_nearby_indices :
    ∀ (d b c : ℕ) (f : ℝ → ℕ → ℝ) (g : ℤ → ℝ) (f₀ : ℤ → ℝ) (α β : ℝ), 0 < d → 0 < b →
      (∀ η, 0 ≤ η → Tendsto (fun j : ℕ => f η j / (j : ℝ) ^ d) atTop (𝓝 (α + β * η))) →
      (∀ j : ℕ, f₀ j = f 0 j) → (∀ η, 0 < η → ∀ᶠ j : ℕ in atTop, g j ≤ f η j) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
        g (b * M + (M / n : ℕ) - c) ≤ f₀ (b * M - c) + ε * (M : ℝ) ^ d := by
  intro d b c f g f₀ α β _hd hb hf hf₀ hg ε hε
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hlim : Tendsto (fun n : ℕ => α * ((b:ℝ) + 1 / (n:ℝ)) ^ d) atTop
      (𝓝 (α * (b:ℝ) ^ d)) := by
    have := ((tendsto_one_div_atTop_nhds_zero_nat.const_add (b : ℝ)).pow d).const_mul α
    rwa [add_zero] at this
  have hn : ∀ᶠ n : ℕ in atTop, α * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * (b:ℝ) ^ d + ε / 3 :=
    (tendsto_order.1 hlim).2 _ (by linarith)
  filter_upwards [hn, eventually_gt_atTop 0] with n hn hn0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hrpos : (0:ℝ) < (b:ℝ) + 1 / (n:ℝ) := by positivity
  obtain ⟨η, hη, hηlt⟩ : ∃ η : ℝ, 0 < η ∧
      (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 := by
    have hcont : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝[>] 0)
        (𝓝 (α * ((b:ℝ) + 1 / (n:ℝ)) ^ d)) := by
      have : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝 0)
          (𝓝 ((α + β * 0) * ((b:ℝ) + 1 / (n:ℝ)) ^ d)) :=
        ((continuous_const.add (continuous_const.mul continuous_id)).mul
          continuous_const).tendsto 0
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev := (hcont.eventually (gt_mem_nhds (show α * ((b:ℝ) + 1 / (n:ℝ)) ^ d <
      α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 by linarith))).and
      (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Set.Ioi 0)
    obtain ⟨η, h1, h2⟩ := hev.exists
    exact ⟨η, h2, h1⟩
  have hc0 : Tendsto (fun M : ℕ => (c:ℝ) / M) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hr₁ : Tendsto (fun M : ℕ => ((b * M + M / n - c : ℕ) : ℝ) / M) atTop
      (𝓝 ((b:ℝ) + 1 / (n:ℝ))) := by
    have : Tendsto (fun M : ℕ => (b:ℝ) + ((M / n : ℕ) : ℝ) / M - (c:ℝ) / M) atTop
        (𝓝 ((b:ℝ) + 1 / n - 0)) :=
      ((tendsto_natDiv_div_self n hn0).const_add _).sub hc0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0
    have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hle : c ≤ b * M + M / n :=
      le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
  have hr₀ : Tendsto (fun M : ℕ => ((b * M - c : ℕ) : ℝ) / M) atTop (𝓝 (b:ℝ)) := by
    have : Tendsto (fun M : ℕ => (b:ℝ) - (c:ℝ) / M) atTop (𝓝 ((b:ℝ) - 0)) :=
      tendsto_const_nhds.sub hc0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0
    have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hle : c ≤ b * M := le_trans hMc (Nat.le_mul_of_pos_left M hb)
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
  obtain ⟨hA, hu₁⟩ := tendsto_comp_div_pow_of_ratio d (f η) (α + β * η) _ _ hrpos
    (hf η hη.le) hr₁
  obtain ⟨hB, -⟩ := tendsto_comp_div_pow_of_ratio d (f 0) (α + β * 0) _ _ hbR
    (hf 0 le_rfl) hr₀
  have hev : ∀ᶠ M : ℕ in atTop,
      f η (b * M + M / n - c) / (M:ℝ) ^ d - f 0 (b * M - c) / (M:ℝ) ^ d < ε :=
    (tendsto_order.1 (hA.sub hB)).2 ε (by rw [mul_zero, add_zero]; linarith)
  filter_upwards [hev, hu₁.eventually (hg η hη), eventually_ge_atTop c, eventually_gt_atTop 0]
    with M hM hgM hMc hM0
  have hMR : (0:ℝ) < M := by exact_mod_cast hM0
  have hle1 : c ≤ b * M + M / n :=
    le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))
  have hle0 : c ≤ b * M := le_trans hMc (Nat.le_mul_of_pos_left M hb)
  have e1 : ((b:ℤ) * M + ((M / n : ℕ) : ℤ) - c) = ((b * M + M / n - c : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle1]; push_cast; ring
  have e0 : ((b:ℤ) * M - c) = ((b * M - c : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle0]; push_cast; ring
  rw [e1, e0, hf₀]
  have hpos : 0 < (M:ℝ) ^ d := pow_pos hMR d
  rw [← sub_div, div_lt_iff₀ hpos] at hM
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAntilinearNormalForm
section
namespace GlobalTheory

theorem coordsDiag_key (a b y : ℂ) (h : ‖b‖ < ‖a‖) (hy : a * y + b * starRingEnd ℂ y = 0) : y = 0 := by
  by_contra hne
  have h1 : ‖a * y‖ = ‖b * starRingEnd ℂ y‖ := by
    rw [eq_neg_of_add_eq_zero_left hy, norm_neg]
  rw [norm_mul, norm_mul, Complex.norm_conj] at h1
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hne
  have h2 := mul_right_cancel₀ hy'.ne' h1
  linarith

theorem coordsDiag : ∀ (g : ℕ) (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)),
    (∀ j : Fin g, ∃ q : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ v, q (T v) = T (Pi.single j (v j))) →
    ∀ (α β : Fin g → ℂ), (∀ j, ‖β j‖ < ‖α j‖) →
    (∀ j (y : ℂ), T (Pi.single j y) j = α j * y + β j * starRingEnd ℂ y) →
    ∃ D : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
      (∀ v, D (T v) = fun j ↦ v j + β j / α j * starRingEnd ℂ (v j)) ∧
      ∀ (c : Fin g → ℝ) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ v, T (fun m ↦ (c m : ℂ) * v m) = M (T v)) →
        ∀ w, D (M w) = fun j ↦ (c j : ℂ) * D w j := by
  intro g T hq α β hαβ hT
  choose q hq using hq
  have hα : ∀ j, α j ≠ 0 := fun j h => by
    have := hαβ j
    rw [h, norm_zero] at this
    exact (norm_nonneg _).not_gt this
  have hTinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    funext j
    have h1 := hq j v
    rw [hv, map_zero] at h1
    have h2 := congrFun h1.symm j
    rw [hT] at h2
    exact coordsDiag_key _ _ _ (hαβ j) h2
  have hTsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTinj
  let L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    LinearMap.pi (fun j => (α j)⁻¹ • (LinearMap.proj j ∘ₗ q j))
  have hL : ∀ v, L (T v) = fun j ↦ v j + β j / α j * starRingEnd ℂ (v j) := by
    intro v; funext j
    simp only [L, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, smul_eq_mul]
    rw [hq j v, hT]
    field_simp [hα j]
  have hLinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨v, rfl⟩ := hTsurj w
    have hv : v = 0 := by
      funext j
      have h3 := congrFun ((hL v).symm.trans hw) j
      have hz : ‖β j / α j‖ < ‖(1 : ℂ)‖ := by
        rw [norm_div, norm_one, div_lt_one (norm_pos_iff.mpr (hα j))]
        exact hαβ j
      apply coordsDiag_key 1 (β j / α j) (v j) hz
      simpa using h3
    rw [hv, map_zero]
  have hLsurj := LinearMap.injective_iff_surjective.mp hLinj
  refine ⟨LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩, hL, ?_⟩
  intro c M hM w
  obtain ⟨v, rfl⟩ := hTsurj w
  show L (M (T v)) = fun j => (c j : ℂ) * L (T v) j
  rw [← hM, hL, hL]
  funext j
  simp only [map_mul, Complex.conj_ofReal]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisOfDiscreteOfSpanEqTopComplexPi
section
namespace GlobalTheory

theorem exists_basis_of_discrete_of_span_eq_top_complex_pi :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ b : Module.Basis (Fin (2 * g)) ℤ Λ,
        LinearIndependent ℝ (fun i => (b i : Fin g → ℂ)) ∧
          Submodule.span ℝ (Set.range fun i => (b i : Fin g → ℂ)) = ⊤ := by
  intro g Λ hd h
  haveI : IsZLattice ℝ Λ := ⟨h⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  have hr : Module.finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex]
    simp [mul_comm]
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ hr
  have e : (fun i => (b i : Fin g → ℂ)) = ⇑(b.ofZLatticeBasis ℝ Λ) := by
    funext i
    exact (Module.Basis.ofZLatticeBasis_apply ℝ Λ b i).symm
  refine ⟨b, ?_, ?_⟩
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).linearIndependent
  · rw [e]; exact (b.ofZLatticeBasis ℝ Λ).span_eq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstAndFinite
section
namespace GlobalTheory.EtC

def firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A) :
    Subalgebra R (PiTensorProduct R (fun _ : Fin (k + 1) => A)) :=
  Algebra.adjoin R (Set.range (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) 0) ∪
    ⋃ i : Fin (k + 1), (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i) '' (F : Set A))

def firstIncl (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A) :
    A →ₐ[R] firstAndFinite R A k F :=
  (PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) 0).codRestrict _
    (fun a => Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))

end GlobalTheory.EtC
end

