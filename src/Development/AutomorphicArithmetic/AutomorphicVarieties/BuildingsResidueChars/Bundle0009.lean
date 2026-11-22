import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0003

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QuadraticTorusFixedVerticesFinite
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem rescale {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {p : O} (hp : Irreducible p) {x : K} (hx : x ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ ∃ a b : O, algebraMap O K a = s ^ 2 * x ∧ a * b = p ^ 2 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective O x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hp0 : p ≠ 0 := hp.ne_zero
  have hinj := IsFractionRing.injective O K
  have hP : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp0
  have hB : algebraMap O K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hp
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hp
  set t := (m + n) / 2 with ht
  set r := (m + n) % 2 with hr
  have hN : r + t + t = m + n := by omega
  have hr2 : r ≤ 2 := by omega
  have hO : (↑(u * v) * p ^ r) * (p ^ t * p ^ t) = (↑u * p ^ m) * (↑v * p ^ n) := by
    calc (↑(u * v) * p ^ r) * (p ^ t * p ^ t) = ↑u * ↑v * p ^ (r + t + t) := by
            rw [Units.val_mul]; ring
      _ = (↑u * p ^ m) * (↑v * p ^ n) := by rw [hN]; ring
  have key : algebraMap O K (↑(u * v) * p ^ r) * (algebraMap O K p ^ t * algebraMap O K p ^ t)
      = algebraMap O K (↑u * p ^ m) * algebraMap O K (↑v * p ^ n) := by
    rw [← map_pow, ← map_mul, ← map_mul, ← map_mul, hO]
  refine ⟨algebraMap O K (↑v * p ^ n) / algebraMap O K p ^ t, div_ne_zero hB (pow_ne_zero _ hP),
    ↑(u * v) * p ^ r, ↑(u * v)⁻¹ * p ^ (2 - r), ?_, ?_⟩
  · have hT : algebraMap O K p ^ t * algebraMap O K p ^ t ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hP) (pow_ne_zero _ hP)
    have e : algebraMap O K (↑(u * v) * p ^ r) = algebraMap O K (↑u * p ^ m) * algebraMap O K (↑v * p ^ n)
        / (algebraMap O K p ^ t * algebraMap O K p ^ t) := by
      rw [eq_div_iff hT, key]
    rw [e]
    field_simp
  · calc ↑(u * v) * p ^ r * (↑(u * v)⁻¹ * p ^ (2 - r))
        = (↑(u * v) * ↑(u * v)⁻¹) * p ^ (r + (2 - r)) := by rw [pow_add]; ring
      _ = p ^ 2 := by rw [Units.mul_inv, one_mul, Nat.add_sub_cancel' hr2]

private theorem rescaleE {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {τ : K} {p : O} (hp : Irreducible p) {c : (Etau K τ)ˣ} (hc : c ∈ Cint O τ) :
    ∃ s : K, s ≠ 0 ∧ IsIntegral O (s • (c : Etau K τ)) ∧
      IsIntegral O ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
  obtain ⟨hc1, hc2⟩ := hc
  have sq : ∀ u : (Etau K τ)ˣ, (u : Etau K τ) * u =
      algebraMap K (Etau K τ) (QuadraticAlgebra.norm (u : Etau K τ)) * quo u := by
    intro u
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    have h1 : star (u : Etau K τ) * star ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
      rw [← star_mul, Units.inv_mul, star_one]
    unfold quo
    calc (u : Etau K τ) * u = u * u * (star (u : Etau K τ) * star ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
          rw [h1, mul_one]
      _ = u * star (u : Etau K τ) * (u * star ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by ring
  obtain ⟨N, hNd⟩ : ∃ N, N = QuadraticAlgebra.norm (c : Etau K τ) := ⟨_, rfl⟩
  obtain ⟨N', hNd'⟩ : ∃ N', N' = QuadraticAlgebra.norm ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) := ⟨_, rfl⟩
  have hNN : N * N' = 1 := by
    rw [hNd, hNd', ← map_mul, Units.mul_inv, map_one]
  have hN : N ≠ 0 := left_ne_zero_of_mul_eq_one hNN
  have sqc := sq c
  have sqd := sq c⁻¹
  rw [← hNd] at sqc
  rw [← hNd'] at sqd
  obtain ⟨s, hs, a, b, ha, hab⟩ := rescale hp hN
  have hab' : algebraMap O K a * algebraMap O K b = algebraMap O K p ^ 2 := by
    rw [← map_mul, hab, map_pow]
  refine ⟨s, hs, ?_, ?_⟩
  · apply IsIntegral.of_pow (n := 2) two_pos
    have e : (s • (c : Etau K τ)) ^ 2 = algebraMap O (Etau K τ) a * quo c := by
      calc (s • (c : Etau K τ)) ^ 2 = algebraMap K (Etau K τ) s ^ 2 * ((c : Etau K τ) * c) := by
            rw [Algebra.smul_def]; ring
        _ = algebraMap K (Etau K τ) s ^ 2 * (algebraMap K (Etau K τ) N * quo c) := by rw [sqc]
        _ = algebraMap O (Etau K τ) a * quo c := by
            rw [algebraMap_etau a, ha, map_mul, map_pow]; ring
    rw [e]
    exact (isIntegral_algebraMap).mul hc1
  · apply IsIntegral.of_pow (n := 2) two_pos
    have hk : (algebraMap O K p * s⁻¹) ^ 2 * N' = algebraMap O K b := by
      field_simp
      linear_combination (-N') * hab' + (algebraMap O K b * N') * ha + (algebraMap O K b * s ^ 2) * hNN
    have e : ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) ^ 2
        = algebraMap O (Etau K τ) b * quo c⁻¹ := by
      calc ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) ^ 2
          = algebraMap K (Etau K τ) (algebraMap O K p * s⁻¹) ^ 2
            * (((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) * ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
            rw [Algebra.smul_def]; ring
        _ = algebraMap K (Etau K τ) (algebraMap O K p * s⁻¹) ^ 2
            * (algebraMap K (Etau K τ) N' * quo c⁻¹) := by rw [sqd]
        _ = algebraMap O (Etau K τ) b * quo c⁻¹ := by
            rw [algebraMap_etau b, ← hk]
            simp only [map_mul, map_pow]
            ring
    rw [e]
    exact (isIntegral_algebraMap).mul hc2

private theorem cls_smul {K : Type} [Field K] {τ : K} (S : Set (Etau K τ)) {s : K} (hs : s ≠ 0) :
    cls τ ((s • ·) '' S) = cls τ S := by
  ext T
  simp only [cls, Set.mem_setOf_eq, Set.image_image, smul_smul]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u * Units.mk0 s hs, by congr 1⟩
  · rintro ⟨u, rfl⟩
    refine ⟨u * (Units.mk0 s hs)⁻¹, ?_⟩
    congr 1
    funext y
    simp [hs]

private theorem exists_finite_representatives_mod_smul_of_fg {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {m : O}
    (hq : Finite (O ⧸ Ideal.span {m})) (R : Submodule O M) (hR : R.FG) :
    ∃ F : Set M, F.Finite ∧ ∀ x ∈ R, ∃ y ∈ F, ∃ z ∈ R, x - y = m • z := by
  haveI := hq
  obtain ⟨g, rfl⟩ := hR
  have hsurj := Ideal.Quotient.mk_surjective (I := Ideal.span {m})
  refine ⟨Set.range (fun r : (↥g → O ⧸ Ideal.span {m}) =>
    ∑ i : ↥g, Function.surjInv hsurj (r i) • (i : M)), Set.finite_range _, ?_⟩
  intro x hx
  obtain ⟨f, -, rfl⟩ := (Submodule.mem_span_finset).mp hx
  have hk : ∀ i : ↥g, ∃ k : O, k * m = f i - Function.surjInv hsurj (Ideal.Quotient.mk _ (f i)) := by
    intro i
    apply Ideal.mem_span_singleton'.mp
    apply Ideal.Quotient.eq.mp
    rw [Function.surjInv_eq hsurj]
  choose k hk using hk
  refine ⟨_, ⟨fun i => Ideal.Quotient.mk _ (f i), rfl⟩, ∑ i : ↥g, k i • (i : M), ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span i.2)
  · rw [← Finset.sum_coe_sort g, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, ← hk i, smul_smul, mul_comm]

theorem UpperTheory.quadraticTorus_fixedVertices_finite :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → (Fv O τ).Finite := by
  intro O K _ _ _ _ _ Δ τ hL hτ
  haveI := hL.frac
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨c0, hc0, hden⟩ := int_denom hL hτ
  have hm : c0 * p ≠ 0 := mul_ne_zero hc0 hp.ne_zero
  obtain ⟨F, hF, hFR⟩ := exists_finite_representatives_mod_smul_of_fg (finite_quot_span hL hm)
    (Subalgebra.toSubmodule (integralClosure O (Etau K τ))) (intE_fg hL hτ)
  have hmemR : ∀ z, z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)) ↔ IsIntegral O z := by
    intro z
    rw [Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
  let 𝒯 : Set (Set (Etau K τ)) := {T | ∃ M : Submodule O (Etau K τ), T = M ∧
    (∀ z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)), (c0 * p) • z ∈ M) ∧
    M ≤ Subalgebra.toSubmodule (integralClosure O (Etau K τ))}
  have h𝒯 : 𝒯.Finite := by
    apply Set.Finite.of_finite_image (f := fun T => T ∩ F)
    · exact (hF.powerset).subset (by rintro _ ⟨T, -, rfl⟩; exact Set.inter_subset_right)
    · have key : ∀ M M' : Submodule O (Etau K τ),
          (∀ z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)), (c0 * p) • z ∈ M) →
          M ≤ Subalgebra.toSubmodule (integralClosure O (Etau K τ)) →
          (∀ z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)), (c0 * p) • z ∈ M') →
          (M : Set (Etau K τ)) ∩ F = (M' : Set (Etau K τ)) ∩ F → (M : Set (Etau K τ)) ⊆ M' := by
        intro M M' hm1 hR1 hm2 he x hx
        obtain ⟨y, hyF, z, hz, hxy⟩ := hFR x (hR1 hx)
        have hy : y ∈ M := by
          have e : y = x - (c0 * p) • z := by rw [← hxy]; abel
          rw [e]
          exact M.sub_mem hx (hm1 z hz)
        have hy2 : y ∈ (M' : Set (Etau K τ)) ∩ F := by
          rw [← he]
          exact ⟨hy, hyF⟩
        have e : x = y + (c0 * p) • z := by rw [← hxy]; abel
        rw [e]
        exact M'.add_mem hy2.1 (hm2 z hz)
      rintro _ ⟨M1, rfl, h1m, h1R⟩ _ ⟨M2, rfl, h2m, h2R⟩ heq
      have heq' : (M1 : Set (Etau K τ)) ∩ F = (M2 : Set (Etau K τ)) ∩ F := heq
      exact Set.Subset.antisymm (key _ _ h1m h1R h2m heq') (key _ _ h2m h2R h1m heq'.symm)
  apply (h𝒯.image (fun T => cls τ T)).subset
  rintro X ⟨S, hS, hω, ⟨c, hc, hgen⟩, rfl⟩
  obtain ⟨s, hs, hsc, hsd⟩ := rescaleE hp hc
  refine ⟨(s • ·) '' S, ?_, cls_smul S hs⟩
  obtain ⟨g, hg⟩ := hS.fg
  have hcomm : ∀ (o : O) (x : Etau K τ), o • (s • x) = s • (o • x) := by
    intro o x
    simp only [Algebra.smul_def]
    ring
  let M : Submodule O (Etau K τ) :=
    { carrier := (s • ·) '' S
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        refine ⟨u + v, ?_, smul_add s u v⟩
        rw [hg] at hu hv ⊢
        exact Submodule.add_mem _ hu hv
      zero_mem' := ⟨0, by rw [hg]; exact Submodule.zero_mem _, smul_zero s⟩
      smul_mem' := by
        rintro o _ ⟨u, hu, rfl⟩
        refine ⟨o • u, ?_, (hcomm o u).symm⟩
        rw [hg] at hu ⊢
        exact Submodule.smul_mem _ o hu }
  refine ⟨M, rfl, ?_, ?_⟩
  · intro z hz
    have hzi : IsIntegral O z := (hmemR z).mp hz
    have e1 : algebraMap O (Etau K τ) p = (s • (c : Etau K τ)) *
        ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
      rw [smul_mul_smul_comm, Units.mul_inv, algebraMap_etau p, Algebra.algebraMap_eq_smul_one]
      congr 1
      field_simp
    have hy : IsIntegral O (((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * z) :=
      hsd.mul hzi
    obtain ⟨a, b, h1, h2⟩ := hden _ hy
    have e2 : algebraMap O (Etau K τ) c0 *
        (((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * z)
        = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * ω := by
      rw [algebraMap_etau c0, algebraMap_etau a, algebraMap_etau b]
      ext
      · have h1' := h1
        simp at h1' ⊢
        linear_combination h1'
      · have h2' := h2
        simp at h2' ⊢
        linear_combination h2'
    have e3 : (c0 * p) • z = a • (s • (c : Etau K τ)) + b • (s • (ω * (c : Etau K τ))) := by
      calc (c0 * p) • z = algebraMap O (Etau K τ) c0 * algebraMap O (Etau K τ) p * z := by
            rw [Algebra.smul_def, map_mul]
        _ = (s • (c : Etau K τ)) * (algebraMap O (Etau K τ) c0 *
              (((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * z)) := by
            rw [e1]; ring
        _ = (s • (c : Etau K τ)) * (algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * ω) := by
            rw [e2]
        _ = a • (s • (c : Etau K τ)) + b • (s • (ω * (c : Etau K τ))) := by
            rw [Algebra.smul_def a, Algebra.smul_def b, ← mul_smul_comm]
            ring
    rw [e3]
    have m1 : s • (c : Etau K τ) ∈ M := ⟨_, hgen.1, rfl⟩
    have m2 : s • (ω * (c : Etau K τ)) ∈ M := ⟨_, hω _ hgen.1, rfl⟩
    exact M.add_mem (M.smul_mem a m1) (M.smul_mem b m2)
  · rintro _ ⟨w, hw, rfl⟩
    rw [hmemR]
    have e : s • w = (s • (c : Etau K τ)) * (((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w) := by
      rw [smul_mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
    show IsIntegral O (s • w)
    rw [e]
    exact hsc.mul (hgen.2 w hw)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SigLEqOfHermSemilinearEqStar
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob Matrix

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {Δ τ : K}

private theorem sigL_mul' (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL]

private theorem sigL_sigL' (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sigL_star' (x : EL Δ τ) : sigL (star x) = star (sigL x) := by
  ext <;> simp [sigL]

private theorem sigL_one' : sigL (1 : EL Δ τ) = 1 := by
  ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem trace_sigL (x : EL Δ τ) : QuadraticAlgebra.trace (sigL x) = star (QuadraticAlgebra.trace x) := by
  have e : star (algebraMap K (Lsq K Δ) τ) = algebraMap K (Lsq K Δ) τ := by
    ext <;> simp
  simp [QuadraticAlgebra.trace_def, sigL, e]

private theorem eq_zero_of_trace (hτ : τ ^ 2 - 4 ≠ 0) {w : EL Δ τ}
    (h : ∀ x, QuadraticAlgebra.trace (w * x) = 0) : w = 0 := by
  have h1 := h 1
  have h2 := h QuadraticAlgebra.omega
  simp [QuadraticAlgebra.trace_def] at h1 h2
  have hu : IsUnit (algebraMap K (Lsq K Δ) (τ ^ 2 - 4)) := (IsUnit.mk0 _ hτ).map _
  rw [map_sub, map_pow, map_ofNat] at hu
  refine QuadraticAlgebra.ext ?_ ?_
  · refine hu.mul_right_eq_zero.1 ?_
    linear_combination ((algebraMap K (Lsq K Δ) τ) ^ 2 - 2) * h1 - (algebraMap K (Lsq K Δ) τ) * h2
  · refine hu.mul_right_eq_zero.1 ?_
    linear_combination 2 * h2 - (algebraMap K (Lsq K Δ) τ) * h1

end SlopeTestRemainingChoices

theorem UpperTheory.sigL_eq_of_herm_semilinear_eq_star :
    ∀ (K : Type) [Field K] [CharZero K] (Δ τ c : K) (d m : EL Δ τ), τ ^ 2 - 4 ≠ 0 →
        (∀ x y : Sp Δ τ, herm c m (semi d x) (semi d y) = star (herm c m x y)) → sigL m = m * d * star (sigL d) := by
  intro K _ _ Δ τ c d m hτ h
  have key : ∀ a : EL Δ τ, QuadraticAlgebra.trace ((m * d * star (sigL d) - sigL m) * a) = 0 := fun a => by
    have e := h (0, sigL a) (0, 1)
    simp only [herm, semi, star_zero, mul_zero, zero_mul, zero_add, sigL_sigL', sigL_one', mul_one, star_one,
      sigL_mul'] at e
    rw [← trace_sigL, sigL_mul', sigL_sigL'] at e
    rw [sub_mul, map_sub, sub_eq_zero, ← e]
    congr 1
    ring
  exact (sub_eq_zero.1 (eq_zero_of_trace hτ key)).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpanOrdinaryPartEqSupUnitGeneralizedEigenspaces
section
open IsLocalRing UpperTheory.V.Hi UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

open TensorProduct in
private theorem UpperTheory.pi_scalar_right_tmul {O Ω ι : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    [Fintype ι] [DecidableEq ι] (a : Ω) (v : ι → O) :
    TensorProduct.piScalarRight O Ω Ω ι (a ⊗ₜ v) = a • fun i => algebraMap O Ω (v i) := by
  ext i
  simp [Algebra.smul_def, mul_comm]

private theorem UpperTheory.map_max_gen_eigenspace_of_intertwine {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (E : V ≃ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ x, g (E x) = E (f x)) (μ : K) :
    (f.maxGenEigenspace μ).map E.toLinearMap = g.maxGenEigenspace μ := by
  have hp : ∀ (k : ℕ) x, ((g - μ • 1) ^ k) (E x) = E (((f - μ • 1) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
      simp [h]
  ext y
  obtain ⟨x, rfl⟩ := E.surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Module.End.mem_maxGenEigenspace,
    Module.End.mem_maxGenEigenspace]
  simp only [hp, EmbeddingLike.map_eq_zero_iff]

theorem UpperTheory.span_ordinaryPart_eq_sup_unit_generalized_eigenspaces :
    ∀ (O Ω ι : Type) [CommRing O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] [Fintype ι] (T₀ : Module.End O (ι → O)) (T : Module.End Ω (ι → Ω)), (∀ v, T (fun i => algebraMap O Ω (v i)) = fun i => algebraMap O Ω (T₀ v i)) → ⨆ μ : {μ : Ω // IsIntUnit O μ}, T.maxGenEigenspace μ.1 = Submodule.span Ω ((fun (v : ι → O) i => algebraMap O Ω (v i)) '' (ordPart T₀ : Set (ι → O))) := by
  intro O Ω ι _ hO _ _ _ _ T₀ T hT
  classical
  haveI : IsAdicComplete (maximalIdeal O) O := hO.complete
  have hadm := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordAdm_maximalIdeal_and_finite_quotients (R := O) (M := ι → O)).1
  have hex := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hadm T₀
  have key := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt (K := Ω) hex.1
  set E := TensorProduct.piScalarRight O Ω Ω ι with hE
  have hEt : ∀ (a : Ω) (v : ι → O),
      E (a ⊗ₜ v) = a • fun i => algebraMap O Ω (v i) := UpperTheory.pi_scalar_right_tmul
  have hc : ∀ x, T (E x) = E (T₀.baseChange Ω x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rw [LinearMap.baseChange_tmul, hEt, hEt, map_smul, hT]
    | add x y hx hy => simp only [map_add, hx, hy]
  have h1 := congrArg (Submodule.map E.toLinearMap) key
  simp only [Submodule.map_iSup, UpperTheory.map_max_gen_eigenspace_of_intertwine E _ T hc] at h1
  rw [iSup_subtype]
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEt]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      rw [← hex.2.1]
      exact ⟨v, rfl⟩
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    rw [← hex.2.1] at hv
    obtain ⟨w, rfl⟩ := hv
    refine ⟨_, ⟨(1 : Ω) ⊗ₜ w, rfl⟩, ?_⟩
    rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEt, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UpOperatorMapsLatticeOfControlValues
section
open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.Up_operator_maps_lattice_of_control_values :
    ∀ (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (W : WtRep X.I O Ω) (m : ℕ) (Λ Λ' : Submodule O Ω), (∀ a ∈ maximalIdeal O, ∀ w ∈ Λ, a • w ∈ Λ') → ∀ F ∈ X.Lat m W Λ, (∀ g i, X.ctrl m W F g i ∈ Λ') → X.UF m W ⟨X.I.z, X.I.z_mem⟩ F ∈ X.Lat m W Λ' := by
  intro Γ Ga Gp _ _ _ X O Ω _ _ _ _ W m Λ Λ' h F hF hc
  have hu : ∀ i g k, X.unt m W F i g k ∈ Λ := (Frame.mem_lat X m W Λ F).mp hF
  have hu0 : ∀ i g, X.unt m W F i g 0 ∈ Λ' := fun i g => by
    rw [← Frame.ctrl_apply]
    exact hc g i
  have hF' : ∀ i g, F i g = (W.ξ g.2 : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ X.unt m W F i g := fun i g => by
    rw [Frame.unt_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hM : ∀ (M : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω),
      (∀ k l, M k l ∈ (algebraMap O Ω).range) → ∀ w : Fin (W.d + 1) → Ω, (∀ l, w l ∈ Λ') →
      ∀ k, (M *ᵥ w) k ∈ Λ' := by
    intro M hMi w hw k
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun l _ => ?_
    obtain ⟨y, hy⟩ := hMi k l
    rw [← hy, ← Algebra.smul_def]
    exact Λ'.smul_mem y (hw l)
  have main : ∀ c : Ω, (∀ l j, c * (W.ξ X.I.z : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) l j ∈ (algebraMap O Ω).range) →
      (∀ l j, j ≠ 0 → ∃ x ∈ maximalIdeal O, c * (W.ξ X.I.z : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) l j = algebraMap O Ω x) →
      (c • ∑ᶠ (q : ↥X.I.N ⧸ (X.I.Nconj X.I.z).subgroupOf X.I.N),
        X.rpF Ω (W.d + 1) m (↑(Quotient.out q) * X.I.z)) F ∈ X.Lat m W Λ' := by
    intro c hP hN
    refine finsum_induction (p := fun T : Module.End Ω (Fin m → X.Fn Ω (W.d + 1)) => (c • T) F ∈ X.Lat m W Λ') ?_ ?_ ?_
    · simp
    · intro S T hS hT
      simpa [smul_add] using add_mem hS hT
    · intro q
      have hn : ((Quotient.out q : ↥X.I.N) : Gp) ∈ X.I.N := (Quotient.out q).2
      generalize ((Quotient.out q : ↥X.I.N) : Gp) = n at hn ⊢
      rw [Frame.mem_lat]
      intro i g k
      have e : X.unt m W ((c • X.rpF Ω (W.d + 1) m (n * X.I.z)) F) i g
          = (W.ξ n : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω) *ᵥ ((c • (W.ξ X.I.z : Matrix (Fin (W.d + 1)) (Fin (W.d + 1)) Ω)) *ᵥ
              X.unt m W F i (g * (1, n * X.I.z))) := by
        have e1 : X.rpF Ω (W.d + 1) m (n * X.I.z) F i g = F i (g * (1, n * X.I.z)) := by
          simp [Frame.rpF, Frame.rp, rtr]
        rw [Frame.unt_apply, LinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, e1,
          hF' i (g * (1, n * X.I.z))]
        simp only [Prod.snd_mul, mul_one, map_mul, Units.val_mul, Matrix.mulVec_smul,
          Matrix.mulVec_mulVec, ← mul_assoc]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, Matrix.mul_smul, Matrix.smul_mulVec]
      rw [e]
      refine hM _ (fun k l => W.int_N _ hn k l) _ (fun l => ?_) k
      simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
      refine Submodule.sum_mem _ fun j _ => ?_
      by_cases hj : j = 0
      · subst hj
        obtain ⟨y, hy⟩ := hP l 0
        rw [← hy, ← Algebra.smul_def]
        exact Λ'.smul_mem y (hu0 _ _)
      · obtain ⟨x, hx, hxe⟩ := hN l j hj
        rw [hxe, ← Algebra.smul_def]
        exact h x hx _ (hu _ _ _)
  exact main _ (fun l j => W.int_P _ X.I.z_mem l j) (fun l j hj => W.nilpotent_central_action l j hj)
end

