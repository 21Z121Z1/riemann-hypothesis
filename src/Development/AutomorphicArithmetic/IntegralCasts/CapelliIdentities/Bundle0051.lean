import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfMonicRoot
section
theorem UpperTheory.Reformulated.B.NormLeOneOfMonicRoot.norm_le_one_of_monic_root.{u_1, u_2} :
    ∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : NormedField L] [IsUltrametricDist L]
    (φ : R →+* L),
    (∀ (a : R), ‖(φ : R → L) a‖ ≤ (1 : ℝ)) →
      ∀ (x : L) (p : Polynomial R), p.Monic → Polynomial.eval₂ φ x p = (0 : L) → ‖x‖ ≤ (1 : ℝ) := by
  intro R L _ _ _ φ hφ x p hp hx
  by_contra hlt
  have h1 : 1 < ‖x‖ := not_le.mp hlt
  have h0 : 0 < ‖x‖ := lt_trans one_pos h1
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hx
  have hx' : x ^ p.natDegree = -∑ i ∈ Finset.range p.natDegree, φ (p.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hx
  have hb : ‖∑ i ∈ Finset.range p.natDegree, φ (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ p.natDegree / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    have hi' : i + 1 ≤ p.natDegree := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, le_div_iff₀ h0]
    calc ‖φ (p.coeff i)‖ * ‖x‖ ^ i * ‖x‖ ≤ 1 * ‖x‖ ^ i * ‖x‖ := by
          gcongr
          exact hφ _
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ ‖x‖ ^ p.natDegree := pow_le_pow_right₀ h1.le hi'
  rw [← norm_neg, ← hx', norm_pow] at hb
  have hlt' : ‖x‖ ^ p.natDegree / ‖x‖ < ‖x‖ ^ p.natDegree :=
    div_lt_self (by positivity) h1
  exact absurd hb (not_le.mpr hlt')
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeSum
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk34.MM :
    Nat → Nat → Type :=
    fun (P Q : Nat) ↦ Matrix (Sum (Fin P) (Fin Q)) (Sum (Fin P) (Fin Q)) Complex

theorem UpperTheory.Reformulated.B.Qk34.norm_le_sum :
    ∀ (P Q : Nat) (X : UpperTheory.Reformulated.B.Qk34.MM P Q),
      @LE.le Real Real.instLE
        (@Norm.norm (UpperTheory.Reformulated.B.Qk34.MM P Q)
          (@NormedRing.toNorm (UpperTheory.Reformulated.B.Qk34.MM P Q)
            (@Matrix.linftyOpNormedRing (Sum (Fin P) (Fin Q)) Complex
              (@instFintypeSum (Fin P) (Fin Q) (Fin.fintype P) (Fin.fintype Q))
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              fun (a b : Sum (Fin P) (Fin Q)) ↦
              @instDecidableEqSum (Fin P) (Fin Q) (instDecidableEqFin P) (instDecidableEqFin Q) a b))
          X)
        (∑ i : Sum (Fin P) (Fin Q), ∑ j : Sum (Fin P) (Fin Q), @Norm.norm Complex Complex.instNorm (X i j)) := by
  intro P Q X
  have h := Matrix.linfty_opNorm_def (A := X)
  refine le_trans (le_of_eq h) ?_
  have key : ((Finset.univ : Finset (Sum (Fin P) (Fin Q))).sup
      fun i => ∑ j : Sum (Fin P) (Fin Q), ‖X i j‖₊)
      ≤ ∑ i : Sum (Fin P) (Fin Q), ∑ j : Sum (Fin P) (Fin Q), ‖X i j‖₊ :=
    Finset.sup_le fun i hi =>
      Finset.single_le_sum (f := fun i => ∑ j : Sum (Fin P) (Fin Q), ‖X i j‖₊)
        (fun _ _ => by positivity) hi
  have key' := NNReal.coe_le_coe.mpr key
  simpa only [NNReal.coe_sum, coe_nnnorm] using key'
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLtOne
section
namespace UpperTheory.Reformulated.B.NormLtOne

theorem norm_lt_one {l : ℕ} [Fact l.Prime] {O R : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [CommRing R] [IsLocalRing R] [Algebra O R]
    (y : R →ₐ[O] PadicAlgCl l) (a : R) (ha : a ∈ IsLocalRing.maximalIdeal R) : ‖y a‖ < 1 := by
  by_contra hx
  rw [not_lt] at hx
  have hx0 : y a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact absurd hx (by norm_num)
  have hu : ‖(y a)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hx
  have hint : IsIntegral ℚ_[l] (y a)⁻¹ := Algebra.IsIntegral.isIntegral _
  have hmon : (minpoly ℚ_[l] (y a)⁻¹).Monic := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] (y a)⁻¹).coeff n‖ ≤ 1 := by
    rw [← spectralValue_le_one_iff hmon]
    exact hu
  have hz := minpoly.aeval ℚ_[l] (y a)⁻¹
  generalize minpoly ℚ_[l] (y a)⁻¹ = P at hmon hc hz
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_smul] at hz
  let c : ℕ → ℤ_[l] := fun i => ⟨P.coeff i, hc i⟩
  have hr : (∑ i ∈ Finset.range P.natDegree,
      algebraMap O R (algebraMap ℤ_[l] O (c i)) * a ^ (P.natDegree - i)) ∈ IsLocalRing.maximalIdeal R := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ha _ ?_)
    have := Finset.mem_range.mp hi
    omega
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ (neg_mem hr)
  apply (hunit.map y).ne_zero
  have hz' := congrArg (· * y a ^ P.natDegree) hz
  simp only [zero_mul, add_mul, Finset.sum_mul] at hz'
  rw [← mul_pow, inv_mul_cancel₀ hx0, one_pow] at hz'
  rw [sub_neg_eq_add, map_add, map_one, map_sum, add_comm, ← hz']
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := (Finset.mem_range.mp hi).le
  rw [map_mul, map_pow, AlgHom.commutes, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), Algebra.smul_def, mul_assoc,
    pow_sub₀ _ hx0 hi', inv_pow, mul_comm (y a ^ P.natDegree)]
  rfl

end UpperTheory.Reformulated.B.NormLtOne
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormOnValuationRing
section
open scoped NNReal

private theorem UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ = ‖a‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  exact PadicAlgCl.norm_extends l (a : ℚ_[l])

private theorem UpperTheory.Reformulated.B.NormOnValuationRing.norm_le_one {l : ℕ} [Fact (Nat.Prime l)] {y : PadicAlgCl l}
    (hy : IsIntegral ℤ_[l] y) : ‖y‖ ≤ 1 := by
  let v : Valuation (PadicAlgCl l) ℝ≥0 := NormedField.valuation
  have hv : ∀ z : PadicAlgCl l, z ∈ v.integer ↔ ‖z‖ ≤ 1 := fun z => by
    rw [Valuation.mem_integer_iff]
    exact NNReal.coe_le_coe.symm
  let f : ℤ_[l] →+* v.integer :=
    (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer fun a => (hv _).2 (by
      rw [UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap]; exact a.norm_le_one)
  have h : IsIntegral v.integer y :=
    hy.map_of_comp_eq f (RingHom.id _) (by ext a; rfl)
  exact (hv y).1 ((Valuation.integer.integers v).mem_of_integral h)

theorem UpperTheory.Reformulated.B.NormOnValuationRing.mem_max_iff :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {T : Type}
    [inst_1 : CommRing T] [inst_2 : IsLocalRing T] [inst_3 : Algebra ℤ_[l] T] [Algebra.IsIntegral ℤ_[l] T]
    (φ : T →ₐ[ℤ_[l]] PadicAlgCl l) (x : T), x ∈ IsLocalRing.maximalIdeal T ↔ ‖(φ : T → PadicAlgCl l) x‖ < (1 : ℝ) := by
  intro l _ T _ _ _ _ φ x
  have hle : ∀ t : T, ‖φ t‖ ≤ 1 := fun t =>
    UpperTheory.Reformulated.B.NormOnValuationRing.norm_le_one ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) t).map φ)
  let P : Ideal T :=
    { carrier := {t | ‖φ t‖ < 1}
      add_mem' := fun {a b} ha hb => by
        change ‖φ (a + b)‖ < 1
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        change ‖φ (c * a)‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ t : T, t ∈ P ↔ ‖φ t‖ < 1 := fun _ => Iff.rfl
  have hprime : P.IsPrime := by
    refine ⟨?_, fun {a b} hab => ?_⟩
    · rw [Ideal.ne_top_iff_one, hP]
      simp
    · rw [hP, map_mul, norm_mul] at hab
      by_contra h
      rw [not_or, hP, hP, not_lt, not_lt] at h
      exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hab)
  have hcomap : P.comap (algebraMap ℤ_[l] T) = IsLocalRing.maximalIdeal ℤ_[l] := by
    ext a
    rw [Ideal.mem_comap, hP, φ.commutes, UpperTheory.Reformulated.B.NormOnValuationRing.norm_algebraMap,
      IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  have hmax : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) P
      (hcomap ▸ IsLocalRing.maximalIdeal.isMaximal ℤ_[l])
  rw [← IsLocalRing.eq_maximalIdeal hmax, hP]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormPowSubPowLe
section
theorem UpperTheory.Reformulated.B.Qi18.norm_pow_sub_pow_le.{u_1} :
    ∀ {K : Type u_1} [inst : NormedField K]
    [IsUltrametricDist K] (x y : K), ‖x‖ ≤ (1 : ℝ) → ‖y‖ ≤ (1 : ℝ) → ∀ (e : ℕ), ‖x ^ e - y ^ e‖ ≤ ‖x - y‖ := by
  intro K _ _ x y hx hy e
  induction e with
  | zero => simp
  | succ n ih =>
    have h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans ih
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hy)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormRingALe
section
noncomputable def UpperTheory.Reformulated.B.Qi27.muPrime :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Set ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ {ζ : ℂ_[l] | ∃ (n : ℕ), (0 : ℕ) < n ∧ ¬l ∣ n ∧ ζ ^ n = (1 : ℂ_[l])}

noncomputable def UpperTheory.Reformulated.B.Qi27.ringA :
    (l : ℕ) → [inst : Fact (Nat.Prime l)] → Subring ℂ_[l] :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Subring.closure (UpperTheory.Reformulated.B.Qi27.muPrime l)

theorem UpperTheory.Reformulated.B.Qi27.norm_ringA_le :
    ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {x : ℂ_[l]}, x ∈ UpperTheory.Reformulated.B.Qi27.ringA l → ‖x‖ ≤ (1 : ℝ) := by
  intro l hl x hx
  unfold UpperTheory.Reformulated.B.Qi27.ringA at hx
  induction hx using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨n, hn, -, h⟩ := hy
    have h1 : ‖y‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg y) hn.ne').1 h1).le
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  | neg a _ ha => simpa using ha
  | mul a b _ _ ha hb =>
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg b) hb
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormalizedMatrixSpan
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat :
    Type → ℕ → Type :=
    fun (C : Type) (N : ℕ) ↦ Matrix (Fin N) (Fin N) C

noncomputable def UpperTheory.Reformulated.B.NormalizedMatrixSpan.Normd :
    {C : Type} →
      [inst : Field C] →
        {N : ℕ} → {Γ : Type} → [inst_1 : Group Γ] → (Γ →* GL (Fin N) C) → Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N) → Prop :=
    fun {C : Type} [Field C] {N : ℕ} {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C)
        (A : Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N)) ↦
      ∀ (g : Γ),
        ∀ a ∈ A,
          (↑((ρ : Γ → GL (Fin N) C) g) : Matrix (Fin N) (Fin N) C) * a *
              (↑((ρ : Γ → GL (Fin N) C) g⁻¹) : Matrix (Fin N) (Fin N) C) ∈
            A

noncomputable def UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens :
    {Γ C : Type} →
      [inst : Group Γ] →
        [inst_1 : Field C] →
          {N : ℕ} → (Γ →* GL (Fin N) C) → Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N) → Set (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N) :=
    fun {Γ C : Type} [Group Γ] [Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N)) ↦
      {x : UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N | ∃ a ∈ A, ∃ (g : Γ), x = a * (↑((ρ : Γ → GL (Fin N) C) g) : Matrix (Fin N) (Fin N) C)}

theorem UpperTheory.Reformulated.B.NormalizedMatrixSpan.span_mul :
    ∀ {Γ C : Type} [inst : Group Γ] [inst_1 : Field C] {N : ℕ} (ρ : Γ →* GL (Fin N) C)
      (A : Subalgebra C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N)),
      UpperTheory.Reformulated.B.NormalizedMatrixSpan.Normd ρ A →
        ∀ (x y : UpperTheory.Reformulated.B.NormalizedMatrixSpan.Mat C N),
          x ∈ Submodule.span C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens ρ A) →
            y ∈ Submodule.span C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens ρ A) → x * y ∈ Submodule.span C (UpperTheory.Reformulated.B.NormalizedMatrixSpan.gens ρ A) := by
  intro Γ C _ _ N ρ A hA x y hx hy
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, ha, g, rfl⟩, _, ⟨b, hb, k, rfl⟩, rfl⟩
  refine ⟨a * ((ρ g : Matrix (Fin N) (Fin N) C) * b * (ρ g⁻¹ : Matrix (Fin N) (Fin N) C)),
    A.mul_mem ha (hA g b hb), g * k, ?_⟩
  have e : (ρ g⁻¹ : Matrix (Fin N) (Fin N) C) * (ρ (g * k) : Matrix (Fin N) (Fin N) C)
      = (ρ k : Matrix (Fin N) (Fin N) C) := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel_left]
  simp only [mul_assoc, e]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OddSpanVariable
section
theorem UpperTheory.Reformulated.B.PowerSeriesMemSpanIndexedVariables.ep_odd_span_X :
    ∀ {O σ ι : Type} [inst : CommRing O] (e : ι → σ) (s : Finset ι)
    (f : MvPowerSeries σ O),
    (∀ (n : σ →₀ ℕ),
        (∀ i ∈ s, (n : σ → ℕ) (e i) = (0 : ℕ)) → (MvPowerSeries.coeff n : MvPowerSeries σ O → O) f = (0 : O)) →
      f ∈ Ideal.span (Set.range fun (i : ι) ↦ MvPowerSeries.X (e i)) := by
  intro O σ ι inst e s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact Ideal.zero_mem _
  | insert a s _ ih =>
    intro f hf
    let g : MvPowerSeries σ O := fun n => if n (e a) = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g
        = if n (e a) = 0 then MvPowerSeries.coeff n f else 0 := fun _ => rfl
    have h1 : g ∈ Ideal.span (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O)) := by
      refine ih g fun n hn => ?_
      rw [hg]
      split_ifs with h
      · refine hf n fun i hi => ?_
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have h2 : (MvPowerSeries.X (e a) : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro n hn
      rw [map_sub, hg, if_pos hn, sub_self]
    have h3 : f - g ∈ Ideal.span
        (Set.range fun (i : ι) ↦ (MvPowerSeries.X (e i) : MvPowerSeries σ O)) :=
      Ideal.mem_of_dvd _ h2 (Ideal.subset_span ⟨a, rfl⟩)
    have h4 := Ideal.add_mem _ h3 h1
    rwa [sub_add_cancel] at h4
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OmMul
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qe48.DR :
    (R B : Type) → [inst : CommRing R] → [inst_1 : CommRing B] → [Algebra R B] → Type :=
    fun (R B : Type) [CommRing R] [CommRing B] [Algebra R B] ↦ ExteriorAlgebra B Ω[B⁄R]

noncomputable def UpperTheory.Reformulated.B.Qe48.omB :
    (k : Type) →
      [inst : Field k] →
        (K : Type) →
          [inst_1 : Field K] → [inst_2 : Algebra k K] → Subalgebra k K → ℕ → Submodule k (UpperTheory.Reformulated.B.Qe48.DR k K) :=
    fun (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (B : Subalgebra k K) (q : ℕ) ↦
      Submodule.span k
        {y : UpperTheory.Reformulated.B.Qe48.DR k K |
          ∃ b ∈ B,
            ∃ (v : Fin q → K),
              (∀ (j : Fin q), v j ∈ B) ∧
                y =
                  b •
                    (ExteriorAlgebra.ιMulti K q : (Fin q → Ω[K⁄k]) → ExteriorAlgebra K Ω[K⁄k]) fun (j : Fin q) ↦
                      (KaehlerDifferential.D k K : K → Ω[K⁄k]) (v j)}

theorem UpperTheory.Reformulated.B.Qe48.om_mul :
    ∀ {L : Type} [inst : Field L] [inst_1 : Algebra ℂ L] (B : Subalgebra ℂ L) {p q : ℕ} {u w : UpperTheory.Reformulated.B.Qe48.DR ℂ L},
      u ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B p → w ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B q → u * w ∈ UpperTheory.Reformulated.B.Qe48.omB ℂ L B (p + q) := by
  intro L _ _ B p q u w hu hw
  unfold UpperTheory.Reformulated.B.Qe48.omB at hu hw ⊢
  have h := Submodule.mul_mem_mul hu hw
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨b, hb, v, hv, rfl⟩, _, ⟨c, hc, v', hv', rfl⟩, rfl⟩
  refine ⟨b * c, B.mul_mem hb hc, Fin.append v v', ?_, ?_⟩
  · intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact hv i
    · rw [Fin.append_right]; exact hv' i
  · show _ * _ = _
    rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_mul_ιMulti]
    congr 2
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OmegaConstruction
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.OmegaConstruction.Om :
    (O : Type) → [inst : CommRing O] → [IsLocalRing O] → ℕ → Type :=
    fun (O : Type) [CommRing O] [IsLocalRing O] (m : ℕ) ↦ O ⧸ IsLocalRing.maximalIdeal O ^ m

noncomputable def UpperTheory.Reformulated.B.OmegaConstruction.red :
    {O : Type} →
      [inst : CommRing O] →
        [inst_1 : IsLocalRing O] →
          {n : ℕ} → (m : ℕ) → Matrix (Fin n) (Fin n) O → Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.OmegaConstruction.Om O m) :=
    fun {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (m : ℕ) (Z : Matrix (Fin n) (Fin n) O) ↦
      Z.map (⇑(Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ m)) : O → O ⧸ IsLocalRing.maximalIdeal O ^ m)

theorem UpperTheory.Reformulated.B.OmegaConstruction.red_sub :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsLocalRing O] {n : ℕ} (m : ℕ) (A B : Matrix (Fin n) (Fin n) O),
      UpperTheory.Reformulated.B.OmegaConstruction.red m (A - B) = UpperTheory.Reformulated.B.OmegaConstruction.red m A - UpperTheory.Reformulated.B.OmegaConstruction.red m B := by
  intro O _ _ n m A B
  ext i j
  exact map_sub (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ m)) (A i j) (B i j)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OneAlg
section
open Polynomial in
theorem UpperTheory.Reformulated.B.Ra3.one_alg :
    ∀ (R S : Type) [inst : CommRing R] [IsDomain R]
    [inst_2 : CommRing S] [IsDomain S] [inst_4 : Algebra R S],
    Function.Injective (⇑(Algebra.algebraMap R S) : R → S) →
      ∀ (x : S),
        Function.Surjective (⇑(Polynomial.aeval x) : Polynomial R → S) →
          IsAlgebraic R x →
            ∀ (c : S),
              c ≠ (0 : S) →
                ∃ (b : R),
                  b ≠ (0 : R) ∧
                    ∀ (K : Type) [inst_5 : Field K] [IsAlgClosed K] (y : R →+* K),
                      (y : R → K) b ≠ (0 : K) →
                        ∃ (ξ : S →+* K), ξ.comp (Algebra.algebraMap R S) = y ∧ (ξ : S → K) c ≠ (0 : K) := by
  classical
  intro R S _ _ _ _ _ hinj x hsurj halg c hc
  have hcalg : IsAlgebraic R c := by
    obtain ⟨g, rfl⟩ := hsurj c
    exact Algebra.isAlgebraic_adjoin_singleton_iff.mpr halg _
      (Polynomial.aeval_mem_adjoin_singleton R x)
  obtain ⟨b', hb', w, hw⟩ := hcalg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hc)
  obtain ⟨q0, hq0, hq0x⟩ := halg
  have hex : ∃ n, ∃ p : R[X], p ≠ 0 ∧ aeval x p = 0 ∧ p.natDegree = n :=
    ⟨_, q0, hq0, hq0x, rfl⟩
  obtain ⟨p, hp0, hpx, hpn⟩ := Nat.find_spec hex
  have hmin : ∀ f : R[X], f ≠ 0 → aeval x f = 0 → p.natDegree ≤ f.natDegree := fun f hf hfx => by
    rw [hpn]
    exact Nat.find_min' hex ⟨f, hf, hfx, rfl⟩
  have hpos : 0 < p.natDegree := by
    by_contra h
    have h0 : p.natDegree = 0 := by omega
    rw [natDegree_eq_zero] at h0
    obtain ⟨r, rfl⟩ := h0
    rw [aeval_C] at hpx
    have hr : r = 0 := hinj (by simpa using hpx)
    exact hp0 (by simp [hr])
  refine ⟨p.leadingCoeff * b', mul_ne_zero (leadingCoeff_ne_zero.mpr hp0) hb', ?_⟩
  intro K _ _ y hy
  rw [map_mul] at hy
  have hya : y p.leadingCoeff ≠ 0 := left_ne_zero_of_mul hy
  have hyb : y b' ≠ 0 := right_ne_zero_of_mul hy
  have hdeg : (p.map y).degree ≠ 0 := by
    rw [degree_map_eq_of_leadingCoeff_ne_zero y hya]
    exact (natDegree_pos_iff_degree_pos.mp hpos).ne'
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (p.map y) hdeg
  have htp : eval₂ y t p = 0 := by rwa [IsRoot.def, eval_map] at ht
  have hker : ∀ n, ∀ f : R[X], f.natDegree ≤ n → aeval x f = 0 → eval₂ y t f = 0 := by
    intro n
    induction n with
    | zero =>
      intro f hf hfx
      by_cases h0 : f = 0
      · simp [h0]
      · have := hmin f h0 hfx
        omega
    | succ n ih =>
      intro f hf hfx
      by_cases h0 : f = 0
      · simp [h0]
      have hle := hmin f h0 hfx
      have hfpos : 0 < f.natDegree := by omega
      have hlt := natDegree_cancelLeads_lt_of_natDegree_le_natDegree hle hfpos
      have hcx : aeval x (p.cancelLeads f) = 0 := by simp [cancelLeads, hpx, hfx]
      have h1 := ih _ (by omega) hcx
      simp only [cancelLeads, eval₂_sub, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, htp, mul_zero,
        sub_zero, Nat.sub_eq_zero_of_le hle, pow_zero, mul_one] at h1
      exact (mul_eq_zero.mp h1).resolve_left hya
  let φ : R[X] →+* S := (aeval x : R[X] →ₐ[R] S).toRingHom
  let ψ : R[X] →+* K := eval₂RingHom y t
  have hφ : Function.Surjective φ := hsurj
  have hk : RingHom.ker φ ≤ RingHom.ker ψ := fun f hf =>
    hker _ f le_rfl hf
  let ξ : S →+* K := RingHom.liftOfSurjective φ hφ ⟨ψ, hk⟩
  have hξ : ∀ f, ξ (φ f) = ψ f := fun f =>
    RingHom.liftOfRightInverse_comp_apply φ _ _ ⟨ψ, hk⟩ f
  have halgm : ∀ r : R, ξ (Algebra.algebraMap R S r) = y r := fun r => by
    have h2 : φ (C r) = Algebra.algebraMap R S r := aeval_C x r
    rw [← h2, hξ]
    simp [ψ]
  refine ⟨ξ, RingHom.ext halgm, fun h => hyb ?_⟩
  rw [← halgm b']
  have h3 : Algebra.algebraMap R S b' = c * w := hw
  rw [h3, map_mul, h, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OpenFix
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi42.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi42.GQ :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Gal(UpperTheory.Reformulated.B.Qi42.Om l/ℚ_[l])

theorem UpperTheory.Reformulated.B.Qi42.open_fix :
    ∀ {v : ℕ} [inst : Fact (Nat.Prime v)] (H : Subgroup (UpperTheory.Reformulated.B.Qi42.GQ v)),
      IsOpen (↑H : Set (UpperTheory.Reformulated.B.Qi42.GQ v)) → (IntermediateField.fixedField H).fixingSubgroup = H := by
  intro v inst H hH
  haveI : IsGalois ℚ_[v] (PadicAlgCl v) := IsAlgClosure.isGalois ℚ_[v] (PadicAlgCl v)
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨H, Subgroup.isClosed_of_isOpen H hH⟩
end

