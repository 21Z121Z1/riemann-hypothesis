import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestAlt
section
namespace AevalSpecializationAlgHom

open MvPolynomial

private theorem key {Ω : Type} [Field Ω] [Algebra ℚ Ω] {σ : Type} (τ : σ → Ω) (F : MvPolynomial σ ℚ)
    {E : Type} [CommRing E] [Algebra ℚ E] (u : σ → E) (hF : aeval τ F ≠ (0 : Ω))
    (v : E) (hv : v * aeval u F = 1) (P : MvPolynomial (Option σ) ℚ) :
    ∃ (N : ℕ) (G : MvPolynomial σ ℚ),
      aeval (fun o => Option.elim o (aeval τ F)⁻¹ τ) P * (aeval τ F) ^ N = aeval τ G ∧
      aeval (fun o => Option.elim o v u) P * (aeval u F) ^ N = aeval u G := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by simp, by simp⟩
  | add p q hp hq =>
    obtain ⟨N1, G1, h1, h1'⟩ := hp
    obtain ⟨N2, G2, h2, h2'⟩ := hq
    refine ⟨N1 + N2, G1 * F ^ N2 + G2 * F ^ N1, ?_, ?_⟩
    · simp only [map_add, map_mul, map_pow, ← h1, ← h2]; ring
    · simp only [map_add, map_mul, map_pow, ← h1', ← h2']; ring
  | mul_X p o hp =>
    obtain ⟨N, G, h1, h1'⟩ := hp
    cases o with
    | none =>
      refine ⟨N + 1, G, ?_, ?_⟩
      · simp only [map_mul, aeval_X, Option.elim_none]
        rw [← h1, pow_succ]
        field_simp
      · simp only [map_mul, aeval_X, Option.elim_none]
        rw [← h1', pow_succ]
        linear_combination (aeval (fun o => Option.elim o v u) p * aeval u F ^ N) * hv
    | some i =>
      refine ⟨N, G * X i, ?_, ?_⟩
      · simp only [map_mul, aeval_X, Option.elim_some, ← h1]; ring
      · simp only [map_mul, aeval_X, Option.elim_some, ← h1']; ring

end AevalSpecializationAlgHom

theorem UpperTheory.Reformulated.B.Yde9.main :
    ∀ (Ω : Type) [inst : Field Ω] [inst_1 : Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ) (S : Subalgebra ℚ Ω)
      (E : Type) [inst_2 : CommRing E] [inst_3 : Algebra ℚ E] (u : σ → E),
      (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) F ≠ (0 : Ω) →
        S = Algebra.adjoin ℚ (Insert.insert ((MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) F)⁻¹ (Set.range τ)) →
          (∀ (G : MvPolynomial σ ℚ),
              (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) G = (0 : Ω) →
                (MvPolynomial.aeval u : MvPolynomial σ ℚ → E) G = (0 : E)) →
            IsUnit ((MvPolynomial.aeval u : MvPolynomial σ ℚ → E) F) →
              ∃ (φ : ↥S →ₐ[ℚ] E),
                ∀ (G : MvPolynomial σ ℚ) (s : ↥S),
                  (↑s : Ω) = (MvPolynomial.aeval τ : MvPolynomial σ ℚ → Ω) G →
                    (φ : ↥S → E) s = (MvPolynomial.aeval u : MvPolynomial σ ℚ → E) G := by
  intro Ω _ _ σ τ F S E _ _ u hF hS hker hU
  obtain ⟨w, hw⟩ := hU
  set v : E := ((w⁻¹ : Eˣ) : E) with hvdef
  have hv : v * MvPolynomial.aeval u F = 1 := by rw [← hw]; simp [v]
  set τ' : Option σ → Ω := fun o => Option.elim o (MvPolynomial.aeval τ F)⁻¹ τ with hτ'
  set u' : Option σ → E := fun o => Option.elim o v u with hu'
  have hS' : S = (MvPolynomial.aeval τ').range := by
    rw [hS, ← Algebra.adjoin_range_eq_range_aeval, Option.range_eq]
    rfl
  subst hS'
  have hsurj := AlgHom.rangeRestrict_surjective (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω)
  have hK : ∀ P ∈ RingHom.ker (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).rangeRestrict,
      (MvPolynomial.aeval u') P = 0 := by
    intro P hP
    rw [RingHom.mem_ker] at hP
    have hP' : MvPolynomial.aeval τ' P = 0 := congrArg Subtype.val hP
    obtain ⟨N, G, h1, h1'⟩ := AevalSpecializationAlgHom.key τ F u hF v hv P
    have h0 : MvPolynomial.aeval τ G = 0 := by
      rw [← h1]; simp only [τ'] at hP'; simp [hP']
    have h2 := hker G h0
    rw [h2] at h1'
    have hunit : IsUnit (MvPolynomial.aeval u F ^ N) := by
      rw [← hw]; exact (w.isUnit).pow N
    exact (hunit.mul_left_eq_zero).mp h1'
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let L := Ideal.Quotient.liftₐ (RingHom.ker (MvPolynomial.aeval τ' : MvPolynomial (Option σ) ℚ →ₐ[ℚ] Ω).rangeRestrict) (MvPolynomial.aeval u') hK
  refine ⟨L.comp e.symm.toAlgHom, ?_⟩
  intro G s hs
  have hs' : s = (MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G) := by
    apply Subtype.ext
    rw [hs]
    simp [MvPolynomial.aeval_rename]
    rfl
  rw [hs']
  have he : e.symm ((MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G)) =
      Ideal.Quotient.mk _ (MvPolynomial.rename some G) :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply hsurj _
  change L (e.symm ((MvPolynomial.aeval τ').rangeRestrict (MvPolynomial.rename some G))) = _
  rw [he]
  change MvPolynomial.aeval u' (MvPolynomial.rename some G) = _
  rw [MvPolynomial.aeval_rename]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestExtra
section
namespace SupNormSqLeSumNormSq

private lemma entry_le {m n : ℕ} (x : Fin m → Fin n → ℂ) (a : Fin m) (j : Fin n) :
    ‖x a j‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
  apply Real.le_sqrt_of_sq_le
  calc ‖x a j‖ ^ (2 : ℕ) ≤ ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun j => ‖x a j‖ ^ (2 : ℕ)) (fun _ _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun a => ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))
          (fun _ _ => by positivity) (Finset.mem_univ a)

end SupNormSqLeSumNormSq

theorem UpperTheory.Reformulated.B.Yhb3.main :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ), ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by
  intro m n x
  have hS : 0 ≤ ∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ) := by positivity
  have h : ‖x‖ ≤ Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => SupNormSqLeSumNormSq.entry_le x a j
  calc ‖x‖ ^ (2 : ℕ) ≤ (Real.sqrt (∑ a : Fin m, ∑ j : Fin n, ‖x a j‖ ^ (2 : ℕ))) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestFurther
section
theorem UpperTheory.Reformulated.B.Yhb2.main :
    ∀ {a : WithBot ℕ∞} {d : ℕ}, a < (↑(d + (1 : ℕ)) : WithBot ℕ∞) → a ≤ (↑d : WithBot ℕ∞) := by
  intro a d h
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe b =>
    have h1 : b < ((d+1 : ℕ) : ℕ∞) := by exact_mod_cast h
    have h2 : b ≤ (d : ℕ∞) := by
      induction b using ENat.recTopCoe with
      | top => exact absurd h1 (not_lt.mpr le_top)
      | coe n =>
        have h3 : n < d + 1 := by exact_mod_cast h1
        exact_mod_cast Nat.lt_succ_iff.mp h3
    exact_mod_cast h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestLast
section
theorem UpperTheory.Reformulated.B.Yhd4.main :
    ∀ {G V : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [ContinuousMul G] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module ℂ V] (ρ : Representation ℂ G V) (v : V),
      {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} ∈ nhds (1 : G) →
        IsOpen {g : G | ((ρ : G → V →ₗ[ℂ] V) g : V → V) v = v} := by
  intro G V _ _ _ _ _ ρ v hS
  rw [isOpen_iff_mem_nhds]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  have hc : Filter.Tendsto (fun h : G => g⁻¹ * h) (nhds g) (nhds 1) := by
    have := ((continuous_const_mul g⁻¹ : Continuous (fun h : G => g⁻¹ * h)).tendsto g)
    simpa using this
  filter_upwards [hc hS] with h hh
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hh ⊢
  have : h = g * (g⁻¹ * h) := by group
  rw [this, map_mul, Module.End.mul_apply, hh, hg]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestMore
section
namespace ZbYha7

open scoped ComplexOrder in
private lemma pos {I : Type} [Fintype I] (A : Matrix I I ℂ) (hA : A.PosDef) (x : I → ℂ) (hx : x ≠ 0) :
    0 < RCLike.re (star x ⬝ᵥ A.mulVec x) :=
  (RCLike.pos_iff.mp (hA.dotProduct_mulVec_pos hx)).1

private lemma scale {I : Type} [Fintype I] (A : Matrix I I ℂ) (x : I → ℂ) (r : ℝ) :
    RCLike.re (star ((r : ℂ) • x) ⬝ᵥ A.mulVec ((r : ℂ) • x)) = r ^ 2 * RCLike.re (star x ⬝ᵥ A.mulVec x) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [smul_eq_mul, RCLike.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  simp [Complex.re_ofReal_mul, sq]

private lemma cont {I : Type} [Fintype I] (A : Matrix I I ℂ) :
    Continuous fun x : I → ℂ => RCLike.re (star x ⬝ᵥ A.mulVec x) := by
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

end ZbYha7

theorem UpperTheory.Reformulated.B.Yha7.main :
    ∀ {I : Type} [inst : Fintype I] [DecidableEq I] (A : Matrix I I Complex),
      @Matrix.PosDef I Complex Complex.instRing Complex.partialOrder Complex.instStarRing A →
        ∃ (l : Real),
          And (@LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) l)
            (∀ (x : I → Complex),
              @LE.le Real Real.instLE
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) l
                  (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                    (@Norm.norm (I → Complex)
                      (@NormedRing.toNorm (I → Complex)
                        (@Pi.normedRing I (fun (a : I) ↦ Complex) inst fun (i : I) ↦
                          @CStarAlgebra.toNormedRing Complex
                            (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))
                      x)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@DFunLike.coe
                  (@AddMonoidHom Complex Real
                    (@AddZero.mk Complex
                      (@AddMonoid.toZero Complex
                        (@AddCommMonoid.toAddMonoid Complex
                          (@Semiring.toAddCommMonoid Complex
                            (@Ring.toSemiring Complex
                              (@CommRing.toRing Complex
                                (@Field.toCommRing Complex
                                  (@NormedField.toField Complex
                                    (@DenselyNormedField.toNormedField Complex
                                      (@RCLike.toDenselyNormedField Complex Complex.instRCLike)))))))))
                      (@AddSemigroup.toAdd Complex
                        (@AddMonoid.toAddSemigroup Complex
                          (@AddCommMonoid.toAddMonoid Complex
                            (@Semiring.toAddCommMonoid Complex
                              (@Ring.toSemiring Complex
                                (@CommRing.toRing Complex
                                  (@Field.toCommRing Complex
                                    (@NormedField.toField Complex
                                      (@DenselyNormedField.toNormedField Complex
                                        (@RCLike.toDenselyNormedField Complex Complex.instRCLike)))))))))))
                    (@AddZeroClass.toAddZero Real (@AddMonoid.toAddZeroClass Real Real.instAddMonoid)))
                  Complex (fun (x : Complex) ↦ Real)
                  (@AddMonoidHom.instFunLike Complex Real
                    (@AddZero.mk Complex
                      (@AddMonoid.toZero Complex
                        (@AddCommMonoid.toAddMonoid Complex
                          (@Semiring.toAddCommMonoid Complex
                            (@Ring.toSemiring Complex
                              (@CommRing.toRing Complex
                                (@Field.toCommRing Complex
                                  (@NormedField.toField Complex
                                    (@DenselyNormedField.toNormedField Complex
                                      (@RCLike.toDenselyNormedField Complex Complex.instRCLike)))))))))
                      (@AddSemigroup.toAdd Complex
                        (@AddMonoid.toAddSemigroup Complex
                          (@AddCommMonoid.toAddMonoid Complex
                            (@Semiring.toAddCommMonoid Complex
                              (@Ring.toSemiring Complex
                                (@CommRing.toRing Complex
                                  (@Field.toCommRing Complex
                                    (@NormedField.toField Complex
                                      (@DenselyNormedField.toNormedField Complex
                                        (@RCLike.toDenselyNormedField Complex Complex.instRCLike)))))))))))
                    (@AddZeroClass.toAddZero Real (@AddMonoid.toAddZeroClass Real Real.instAddMonoid)))
                  (@RCLike.re Complex Complex.instRCLike)
                  (@dotProduct I Complex inst Complex.instMul Complex.instAddCommMonoid
                    (@Star.star (I → Complex)
                      (@Pi.instStarForall I (fun (a : I) ↦ Complex) fun (i : I) ↦
                        @InvolutiveStar.toStar Complex
                          (@StarAddMonoid.toInvolutiveStar Complex
                            (@AddCommMonoid.toAddMonoid Complex
                              (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex
                                      Complex.instNonUnitalCommRing)))))
                            (@StarRing.toStarAddMonoid Complex
                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                              Complex.instStarRing)))
                      x)
                    (@Matrix.mulVec I I Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                      inst A x)))) := by
  intro I inst _ A hA
  set f : (I → ℂ) → ℝ := fun x => RCLike.re (star x ⬝ᵥ A.mulVec x) with hf
  have hpos : ∀ x : I → ℂ, x ≠ 0 → 0 < f x := fun x hx => by
    exact ZbYha7.pos A hA x hx
  have hS : ∃ l : ℝ, 0 < l ∧ ∀ y ∈ Metric.sphere (0 : I → ℂ) 1, l ≤ f y := by
    by_cases hne : (Metric.sphere (0 : I → ℂ) 1).Nonempty
    · obtain ⟨y0, hy0, hmin⟩ := (isCompact_sphere (0 : I → ℂ) 1).exists_isMinOn hne
        (ZbYha7.cont A).continuousOn
      refine ⟨f y0, hpos y0 ?_, fun y hy => hmin hy⟩
      intro h; rw [h] at hy0; simp at hy0
    · exact ⟨1, one_pos, fun y hy => (hne ⟨y, hy⟩).elim⟩
  obtain ⟨l, hl, hlS⟩ := hS
  refine ⟨l, hl, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set y : I → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hy
  have hyS : y ∈ Metric.sphere (0 : I → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, hy, norm_smul]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    field_simp
  have h1 := hlS y hyS
  have hxy : x = ((‖x‖ : ℝ) : ℂ) • y := by
    rw [hy, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  have h2 : f x = ‖x‖ ^ 2 * f y := by
    conv_lhs => rw [hxy]
    exact ZbYha7.scale A y ‖x‖
  change l * ‖x‖ ^ 2 ≤ f x
  rw [h2, mul_comm l]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestSide
section
theorem UpperTheory.Reformulated.B.Yhc6.main :
    ∀ {k : Type} [inst : Field k] [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {n : ℕ} (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) (m : ℕ),
      ((↑g : Matrix (Fin n) (Fin n) k) * x * (↑g⁻¹ : Matrix (Fin n) (Fin n) k)) ^ m =
        (↑g : Matrix (Fin n) (Fin n) k) * x ^ m * (↑g⁻¹ : Matrix (Fin n) (Fin n) k) := by
  intro k _ _ _ _ n g x m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestTail
section
theorem UpperTheory.Reformulated.B.Yhd2.main :
    ∀ {G M : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
      [inst_4 : AddCommGroup M] [inst_5 : _root_.Module ℂ M] (ρ : Representation ℂ G M) (x : M),
      IsOpen {g : G | ((ρ : G → M →ₗ[ℂ] M) g : M → M) x = x} →
        (Set.range fun (g : G) ↦ ((ρ : G → M →ₗ[ℂ] M) g : M → M) x).Countable := by
  intro G M _ _ _ _ _ _ ρ x hS
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  apply (hDc.image (fun (g : G) ↦ ((ρ : G → M →ₗ[ℂ] M) g : M → M) x)).mono
  rintro _ ⟨g, rfl⟩
  have hU : IsOpen ((fun h : G ↦ g⁻¹ * h) ⁻¹' {g : G | ((ρ : G → M →ₗ[ℂ] M) g : M → M) x = x}) :=
    hS.preimage (continuous_const.mul continuous_id)
  have hne : ((fun h : G ↦ g⁻¹ * h) ⁻¹' {g : G | ((ρ : G → M →ₗ[ℂ] M) g : M → M) x = x}).Nonempty :=
    ⟨g, by simp⟩
  obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open hU hne
  refine ⟨d, hdD, ?_⟩
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hdU
  have : d = g * (g⁻¹ * d) := by group
  simp only
  rw [this, map_mul, Module.End.mul_apply, hdU]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestTer
section
theorem UpperTheory.Reformulated.B.Yha6.main :
    ∀ (Λ : Type) [inst : AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : Submodule ℤ Λ),
      (∀ (v : Λ) (n : ℤ), n ≠ (0 : ℤ) → n • v ∈ N → v ∈ N) →
        ∃ (k : ℕ) (n : ℕ) (b : Module.Basis (Fin n) ℤ Λ) (f : Fin k → Fin n),
          Function.Injective f ∧ Submodule.span ℤ (Set.range fun (i : Fin k) ↦ (b : Fin n → Λ) (f i)) = N := by
  intro Λ _ _ _ N hsat
  obtain ⟨k, snf⟩ := Submodule.smithNormalForm (Module.finBasis ℤ Λ) N
  refine ⟨k, _, snf.bM, snf.f, snf.f.injective, ?_⟩
  have ha : ∀ i, snf.a i ≠ 0 := by
    intro i h
    have h1 := snf.snf i
    rw [h, zero_smul] at h1
    exact snf.bN.ne_zero i (Subtype.ext h1)
  have hmem : ∀ i, snf.bM (snf.f i) ∈ N := by
    intro i
    apply hsat _ (snf.a i) (ha i)
    rw [← snf.snf i]
    exact (snf.bN i).2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmem i
  · intro x hx
    have hx' : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (Set.range snf.bN) := by
      rw [snf.bN.span_eq]; trivial
    have := Submodule.apply_mem_span_image_of_mem_span N.subtype hx'
    simp only [Submodule.subtype_apply] at this
    refine Submodule.span_le.mpr ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp only [Submodule.subtype_apply, snf.snf i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSide
section
theorem UpperTheory.Reformulated.B.DYha3.main :
    ∀ {E : Type} [inst : Field E] [NumberField E] (x : E), ∃ (n : ℕ), (0 : ℕ) < n ∧ IsIntegral ℤ ((↑n : E) * x) := by
  intro E _ _ x
  obtain ⟨y, hy, h⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr
    (Algebra.IsIntegral.isIntegral (R := ℚ) x).isAlgebraic).exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h
    simpa using h
  · rw [e] at h
    simpa using h.neg
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideAlt
section
theorem UpperTheory.Reformulated.B.Yhd5.main :
    ∀ {n : ℕ} {U : Set (Fin n → ℂ)} {ι : Type} (u : Finset ι) {f : ι → (Fin n → ℂ) → ℂ},
      (∀ i ∈ u, DifferentiableOn ℂ (f i) U) → DifferentiableOn ℂ (fun (t : Fin n → ℂ) ↦ ∏ i ∈ u, f i t) U := by
  intro n U ι u f h
  classical
  induction u using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    have h1 : DifferentiableOn ℂ (f a) U := h a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simp only [Finset.prod_insert ha]
    exact h1.mul h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideExtra
section
namespace MeasureEqCardCosetsMul
end MeasureEqCardCosetsMul

theorem UpperTheory.Reformulated.B.Yla7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G]
      [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] {I : Subgroup G},
      IsOpen (↑I : Set G) →
        ∀ {D : Set G},
          (∀ g ∈ D, ∀ i ∈ I, g * i ∈ D) →
            ∀ (S : Finset (G ⧸ I)),
              (∀ (q : G ⧸ I), q ∈ S ↔ Quotient.out q ∈ D) →
                (μ : Set G → ENNReal) D = (↑S.card : ENNReal) * (μ : Set G → ENNReal) (↑I : Set G) := by
  intro G _ _ _ _ _ μ _ I hI D hD S hS
  classical
  set f : G ⧸ I → Set G := fun q => (fun h => (Quotient.out q)⁻¹ * h) ⁻¹' (I : Set G) with hf
  have hmem : ∀ q x, x ∈ f q ↔ (Quotient.out q)⁻¹ * x ∈ I := fun q x => Iff.rfl
  have hmk : ∀ q x, x ∈ f q → (QuotientGroup.mk x : G ⧸ I) = q := by
    intro q x hx
    rw [hmem] at hx
    have : (QuotientGroup.mk (Quotient.out q) : G ⧸ I) = QuotientGroup.mk x :=
      QuotientGroup.eq.mpr hx
    rw [← this]
    exact Quotient.out_eq' q
  have hDeq : D = ⋃ q ∈ S, f q := by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · intro hx
      refine ⟨(QuotientGroup.mk x : G ⧸ I), ?_, ?_⟩
      · rw [hS]
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul I x
        rw [hh]
        exact hD x hx h h.2
      · rw [hmem]
        have : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk x : G ⧸ I)) : G ⧸ I) = QuotientGroup.mk x :=
          Quotient.out_eq' _
        exact QuotientGroup.eq.mp this
    · rintro ⟨q, hq, hx⟩
      rw [hmem] at hx
      have h1 := hD _ ((hS q).mp hq) _ hx
      simpa using h1
  have hdisj : (S : Set (G ⧸ I)).PairwiseDisjoint f := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    exact hab ((hmk a x hxa).symm.trans (hmk b x hxb))
  have hmeas : ∀ q ∈ S, MeasurableSet (f q) := by
    intro q _
    exact (hI.preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hDeq, MeasureTheory.measure_biUnion_finset hdisj hmeas]
  have : ∀ q ∈ S, μ (f q) = μ (I : Set G) := by
    intro q _
    exact MeasureTheory.measure_preimage_mul μ _ _
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsSideFurther
section
theorem UpperTheory.Reformulated.B.Yla6.main :
    ∀ {a b c d : Type} [inst : Fintype b] [inst_1 : Fintype c] (A : Matrix a b ℂ) (M : Matrix b c ℂ) (B : Matrix c d ℂ)
      {α μ β : ℝ},
      (∀ (i : a) (j : b), ‖A i j‖ ≤ α) →
        (∀ (i : b) (j : c), ‖M i j‖ ≤ μ) →
          (∀ (i : c) (j : d), ‖B i j‖ ≤ β) →
            ∀ (i : a) (j : d), ‖(A * M * B) i j‖ ≤ (↑(Fintype.card b) : ℝ) * (↑(Fintype.card c) : ℝ) * (α * μ * β) := by
  intro a b c d _ _ A M B α μ β hA hM hB i j
  have h1 : ‖(A * M * B) i j‖ ≤ ∑ l : c, ∑ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ := by
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => (norm_sum_le _ _).trans ?_)
    simp [norm_mul]
  have h2 : ∀ l : c, ∀ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ ≤ α * μ * β := by
    intro l k
    have ha : 0 ≤ α := (norm_nonneg _).trans (hA i k)
    have hm : 0 ≤ μ := (norm_nonneg _).trans (hM k l)
    exact mul_le_mul (mul_le_mul (hA i k) (hM k l) (norm_nonneg _) ha) (hB l j) (norm_nonneg _)
      (mul_nonneg ha hm)
  calc ‖(A * M * B) i j‖ ≤ ∑ l : c, ∑ k : b, ‖A i k‖ * ‖M k l‖ * ‖B l j‖ := h1
    _ ≤ ∑ _l : c, ∑ _k : b, α * μ * β :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => h2 l k
    _ = (↑(Fintype.card b) : ℝ) * (↑(Fintype.card c) : ℝ) * (α * μ * β) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
end

