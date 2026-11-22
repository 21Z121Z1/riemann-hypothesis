import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RadicalEltMovingDualToMajorant
section
open scoped ComplexOrder
open Matrix

namespace GlobalTheory

theorem radical_elt_moving_dual_to_majorant (n p : ℕ) (J θ : Matrix (Fin n) (Fin n) ℂ)
    (hJ : J.conjTranspose = J) (hθ : θ * θ = 1) (hQ : (J * θ).PosDef)
    (X₂ Y₂ : Matrix (Fin n) (Fin p) ℂ) (hXX : X₂.conjTranspose * J * X₂ = 0)
    (hYY : Y₂.conjTranspose * J * Y₂ = 0) (hXY : X₂.conjTranspose * J * Y₂ = 1) :
    ∃ u₁ : GL (Fin n) ℂ, (u₁.1).conjTranspose * J * u₁.1 = J ∧ u₁.1 * X₂ = X₂ ∧
      (∀ v : Fin n → ℂ, Matrix.mulVec (X₂.conjTranspose * J) v = 0 →
        ∃ w : Fin p → ℂ, Matrix.mulVec u₁.1 v - v = Matrix.mulVec X₂ w) ∧
      θ * X₂ = u₁.1 * Y₂ * (X₂.conjTranspose * (J * θ) * X₂) := by
  have hθJ : θᴴ * J = J * θ := by
    have := hQ.isHermitian.eq
    rwa [conjTranspose_mul, hJ] at this
  have hYX : Y₂ᴴ * J * X₂ = 1 := by
    have := congrArg conjTranspose hXY
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hinj : Function.Injective X₂.mulVec := by
    intro a b hab
    have := congrArg (fun v => (Y₂ᴴ * J).mulVec v) hab
    simpa [Matrix.mulVec_mulVec, hYX] using this
  have hP : (X₂ᴴ * (J * θ) * X₂).PosDef := hQ.conjTranspose_mul_mul_same hinj
  obtain ⟨P, hPdef⟩ : ∃ P, P = X₂ᴴ * (J * θ) * X₂ := ⟨_, rfl⟩
  rw [← hPdef] at hP ⊢
  have hdet : IsUnit P.det := isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hPiH : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.isHermitian.eq]
  obtain ⟨Y', hY'⟩ : ∃ Y', Y' = θ * X₂ * P⁻¹ := ⟨_, rfl⟩
  have hXY' : X₂ᴴ * J * Y' = 1 := by
    rw [← hPPi, hY', hPdef]; simp only [Matrix.mul_assoc]
  have hY'Y' : Y'ᴴ * J * Y' = 0 := by
    have h1 : ∀ B : Matrix (Fin n) (Fin p) ℂ, θᴴ * (J * (θ * B)) = J * B := by
      intro B
      rw [← Matrix.mul_assoc, hθJ, Matrix.mul_assoc, ← Matrix.mul_assoc θ, hθ, Matrix.one_mul]
    have h2 : X₂ᴴ * (J * (X₂ * P⁻¹)) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.zero_mul]
    rw [hY']
    simp only [conjTranspose_mul, hPiH, Matrix.mul_assoc, h1, h2, Matrix.mul_zero]
  obtain ⟨D, hD⟩ : ∃ D, D = Y' - Y₂ := ⟨_, rfl⟩
  have hXD : X₂ᴴ * J * D = 0 := by rw [hD, Matrix.mul_sub, hXY', hXY, sub_self]
  have hDX : Dᴴ * J * X₂ = 0 := by
    have := congrArg conjTranspose hXD
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have hkey : Dᴴ * J * D + Dᴴ * J * Y₂ + Y₂ᴴ * J * D = 0 := by
    rw [hD]
    simp only [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] at hY'Y' hYY ⊢
    rw [hY'Y', hYY]
    abel

  have tXX : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (X₂ * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.zero_mul]
  have tXD : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (D * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXD, Matrix.zero_mul]
  have tDX : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), Dᴴ * (J * (X₂ * B)) = 0 := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hDX, Matrix.zero_mul]
  have tXY : ∀ {m : Type} (B : Matrix (Fin p) m ℂ), X₂ᴴ * (J * (Y₂ * B)) = B := by
    intro m B; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXY, Matrix.one_mul]
  have hXX' : X₂ᴴ * (J * X₂) = 0 := by rw [← Matrix.mul_assoc, hXX]
  have hXD' : X₂ᴴ * (J * D) = 0 := by rw [← Matrix.mul_assoc, hXD]
  have hDX' : Dᴴ * (J * X₂) = 0 := by rw [← Matrix.mul_assoc, hDX]
  have hXY'' : X₂ᴴ * (J * Y₂) = 1 := by rw [← Matrix.mul_assoc, hXY]
  obtain ⟨E, hE⟩ : ∃ E, E = Dᴴ * J * Y₂ := ⟨_, rfl⟩
  have hE' : Dᴴ * (J * Y₂) = E := by rw [hE, Matrix.mul_assoc]
  obtain ⟨u, hu⟩ : ∃ u : Matrix (Fin n) (Fin n) ℂ,
      u = 1 + (D * X₂ᴴ * J - X₂ * Dᴴ * J + X₂ * E * X₂ᴴ * J) := ⟨_, rfl⟩
  have huJ : uᴴ * J * u = J := by
    have hexp : uᴴ * J * u = J + J * X₂ * (Dᴴ * J * D + Dᴴ * J * Y₂ + Y₂ᴴ * J * D) * X₂ᴴ * J := by
      rw [hu, hE]
      simp only [conjTranspose_add, conjTranspose_sub, conjTranspose_mul, conjTranspose_one,
        conjTranspose_conjTranspose, hJ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, Matrix.mul_one, tXX, tXD, tDX,
        hXX', hXD', hDX', Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, sub_zero, zero_sub]
      abel
    rw [hexp, hkey]; simp
  have huX : u * X₂ = X₂ := by
    rw [hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, hXX', hDX',
      Matrix.mul_zero, add_zero, sub_zero]
  have huY : u * Y₂ = Y' := by
    rw [hu]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.one_mul, hXY'',
      Matrix.mul_one, hE']
    rw [hD]; abel
  have hdetJ : J.det ≠ 0 := by
    intro h0
    have := hQ.det_pos
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact lt_irrefl _ this
  have hudet : IsUnit u.det := by
    refine isUnit_iff_ne_zero.mpr fun h0 => hdetJ ?_
    have := congrArg Matrix.det huJ
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  have huU : IsUnit u := (Matrix.isUnit_iff_isUnit_det u).mpr hudet
  refine ⟨huU.unit, ?_, ?_, ?_, ?_⟩
  · simpa using huJ
  · simpa using huX
  · intro v hv
    have hv' : X₂ᴴ *ᵥ (J *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec]; exact hv
    refine ⟨-(Dᴴ *ᵥ (J *ᵥ v)), ?_⟩
    simp only [IsUnit.unit_spec, hu, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero, Matrix.mulVec_neg]
    abel
  · simp only [IsUnit.unit_spec, huY, hY', Matrix.mul_assoc, hPiP, Matrix.mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationLeCardOfSpan
section
namespace GlobalTheory

theorem eq_zero_of_sum_eq_zero_of_unit_mul_pow {R : Type*} [CommRing R] [IsDomain R] {ϖ : R}
    (hϖ : Irreducible ϖ) {e : ℕ} (c : Fin e → R)
    (hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : R), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n))
    (hsum : ∑ i, c i = 0) : ∀ i, c i = 0 := by
  classical
  by_contra hne
  push_neg at hne
  choose! n w hw hcw using hc
  set S := Finset.univ.filter (fun i => c i ≠ 0) with hS
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [hS, hi]⟩
  obtain ⟨i0, hi0S, hmin⟩ := S.exists_min_image (fun i => i.val + e * n i) hSne
  have hi0 : c i0 ≠ 0 := (Finset.mem_filter.1 hi0S).2
  have hdvd : ∀ i ∈ Finset.univ.erase i0, ϖ ^ (i0.val + e * n i0 + 1) ∣ c i := by
    intro i hi
    have hii0 : i ≠ i0 := Finset.ne_of_mem_erase hi
    by_cases hci : c i = 0
    · rw [hci]; exact dvd_zero _
    · have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hci⟩
      have hle : i0.val + e * n i0 ≤ i.val + e * n i := hmin i hiS
      have hne' : i.val + e * n i ≠ i0.val + e * n i0 := by
        intro heq
        apply hii0
        apply Fin.ext
        have h1 : (i.val + e * n i) % e = i.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
        have h2 : (i0.val + e * n i0) % e = i0.val := by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i0.isLt]
        rw [← h1, ← h2, heq]
      rw [hcw i hci]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  obtain ⟨X, hX⟩ := Finset.dvd_sum hdvd
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), hX, hcw i0 hi0] at hsum
  have h0 : ϖ ^ (i0.val + e * n i0) * (w i0 + ϖ * X) = 0 := by rw [← hsum]; ring
  have h1 : w i0 + ϖ * X = 0 :=
    (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hϖ.ne_zero)
  have h2 : ϖ ∣ w i0 := ⟨-X, by linear_combination h1⟩
  exact hϖ.not_isUnit (isUnit_of_dvd_unit h2 (hw i0 hi0))

theorem ramification_le_card_of_span :
    ∀ (F : Type) [Field F] (T' T'' : Subring F), IsDiscreteValuationRing T' →
      IsDiscreteValuationRing T'' → ∀ (h : T' ≤ T''),
      (∀ x ∈ T', (∃ y ∈ T'', x * y = 1) → ∃ y ∈ T', x * y = 1) → ∀ (s : Finset F),
      (∀ y ∈ T'', ∃ d ∈ T', d ≠ 0 ∧ d * y ∈ Submodule.span T' (s : Set F)) →
      ∀ π : T', Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ ∃ e : ℕ, 1 ≤ e ∧ e ≤ s.card ∧
        Associated (Subring.inclusion h π) (ϖ ^ e) := by
  intro F _ T' T'' h1 h2 h hdom s hspan π hπ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T''
  have hπ0 : Subring.inclusion h π ≠ 0 := by
    intro h0
    apply hπ.ne_zero
    apply Subtype.ext
    have := congrArg Subtype.val h0
    simpa using this
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hϖ
  refine ⟨ϖ, hϖ, e, ?_, ?_, he⟩
  · rcases Nat.eq_zero_or_pos e with rfl | hpos
    · exfalso
      rw [pow_zero] at he
      have hu : IsUnit (Subring.inclusion h π) := he.isUnit_iff.2 isUnit_one
      obtain ⟨y, hy⟩ := hu.exists_right_inv
      obtain ⟨z, hzT', hz⟩ := hdom (π : F) π.2
        ⟨(y : F), y.2, by simpa using congrArg Subtype.val hy⟩
      exact hπ.not_isUnit (isUnit_iff_exists_inv.2 ⟨⟨z, hzT'⟩, Subtype.ext hz⟩)
    · exact hpos
  ·
    choose d hdT hd0 hdspan using
      fun i : Fin e => hspan ((ϖ ^ (i : ℕ) : T'') : F) (ϖ ^ (i : ℕ)).2
    set D : F := ∏ i, d i with hDdef
    have hDT : D ∈ T' := Subring.prod_mem _ (fun i _ => hdT i)
    have hD0 : D ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)
    let f : Fin e → F := fun i => D * ((ϖ ^ (i : ℕ) : T'') : F)
    have hfspan : ∀ i, f i ∈ Submodule.span T' (s : Set F) := by
      intro i
      have hmem : (∏ j ∈ Finset.univ.erase i, d j) ∈ T' :=
        Subring.prod_mem _ (fun j _ => hdT j)
      have := Submodule.smul_mem (Submodule.span T' (s : Set F))
        (⟨∏ j ∈ Finset.univ.erase i, d j, hmem⟩ : T') (hdspan i)
      rw [Subring.smul_def] at this
      have heq : f i = (∏ j ∈ Finset.univ.erase i, d j) * (d i * ((ϖ ^ (i : ℕ) : T'') : F)) := by
        simp only [f, hDdef]
        rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)]
        ring
      rw [heq]
      exact this
    have hli : LinearIndependent T' f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      obtain ⟨v, hv⟩ := he.symm
      let c : Fin e → T'' := fun i =>
        Subring.inclusion h (g i * ⟨D, hDT⟩) * ϖ ^ (i : ℕ)
      have hcsum : ∑ i, c i = 0 := by
        apply Subtype.ext
        have hcs : ((∑ i, c i : T'') : F) = ∑ i, g i • f i := by
          simp [c, f, Subring.smul_def, mul_assoc]
        rw [hcs, hg]
        rfl
      have hc : ∀ i, c i ≠ 0 → ∃ (n : ℕ) (w : T''), IsUnit w ∧ c i = w * ϖ ^ (i.val + e * n) := by
        intro i hci
        have ha : g i * ⟨D, hDT⟩ ≠ 0 := by
          intro h0; apply hci; simp only [c, h0, map_zero, zero_mul]
        obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
        refine ⟨m, Subring.inclusion h (u : T') * (v : T'') ^ m,
          (u.isUnit.map (Subring.inclusion h)).mul (v.isUnit.pow m), ?_⟩
        simp only [c]
        rw [hu, map_mul, map_pow, ← hv]
        ring
      have hc0 := eq_zero_of_sum_eq_zero_of_unit_mul_pow hϖ c hc hcsum
      intro i
      have := hc0 i
      simp only [c, mul_eq_zero, pow_eq_zero_iff', hϖ.ne_zero, false_and, or_false] at this
      have h3 : g i * ⟨D, hDT⟩ = 0 := by
        apply Subtype.ext
        have := congrArg Subtype.val this
        simpa using this
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h4
      · exact absurd (congrArg Subtype.val h4) hD0
    let f' : Fin e → Submodule.span T' (s : Set F) := fun i => ⟨f i, hfspan i⟩
    have hli' : LinearIndependent T' f' :=
      LinearIndependent.of_comp (Submodule.span T' (s : Set F)).subtype hli
    have hcard := hli'.cardinal_le_rank.trans (rank_span_finset_le s)
    simpa using hcard

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComapIncludeRightField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem range_comap_includeRight_field :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (k : Type) [Field k] [Algebra A k],
    Set.range (PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom) = {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A k)} := by
  intro A B _ _ _ k _ _
  ext r
  constructor
  · rintro ⟨q, rfl⟩
    show Ideal.comap (algebraMap A B) (Ideal.comap _ q.asIdeal) = _
    rw [Ideal.comap_comap, ← Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap,
      ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ q.asIdeal),
      ← RingHom.ker_eq_comap_bot]
  · intro hr
    change Ideal.comap (algebraMap A B) r.asIdeal = RingHom.ker (algebraMap A k) at hr
    set f := algebraMap A k with hf
    let I := RingHom.ker f
    let K := r.asIdeal.ResidueField
    let g : A →+* K := (algebraMap B K).comp (algebraMap A B)
    have hg : RingHom.ker g = I := by
      change RingHom.ker ((algebraMap B K).comp (algebraMap A B)) = RingHom.ker f
      rw [← RingHom.comap_ker, Ideal.ker_algebraMap_residueField, hr]
    have hIg : ∀ a ∈ I, g a = 0 := fun a ha => by rw [← RingHom.mem_ker, hg]; exact ha
    let ι₁ : A ⧸ I →+* k := RingHom.kerLift f
    let ι₂ : A ⧸ I →+* K := Ideal.Quotient.lift I g hIg
    have inj₁ : Function.Injective ι₁ := RingHom.kerLift_injective f
    have inj₂ : Function.Injective ι₂ := RingHom.lift_injective_of_ker_le_ideal I hIg hg.le
    letI : Algebra (A ⧸ I) k := ι₁.toAlgebra
    letI : Algebra (A ⧸ I) K := ι₂.toAlgebra
    haveI : Nontrivial (k ⊗[A ⧸ I] K) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain (A ⧸ I) k K inj₁ inj₂
    haveI : SMulCommClass (A ⧸ I) A k := ⟨fun x a y => by
      simp only [Algebra.smul_def]; ring⟩
    let α : k →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.includeLeft
    let β : B →ₐ[A] k ⊗[A ⧸ I] K :=
      { ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) with
        commutes' := fun a => by
          change (1 : k) ⊗ₜ[A ⧸ I] (algebraMap (A ⧸ I) K (Ideal.Quotient.mk I a)) = _
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := K),
            ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
          rfl }
    let φ : k ⊗[A] B →ₐ[A] k ⊗[A ⧸ I] K := Algebra.TensorProduct.lift α β (fun _ _ => Commute.all _ _)
    obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[A ⧸ I] K)
    refine ⟨PrimeSpectrum.comap φ.toRingHom ⟨m, hm.isPrime⟩, ?_⟩
    ext1
    show Ideal.comap _ (Ideal.comap φ.toRingHom m) = r.asIdeal
    have hcomp : φ.toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B).toRingHom =
        ((Algebra.TensorProduct.includeRight : K →ₐ[A ⧸ I] k ⊗[A ⧸ I] K).toRingHom.comp
          (algebraMap B K)) := by
      ext b
      simp [φ, α, β, Algebra.TensorProduct.lift_tmul]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, Ideal.eq_bot_of_prime (Ideal.comap _ m),
      ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeOfGrowthInRadius
section
open Filter Topology

namespace GlobalTheory

theorem rank_le_of_growth_in_radius : ∀ (D : ℕ) (f : ℝ → ℕ → ℝ) (α γ ρ t₀ t₁ : ℝ), 0 ≤ ρ →
    (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => f t m / (m : ℝ) ^ (D + 1)) atTop (𝓝 (α + γ * t))) →
    (∀ (t : ℝ) (m Q : ℕ), 0 < m → 0 < Q → ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) →
      ρ * (m : ℝ) ^ D * Real.log Q ≤ f t m) → ρ ≤ γ := by
  intro D f α γ ρ t₀ t₁ hρ hlim hbd
  have hev : ∀ᶠ m : ℕ in atTop, ρ * (m : ℝ) ^ D * Real.exp (-(m : ℝ)) ≤ 1 := by
    have h1 : Tendsto (fun x : ℝ => x ^ D * Real.exp (-x)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero D
    have h2 : Tendsto (fun m : ℕ => ρ * ((m : ℝ) ^ D * Real.exp (-(m : ℝ)))) atTop (𝓝 (ρ * 0)) :=
      (h1.comp tendsto_natCast_atTop_atTop).const_mul ρ
    rw [mul_zero] at h2
    filter_upwards [h2.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with m hm
    rw [mul_assoc]; exact hm.le
  have key : ∀ t, max t₀ (t₁ + 2) ≤ t → ρ * (t - t₁ - 2) ≤ α + γ * t := by
    intro t ht
    have ht0 : t₀ ≤ t := le_trans (le_max_left _ _) ht
    have ht1 : t₁ + 2 ≤ t := le_trans (le_max_right _ _) ht
    refine ge_of_tendsto (hlim t ht0) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with m hm hm1
    have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
    have hm1' : (1:ℝ) ≤ m := by exact_mod_cast hm1
    set x := Real.exp ((t - t₁ - 1) * m) with hx
    have hx2 : 2 ≤ x := by
      have : 1 ≤ (t - t₁ - 1) * m := by nlinarith
      have h := Real.add_one_le_exp ((t - t₁ - 1) * m)
      linarith
    set Q := ⌊x⌋₊ with hQ
    have hQle : (Q : ℝ) ≤ x := Nat.floor_le (by linarith)
    have hQgt : x < Q + 1 := Nat.lt_floor_add_one x
    have hQpos : 0 < Q := by
      rw [hQ]; exact Nat.floor_pos.mpr (by linarith)
    have e2 : Real.exp (-(m:ℝ)) ≤ 1 / 2 := by
      have h := Real.add_one_le_exp (m:ℝ)
      have hp : Real.exp (-(m:ℝ)) * Real.exp m = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-(m:ℝ))]
    have hQge : Real.exp ((t - t₁ - 2) * m) ≤ Q := by
      have e1 : Real.exp ((t - t₁ - 2) * m) = x * Real.exp (-(m:ℝ)) := by
        rw [hx, ← Real.exp_add]; congr 1; ring
      rw [e1]
      have : x * Real.exp (-(m:ℝ)) ≤ x * (1 / 2) := mul_le_mul_of_nonneg_left e2 (by linarith)
      linarith
    have e3 : x * Real.exp (t₁ * m) = Real.exp (-(m:ℝ)) * Real.exp (t * m) := by
      rw [hx, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hρm : 0 ≤ ρ * (m : ℝ) ^ D := mul_nonneg hρ (pow_nonneg hmpos.le _)
    have hcond : ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m) ≤ Real.exp (t * m) := by
      calc ρ * (m : ℝ) ^ D * Q * Real.exp (t₁ * m)
          ≤ ρ * (m : ℝ) ^ D * x * Real.exp (t₁ * m) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQle hρm) (Real.exp_pos _).le
        _ = (ρ * (m : ℝ) ^ D * Real.exp (-(m:ℝ))) * Real.exp (t * m) := by
            rw [mul_assoc (ρ * (m : ℝ) ^ D) x, e3]; ring
        _ ≤ 1 * Real.exp (t * m) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
        _ = Real.exp (t * m) := one_mul _
    have hb := hbd t m Q (by omega) hQpos hcond
    have hlog : (t - t₁ - 2) * (m : ℝ) ≤ Real.log Q :=
      calc (t - t₁ - 2) * (m : ℝ) = Real.log (Real.exp ((t - t₁ - 2) * m)) := (Real.log_exp _).symm
        _ ≤ Real.log Q := Real.log_le_log (Real.exp_pos _) hQge
    rw [le_div_iff₀ (by positivity)]
    calc ρ * (t - t₁ - 2) * (m : ℝ) ^ (D + 1) = ρ * (m : ℝ) ^ D * ((t - t₁ - 2) * m) := by ring
      _ ≤ ρ * (m : ℝ) ^ D * Real.log Q := mul_le_mul_of_nonneg_left hlog hρm
      _ ≤ f t m := hb
  by_contra h
  push_neg at h
  have hd : 0 < ρ - γ := sub_pos.mpr h
  set T := max (max t₀ (t₁ + 2)) ((α + ρ * (t₁ + 2)) / (ρ - γ) + 1) with hTdef
  have hk := key T (le_max_left _ _)
  have hT : (α + ρ * (t₁ + 2)) / (ρ - γ) + 1 ≤ T := le_max_right _ _
  have hlt : (α + ρ * (t₁ + 2)) / (ρ - γ) < T := by linarith
  have h3 : α + ρ * (t₁ + 2) < T * (ρ - γ) := (div_lt_iff₀ hd).mp hlt
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatrixIdentityTransferToComplexMap
section
open Matrix

namespace GlobalTheory

noncomputable def endRealMatrixRingHom {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Module.End ℂ (Fin g → ℂ) →+* Matrix (Fin n) (Fin n) ℝ where
  toFun f := LinearMap.toMatrix e e (f.restrictScalars ℝ)
  map_one' := by
    have : ((1 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 1 := rfl
    rw [this]; exact LinearMap.toMatrix_one e
  map_mul' f h := by
    have : ((f * h).restrictScalars ℝ) = f.restrictScalars ℝ * h.restrictScalars ℝ := rfl
    rw [this]; exact LinearMap.toMatrix_mul e _ _
  map_zero' := by
    have : ((0 : Module.End ℂ (Fin g → ℂ)).restrictScalars ℝ) = 0 := rfl
    rw [this]; exact map_zero _
  map_add' f h := by
    have : ((f + h).restrictScalars ℝ) = f.restrictScalars ℝ + h.restrictScalars ℝ := rfl
    rw [this]; exact map_add _ _ _

theorem endRealMatrixRingHom_injective {g n : ℕ} (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) :
    Function.Injective (endRealMatrixRingHom e) := by
  intro f h hfh
  have h1 : f.restrictScalars ℝ = h.restrictScalars ℝ := (LinearMap.toMatrix e e).injective hfh
  exact LinearMap.restrictScalars_injective ℝ h1

theorem matrix_identity_transfer (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ))
    (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (Tq : Matrix (Fin n) (Fin n) ℚ)
    (hT : Tq.map (Rat.cast : ℚ → ℝ) = LinearMap.toMatrix e e (γ.restrictScalars ℝ))
    (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ)
    (hid : (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tq + ∑ i, c i • ((Polynomial.aeval Tq (p i)) ^ 2 * Tq)) :
    (1 : Module.End ℂ (Fin g → ℂ)) = c₀ • γ + ∑ i, c i • ((Polynomial.aeval γ (p i)) ^ 2 * γ) := by
  let F := (endRealMatrixRingHom e).toRatAlgHom
  let ψ : Matrix (Fin n) (Fin n) ℚ →ₐ[ℚ] Matrix (Fin n) (Fin n) ℝ := (Algebra.ofId ℚ ℝ).mapMatrix
  have hψ : ∀ M, ψ M = M.map (Rat.cast : ℚ → ℝ) := by
    intro M; ext i j; simp [ψ]
  have hFγ : F γ = ψ Tq := by rw [hψ, hT]; rfl
  apply endRealMatrixRingHom_injective e
  change F 1 = F _
  have key := congrArg ψ hid
  rw [map_one] at key
  rw [map_one, key]
  simp only [map_add, map_sum, map_smul, map_mul, map_pow, ← Polynomial.aeval_algHom_apply, hFγ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReDetRelation
section
open MvPolynomial

namespace GlobalTheory.MxDet

noncomputable def linF {ι : Type} [Fintype ι] (x : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (x i) * MvPolynomial.X i

noncomputable def iterD {ι : Type} : (m : ℕ) → (Fin m → ι) → (MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ)
  | 0, _ => LinearMap.id
  | m + 1, a => (MvPolynomial.pderiv (a 0)).toLinearMap ∘ₗ iterD m (Fin.tail a)

theorem pderiv_linF {ι : Type} [Fintype ι] (x : ι → ℝ) (j : ι) :
    MvPolynomial.pderiv j (linF x) = MvPolynomial.C (x j) := by
  rw [linF, map_sum, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [MvPolynomial.pderiv_X, Pi.single_apply, hb, hb.symm]
  · simp

theorem iterD_linF_pow {ι : Type} [Fintype ι] (x : ι → ℝ) (N : ℕ) : ∀ (m : ℕ) (a : Fin m → ι),
    iterD m a (linF x ^ N) = MvPolynomial.C ((N.descFactorial m : ℝ) * ∏ j, x (a j)) * linF x ^ (N - m)
  | 0, a => by simp [iterD]
  | m + 1, a => by
    rw [iterD, LinearMap.comp_apply, iterD_linF_pow x N m, Derivation.coeFn_coe, MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_pow, pderiv_linF, Nat.descFactorial_succ, Fin.prod_univ_succ, Nat.sub_sub]
    simp only [Fin.tail, Nat.cast_mul, map_mul, map_natCast]
    ring

theorem exists_functional {ι : Type} [Fintype ι] (e : ℕ) (I : (Fin e → ι) → ℝ) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ x : ι → ℝ, T (linF x ^ e) = ∑ a : Fin e → ι, (∏ j, x (a j)) * I a := by
  refine ⟨∑ a : Fin e → ι, (I a / (e.factorial : ℝ)) • (MvPolynomial.lcoeff ℝ 0 ∘ₗ iterD e a), fun x => ?_⟩
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have he : (e.factorial : ℝ) ≠ 0 := by exact_mod_cast e.factorial_ne_zero
  rw [LinearMap.smul_apply, LinearMap.comp_apply, iterD_linF_pow, Nat.sub_self, pow_zero, mul_one,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_zero_C, Nat.descFactorial_self, smul_eq_mul]
  field_simp

theorem det_comb {ι : Type} [Fintype ι] (e : ℕ) (H : ι → Matrix (Fin e) (Fin e) ℂ) (x : ι → ℝ) :
    (∑ i, (x i : ℂ) • H i).det = ∑ c : Fin e → ι, ((∏ l, x (c l) : ℝ) : ℂ) *
      ∑ σ : Equiv.Perm (Fin e), (Equiv.Perm.sign σ : ℂ) * ∏ l, H (c l) (σ l) l := by
  rw [Matrix.det_apply']
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  ring

end GlobalTheory.MxDet

theorem GlobalTheory.MxDet.re_det_relation : ∀ (ι J : Type) [Fintype ι] [Fintype J] (e : ℕ) (a : J → ℝ) (n : J → ι → ℝ), ∑ j, MvPolynomial.C (a j) * (∑ i, MvPolynomial.C (n j i) * MvPolynomial.X i : MvPolynomial ι ℝ) ^ e = 0 → ∀ H : ι → Matrix (Fin e) (Fin e) ℂ, ∑ j, a j * (∑ i, (n j i : ℂ) • H i).det.re = 0 := by
  intro ι J _ _ e a n hrel H
  obtain ⟨T, hT⟩ := GlobalTheory.MxDet.exists_functional e fun c : Fin e → ι =>
    (∑ σ : Equiv.Perm (Fin e), (Equiv.Perm.sign σ : ℂ) * ∏ l, H (c l) (σ l) l).re
  have h := congrArg T hrel
  simp only [map_sum, map_zero, MvPolynomial.C_mul', LinearMap.map_smul, smul_eq_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have := hT (n j)
  simp only [GlobalTheory.MxDet.linF, MvPolynomial.C_mul'] at this
  rw [this, GlobalTheory.MxDet.det_comb, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.re_ofReal_mul]
end

