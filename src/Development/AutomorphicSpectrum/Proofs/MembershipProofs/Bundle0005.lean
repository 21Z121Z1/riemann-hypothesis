import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0004
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.OrderOKOneInert
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0002

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.BigCellLocal
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

section Iso

variable {A : Type} [CommRing A] (σ : A →+* A) {ι : Type} [Fintype ι] [DecidableEq ι]

def Iso (D₁ D₂ M : Matrix ι ι A) : Prop := Mᵀ * D₁ * M.map σ = D₂

variable {σ}

omit [DecidableEq ι] in
theorem Iso.mul {D₁ D₂ D₃ M N : Matrix ι ι A} (h : Iso σ D₁ D₂ M) (h' : Iso σ D₂ D₃ N) : Iso σ D₁ D₃ (M * N) := by
  unfold Iso at *
  rw [transpose_mul, Matrix.map_mul, ← h', ← h]
  simp only [Matrix.mul_assoc]

theorem Iso.inv {D₁ D₂ M N : Matrix ι ι A} (h : Iso σ D₁ D₂ M) (hN : M * N = 1) : Iso σ D₂ D₁ N := by
  unfold Iso at *
  have h1 : M.map σ * N.map σ = 1 := by
    rw [← Matrix.map_mul, hN]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have h2 : Nᵀ * Mᵀ = 1 := by rw [← transpose_mul, hN, transpose_one]
  calc _ = (Nᵀ * Mᵀ) * D₁ * (M.map σ * N.map σ) := by rw [← h]; simp only [Matrix.mul_assoc]
    _ = D₁ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem Iso.isUnit_det {D₁ D₂ M : Matrix ι ι A} (h : Iso σ D₁ D₂ M) (hD : IsUnit D₂.det) : IsUnit M.det := by
  unfold Iso at h
  rw [← h, det_mul, det_mul, det_transpose] at hD
  exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hD)

end Iso

section Split

variable {A : Type} [CommRing A] {σ : A →+* A} {β : Type} [Fintype β] [DecidableEq β]

def Wm (A : Type) [CommRing A] (β : Type) [DecidableEq β] : Matrix (β ⊕ β) (β ⊕ β) A := fromBlocks 0 1 1 0

theorem Wm_mul_self : Wm A β * Wm A β = 1 := by
  simp [Wm, fromBlocks_multiply]

theorem Wm_det : IsUnit (Wm A β).det := by
  have := congrArg det (Wm_mul_self (A := A) (β := β))
  rw [det_mul, det_one] at this
  exact IsUnit.of_mul_eq_one _ this

theorem map_one' : (1 : Matrix β β A).map σ = 1 := Matrix.map_one _ (map_zero σ) (map_one σ)

theorem iso_Wm : Iso σ (Wm A β) (Wm A β) (Wm A β) := by
  simp [Iso, Wm, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_map, map_one']

theorem iso_n {s : Matrix β β A} (hs : s.map σ = -sᵀ) : Iso σ (Wm A β) (Wm A β) (fromBlocks 1 s 0 1) := by
  simp [Iso, Wm, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_map, map_one', hs]

theorem iso_col {a b c d : Matrix β β A} (h : Iso σ (Wm A β) (Wm A β) (fromBlocks a b c d)) :
    cᵀ * a.map σ + aᵀ * c.map σ = 0 := by
  simp only [Iso, Wm, fromBlocks_multiply, fromBlocks_transpose, fromBlocks_map] at h
  simpa using (fromBlocks_inj.mp h).1

theorem exists_skew [IsLocalRing A] (hσ : ∀ z, σ (σ z) = z) {w : A} (hw : w + σ w = 1) {z : A} (hz : IsUnit (z - σ z))
    {a b c d : Matrix β β A} (h : Iso σ (Wm A β) (Wm A β) (fromBlocks a b c d)) :
    ∃ s : Matrix β β A, s.map σ = -sᵀ ∧ IsUnit (a + s * c).det := by
  haveI : IsLocalHom σ := ⟨fun x hx => by simpa [hσ] using hx.map σ⟩
  set π := IsLocalRing.residue A with hπ
  set τ := IsLocalRing.ResidueField.map σ with hτ
  have hc : ∀ x, τ (π x) = π (σ x) := fun x => IsLocalRing.ResidueField.map_residue σ x
  have hm : ∀ m : Matrix β β A, (m.map π).map τ = (m.map σ).map π := fun m => by
    ext i j; simp [hc]
  have hdet := (h.isUnit_det Wm_det).map π
  rw [RingHom.map_det, RingHom.mapMatrix_apply, fromBlocks_map] at hdet
  obtain ⟨s, hs1, hs2⟩ := GlobalTheory.CompanionTheory.CommonTransversal.exists_skew_isUnit_det τ (a.map π)ᵀ (c.map π)ᵀ
    (fun x => by
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
      rw [← hπ, hc, hc, hσ])
    ⟨π z, fun e => by
      have := hz.map π
      rw [map_sub, ← hc, e, sub_self] at this
      exact not_isUnit_zero this⟩
    (by
      have := congrArg (fun m => m.map π) (iso_col h)
      simp only [Matrix.map_add _ (map_add π), Matrix.map_mul, Matrix.map_zero _ (map_zero π)] at this
      rw [transpose_map, transpose_map, transpose_transpose, transpose_transpose, hm, hm, add_comm]
      exact this)
    (fun v h1 h2 => by
      rw [vecMul_transpose] at h1 h2
      have h3 : fromBlocks (a.map π) (b.map π) (c.map π) (d.map π) *ᵥ Sum.elim v 0 = 0 := by
        rw [fromBlocks_mulVec]
        simp [h1, h2]
      have h4 := Matrix.eq_zero_of_mulVec_eq_zero hdet.ne_zero h3
      ext i
      exact congrFun h4 (Sum.inl i))
  choose f hf using (IsLocalRing.residue_surjective (R := A))
  refine ⟨Matrix.of fun i j => w * f (s j i) - σ (w * f (s i j)), ?_, ?_⟩
  · ext i j
    simp [hσ]
  · have e : (Matrix.of fun i j => w * f (s j i) - σ (w * f (s i j))).map π = sᵀ := by
      ext i j
      have h5 : τ (s i j) = - s j i := congrFun (congrFun hs1 j) i
      have h6 : π w + τ (π w) = 1 := by rw [hc, ← map_add, hw, map_one]
      have hf' : ∀ x, π (f x) = x := hf
      simp only [map_apply, of_apply, map_sub, ← hc, map_mul, hf', h5, transpose_apply]
      linear_combination s j i * h6
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
      Matrix.map_add _ (map_add π), Matrix.map_mul, e, ← det_transpose, transpose_add, transpose_mul, transpose_transpose]
    exact hs2.ne_zero

theorem decomp_split [IsLocalRing A] (hσ : ∀ z, σ (σ z) = z) {w : A} (hw : w + σ w = 1) {z : A} (hz : IsUnit (z - σ z))
    {h : Matrix (β ⊕ β) (β ⊕ β) A} (hh : Iso σ (Wm A β) (Wm A β) h) :
    ∃ s u t b d : Matrix β β A, Iso σ (Wm A β) (Wm A β) (fromBlocks 1 s 0 1) ∧
      Iso σ (Wm A β) (Wm A β) (fromBlocks 1 u 0 1) ∧ Iso σ (Wm A β) (Wm A β) (fromBlocks t b 0 d) ∧ IsUnit t.det ∧
      h = fromBlocks 1 s 0 1 * (Wm A β * fromBlocks 1 u 0 1 * Wm A β) * fromBlocks t b 0 d := by
  rw [← fromBlocks_toBlocks h] at hh ⊢
  generalize h.toBlocks₁₁ = a at *
  generalize h.toBlocks₁₂ = b at *
  generalize h.toBlocks₂₁ = c at *
  generalize h.toBlocks₂₂ = d at *
  obtain ⟨s, hs, ha⟩ := exists_skew hσ hw hz hh
  have h1 := (iso_n hs).mul hh
  simp only [fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, zero_add] at h1
  set a' := a + s * c with ha'
  have h2 := iso_col h1
  have i1 : a' * a'⁻¹ = 1 := mul_nonsing_inv _ ha
  have i2 : a'⁻¹ * a' = 1 := nonsing_inv_mul _ ha
  have i3 : a'.map σ * a'⁻¹.map σ = 1 := by rw [← Matrix.map_mul, i1, map_one']
  have i4 : a'⁻¹ᵀ * a'ᵀ = 1 := by rw [← transpose_mul, i1, transpose_one]
  have hu : (c * a'⁻¹).map σ = -(c * a'⁻¹)ᵀ := by
    have := congrArg (fun m => a'⁻¹ᵀ * m * a'⁻¹.map σ) h2
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero, Matrix.zero_mul] at this
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, i4, Matrix.mul_assoc _ (a'.map σ), i3] at this
    rw [Matrix.map_mul, transpose_mul, eq_neg_iff_add_eq_zero, add_comm]
    simpa using this
  have hs' : (-s).map σ = -(-s)ᵀ := by rw [Matrix.map_neg _ (map_neg σ), hs, transpose_neg]
  have hu' : (-(c * a'⁻¹)).map σ = -(-(c * a'⁻¹))ᵀ := by rw [Matrix.map_neg _ (map_neg σ), hu, transpose_neg]
  have h3 := ((iso_Wm.mul (iso_n hu')).mul iso_Wm).mul h1
  have e3 : Wm A β * fromBlocks 1 (-(c * a'⁻¹)) 0 1 * Wm A β * fromBlocks a' (b + s * d) c d =
      fromBlocks a' (b + s * d) 0 (d - c * a'⁻¹ * (b + s * d)) := by
    simp [Wm, fromBlocks_multiply, Matrix.mul_assoc, i2, sub_eq_neg_add]
  rw [e3] at h3
  refine ⟨-s, c * a'⁻¹, a', _, _, iso_n hs', iso_n hu, h3, ha, ?_⟩
  rw [Matrix.mul_assoc]
  have e4 : Wm A β * fromBlocks 1 (c * a'⁻¹) 0 1 * Wm A β * fromBlocks a' (b + s * d) 0 (d - c * a'⁻¹ * (b + s * d)) =
      fromBlocks a' (b + s * d) c d := by
    simp [Wm, fromBlocks_multiply, Matrix.mul_assoc, i2]
  rw [e4]
  simp [fromBlocks_multiply, ha']

end Split

section Lift

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E} {σ : A →+* A}
  {ι : Type} [Fintype ι] [DecidableEq ι]

end Lift

end GlobalTheory.CompanionTheory.VacLoc.BigCellLocal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.CharacterAugmentationSubspaceQuotientActionTop
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WittOrbit

section

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E}

theorem int_mul {l m n : Type} [Fintype m] {X : Matrix l m E} {Y : Matrix m n E} (hX : ∀ i j, X i j ∈ A)
    (hY : ∀ i j, Y i j ∈ A) : ∀ i j, (X * Y) i j ∈ A := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem int_map {m n : Type} {X : Matrix m n E} (hs : ∀ z ∈ A, c z ∈ A) (hX : ∀ i j, X i j ∈ A) :
    ∀ i j, (X.map c) i j ∈ A := by
  intro i j
  rw [Matrix.map_apply]
  exact hs _ (hX i j)

theorem map_map_eq {m n : Type} (hc : ∀ z, c (c z) = z) (X : Matrix m n E) : (X.map c).map c = X := by
  ext i j; simp [hc]

theorem map_mul' {l m n : Type} [Fintype m] (X : Matrix l m E) (Y : Matrix m n E) :
    (X * Y).map c = X.map c * Y.map c :=
  Matrix.map_mul

end

end GlobalTheory.CompanionTheory.WittOrbit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.DualNumberGraphFiltrationIsotropicOfSkew
section
open GlobalTheory.CompanionTheory.VacLoc ValuativeRel GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.VacLoc.GoodInh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem goodChar_of_hasConductor (χ : AddChar k Circle) (c : kˣ) (hχ : HasConductor χ c) :
    GoodChar (Circle.coeHom.compAddChar χ) 𝒪[k] c := by
  have hcoe : ∀ z, (Circle.coeHom.compAddChar χ) z = 1 ↔ χ z = 1 := fun z => by
    show ((χ z : Circle) : ℂ) = 1 ↔ _
    exact Circle.coe_eq_one
  refine ⟨fun x => ?_, IsNonarchimedeanLocalField.isCompact_closedBall k 1, Valuation.isOpen_integer,
    fun x => ?_, fun U hU => ?_, fun x => ?_⟩
  · show ‖((χ x : Circle) : ℂ)‖ = 1
    exact Circle.norm_coe _
  · have key : (∀ y ∈ 𝒪[k], (Circle.coeHom.compAddChar χ) (x * y) = 1) ↔
        ∀ y, ValuativeRel.valuation k y ≤ ValuativeRel.valuation k x → χ y = 1 := by
      simp only [hcoe]
      constructor
      · intro H y hy
        by_cases hx : x = 0
        · have h0 : ValuativeRel.valuation k y = 0 := by
            rw [hx, map_zero] at hy
            exact le_antisymm hy zero_le'
          rw [(Valuation.zero_iff _).1 h0, AddChar.map_zero_eq_one]
        · have hmem : x⁻¹ * y ∈ 𝒪[k] := by
            rw [Valuation.mem_integer_iff, map_mul]
            calc ValuativeRel.valuation k x⁻¹ * ValuativeRel.valuation k y
                ≤ ValuativeRel.valuation k x⁻¹ * ValuativeRel.valuation k x :=
                  mul_le_mul_of_nonneg_left hy zero_le'
              _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
          have h1 := H _ hmem
          rwa [mul_inv_cancel_left₀ hx] at h1
      · intro H y hy
        apply H
        rw [map_mul]
        calc ValuativeRel.valuation k x * ValuativeRel.valuation k y
            ≤ ValuativeRel.valuation k x * 1 :=
              mul_le_mul_of_nonneg_left ((Valuation.mem_integer_iff _ _).1 hy) zero_le'
          _ = ValuativeRel.valuation k x := mul_one _
    rw [key, hχ x, Valuation.mem_integer_iff, map_mul]
    constructor
    · intro hle
      calc ValuativeRel.valuation k ((c⁻¹ : kˣ) : k) * ValuativeRel.valuation k x
          ≤ ValuativeRel.valuation k ((c⁻¹ : kˣ) : k) * ValuativeRel.valuation k (c : k) :=
            mul_le_mul_of_nonneg_left hle zero_le'
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    · intro hle
      calc ValuativeRel.valuation k x
          = ValuativeRel.valuation k ((c : k) * (((c⁻¹ : kˣ) : k) * x)) := by
            rw [← mul_assoc, Units.mul_inv, one_mul]
        _ = ValuativeRel.valuation k (c : k) *
            ValuativeRel.valuation k (((c⁻¹ : kˣ) : k) * x) := map_mul _ _ _
        _ ≤ ValuativeRel.valuation k (c : k) * 1 := by
            rw [map_mul]
            exact mul_le_mul_of_nonneg_left hle zero_le'
        _ = ValuativeRel.valuation k (c : k) := mul_one _
  · obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).1 hU
    obtain ⟨δ, hδ0, hδ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := k)
    obtain ⟨ϖ, hϖ⟩ := ValuativeRel.valuation_surjective (K := k) δ
    obtain ⟨z, hz⟩ := ValuativeRel.valuation_surjective (K := k)
      (γ : ValuativeRel.ValueGroupWithZero k)
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hz
      exact γ.ne_zero hz.symm
    have hϖ0 : ϖ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hϖ
      exact hδ0.ne hϖ
    refine ⟨Units.mk0 (z * ϖ) (mul_ne_zero hz0 hϖ0), fun y hy => hγ ?_⟩
    have hy' : ValuativeRel.valuation k y ≤ 1 := (Valuation.mem_integer_iff _ _).1 hy
    show ValuativeRel.valuation k (z * ϖ * y) < γ
    rw [map_mul, map_mul, hz, hϖ]
    calc (γ : ValuativeRel.ValueGroupWithZero k) * δ * ValuativeRel.valuation k y
        ≤ γ * δ * 1 := mul_le_mul_of_nonneg_left hy' zero_le'
      _ = γ * δ := mul_one _
      _ < γ * 1 := mul_lt_mul_of_pos_left hδ1 (zero_lt_iff.2 γ.ne_zero)
      _ = γ := mul_one _
  · by_cases hx : ValuativeRel.valuation k x ≤ 1
    · exact ⟨1, by simp, by simpa [Valuation.mem_integer_iff] using hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      refine ⟨(Units.mk0 x hx0)⁻¹, ?_, ?_⟩
      · rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, Units.val_mk0, Valuation.map_inv]
        exact (inv_le_one₀ ((Valuation.pos_iff _).2 hx0)).2 (le_of_lt (not_le.1 hx))
      · rw [Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hx0]
        exact one_mem _

theorem exists_goodChar :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      (∃ ψ : AddChar k ℂ, GoodChar ψ 𝒪[k] 1) ∧
      ∀ ψ : AddChar k ℂ, Continuous ψ → (∀ x, ‖ψ x‖ = 1) → ψ ≠ 1 → ∃ u : kˣ, GoodChar ψ 𝒪[k] u := by
  intro k _ _ _ _
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  refine ⟨?_, fun ψ hψc hψn hψ1 => ?_⟩
  · obtain ⟨-, ⟨χ, -, -, hχ⟩, -⟩ := GlobalTheory.SplitWeil.conductor_exists k
    exact ⟨_, goodChar_of_hasConductor χ 1 hχ⟩
  · let χ : AddChar k Circle :=
      { toFun := fun x => ⟨ψ x, mem_sphere_zero_iff_norm.2 (hψn x)⟩
        map_zero_eq_one' := Circle.ext (by simp)
        map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul ψ a b) }
    have hχψ : Circle.coeHom.compAddChar χ = ψ := AddChar.ext _ _ fun x => rfl
    have hχc : Continuous χ := hψc.subtype_mk _
    have hχ1 : χ ≠ 1 := by
      intro h1
      apply hψ1
      rw [← hχψ, h1]
      exact AddChar.ext _ _ fun x => by simp
    obtain ⟨c, hc⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
    exact ⟨c, hχψ ▸ goodChar_of_hasConductor χ c hc⟩

end GlobalTheory.CompanionTheory.VacLoc.GoodInh
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsBasisCols
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.MatSat

theorem exists_basis_cols {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {β γ : Type} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (A : Matrix (β ⊕ γ) β O) (hA : Function.Injective A.mulVecLin) :
    ∃ (P : Matrix (β ⊕ γ) (β ⊕ γ) O) (a : β → O) (s u : Matrix β β O),
      IsUnit P.det ∧ (∀ j, a j ≠ 0) ∧ A * s = P.toCols₁ * Matrix.diagonal a ∧
        A = P.toCols₁ * u := by
  classical
  obtain ⟨n, S⟩ := Submodule.smithNormalForm (Pi.basisFun O (β ⊕ γ)) (LinearMap.range A.mulVecLin)
  obtain ⟨φ⟩ : Nonempty (Fin n ≃ β) :=
    ⟨S.bN.indexEquiv ((Pi.basisFun O β).map (LinearEquiv.ofInjective A.mulVecLin hA))⟩
  obtain ⟨f', hf'⟩ : ∃ f' : β ↪ β ⊕ γ, ∀ b, f' b = S.f (φ.symm b) :=
    ⟨φ.symm.toEmbedding.trans S.f, fun _ => rfl⟩
  have hcard : Fintype.card γ = Fintype.card ((Set.range f')ᶜ : Set (β ⊕ γ)) := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective f'.injective, Fintype.card_sum]
    omega
  obtain ⟨e, he⟩ : ∃ e : β ⊕ γ ≃ β ⊕ γ, ∀ b, e (Sum.inl b) = f' b :=
    ⟨(Equiv.sumCongr (Equiv.ofInjective f' f'.injective) (Fintype.equivOfCardEq hcard)).trans
      (Equiv.Set.sumCompl (Set.range f')), fun b => by simp⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (β ⊕ γ) (β ⊕ γ) O,
      P = (Pi.basisFun O (β ⊕ γ)).toMatrix (S.bM.reindex e.symm) := ⟨_, rfl⟩
  have hPdet : IsUnit P.det := by
    letI := (Pi.basisFun O (β ⊕ γ)).invertibleToMatrix (S.bM.reindex e.symm)
    rw [hPdef]
    exact Matrix.isUnit_det_of_invertible _
  have hP1 : ∀ i b, P.toCols₁ i b = S.bM (f' b) i := by
    intro i b
    show P i (Sum.inl b) = _
    rw [hPdef, Module.Basis.toMatrix_apply, Pi.basisFun_repr, Module.Basis.reindex_apply,
      Equiv.symm_symm, he]
  have hpre : ∀ b, ∃ v : β → O, A *ᵥ v = (S.bN (φ.symm b) : β ⊕ γ → O) := by
    intro b
    obtain ⟨v, hv⟩ := LinearMap.mem_range.1 (S.bN (φ.symm b)).2
    exact ⟨v, hv⟩
  choose pre hpre using hpre
  obtain ⟨s, hs⟩ : ∃ s : Matrix β β O, ∀ i b, s i b = pre b i :=
    ⟨Matrix.of fun i b => pre b i, fun _ _ => rfl⟩
  have ha : ∀ b, S.a (φ.symm b) ≠ 0 := by
    intro b h
    have h1 := S.snf (φ.symm b)
    rw [h, zero_smul] at h1
    exact S.bN.ne_zero _ ((Submodule.coe_eq_zero).1 h1)
  obtain ⟨u, hu⟩ : ∃ u : Matrix β β O, ∀ b' b, u b' b =
      S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩ (φ.symm b') *
        S.a (φ.symm b') :=
    ⟨Matrix.of fun b' b => S.bN.repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
      (φ.symm b') * S.a (φ.symm b'), fun _ _ => rfl⟩
  refine ⟨P, fun b => S.a (φ.symm b), s, u, hPdet, ha, ?_, ?_⟩
  · ext i b
    rw [Matrix.mul_diagonal, hP1, Matrix.mul_apply]
    have h1 := congrFun (hpre b) i
    simp only [Matrix.mulVec, dotProduct] at h1
    simp only [hs]
    rw [h1, S.snf, hf']
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · ext i b
    have hw := S.bN.sum_repr ⟨A.mulVecLin (Pi.single b 1), LinearMap.mem_range_self _ _⟩
    have hw' := congrArg (fun v : LinearMap.range A.mulVecLin => (v : β ⊕ γ → O) i) hw
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, S.snf] at hw'
    have hcol : (A.mulVecLin (Pi.single b 1)) i = A i b := by
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [Matrix.mul_apply]
    refine hcol.symm.trans (hw'.symm.trans ?_)
    simp only [hP1, hu, hf']
    refine Fintype.sum_equiv φ _ _ fun k => ?_
    simp only [Equiv.symm_apply_apply]
    ring

theorem exists_saturation {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] {β γ : Type} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (C : Matrix (β ⊕ γ) β K)
    (hC : ∃ L : Matrix β (β ⊕ γ) K, L * C = 1) :
    ∃ (t : GL β K) (C₀ : Matrix (β ⊕ γ) β O) (D : Matrix (β ⊕ γ) γ O),
      C * (t : Matrix β β K) = C₀.map (algebraMap O K) ∧
        IsUnit (Matrix.fromCols C₀ D).det := by
  classical
  obtain ⟨L, hL⟩ := hC
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : (β ⊕ γ) × β => C p.1 p.2)
  have hb' : ∀ p : (β ⊕ γ) × β, ∃ x : O,
      algebraMap O K x = algebraMap O K (b : O) * C p.1 p.2 := by
    intro p
    obtain ⟨x, hx⟩ := RingHom.mem_rangeS.1 (hb p)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose c hc using hb'
  have hbne : algebraMap O K (b : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Matrix (β ⊕ γ) β O,
      C₁.map (algebraMap O K) = algebraMap O K (b : O) • C :=
    ⟨Matrix.of fun i j => c (i, j), by ext i j; simp [hc]⟩
  have hinj : Function.Injective C₁.mulVecLin := by
    intro v w hvw
    have h1 : C₁ *ᵥ v = C₁ *ᵥ w := hvw
    have h2 : ∀ x : β → O, (algebraMap O K) ∘ (C₁ *ᵥ x) =
        algebraMap O K (b : O) • (C *ᵥ ((algebraMap O K) ∘ x)) := by
      intro x
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hC₁]
      first
      | rw [Matrix.smul_mulVec]
      | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    have e1 := h2 v
    have e2 := h2 w
    rw [h1] at e1
    have h3 : C *ᵥ ((algebraMap O K) ∘ v) = C *ᵥ ((algebraMap O K) ∘ w) :=
      smul_right_injective (β ⊕ γ → K) hbne (e1.symm.trans e2)
    have h4 : (algebraMap O K) ∘ v = (algebraMap O K) ∘ w := by
      have := congrArg (fun z => L *ᵥ z) h3
      simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using this
    funext i
    exact IsFractionRing.injective O K (congrFun h4 i)
  obtain ⟨P, a, s, u, hP, -, -, hu⟩ := exists_basis_cols C₁ hinj
  have hCw : C = (P.toCols₁.map (algebraMap O K)) *
      ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) := by
    have e1 : algebraMap O K (b : O) • C = (P.toCols₁.map (algebraMap O K)) * (u.map (algebraMap O K)) := by
      rw [← hC₁, hu, Matrix.map_mul]
    rw [Matrix.mul_smul, ← e1, smul_smul, inv_mul_cancel₀ hbne, one_smul]
  have hLw : (L * P.toCols₁.map (algebraMap O K)) *
      ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) = 1 := by
    rw [Matrix.mul_assoc, ← hCw, hL]
  have hwL : ((algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K)) *
      (L * P.toCols₁.map (algebraMap O K)) = 1 := by
    first
    | exact mul_eq_one_comm.1 hLw
    | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) |>.1 hLw
  refine ⟨⟨L * P.toCols₁.map (algebraMap O K),
    (algebraMap O K (b : O))⁻¹ • u.map (algebraMap O K), hLw, hwL⟩, P.toCols₁, P.toCols₂, ?_, ?_⟩
  · show C * (L * P.toCols₁.map (algebraMap O K)) = P.toCols₁.map (algebraMap O K)
    rw [hCw, Matrix.mul_assoc, hwL, Matrix.mul_one]
  · rw [Matrix.fromCols_toCols]
    exact hP

end GlobalTheory.CompanionTheory.MatSat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.IsLatticeOfCompactOpen
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitIdx

section Lattice

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end Lattice

def invT {k : Type} [CommRing k] {β : Type} [Fintype β] [DecidableEq β] (u : GL β k) : GL β k :=
  ⟨((u⁻¹ : GL β k) : Matrix β β k)ᵀ, (u : Matrix β β k)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

def swapAlg (k : Type) [CommRing k] : (k × k) ≃ₐ[k] k × k :=
  { (RingEquiv.prodComm : k × k ≃+* k × k) with commutes' := fun _ => rfl }

section Split

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {E : Type} [CommRing E] [Algebra k E] [TopologicalSpace E] [IsModuleTopology k E]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end Split

end GlobalTheory.CompanionTheory.SplitIdx
end
end

