import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveBijectiveRelationRowVecEqMatrix
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.RelLin

theorem main : ∀ (N : ℕ) [NeZero N] (R : (Fin 2 → ZMod N) → (Fin 2 → ZMod N) → Prop),
    (∀ x, ∃ y, R x y) → (∀ x y x' y', R x y → R x' y' → R (x - x') (y - y')) →
    (∀ x y, R x y → (x = 0 ↔ y = 0)) → ∃ A : GL (Fin 2) (ZMod N), ∀ x, R x (vmul x A) := by
  intro N _ R h1 h2 h3
  choose f hf using h1
  have huniq : ∀ x y y', R x y → R x y' → y = y' := by
    intro x y y' hy hy'
    have h := h3 _ _ (h2 x y x y' hy hy')
    exact sub_eq_zero.mp (h.mp (sub_self x))
  have hsub : ∀ x x', f (x - x') = f x - f x' :=
    fun x x' => huniq _ _ _ (hf (x - x')) (h2 _ _ _ _ (hf x) (hf x'))
  let g : (Fin 2 → ZMod N) →+ (Fin 2 → ZMod N) := AddMonoidHom.ofMapSub f hsub
  let L : (Fin 2 → ZMod N) →ₗ[ZMod N] (Fin 2 → ZMod N) := g.toZModLinearMap N
  have hL : ∀ x, L x = f x := fun x => rfl
  have hinj : Function.Injective f := by
    intro x x' hxx
    have : f (x - x') = 0 := by rw [hsub, hxx, sub_self]
    exact sub_eq_zero.mp ((h3 _ _ (hf (x - x'))).mpr this)
  let M : Matrix (Fin 2) (Fin 2) (ZMod N) := LinearMap.toMatrixRight' L
  have hM : ∀ x, x ᵥ* M = f x := by
    intro x
    rw [← hL, ← Matrix.toLinearMapRight'_apply]
    simp [M]
  have hU : IsUnit M := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, hM x⟩
  refine ⟨hU.unit, fun x => ?_⟩
  have : vmul x hU.unit = f x := by
    simp [vmul, hM]
  rw [this]
  exact hf x

end GlobalTheory.RelLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixFamilyDegreeLeRankMulLineBound
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem deg_le_rank_mul_of_linesLE : ∀ (r : ℕ) (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F → ∀ g : Place k F → Matrix (Fin r) (Fin r) F, admitted g → ∀ b : ℝ, LinesLE g b → (deg g : ℝ) ≤ r * b := by
  intro r
  induction r with
  | zero =>
    intro k F _ _ _ _ _ _ g _ b _
    have : deg g = 0 := by simp [deg, ord, Matrix.det_isEmpty]
    simp [this]
  | succ r ih =>
    intro k F _ _ _ _ _ hF g hg b hb

    set S : Set ℝ := {c | LinesLE g c} with hS
    have hbS : b ∈ S := hb

    have hbdd : BddBelow S := by
      refine ⟨(degLine (pullAd (id : Place k F → Place k F) g) (Pi.single 0 1) : ℝ), ?_⟩
      intro c hc
      have hres : IsRes (k := k) (F := F) (E := F) (id : Place k F → Place k F) := by
        intro p x; rfl
      have h1 := hc F id hres (Pi.single 0 1) (by
        intro h; have := congrFun h 0; simp at this)
      simpa [Module.finrank_self] using h1
    set a := sInf S with ha
    have hab : a ≤ b := csInf_le hbdd hbS
    have haS : LinesLE g a := by
      intro E _ _ _ _ _ ρ hρ w hw
      have hn : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
      have : (degLine (pullAd ρ g) w : ℝ) / Module.finrank F E ≤ a := by
        refine le_csInf ⟨b, hbS⟩ ?_
        intro c hc
        rw [div_le_iff₀ hn]
        exact hc E ρ hρ w hw
      rwa [div_le_iff₀ hn] at this
    have key : ∀ ε : ℝ, 0 < ε → (deg g : ℝ) ≤ (r + 1) * a + r * ε := by
      intro ε hε
      have hnot : ¬ LinesLE g (a - ε) := fun h => by
        have := csInf_le hbdd (show a - ε ∈ S from h); linarith
      simp only [LinesLE, not_forall, not_le] at hnot
      obtain ⟨E, _, _, _, _, _, ρ, hρ, x, hx, hlt⟩ := hnot
      have hn : (0 : ℝ) < Module.finrank F E := by exact_mod_cast Module.finrank_pos
      obtain ⟨hGadm, hGdeg, -, hGlines⟩ := GlobalTheory.T.isAdmissibleAdelicMatrixFamily_pullback_extension k F E hF ρ hρ (r + 1) g hg
      have hE : IsFF k E := (GlobalTheory.T.functionFieldOneVariable_transcendental_finite_and_ext k F hF).2 E
      have hLG : LinesLE (pullAd ρ g) (a * Module.finrank F E) := hGlines a haS
      have hδle : (degLine (pullAd ρ g) x : ℝ) ≤ a * Module.finrank F E := haS E ρ hρ x hx
      obtain ⟨h, u, -, -, hzero, hadm', hadmq, hdeg, hsum, hlines⟩ :=
        GlobalTheory.T.iwasawa_decomposition_admissible_family k E hE r (pullAd ρ g) hGadm x hx
      have hLq := GlobalTheory.T.quotient_line_degree_le_of_triangular_family k E hE r (fun v => u v * pullAd ρ g v * h) hadm' hzero hadmq
        (a * Module.finrank F E) (hlines _ hLG)
      rw [hsum] at hLq
      have hq := ih k E hE _ hadmq _ hLq
      have hdegZ : (Module.finrank F E : ℤ) * deg g =
          degLine (pullAd ρ g) x + deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) := by
        rw [← hGdeg, hdeg]
      have hdegR : (Module.finrank F E : ℝ) * (deg g : ℝ) =
          (degLine (pullAd ρ g) x : ℝ) + (deg (fun v => (u v * pullAd ρ g v * h).submatrix Fin.succ Fin.succ) : ℝ) := by
        exact_mod_cast hdegZ
      set n : ℝ := (Module.finrank F E : ℝ)
      set δ : ℝ := (degLine (pullAd ρ g) x : ℝ)
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have h2 : (r : ℝ) * (a * n - δ) ≤ r * (ε * n) := by
        apply mul_le_mul_of_nonneg_left _ hr; nlinarith
      have h3 : n * (deg g : ℝ) ≤ n * ((r + 1) * a + r * ε) := by nlinarith
      exact le_of_mul_le_mul_left h3 hn
    have hfin : (deg g : ℝ) ≤ (r + 1) * a := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := key (ε / (r + 1)) (by positivity)
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      have : (r : ℝ) * (ε / (r + 1)) ≤ ε := by
        rw [mul_div_assoc']; rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) r]

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAll
section
noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

theorem locOrder_eq_of_le {B : Type} [Ring B] [Algebra ℚ B] (OB Λ : Subring B) (hle : OB ≤ Λ)
    (N : ℕ) (hN : 0 < N) (hNΛ : ∀ x ∈ Λ, (N : B) * x ∈ OB) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    locOrder ℓ OB = locOrder ℓ Λ := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.image_mono hle)
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.one_tmul_mem_locOrder_of_nsmul_mem OB x N hN (hNΛ x hx) ℓ hℓ

theorem locOrder_matrix : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  intro F B _ _ _ _ _ _ _ _ _ n hn OB hfin hspan
  obtain ⟨Λ, hle, hΛ, hΛfin, N₁, hN₁, hN₁Λ⟩ := GlobalTheory.T.exists_order_containing_integers F B OB hfin hspan
  have hspanΛ : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ := fun b => by
    obtain ⟨m, hm, hmb⟩ := hspan b; exact ⟨m, hm, hle hmb⟩
  obtain ⟨N₂, hN₂, hfree⟩ := GlobalTheory.T.localOrderTensorPadic_free_almost_all F B Λ hΛ hΛfin hspanΛ
  obtain ⟨N₃, hN₃, hazu⟩ := GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all F B Λ hΛ hΛfin hspanΛ
  refine ⟨N₁ * N₂ * N₃, by positivity, fun ℓ _ hℓ => ?_⟩
  have h₁ : ¬ ℓ ∣ N₁ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)
  have h₂ : ¬ ℓ ∣ N₂ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have h₃ : ¬ ℓ ∣ N₃ := fun h => hℓ (Dvd.dvd.mul_left h _)
  have heq := locOrder_eq_of_le OB Λ hle N₁ hN₁ hN₁Λ ℓ h₁
  letI := cenAlgebra ℓ F B Λ hΛ
  haveI := isScalarTower_cenAlgebra ℓ F B Λ hΛ
  haveI : Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := GlobalTheory.cenOrder_finite F ℓ
  obtain ⟨hF, hrank⟩ := hfree ℓ h₂
  haveI := hF
  haveI := hazu ℓ h₃
  obtain ⟨φ⟩ := GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local ℓ (cenOrder ℓ F) (locOrder ℓ Λ) n (hrank.trans hn)
  refine ⟨(Subalgebra.equivOfEq _ _ heq).trans (φ.restrictScalars ℤ_[ℓ]), fun a => ?_⟩
  refine ⟨heq ▸ cenMap_mem ℓ F B Λ hΛ a.2, ?_⟩
  have h2 : (Subalgebra.equivOfEq _ _ heq) ⟨cenMap ℓ F B a, heq ▸ cenMap_mem ℓ F B Λ hΛ a.2⟩ =
      algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a := Subtype.ext rfl
  rw [AlgEquiv.trans_apply, h2, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

end GlobalTheory.LocMatrix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOpsStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicValuationAtLeastAtEmbedding_ring_ops : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ r : ℝ, Sz l lam r 0) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y) ∧ Sz l lam r (x - y)) ∧ (∀ (r s : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam s y → Sz l lam (r + s) (x * y)) ∧ (∀ (r s : ℝ) (x : ℂ), r ≤ s → Sz l lam r x → Sz l lam s x) ∧ (∀ n : ℤ, Sz l lam 0 (n : ℂ)) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (x : κ → ℂ), (∀ k ∈ t, Sz l lam r (x k)) → Sz l lam r (∑ k ∈ t, x k)) := by
  first | exact @GlobalTheory.QFam.SzSum.sz_ring | exact GlobalTheory.QFam.SzSum.sz_ring | (intros; apply GlobalTheory.QFam.SzSum.sz_ring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicPropertiesStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicValuationAtLeast_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ (n : ℕ) (x : ℂ), ¬ l ∣ n → IsIntegral ℤ ((n : ℂ) * x) → Sz l lam 0 x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y)) ∧ (∀ (r r' : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r' y → Sz l lam (r + r') (x * y)) ∧ (∀ (r r' : ℝ) (x : ℂ), r ≤ r' → Sz l lam r x → Sz l lam r' x) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r x → Sz l lam r (-x)) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r (x ^ 2) → y = x → Sz l lam (r / 2) y) := by
  first | exact @GlobalTheory.SzRules.main | exact GlobalTheory.SzRules.main | (intros; apply GlobalTheory.SzRules.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastOfForallRatGtStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicValuationAtLeast_of_forall_rat_gt : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (r : ℝ) (x : ℂ), (∀ q : ℚ, r < q → Sz l lam q x) → Sz l lam r x := by
  first | exact @GlobalTheory.QFam.sz_of_forall_rat_gt | exact GlobalTheory.QFam.sz_of_forall_rat_gt | (intros; apply GlobalTheory.QFam.sz_of_forall_rat_gt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationBoundAtRamifiedPrime
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.SzRamified

theorem norm_int_eq_one {l : ℕ} [Fact l.Prime] {z : ℤ} (h : ¬ (l : ℤ) ∣ z) : ‖(z : ℂ_[l])‖ = 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] ℂ_[l]) z, norm_algebraMap']
  exact le_antisymm (Padic.norm_int_le_one z) (not_lt.mp fun h' => h (Padic.norm_intCast_lt_one_iff.mp h'))

theorem norm_bound {l : ℕ} [Fact l.Prime] (W S P : ℂ_[l]) (hl : 4 < l) (hW : W ^ 2 = -(l : ℂ_[l]))
    (hP : ‖12 * P‖ ≤ 1) (hS : ‖((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P‖ ≤ 1) :
    ‖S‖ ≤ (l : ℝ) ^ (1 / 2 : ℝ) := by
  have hpr : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hpr.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hn : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]
  have h12 : ‖(12 : ℂ_[l])‖ = 1 := by
    have hd : ¬ (l : ℤ) ∣ 12 := by
      intro h
      have h' : l ∣ 12 := by exact_mod_cast h
      have h4 : l ∣ 2 ^ 2 * 3 := h'
      rcases (Nat.Prime.dvd_mul hpr).1 h4 with h5 | h5
      · have := Nat.le_of_dvd (by norm_num) (hpr.dvd_of_dvd_pow h5); omega
      · have := Nat.le_of_dvd (by norm_num) h5; omega
    simpa using norm_int_eq_one (l := l) hd
  have h2 : ‖(2 : ℂ_[l])‖ = 1 := by
    have hd : ¬ (l : ℤ) ∣ 2 := by
      intro h
      have := Int.le_of_dvd (by norm_num) h
      omega
    simpa using norm_int_eq_one (l := l) hd
  have hW2 : ‖W‖ ^ 2 = (l : ℝ)⁻¹ := by rw [← norm_pow, hW, norm_neg, hn]
  have hW1 : ‖W‖ < 1 := by
    have : ‖W‖ ^ 2 < 1 := by rw [hW2]; exact inv_lt_one_of_one_lt₀ hl1
    nlinarith [norm_nonneg W]
  have h1W : ‖1 + W‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hW1.ne'), norm_one,
      max_eq_left hW1.le]
  have hP1 : ‖P‖ ≤ 1 := by rwa [norm_mul, h12, one_mul] at hP
  have hB : ‖((1 + W) ^ 2 - 1) * P‖ ≤ 1 := by
    have e : ((1 + W) ^ 2 - 1) * P = W * (2 + W) * P := by ring
    have h2W : ‖2 + W‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2.le hW1.le)
    rw [e, norm_mul, norm_mul]
    exact mul_le_one₀ (mul_le_one₀ hW1.le (norm_nonneg _) h2W) (norm_nonneg _) hP1
  have hA : ‖W‖ * ‖S‖ ≤ 1 := by
    have e : 2 * W * (1 + W) * S =
        (((1 + W) ^ 2 - (1 + (l : ℂ_[l]))) * S - ((1 + W) ^ 2 - 1) * P) + ((1 + W) ^ 2 - 1) * P := by
      linear_combination S * hW
    have := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hS hB)
    rwa [← e, norm_mul, norm_mul, norm_mul, h2, h1W, one_mul, mul_one] at this
  have hsq : ‖S‖ ^ 2 ≤ l := by
    have h3 : (‖W‖ * ‖S‖) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hA
    rw [mul_pow, hW2, inv_mul_le_iff₀ hl0, mul_one] at h3
    exact h3
  rw [← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le hsq

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (w σ p : ℂ), 4 < l → w ^ 2 = -(l : ℂ) → Sz l lam 0 (12 * p) → Sz l lam 0 (((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) → Sz l lam (1 / 2) σ := by
  intro l _ lam w σ p hl hw hp hs
  obtain ⟨hp, hp'⟩ := hp
  obtain ⟨hs, hs'⟩ := hs
  rw [Real.rpow_zero] at hp' hs'
  have hlK : (l : ℂ) ∈ algebraicClosure ℚ ℂ := natCast_mem _ l
  have hwK : w ∈ algebraicClosure ℚ ℂ := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [← mem_algebraicClosure_iff, hw]
    exact neg_mem hlK
  have hpK : p ∈ algebraicClosure ℚ ℂ := by
    have e : p = (12 * p) / ((12 : ℕ) : ℂ) := by push_cast; ring
    rw [e]
    exact div_mem hp (natCast_mem _ 12)
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hw0 : w ≠ 0 := by
    rintro rfl
    have : (l : ℂ) = 0 := by linear_combination hw
    have h' : l = 0 := by exact_mod_cast this
    omega
  have hw1 : 1 + w ≠ 0 := by
    intro h
    have : ((l + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination hw + (1 - w) * h
    exact Nat.succ_ne_zero l (by exact_mod_cast this)
  have hσK : σ ∈ algebraicClosure ℚ ℂ := by
    have e : σ = ((((1 + w) ^ 2 - (1 + (l : ℂ))) * σ - ((1 + w) ^ 2 - 1) * p) + ((1 + w) ^ 2 - 1) * p) /
        (((2 : ℕ) : ℂ) * w * (1 + w)) := by
      rw [eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) hw0) hw1)]
      push_cast
      linear_combination σ * hw
    have h1 : 1 + w ∈ algebraicClosure ℚ ℂ := add_mem (one_mem _) hwK
    rw [e]
    exact div_mem (add_mem hs (mul_mem (sub_mem (pow_mem h1 2) (one_mem _)) hpK))
      (mul_mem (mul_mem (natCast_mem _ 2) hwK) h1)
  refine ⟨hσK, norm_bound (lam ⟨w, hwK⟩) _ (lam ⟨p, hpK⟩) hl ?_ ?_ ?_⟩
  · have e : (⟨w, hwK⟩ : algebraicClosure ℚ ℂ) ^ 2 = -(l : algebraicClosure ℚ ℂ) := Subtype.ext (by simpa using hw)
    rw [← map_pow, e, map_neg, map_natCast]
  · have e : (⟨12 * p, hp⟩ : algebraicClosure ℚ ℂ) = ((12 : ℕ) : algebraicClosure ℚ ℂ) * ⟨p, hpK⟩ :=
      Subtype.ext (by
        show 12 * p = ((12 : ℕ) : ℂ) * p
        norm_num)
    rw [e, map_mul, map_natCast] at hp'
    exact_mod_cast hp'
  · have e : (⟨_, hs⟩ : algebraicClosure ℚ ℂ) =
        ((1 + ⟨w, hwK⟩) ^ 2 - (1 + (l : algebraicClosure ℚ ℂ))) * ⟨σ, hσK⟩ - ((1 + ⟨w, hwK⟩) ^ 2 - 1) * ⟨p, hpK⟩ :=
      Subtype.ext (by simp)
    rw [e] at hs'
    simpa only [map_sub, map_mul, map_pow, map_add, map_one, map_natCast] using hs'

end GlobalTheory.SzRamified
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqOfFactorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.app_opensRange_eq_appLE_comp_of_factor : ∀ {X Y : Scheme.{0}} {A : CommRingCat.{0}} (κ : Spec A ⟶ Y) [IsOpenImmersion κ] (j : X ⟶ Y) (O : X.Opens) (q : A ⟶ Γ(X, O)) (hO : j ⁻¹ᵁ κ.opensRange = O), O.ι ≫ j = (O.toSpecΓ ≫ Spec.map q) ≫ κ → j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op = κ.appLE κ.opensRange ⊤ (fun x _ ↦ ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso A).hom ≫ q := by
  first | exact @GlobalTheory.SectionsPinch.app_eq_of_factor | exact GlobalTheory.SectionsPinch.app_eq_of_factor | (intros; apply GlobalTheory.SectionsPinch.app_eq_of_factor; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeIsoSpreadsToSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.IsoSpread

theorem spMap_inclusion_comp {S : Type} [CommRing S] {A B C : Subring S} (h₁ : A ≤ B)
    (h₂ : B ≤ C) :
    spMap (Subring.inclusion h₂) ≫ spMap (Subring.inclusion h₁) =
      spMap (Subring.inclusion (h₁.trans h₂)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem spMap_subtype_comp {S : Type} [CommRing S] {A B : Subring S} (h : A ≤ B) :
    spMap B.subtype ≫ spMap (Subring.inclusion h) = spMap A.subtype := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_isPullback_lift {X₀ X₁ T₀ T₁ T₂ : Scheme.{0}} {f₀ : X₀ ⟶ T₀} {f₁ : X₁ ⟶ T₁}
    {π₁ : X₁ ⟶ X₀} {u : T₁ ⟶ T₂} {v : T₂ ⟶ T₀} {w : T₁ ⟶ T₀} (huv : u ≫ v = w)
    (hp : IsPullback π₁ f₁ f₀ w) :
    ∃ m : X₁ ⟶ pullback f₀ v, m ≫ pullback.fst _ _ = π₁ ∧ m ≫ pullback.snd _ _ = f₁ ≫ u ∧
      IsPullback m f₁ (pullback.snd f₀ v) u := by
  subst huv
  refine ⟨pullback.lift π₁ (f₁ ≫ u) (by rw [Category.assoc, hp.w]), pullback.lift_fst _ _ _,
    pullback.lift_snd _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst]
  exact hp

end GlobalTheory.IsoSpread

namespace GlobalTheory

open GlobalTheory.IsoSpread in

theorem iso_spreads_to_subring :
    ∀ (S : Type) [CommRing S] (R₀ : Subring S) (X X₀ Z : Scheme.{0}) (f : X ⟶ Sp S) (f₀ : X₀ ⟶ Sp R₀) (q : Z ⟶ Sp R₀) (π : X ⟶ X₀) [QuasiCompact f₀] [QuasiSeparated f₀] [LocallyOfFinitePresentation f₀] [QuasiCompact q] [QuasiSeparated q] [LocallyOfFinitePresentation q] (φ : X ⟶ Z), IsPullback π f f₀ (spMap R₀.subtype) → IsPullback φ f q (spMap R₀.subtype) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (X₁ : Scheme.{0}) (f₁ : X₁ ⟶ Sp R₁) (π₁ : X₁ ⟶ X₀) (j : X ⟶ X₁), IsPullback π₁ f₁ f₀ (spMap (Subring.inclusion hle)) → j ≫ π₁ = π → j ≫ f₁ = f ≫ spMap R₁.subtype → ∃ ψ : X₁ ⟶ Z, j ≫ ψ = φ ∧ IsPullback ψ f₁ q (spMap (Subring.inclusion hle)) := by
  classical
  intro S _ R₀ X X₀ Z f f₀ q π _ _ _ _ _ _ φ hπ hφ

  obtain ⟨Fa, ha⟩ := morphism_descends_to_subring S R₀ X X₀ Z f f₀ q π φ hπ
    (hφ.w.trans hπ.w.symm)
  obtain ⟨Fb, hb⟩ := morphism_descends_to_subring S R₀ X Z X₀ f q f₀ φ π hφ
    (hπ.w.trans hφ.w.symm)

  let R₂ : Subring S := Subring.closure ((R₀ : Set S) ∪ (Fa : Set S) ∪ (Fb : Set S))
  have h₀₂ : R₀ ≤ R₂ := fun x hx ↦ Subring.subset_closure (Or.inl (Or.inl hx))
  have hFa : (Fa : Set S) ⊆ R₂ := fun x hx ↦ Subring.subset_closure (Or.inl (Or.inr hx))
  have hFb : (Fb : Set S) ⊆ R₂ := fun x hx ↦ Subring.subset_closure (Or.inr hx)
  obtain ⟨j₂, hj₂f, hj₂s, hj₂⟩ := exists_isPullback_lift (spMap_subtype_comp h₀₂) hπ
  obtain ⟨k₂, hk₂f, hk₂s, hk₂⟩ := exists_isPullback_lift (spMap_subtype_comp h₀₂) hφ
  obtain ⟨ψ₂, hψ₂, hψ₂q⟩ := ha R₂ h₀₂ hFa _ _ _ j₂ (IsPullback.of_hasPullback _ _) hj₂f hj₂s
  obtain ⟨χ₂, hχ₂, hχ₂q⟩ := hb R₂ h₀₂ hFb _ _ _ k₂ (IsPullback.of_hasPullback _ _) hk₂f hk₂s
  let α₂ := pullback.lift ψ₂ (pullback.snd f₀ (spMap (Subring.inclusion h₀₂)))
    (by rw [hψ₂q, pullback.condition])
  let β₂ := pullback.lift χ₂ (pullback.snd q (spMap (Subring.inclusion h₀₂)))
    (by rw [hχ₂q, pullback.condition])
  have hα₂f : α₂ ≫ pullback.fst _ _ = ψ₂ := pullback.lift_fst _ _ _
  have hα₂s : α₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hβ₂f : β₂ ≫ pullback.fst _ _ = χ₂ := pullback.lift_fst _ _ _
  have hβ₂s : β₂ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have hjα : j₂ ≫ α₂ = k₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hα₂f, hψ₂, hk₂f]
    · rw [Category.assoc, hα₂s, hj₂s, hk₂s]
  have hkβ : k₂ ≫ β₂ = j₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hβ₂f, hχ₂, hj₂f]
    · rw [Category.assoc, hβ₂s, hj₂s, hk₂s]

  obtain ⟨Fc, hc⟩ := morphisms_eq_spread_to_subring S R₂ X _ _ f _ _ j₂ (α₂ ≫ β₂) (𝟙 _) hj₂
    (by rw [Category.assoc, hβ₂s, hα₂s]) (Category.id_comp _)
    (by rw [reassoc_of% hjα, hkβ, Category.comp_id])
  obtain ⟨Fd, hd⟩ := morphisms_eq_spread_to_subring S R₂ X _ _ f _ _ k₂ (β₂ ≫ α₂) (𝟙 _) hk₂
    (by rw [Category.assoc, hα₂s, hβ₂s]) (Category.id_comp _)
    (by rw [reassoc_of% hkβ, hjα, Category.comp_id])
  refine ⟨Fa ∪ Fb ∪ Fc ∪ Fd, fun R₁ hle hF X₁ f₁ π₁ j hp₁ hj₁ hjf ↦ ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨⟨⟨hFa₁, hFb₁⟩, hFc₁⟩, hFd₁⟩ := hF
  have h₂₁ : R₂ ≤ R₁ := Subring.closure_le.mpr
    (Set.union_subset (Set.union_subset (fun x hx ↦ hle hx) hFa₁) hFb₁)
  obtain ⟨m, hmf, hms, hm⟩ := exists_isPullback_lift (w := spMap (Subring.inclusion hle))
    (spMap_inclusion_comp h₀₂ h₂₁) hp₁
  obtain ⟨n, hnf, hns, hn⟩ := exists_isPullback_lift (w := spMap (Subring.inclusion hle))
    (spMap_inclusion_comp h₀₂ h₂₁) (IsPullback.of_hasPullback q (spMap (Subring.inclusion hle)))
  have hmc : m ≫ α₂ ≫ β₂ = m := (hc R₁ h₂₁ hFc₁ X₁ f₁ m hm).trans (Category.comp_id _)
  have hnd : n ≫ β₂ ≫ α₂ = n := (hd R₁ h₂₁ hFd₁ _ _ n hn).trans (Category.comp_id _)
  have hjm : j ≫ m = j₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, hj₁, hj₂f]
    · rw [Category.assoc, hms, reassoc_of% hjf, spMap_subtype_comp, hj₂s]
  have hw : (m ≫ ψ₂) ≫ q = f₁ ≫ spMap (Subring.inclusion hle) := by
    rw [Category.assoc, hψ₂q, reassoc_of% hmf, hp₁.w]
  let α : X₁ ⟶ pullback q (spMap (Subring.inclusion hle)) := pullback.lift (m ≫ ψ₂) f₁ hw
  let β : pullback q (spMap (Subring.inclusion hle)) ⟶ X₁ :=
    hp₁.lift (n ≫ χ₂) (pullback.snd _ _) (by rw [Category.assoc, hχ₂q, reassoc_of% hnf,
      pullback.condition])
  have hαf : α ≫ pullback.fst _ _ = m ≫ ψ₂ := pullback.lift_fst _ _ _
  have hαs : α ≫ pullback.snd _ _ = f₁ := pullback.lift_snd _ _ _
  have hβf : β ≫ π₁ = n ≫ χ₂ := hp₁.lift_fst _ _ _
  have hβs : β ≫ f₁ = pullback.snd _ _ := hp₁.lift_snd _ _ _
  have hαn : α ≫ n = m ≫ α₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hnf, hαf, Category.assoc, hα₂f]
    · rw [Category.assoc, hns, reassoc_of% hαs, Category.assoc, hα₂s, hms]
  have hβm : β ≫ m = n ≫ β₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hmf, hβf, Category.assoc, hβ₂f]
    · rw [Category.assoc, hms, reassoc_of% hβs, Category.assoc, hβ₂s, hns]
  have h₁ : α ≫ β = 𝟙 X₁ := by
    apply hp₁.hom_ext
    · rw [Category.assoc, hβf, reassoc_of% hαn, Category.id_comp, ← hβ₂f, ← Category.assoc m,
        ← Category.assoc, Category.assoc m, hmc, hmf]
    · rw [Category.assoc, hβs, hαs, Category.id_comp]
  have h₂ : β ≫ α = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hαf, reassoc_of% hβm, Category.id_comp, ← hα₂f, ← Category.assoc n,
        ← Category.assoc, Category.assoc n, hnd, hnf]
    · rw [Category.assoc, hαs, hβs, Category.id_comp]
  exact ⟨m ≫ ψ₂, by rw [reassoc_of% hjm, hψ₂],
    IsPullback.of_iso_pullback ⟨hw⟩ ⟨α, β, h₁, h₂⟩ hαf hαs⟩

end GlobalTheory
end

