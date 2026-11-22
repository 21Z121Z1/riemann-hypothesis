import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0542
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0547
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0515
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusTangentMemSpecialUnitaryLieDiagonal
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem torusDer_sum_angles (φ : Fin (r - 1) → ℝ) : ∑ a : Fin r, angles φ a = 0 := by
  cases r with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, angles φ i.castSucc = φ ⟨i, by simp⟩ := by
      intro i; unfold angles; rw [dif_pos (by simp)]; rfl
    have h2 : angles φ (Fin.last n) = -∑ k, φ k := by
      unfold angles; rw [dif_neg (by simp)]
    rw [h2, Finset.sum_congr rfl fun i _ => h1 i]
    rw [add_neg_eq_zero]
    exact Fintype.sum_equiv (finCongr (by simp)) _ _ (fun i => rfl)

theorem torusDer_hermC_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (w b)) := by
  simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem torusDer_conj_mulVec (Y : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    (fun b => conj ((Y *ᵥ w) b)) = Y.map (starRingEnd ℂ) *ᵥ fun b => conj (w b) := by
  ext b; simp [mulVec, dotProduct, map_sum]

theorem torusDer_skew_of_mat (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ)
    (hK : Yᵀ * G.map τ + G.map τ * Y.map (starRingEnd ℂ) = 0) (u w : Fin r → ℂ) :
    hermC τ G (Y *ᵥ u) w + hermC τ G u (Y *ᵥ w) = 0 := by
  rw [torusDer_hermC_dot, torusDer_hermC_dot, torusDer_conj_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, ← dotProduct_add, ← add_mulVec, hK, zero_mulVec, dotProduct_zero]

end GlobalTheory.TorusFrame

namespace GlobalTheory.TorusFrame

open Complex
open scoped ComplexConjugate

theorem skewHermitian_of_diagonal_imaginary_frame {r : ℕ} (G M Y : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit M.det) (d s : Fin r → ℂ)
    (hd : ∀ a, conj (d a) = -d a) (hJ : Mᵀ * G * M.map (starRingEnd ℂ) = diagonal s)
    (hYM : Y * M = M * diagonal d) :
    Yᵀ * G + G * Y.map (starRingEnd ℂ) = 0 := by
  have e1 : Mᵀ * (Yᵀ * G) * M.map (starRingEnd ℂ) = diagonal d * diagonal s := by
    calc Mᵀ * (Yᵀ * G) * M.map (starRingEnd ℂ) = (Y * M)ᵀ * G * M.map (starRingEnd ℂ) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal d * diagonal s := by
          rw [hYM, transpose_mul, diagonal_transpose, ← hJ]; simp only [Matrix.mul_assoc]
  have e2 : Mᵀ * (G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) =
      diagonal s * (diagonal d).map (starRingEnd ℂ) := by
    calc Mᵀ * (G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) = Mᵀ * G * (Y * M).map (starRingEnd ℂ) := by
          rw [Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal s * (diagonal d).map (starRingEnd ℂ) := by
          rw [hYM, Matrix.map_mul, ← hJ]; simp only [Matrix.mul_assoc]
  have h2 : Mᵀ * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, e1, e2]
    ext a b
    by_cases h : a = b
    · subst h; simp [diagonal_apply, hd]; ring
    · simp [diagonal_apply, h]
  have hL : (M⁻¹)ᵀ * Mᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
  have hR : M.map (starRingEnd ℂ) * (M⁻¹).map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  calc Yᵀ * G + G * Y.map (starRingEnd ℂ)
      = ((M⁻¹)ᵀ * Mᵀ) * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) *
          (M.map (starRingEnd ℂ) * (M⁻¹).map (starRingEnd ℂ)) := by rw [hL, hR, Matrix.one_mul, Matrix.mul_one]
    _ = (M⁻¹)ᵀ * (Mᵀ * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ)) *
          (M⁻¹).map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h2, Matrix.mul_zero, Matrix.zero_mul]

theorem torusDer_skew_diag {r : ℕ} (G M : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit M.det) (d s : Fin r → ℂ)
    (hd : ∀ a, conj (d a) = -d a) (hJ : Mᵀ * G * M.map (starRingEnd ℂ) = diagonal s) :
    (M * diagonal d * M⁻¹)ᵀ * G + G * (M * diagonal d * M⁻¹).map (starRingEnd ℂ) = 0 :=
  skewHermitian_of_diagonal_imaginary_frame G M _ hu d s hd hJ (by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one])

theorem torusDer_mem_realLie_and_inFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r), IsOrth X x → ∀ θ : X.Ψ → Fin (r - 1) → ℝ, torusDer x θ ∈ realLie X.Ψ X.Gm ∧
      ∀ τ a b, inFrame x (torusDer x θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0 := by
  intro E _ _ _ r X x hx θ
  have key : ∀ τ : X.Ψ, Matrix.of (torusDer x θ τ) =
      mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ := fun τ => rfl
  refine ⟨?_, fun τ a b => ?_⟩
  · intro τ
    have hu := isUnit_det_of_isOrth hx τ
    refine ⟨?_, fun u w => ?_⟩
    · rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul, trace_diagonal,
        ← Finset.mul_sum, ← ofReal_sum, torusDer_sum_angles, ofReal_zero, mul_zero]
    · rw [key]
      refine torusDer_skew_of_mat τ.1 X.Gm _ ?_ u w
      refine torusDer_skew_diag _ _ hu _ (fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (fun a => ?_) ?_
      · simp
      · rw [← gram_eq]; exact hx τ
  · have hu := isUnit_det_of_isOrth hx τ
    unfold inFrame
    rw [key, show (mat x τ)⁻¹ * (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) * mat x τ =
        ((mat x τ)⁻¹ * mat x τ) * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * ((mat x τ)⁻¹ * mat x τ) by
        simp only [Matrix.mul_assoc], nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one, diagonal_apply]

end GlobalTheory.TorusFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyRealDegreeAndChartDimensionEqStatement
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.totallyRealDegree_and_chartDimension_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), fdeg E = X.Ψ.card ∧ nd X = X.Ψ.card * (r * (r - 1) / 2) := by
  first | exact @GlobalTheory.ChartCount.fdeg_and_nd | exact GlobalTheory.ChartCount.fdeg_and_nd | (intros; apply GlobalTheory.ChartCount.fdeg_and_nd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportOfSeparating
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem transport_of_separating : ∀ (g : ℂ ≃+* ℂ) (ι S : Type) [Fintype ι] [Fintype S] (act : ι → SL(2, ℤ) → ι) (N w : ℕ) (m : S → ℕ) (f f' : ι → ℍ → ℂ) (u u' : S → ι → ℍ → ℂ) (τ₀ τ₁ : ℍ) (ω₀ ω₁ : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ s, IsFam act (m s) (u s)) → (∀ i, QConj g N (f i) (f' i)) → (∀ s i, QConj g N (u s i) (u' s i)) → ω₀ ≠ 0 → g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 → g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 → ∀ i i' : ι, (∀ j, (∀ s, u s j τ₀ = u s i τ₀) → f j τ₀ = f i τ₀) → (∀ s, g (u s i τ₀ / ω₀ ^ m s) = u' s i' τ₁ / ω₁ ^ m s) → g (f i τ₀ / ω₀ ^ w) = f' i' τ₁ / ω₁ ^ w := by
  intro g ι S _ _ act N w m f f' u u' τ₀ τ₁ ω₀ ω₁ hN hact hf hu hq hqu hω h4 h6 i i' hsep hi
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_perm_transport_modular_families_values g ι (Option S) act N (fun o => o.elim w m)
    (fun o => o.elim f u) (fun o => o.elim f' u') τ₀ τ₁ ω₀ ω₁ hN hact
    (by rintro (_ | s); exacts [hf, hu s])
    (by rintro (_ | s) k; exacts [hq k, hqu s k]) h4 h6
  have hj : f (ρ.symm i') τ₀ = f i τ₀ := by
    apply hsep
    intro s
    have h1 : g (u s (ρ.symm i') τ₀ / ω₀ ^ m s) = u' s (ρ (ρ.symm i')) τ₁ / ω₁ ^ m s :=
      hρ (some s) (ρ.symm i')
    rw [Equiv.apply_symm_apply, ← hi s] at h1
    have h2 := g.injective h1
    exact (div_left_inj' (pow_ne_zero _ hω)).1 h2
  have h3 : g (f (ρ.symm i') τ₀ / ω₀ ^ w) = f' (ρ (ρ.symm i')) τ₁ / ω₁ ^ w :=
    hρ none (ρ.symm i')
  rwa [Equiv.apply_symm_apply, hj] at h3

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumRingEqSumIdealCosetsTsumStatement
section
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_ring_eq_sum_ideal_cosets_tsum : ∀ (R : Type) [CommRing R] (M : Ideal R) [Fintype (R ⧸ M)] (h : R → ℂ), Summable h → ∑' α, h α = ∑ c : R ⧸ M, ∑' μ : M, h (Quotient.out c + μ) := by
  first | exact @GlobalTheory.cosets_main | exact GlobalTheory.cosets_main | (intros; apply GlobalTheory.cosets_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRestrictedCharacterInIsotypicPartStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_restricted_character_in_isotypic_part : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), ∀ (χ : G ⋊[φ] Γ → ℂ) (Y : G → ℂ), IsChar ℂ ℂ χ → IsIrrChar ℂ ℂ (fun g => χ (inl g)) → IsChar ℂ ℂ Y → ∑ᶠ g, χ (inl g) * star (Y g) ≠ 0 → Kills (fun δ => χ (inl δ * inr s)) Y := by
  first | (exact @GlobalTheory.Shin.kills_twist_of_pair_ne_zero) | (exact GlobalTheory.Shin.kills_twist_of_pair_ne_zero) | (intros; apply GlobalTheory.Shin.kills_twist_of_pair_ne_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOfBasisFunctor
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem twoCocycle_coboundary_of_basisFunctor_alt : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → (F).obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp (F) u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (F).obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp (F) u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T z hz
  classical
  obtain ⟨n, d, hd, hcT⟩ := hcov T
  have hpt : ∀ i : Fin n, ∃ (p : C') (_ : T ⟶ G.obj p), ∀ S (u : T ⟶ S),
      IsUnit (mp F u (d i)) → Nonempty (G.obj p ⟶ S) := by
    intro i
    obtain ⟨T', l, hl, -, -, huniv⟩ := H T (d i)
    obtain ⟨p, v, w, -⟩ := hcT i T' l hl
    exact ⟨p, v, fun S u hu ↦ by obtain ⟨m, -⟩ := huniv S u hu; exact ⟨w ≫ m⟩⟩
  choose p v hp using hpt
  obtain ⟨f, hf⟩ := GlobalTheory.T.twoCocycle_comma_coboundary_of_standardCover_alt F G H hcov hdir T n d hd z hz
    fun i ↦ GlobalTheory.T.twoCocycle_coboundary_on_unitLocus_piece F G H hdir T (d i) (p i) (v i) (hp i) z hz
  have hup : ∀ t (u : T ⟶ G.obj t) t' t'' (a : t ⟶ t') (b : t' ⟶ t''),
      (∃ i, IsUnit (mp F (u ≫ G.map a) (d i))) → ∃ i, IsUnit (mp F (u ≫ G.map (a ≫ b)) (d i)) := by
    rintro t u t' t'' a b ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rw [G.map_comp, ← Category.assoc, mp_comp]
    exact hi.map _
  obtain ⟨h, hh⟩ := Desc.coboundary_of_restrict (G ⋙ F) (E := fun t ↦ T ⟶ G.obj t)
    (fun u a ↦ u ≫ G.map a) (fun u a b ↦ by simp only [Functor.map_comp, Category.assoc])
    (fun _ _ ↦ True) (fun t u ↦ ∃ i, IsUnit (mp F u (d i))) (fun _ _ _ _ _ ↦ trivial)
    (fun t u _ ↦ GlobalTheory.T.eq_zero_of_upwardFamily_standardCover F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    (fun t u _ ↦ GlobalTheory.T.exists_glued_section_upwardFamily_standardCover F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    (fun t u _ ↦ GlobalTheory.T.van1_of_covBy_upward_sieve F G H hdir t _ (hup t u) (GlobalTheory.T.basisObjects_unitLoci_cover_above F G H hcov hdir T n d hd t u))
    z (fun t t' t'' t''' u a b c _ ↦ hz t t' t'' t''' u a b c) f
    (fun t t' t'' u a b hi ↦ hf t t' t'' u a b hi)
  exact ⟨h, fun t t' t'' u a b ↦ hh t t' t'' u a b trivial⟩

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariant
section
noncomputable section

open Formalism.UG

namespace GlobalTheory.SatakeWeyl

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q n m : ℕ}

theorem mem_radU_iff (u : GU σ n) : u ∈ radU σ (Fin.val : Fin n → ℕ) ↔ IsUnipU u := by
  refine ⟨fun h => ⟨fun i j hij => ?_, fun i => ?_⟩, fun h i j hij => ?_⟩
  · exact (h i j (le_of_lt hij)).trans (Matrix.one_apply_ne (ne_of_gt hij))
  · exact (h i i le_rfl).trans (Matrix.one_apply_eq i)
  · rcases hij.eq_or_lt with e | e
    · obtain rfl : j = i := Fin.ext e
      exact (h.2 j).trans (Matrix.one_apply_eq j).symm
    · exact (h.1 i j e).trans (Matrix.one_apply_ne (ne_of_gt (show j < i from e))).symm

theorem satU_eq (T : (Fin m → ℤ) → GU σ n) (hT : ∀ a, mat (T a) = tMat ϖ n m a) (h : GU σ n → ℂ) (α : Fin m → ℂ) :
    SatU ϖ q h α = ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) *
      ((q : ℂ) ^ 0 * (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
        cellSum (KU σ n) (radU σ Fin.val) h (T a)) := by
  unfold SatU cellSum
  refine finsum_congr fun a => ?_
  rw [Finset.prod_mul_distrib, pow_zero, one_mul, mul_assoc]
  congr 2
  refine finsum_congr fun x => ?_
  congr 1
  refine propext ⟨?_, ?_⟩
  · rintro ⟨u, hu, k, hk, e⟩
    exact ⟨u, (mem_radU_iff u).2 hu, k, hk, mat_injective (by rw [mat_mul, mat_mul, hT]; exact e)⟩
  · rintro ⟨u, hu, k, hk, e⟩
    refine ⟨u, (mem_radU_iff u).1 hu, k, hk, ?_⟩
    have := congrArg mat e
    rw [mat_mul, mat_mul, hT] at this
    exact this

theorem sum_perm (S : (Fin m → ℤ) → ℂ) (π : Equiv.Perm (Fin m)) (hS : ∀ a, S (a ∘ π) = S a) (α : Fin m → ℂ) :
    ∑ᶠ a : Fin m → ℤ, (∏ i, (α ∘ π) i ^ a i) * S a = ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) * S a := by
  rw [← finsum_comp_equiv (Equiv.arrowCongr π.symm (Equiv.refl ℤ))]
  refine finsum_congr fun a => ?_
  have e : (Equiv.arrowCongr π.symm (Equiv.refl ℤ)) a = a ∘ π := by ext i; simp
  rw [e, hS]
  congr 1
  exact Equiv.prod_comp π (fun i => α i ^ a i)

theorem sum_neg (S : (Fin m → ℤ) → ℂ) (j : Fin m) (hS : ∀ a, S (Function.update a j (-a j)) = S a) (α : Fin m → ℂ) :
    ∑ᶠ a : Fin m → ℤ, (∏ i, Function.update α j (α j)⁻¹ i ^ a i) * S a =
      ∑ᶠ a : Fin m → ℤ, (∏ i, α i ^ a i) * S a := by
  have hinv : Function.Involutive fun a : Fin m → ℤ => Function.update a j (-a j) := fun a => by simp
  rw [← finsum_comp_equiv hinv.toPerm]
  refine finsum_congr fun a => ?_
  rw [Function.Involutive.coe_toPerm, hS]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i = j
  · subst hi
    simp
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

theorem perm_of_swap (S : (Fin m → ℤ) → ℂ)
    (hS : ∀ (i j : Fin m), j.val = i.val + 1 → ∀ a, S (a ∘ Equiv.swap i j) = S a) (π : Equiv.Perm (Fin m)) :
    ∀ a, S (a ∘ π) = S a := by
  cases m with
  | zero => intro a; congr 1; funext i; exact i.elim0
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    induction hπ using Submonoid.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hS _ _ (by simp)
    | one => intro a; rfl
    | mul x y _ _ hx hy => intro a; rw [← hx a, ← hy (a ∘ x)]; rfl

theorem satWeyl_of_coeff (hswap : CoeffSwap) (hneg : CoeffNeg) : SatWeyl := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α _ h hh
  choose T hT using fun a : Fin m → ℤ => P.fSatake_tMat_exists (n := n) hU hm a
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hp : ∀ f : Fin m → ℤ, ∏ i, (q : ℂ) ^ f i = (q : ℂ) ^ ∑ i, f i := fun f =>
    (map_prod (zpowersHom ℂˣ (Units.mk0 (q : ℂ) hq)) (fun i => Multiplicative.ofAdd (f i)) Finset.univ) |>
      congrArg (Units.coeHom ℂ) |> fun e => by
        simpa [map_prod, ← ofAdd_sum] using e.symm
  set S : (Fin m → ℤ) → ℂ := fun a => (q : ℂ) ^ 0 *
    (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      cellSum (KU σ n) (radU σ Fin.val) h (T a) with hSdef
  have h1 : ∀ π : Equiv.Perm (Fin m), ∀ a, S (a ∘ π) = S a := by
    refine perm_of_swap S fun i j hij a => ?_
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    simp only [hSdef]
    rw [hswap L ϖ σ q n m hU hm hm' h hh a i j hij _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem i j (by simp) (by simp) hne]
    · simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
      push_cast
      ring
    · rintro c - ⟨hc, hc'⟩
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hc hc', sub_self]
  have h2 : ∀ j : Fin m, j.val + 1 = m → ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j hj a
    simp only [hSdef]
    rw [hneg L ϖ σ q n m hU hm hm' h hh a j hj _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [Function.update_self]
      ring
    · intro c _ hc
      rw [Function.update_of_ne hc, sub_self]
    · simp
  have h3 : ∀ j : Fin m, ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j a
    have hj := j.2
    let l : Fin m := ⟨m - 1, by omega⟩
    rw [← h1 (Equiv.swap j l) a, ← h2 l (by show m - 1 + 1 = m; omega) (a ∘ Equiv.swap j l),
      ← h1 (Equiv.swap j l) (Function.update a j (-a j))]
    congr 1
    rw [Function.update_comp_equiv]
    simp
  refine ⟨fun π => ?_, fun i => ?_⟩
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_perm S π (h1 π) α
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_neg S i (h3 i) α

theorem satWeyl : SatWeyl := by
  have hr : RankOne := GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps GlobalTheory.T.cell_sum_two_stage_descent_unipotent GlobalTheory.T.cell_sum_left_right_invariance_normaliser
    (GlobalTheory.T.contractingAutChainCosetSumScaling_of_unimodularity (GlobalTheory.T.relIndexCosetSumUnimodularity_of_finiteIndex GlobalTheory.T.finite_index_left_right_coset_sums_eq) GlobalTheory.T.contracting_automorphism_subgroup_chain_index)
  have hl : LeviStep := GlobalTheory.T.unitaryCellSumLeviReduction_of_steps hr GlobalTheory.T.exists_smaller_unitary_group_embedding GlobalTheory.T.smaller_unitary_embedding_preserves_integral_parts GlobalTheory.T.unitary_diagonal_factorization_along_embedding GlobalTheory.T.unitary_levi_normalizes_unipotent_radical
    (GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart GlobalTheory.T.unitary_block_triangular_levi_part_unitary) GlobalTheory.T.unitary_dominant_diagonal_conjugation_contracts GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq
  have hi : IntIndex := GlobalTheory.T.card_integers_mod_uniformizer_eq_q_sq
  have ht : TraceZeroIndex := GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq hi
  exact satWeyl_of_coeff (GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction hl (GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq hi) GlobalTheory.T.unitaryFourLeviGL2_cartan_doubleCosets)
    (GlobalTheory.T.unitarySatakeCoeff_lastSignChange_of_leviReduction hl (GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard ht) (GlobalTheory.T.unitaryRankThreeRootIndex_of_cards hi ht))

end GlobalTheory.SatakeWeyl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperTriangularSignFormDiagonalUnimodular
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

theorem GlobalTheory.upperTriangular_signForm_diagonal : ∀ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℂ) (s : Fin r → ℝ), (∀ a, s a = 1 ∨ s a = -1) → IsUnit b.det → (∀ a c : Fin r, c < a → b a c = 0) → bᵀ * diagonal (fun a => (s a : ℂ)) * b.map (starRingEnd ℂ) = diagonal (fun a => (s a : ℂ)) → (∀ a c : Fin r, a ≠ c → b a c = 0) ∧ ∀ a, ‖b a a‖ = 1 := by
  intro r b s hs hdet hup hJ
  classical
  set J : Matrix (Fin r) (Fin r) ℂ := diagonal (fun a => (s a : ℂ)) with hJdef
  have hss : ∀ a, (s a : ℂ) * (s a : ℂ) = 1 := by
    intro a; rcases hs a with h | h <;> simp [h]
  have hJJ : J * J = 1 := by
    rw [hJdef, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hss]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  have hbt : BlockTriangular b id := fun i j hij => hup i j hij
  haveI : Invertible b := b.invertibleOfIsUnitDet hdet
  have hinv : BlockTriangular b⁻¹ id := blockTriangular_inv_of_blockTriangular hbt
  have hright : bᵀ * (J * b.map (starRingEnd ℂ) * J) = 1 := by
    calc bᵀ * (J * b.map (starRingEnd ℂ) * J) = (bᵀ * J * b.map (starRingEnd ℂ)) * J := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have heq : J * b.map (starRingEnd ℂ) * J = (bᵀ)⁻¹ := (Matrix.inv_eq_right_inv hright).symm
  rw [← Matrix.transpose_nonsing_inv] at heq
  have hoff : ∀ a c : Fin r, a < c → b a c = 0 := by
    intro a c hac
    have h1 := congrFun (congrFun heq a) c
    have h2 : (b⁻¹)ᵀ a c = 0 := by
      rw [transpose_apply]; exact hinv hac
    rw [h2, hJdef, mul_diagonal, diagonal_mul] at h1
    simp only [map_apply] at h1
    have hsa : (s a : ℂ) ≠ 0 := by rcases hs a with h | h <;> simp [h]
    have hsc : (s c : ℂ) ≠ 0 := by rcases hs c with h | h <;> simp [h]
    have : (starRingEnd ℂ) (b a c) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hsa
        · exact h
      · exact absurd h hsc
    simpa using this
  have hdiag : ∀ a c : Fin r, a ≠ c → b a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact hoff a c h
    · exact hup a c h
  refine ⟨hdiag, fun a => ?_⟩
  have h1 := congrFun (congrFun hJ a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
  · have hJaa : J a a = (s a : ℂ) := by simp [hJdef]
    rw [mul_diagonal, transpose_apply, map_apply, hJaa] at h1
    have hsa : (s a : ℂ) ≠ 0 := by rcases hs a with h | h <;> simp [h]
    have h2 : b a a * (starRingEnd ℂ) (b a a) = 1 := by
      have : (s a : ℂ) * (b a a * (starRingEnd ℂ) (b a a)) = (s a : ℂ) * 1 := by
        linear_combination h1
      exact mul_left_cancel₀ hsa this
    rw [Complex.mul_conj] at h2
    have h3 : Complex.normSq (b a a) = 1 := by exact_mod_cast h2
    rw [Complex.normSq_eq_norm_sq] at h3
    have h4 : 0 ≤ ‖b a a‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖b a a‖ - 1), sq_nonneg (‖b a a‖ + 1)]
  · intro k _ hk
    rw [mul_diagonal, transpose_apply, map_apply, hdiag k a hk]
    simp
  · intro h; exact absurd (Finset.mem_univ a) h
end

