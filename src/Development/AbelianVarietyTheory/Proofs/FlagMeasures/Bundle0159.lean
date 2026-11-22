import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0096
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0105
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0106
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestWeightVectorFixedByLowerUnitriangular
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolTopLayerLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

section
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem inN_map_mem_of_le (F : FlagD H r) {g : V →ₗ[K] V} (hg : F.InN g) {S : Submodule K V} (hX : F.X ≤ S)
    (hz : F.z ∈ S) : (∀ x ∈ F.X, g x ∈ S) ∧ g F.z ∈ S := by
  have hXa : ∀ a : Fin r, F.Xa a ≤ F.X := fun a =>
    Submodule.span_mono (Set.image_mono fun b _ => b.isLt)
  have he : ∀ a : Fin r, F.e a.castSucc ∈ F.X := fun a => Submodule.subset_span ⟨a, a.isLt, rfl⟩
  constructor
  · have : F.X ≤ S.comap g := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, -, rfl⟩
      have := S.add_mem (hX (hXa a (hg.2.2.1 a))) (hX (he a))
      simpa using this
    exact fun x hx => this hx
  · have := S.add_mem (hX (hg.2.2.2 F.z F.zperp)) hz
    simpa using this

theorem unipotent_map_mem_V0 (F F' : FlagD H r) {g : V →ₗ[K] V} (hg : F.InN g) (hg' : F'.InN g) :
    ∀ x ∈ V0 F F', g x ∈ V0 F F' := by
  have h1 := inN_map_mem_of_le F hg (S := V0 F F') (le_sup_left.trans le_sup_left)
    (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have h2 := inN_map_mem_of_le F' hg' (S := V0 F F') (le_sup_right.trans le_sup_left)
    (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have : V0 F F' ≤ (V0 F F').comap g := by
    refine sup_le (sup_le h1.1 h2.1) (Submodule.span_le.2 ?_)
    rintro _ (rfl | rfl)
    · exact h1.2
    · exact h2.2
  exact fun x hx => this hx

end

theorem star_stable_pow {K : Type} [Field K] [StarRing K] (𝔠 : Ideal (𝓞 K))
    (h : ∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) (n : ℕ) :
    ∀ x ∈ 𝔠 ^ (n + 1), ∃ y ∈ 𝔠 ^ (n + 1), (y : K) = star (x : K) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨a', ha', ea⟩ := ih a ha
      obtain ⟨b', hb', eb⟩ := h b hb
      refine ⟨a' * b', Ideal.mul_mem_mul ha' hb', ?_⟩
      show (a' : K) * (b' : K) = star ((a : K) * (b : K))
      rw [ea, eb, star_mul']
    · rintro a b ⟨a', ha', ea⟩ ⟨b', hb', eb⟩
      refine ⟨a' + b', add_mem ha' hb', ?_⟩
      show (a' : K) + (b' : K) = star ((a : K) + (b : K))
      rw [ea, eb, star_add]

theorem invVol_top_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊔ N.R1) (N.Gam Λ ⊔ N.R1) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ 𝔠 hc0 hcs hcT hcD e hsp hnear
  obtain ⟨hR, -⟩ := GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary K V H hK r N
  obtain ⟨hNF, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨-, -, -, -, hlat, hint⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hΛ
  set L := N.Ref (latL N.F N.F' Λ) with hL
  set M := N.P0 ⊓ rs (𝓞 K) (V0 N.F N.F') with hM
  have hMfg : M.FG := by
    rw [← hint]
    exact Submodule.FG.of_le hlat.fg inf_le_left
  have hstab : ∀ A : Subgroup (V ≃ₗ[K] V), (∀ s ∈ A, ∀ x ∈ M, s x ∈ M) →
      A ≤ MulAction.stabilizer (V ≃ₗ[K] V) M := by
    intro A hA s hs
    rw [MulAction.mem_stabilizer_iff]
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      exact hA s hs y hy
    · intro x hx
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s⁻¹ • x, hA _ (A.inv_mem hs) x hx, ?_⟩
      rw [smul_inv_smul]
  have hG : N.Gam L ⊔ N.R1 ≤ MulAction.stabilizer (V ≃ₗ[K] V) M := by
    refine sup_le (hstab _ ?_) (hstab _ ?_)
    · intro s hs x hx
      rw [← hint] at hx ⊢
      refine ⟨?_, unipotent_map_mem_V0 N.F N.F' ((hR s).1 hs.1).1 ((hR s).1 hs.1).2 x hx.2⟩
      have h1 : s • L = L := hs.2
      have h2 := Submodule.smul_mem_pointwise_smul x s L hx.1
      rw [h1] at h2
      exact h2
    · intro s hs x hx
      have h1 : s • x = x := (mem_fixingSubgroup_iff _).1 hs.2 x hx.2
      have h2 : s x = x := h1
      rw [h2]
      exact hx
  have hGR : N.Gam L ⊔ N.R1 ≤ N.R := sup_le inf_le_left inf_le_left
  have hle : 𝔠 ^ (3 * e + 11) ≤ Ideal.span {(N.T : 𝓞 K)} * 𝔠 ^ (3 * e + 10) := by
    rw [show 3 * e + 11 = (3 * e + 10) + 1 from rfl, pow_succ']
    exact Ideal.mul_mono_left fun x hx => Ideal.mem_span_singleton.2 (hcT x hx)
  obtain ⟨h0, hidx⟩ := GlobalTheory.T.relIndex_congruence_subgroup_le_absNorm_pow K V (N.Gam L ⊔ N.R1) M (𝔠 ^ (3 * e + 11)) (N.Gam Λ ⊔ N.R1) hMfg
    (pow_ne_zero _ hc0) (fun s hs => hG hs) (by
      intro s hs hcong
      obtain ⟨s', hs', hV, hP⟩ := GlobalTheory.T.hermFramePairNormalForm_congruence_lift_smallGroup K V H hK r N (𝔠 ^ (3 * e + 10))
        (star_stable_pow 𝔠 hcs (3 * e + 9)) s (hGR hs)
        (fun x hx => Submodule.smul_mono_left hle (hcong x hx))
      have hfix := GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence K V H hK r N g Λ hg hΛ 𝔠 hc0 hcs hcT hcD e hsp hnear s' hs' hP
      have h1 : s' ∈ N.Gam Λ := ⟨hs'.1, hfix⟩
      have h2 : s'⁻¹ * s ∈ N.R1 := by
        refine ⟨N.R.mul_mem (N.R.inv_mem hs'.1) (hGR hs), (mem_fixingSubgroup_iff _).2 fun y hy => ?_⟩
        have h3 : s • y = s' • y := (hV y hy).symm
        rw [mul_smul, h3, inv_smul_smul]
      have h4 := mul_mem (Subgroup.mem_sup_left h1 : s' ∈ N.Gam Λ ⊔ N.R1) (Subgroup.mem_sup_right h2)
      rwa [mul_inv_cancel_left] at h4)
  have hd : Module.finrank K (Submodule.span K (M : Set V)) ≤ 2 * r + 1 := by
    have h1 : Submodule.span K (M : Set V) ≤ V0 N.F N.F' := Submodule.span_le.2 fun x hx => hx.2
    have h2 := Submodule.finrank_mono h1
    have h3 := hNF.2.2.2.2.1
    have h4 := N.j_le
    omega
  have hn : 1 ≤ Ideal.absNorm 𝔠 := Nat.one_le_iff_ne_zero.2 (fun h => hc0 (Ideal.absNorm_eq_zero_iff.1 h))
  have hfin : (N.Gam Λ ⊔ N.R1).relIndex (N.Gam L ⊔ N.R1) ≤
      Ideal.absNorm 𝔠 ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
    refine hidx.trans ?_
    rw [map_pow, ← pow_mul]
    exact Nat.pow_le_pow_right hn (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd 2))
  have hdiv : ∀ a b : ℕ, (a : ℝ) / (b : ℝ) ≤ a := by
    intro a b
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · exact div_le_self (Nat.cast_nonneg a) (by exact_mod_cast hb)
  unfold GlobalTheory.HL.invVol
  refine (hdiv _ _).trans ?_
  exact_mod_cast hfin

end GlobalTheory.DegCnt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometric
section
open NumberField Matrix

namespace GlobalTheory.FlagMeas

open ReciprocityTheory.ChartRestriction.G.FD

theorem exists_congr_of_hasSignature {n p q : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature M p q) (f : Fin n ≃ Fin p ⊕ Fin q) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, A.det ≠ 0 ∧
      Aᵀ * Mᵀ * A.map (starRingEnd ℂ) = ((Formalism.UG.Jpq p q).submatrix f f)ᵀ := by
  obtain ⟨e, P, hP⟩ := h
  have hPu : IsUnit (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  refine ⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f, ?_, ?_⟩
  · have hσ : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f =
        ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix f f).submatrix (e.trans f.symm) id := by
      ext i j; simp
    rw [hσ, Matrix.det_permute, Matrix.det_submatrix_equiv_self]
    exact mul_ne_zero (by simp) hPu.ne_zero
  · have hM : M = (M.reindex e e).submatrix e e := by ext i j; simp
    have hA : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f)ᴴ * M *
        (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e f = (Formalism.UG.Jpq p q).submatrix f f := by
      rw [hM, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, ← hP]
      congr 1
    rw [← hA]
    simp [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.conjTranspose]
    rfl

theorem sameKindIsometric : SameKindIsometric := by
  intro E _ _ _ hE n J J' hJ hJ' hd hd' hΛ hΛ' hsig
  obtain ⟨hTC, hφ, hun⟩ := hE
  have hne : ∃ z : E, star z ≠ z := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hc := hTC.isComplex w
    rw [InfinitePlace.isComplex_iff] at hc
    apply hc
    rw [ComplexEmbedding.isReal_iff]
    ext z
    rw [ComplexEmbedding.conjugate_coe_eq, ← hφ, hcon]
  obtain ⟨hcm, hst⟩ := (GlobalTheory.LeastExponentCompare.conj_iff E star).1
    ⟨fun φ z => by rw [hφ]; rfl, hne⟩
  have := hcm
  have hcc : ∀ z : E, star z = cc z := fun z => congrFun hst z
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
    refine Formalism.L2.Pj.unramBridge_holds E fun P hP => ?_
    obtain ⟨θ, t, ht, hθ⟩ := hun P hP
    refine ⟨θ, ?_⟩
    convert hθ using 2
    ext
    simp [ht, hcc, cc]
  have hform : ∀ (M : Matrix (Fin n) (Fin n) E) (x y : Fin n → E),
      ReciprocityTheory.ChartRestriction.G.FD.herm Mᵀ x y = star y ⬝ᵥ (M *ᵥ x) := by
    intro M x y
    simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply, Pi.star_apply, hcc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hone : ∀ z : E, z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ↔ z ∈ (algebraMap (𝓞 E) E).range := by
    intro z
    rw [FractionalIdeal.mem_one_iff, RingHom.mem_range]
  have hmod : ∀ (M : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
      (∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (M *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) →
      ∀ x, x ∈ L ↔ ∀ y ∈ L, ReciprocityTheory.ChartRestriction.G.FD.herm Mᵀ x y ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro M L h x
    simp only [hone, hform]
    exact h x
  have hherm : ∀ M : Matrix (Fin n) (Fin n) E, Mᴴ = M → ∀ a b, cc (Mᵀ a b) = Mᵀ b a := by
    intro M hM a b
    rw [← hcc]
    have := congrFun (congrFun hM a) b
    simpa [Matrix.conjTranspose_apply] using this
  have hc : ∀ z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), cc z ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    intro z hz
    rw [FractionalIdeal.mem_one_iff] at hz ⊢
    obtain ⟨x, rfl⟩ := hz
    exact ⟨IsCMField.ringOfIntegersComplexConj E x, by simp [cc]⟩
  have hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧
      J'ᵀ.map τ = Qᵀ * Jᵀ.map τ * Q.map (starRingEnd ℂ) := by
    intro τ
    obtain ⟨p, q, h1, h2⟩ := hsig τ
    obtain ⟨e, -, -⟩ := id h1
    obtain ⟨A, hA, hA'⟩ := exists_congr_of_hasSignature h1 e
    obtain ⟨B, hB, hB'⟩ := exists_congr_of_hasSignature h2 e
    have hBi : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.2 hB)
    refine ⟨A * B⁻¹, by simp [Matrix.det_nonsing_inv, hA, hB], ?_⟩
    rw [Matrix.transpose_map, Matrix.transpose_map]
    have h1' : (B⁻¹)ᵀ * Bᵀ = 1 := by rw [← Matrix.transpose_mul, hBi, Matrix.transpose_one]
    have h2' : B.map (starRingEnd ℂ) * (B⁻¹).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hBi]
      simp
    have hY : (J'.map τ)ᵀ = (B⁻¹)ᵀ * (Bᵀ * (J'.map τ)ᵀ * B.map (starRingEnd ℂ)) *
        (B⁻¹).map (starRingEnd ℂ) := by
      simp only [← Matrix.mul_assoc]
      rw [h1', Matrix.one_mul, Matrix.mul_assoc, h2', Matrix.mul_one]
    rw [hY, hB', ← hA', Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨Λ, hΛl, hΛm⟩ := hΛ
  obtain ⟨Λ', hΛl', hΛm'⟩ := hΛ'
  obtain ⟨P, hPd, hP⟩ := GlobalTheory.SelfDualGenus.congr_of_modular
    (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt
    (by
      intro h
      have h1 : (1 : E) ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
        rw [FractionalIdeal.mem_one_iff]
        exact ⟨1, map_one _⟩
      rw [h, FractionalIdeal.mem_zero_iff] at h1
      exact one_ne_zero h1) hc (hherm J hJ) (hherm J' hJ') (by rwa [Matrix.det_transpose])
    (by rwa [Matrix.det_transpose]) ⟨hΛl.fg, hΛl.span_eq_top⟩ ⟨hΛl'.fg, hΛl'.span_eq_top⟩
    (hmod J Λ hΛm) (hmod J' Λ' hΛm') hs
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero P hPd, ?_⟩
  have hT := congrArg Matrix.transpose hP
  rw [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_transpose] at hT
  change Pᴴ * J * P = J'
  rw [hT, Matrix.mul_assoc]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply, hcc]

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerRepK
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.FormF

variable {n : ℕ}

lemma toMK_cont (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) :=
  (isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val

lemma inner_rep {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn G σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G)
    (x y : H) : ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  LinearIsometry.inner_map_map (⟨(σ g : H →ₗ[ℂ] H), h.2.1 g hg⟩ : H →ₗᵢ[ℂ] H) x y

lemma inner_rep_K {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (h : IsURepOn (Kset ε) σ) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Kset ε) (x y : H) : ⟪σ g x, y⟫_ℂ = ⟪x, σ (star g) y⟫_ℂ := by
  rw [← inner_rep h hg x, ← ContinuousLinearMap.comp_apply (σ g) (σ (star g)), ← h.1.2 _ hg _ (Kset_star ε hg),
    Unitary.mul_star_self_of_mem hg.1, h.1.1, ContinuousLinearMap.one_apply]

theorem rangeType : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (T : S →L[ℂ] H'), IsKTypeOf ε σ abelian₂ S → (∀ k ∈ Kset ε, ∀ x y : S, (y : H) = σ k x → T y = σ' k (T x)) → T ≠ 0 → IsKTypeOf ε σ' abelian₂ (LinearMap.range (T : S →ₗ[ℂ] H')) := by
  intro n ε abelian₂ H _ _ σ S H' _ _ σ' T hS hT hT0
  haveI := hS.1
  have hinj : Function.Injective T := by
    rcases hS.2.2.1 ((LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype) (Submodule.map_subtype_le _ _) (by
      rintro k hk _ ⟨x, hx, rfl⟩
      refine ⟨⟨σ k x, hS.2.1 k hk x x.2⟩, ?_, rfl⟩
      have hx' : T x = 0 := hx
      change T _ = 0
      rw [hT k hk x _ rfl, hx', map_zero]) with h | h
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have : (x : H) ∈ (LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype := ⟨x, hx, rfl⟩
      rw [h] at this
      exact Subtype.ext this
    · exfalso
      apply hT0
      ext x
      have : (x : H) ∈ (LinearMap.ker (T : S →ₗ[ℂ] H')).map S.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hxy⟩ := this
      have : y = x := Subtype.ext hxy
      subst this
      exact hy
  have hT' : ∀ k (hk : k ∈ Kset ε) (x : S), σ' k (T x) = T ⟨σ k x, hS.2.1 k hk x x.2⟩ :=
    fun k hk x => (hT k hk x _ rfl).symm
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rintro k hk _ ⟨x, rfl⟩
    exact ⟨_, (hT' k hk x).symm⟩
  · intro S' hle hst
    rcases hS.2.2.1 ((S'.comap (T : S →ₗ[ℂ] H')).map S.subtype) (Submodule.map_subtype_le _ _) (by
      rintro k hk _ ⟨x, hx, rfl⟩
      refine ⟨⟨σ k x, hS.2.1 k hk x x.2⟩, ?_, rfl⟩
      have hx' : T x ∈ S' := hx
      change T _ ∈ S'
      rw [← hT' k hk x]
      exact hst k hk _ hx') with h | h
    · left
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨x, rfl⟩ := hle hz
      have : (x : H) ∈ (S'.comap (T : S →ₗ[ℂ] H')).map S.subtype := ⟨x, hz, rfl⟩
      rw [h] at this
      have : x = 0 := Subtype.ext this
      simp [this]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨x, rfl⟩
      have : (x : H) ∈ (S'.comap (T : S →ₗ[ℂ] H')).map S.subtype := by rw [h]; exact x.2
      obtain ⟨y, hy, hxy⟩ := this
      have : y = x := Subtype.ext hxy
      subst this
      exact hy
  · obtain ⟨v, hv, hv0, hwt⟩ := hS.2.2.2.1
    refine ⟨T ⟨v, hv⟩, ⟨_, rfl⟩, fun h => hv0 (congrArg Subtype.val (hinj (h.trans (map_zero T).symm))), ?_⟩
    intro θ hθ
    rw [← map_smul]
    exact (hT _ hθ ⟨v, hv⟩ _ (hwt θ hθ).symm).symm
  · rintro μ _ ⟨x, rfl⟩ h0 hwt
    refine hS.2.2.2.2 μ x x.2 (fun h => h0 (by have : x = 0 := Subtype.ext h; simp [this])) fun θ hθ => ?_
    have := hwt θ hθ
    change σ' _ (T x) = _ • T x at this
    rw [hT' _ hθ, ← map_smul] at this
    exact congrArg Subtype.val (hinj this)

theorem psEntry : PhiPos → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), FiniteDimensional ℂ W → (∀ v : W, ContinuousOn (fun k => τ k v) (Kset ε)) → ∀ x : Matrix (Fin n) (Fin n) ℂ, x.PosDef → ∀ u y : W, ⟪y, ps ε lam τ w x u⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * x * toMK k) * (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, u⟫_ℂ) ∂(muK ε) := by
  intro hP n ε lam W _ _ τ w hW hτ x hx u y
  haveI := FiniteDimensional.complete ℂ W
  have hk : Continuous (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.continuous.comp continuous_subtype_val
  have h1 : Continuous (fun k : KG ε => τ (toMK k) w) := (hτ w).comp_continuous hk fun k => k.2
  have h2 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k)) := by
    have e : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k => K_inv k.2
    simp only [e]
    unfold Phi
    refine continuous_finset_prod _ fun i _ => Continuous.zpow₀ ?_ _ fun k => Or.inl ?_
    · unfold leadMinor
      exact (((hk.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hk).matrix_submatrix _ _).matrix_det
    · exact (hP n lam _ (hx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC k.2).1))).1 i
  have h3 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) :=
    h2.smul (((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp ((innerSL ℂ).continuous.comp h1)).clm_apply h1)
  have h4 := h3.integrable_of_hasCompactSupport (μ := muK ε) (HasCompactSupport.of_compactSpace _)
  unfold ps
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply h4,
    ← integral_inner (h4.apply_continuousLinearMap u)]
  congr 2
  funext k
  simp [inner_smul_right, mul_comm]

theorem muConj : ∀ (n : ℕ) (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ), ∫ k : KG ε, F ((toMK k).map star) ∂(muK ε) = ∫ k : KG ε, F (toMK k) ∂(muK ε) := by
  intro n ε F
  let c0 : (Matrix (Fin n) (Fin n) ℂ)ˣ →* (Matrix (Fin n) (Fin n) ℂ)ˣ :=
    Units.map (RingHom.mapMatrix (starRingEnd ℂ)).toMonoidHom
  let c : KG ε → KG ε := fun k => ⟨⟨c0 k.1.1, UJ_star k.1.2⟩, K_star k.2⟩
  have hc : ∀ k, toMK (c k) = (toMK k).map star := fun k => rfl
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hcc : ∀ k, c (c k) = k := fun k => hemb.injective (by simp only [hc, map_star_star])
  have hcont : Continuous c := by
    rw [hemb.continuous_iff]
    exact hemb.continuous.matrix_map continuous_star
  let e : KG ε ≃ₜ* KG ε :=
    { toFun := c, invFun := c, left_inv := hcc, right_inv := hcc
      map_mul' := fun a b => hemb.injective (by
        change (toMK a * toMK b).map star = (toMK a).map star * (toMK b).map star
        exact map_star_mul _ _)
      continuous_toFun := hcont, continuous_invFun := hcont }
  haveI := (compact_haar_holds n ε).1
  haveI : IsProbabilityMeasure ((muK ε).map e) := Measure.isProbabilityMeasure_map hcont.measurable.aemeasurable
  haveI : ((muK ε).map e).IsHaarMeasure := e.isHaarMeasure_map _
  have h : (muK ε).map e = muK ε := Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _
  have := integral_map_equiv (μ := muK ε) e.toHomeomorph.toMeasurableEquiv (fun k => F (toMK k))
  rw [show (muK ε).map e.toHomeomorph.toMeasurableEquiv = muK ε from h] at this
  exact this.symm

theorem avgMap : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (u : H), FiniteDimensional ℂ W → IsURepOn (Kset ε) ρ → CompleteSpace H → IsURepOn (Kset ε) σ → ∃ T : W →L[ℂ] H, (∀ k ∈ Kset ε, ∀ x, T (ρ k x) = σ k (T x)) ∧ ∀ (x : W) (φ : H →L[ℂ] ℂ), Integrable (fun k : KG ε => ⟪ρ (toMK k) w, x⟫_ℂ * φ (σ (toMK k) u)) (muK ε) ∧ φ (T x) = ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ * φ (σ (toMK k) u) ∂(muK ε) := by
  intro n ε W _ _ ρ w H _ _ σ u hW hρ hH hσ
  have h1 : Continuous (fun k : KG ε => ρ (toMK k) w) := (hρ.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have h2 : Continuous (fun k : KG ε => σ (toMK k) u) := (hσ.2.2 u).comp_continuous (toMK_cont ε) fun k => k.2
  have hi : ∀ x : W, Integrable (fun k : KG ε => ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u) (muK ε) := fun x =>
    ((h1.inner continuous_const).smul h2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let T : W →ₗ[ℂ] H :=
    { toFun := fun x => ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε)
      map_add' := fun x y => by simp only [inner_add_right, add_smul]; exact integral_add (hi x) (hi y)
      map_smul' := fun c x => by simp only [inner_smul_right, mul_smul, integral_smul, RingHom.id_apply] }
  refine ⟨LinearMap.toContinuousLinearMap T, fun k hk x => ?_, fun x φ => ⟨?_, ?_⟩⟩
  · obtain ⟨k0, rfl⟩ : k ∈ Set.range (fun k : KG ε => toMK k) := by rw [range_toMK]; exact hk
    change ∫ k : KG ε, ⟪ρ (toMK k) w, ρ (toMK k0) x⟫_ℂ • σ (toMK k) u ∂(muK ε) =
      σ (toMK k0) (∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hi x), ← integral_mul_left_eq_self _ k0]
    congr 1
    funext k
    have e : toMK (k0 * k) = toMK k0 * toMK k := rfl
    simp only [e, hρ.1.2 _ k0.2 _ k.2, hσ.1.2 _ k0.2 _ k.2, ContinuousLinearMap.comp_apply, inner_rep hρ k0.2,
      map_smul]
  · simpa using φ.integrable_comp (hi x)
  · change φ (∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ • σ (toMK k) u ∂(muK ε)) = _
    rw [← ContinuousLinearMap.integral_comp_comm _ (hi x)]
    simp

theorem avgSchur : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ρ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), FiniteDimensional ℂ W → IsURepOn (Kset ε) ρ → (∀ S : Submodule ℂ W, IsKStableOn ε ρ S → S = ⊥ ∨ S = ⊤) → w ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧ ∀ (x : W) (φ : W →L[ℂ] ℂ), ∫ k : KG ε, ⟪ρ (toMK k) w, x⟫_ℂ * φ (ρ (toMK k) w) ∂(muK ε) = c * φ x := by
  intro n ε W _ _ ρ w hW hρ hirr hw
  haveI := FiniteDimensional.complete ℂ W
  haveI : Nontrivial W := ⟨⟨w, 0, hw⟩⟩
  obtain ⟨T, hT, hTi⟩ := avgMap n ε W ρ w W ρ w hW hρ inferInstance hρ
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T : W →ₗ[ℂ] W)
  have hTc : ∀ x, T x = c • x := by
    rcases hirr (Module.End.eigenspace (T : W →ₗ[ℂ] W) c) (fun k hk x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      change T _ = _ at hx ⊢
      rw [hT k hk, hx, map_smul]) with h | h
    · exact absurd h hc
    · intro x
      have : x ∈ Module.End.eigenspace (T : W →ₗ[ℂ] W) c := by rw [h]; trivial
      exact Module.End.mem_eigenspace_iff.1 this
  refine ⟨c, ?_, fun x φ => by rw [← (hTi x φ).2, hTc, map_smul, smul_eq_mul]⟩
  rintro rfl
  have h1 : Continuous (fun k : KG ε => ρ (toMK k) w) := (hρ.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have h0 := (hTi w (innerSL ℂ w)).2
  rw [hTc, zero_smul, map_zero] at h0
  have e : ∀ k : KG ε, ⟪ρ (toMK k) w, w⟫_ℂ * innerSL ℂ w (ρ (toMK k) w) =
      ((‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [innerSL_apply_apply, ← inner_conj_symm, Complex.conj_mul']; simp
  simp only [e, integral_ofReal] at h0
  have hc2 : Continuous (fun k : KG ε => ‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2) := (continuous_const.inner h1).norm.pow 2
  have hpos := hc2.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := muK ε) (x := 1)
    (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (by
      have : toMK (1 : KG ε) = 1 := rfl
      simpa [this, hρ.1.1] using hw)
  have : (0 : ℝ) = ∫ k : KG ε, ‖⟪w, ρ (toMK k) w⟫_ℂ‖ ^ 2 ∂(muK ε) := by exact_mod_cast h0
  linarith

end GlobalTheory.Dec.FormF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestWeightVectorFixedByLowerUnitriangularStatement
section
open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_weight_vector_fixed_by_lower_unitriangular : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), Formalism.QuantumDeterminants.IsCRepOn (GlobalTheory.Dec.KC ε) τ → DifferentiableAt ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) (fun i j => (1 : Matrix (Fin n) (Fin n) ℂ) i j) → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) τ (-abelian₂) w → (∀ (μ : Fin n → ℝ) (v : W), v ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) τ (-μ) v → Formalism.MainNotions.S.CDom ε μ abelian₂) → ∀ y ∈ GlobalTheory.Dec.KC ε, Formalism.MainNotions.S.IsLoUni y → τ y w = w := by
  first | exact @GlobalTheory.Dec.LowFix.lowest_fixed | exact GlobalTheory.Dec.LowFix.lowest_fixed | (intros; apply GlobalTheory.Dec.LowFix.lowest_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagLocalSizesUnitaryStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_flagLocalSizes_unitary : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (i : Fin a), Measurable fun g : Formalism.REAL.UJ ε => locSize j W (uMat g) i := by
  first | exact @GlobalTheory.FlagMeas.measurable_locSize_uMat | exact GlobalTheory.FlagMeas.measurable_locSize_uMat | (intros; apply GlobalTheory.FlagMeas.measurable_locSize_uMat <;> assumption)
end

