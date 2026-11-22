import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0055
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
import Formalism.QuotientMetricDivisors.Statement
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrob

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterGlobalArtinUnitsTrivialUniformiserPower
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat

namespace GlobalTheory.NormCompat

theorem chi_artin_restrict : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] [IsAlgClosure K Ω] (art : Ideles E →* Gab E Ω) (artK : Ideles K →* Gab K Ω), IsGlobalArtin art → IsGlobalArtin artK → ∀ (ρ : Gab K Ω →* Gab E Ω), (∀ τ : G K Ω, ρ (toAb K Ω τ) = toAb E Ω (τ.restrictScalars E)) → ∀ (B : Type) [CommGroup B] (χ : Gab E Ω →* B) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → (∀ x, IsUnitAt v x → χ (art (localIdele E v x)) = 1) → (∀ x, IsUnitAt w x → χ (ρ (artK (localIdele K w x))) = 1) ∧ ∀ x ϖ, IsUnifAt w x → IsUnifAt v ϖ → χ (ρ (artK (localIdele K w x))) = χ (art (localIdele E v ϖ)) ^ w.asIdeal.inertiaDeg (𝓞 E) := by
  intro E Ω _ _ _ _ _ K _ _ _ art artK ha haK ρ hρ B _ χ v w hwv hχ
  obtain ⟨A, hAw⟩ := exists_isPlaceOver (F := K) Ω w
  obtain ⟨hAv, -, hine, hfrob⟩ := GlobalTheory.T.frobenius_restrictScalars_pow_mod_inertia E Ω K v w hwv A hAw

  have hI : ∀ ι ∈ Ine (F := E) A, χ (toAb E Ω ι) = 1 := by
    intro ι hι
    obtain ⟨u, hu, e⟩ := (ha.ine v A hAv (toAb E Ω ι)).mpr ⟨ι, hι, rfl⟩
    rw [← e]
    exact hχ u hu
  refine ⟨fun x hx => ?_, fun x ϖ hx hϖ => ?_⟩
  · obtain ⟨ι, hι, e⟩ := (haK.ine w A hAw _).mp ⟨x, hx, rfl⟩
    rw [← e, hρ]
    exact hI _ (hine ι hι)
  · obtain ⟨σ, hσ, e⟩ := (haK.frob w A hAw _).mp ⟨x, hx, rfl⟩
    obtain ⟨φ, hφ, e'⟩ := (ha.frob v A hAv _).mp ⟨ϖ, hϖ, rfl⟩
    have hm := hI _ (hfrob σ φ hσ hφ)
    have hr : (σ⁻¹).restrictScalars E = (σ.restrictScalars E)⁻¹ := AlgEquiv.ext fun _ => rfl
    rw [← e, hρ, ← e', hr, map_inv, map_inv, map_inv, map_inv, inv_pow]
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, map_pow] at hm
    rw [inv_inj]
    exact mul_inv_eq_one.mp hm

end GlobalTheory.NormCompat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenspaceLeEigenspacePow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem eigenspace_le_eigenspace_pow {V : Type*} [AddCommGroup V] [Module ℂ V] (f : End ℂ V)
    (α : ℂ) (m : ℕ) : f.eigenspace α ≤ (f ^ m).eigenspace (α ^ m) := by
  intro v hv
  rw [End.mem_eigenspace_iff] at hv ⊢
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', End.mul_apply, ih, map_smul, hv, smul_smul, pow_succ]

theorem absSpace_of_neg {V : Type*} [AddCommGroup V] [Module ℂ V] (f : End ℂ V) {r : ℝ}
    (hr : r < 0) : absSpace f r = ⊥ := by
  rw [absSpace, eq_bot_iff]
  exact iSup₂_le fun α hα => absurd (hα ▸ norm_nonneg α) (not_le.mpr hr)

theorem absSpace_pow {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : End ℂ V} (hf : f.IsSemisimple) {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : 0 ≤ r) :
    absSpace (f ^ m) (r ^ m) = absSpace f r := by
  have hP : absSpace f r ≤ absSpace (f ^ m) (r ^ m) :=
    iSup₂_le fun α hα => (eigenspace_le_eigenspace_pow f α m).trans
      (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = r ^ m) => (f ^ m).eigenspace β) (α ^ m)
        (by rw [norm_pow, hα]) le_rfl)
  set Q : Submodule ℂ V := ⨆ β ∈ {β : ℂ | ‖β‖ ≠ r ^ m}, (f ^ m).eigenspace β with hQ
  have hd : Disjoint (absSpace (f ^ m) (r ^ m)) Q :=
    (End.eigenspaces_iSupIndep (f ^ m)).disjoint_biSup_biSup
      (s := {β : ℂ | ‖β‖ = r ^ m}) (t := {β : ℂ | ‖β‖ ≠ r ^ m})
      (Set.disjoint_left.mpr fun _ h1 h2 => h2 h1)
  have ht : absSpace f r ⊔ Q = ⊤ := by
    rw [eq_top_iff, ← hf.iSup_eigenspace_eq_top]
    refine iSup_le fun α => ?_
    by_cases hα : ‖α‖ = r
    · exact le_sup_of_le_left
        (le_iSup₂_of_le (f := fun (β : ℂ) (_ : ‖β‖ = r) => f.eigenspace β) α hα le_rfl)
    · refine le_sup_of_le_right ((eigenspace_le_eigenspace_pow f α m).trans ?_)
      refine le_iSup₂_of_le (f := fun β (_ : β ∈ {β : ℂ | ‖β‖ ≠ r ^ m}) => (f ^ m).eigenspace β)
        (α ^ m) ?_ le_rfl
      intro h
      rw [norm_pow] at h
      exact hα ((pow_left_inj₀ (norm_nonneg α) hr hm.ne').mp h)
  calc absSpace (f ^ m) (r ^ m) = (absSpace f r ⊔ Q) ⊓ absSpace (f ^ m) (r ^ m) := by
        rw [ht, top_inf_eq]
    _ = absSpace f r := by rw [sup_inf_assoc_of_le _ hP, hd.symm.eq_bot, sup_bot_eq]

theorem absSpace_eq_of_deg_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (φ ψ : Weil h), deg φ = deg ψ →
    ∀ r : ℝ, absSpace (a.ρ φ) r = absSpace (a.ρ ψ) r := by
  intro E Ω _ _ _ _ _ A w h V _ _ _ a φ ψ hd r
  rcases lt_or_ge r 0 with hr | hr
  · rw [absSpace_of_neg _ hr, absSpace_of_neg _ hr]
  · obtain ⟨m, hm, he⟩ := GlobalTheory.T.exists_pow_eq_pow_of_weilDegree_eq_smooth E Ω A w h V a.ρ a.smooth φ ψ hd
    rw [← absSpace_pow (a.semisimple φ) hm hr, ← absSpace_pow (a.semisimple ψ) hm hr, he]

end GlobalTheory.WeilDeligne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalUnitaryCoordinateZeroOfRationalPoints
section
noncomputable section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.UDense

theorem map_inv_field_hom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    (A⁻¹).map f = (A.map f)⁻¹ := by
  have h1 : A.adjugate.map f = (A.map f).adjugate := by
    have := RingHom.map_adjugate f A; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (A.map f).det = f A.det := by
    have := RingHom.map_det f A; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv',
    Ring.inverse_eq_inv', map_inv₀]

theorem eval_bind₁_scale {ι : Type} (r w : ι → ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval w
        (MvPolynomial.bind₁ (fun j => MvPolynomial.C (r j) * MvPolynomial.X j) f) =
      MvPolynomial.eval (fun j => r j * w j) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, MvPolynomial.bind₁_X_right, MvPolynomial.eval_X,
      MvPolynomial.eval_C]

theorem vanish_generic (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hF : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (hX : IsUPt X) (hd : ∀ σ, (1 + X σ).det ≠ 0) :
    MvPolynomial.eval (upt X) F = 0 := by
  classical
  let V : (L →+* ℂ) → Matrix (Fin n) (Fin n) (MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :=
    fun σ => Matrix.of fun i j => MvPolynomial.X (σ, i, j)
  let P : (L →+* ℂ) × Fin n × Fin n → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
    fun p => ((1 + V p.1) * (1 - V p.1).adjugate) p.2.1 p.2.2
  let D : (L →+* ℂ) × Fin n × Fin n → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
    fun p => (1 - V p.1).det
  obtain ⟨G, M, hGM⟩ := GlobalTheory.T.mvPolynomial_clear_denominators_eval F P D
  have evV : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) σ,
      (V σ).map (MvPolynomial.eval (upt y)) = y σ := by
    intro y σ; ext i j; simp [V, upt]
  have evDet : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) σ,
      MvPolynomial.eval (upt y) ((1 - V σ).det) = (1 - y σ).det := by
    intro y σ
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), evV]
  have evP : ∀ (y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), (∀ σ, (1 - y σ).det ≠ 0) →
      (fun p => MvPolynomial.eval (upt y) (P p) / MvPolynomial.eval (upt y) (D p)) =
        upt (fun σ => (1 + y σ) * (1 - y σ)⁻¹) := by
    intro y hy
    funext p
    have hm : ((1 + V p.1) * (1 - V p.1).adjugate).map (MvPolynomial.eval (upt y)) =
        (1 + y p.1) * (1 - y p.1).adjugate := by
      rw [Matrix.map_mul, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, RingHom.map_adjugate,
        RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
        Matrix.map_one _ (map_zero _) (map_one _), evV]
    have hP : MvPolynomial.eval (upt y) (P p) = ((1 + y p.1) * (1 - y p.1).adjugate) p.2.1 p.2.2 := by
      rw [← hm]; rfl
    rw [hP, show MvPolynomial.eval (upt y) (D p) = (1 - y p.1).det from evDet y p.1]
    simp only [upt, Matrix.inv_def, Matrix.mul_smul, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
    rw [div_eq_inv_mul]
  let Q := G * ∏ σ, (1 - V σ).det
  have hQ : ∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 →
      MvPolynomial.eval (upt (ratPt S)) Q = 0 := by
    intro S hS
    have hdS : ∀ σ : L →+* ℂ, (1 - ratPt S σ).det = σ (1 - S).det := by
      intro σ
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
      rfl
    simp only [Q, map_mul, map_prod, evDet, hdS]
    by_cases h0 : (1 - S).det = 0
    · have σ0 : L →+* ℂ := Classical.arbitrary _
      rw [Finset.prod_eq_zero (Finset.mem_univ σ0) (by rw [h0, map_zero]), mul_zero]
    · obtain ⟨γ₀, hγ, hγv⟩ := GlobalTheory.T.cayleyTransform_mem_rational_unitaryGroup L n S hS h0
      have hne : ∀ σ : L →+* ℂ, (1 - ratPt S σ).det ≠ 0 := fun σ => by
        rw [hdS]; exact (map_ne_zero σ).2 h0
      have hDy : ∀ p, MvPolynomial.eval (upt (ratPt S)) (D p) ≠ 0 := fun p => by
        rw [show MvPolynomial.eval (upt (ratPt S)) (D p) = _ from evDet _ p.1]; exact hne p.1
      obtain ⟨-, hG⟩ := hGM _ hDy
      rw [hG, evP _ hne]
      have hc : (fun σ => (1 + ratPt S σ) * (1 - ratPt S σ)⁻¹) = ratPt (γ₀ : Matrix (Fin n) (Fin n) L) := by
        funext σ
        rw [hγv]
        simp only [ratPt, Matrix.map_mul, map_inv_field_hom, Matrix.map_sub _ (map_sub _), Matrix.map_add _ (map_add _),
          Matrix.map_one _ (map_zero _) (map_one _)]
      rw [hc, hF γ₀ hγ, mul_zero, zero_mul]
  obtain ⟨Y, hYs, hYd, hYX⟩ := GlobalTheory.T.unitary_family_eq_cayley_of_skew_family L n X hX hd
  have hQY := GlobalTheory.T.mvPolynomial_eval_zero_of_vanishing_rational_skewHermitian L n Q hQ Y hYs
  have hDY : ∀ p, MvPolynomial.eval (upt Y) (D p) ≠ 0 := fun p => by
    rw [show MvPolynomial.eval (upt Y) (D p) = _ from evDet _ p.1]; exact hYd p.1
  obtain ⟨hM, hG⟩ := hGM _ hDY
  simp only [Q, map_mul, map_prod, evDet] at hQY
  have hprod : ∏ σ, (1 - Y σ).det ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hYd σ
  have hG0 : MvPolynomial.eval (upt Y) G = 0 := (mul_eq_zero.1 hQY).resolve_right hprod
  rw [hG, evP _ hYd, show (fun σ => (1 + Y σ) * (1 - Y σ)⁻¹) = X from funext hYX] at hG0
  exact (mul_eq_zero.1 hG0).resolve_left hM

theorem eval_eq_zero_of_rat : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0) →
    ∀ X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → MvPolynomial.eval (upt X) F = 0 := by
  intro L _ _ _ n F hF X hX
  obtain ⟨a, ha, hdet⟩ := GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero L n X
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := complexConj_invol L
  have ha' : c a * a = 1 := by rw [mul_comm]; exact ha
  have hca0 : c a ≠ 0 := left_ne_zero_of_mul_eq_one ha'
  have hemb : ∀ (σ : L →+* ℂ) x, ComplexEmbedding.conjugate σ x = σ (c x) := fun σ x =>
    (IsCMField.complexEmbedding_complexConj L σ x).symm
  let F' := MvPolynomial.bind₁ (fun p : (L →+* ℂ) × Fin n × Fin n => MvPolynomial.C (p.1 (c a)) * MvPolynomial.X p) F
  have hF'ev : ∀ z, MvPolynomial.eval z F' = MvPolynomial.eval (fun p => p.1 (c a) * z p) F :=
    fun z => eval_bind₁_scale _ z F
  have hF' : ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F' = 0 := by
    intro γ₀ hγ
    let s : GL (Fin n) L := Units.map (algebraMap L (Matrix (Fin n) (Fin n) L) : L →* Matrix (Fin n) (Fin n) L)
      (Units.mk0 (c a) hca0)
    have hs : (s : Matrix (Fin n) (Fin n) L) = Matrix.scalar (Fin n) (c a) := rfl
    have hmem : s * γ₀ ∈ GQ0 L n := by
      refine (GQ0 L n).mul_mem ?_ hγ
      show (s : Matrix (Fin n) (Fin n) L) * conjT c s = 1
      rw [hs, conjT]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.scalar_apply, hcc, ha']
      · simp [Matrix.scalar_apply, Matrix.one_apply, hij]
    have := hF _ hmem
    rw [hF'ev, ← this]
    refine congrArg (fun z => MvPolynomial.eval z F) ?_
    funext p
    simp [upt, ratPt, hs, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  let X' : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ => σ a • X σ
  have hX' : IsUPt X' := by
    intro σ
    simp only [X', Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hX σ, hemb, ← map_mul, ha, ha',
      map_one, one_smul]
  have h := vanish_generic L n F' hF' X' hX' hdet
  rw [hF'ev] at h
  rw [← h]
  refine congrArg (fun z => MvPolynomial.eval z F) ?_
  funext p
  simp only [upt, X', Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, ha', map_one, one_mul]

end GlobalTheory.UDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSpanningFamily
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section
namespace GlobalTheory.PhtSpan

open GlobalTheory.DRFil

section Ev
variable {Q F LL : Type} [Field Q] [CharZero Q] [Field F] [Algebra Q F] [FiniteDimensional Q F]
  [Field LL] [Algebra Q LL]

def ev (τ : F →ₐ[Q] LL) : LL ⊗[Q] F →ₗ[LL] LL :=
  (Algebra.TensorProduct.lift (AlgHom.id LL LL) τ (fun _ _ => Commute.all _ _)).toLinearMap

@[simp] theorem ev_tmul (τ : F →ₐ[Q] LL) (a : LL) (c : F) : ev τ (a ⊗ₜ[Q] c) = a * τ c := by
  simp [ev]

def e (τ : F →ₐ[Q] LL) : LL ⊗[Q] F := (exists_idem τ).choose

end Ev
end GlobalTheory.PhtSpan

namespace GlobalTheory.PhtSpan
open GlobalTheory.DRFil

section Mod
variable {Q F LL : Type} [Field Q] [CharZero Q] [Field F] [Algebra Q F] [FiniteDimensional Q F]
  [Field LL] [Algebra Q LL] {B : Type} [CommRing B] [Algebra Q B] [Algebra F B] [IsScalarTower Q F B]
  {V : Type} [AddCommGroup V] [Module LL V] [Module Q V] [IsScalarTower Q LL V]

end Mod
end GlobalTheory.PhtSpan

namespace GlobalTheory.PhtSpan
open GlobalTheory.DRFil

end GlobalTheory.PhtSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueEmbeddingEigenspaceSum
section
noncomputable section

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial IntermediateField

namespace GlobalTheory.EigDecomp

theorem exists_integral_separating (E : Type) [Field E] [NumberField E] :
    ∃ α : 𝓞 E, (∀ τ τ' : E →+* ℂ, τ (α : E) = τ' (α : E) → τ = τ') ∧
      ∀ a : 𝓞 E, ∃ N : ℤ, N ≠ 0 ∧ ∃ g : ℤ[X], aeval α g = N • a := by
  obtain ⟨α0, hα0⟩ := Field.exists_primitive_element ℚ E
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ ({α0} : Finset E)
  have hi : IsIntegral ℤ (d • α0) := hint α0 (Finset.mem_singleton_self _)
  let α : 𝓞 E := ⟨d • α0, hi⟩
  have hαE : (α : E) = d • α0 := rfl
  have hadjF : ℚ⟮(α : E)⟯ = ⊤ := by
    refine top_le_iff.mp (hα0 ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)
    have h1 : α0 = ((d : ℚ)⁻¹) • (α : E) := by
      rw [hαE, zsmul_eq_mul, Algebra.smul_def, ← mul_assoc, ← map_intCast (algebraMap ℚ E) d, ← map_mul,
        inv_mul_cancel₀ (Int.cast_ne_zero.mpr hd), map_one, one_mul]
    rw [h1]
    exact IntermediateField.smul_mem _ (IntermediateField.mem_adjoin_simple_self ℚ _)
  have hadj : Algebra.adjoin ℚ {(α : E)} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (α : E)), hadjF, IntermediateField.top_toSubalgebra]
  refine ⟨α, fun τ τ' h => ?_, fun a => ?_⟩
  · have := AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := τ.toRatAlgHom) (φ₂ := τ'.toRatAlgHom)
      (by rintro x rfl; exact h)
    ext x
    exact congrArg (fun f : E →ₐ[ℚ] ℂ => f x) this
  · have ha : (a : E) ∈ Algebra.adjoin ℚ {(α : E)} := hadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨g, hg⟩ := ha
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) g
    refine ⟨b, nonZeroDivisors.ne_zero hbM, IsLocalization.integerNormalization (nonZeroDivisors ℤ) g, ?_⟩
    apply RingOfIntegers.coe_injective
    have hg' : aeval (algebraMap (𝓞 E) E α) g = algebraMap (𝓞 E) E a := hg
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap ℚ, hb, map_zsmul, hg', map_zsmul]

end GlobalTheory.EigDecomp

namespace GlobalTheory.EigDecomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem nodal_eq_minpoly_map (c : Coeff l) (α : 𝓞 E)
    (hinj : Function.Injective fun τ : E →+* ℂ => embK c τ α) :
    Lagrange.nodal Finset.univ (fun τ : E →+* ℂ => embK c τ α) = (minpoly ℤ α).map (Int.castRingHom c.F) := by
  have hint : IsIntegral ℤ α := Algebra.IsIntegral.isIntegral α
  have hintE : IsIntegral ℤ (α : E) := RingOfIntegers.isIntegral_coe α
  symm
  refine eq_of_monic_of_dvd_of_natDegree_le Lagrange.nodal_monic ((minpoly.monic hint).map _) ?_ ?_
  · rw [Lagrange.nodal]
    refine Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C hinj).set_pairwise _) fun τ _ => dvd_iff_isRoot.mpr ?_
    have h := aeval_algHom_apply (embK c τ).toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    rw [IsRoot.def, eval_map, ← algebraMap_int_eq, ← aeval_def]
    exact h
  · rw [natDegree_map_eq_of_injective (RingHom.injective_int _), Lagrange.natDegree_nodal, Finset.card_univ,
      NumberField.Embeddings.card E ℂ, ← RingOfIntegers.minpoly_coe,
      ← natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hintE]
    exact minpoly.natDegree_le _

end GlobalTheory.EigDecomp

namespace GlobalTheory.EigDecomp

theorem X_sub_C_mul_basis {ι F : Type*} [Field F] [DecidableEq ι] {s : Finset ι} {v : ι → F} {i : ι}
    (hi : i ∈ s) :
    (X - C (v i)) * Lagrange.basis s v i = C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi, mul_left_comm]
  congr 1
  exact EuclideanDomain.mul_div_cancel' (X_sub_C_ne_zero _) (Lagrange.X_sub_C_dvd_nodal v hi)

theorem exists_unique_eigen_sum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l : Level H} (c : Coeff l) {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (φ : c.F →+* R)
    (ρ : 𝓞 E →+* Module.End R V) (v : V), ∃! w : (E →+* ℂ) → V,
      (∀ τ a, ρ a (w τ) = φ (embK c τ a) • w τ) ∧ ∑ τ, w τ = v := by
  intro E _ _ _ H l c R V _ _ _ φ ρ v
  classical
  obtain ⟨α, hinj, hden⟩ := exists_integral_separating E
  let lam : (E →+* ℂ) → c.F := fun τ => embK c τ α
  have hlinj : Function.Injective lam := fun τ τ' h => hinj τ τ' (by
    have := congrArg (fun x : c.F => (x : ℂ)) h
    simpa [lam, embK_coe] using this)
  let A : Module.End R V := ρ α
  let ψ : c.F →+* Module.End R V := (algebraMap R (Module.End R V)).comp φ
  have hc : ∀ x, Commute (ψ x) A := fun x => Algebra.commute_algebraMap_left (φ x) A
  let ev : Polynomial c.F →+* Module.End R V := eval₂RingHom' ψ A hc
  have hev : ∀ p, ev p = p.eval₂ ψ A := fun p => rfl
  have hev_int : ∀ g : ℤ[X], ev (g.map (Int.castRingHom c.F)) = aeval A g := by
    intro g
    rw [hev, eval₂_map, aeval_def]
    congr 1
    exact RingHom.ext_int _ _
  have heig : ∀ (μ : c.F) (x : V), A x = φ μ • x → ∀ p : Polynomial c.F, ev p x = φ (p.eval μ) • x := by
    intro μ x hx p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, eval_add, map_add, add_smul]
    | monomial k a =>
      have hk : ∀ k : ℕ, (A ^ k) x = φ μ ^ k • x := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ, mul_comm]
      rw [hev, eval₂_monomial, eval_monomial, Module.End.mul_apply, hk, map_mul, map_pow]
      simp [ψ, smul_smul, mul_comm]
  have hnodal : ev (Lagrange.nodal Finset.univ lam) = 0 := by
    rw [nodal_eq_minpoly_map c α hlinj, hev_int]
    have h := aeval_algHom_apply ρ.toIntAlgHom α (minpoly ℤ α)
    rw [minpoly.aeval, map_zero] at h
    exact h
  let P : (E →+* ℂ) → Module.End R V := fun τ => ev (Lagrange.basis Finset.univ lam τ)
  have hPeig : ∀ τ x, A (P τ x) = φ (lam τ) • P τ x := by
    intro τ x
    have h := congrArg (fun p => ev p x) (X_sub_C_mul_basis (s := Finset.univ) (v := lam) (Finset.mem_univ τ))
    simp only [map_mul, map_sub, hnodal, mul_zero, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.zero_apply] at h
    rw [hev X, eval₂_X, hev (C _), eval₂_C] at h
    simpa [ψ, sub_eq_zero, P] using h
  have hsum : ∑ τ, P τ = 1 := by
    simp only [P]
    rw [← map_sum, Lagrange.sum_basis hlinj.injOn Finset.univ_nonempty, map_one]
  have hall : ∀ τ x, A x = φ (lam τ) • x → ∀ a, ρ a x = φ (embK c τ a) • x := by
    intro τ x hx a
    obtain ⟨N, hN, g, hg⟩ := hden a
    have h1 : ρ (N • a) x = φ (embK c τ (N • a)) • x := by
      rw [← hg]
      have e1 := aeval_algHom_apply ρ.toIntAlgHom α g
      have e2 := aeval_algHom_apply (embK c τ).toIntAlgHom α g
      change ρ (aeval α g) x = φ (embK c τ (aeval α g)) • x
      rw [← show aeval A g = ρ (aeval α g) from e1, ← show aeval (lam τ) g = embK c τ (aeval α g) from e2,
        ← hev_int, heig _ _ hx, eval_map, ← algebraMap_int_eq, ← aeval_def]
    have hu : IsUnit (N : R) := by
      rw [← map_intCast φ]
      exact (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hN)).map φ
    rw [map_zsmul, map_zsmul, map_zsmul, LinearMap.smul_apply, ← Int.cast_smul_eq_zsmul R,
      ← Int.cast_smul_eq_zsmul R, smul_assoc] at h1
    exact hu.smul_left_cancel.mp h1
  refine ⟨fun τ => P τ v, ⟨fun τ a => hall τ _ (hPeig τ v) a, ?_⟩, ?_⟩
  · show ∑ τ, P τ v = v
    rw [← LinearMap.sum_apply, hsum, Module.End.one_apply]
  · rintro w ⟨hw, hws⟩
    funext τ
    show w τ = P τ v
    rw [← hws, map_sum, Finset.sum_eq_single τ]
    · rw [heig (lam τ) _ (hw τ α), Lagrange.eval_basis_self hlinj.injOn (Finset.mem_univ τ), map_one, one_smul]
    · intro τ' _ hne
      rw [heig (lam τ') _ (hw τ' α), Lagrange.eval_basis_of_ne (Ne.symm hne) (Finset.mem_univ τ'), map_zero, zero_smul]
    · simp

end GlobalTheory.EigDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDualLatticeBaseChangeStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDualLattice_baseChange : ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K'] (φ : K →+* K') (d d' : ℕ)
  (G : Matrix (Fin d') (Fin d) K'), Function.Bijective G.mulVec → ∀ (H : Matrix (Fin d) (Fin d) K) (H' : Matrix (Fin d') (Fin d') K'),
  (∀ x y : Fin d → K, Formalism.DivisionValues.hform H' (Matrix.mulVec G fun k => φ (x k)) (Matrix.mulVec G fun k => φ (y k)) = φ (Formalism.DivisionValues.hform H x y)) →
  IsUnit H.det → ∀ A : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K A →
    Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H')
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K)))) =
    Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) ''
      ((Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K))) := by
  first | exact @GlobalTheory.Mem.DualBC.dual_baseChange | exact GlobalTheory.Mem.DualBC.dual_baseChange | (intros; apply GlobalTheory.Mem.DualBC.dual_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaLiftOfResidualTrivialStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_lift_of_residual_trivial : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ (L : IntermediateField E Ω) (ψ : G E Ω), ψ ∈ Dec (F := E) A → (∀ x ∈ L, IsIntegral ℤ x → A.valuation (ψ x - x) < 1) → ∃ ι ∈ Ine (F := E) A, ∀ x ∈ L, ι x = ψ x := by
  first | exact @GlobalTheory.InertiaLift.exists_mem_Ine_eq_on | exact GlobalTheory.InertiaLift.exists_mem_Ine_eq_on | (intros; apply GlobalTheory.InertiaLift.exists_mem_Ine_eq_on <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransvectionWeightVecExpansionStatement
section
open Matrix GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transvection_weightVec_expansion : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (i j : Fin n), i ≠ j → ∀ (μ : Fin n → ℤ) (v : ι → ℂ), IsWtVec Φ μ v → ∃ (K : ℕ) (w : ℕ → ι → ℂ), w 0 = v ∧ (∀ k : ℕ, IsWtVec Φ (μ + (k : ℤ) • (Pi.single i 1 - Pi.single j 1)) (w k)) ∧ ∀ (s : ℂ) (B : GL (Fin n) ℂ), B.val = transvection i j s → Φ B *ᵥ v = ∑ k ∈ Finset.range (K + 1), s ^ k • w k := by
  first | exact @GlobalTheory.transvection_weightVec_expansion | exact GlobalTheory.transvection_weightVec_expansion | (intros; apply GlobalTheory.transvection_weightVec_expansion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilGroupIsSemisimpleOfSemisimpleFrobStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilGroup_isSemisimple_of_semisimple_frob : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ (Weil h) V), IsSmooth ρ → ∀ φ : Weil h, deg φ = 1 → End.IsSemisimple (ρ φ) → ∀ σ : Weil h, End.IsSemisimple (ρ σ) := by
  first | exact @GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob | exact GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob | (intros; apply GlobalTheory.WeilDeligne.isSemisimple_of_isSemisimple_frob <;> assumption)
end

