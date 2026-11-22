import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0518
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffZeroEqZeroIff
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.PinPlace

theorem mem_mul_iff {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (y : K) :
    (∃ a : R, y = algebraMap R K (ϖ * a)) ↔ y = 0 ∨ y⁻¹ ∉ (algebraMap R K).range := by
  have hinj := IsFractionRing.injective R K
  constructor
  · rintro ⟨a, rfl⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, b, hb⟩ := hc
    have h1 : ϖ * a * b = 1 := hinj (by rw [map_mul, hb, mul_inv_cancel₀ h0, map_one])
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a * b) (by rw [← mul_assoc, h1]))
  · rintro (rfl | h)
    · exact ⟨0, by simp⟩
    · rcases ValuationRing.isInteger_or_isInteger R y with ⟨b, rfl⟩ | hb
      · have hb : ¬ IsUnit b := by
          rintro ⟨u, rfl⟩
          refine h ⟨(u⁻¹ : Rˣ), ?_⟩
          exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
        have hm : b ∈ IsLocalRing.maximalIdeal R := hb
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
        obtain ⟨a, rfl⟩ := hm
        exact ⟨a, rfl⟩
      · exact absurd hb h

variable {D : D7} {p : ℕ} [Fact p.Prime] {la : PlL D p} {jc : DV.KW p →+* ℂ}

theorem mem_range_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    y ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ↔
      la.1.valuation D.what₂.LL z ≤ 1 := by
  obtain ⟨W, h1, h2⟩ := h
  rw [← h2, hyz, h1]

theorem mem_pW_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    (∃ a : WittVector p (AlgebraicClosure (ZMod p)),
        y = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
      la.1.valuation D.what₂.LL z < 1 := by
  rw [mem_mul_iff (WittVector.irreducible p) y,
    mem_range_iff h (y := y⁻¹) (z := z⁻¹) (by rw [map_inv₀, map_inv₀, hyz])]
  have h0 : y = 0 ↔ z = 0 := by
    rw [← map_eq_zero_iff jc jc.injective, hyz, map_eq_zero_iff _ D.what₂.embLL.injective]
  rw [h0, map_inv₀, not_le]
  by_cases hz : z = 0
  · simp [hz]
  · have hv : 0 < la.1.valuation D.what₂.LL z := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz)
    rw [one_lt_inv₀ hv]
    simp [hz]

theorem pinned_reads_place : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) →
    ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p) (τ : DV.Emb D p) (e : D.host.E →+* D.what₂.LL),
      (jC p la).comp τ = D.what₂.embLL.comp e → ∀ x : 𝓞 D.host.E,
        τ x ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ∧
        ((∃ a : WittVector p (AlgebraicClosure (ZMod p)),
            τ x = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
          la.1.valuation D.what₂.LL (e x) < 1) ∧
        (la.1.valuation D.what₂.LL (e x) < 1 ↔ RingOfIntegers.mapRingHom e x ∈ la.1.asIdeal) := by
  intro D jC h p _ la τ e hτ x
  have hx : jC p la (τ x) = D.what₂.embLL (e x) := RingHom.congr_fun hτ (x : D.host.E)
  have he : e x = algebraMap (𝓞 D.what₂.LL) D.what₂.LL (RingOfIntegers.mapRingHom e x) := rfl
  refine ⟨(mem_range_iff (h p la) hx).2 ?_, mem_pW_iff (h p la) hx, ?_⟩
  · rw [he]; exact la.1.valuation_le_one _
  · rw [he]; exact la.1.valuation_lt_one_iff_mem _

theorem coeff_zero_eq_zero_iff {k : Type} [Field k] [CharP k p] [PerfectRing k p] (b : WittVector p k) :
    b.coeff 0 = 0 ↔ ∃ a : WittVector p k, b = p * a := by
  constructor
  · intro h0
    have hb : ¬ IsUnit b := by
      rintro ⟨u, rfl⟩
      have h1 := congrArg (fun w : WittVector p k => w.coeff 0) u.mul_inv
      simp only [WittVector.mul_coeff_zero, WittVector.one_coeff_zero] at h1
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    have hm : b ∈ IsLocalRing.maximalIdeal (WittVector p k) := hb
    rw [(WittVector.irreducible p).maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨a, rfl⟩ := hm
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [WittVector.mul_coeff_zero]
    have : ((p : WittVector p k)).coeff 0 = 0 := by simp
    rw [this, zero_mul]

theorem pinned_tiedFor : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) → Formalism.L2.Geo.ComplexEmbeddingsCompatible jC := by
  intro D jC h p _ la τ e hτ x
  obtain ⟨-, h2, -⟩ := pinned_reads_place D jC h p la τ e hτ x
  rw [← h2]
  constructor
  · rintro ⟨b, hb, h0⟩
    obtain ⟨a, rfl⟩ := (coeff_zero_eq_zero_iff b).1 h0
    exact ⟨a, hb.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨p * a, ha.symm, (coeff_zero_eq_zero_iff _).2 ⟨a, rfl⟩⟩

end GlobalTheory.ShFam.PinPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivial
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FreeOnDomain

theorem exists_conj_first_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ P B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, P.det ≠ 0 ∧ (∀ a : Fin n, B a.succ 0 = 0) ∧ A * P = P * B := by
  first
  | exact @_root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero
  | exact _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero
  | (apply _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> assumption)
  | (intros; apply _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero ..)

theorem exists_conj_triangular (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ P T : Matrix (Fin n) (Fin n) ℂ, P.det ≠ 0 ∧ (∀ a c, c < a → T a c = 0) ∧ A * P = P * T := by
  induction n with
  | zero => exact ⟨1, 1, by simp, fun a => a.elim0, Subsingleton.elim _ _⟩
  | succ n ih =>
    obtain ⟨P, B, hP, hB, e⟩ := exists_conj_first_col A
    obtain ⟨Q, T, hQ, hT, e'⟩ := ih (B.submatrix Fin.succ Fin.succ)
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      of (Fin.cons (Fin.cons 1 fun _ => 0) fun a => Fin.cons 0 (Q a))
    let T' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      of (Fin.cons ((B * D) 0) fun a => Fin.cons 0 (T a))
    have hD : D.det = Q.det := by
      rw [det_succ_row_zero, Fin.sum_univ_succ]
      simp only [D, of_apply, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      rfl
    have hBD : B * D = D * T' := by
      ext a c
      refine Fin.cases ?_ (fun a => ?_) a
      · rw [mul_apply (M := D), Fin.sum_univ_succ]
        simp [D, T']
      · refine Fin.cases ?_ (fun c => ?_) c
        · simp [D, T', mul_apply, Fin.sum_univ_succ, hB]
        · have := congrFun (congrFun e' a) c
          simpa [D, T', mul_apply, Fin.sum_univ_succ] using this
    refine ⟨P * D, T', ?_, fun a c h => ?_, ?_⟩
    · rw [det_mul, hD]; exact mul_ne_zero hP hQ
    · revert h
      refine Fin.cases ?_ (fun a => ?_) a
      · intro h; exact absurd h (by simp)
      · refine Fin.cases ?_ (fun c => ?_) c
        · intro _; simp [T']
        · intro h; simpa [T'] using hT a c (Fin.succ_lt_succ_iff.1 h)
    · rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, hBD, Matrix.mul_assoc]

theorem toBlocks₁₂_eq_zero {p q : ℕ} {F F' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hF : IsUnit F.det)
    (h2 : IsUnit F.toBlocks₂₂.det) (h2' : IsUnit F'.toBlocks₂₂.det) (h : moeb F' 0 = moeb F 0) :
    (F⁻¹ * F').toBlocks₁₂ = 0 := by
  rw [moeb_zero, moeb_zero] at h
  have h1 : F'.toBlocks₁₂ = F.toBlocks₁₂ * (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    rw [← Matrix.mul_assoc, ← h, nonsing_inv_mul_cancel_right _ _ h2']
  have e : F' * fromBlocks 0 0 0 1 =
      F * fromBlocks (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    conv_lhs => rw [← fromBlocks_toBlocks F']
    conv_rhs => enter [1]; rw [← fromBlocks_toBlocks F]
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, ← h1, mul_nonsing_inv_cancel_left _ _ h2]
  have e2 : (F⁻¹ * F') * fromBlocks 0 0 0 1 =
      fromBlocks (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    rw [Matrix.mul_assoc, e, nonsing_inv_mul_cancel_left _ _ hF]
  rw [← fromBlocks_toBlocks (F⁻¹ * F'), fromBlocks_multiply] at e2
  simpa using congrArg toBlocks₁₂ e2

theorem exists_conj_block {r j : ℕ} (hj : j ≤ r) (M : Matrix (Fin r) (Fin r) ℂ)
    (hM : (reindex (idx hj) (idx hj) M).toBlocks₁₂ = 0) :
    ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧ (∀ a c : Fin r, (c : ℕ) < r - j → ¬ (a : ℕ) < r - j → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ M * b = b * t := by
  set G := reindex (idx hj) (idx hj) M with hG
  obtain ⟨P, T, hP, hT, e⟩ := exists_conj_triangular _ G.toBlocks₁₁
  obtain ⟨Q, S, hQ, hS, e'⟩ := exists_conj_triangular _ G.toBlocks₂₂
  have hm : G * fromBlocks P 0 0 Q = fromBlocks P 0 0 Q * fromBlocks T 0 (Q⁻¹ * (G.toBlocks₂₁ * P)) S := by
    conv_lhs => rw [← fromBlocks_toBlocks G, hM]
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e, e', mul_nonsing_inv_cancel_left _ _ hQ.isUnit]
  refine ⟨(fromBlocks P 0 0 Q).submatrix (idx hj) (idx hj),
    (fromBlocks T 0 (Q⁻¹ * (G.toBlocks₂₁ * P)) S).submatrix (idx hj) (idx hj), ?_, fun a c hc ha => ?_,
    fun a c h => ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; exact mul_ne_zero hP hQ
  · obtain ⟨a, rfl⟩ := (idx hj).symm.surjective a
    obtain ⟨c, rfl⟩ := (idx hj).symm.surjective c
    rcases a with a | a <;> rcases c with c | c
    · rw [idx_symm_inl] at hc; omega
    · simp
    · simp
    · rw [idx_symm_inr] at ha; exact absurd a.2 ha
  · obtain ⟨a, rfl⟩ := (idx hj).symm.surjective a
    obtain ⟨c, rfl⟩ := (idx hj).symm.surjective c
    rw [Fin.lt_def] at h
    rcases a with a | a <;> rcases c with c | c
    · rw [idx_symm_inl, idx_symm_inl] at h
      simpa using hT a c (by rw [Fin.lt_def]; omega)
    · simp
    · rw [idx_symm_inl, idx_symm_inr] at h
      have := a.2; omega
    · rw [idx_symm_inr, idx_symm_inr] at h
      simpa using hS a c h
  · have : M = G.submatrix (idx hj) (idx hj) := by simp [hG]
    rw [submatrix_mul_equiv, ← hm, ← submatrix_mul_equiv _ _ _ (idx hj), ← this]

theorem eq_one_of_domPt_lact_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1 := by
  intro E _ _ _ r j X hj Tau _ κ hp γ hγ x hx h
  obtain ⟨x, ho, b₀, hb₀, rfl⟩ := ortho_holds r X x hx
  rw [KU.lact_rmul', domPt_rmul X hj κ hb₀, domPt_rmul X hj κ hb₀] at h
  have hx := IC.orth_mem_dom X ho
  have hx' := IC.orth_mem_dom X (KU.isOrth_lact X hγ ho)
  have key : ∀ τ : X.Ψ, ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧
      (∀ a c : Fin r, (c : ℕ) < r - j → ¬ (a : ℕ) < r - j → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ (mat x τ)⁻¹ * mat (lact γ x) τ * b = b * t := by
    intro τ
    refine exists_conj_block hj _ ?_
    obtain ⟨s, rfl⟩ := κ.surjective τ
    have u0 : IsUnit (mat (x0F X) (κ s)).det := (det_x0F X _).isUnit
    have hF : IsUnit (frameCo X hj x (κ s)).det := by
      rw [frameCo, det_reindex_self, det_mul]
      exact (isUnit_nonsing_inv_det _ u0).mul (hx _).1.isUnit
    have := toBlocks₁₂_eq_zero hF (frameCo_isUnit₂₂ X hj hp hx _) (frameCo_isUnit₂₂ X hj hp hx' _) (congrFun h s)
    rw [frameCo, frameCo, inv_reindex, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ u0] at this
    simp only [reindex_apply, submatrix_mul_equiv] at this ⊢
    rwa [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ u0] at this
  choose b t hb hb0 ht e using key
  have e' : ∀ τ, mat (lact γ x) τ * b τ = mat x τ * b τ * t τ := fun τ => by
    rw [Matrix.mul_assoc, ← e, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (hx τ).1.isUnit]
  refine X.Γ_free γ hγ (rmul x fun τ => b τ)
    (GlobalTheory.PointOfFrames.rmul_mem_dom X hx _ hb (by rw [hp]; exact hb0)) (fun τ => t τ) (fun τ => ⟨?_, ht τ⟩) ?_
  · intro h0
    have h1 := congrArg det (e' τ)
    have h0' : (t τ).det = 0 := h0
    rw [det_mul, det_mul, h0', mul_zero] at h1
    exact mul_ne_zero (hx' τ).1 (hb τ) h1
  · exact (KU.lact_rmul' X γ x _).trans (funext e')

end GlobalTheory.FreeOnDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBelowOfRange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Untw

theorem exists_below_of_range (D D' : D7) (h : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (v' : D'.what₂.places.Pl) :
    ∃ v : D.what₂.places.Pl, Below D D' v v' := by
  first
  | exact @_root_.GlobalTheory.PrimeBelow.exists_below
  | exact _root_.GlobalTheory.PrimeBelow.exists_below
  | (apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeBelow.exists_below <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeBelow.exists_below ..)

theorem resChar_of_below {D D' : D7} {v : D.what₂.places.Pl} {v' : D'.what₂.places.Pl} (hB : Below D D' v v') :
    D'.what₂.places.resChar v' = D.what₂.places.resChar v := by
  refine GlobalTheory.LvT.Inh.resChar_eq_of_mem_plEq D' v' (D.what₂.places.resChar_prime v) ((hB _ _ ?_).1 (GlobalTheory.LvT.Inh.resChar_mem_plEq D v))
  simp only [map_natCast]

end GlobalTheory.Mem.R3.Rw.Untw

namespace GlobalTheory.Mem.R3.Rw

theorem stepW_seed (h : SeedBd) : StepW Pinned fun K B f T _ =>
    (↑(NonzeroPlacesOverPrimes.forcedContentSupportPrimes K B.toPre) : Set ℕ) ⊆ ↑T.pl ∧ ∀ px : PreX B.toPre,
      SeedW K B.toPre f B.KsC B.fixedCoefficientFieldInComplex px Set.univ ⊤ → SeedW K B.toPre f B.KsC B.fixedCoefficientFieldInComplex px ↑T.pl B.LLC := by
  refine EvG.imp h fun K _ _ _ _ H => ?_
  choose S S₂ hS₂ hS using H
  refine ⟨fun _ _ _ => ∅, fun P f F F₀ => S P f F F₀ ∪ NonzeroPlacesOverPrimes.forcedContentSupportPrimes K P, fun _ _ _ _ _ => ∅,
    fun P f F F₀ _ => S₂ P f F F₀, by simp, fun P f F F₀ _ => hS₂ P f F F₀, ?_⟩
  intro B f T _ hHas hP _ _ _ _ w _
  refine ⟨fun p hp => hP (Finset.mem_union_right _ hp), fun px hs => (hS _ _ _ _ px hs).mono ?_ ?_⟩
  · intro p hp
    exact hP (Finset.mem_union_left _ hp)
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact hHas.2 z hz

theorem datGood_of_untw : GlobalTheory.Published.GreenCuspidal → DatExS → LowerUnitaryCaseCondition → DatExt →
    StepW Pinned fun K B f T w => T = TwDat.untw B T.pl → DatGood K B f T w := by
  intro hG hDS hHL hDE
  have hP : StepW Pinned Pinned := StepW.of_all fun _ _ _ _ _ _ _ h => h
  have hHLw : StepW Pinned fun K B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
      (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → z.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z.geo →
      HoldsL z.R z.F := hHL
  refine (((((hP.and hDS).and hHLw).and hDE).and GlobalTheory.T.exists_GJStage_GIs2_pinned).and (stepW_seed Resize.seeds_uniform)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  obtain ⟨⟨⟨⟨⟨⟨pin⟩, hDS'⟩, hHL'⟩, hDE'⟩, G, hG2⟩, hf0, hsd⟩ := H
  intro hT
  obtain ⟨Z, rfl, hGT, hGA, hKap⟩ := exists_lt_grpTrue hG w hO pin.hX G
  have hVol := (hG2 Z.W Z.V Z.S Z.N).1
  obtain ⟨z₁, hF₁⟩ := hDS' Z pin.hX hGT hGA hVol
  have hL₁ := hHL' Z pin.hX _ z₁ hGT hGA hF₁.1 hF₁.2.1
  have hs : SeedW K B.toPre f B.KsC B.fixedCoefficientFieldInComplex w.px Set.univ ⊤ :=
    ⟨B, f, T, w, Z, pin.hX, _, z₁, rfl, HEq.rfl, rfl, rfl, HEq.rfl, ⟨pin⟩, hGT, hGA, hF₁, hL₁, fun _ _ => trivial, le_top⟩
  obtain ⟨B₀, f₀, T₀, w₀, Z₀, hX₀, Wt₀, z₀, hB₀, hf₀, hKs, hL0, hpx, hpin₀, hGT₀, hGA₀, hFine₀, hHL₀, hW₀, hLL⟩ := hsd w.px hs
  have hE : Enl B₀ B := enl_of_fields hB₀ hKs hL0 hLL
  obtain ⟨z', hFine', hExt⟩ := hDE' B₀ f₀ T₀ w₀ hE hf₀.symm hpin₀ hpx.symm Z₀ hX₀ Wt₀ z₀ hGT₀ hGA₀ hFine₀ hHL₀ Z pin.hX hGT hGA hVol
  refine ⟨Z, pin.hX, z', hG2, hGT, hGA, hKap, hFine'.1, hFine'.2.1, hFine'.2.2.1, hFine'.2.2.2, ?_, ?_⟩
  · intro v' hv'
    rcases (Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').1 hv' with h | h
    · obtain ⟨v, hB⟩ := Untw.exists_below_of_range (w₀.D Z₀) (w.D Z) hE.2.2.2 v'
      have hv : v ∈ z₀.W1 (fun _ _ => 0) := (hExt.W1 v v' hB).2 ((Dat.mem_auxiliaryPlaces_iff_three_parts z' _ v').2 (Or.inl h))
      have hr : B.places.resChar v' = B₀.places.resChar v := Untw.resChar_of_below hB
      have hm : B₀.places.resChar v ∈ (T.pl : Set ℕ) := hW₀ v hv
      rw [hr]
      exact hm
    · exact hf0 (NonzeroPlacesOverPrimes.resChar_mem_f0Primes K B f T w Z v' h)
  · intro v _
    have e := congrArg (fun T' : TwDat B => T'.psi v) hT
    exact e.trans rfl

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
section
noncomputable section

namespace GlobalTheory.UnifComp

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
  GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem ptF_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (h : FrMap φ y z) :
    ptF z = spMap φ.toRingHom ≫ ptF y := by
  apply pullback.hom_ext
  · rw [ptF, pullback.lift_fst, Category.assoc, ptF, pullback.lift_fst, h.1]
  · rw [ptF, pullback.lift_snd, Category.assoc, ptF, pullback.lift_snd, ← Spec.map_comp]
    congr 1
    ext a
    exact (φ.commutes a).symm

theorem ptF_frBor {S : Type} [CommRing S] [Algebra c.F S] {t : Ix Dw → Sˣ} {y z : FrPt Xo c S}
    (h : FrBor t y z) : ptF z = ptF y := by
  apply pullback.hom_ext
  · rw [ptF, pullback.lift_fst, ptF, pullback.lift_fst, h.1]
  · rw [ptF, pullback.lift_snd, ptF, pullback.lift_snd]

theorem liesOn_chart {h : GenFrEx Xo c} (C : GlobalTheory.Reg.FChart h) : LiesOn C.Z C.y := by
  intro s
  let η : Sp C.R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum C.R)
  let s₀ : Sp (Om C.Z) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Om C.Z))
  have e : spMap C.R.val.toRingHom s₀ = η :=
    PrimeSpectrum.ext (Ideal.comap_bot_of_injective C.R.val.toRingHom Subtype.val_injective)
  have h1 : ptF C.y η ∈ (C.Z : Set (Xo.XF c)) := by
    have := liesOn_genFr h C.Z s₀
    rw [← ptF_frBor C.bor, ptF_frMap C.gen, Scheme.Hom.comp_apply, e] at this
    exact this
  have h2 : η ⤳ s := (PrimeSpectrum.le_iff_specializes (R := C.R) _ _).1 bot_le
  exact (h2.map (ptF C.y).continuous).mem_closed (isClosed_of_mem_irreducibleComponents _ C.Z.2) h1

theorem exists_liesOn {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hU : Formalism.L2.PjFree.IsUnf U)
    (k : U.Comp) : ∃ Z : Comp Xo c, ∀ x : (U.X k).dom, LiesOn Z (U.un k x) := by
  obtain ⟨-, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneComp.exists_comp_of_charts E H Dw l Xo c σ r U hU h k
  refine ⟨Z, fun x s => ?_⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) (U.un k x)
  rw [← hZ x C ψ z t hz hb, ptF_frBor hb, ptF_frMap hz, Scheme.Hom.comp_apply]
  exact liesOn_chart C _

theorem eq_of_carries {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} {h : GenFrEx Xo c} {k : U.Comp}
    {Z Z' : Comp Xo c} (hk : GlobalTheory.CompModel.CarriesGeneric U h k Z) (h' : ∀ x : (U.X k).dom, LiesOn Z' (U.un k x)) :
    Z' = Z := by
  obtain ⟨P, w, x, t, hw, ht⟩ := hk
  by_contra hne
  let s : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z' Z hne) (h' x s) ?_
  rw [← ptF_frBor ht, ptF_frMap hw, Scheme.Hom.comp_apply]
  exact liesOn_genFr h Z _

theorem exists_equiv_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k, (U.X k).dom.Nonempty) → FnAlgClosed Xo c → ∃ q : U.Comp ≃ Comp Xo c, ∀ k (x : (U.X k).dom) (s : Sp (CAt σ)), GlobalTheory.AllWt.ptF (U.un k x) s ∈ (q k).1 := by
  intro E _ _ _ H Dw l Xo c σ N U hσ hU _ hF
  obtain ⟨-, -, h, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  choose q hq using exists_liesOn U hU
  refine ⟨Equiv.ofBijective q ⟨fun k k' e => ?_, fun Z => ?_⟩, fun k x s => hq k x s⟩
  · obtain ⟨Z, hZ⟩ := GlobalTheory.CompModel.exists_comp U hσ hU h k
    obtain ⟨Z', hZ'⟩ := GlobalTheory.CompModel.exists_comp U hσ hU h k'
    obtain rfl : Z = Z' := (eq_of_carries hZ (hq k)).symm.trans (e.trans (eq_of_carries hZ' (hq k')))
    obtain ⟨P, w, x, t, hw, ht⟩ := hZ
    obtain ⟨P', w', x', t', hw', ht'⟩ := hZ'
    exact GlobalTheory.GeomConn.comp_eq_of_fnAlgClosed E H Dw l Xo c σ N U.toPj hσ hU hF h Z k k' x x'
      ⟨P, w, t, hw, ht⟩ ⟨P', w', t', hw', ht'⟩
  · obtain ⟨k, hk⟩ := GlobalTheory.CompModel.exists_model U hU h Z
    exact ⟨k, eq_of_carries hk (hq k)⟩

end GlobalTheory.UnifComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT

namespace GlobalTheory.KeyFourth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def Tied {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (s : LB.Sec (PPx x)) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (Φ : FibKey Xo S x) : Prop :=
  SecTie Φ.m Φ.th s ∧ ∃ hg : Φ.T.g = g, ∀ i : Fin Φ.T.g,
    (Φ.v i).left ≫ Φ.m.φ = u (e (i.cast hg)).1 (e (i.cast hg)).2

def kch {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : Sˣ := ∏ i, t i ^ keyEx Dw i

theorem kch_mul {S : Type} [CommRing S] (t t' : Ix Dw → Sˣ) : kch (t * t') = kch t * kch t' := by
  simp only [kch, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem kch_inv {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : kch t⁻¹ = (kch t)⁻¹ := by
  simp only [kch, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem kch_eq {S : Type} [CommRing S] (t : Ix Dw → Sˣ) :
    kch t = (∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t (some x)) * (t none ^ 2)⁻¹ := by
  rw [kch, Fintype.prod_option, mul_comm]
  simp only [keyEx, zpow_one, zpow_neg]
  rfl

def RootVal {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (y : FrPt Xo c (CAt σ)) (v : ℂ) : Prop :=
  ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un k x) y ∧
    v = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ)

end GlobalTheory.KeyFourth
end
end

