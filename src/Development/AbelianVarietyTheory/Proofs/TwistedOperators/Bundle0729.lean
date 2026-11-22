import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0699
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalStabilizerDoubledVacuumEigenvalueEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0722
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairListProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LineDerivSplit

theorem pure_add₀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul₀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pure_listSum {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} (l : List ι)
    (h : ι → SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (l.map h).sum φ = (l.map fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (h i) φ).sum := by
  induction l with
  | nil => funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  | cons a l ih => simp [pure_add₀, ih]

theorem sum_listSum {α ι : Type} [AddCommMonoid α] {m : ℕ} (l : List ι) (a : Fin m → ι → α) :
    ∑ j, (l.map (a j)).sum = (l.map fun i => ∑ j, a j i).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [Finset.sum_add_distrib, ih]

theorem derivSplit : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ {ι : Type} (l : List ι) (γs : ι → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ X.J)),
    (∀ i, γs i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X) → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, (∀ t, γ t = (l.map fun i => γs i t).prod) →
    ∀ ΦD ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb, ∀ Φ₁D : (Fin n × Fin d → AF F) → ℂ,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) →
    ∃ Ψ : ι → ((Fin n × Fin d → AF F) → ℂ), (∀ i, Ψ i ∈ GlobalTheory.SquareAgree.algD M B.ψ B.emb) ∧
      (∀ i, ∀ u, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (om (γs i (Multiplicative.ofAdd t), 1) ΦD)))
        (GlobalTheory.WeilM.thetaSum F (M.co.rho B.ψ u (Ψ i))) 0) ∧ Φ₁D = (l.map Ψ).sum := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP ι l γs hγs γ hγ hprod ΦD hΦD Φ₁D hΦ₁
  have hact := GlobalTheory.T.polynomial_datum_action_of_pair hPr F E σ B n d X W M χX χW om r s r' s' hP
  choose Ds hDsP hDs using fun i => hact.1 (γs i) (hγs i)
  obtain ⟨Dγ, -, hDγ⟩ := hact.1 γ hγ
  obtain ⟨m, c, g, hg⟩ := (Submodule.mem_span_set').1 hΦD
  choose f φ hf hSB hcof hgf using fun j => (g j).2
  have hstd : ∀ j, ∀ᶠ v in Filter.cofinite,
      φ j v = Set.indicator {x : Fin n × Fin d → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} 1 := by
    intro j
    filter_upwards [hcof j, hP.good.std] with v h1 h2
    rw [h1, h2]
  have hmem : ∀ j, c j • f j ∈ M.Pol B.ψ B.emb := fun j => Submodule.smul_mem _ _ (hf j)
  have hΦ : ΦD = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c j • f j) (φ j) := by
    rw [← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgf j, pure_smul₀]
  refine ⟨fun i => ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j), fun i => ?_, fun i u => ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j _ => Submodule.subset_span ?_
    exact ⟨_, φ j, hDsP i _ (hmem j), hSB j, hcof j, rfl⟩
  · rw [hΦ]
    exact GlobalTheory.ThetaLineDerFirst.hasDerivAt_thetaSum_lineFirst hPr M B.ψ χX χW om hP.base.std hP.good hP.weil (γs i) (hγs i) m
      (fun j => c j • f j) (fun j => Ds i (c j • f j)) φ (fun j => ⟨hSB j, hcof j⟩)
      (fun j => (hDs i _ (hmem j) _).2 rfl) u
  · have hpt : ∀ x, Φ₁D x = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) x := by
      intro x
      have h2 : HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x)
          (∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) x) 0 := by
        have e : (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) =
            fun t => ∑ j, om (γ (Multiplicative.ofAdd t), 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c j • f j) (φ j)) x := by
          funext t
          rw [hΦ, map_sum, Finset.sum_apply]
        rw [e]
        have hs := HasDerivAt.sum (u := Finset.univ) fun j _ => GlobalTheory.ThetaFacInf.Fib.hasDerivAt_pure (φ j) (hSB j) (hstd j)
          ((hDγ _ (hmem j) _).2 rfl) x
        simpa [Finset.sum_fn] using hs
      exact (hΦ₁ x).unique h2
    have hadd : ∀ j, Dγ (c j • f j) = (l.map fun i => Ds i (c j • f j)).sum := fun j =>
      GlobalTheory.T.theta_pair_list_action hPr F E σ B n d X W M χX χW om r s r' s' hP l γs hγs γ hγ hprod _ (hmem j) _ _
        ((hDγ _ (hmem j) _).2 rfl) (fun i => (hDs i _ (hmem j) _).2 rfl)
    calc Φ₁D = ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Dγ (c j • f j)) (φ j) :=
          funext fun x => (hpt x).trans (Finset.sum_apply x _ _).symm
      _ = ∑ j, (l.map fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j)).sum := by
          simp only [hadd, pure_listSum]
      _ = (l.map fun i => ∑ j, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j)).sum :=
          sum_listSum l (fun j i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Ds i (c j • f j)) (φ j))

end GlobalTheory.LineDerivSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorSource
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitVacV
open GlobalTheory.DblVacSiegel

theorem siegel_eigen_eq_one_any : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), v ∉ X.T →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a'))))
      (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ r : (Fin a × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M.vac v) r → tens (evFin F v) (G.M.vac v) r ≠ 0 →
    ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → ∀ μ : ℂ,
      omd p (boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x))) =
        μ • boxFun (tens (evFin F v) (G.M.vac v) r) (fun x => star (tens (evFin F v) (G.M.vac v) r x)) → μ = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv d' dd omd hdd hW r hr h0 p hp hpd μ hμ
  obtain ⟨t, ht₀⟩ := hpd
  have ht : GlobalTheory.DblVac.matD p * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (t : Matrix (Fin a) (Fin a) (AE F E)) := ht₀
  have hF := hT.base.cm.1
  set Ψ := tens (evFin F v) (G.M.vac v) r with hΨ
  have hS := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hr.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hr.2)
  have hl := lDiag_box_ne_zero hF hr.2 h0
  have hS0 : (boxFun Ψ fun x => star (Ψ x)) ≠ 0 := fun h => hl (by rw [h, map_zero])
  have hn := norm_eq_one_of_eigen hF hW.2.1.unit hS hS0 hμ
  have hrule := hW.2.2 _ DiagForm.lDiag_adm (fun z φ hφ => by
    have e : z * (diagCols (Fin a) : Matrix _ _ (AE F E))ᵀ = Matrix.fromCols z z := by
      rw [diagCols, Matrix.transpose_fromRows, Matrix.mul_fromCols, Matrix.transpose_one, Matrix.mul_one]
    rw [e, Darboux.rho, hdd]
    exact DiagForm.lDiag_schr B.ψ _ _ hφ) p t ht _ hS
  have hvec : ∀ (g : GlobalTheory.DblVac.UD σ G.V) (s : Matrix (Fin a) (Fin a) (AE F E)),
      GlobalTheory.DblVac.matD g * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) = (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * s → ∀ z,
      (GlobalTheory.DblVac.matD g *ᵥ Sum.elim z z) ∘ Sum.inl = s *ᵥ z := fun g s hs z => by
    have e : ∀ z : Fin a → AE F E, (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) *ᵥ z = Sum.elim z z := fun z => by
      rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
    rw [← e, Matrix.mulVec_mulVec, hs, ← Matrix.mulVec_mulVec, e]
    rfl
  have ht' : GlobalTheory.DblVac.matD p⁻¹ * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) =
      (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * ((t⁻¹ : GL (Fin a) (AE F E)) : Matrix (Fin a) (Fin a) (AE F E)) := by
    have e1 : GlobalTheory.DblVac.matD p⁻¹ * GlobalTheory.DblVac.matD p = 1 := p.1.inv_mul
    calc _ = GlobalTheory.DblVac.matD p⁻¹ * ((diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (t : Matrix (Fin a) (Fin a) (AE F E))) *
          ((t⁻¹ : GL (Fin a) (AE F E)) : Matrix (Fin a) (Fin a) (AE F E)) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, t.mul_inv, Matrix.mul_one]
      _ = _ := by rw [← ht, ← Matrix.mul_assoc, e1, Matrix.one_mul]
  have hunr : ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → UnrAt (X.β / X.α) P := fun P hP => by
    have hPT : P ∉ above E (X.T : Set (Pl F)) := fun h => hv (hP ▸ (h : P.under (𝓞 F) ∈ (X.T : Set (Pl F))))
    rw [div_eq_mul_inv]
    exact (hT.chars.unrβ P hPT).mul (hT.chars.unrα P hPT).inv
  have hβ : (X.β / X.α) (Matrix.GeneralLinearGroup.det t) = 1 := by
    refine GlobalTheory.DblVacSiegelAny.chr_det_eq_one_any (v := v) G.V hT.geo.hV.lat hunr t (fun u hu => ?_) fun z hz => ?_
    · have e1 : (GlobalTheory.DblVac.matD p - 1) * (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) =
          (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * ((t : Matrix (Fin a) (Fin a) (AE F E)) - 1) := by
        rw [Matrix.sub_mul, Matrix.mul_sub, ht, Matrix.one_mul, Matrix.mul_one]
      have e2 : (diagCols (Fin a) : Matrix (Fin a ⊕ Fin a) (Fin a) (AE F E)) * (u • ((t : Matrix (Fin a) (Fin a) (AE F E)) - 1)) = 0 := by
        rw [Matrix.mul_smul, ← e1, ← Matrix.smul_mul, hp.1 u hu, Matrix.zero_mul]
      rw [diagCols, Matrix.fromRows_mul, Matrix.one_mul] at e2
      ext i j
      exact congrFun (congrFun e2 (Sum.inl i)) j
    · have hz' := hp.2 (Sum.elim z z) ⟨hz, hz⟩
      exact ⟨hvec p _ ht z ▸ hz'.1.1, hvec p⁻¹ _ ht' z ▸ hz'.2.1⟩
  rw [hμ, map_smul, smul_eq_mul, hβ, Circle.coe_one, one_mul] at hrule
  have hμ' := mul_right_cancel₀ hl hrule
  rw [hμ', Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hn
  rw [hμ', hn, Complex.ofReal_one]

theorem eigen_eq_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ c : ℂ, Acts (evFin F v) (om (k, 1)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd k hk c hc
  obtain ⟨d', hd', -, dd, omd, hdc, hsp, hbox⟩ := hT.weil.2.1
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  let H : Subgroup (GlobalTheory.DblVac.UD σ G.V) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.V v, p ∈ GlobalTheory.DblVac.PDiag σ G.V → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.vacuum_split_place_indicator_base hP F E σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd d' hd' dd omd hdc hsp r hr p hp
    have h1 := siegel_eigen_eq_one_any F E σ B a a' G X om om' hT v hv d' dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.V v, q ∈ GlobalTheory.DblVac.PAnti σ G.V → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.V v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.vacuum_split_place_indicator_base hP F E σ B a a' G X om om' hT v hsp₀ hv hψ htwo hstd d' hd' dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.V v k hk
  have hfix : omd gd S = S :=
    GlobalTheory.T.split_place_diagonal_stabilizer_generated_hermitian_doubling σ B G.V _ _ hT.base hT.geo.hV v hsp₀ hψ htwo H hD hA gd hgdK
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inl _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inl_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hcS : c • S = S := by
    calc c • S = boxFun (c • V₀) (fun x => star (V₀ x)) := by
          funext x
          simp [hS, boxFun, mul_assoc]
      _ = omd gd S := hb.symm
      _ = S := hfix
  obtain ⟨x, hx⟩ := hS0
  have := congrFun hcS x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx (this.trans (one_mul _).symm)

end GlobalTheory.SplitVacV

end
end

