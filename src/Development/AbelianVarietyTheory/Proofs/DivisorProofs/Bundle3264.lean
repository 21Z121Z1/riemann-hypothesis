import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3250
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3248
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3249
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1633
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefL2LeSupOfLinIndep
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped ComplexOrder
namespace GlobalTheory.HSAmp

theorem gram_posDef_and_l2_le_sup_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (ι : Type) [Fintype ι] [DecidableEq ι] (f : ι → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → IsFam (fun σ => (ω σ).meas) (vals P a b f) ∧ (gram (fun σ => (ω σ).meas) (vals P a b f)).PosDef ∧ ∀ (c : ι → ℂ) (M : ℝ), (∀ σ y, cmb (vals P a b f) c σ y ≤ M) → l2 (fun σ => (ω σ).meas) (vals P a b f) c ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * M := by
  intro k _ X _ p D hX hG P ω a b ι _ _ f hf hli
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  have hfin := fun σ => GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos k X p D hX hG σ (ω σ)
  obtain ⟨hprod, hnu⟩ := GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P a b
  have hfam : IsFam (fun σ => (ω σ).meas) (vals P a b f) := by
    refine ⟨inferInstance, fun σ i j => ?_⟩
    haveI := (hfin σ).1
    obtain ⟨C₁, hC₁⟩ := (hnu (f i) (hf i)).2
    obtain ⟨C₂, hC₂⟩ := (hnu (f j) (hf j)).2
    refine Integrable.of_bound (hprod σ _ (hf i) _ (hf j)).aestronglyMeasurable (C₁ * C₂)
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 : 0 ≤ P.nu a b σ y (f j) := (norm_val P a b σ y (f j)) ▸ norm_nonneg _
    simp only [vals, norm_mul, Complex.norm_conj, norm_val]
    exact mul_le_mul (hC₁ σ y) (hC₂ σ y) h0 (le_trans ((norm_val P a b σ y (f i)) ▸ norm_nonneg _) (hC₁ σ y))
  have hl2 := gram_isHermitian_and_l2_eq_quadratic_form (S := k →+* ℂ) (Y := fun σ => CxPts p σ) (ι := ι) (fun σ => (ω σ).meas) (vals P a b f) hfam
  have hcont : ∀ (c : ι → ℂ) σ, Continuous (cmb (vals P a b f) c σ) := by
    intro c σ
    have e : cmb (vals P a b f) c σ = fun y => (∑ i, ∑ j, (c i * (starRingEnd ℂ) (c j)) *
        (vals P a b f σ y i * (starRingEnd ℂ) (vals P a b f σ y j))).re := by
      funext y
      have h1 := Complex.mul_conj' (∑ i, c i * vals P a b f σ y i)
      rw [map_sum, Finset.sum_mul_sum] at h1
      simp only [cmb]
      rw [← Complex.ofReal_re (‖_‖ ^ 2), Complex.ofReal_pow, ← h1]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul]; ring
    rw [e]
    exact Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (hprod σ _ (hf i) _ (hf j)))
  haveI : Fintype (k →+* ℂ) := Fintype.ofFinite _
  refine ⟨hfam, GlobalTheory.T.gram_posDef_of_l2_definite (k →+* ℂ) (fun σ => CxPts p σ) ι (fun σ => (ω σ).meas) (vals P a b f) hfam
    fun c hc => ?_, fun c M hM => ?_⟩
  · rw [l2, finsum_eq_sum_of_fintype] at hc
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun σ _ =>
      integral_nonneg fun y => sq_nonneg ‖∑ i, c i * vals P a b f σ y i‖).1 hc
    refine GlobalTheory.T.linearIndependent_complex_sectionValues_of_int k X p D hX P a b ι f hf hli c fun σ y => ?_
    haveI := (hfin σ).2
    have hae := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg ‖∑ i, c i * vals P a b f σ y i‖)
      ((hl2.2 c).1 σ)).1 (hz σ (Finset.mem_univ _))
    have hall := (Continuous.ae_eq_iff_eq _ (hcont c σ) continuous_const).1 hae
    have hy : ‖∑ i, c i * vals P a b f σ y i‖ ^ 2 = 0 := congrFun hall y
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hy)
  · rw [l2, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_mul]
    refine Finset.sum_le_sum fun σ _ => ?_
    haveI := (hfin σ).1
    calc ∫ y, cmb (vals P a b f) c σ y ∂(ω σ).meas ≤ ∫ _y, M ∂(ω σ).meas :=
          integral_mono ((hl2.2 c).1 σ) (integrable_const M) fun y => hM σ y
      _ = ((ω σ).meas Set.univ).toReal * M := by
          rw [integral_const, smul_eq_mul, measureReal_def]

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckExistenceClosedSubschemesSeparatedStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grothendieck_existence_closedSubschemes_separated : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isSeparated | exact GlobalTheory.FormalAlg.alg_of_isSeparated | (intros; apply GlobalTheory.FormalAlg.alg_of_isSeparated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLevelForgettingFiniteEtaleSurjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_levelForgetting_finite_etale_surjective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N N' : ℕ) (hd : N ∣ N') (hc : N'.Coprime p), 3 ≤ N → ∀ (M : Model b N) (M' : Model b N') (t : M'.X ⟶ M.X), t ≫ M.s = M'.s → Nonempty (ObjMap (M'.univ.forget N hd hc) M.univ t) → IsFinite t ∧ Etale t ∧ Surjective t := by
  first | exact @GlobalTheory.UPel.HT.forget_map_finite_etale_surjective | exact GlobalTheory.UPel.HT.forget_map_finite_etale_surjective | (intros; apply GlobalTheory.UPel.HT.forget_map_finite_etale_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsWeightEqFinrankMulStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_forms_weight_eq_finrank_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = (Module.finrank ℂ (GlobalTheory.BCT.TrKer.Wsp lam) : ℂ) * trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) := by
  first | exact @GlobalTheory.BCT.TrKer.trOn_forms_eq_finrank_mul | exact GlobalTheory.BCT.TrKer.trOn_forms_eq_finrank_mul | (intros; apply GlobalTheory.BCT.TrKer.trOn_forms_eq_finrank_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFamilyWeierstrassTwistStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_family_weierstrass_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (y : Fin 2 → ZMod N) (κ : Emb F → ℕ), IsFam (gact N 1) (wt (2 * s) κ : ℕ) (fun α ↦ hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  first | exact @GlobalTheory.HilbFam.isFam_hfun_GL | exact GlobalTheory.HilbFam.isFam_hfun_GL | (intros; apply GlobalTheory.HilbFam.isFam_hfun_GL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMorseSectionsMLAddAUniform
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.Morse

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem cmb_eq_frame (P : Pair p) (m : ℕ) {ι : Type} [Fintype ι] (f : ι → X.functionField)
    (hf : ∀ l, f l ∈ P.H m 1) (c : ι → ℂ) (σ : k →+* ℂ) (y : CxPts p σ) (i : P.L.B.ι) (j : P.A.B.ι)
    (hi : y ∈ ptsIn p σ (P.L.B.U i)) (hj : y ∈ ptsIn p σ (P.A.B.U j)) :
    cmb (vals P m 1 f) c σ y = ‖∑ l, c l * ratVal (P.loc m 1 (f l) i j) y‖ ^ 2 *
      Real.exp (-((m : ℝ) * (P.L.φ σ).φ i y)) * Real.exp (-(P.A.φ σ).φ j y) := by
  obtain ⟨θ, hθ, h⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P m 1 σ y i j hi hj
  have e : ∑ l, c l * vals P m 1 f σ y l = θ * ((∑ l, c l * ratVal (P.loc m 1 (f l) i j) y) *
      (Real.exp (-(((m : ℤ) : ℝ) * (P.L.φ σ).φ i y + ((1 : ℤ) : ℝ) * (P.A.φ σ).φ j y) / 2) : ℝ)) := by
    simp only [vals, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h _ (hf l)]
    ring
  rw [cmb, e, norm_mul, hθ, one_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    mul_pow, sq (Real.exp _), ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem continuous_cmb {D : ℕ} (hX : IsArithVar p D) (P : Pair p) (m : ℕ) {ι : Type} [Fintype ι]
    (f : ι → X.functionField) (hf : ∀ l, f l ∈ P.H m 1) (c : ι → ℂ) (σ : k →+* ℂ) :
    Continuous fun y => cmb (vals P m 1 f) c σ y := by
  have hp := (GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded k X p D hX P m 1).1 σ
  have e : (fun y => cmb (vals P m 1 f) c σ y) = fun y =>
      (∑ a, ∑ b, c a * (starRingEnd ℂ) (c b) *
        (val P m 1 σ y (f a) * (starRingEnd ℂ) (val P m 1 σ y (f b)))).re := by
    funext y
    rw [cmb, ← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum,
      Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [vals, map_mul]
    ring
  rw [e]
  exact Complex.continuous_re.comp (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
    continuous_const.mul (hp _ (hf a) _ (hf b)))

theorem integral_over_chart_le_l2 {D : ℕ} (hX : IsArithVar p D) (hs : GenSmooth p D) (P : Pair p) (m : ℕ) {ι : Type}
    [Fintype ι] (f : ι → X.functionField) (hf : ∀ l, f l ∈ P.H m 1) (c : ι → ℂ) (ω : ∀ σ, VolDens p σ D)
    (σ : k →+* ℂ) (C : AlgChart p σ D) (T : Set (ReciprocityTheory.L2DbarEstimates.V D)) (hT : IsOpen T) (hTt : T ⊆ C.e.target) :
    ∫ v in T, cmb (vals P m 1 f) c σ (C.e.symm v) * (ω σ).dens C (C.e.symm v) ≤
      l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  haveI := hX.compactSpace σ
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  obtain ⟨hfin, -⟩ := GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos k X p D hX hs σ (ω σ)
  have hcont := continuous_cmb hX P m f hf c σ
  set S := C.e.source ∩ C.e ⁻¹' T with hSdef
  have hSo : IsOpen S := C.e.isOpen_inter_preimage hT
  have hSs : S ⊆ C.e.source := Set.inter_subset_left
  have hST : C.e '' S = T := by
    rw [hSdef, C.e.image_source_inter_eq']
    ext v
    refine ⟨fun hv => ?_, fun hv => ⟨hTt hv, ?_⟩⟩
    · have h := hv.2
      simp only [Set.mem_preimage, C.e.right_inv hv.1] at h
      exact h
    · simp only [Set.mem_preimage, C.e.right_inv (hTt hv)]
      exact hv
  have h1 := (GlobalTheory.T.meas_integral_eq_chartDensity_integral k X p D hX σ (ω σ) C S _ hSo.measurableSet hSs hcont).2
  rw [hST] at h1
  rw [← h1]
  have hnn : ∀ σ' (y : CxPts p σ'), 0 ≤ cmb (vals P m 1 f) c σ' y := fun _ _ => by unfold cmb; positivity
  have hint : Integrable (fun y => cmb (vals P m 1 f) c σ y) (ω σ).meas :=
    integrableOn_univ.1 (hcont.continuousOn.integrableOn_compact isCompact_univ)
  calc ∫ y in S, cmb (vals P m 1 f) c σ y ∂(ω σ).meas ≤ ∫ y, cmb (vals P m 1 f) c σ y ∂(ω σ).meas :=
        setIntegral_le_integral hint (Eventually.of_forall (hnn σ))
    _ ≤ l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
        unfold l2
        exact single_le_finsum (f := fun σ' => ∫ y, cmb (vals P m 1 f) c σ' y ∂(ω σ').meas) σ (Set.toFinite _)
          fun σ' => integral_nonneg (hnn σ')

theorem local_bound {D : ℕ} (hX : IsArithVar p D) (hs : GenSmooth p D) (P : Pair p) (hP : P.L.SemiPos D)
    (ω : ∀ σ, VolDens p σ D) (ρ : ∀ σ, CxPts p σ → ℝ) (hρ : ∀ σ, (ω σ).IsRatio (P.L.φ σ) (ρ σ)) (ε : ℝ)
    (hε : 0 < ε) (σ : k →+* ℂ) (y₀ : CxPts p σ) :
    ∃ N ∈ 𝓝 y₀, ∀ᶠ m : ℕ in atTop, ∀ (ι : Type) [Fintype ι] (f : ι → X.functionField),
      (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ), ∀ y ∈ N,
        cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  obtain ⟨R⟩ := hs σ
  obtain ⟨a, ha⟩ := R.cover y₀
  set C := R.chart a with hC
  set i := pick (P.L.φ σ).isLB y₀ with hi
  set j := pick (P.A.φ σ).isLB y₀ with hj
  set O := C.e.source ∩ ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j) with hOdef
  have hO : IsOpen O := (C.e.open_source.inter (isOpen_ptsIn _)).inter (isOpen_ptsIn _)
  have hy₀O : y₀ ∈ O := ⟨⟨ha, mem_pick _ _⟩, mem_pick _ _⟩
  set U := C.e '' O with hUdef
  have hU : IsOpen U := C.e.isOpen_image_of_subset_source hO fun y hy => hy.1.1
  have hUO : ∀ v ∈ U, C.e.symm v ∈ O ∧ v ∈ C.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨by rwa [C.e.left_inv hy.1.1], C.e.map_source hy.1.1⟩
  obtain ⟨r, hr, hrU⟩ : ∃ r > 0, Metric.closedBall (C.e y₀) r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds ⟨y₀, hy₀O, rfl⟩)
  set K := Metric.closedBall (C.e y₀) r with hK
  have hsymm : ContinuousOn C.e.symm U := C.e.continuousOn_symm.mono fun v hv => (hUO v hv).2
  have hdc : ContinuousOn (fun v => (ω σ).dens C (C.e.symm v)) U :=
    ((ω σ).cont C).comp hsymm fun v hv => (hUO v hv).1.1.1
  have hψc : ContinuousOn (fun v => (P.A.φ σ).φ j (C.e.symm v)) U :=
    ContinuousOn.comp (show ContinuousOn ((P.A.φ σ).φ j) (ptsIn p σ (P.A.B.U j)) from
      fun y hy => ((P.A.cInf σ) j y hy).continuousAt.continuousWithinAt) hsymm fun v hv => (hUO v hv).1.2
  have hφ' : ContDiffOn ℝ 2 (fun v => (P.L.φ σ).φ i (C.e.symm v)) U := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((P.L.cInf σ).contDiffAt C hy.1.1 hy.1.2).contDiffWithinAt
  have hlevi : ∀ z ∈ U, ∀ ξ : Fin D → ℂ,
      0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (((P.L.φ σ).φ i (C.e.symm v) : ℝ) : ℂ)) z ξ).re := by
    rintro _ ⟨y, hy, rfl⟩ ξ
    exact hP σ i C y ⟨hy.1.1, hy.1.2⟩ ξ
  have hgc : ContinuousOn (fun v => Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v)) U :=
    (Real.continuous_exp.comp_continuousOn hψc.neg).mul hdc
  have hgp : ∀ v ∈ U, 0 < Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v) := fun v hv =>
    mul_pos (Real.exp_pos _) ((ω σ).pos C _ (hUO v hv).1.1.1)
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_closedBall (C.e y₀) r).exists_isMinOn
    ⟨C.e y₀, Metric.mem_closedBall_self hr.le⟩ (hdc.mono hrU)
  have hd₀ : 0 < (ω σ).dens C (C.e.symm v₀) := (ω σ).pos C _ (hUO v₀ (hrU hv₀)).1.1.1
  obtain ⟨δ, hδ, hball, hev⟩ := GlobalTheory.T.local_holomorphic_morse_inequality_uniform D U K (fun v => (P.L.φ σ).φ i (C.e.symm v))
    (fun v => Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v))
    (ε * (ω σ).dens C (C.e.symm v₀)) hU (isCompact_closedBall _ _) hrU hφ' hlevi hgc hgp (mul_pos hε hd₀)
  refine ⟨C.e.source ∩ C.e ⁻¹' K, inter_mem (C.e.open_source.mem_nhds ha)
    ((C.e.continuousAt ha).preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr)), ?_⟩
  filter_upwards [hev] with m hm ι _ f hf c y hy
  have hyO : y ∈ O := by
    have := (hUO (C.e y) (hrU hy.2)).1
    rwa [C.e.left_inv hy.1] at this
  set F : ReciprocityTheory.L2DbarEstimates.V D → ℂ := fun v => ∑ l, c l * ratVal (P.loc m 1 (f l) i j) (C.e.symm v) with hF
  have hFd : DifferentiableOn ℂ F U := by
    refine DifferentiableOn.fun_sum (𝕜 := ℂ) (u := Finset.univ)
      (A := fun l v => c l * ratVal (P.loc m 1 (f l) i j) (C.e.symm v)) fun l _ => ?_
    exact (((GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P m 1 σ (f l) (hf l) i j).2 D C).mono fun v hv =>
      ⟨(hUO v hv).2, (hUO v hv).1.1.2, (hUO v hv).1.2⟩).const_mul (c l)
  have hid : ∀ v ∈ U, ‖F v‖ ^ 2 * Real.exp (-((m : ℝ) * (P.L.φ σ).φ i (C.e.symm v))) *
      (Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v)) =
      cmb (vals P m 1 f) c σ (C.e.symm v) * (ω σ).dens C (C.e.symm v) := by
    intro v hv
    rw [cmb_eq_frame P m f hf c σ _ i j (hUO v hv).1.1.2 (hUO v hv).1.2]
    ring
  have hBU : ∀ w ∈ Metric.ball (C.e y) δ, w ∈ U := fun w hw =>
    hball _ hy.2 (Metric.ball_subset_closedBall hw)
  have hI : ∫ w in Metric.ball (C.e y) δ, ‖F w‖ ^ 2 * Real.exp (-((m : ℝ) * (P.L.φ σ).φ i (C.e.symm w))) *
      (Real.exp (-(P.A.φ σ).φ j (C.e.symm w)) * (ω σ).dens C (C.e.symm w)) =
      ∫ w in Metric.ball (C.e y) δ, cmb (vals P m 1 f) c σ (C.e.symm w) * (ω σ).dens C (C.e.symm w) :=
    setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun w hw => hid w (hBU w hw)
  have hle := integral_over_chart_le_l2 hX hs P m f hf c ω σ C _ Metric.isOpen_ball fun w hw => (hUO w (hBU w hw)).2
  have hInn : 0 ≤ ∫ w in Metric.ball (C.e y) δ, cmb (vals P m 1 f) c σ (C.e.symm w) * (ω σ).dens C (C.e.symm w) :=
    setIntegral_nonneg Metric.isOpen_ball.measurableSet fun w hw =>
      mul_nonneg (by unfold cmb; positivity) ((ω σ).pos C _ (hUO w (hBU w hw)).1.1.1).le
  have hdy : 0 < (ω σ).dens C y := (ω σ).pos C y hy.1
  have hρ0 : 0 ≤ ρ σ y := by
    have h2 := C.chernDens_nonneg (P.L.cInf σ) (hP σ) hy.1
    rw [(hρ σ).2 C y hy.1] at h2
    exact (mul_nonneg_iff_of_pos_right hdy).1 h2
  have hdet : (ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((P.L.φ σ).φ i (C.e.symm v) : ℝ) : ℂ)) (C.e y)).det.re /
      Real.pi ^ D = ρ σ y * (ω σ).dens C y / D.factorial := by
    have h1 := (hρ σ).2 C y hy.1
    rw [C.chernDens_eq (P.L.cInf σ) hy.1 hyO.1.2] at h1
    have hpi : 0 < Real.pi ^ D := by positivity
    have hfac : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
    rw [div_eq_div_iff hpi.ne' hfac.ne', ← h1]
    simp only [AlgChart.hess]
    field_simp
  have h0 := hm (C.e y) hy.2 F hFd
  beta_reduce at h0
  rw [hid _ (hrU hy.2), hI, hdet, C.e.left_inv hy.1] at h0
  have hmin' : (ω σ).dens C (C.e.symm v₀) ≤ (ω σ).dens C y := by
    have := hmin hy.2
    simp only [Set.mem_setOf_eq, C.e.left_inv hy.1] at this
    exact this
  set I := ∫ w in Metric.ball (C.e y) δ, cmb (vals P m 1 f) c σ (C.e.symm w) * (ω σ).dens C (C.e.symm w)
  have hM : 0 ≤ (m : ℝ) ^ D * I := mul_nonneg (by positivity) hInn
  have h3 : (ω σ).dens C y * cmb (vals P m 1 f) c σ y ≤
      (ω σ).dens C y * ((ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * I) := by
    rw [mul_comm]
    refine h0.trans ?_
    calc (ρ σ y * (ω σ).dens C y / D.factorial + ε * (ω σ).dens C (C.e.symm v₀)) * (m : ℝ) ^ D * I
        = (ρ σ y * (ω σ).dens C y / D.factorial + ε * (ω σ).dens C (C.e.symm v₀)) * ((m : ℝ) ^ D * I) := by ring
      _ ≤ (ρ σ y * (ω σ).dens C y / D.factorial + ε * (ω σ).dens C y) * ((m : ℝ) ^ D * I) := by gcongr
      _ = (ω σ).dens C y * ((ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * I) := by ring
  refine (le_of_mul_le_mul_left h3 hdy).trans (mul_le_mul_of_nonneg_left hle ?_)
  positivity

theorem cmb_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (ρ : ∀ σ, CxPts p σ → ℝ),
    (∀ σ, (ω σ).IsRatio (P.L.φ σ) (ρ σ)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ (ι : Type) [Fintype ι]
    (f : ι → X.functionField), (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ) (σ : k →+* ℂ) (y : CxPts p σ),
    cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  intro k _ X _ p D hX hs P hP ω ρ hρ ε hε
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  choose N hN hev using fun σ (y₀ : CxPts p σ) => local_bound hX hs P hP ω ρ hρ ε hε σ y₀
  have hcov : ∀ σ : k →+* ℂ, ∃ t : Finset (CxPts p σ), ∀ y, ∃ y₀ ∈ t, y ∈ N σ y₀ := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨t, -, ht⟩ := (isCompact_univ (X := CxPts p σ)).elim_nhds_subcover (N σ) fun y _ => hN σ y
    exact ⟨t, fun y => by simpa using ht (Set.mem_univ y)⟩
  choose t ht using hcov
  have hall : ∀ᶠ m : ℕ in atTop, ∀ σ : k →+* ℂ, ∀ y₀ ∈ t σ, ∀ (ι : Type) [Fintype ι] (f : ι → X.functionField),
      (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ), ∀ y ∈ N σ y₀,
        cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c :=
    eventually_all.2 fun σ => (eventually_all_finset (t σ)).2 fun y₀ _ => hev σ y₀
  filter_upwards [hall] with m hm ι _ f hf c σ y
  obtain ⟨y₀, hy₀, hy⟩ := ht σ y
  exact hm σ y₀ hy₀ ι f hf c y hy

end GlobalTheory.HSAmp.Morse
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalPrimeDivisorIntegralEqGenericFibreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_prime_divisor_integral_eq_generic_fibre : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (e : ℕ), IsArithVar p (e + 1) → ∀ (L : Fin e → MLine p (τ.comp (algebraMap k K))) (f : CxPts p (τ.comp (algebraMap k K)) → ℝ) (x : G), Order.coheight x = 1 → cycInt (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) x = cycInt L f (j x) := by
  first | exact @GlobalTheory.Mix.cycInt_genericFibre | exact GlobalTheory.Mix.cycInt_genericFibre | (intros; apply GlobalTheory.Mix.cycInt_genericFibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceBothStabilisersFixVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v, ∀ k' ∈ GlobalTheory.InertSph.KAt σ G.W v,
      Acts (evFin F v) (om (k, k')) (G.M.vac v) (G.M.vac v) := by
  first | exact @GlobalTheory.InertSph.vac_fixed_pair | exact GlobalTheory.InertSph.vac_fixed_pair | (intros; apply GlobalTheory.InertSph.vac_fixed_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokes
section
set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem dbarAt_eq_zero_of_eventually {n : ℕ} {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) :
    dbarAt F v = 0 := by
  refine Finset.sum_eq_zero fun a _ => ?_
  have : coefwise (fun f => GlobalTheory.dbar f v (coordVec a)) F = 0 := by
    refine Finset.sum_eq_zero fun S _ => ?_
    have hS : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
      filter_upwards [h] with x hx
      simp [hx]
    beta_reduce
    rw [GlobalTheory.dbar_congr hS, GlobalTheory.dbar_const]
    simp
  rw [this, mul_zero]

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_fn_mul_eq_zero (γ : A.Fld) (χ : M → ℝ) (j : A.ι) (w : V n)
    (h : w ∈ (A.e j).target → χ ((A.e j).symm w) = 0) : A.loc (A.fn χ * γ) j w = 0 := by
  unfold HolAtlas.loc
  split_ifs with hw
  · have key : ∀ x : A.Pt, x.pt = (A.e j).symm w → (A.fn χ * γ) x = 0 := fun x hx => by
      rw [Pi.mul_apply, HolAtlas.fn, hx, h hw]; simp
    exact key _ rfl
  · rfl

end GlobalTheory.CxForm.DbarLocStokes

namespace GlobalTheory.CxForm.DbarLocStokes

open GlobalTheory.CxForm GlobalTheory.CxForm.HolAtlas

theorem integral_dbar_fn_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  intro M _ _ _ _ _ _ n A γ χ i hγ hχ hK
  set K := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have calc0 := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1 0
  have hP : A.IsForm (A.fn χ * γ) := (calc0 _ _ (A.isForm_fn hχ) hγ).2.1
  have hω : A.IsForm (A.dbar (A.fn χ * γ)) := (calc0 _ _ hP hγ).2.2.2.2.1

  have hnear : ∀ (j : A.ι) (w : V n), w ∈ (A.e j).target → (A.e j).symm w ∉ K →
      A.loc (A.fn χ * γ) j =ᶠ[𝓝 w] fun _ => 0 := by
    intro j w hw hwK
    have hW := ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl
    filter_upwards [hW.mem_nhds ⟨hw, hwK⟩] with u hu
    exact loc_fn_mul_eq_zero A γ χ j u fun _ => image_eq_zero_of_notMem_tsupport hu.2
  have hvan : ∀ x : A.Pt, x.pt ∉ K → A.dbar (A.fn χ * γ) x = 0 := by
    intro x hx
    refine dbarAt_eq_zero_of_eventually (hnear _ _ (x.ch.map_source x.2) ?_)
    rwa [x.ch.left_inv x.2]
  rw [GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart A _ i K hω hKc hK hvan]

  set F := A.loc (A.fn χ * γ) i with hFdef
  set B : Set (V n) := A.e i '' K with hBdef
  have hB : IsCompact B := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hK)
  have hBt : B ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hK hy)
  have hF0 : ∀ v ∉ B, F =ᶠ[𝓝 v] fun _ => 0 := by
    intro v hv
    filter_upwards [hB.isClosed.isOpen_compl.mem_nhds hv] with u hu
    refine loc_fn_mul_eq_zero A γ χ i u fun ht => image_eq_zero_of_notMem_tsupport fun hk => hu ⟨_, hk, ?_⟩
    exact (A.e i).right_inv ht
  have hFs : HasCompactSupport F := HasCompactSupport.intro hB fun v hv => (hF0 v hv).self_of_nhds
  have hFC : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S) := fun S =>
    contDiff_iff_contDiffAt.2 fun v => by
      by_cases ht : v ∈ (A.e i).target
      · exact ((hP.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by norm_num)
      · have h0 : (fun v => (bas n).repr (F v) S) =ᶠ[𝓝 v] fun _ => (0 : ℂ) := by
          filter_upwards [hF0 v fun h => ht (hBt h)] with u hu
          simp [hu]
        exact contDiffAt_const.congr_of_eventuallyEq h0
  have hloc : A.loc (A.dbar (A.fn χ * γ)) i = dbarAt F := by
    funext v
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dif_pos ht]
      simp only [HolAtlas.dbar, Pt.crd, Pt.ch, (A.e i).right_inv ht]
      rfl
    · rw [HolAtlas.loc, dif_neg ht, dbarAt_eq_zero_of_eventually (hF0 v fun h => ht (hBt h))]
  rw [hloc]
  exact GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero F hFC hFs

end GlobalTheory.CxForm.DbarLocStokes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionPullbackEqDegreeMulIntersection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem inter_pull_eq_deg_mul_inter : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim →
    ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left,
      inter A (fun j => CechPic.pull f.hom.left (c j)) = deg f * inter B c := by
  intro K _ A B f hd J _ hJ c
  by_cases hi : IsIsogeny f
  · exact GlobalTheory.T.intersection_pullback_isogeny_eq_degree_mul K A B f hi J hJ c
  · have hs : ¬ Surjective f.hom.left := by
      intro hs
      exact hi ⟨GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq K A B f hd hs, hs⟩
    rw [GlobalTheory.T.intersection_number_pullback_not_surjective_eq_zero K A B f hd hs J hJ c, deg, if_neg hi]
    simp

end GlobalTheory.AV.AbVar
end

