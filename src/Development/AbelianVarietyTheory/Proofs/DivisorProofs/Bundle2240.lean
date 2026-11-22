import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibility
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialIntegerExponentDegreeEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
namespace GlobalTheory.FrameHom

open Formalism.L2.LamCM GlobalTheory.LamT.FieldPoly

theorem prod_zpow_eq_zpow_sum {K ι : Type} [Field K] {a : K} (ha : a ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ f i = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ ha]

theorem two_zpow_injective {K : Type} [Field K] [CharZero K] {m n : ℤ} (h : (2 : K) ^ m = 2 ^ n) : m = n := by
  have h' : (((2 : ℚ) ^ m : ℚ) : K) = (((2 : ℚ) ^ n : ℚ) : K) := by
    rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]; exact h
  exact (zpow_right_inj₀ (by norm_num : (0 : ℚ) < 2) (by norm_num)).1 (Rat.cast_injective h')

theorem degree_eq_of_scaling_zpow {K σ : Type} [Field K] [CharZero K] (G P : MvPolynomial σ K) (hP : P ≠ 0) (d : ℤ)
    (h : ∀ x : σ → K, MvPolynomial.eval x P ≠ 0 →
      MvPolynomial.eval (fun v => 2 * x v) G = (2 : K) ^ d * MvPolynomial.eval x G)
    (μ : σ →₀ ℕ) (hμ : MvPolynomial.coeff μ G ≠ 0) : (μ.degree : ℤ) = d := by
  have h1 : P * (MvPolynomial.aeval (fun v => MvPolynomial.C (2 : K) * MvPolynomial.X v : σ → MvPolynomial σ K) G -
      MvPolynomial.C ((2 : K) ^ d) * G) = 0 := by
    apply MvPolynomial.funext
    intro x
    by_cases hx : MvPolynomial.eval x P = 0
    · simp [hx]
    · have e : MvPolynomial.eval x
          (MvPolynomial.aeval (fun v => MvPolynomial.C (2 : K) * MvPolynomial.X v : σ → MvPolynomial σ K) G) =
          MvPolynomial.eval (fun v => 2 * x v) G := by
        clear h hμ
        induction G using MvPolynomial.induction_on with
        | C r => simp
        | add p q hp hq => simp only [map_add, hp, hq]
        | mul_X p v hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [map_mul, map_sub, e, h x hx]
      simp
  have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left hP)
  have h3 := congrArg (MvPolynomial.coeff μ) h2
  rw [coeff_aeval_scale, MvPolynomial.coeff_C_mul] at h3
  have h4 : (2 : K) ^ μ.degree = 2 ^ d := mul_right_cancel₀ hμ h3
  rw [← zpow_natCast] at h4
  exact two_zpow_injective h4

theorem frPoly_secZ_degree_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    e none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      (∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
      ∀ μ, MvPolynomial.coeff μ G ≠ 0 →
        (μ.degree : ℤ) = ∑ b, ((Dw.mult b : ℤ) * (k b : ℤ) + ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
  classical
  intro E _ _ _ H Dw l Xo c K _ _ y₀ e k _he0 F hF G hG μ hμ
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hS : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  have hev : ∀ Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K,
      evalFr (∏ b, blockDetPoly K Dw.mult b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← evalFr_blockDetPoly Dw.mult _ Y]
    simp only [evalFr, map_prod]
  have hDp : (∏ b, blockDetPoly K Dw.mult b) ≠ 0 := fun h0 => by
    have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  refine degree_eq_of_scaling_zpow G _ hDp _ (fun x hx => ?_) μ hμ
  let X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K :=
    fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
  let T : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K := fun b => Matrix.diagonal fun _ => 2
  have hX : ∀ b, (X b).det ≠ 0 := fun b => by
    have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact hx
    exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)
  have hTd : ∀ b, (T b).det ≠ 0 := fun b => by simp [T]
  obtain ⟨z₁, h₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K y₀ (fun b => (X b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hX b').isUnit)
  obtain ⟨z₂, h₂, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c K z₁ (fun b => (T b).transpose) 1
    (fun b' => by rw [Matrix.det_transpose]; exact (hTd b').isUnit)
  rw [Units.val_one] at h₁ h₂
  have h₃ := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c K y₀ z₁ z₂).2 _ _ _ _ h₁ h₂
  simp only [← Matrix.transpose_mul, _root_.mul_one] at h₃
  let t : Ix Dw → Kˣ := fun o => match o with
    | none => 1
    | some _ => Units.mk0 2 h2
  have hb : FrBor t z₁ z₂ := by
    refine ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c K z₁ z₂ z₂).1 t).2
      ⟨fun b => (T b).transpose, fun τ i j hij => ?_, fun τ i => ?_, h₂⟩
    · simp [T, Matrix.transpose_apply, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
    · simp [T, t]
  have e₁ := hG z₁ X hX h₁
  have e₂ := hG z₂ (fun b' => X b' * T b')
    (fun b' => by rw [Matrix.det_mul]; exact mul_ne_zero (hX b') (hTd b')) h₃
  have e₃ := evR_frBor_of_mem_secZ hS Xo c e hF K t z₁ z₂ hb
  have p₁ : ((∏ i, t i ^ e i : Kˣ) : K) = (2 : K) ^ (∑ b, ∑ i : Fin (Dw.mult b), e (some ⟨b, i⟩)) := by
    rw [Units.coe_prod, Fintype.prod_option, Fintype.prod_sigma]
    simp only [t, one_zpow, Units.val_one, _root_.one_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    rw [← prod_zpow_eq_zpow_sum h2]
    exact Finset.prod_congr rfl fun b _ => prod_zpow_eq_zpow_sum h2 _ _
  have p₂ : (∏ b, (X b * T b).det ^ k b) = (2 : K) ^ (∑ b, (Dw.mult b : ℤ) * (k b : ℤ)) * ∏ b, (X b).det ^ k b := by
    rw [← prod_zpow_eq_zpow_sum h2, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Matrix.det_mul]
    simp only [T, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show ((Dw.mult b : ℤ) * (k b : ℤ)) = ((Dw.mult b * k b : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul]
    ring
  have p₃ : evalFr G (fun b' => X b' * T b') = MvPolynomial.eval (fun v => 2 * x v) G := by
    unfold evalFr
    congr 2
    funext v
    simp only [T, Matrix.mul_diagonal, X, Matrix.of_apply]
    exact mul_comm _ _
  have p₄ : evalFr G X = MvPolynomial.eval x G := rfl
  rw [← p₃, ← e₂, p₂, e₃, p₁, ← p₄, ← e₁, Finset.sum_add_distrib, zpow_add₀ h2]
  ring

end GlobalTheory.FrameHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

variable {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] {k : Type} [CommRing k]

theorem functionFieldMap_comp_constFn (p : W ⟶ Sp k) (f : M ⟶ W) [IsDominant f] :
    (functionFieldMap f).comp (Cartier.constFn p) = Cartier.constFn (f ≫ p) := by
  ext a
  simp only [RingHom.comp_apply, Cartier.constFn]
  have h1 := algebraMap_germ (X := W) (U := ⊤) (x := f (genericPoint M)) trivial (algX p ⊤ a)
  have h2 := algebraMap_germ (X := M) (U := ⊤) (x := genericPoint M) trivial (algX (f ≫ p) ⊤ a)
  rw [← h1, ← h2, functionFieldMap_algebraMap]
  congr 1
  have e : f.app ⊤ (algX p ⊤ a) = algX (f ≫ p) ⊤ a := by
    simp [algX, Scheme.Hom.appLE]
    rfl
  rw [← e]
  exact Scheme.Hom.germ_stalkMap_apply f ⊤ _ trivial _

def ratPull (p : W ⟶ Sp k) (f : M ⟶ W) [IsDominant f] (n : ℕ) :
    RatForms p n →ₛₗ[functionFieldMap f] RatForms (f ≫ p) n :=
  TopForm.formMap n (functionFieldMap f) (functionFieldMap_comp_constFn p f)

end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureNeTop
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.CovTop.MeasFin

theorem measure_ne_top_of_isMeasFD {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)))
    (μ : MeasureTheory.Measure (GA D V)) (𝓕 : Set (GA D V)) (hF : IsMeasFD V K μ 𝓕) : μ 𝓕 ≠ ⊤ :=
  (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hF.1.1 hF.2).ne

theorem mass_ne_top : ∀ (hP : Hypotheses2) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), μ 𝓕 ≠ ⊤ :=
  fun _ _ _ _ _ _ _ _ μ 𝓕 hF => measure_ne_top_of_isMeasFD _ _ μ 𝓕 hF

end GlobalTheory.CovTop.MeasFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureNeZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.CovTop

theorem meas_fd_ne_zero : ∀ (hP : Hypotheses2) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕), μ 𝓕 ≠ 0 := by
  intro _ D Tu C t0 _ i P μ 𝓕 hF h0
  haveI : IsTopologicalGroup (GA D (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D (Wc D i)) := ⟨rfl⟩
  haveI : Countable (GQ (Wc D i)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Wc D i).gram
  haveI : μ.IsHaarMeasure := hF.1.1
  have h1 : μ Set.univ = 0 := by
    rw [hF.2.measure_eq_tsum Set.univ]
    refine ENNReal.tsum_eq_zero.2 fun g => ?_
    rw [Set.smul_set_univ, Set.univ_inter, h0]
  exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne' h1

end GlobalTheory.CovTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericThetaExpansionScalarNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KeyScalarNe

theorem polAVSectionInverseImage_ne_zero {K : Type} [Field K] (P : PolAV (Sp K)) (T : Over (Sp K)) (t₀ : T.left) (s : P.L.Sec)
    (hs : ∃ p, p ∈ nonzeroLocus s) (t : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)) (h : IsPolAVSectionInverseImage P T s t) :
    t ≠ 0 := by
  rintro rfl
  obtain ⟨z, hz⟩ := hs
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  have hpb : IsPullback (fst T P.A).left (snd T P.A).left T.hom P.A.hom := by
    rw [Over.fst_left, Over.snd_left]
    exact IsPullback.of_hasPullback _ _
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨y, -, hy⟩ := Scheme.exists_preimage_of_isPullback hpb t₀ z (Subsingleton.elim _ _)
  have hle : (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k) ≤ (snd T P.A).left ⁻¹ᵁ P.L.U k :=
    LB.wchart_le P.L _ (fun _ : Fin 1 => k) 0
  have hyU : y ∈ (LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k) := by
    show y ∈ LB.wchart P.L _ _
    refine Set.mem_iInter.2 fun _ => ?_
    show (snd T P.A).left y ∈ (P.L.U k : Set P.A.left)
    rw [hy]; exact hk
  subst hy
  have e := congrArg (gs (𝟙 _) y _) (h k hle)
  rw [gs_appLE _ _ _ hle (𝟙 _) y hyU, Category.id_comp, gs_stalkMap (snd T P.A).left y _ hk] at e
  have u' := u.map ((snd T P.A).left.stalkMap y).hom
  rw [← e] at u'
  have h0 : gs (𝟙 _) y ((LPow P.A P.L ((1 : ℕ) : ℤ) T).U (fun _ => k)) ((0 : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)).f (fun _ => k)) = 0 := by
    have z0 : (0 : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)).f (fun _ => k) = 0 := rfl
    rw [z0, gs_eq _ y _ hyU, map_zero, map_zero]
  rw [h0] at u'
  exact not_isUnit_zero u'

end GlobalTheory.KeyScalarNe

theorem GlobalTheory.KeyScalarNe.scalar_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (x : KeyIn (FractionRing V)) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D x.P G) (w₀ : GlobalTheory.UT.W0 U.toUnifPre), GlobalTheory.UT.NormW U.toUnifPre w₀ x.rig →
    ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
      [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C →
    ∀ (N : NumD C) (ν : NumOf D.toPre C N) (th : GlobalTheory.UT.SecA x.P C 1) (ϑ : Fam D.toPre C 1) (c : C),
      IsPolAVSectionInverseImage x.P (TFK (R := V) C) x.th th → U.ExpandsF C 1 w₀ th ϑ → ν.FamV ϑ (c • N.vth) → c ≠ 0 := by
  intro V _ _ _ _ _ D x G _ _ _ U w₀ hw C _ _ _ _ _ _ _ N ν th ϑ c hon hex hv
  rintro rfl
  rw [zero_smul] at hv
  have h0 : ν.FamV (0 : Fam D.toPre C 1) 0 := by
    have := GlobalTheory.WeilValues.famV_smul ν hv 0
    rwa [zero_smul, zero_smul] at this
  have hϑ : ϑ = 0 := GlobalTheory.Ex.FamVal.famV_inj ν hv h0
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF GlobalTheory.allSixLaws.1.globalFns U C (k := 1) le_rfl w₀ hw.1
  have ht : th = 0 := by
    have h1 := (he th ϑ).1 hex
    rw [hϑ] at h1
    exact e.map_eq_zero_iff.1 h1
  obtain ⟨z, -, hz⟩ := x.th_ne (IsLocalRing.closedPoint _)
  exact GlobalTheory.KeyScalarNe.polAVSectionInverseImage_ne_zero x.P (TFK (R := V) C) (IsLocalRing.closedPoint C) x.th ⟨z, hz⟩ th hon ht
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermMemRangeStalkOfPullbackMulLocalIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory

theorem germToFunctionField_mem_range_stalk_of_mul_pull : ∀ (k : Type) [CommRing k] (Y X : Scheme.{0}) [IsIntegral Y] [IsIntegral X]
    (p : Y ⟶ Sp k) (σ : X ⟶ Y) (U : Y.Opens) [IsIso (σ ∣_ U)] [Nonempty U] (L : LB Y) (P N : LB X)
    (C : ProdChart P (L.pull σ) N) (J : H0 (σ ≫ p) P ⊤) (g : H0 (σ ≫ p) N ⊤) (s : H0 p L U),
    C.mul (H0.restr le_top J) (H0.pull σ le_rfl s) = H0.restr le_top g → ∀ x : X,
      Function.Bijective (σ.stalkMap x).hom → (∀ (a : P.ι) (ha : x ∈ P.U a), IsUnit (H0.germ a x (memTop x) ha J)) →
      ∀ (i : L.ι) (hi : σ x ∈ L.U i) [Nonempty (U ⊓ L.U i : Y.Opens)],
        Y.germToFunctionField (U ⊓ L.U i) (s.loc i) ∈ (algebraMap (Y.presheaf.stalk (σ x)) Y.functionField).range := by
  intro k _ Y X _ _ p σ U _ _ L P N C J g s hrel x hbij hJ i hi _
  obtain ⟨t, ha, hb, hc⟩ := C.cover x
  have hjx : σ x ∈ L.U (C.b t PUnit.unit) := mem_pull.1 hb
  have hξx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hne : Nonempty (σ ⁻¹ᵁ U) := by
    obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty U›
    obtain ⟨z, -⟩ := (σ ∣_ U).surjective ⟨y, hy⟩
    exact ⟨z⟩
  have hξU : genericPoint X ∈ σ ⁻¹ᵁ U := genericPoint_mem_opens _
  have hσξη : σ (genericPoint X) ⤳ genericPoint Y := by
    obtain ⟨z, hz⟩ := (σ ∣_ U).surjective ⟨genericPoint Y, genericPoint_mem_opens U⟩
    have e : σ z.1 = genericPoint Y := (morphismRestrict_base_coe σ U z).symm.trans (congrArg Subtype.val hz)
    rw [← e]
    exact σ.base.hom.map_specializes ((genericPoint_spec X).specializes trivial)
  have hσξ : σ (genericPoint X) ∈ U ⊓ L.U (C.b t PUnit.unit) :=
    ⟨hξU, (σ.base.hom.map_specializes hξx).mem_open (L.U _).isOpen hjx⟩
  have haξ := hξx.mem_open (P.U (C.a t)).isOpen ha
  have hbξ := hξx.mem_open ((L.pull σ).U (C.b t)).isOpen hb
  have hcξ := hξx.mem_open (N.U (C.c t)).isOpen hc
  have e1 := congrArg (H0.germ (C.c t) (genericPoint X) hξU hcξ) hrel
  rw [C.germ_mul _ _ t _ hξU haξ hbξ hcξ, H0.germ_restr, H0.germ_restr, H0.germ_pull] at e1
  have hsp (B : LB X) (f : H0 (σ ≫ p) B ⊤) (a : B.ι) (hx : x ∈ B.U a) (hξ : genericPoint X ∈ B.U a) :
      H0.germ a (genericPoint X) (memTop _) hξ f =
        X.presheaf.stalkSpecializes hξx (H0.germ a x (memTop x) hx f) := by
    rw [H0.germ_apply, H0.germ_apply]
    exact (X.presheaf.germ_stalkSpecializes_apply _ hξx _).symm
  have hJu := hJ (C.a t) ha
  obtain ⟨h, hh⟩ := hbij.2 (H0.germ (C.c t) x (memTop x) hc g * ↑hJu.unit⁻¹)
  have : Nonempty (L.U (C.b t PUnit.unit)) := ⟨⟨σ x, hjx⟩⟩
  have := nonempty_inf_of_isIntegral U (L.U (C.b t PUnit.unit))
  refine germToFunctionField_mem_range_stalk_of_secOn (LB.coord_mem s) hi hjx ⟨h, ?_⟩
  let φ : Y.functionField →+* X.presheaf.stalk (genericPoint X) :=
    (σ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.stalkSpecializes hσξη).hom
  refine φ.injective ?_
  have eA : φ (algebraMap _ _ h) = X.presheaf.stalkSpecializes hξx (σ.stalkMap x h) := by
    change (σ.stalkMap _).hom ((Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
      Y.presheaf.stalkSpecializes hσξη).hom h) = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact Scheme.Hom.stalkSpecializes_stalkMap_apply σ _ _ hξx h
  have eB : φ (Y.germToFunctionField _ (LB.coord s (C.b t PUnit.unit))) =
      (σ.stalkMap (genericPoint X)).hom (H0.germ (C.b t PUnit.unit) (σ (genericPoint X)) hσξ.1 hσξ.2 s) := by
    change (σ.stalkMap _).hom (Y.presheaf.stalkSpecializes hσξη
      (Y.presheaf.germ _ (genericPoint Y) _ (LB.coord s _))) = _
    rw [Y.presheaf.germ_stalkSpecializes_apply _ hσξη]
    rfl
  rw [eA, eB, hh]
  rw [hsp P J (C.a t) ha haξ, hsp N g (C.c t) hc hcξ] at e1
  have hu : IsUnit (X.presheaf.stalkSpecializes hξx (H0.germ (C.a t) x (memTop x) ha J)) := hJu.map _
  apply hu.mul_left_cancel
  rw [e1, ← map_mul]
  exact congrArg _ (by rw [mul_left_comm, hJu.mul_val_inv, mul_one])

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspDataStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCover_component_extends_to_rankOne_cusp_data : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ σ, GoodEmb Y.d.c₂ σ → ∀ k : (Y.U σ).Comp, ∃ (Xx : FD.DataX D.host.E D.R.r)
      (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), Xx.toData = (Y.U σ).X k ∧ 𝔄 ≠ 0 ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  first | exact @GlobalTheory.CovData.exists_dataX_good | exact GlobalTheory.CovData.exists_dataX_good | (intros; apply GlobalTheory.CovData.exists_dataX_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramLatticeSpanEqTop
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.CovTop.SpanMK

theorem span_MK_eq_top {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (_hR : RowsT p) (hG : GramAt p i) :
    Submodule.span D.what₂.LL ((p.R.toRealDat.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) = ⊤ := by
  obtain ⟨ι, hι, -, himg⟩ := GlobalTheory.CovTop.SupImage.exists_emb_image_latW D _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  have hspan := hG.2.2.2.2.2
  have hall : ∀ g, g ∈ Submodule.span p.T.Q.c.F
      (latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n) : Set (VK p.fw i)) →
      ι g ∈ Submodule.span D.what₂.LL ((p.R.toRealDat.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (himg ▸ ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  obtain ⟨n, b, hbW, -, -, -, hbL⟩ := p.fw.ks i
  rw [eq_top_iff, ← hbL, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  obtain ⟨f, hf⟩ := (p.fw.e i).surjective ⟨b k, hbW k⟩
  have hE : VK p.fw i = p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n := GlobalTheory.AllWt.cuspW_wtZ _ _
  let g : VK p.fw i := ⟨f.1, hE.symm ▸ f.2⟩
  obtain ⟨h, hg⟩ := hι g
  have e1 : ι g = b k := by
    rw [hg]
    have : (⟨(g : p.T.R ((i : ℕ) + 1)), h⟩ : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n) = f := Subtype.ext rfl
    rw [this, hf]
  rw [← e1]
  exact hall g (hspan.ge Submodule.mem_top)

end GlobalTheory.CovTop.SpanMK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentCompatibilityStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_lift_tangent_compatibility : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → (∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1) → ∃ q : A'.left ⟶ A.left, i ≫ q = 𝟙 _ ∧ IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q := by
  first | exact @GlobalTheory.FlagTan.exists_retraction_of_ks_zero | exact GlobalTheory.FlagTan.exists_retraction_of_ks_zero | (intros; apply GlobalTheory.FlagTan.exists_retraction_of_ks_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackBasisLiftCompatibleStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grp_pullback_basis_lift_compatible : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR S ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) → ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) → Submodule.span S (Set.range hb) ⊔ Fil A = ⊤ ∧ LinearIndependent S (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  first | exact @GlobalTheory.LieBasisRing.lifts_basis_mod_fil | exact GlobalTheory.LieBasisRing.lifts_basis_mod_fil | (intros; apply GlobalTheory.LieBasisRing.lifts_basis_mod_fil <;> assumption)
end

