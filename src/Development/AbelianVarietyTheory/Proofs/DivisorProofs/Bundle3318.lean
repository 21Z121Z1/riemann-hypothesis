import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3302
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3280
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3300
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3118
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2415
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3308
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankOmegaLeFinrankFrobeniusKernel
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.PDivGroup

theorem pow_finrank_omega_le_finrank_frobKer : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K), ∀ r : ℕ,
    (p ^ r) ^ Module.finrank K G.omega ≤ Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) := by
  intro p _ K _ h G r
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
  have hN : Module.finrank K (G.A r) = p ^ (r * G.height) := by
    have := G.rank_eq r (IsLocalRing.closedPoint K)
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have hdim := (GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual p K h G).2.2.2
  have hord := GlobalTheory.T.finrank_le_frobeniusKernel_mul_span_primePowers p K (G.A r) r
  have hspan := GlobalTheory.T.finrank_span_pow_pDivGroup_level_le p K h G r
  have hpos : 0 < (p ^ r) ^ Module.finrank K G.dual.omega :=
    pow_pos (pow_pos (Fact.out : p.Prime).pos _) _
  have key : (p ^ r) ^ Module.finrank K G.omega * (p ^ r) ^ Module.finrank K G.dual.omega ≤
      Module.finrank K (G.A r ⧸ frobKerIdeal (p ^ r) K (G.A r)) * (p ^ r) ^ Module.finrank K G.dual.omega := by
    rw [← pow_add, hdim, ← pow_mul, ← hN]
    exact hord.trans (Nat.mul_le_mul_left _ hspan)
  exact Nat.le_of_mul_le_mul_right key hpos

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtOverClosureIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH GlobalTheory.PushEigen
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushEigen

def ptOverClosureIso (K : Type) [Field K] [IsAlgClosed K] :
    ptOver K (AlgebraicClosure K) ≅ 𝟙_ (Over (Sp K)) := by
  let σ : K ≃+* AlgebraicClosure K :=
    RingEquiv.ofBijective (algebraMap K (AlgebraicClosure K)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hI : IsIso (spMap (algebraMap K (AlgebraicClosure K))) := by
    change IsIso (Spec.map σ.toCommRingCatIso.hom)
    infer_instance
  exact Over.isoMk (asIso (spMap (algebraMap K (AlgebraicClosure K)))) (by
    change spMap _ ≫ 𝟙 _ = spMap _
    exact Category.comp_id _)

def ptClosureEquiv {K : Type} [Field K] [IsAlgClosed K] (B : AbVar K) :
    B.Pt ≃* (𝟙_ (Over (Sp K)) ⟶ B.X) where
  toFun x := (ptOverClosureIso K).inv ≫ x
  invFun y := (ptOverClosureIso K).hom ≫ y
  left_inv x := by simp
  right_inv y := by simp
  map_mul' x y := MonObj.comp_mul _ x y

end GlobalTheory.PushEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeGeometricDegreeOfIsNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef.RankNef

theorem rank_le_gdeg_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), P.L.IsNef D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  intro hAr hHS k _ X _ p D hX P hL J _ e x he hx hbox
  have hcz : CharZero X.functionField := by
    have := hX.charZero
    exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 this
  have htb : IsTranscendenceBasis ℤ x := (GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).2 x hx
  obtain ⟨A, hAamp, hAnef, s, hs, hs0⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hAr k X p D hX
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  let Q : Pair p := ⟨P.L, A, P.r, r', P.hr, hr'⟩
  have hQbox : ∀ c, boxFam e x c ∈ Q.H 1 0 := by
    intro c z i j hi _
    obtain ⟨j', hj'⟩ : ∃ j', z ∈ P.A.B.U j' := by
      have h1 : z ∈ (⨆ j, P.A.B.U j) := by rw [P.A.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 h1
    have h2 := hbox c z i j' hi hj'
    simpa [Pair.loc, Q] using h2
  have hbd : ∀ c, ∃ u : ℝ, 0 ≤ u ∧ boxFam e x c ∈ Q.Bl 1 0 (Real.exp u) :=
    fun c => GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX Q 1 0 _ (hQbox c)
  choose u hu0 hu using hbd
  set t₀ : ℝ := ∑ c, u c with ht₀
  have ht₀0 : 0 ≤ t₀ := Finset.sum_nonneg fun c _ => hu0 c
  have hBl : ∀ c, boxFam e x c ∈ Q.Bl 1 0 (Real.exp t₀) := fun c =>
    ⟨(hu c).1, fun σ y => ((hu c).2 σ y).trans
      (Real.exp_le_exp.2 (Finset.single_le_sum (fun c _ => hu0 c) (Finset.mem_univ c)))⟩
  obtain ⟨ε, hεinj, hεrange, hεnu, -⟩ := RepDict.rep_dict k X p Q 0 1 Q.A (Pair.rep_base k X p Q).2.1
  have hsm : ∀ w ∈ A.smallSec, ε w ∈ Q.Bl 0 1 1 := by
    intro w hw
    refine ⟨?_, fun σ y => ?_⟩
    · rw [← SetLike.mem_coe, ← hεrange]; exact ⟨w, rfl⟩
    · have hnn : 0 ≤ Q.nu 0 1 σ y (ε w) := by
        unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      have h2 : Q.nu 0 1 σ y (ε w) ^ 2 ≤ 1 := by rw [hεnu]; exact hw σ y
      exact (pow_le_one_iff_of_nonneg hnn two_ne_zero).1 h2
  obtain ⟨g, hg, hg0⟩ : ∃ g ∈ Q.Bl 0 1 1, g ≠ 0 := by
    by_cases h : ε s = 0
    · refine ⟨ε 0, hsm 0 (HermLB.zero_mem_smallSec _), fun h0 => hs0 ?_⟩
      exact (hεinj (h0.trans h.symm)).symm
    · exact ⟨ε s, hsm s hs, h⟩
  have key : ∀ n : ℕ, 0 < n →
      (D.factorial : ℝ) * ((Fintype.card J * n ^ D : ℕ) : ℝ) ≤ gdeg ((P.L.pow n).tens A) D := by
    intro n hn
    have hrep : Q.Rep (n : ℤ) 1 ((Q.L.pow n).tens Q.A) := by
      have h1 := Pair.rep_pow k X p Q 1 0 Q.L n (Pair.rep_base k X p Q).1
      have h2 := Pair.rep_tens k X p Q _ _ 0 1 _ _ h1 (Pair.rep_base k X p Q).2.1
      simpa using h2
    have hamp : IsAmpleLB ((P.L.pow n).tens A).B :=
      GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX (P.L.pow n) A
        (nefFib_of_isNef (GlobalTheory.NefPow.isNef_pow hAr k X p D hX P.L n hL)) hAamp
    have hsp : ((P.L.pow n).tens A).SemiPos D := (hL.semiPos.pow n).tens hAnef.semiPos
    have hvec : ∀ m : ℕ, 0 < m → ∃ v : Fin ((Fintype.card J * n ^ D) * m ^ D) → X.functionField,
        LinearIndependent ℤ v ∧ ∀ i, v i ∈ Q.Bl (m * (n : ℤ)) (m * 1) (Real.exp ((t₀ * n) * m)) := by
      intro m hm
      obtain ⟨v0, hv0, hv0s⟩ := GlobalTheory.T.exists_linearIndependent_products_function_field X.functionField D x htb J e he (n * m) (Nat.mul_pos hn hm)
      have hcard : Fintype.card J * (n * m) ^ D = (Fintype.card J * n ^ D) * m ^ D := by rw [mul_pow]; ring
      have hgm : g ^ m ∈ Q.H ((m : ℤ) * 0) ((m : ℤ) * 1) :=
        (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).1
      have hgm0 : g ^ m ≠ 0 := pow_ne_zero _ hg0
      refine ⟨fun i => v0 (Fin.cast hcard.symm i) * g ^ m, ?_, fun i => ?_⟩
      · have hli := hv0.map' (LinearMap.mulRight ℤ (g ^ m))
          (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hgm0))
        exact hli.comp _ (Fin.cast_injective _)
      · obtain ⟨w, a, ha, hw⟩ := hv0s (Fin.cast hcard.symm i)
        have hprod := GlobalTheory.T.boxMonomialFamily_prod_mem_normBall_of_exponent_lt k X p Q D J e x 1 0 (Real.exp t₀) (Real.exp_pos _).le hBl (n * m) w a ha
        rw [← hw] at hprod
        obtain ⟨hmem, hnu⟩ := NuMul.mul_mem_H_and_nu_mul k X p Q _ _ _ _ _ _ hprod.1 hgm
        have e1 : (((n * m : ℕ) : ℤ) * 1 + (m : ℤ) * 0) = (m : ℤ) * n := by push_cast; ring
        have e2 : (((n * m : ℕ) : ℤ) * 0 + (m : ℤ) * 1) = (m : ℤ) * 1 := by push_cast; ring
        rw [e1, e2] at hmem hnu
        refine ⟨hmem, fun σ y => ?_⟩
        rw [hnu, (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).2 σ y]
        have hA1 := hprod.2 σ y
        have hB1 : Q.nu 0 1 σ y g ^ m ≤ 1 := by
          have hnn : 0 ≤ Q.nu 0 1 σ y g := by
            unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
          exact pow_le_one₀ hnn (hg.2 σ y)
        have hnn' : 0 ≤ Q.nu ((n * m : ℕ) * 1) ((n * m : ℕ) * 0) σ y (v0 (Fin.cast hcard.symm i)) := by
          unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
        have hexp : Real.exp t₀ ^ (n * m) = Real.exp ((t₀ * n) * m) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        calc _ ≤ Real.exp t₀ ^ (n * m) * 1 := mul_le_mul hA1 hB1 (pow_nonneg (by unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) _) (pow_nonneg (Real.exp_pos _).le _)
          _ = _ := by rw [mul_one, hexp]
    have := GlobalTheory.T.factorial_mul_rank_le_degree_of_indep_small_sections hAr hHS k X p D hX Q n 1 _ hrep hamp hsp (Fintype.card J * n ^ D) (t₀ * n) hvec
    exact this
  have hlim := GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow hAr k X p D hX P.L A
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnD : (0 : ℝ) < (n : ℝ) ^ D := by positivity
  rw [le_div_iff₀ hnD]
  have := key n hn
  push_cast at this
  nlinarith [this]

end GlobalTheory.HSNef.RankNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectAddBundleSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefectAdd

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem int_eq_add_of_ae {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine q σ) {f g h : CxPts q σ → ℝ} (hf : Intg L f) (hg : Intg L g)
    (hh : ∀ ε : ℤˣ, ∀ᵐ y ∂part L ε, h y = f y + g y) :
    Mix.int L h = Mix.int L f + Mix.int L g := by
  simp only [Mix.int]
  rw [integral_congr_ae (hh 1), integral_congr_ae (hh (-1)), integral_add hf.1 hg.1, integral_add hf.2 hg.2]
  ring

theorem defect_add : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M A N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ⊓ nonzeroLocus a ∨ z ∈ nonzeroLocus t) → ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ side N L ((M.tens A).logSec s₁) (N.logSec t) (divOfSec (M.tens A).φ.isLB s₁ h₁) - side (M.tens A) L (N.logSec t) ((M.tens A).logSec s₁) (divOfSec N.φ.isLB t ht) = (side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)) + (side N L (A.logSec a) (N.logSec t) (divOfSec A.φ.isLB a ha) - side A L (N.logSec t) (A.logSec a) (divOfSec N.φ.isLB t ht)) := by
  intro hP F _ X _ _ p σ e hproj hdim L M A N s hs a ha t ht hcod
  obtain ⟨s₁, h₁, hloc, hmult, hlog⟩ := GlobalTheory.T.tensor_product_sections_zeros_multiplicities_norms F X p σ M A s hs a ha
  refine ⟨s₁, h₁, hloc, ?_⟩
  have hσ : Function.Injective σ := σ.injective
  haveI : CompactSpace X := compactSpace_of_projOver hproj
  have iM := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L) M s hs
  have iA := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L) A a ha
  have iMh := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons M L) N t ht
  have iAh := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons A L) N t ht
  have e1 : Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) ((M.tens A).logSec s₁) =
      Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s) +
        Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (A.logSec a) := by
    refine int_eq_add_of_ae _ iM iA fun ε => ?_
    have h0 := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ hσ hproj (e + 1) (Fin.cons N L) ε (nonzeroLocus s₁) h₁
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy
    exact hlog y (by simpa using hy)
  have e2 : Mix.int (Fin.cons (M.tens A) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) +
        Mix.int (Fin.cons A L : Fin (e + 1) → MLine p σ) (N.logSec t) := by
    have key := GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hproj (e + 1) (Fin.cons M L) 0 M A (N.logSec t)
      (by simpa only [Fin.update_cons_zero] using iMh) (by simpa only [Fin.update_cons_zero] using iAh)
    simpa only [Fin.update_cons_zero] using key.2
  have e3 : ∑ᶠ z, ((divOfSec (M.tens A).φ.isLB s₁ h₁).mult z : ℝ) * cycInt L (N.logSec t) z =
      ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (N.logSec t) z +
        ∑ᶠ z, ((divOfSec A.φ.isLB a ha).mult z : ℝ) * cycInt L (N.logSec t) z := by
    rw [← finsum_add_distrib]
    · refine finsum_congr fun z => ?_
      rw [hmult z]
      push_cast
      ring
    · exact (divOfSec M.φ.isLB s hs).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
    · exact (divOfSec A.φ.isLB a ha).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have e4 : ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.tens A).logSec s₁) z =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z +
        ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (A.logSec a) z := by
    rw [← finsum_add_distrib]
    · refine finsum_congr fun z => ?_
      by_cases hz : (divOfSec N.φ.isLB t ht).mult z = 0
      · simp [hz]
      · rw [← mul_add]
        congr 1
        have hco := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
        have hzt : z ∉ nonzeroLocus t := fun h =>
          (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero hz)
        have hz1 : z ∈ nonzeroLocus s ⊓ nonzeroLocus a := (hcod z hco).resolve_right hzt
        have hz1' := TopologicalSpace.Opens.mem_inf.1 hz1
        have hzs₁ : z ∈ nonzeroLocus s₁ := hloc ▸ hz1
        have hdimz := (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hproj hdim z).1 hco
        obtain ⟨-, -, hnull, hint⟩ := GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure hP F X p σ hproj e L z hdimz
        refine int_eq_add_of_ae _ (hint M s hz1'.1) (hint A a hz1'.2) fun ε => ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hnull _ hzs₁ ε)] with y hy
        exact hlog _ (by simpa using hy)
    · exact (divOfSec N.φ.isLB t ht).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
    · exact (divOfSec N.φ.isLB t ht).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  simp only [side]
  rw [e1, e2, e3, e4]
  ring

end GlobalTheory.DefectAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalExtendedBundleOfGeneric
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DiagAmpleExt

theorem diag_comm {S S' : Scheme.{0}} {G : Over S} {A : Over S'} (φ : A.left ⟶ G.left)
    (φ₂ : (G2 A).left ⟶ (G2 G).left) (h : IsSquare φ φ₂) :
    φ ≫ (lift (𝟙 G) (𝟙 G)).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ := by
  apply pullback.hom_ext
  · change φ ≫ (lift (𝟙 G) (𝟙 G)).left ≫ (fst G G).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ ≫ (fst G G).left
    rw [h.1, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id, ← Category.assoc,
      ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp]
  · change φ ≫ (lift (𝟙 G) (𝟙 G)).left ≫ (snd G G).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ ≫ (snd G G).left
    rw [h.2, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id, ← Category.assoc,
      ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp]

theorem relAmple_diag_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hG hφ hsq P P' hP hP' e hA
  have hAab : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hφ
  have := hAab.proper
  set dG := (lift (𝟙 G) (𝟙 G)).left
  set dA := (lift (𝟙 A) (𝟙 A)).left
  have hM : (P'.pull dG).IsLB := pull_isLB hP' _
  refine GlobalTheory.ModelAmpleExt.relAmple_of_generic W L G A φ hG hφ (P'.pull dG) hM ?_
  have i1 : LBIso ((P'.pull dG).pull φ) (P'.pull (φ ≫ dG)) :=
    GlobalTheory.OriginCohom.lbIso_pull_pull_comp hP' dG φ
  have i2 : LBIso (P'.pull (dA ≫ φ₂)) ((P'.pull φ₂).pull dA) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP' dA rfl
  have i3 : LBIso ((P'.pull φ₂).pull dA) (P.pull dA) :=
    GlobalTheory.GenSpread.lbIso_pullback e.symm dA
  rw [diag_comm φ φ₂ hsq] at i1
  have hφ2 := pull_isLB hP' φ₂
  have j : LBIso (P.pull dA) ((P'.pull dG).pull φ) :=
    (LBIso.trans (pull_isLB hM φ) (pull_isLB hP' _) (pull_isLB hP dA) i1 (LBIso.trans (pull_isLB hP' _)
      (pull_isLB hφ2 dA) (pull_isLB hP dA) i2 i3)).symm
  have hsq' : IsPullback (𝟙 A.left) A.hom A.hom (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull hsq' (pull_isLB hP dA) (pull_isLB hM φ)
    (LBIso.trans (pull_isLB hM φ) (pull_isLB hP dA) (pull_isLB (pull_isLB hP dA) _) j.symm
      (GlobalTheory.GenSpread.lbIso_pull_pull hP (𝟙 _) (a := dA) (Category.id_comp _).symm)) hA

end GlobalTheory.DiagAmpleExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectsPullbackOfCompatibleTowerAdic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFormalAssemble

theorem siegPB_id_of_tower : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) := by
  intro g n B _ ζ R _ _ I hI s s' c c' t ce φ ψ β hc hφ hψ hβφ hβψ
  have H := GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms
  have hp : GlobalTheory.AbLaw.IsProjBy c.A.hom :=
    GlobalTheory.WtTower.isProjBy_of_relAmple c.A (pull_isLB c.isLB _) hc.1
  obtain ⟨G, hG, hGφ, -, -, hGP⟩ := GlobalTheory.AlgUniq.exists_iso_algebraisation H R I hI (fun e => (ce e).A) β c.A c'.A
    c.ab c'.ab hp φ ψ (fun e => (hφ e).1) hβφ (fun e => (hψ e).1) hβψ
  choose b₂ hb₂ hb₂P using fun e => (hφ e).2.1
  choose b₂' hb₂' hb₂'P using fun e => (hψ e).2.1
  have hP := hGP c.P c'.P b₂ b₂' c.isLB c'.isLB hb₂ hb₂' fun e =>
    LBIso.trans (pull_isLB c.isLB _) (ce e).isLB (pull_isLB c'.isLB _) (LBIso.symm (hb₂P e)) (hb₂'P e)
  refine ⟨G.hom.left, (G.hom ⊗ₘ G.hom).left, isGrpPullback_of_iso G, ⟨?_, ?_⟩, hP, fun a => ?_⟩
  · rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
  · rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
  · have : IsProper c'.A.hom := c'.ab.proper
    have : IsProper (𝟙_ (Over (Sp R))).hom := show IsProper (𝟙 _) from inferInstance
    have key : c.lev a ≫ G.hom = c'.lev a := by
      refine GlobalTheory.Published.FormalAlgebraisation.Morphisms.hom_ext H hI fun e => ?_
      have hw : pullback.fst (𝟙_ (Over (Sp R))).hom (Out.thick R I e) =
          pullback.snd (𝟙_ (Over (Sp R))).hom (Out.thick R I e) ≫ Out.thick R I e := by
        rw [← pullback.condition]; exact (Category.comp_id _).symm
      have l1 := (hφ e).2.2 a
      have l2 := (hψ e).2.2 a
      simp only [pow_one] at l1 l2
      rw [hw, Over.comp_left, Category.assoc, Category.assoc, ← reassoc_of% l1, ← l2, ← hGφ e]
    rw [Category.id_comp, ← key, Over.comp_left]

end GlobalTheory.SiegFormalAssemble
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePeriodMapAbelianVarietyLatticeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_periodMap_abelianVariety_lattice : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ p : u.Λ →+ ℂ, ∃ x, IsPer u.ex u.Λ x p := by
  first | exact @GlobalTheory.PerSurj.main | exact GlobalTheory.PerSurj.main | (intros; apply GlobalTheory.PerSurj.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapAbelianSchemeNormalCharZeroBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMap_abelianScheme_normal_charZero_base : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) → Geo.Tor.IsNormalScheme X → IsLocallyNoetherian X → (∀ x : X, CharZero (X.residueField x)) → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) → ∃ f : X ⟶ PSpace o n, f ≫ PSpace.str o n = s ∧ ThMap G L ρ m q f := by
  first | exact @GlobalTheory.UMin.ThetaMapGen.main | exact GlobalTheory.UMin.ThetaMapGen.main | (intros; apply GlobalTheory.UMin.ThetaMapGen.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
private theorem tate_nsmul_lev {p : ℕ} {M : Type} [CommGroup M]
    (s : _root_.GlobalTheory.HTLat.Tate p M) (k m : ℕ) :
    (k • s).lev m = s.lev m ^ k := by
  induction k with
  | zero => simp [_root_.GlobalTheory.HTLat.Tate.lev_zero]
  | succ k ih => rw [succ_nsmul, _root_.GlobalTheory.HTLat.Tate.lev_add, ih, pow_succ]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.AV.AbVar.tl_lev_surj_ker : ∀ (K : Type) [Field K]
    (l : ℕ) [Fact l.Prime] (A : _root_.GlobalTheory.AV.AbVar K) (n : ℕ),
    (∀ x : A.Pt, x ^ l ^ n = 1 →
        ∃ t : _root_.GlobalTheory.AV.AbVar.Tl l A, t.lev n = x) ∧
      ∀ t : _root_.GlobalTheory.AV.AbVar.Tl l A, t.lev n = 1 ↔
        ∃ s : _root_.GlobalTheory.AV.AbVar.Tl l A, t = (l : ℤ_[l]) ^ n • s := by
  intro K _ l hl A n
  have hlpos : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  refine ⟨fun x hx => _root_.GlobalTheory.Published.tate_lev_surj l _
    (_root_.GlobalTheory.AV.AbVar.pt_divisible K A l hlpos) n x hx, fun t => ?_⟩
  have hcast : ∀ s : _root_.GlobalTheory.AV.AbVar.Tl l A,
      (l : ℤ_[l]) ^ n • s = (l ^ n : ℕ) • s := by
    intro s
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    push_cast
    rfl
  constructor
  · intro ht
    let u : ℕ → A.Pt := fun m => t.lev (m + n)
    have hu : ∀ m, u m ^ l ^ m = 1 ∧ u (m + 1) ^ l = u m := by
      intro m
      refine ⟨?_, ?_⟩
      · simp only [u]
        rw [Nat.add_comm, _root_.GlobalTheory.HTLat.Tate.lev_add_pow, ht]
      · simp only [u]
        rw [show m + 1 + n = m + n + 1 by omega, _root_.GlobalTheory.HTLat.Tate.lev_succ]
    refine ⟨_root_.GlobalTheory.HTLat.Tate.mk u hu, ?_⟩
    rw [hcast]
    refine _root_.GlobalTheory.HTLat.Tate.ext fun m => ?_
    rw [tate_nsmul_lev,
      _root_.GlobalTheory.HTLat.Tate.lev_mk]
    simp only [u]
    rw [_root_.GlobalTheory.HTLat.Tate.lev_add_pow]
  · rintro ⟨s, rfl⟩
    rw [hcast, tate_nsmul_lev, _root_.GlobalTheory.HTLat.Tate.lev_pow]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPeriodsTranslatedBundleTwistStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_periods_translatedBundle_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → (∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK 0 ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK 0) (-1) (D₂.toPre.psi 0) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi 0) (LB.pullGen D.toPre.P.L _ _ (g.s 0) (toUnit (TK R)).left))) → ∀ χ : D₂.toPre.X, ∃ t : LB.Gen (LB.LinComb D.toPre.P.L (fun i => D₂.toPre.xK χ ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i) (fun i => -1 * GlobalTheory.MumCmp.twε i)), GlobalTheory.MumCmp.MapsAtExp D.toPre.P.L D₂.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε w (D₂.toPre.xK χ) (-1) (D₂.toPre.psi χ) t ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ t (LB.mulGen D.toPre.P.L _ _ _ _ (D.toPre.psi (xe χ)) (LB.pullGen D.toPre.P.L _ _ (g.s (xe χ)) (toUnit (TK R)).left)) := by
  first | exact @GlobalTheory.MumCmp.psi_twist | exact GlobalTheory.MumCmp.psi_twist | (intros; apply GlobalTheory.MumCmp.psi_twist <;> assumption)
end

