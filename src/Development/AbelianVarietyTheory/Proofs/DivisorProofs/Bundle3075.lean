import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2992
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImHermFormAlternatingNondegenerateOnLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.HermImNondeg

theorem hermForm_add_right' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_smul_right' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (a • w) = star a * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hermForm_self_star {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z : Fin g → ℂ) :
    star (hermForm Hm z z) = hermForm Hm z z := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, h.apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem im_hermForm_alternating_nondegenerate (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La) (hP : Function.Injective P)
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) :
    (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have hc : ((EF x x : ℤ) : ℝ) = 0 := by
      rw [← hEF]
      have h1 := congrArg Complex.im (hermForm_self_star hH (P x))
      have h2 : (star (hermForm Hm (P x) (P x))).im = -(hermForm Hm (P x) (P x)).im := Complex.conj_im _
      linarith
    exact_mod_cast hc
  · set z := P x with hz
    have key : ∀ w : Fin g → ℂ, (hermForm Hm z w).im = 0 := by
      intro w
      have hw : w ∈ Submodule.span ℝ (Set.range P) := hspan ▸ Submodule.mem_top
      induction hw using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y, rfl⟩ := ha
        rw [hEF, hx y]; simp
      | zero => simp [hermForm]
      | add a b _ _ h1 h2 => rw [hermForm_add_right', Complex.add_im, h1, h2, add_zero]
      | smul r a _ h1 =>
        rw [← Complex.coe_smul, hermForm_smul_right']
        simp [h1]
    have hI := key (Complex.I • z)
    rw [hermForm_smul_right'] at hI
    have hre : (hermForm Hm z z).re = 0 := by
      have : (star Complex.I * hermForm Hm z z).im = -(hermForm Hm z z).re := by
        simp [Complex.mul_im]
      linarith
    by_contra hne
    have hz0 : z ≠ 0 := by
      intro h0; apply hne; apply hP; rw [← hz, h0, map_zero]
    have := hpos z hz0
    linarith

end GlobalTheory.HermImNondeg

example : ∀ (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Function.Injective P → Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveArakelovFormulaRhsTensorAdditive
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace GlobalTheory.MixHt

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem divOfRatSec_congr {B : LB Y} (hB : B.IsLB) {t t' : B.ι → Y.functionFieldˣ} (ht : IsRatSec B t)
    (ht' : IsRatSec B t') (e : ∀ c, genericPoint Y ∈ B.U c → t c = t' c) :
    divOfRatSec hB ht = divOfRatSec hB ht' :=
  CartierDiv.ext_of_isEqn fun z => by
    obtain ⟨c, hc⟩ := exists_chart hB z
    refine ⟨t c, (presents_divOfRatSec hB ht).isEqn c z hc, ?_⟩
    rw [e c (gen_mem hc)]
    exact (presents_divOfRatSec hB ht').isEqn c z hc

theorem logNorm_congr {σ : k →+* ℂ} {B : LB Y} (φ : Weight q σ B) {t t' : B.ι → Y.functionFieldˣ}
    (e : ∀ c, genericPoint Y ∈ B.U c → t c = t' c) (y : CxPts q σ) : logNorm φ t y = logNorm φ t' y := by
  rw [logNorm, logNorm, e _ (gen_mem (mem_ptsIn.1 (mem_pick φ.isLB y)))]

theorem logNorm_tens_mul {σ : k →+* ℂ} (M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ}
    {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) (hu : IsRatSec A.B u) {y : CxPts q σ}
    (hyr : y ∈ offSupp q σ (M.div hr)) (hyu : y ∈ offSupp q σ (A.div hu)) :
    logNorm ((M.tens A).φ σ) (fun c : M.B.ι × A.B.ι => r c.1 * u c.2) y =
      logNorm (M.φ σ) r y + logNorm (A.φ σ) u y := by
  obtain ⟨h₁, h₂⟩ := mem_ptsIn_inf.1 (mem_pick ((M.tens A).φ σ).isLB y)
  have hu₁ := hr.unitAt M.isLB hyr h₁
  have hu₂ := hu.unitAt A.isLB hyu h₂
  rw [logNorm_eq (M.φ σ) hr hyr h₁, logNorm_eq (A.φ σ) hu hyu h₂]
  change Real.log ‖ratVal ((r (pick ((M.tens A).φ σ).isLB y).1 * u (pick ((M.tens A).φ σ).isLB y).2 :
      Y.functionFieldˣ) : Y.functionField) y‖ - ((M.φ σ).φ (pick ((M.tens A).φ σ).isLB y).1 y +
      (A.φ σ).φ (pick ((M.tens A).φ σ).isLB y).2 y) / 2 = _
  rw [Units.val_mul, ratVal_mul hu₁.regAt hu₂.regAt, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hu₁)) (norm_ne_zero_iff.2 (ratVal_ne_zero hu₂))]
  ring

theorem chernInt_eq_of_null {D : ℕ} (hY : IsArithVar q D) {σ : k →+* ℂ} {B : LB Y} (φ : Weight q σ B)
    {S S' : Set (CxPts q σ)} (hS : S ⊆ S') (Z : Set Y) (hZ : IsClosed Z) (hg : genericPoint Y ∉ Z)
    (hd : S' \ S ⊆ {y | under y ∈ Z}) (f : CxPts q σ → ℝ) : φ.chernInt D S' f = φ.chernInt D S f := by
  have h (ε : ℤˣ) : S' =ᵐ[φ.chernPart D ε] S := ae_eq_set.2
    ⟨measure_mono_null hd (ChernNull.chernPart_over_closed hY Z hZ hg σ φ ε), by
      rw [Set.diff_eq_empty.2 hS]; exact measure_empty⟩
  rw [Weight.chernInt, Weight.chernInt, setIntegral_congr_set (h 1), setIntegral_congr_set (h (-1))]

theorem chernInt_tens {D : ℕ} (hY : IsArithVar q D) (σ : k →+* ℂ) {B : LB Y} (φ : Weight q σ B)
    (M A : HermLB q) {r : M.B.ι → Y.functionFieldˣ} {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ} (ht : IsRatSec (M.tens A).B t)
    (htu : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2)
    (h₁ : φ.ChernIntegrableOn D (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r))
    (h₂ : φ.ChernIntegrableOn D (offSupp q σ (A.div hu)) (logNorm (A.φ σ) u)) :
    φ.chernInt D (offSupp q σ ((M.tens A).div ht)) (logNorm ((M.tens A).φ σ) t) =
      φ.chernInt D (offSupp q σ (M.div hr)) (logNorm (M.φ σ) r) +
        φ.chernInt D (offSupp q σ (A.div hu)) (logNorm (A.φ σ) u) := by
  let S := offSupp q σ (M.div hr) ∩ offSupp q σ (A.div hu) ∩ offSupp q σ ((M.tens A).div ht)
  let Z : Set Y := ((M.div hr).supp : Set Y) ∪ (A.div hu).supp ∪ ((M.tens A).div ht).supp
  have hZ : IsClosed Z :=
    ((M.div hr).supp.isClosed.union (A.div hu).supp.isClosed).union ((M.tens A).div ht).supp.isClosed
  have hg : genericPoint Y ∉ Z := by
    simp only [Z, Set.mem_union, SetLike.mem_coe, not_or]
    exact ⟨⟨CartierDiv.genericPoint_notMem_supp _, CartierDiv.genericPoint_notMem_supp _⟩,
      CartierDiv.genericPoint_notMem_supp _⟩
  have hd (T : Set (CxPts q σ)) : T \ S ⊆ {y | under y ∈ Z} := fun y hy => by
    by_contra hz
    simp only [Set.mem_setOf_eq, Z, Set.mem_union, SetLike.mem_coe, not_or] at hz
    exact hy.2 ⟨⟨mem_offSupp.2 hz.1.1, mem_offSupp.2 hz.1.2⟩, mem_offSupp.2 hz.2⟩
  have hSm : MeasurableSet S :=
    (((isOpen_offSupp _).inter (isOpen_offSupp _)).inter (isOpen_offSupp _)).measurableSet
  rw [chernInt_eq_of_null hY φ (fun _ h => h.2) Z hZ hg (hd _),
    chernInt_eq_of_null hY φ (fun _ h => h.1.1) Z hZ hg (hd _) (logNorm (M.φ σ) r),
    chernInt_eq_of_null hY φ (fun _ h => h.1.2) Z hZ hg (hd _) (logNorm (A.φ σ) u),
    Weight.chernInt_congr hSm (g := fun y => logNorm (M.φ σ) r y + logNorm (A.φ σ) u y) ?_]
  · exact Weight.chernInt_add ⟨h₁.1.mono_set fun _ h => h.1.1, h₁.2.mono_set fun _ h => h.1.1⟩
      ⟨h₂.1.mono_set fun _ h => h.1.2, h₂.2.mono_set fun _ h => h.1.2⟩
  · intro y hy
    rw [logNorm_congr _ htu y]
    exact logNorm_tens_mul M A hr hu hy.1.1 hy.1.2

theorem archInt_tens (hAI : ArchInteg) {e : ℕ} (hY : IsArithVar q e) (N M A : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} {u : A.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r)
    (hu : IsRatSec A.B u) {t : (M.tens A).B.ι → Y.functionFieldˣ} (ht : IsRatSec (M.tens A).B t)
    (htu : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2) :
    N.archInt (M.tens A) e ht = N.archInt M e hr + N.archInt A e hu := by
  have := hY.finite_emb
  unfold HermLB.archInt
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun σ => chernInt_tens hY σ (N.φ σ) M A hr hu ht htu
    (hAI k Y q e hY M N r hr σ) (hAI k Y q e hY A N u hu σ)

theorem archInt_of_isEmpty (hE : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (N M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) (e : ℕ) : N.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine (finsum_congr fun σ => ?_).trans finsum_zero
  have := hE σ
  rw [Weight.chernInt, Set.eq_empty_of_isEmpty (offSupp q σ (M.div hr))]
  simp only [Measure.restrict_empty, integral_zero_measure, sub_zero]

theorem isArithVar_or_isEmpty (hq : IsAmb q) {e : ℕ} (he : topologicalKrullDim Y = (e + 1 : ℕ)) :
    IsArithVar q e ∨ ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ) := by
  obtain ⟨ℓ, _⟩ := CharP.exists Γ(Y, ⊤)
  rcases CharP.char_is_prime_or_zero Γ(Y, ⊤) ℓ with hℓ | rfl
  · refine .inr fun σ => ⟨fun y => ?_⟩
    let f : Γ(Y, ⊤) →+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp y.1.appTop.hom
    have h0 : (ℓ : ℂ) = 0 := by rw [← map_natCast f, CharP.cast_eq_zero, map_zero]
    exact hℓ.ne_zero (Nat.cast_eq_zero.1 h0)
  · have := CharP.charP_to_charZero Γ(Y, ⊤)
    exact .inl ⟨hq.1, hq.2, ‹_›, hq.3, (flat_int_iff_charZero _).2 this, he⟩

theorem pol_add {ι : Type} [Fintype ι] (a b : (ι → ℤ) → ℝ) :
    FibreProj.pol (fun n => a n + b n) = FibreProj.pol a + FibreProj.pol b := by
  simp only [FibreProj.pol, mul_add, Finset.sum_add_distrib]

theorem finsum_mult_add [IsLocallyNoetherian Y] [CompactSpace Y] (D E : CartierDiv Y) (h : Y → ℝ) :
    ∑ᶠ z, ((D + E).mult z : ℝ) * h z = ∑ᶠ z, (D.mult z : ℝ) * h z + ∑ᶠ z, (E.mult z : ℝ) * h z := by
  have hfin (D : CartierDiv Y) : (Function.support fun z => (D.mult z : ℝ) * h z).Finite :=
    D.finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  simp only [CartierDiv.mult_add, Int.cast_add, add_mul]
  exact finsum_add_distrib (hfin D) (hfin E)

theorem recVal_tens : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ (h : Y → ℝ) (L : Fin e → HermLB q) (M A : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (u : A.B.ι → Y.functionFieldˣ) (hu : IsRatSec A.B u) (t : (M.tens A).B.ι → Y.functionFieldˣ) (ht : IsRatSec (M.tens A).B t), (∀ (i : M.B.ι) (j : A.B.ι), genericPoint Y ∈ M.B.U i → genericPoint Y ∈ A.B.U j → t (i, j) = r i * u j) → recVal h L (M.tens A) ht = recVal h L M hr + recVal h L A hu := by
  intro hAI k _ Y _ _ q hq e he h L M A r hr u hu t ht htu
  have := hq.isNoetherian
  have htu' : ∀ c : M.B.ι × A.B.ι, genericPoint Y ∈ (M.tens A).B.U c → t c = r c.1 * u c.2 :=
    fun c hc => htu c.1 c.2 hc.1 hc.2
  have hdiv : (M.tens A).div ht = M.div hr + A.div hu :=
    (divOfRatSec_congr _ ht (PtHtComb.isRatSec_tens hr hu) htu').trans (PtHtComb.div_tens M A hr hu)
  have hmix : mixArch L (M.tens A) ht = mixArch L M hr + mixArch L A hu := by
    rcases isArithVar_or_isEmpty hq he with hY | hE
    · unfold mixArch
      rw [← add_div, ← pol_add]
      congr 2
      funext n
      exact archInt_tens hAI hY (comb L n) M A hr hu ht htu'
    · have h0 (N' : HermLB q) {r' : N'.B.ι → Y.functionFieldˣ} (hr' : IsRatSec N'.B r') :
          mixArch L N' hr' = 0 := by
        simp [mixArch, archInt_of_isEmpty hE, FibreProj.pol]
      rw [h0, h0, h0, add_zero]
  unfold recVal
  rw [hdiv, finsum_mult_add, hmix]
  ring

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCombinationTermsRationalPointFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_combination_terms_rational_point_frame : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) (g' : GtPtF D (FractionRing R)), GtPt.IsPullF (FractionRing R) (toUnit (TF (R := R) (FractionRing R))).left g g' → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, g.b.left] (DegPre.lineε 1))) (l : FractionRing R), l ≠ 0 → ∀ (k : ℕ) (wk : Frm D (FractionRing R) k g'.b), wk.IsGen → (∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing R) z (l ^ k) * (val wk (𝟙 _) z J).val = (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val) → ∀ (s : Fam D (FractionRing R) k) (n : ℕ) (c : Fin n → FractionRing R) (fs : Fin n → ∀ α : D.X, D.SecB k α), (∀ α : D.X, GeneratorPullback.SecLin D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => fs i α) (DegPre.prB D (FractionRing R)).left (fun i => scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i))) → ∀ a : Fin n → D.X → R, (∀ (i : Fin n) (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval (fs i α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a i α) * (val (L := D.P.L) D.rig r z J ^ k).val) → ∀ α : D.X, l ^ k * coef s g' wk α = ∑ i, c i * algebraMap R (FractionRing R) (a i α) := by
  first | exact @GlobalTheory.Poinc.IntEval.coef_comb_pull | exact GlobalTheory.Poinc.IntEval.coef_comb_pull | (intros; apply GlobalTheory.Poinc.IntEval.coef_comb_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramesRespectCubicalStructures
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.IntCube

open GlobalTheory.Poinc.IntEval GlobalTheory.WCub

theorem prod_alt {U : Type} [CommGroup U] (v : Finset (Fin 3) → U) :
    ∏ k : thK.{0}, v k.down ^ thε k =
      v {0, 1, 2} * v {0} * v {1} * v {2} * (v {0, 1} * v {0, 2} * v {1, 2} * v ∅)⁻¹ := by
  refine (Fintype.prod_equiv (Equiv.ulift : thK.{0} ≃ Finset (Fin 3)) _
    (fun I => v I ^ ((-1 : ℤ) ^ (3 - I.card))) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (3 - (∅ : Finset (Fin 3)).card) = -1 := by decide
  have q₁ : ∀ i : Fin 3, (-1 : ℤ) ^ (3 - ({i} : Finset (Fin 3)).card) = 1 := by decide
  have q₄ : (-1 : ℤ) ^ (3 - ({0, 1} : Finset (Fin 3)).card) = -1 := by decide
  have q₅ : (-1 : ℤ) ^ (3 - ({0, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₆ : (-1 : ℤ) ^ (3 - ({1, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₇ : (-1 : ℤ) ^ (3 - ({0, 1, 2} : Finset (Fin 3)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₁, q₄, q₅, q₆, q₇]
  simp only [zpow_neg, zpow_one, mul_inv]
  ac_rfl

section Cube

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S}

def IsCube (p : Finset (Fin 3) → (T ⟶ G)) : Prop :=
  p ∅ = 1 ∧ p {0, 1} = p {0} * p {1} ∧ p {0, 2} = p {0} * p {2} ∧ p {1, 2} = p {1} * p {2} ∧
    p {0, 1, 2} = p {0} * p {1} * p {2}

theorem IsCube.thφ_eq {p : Finset (Fin 3) → (T ⟶ G)} (hp : IsCube p) (k : thK.{0}) :
    (lift (p {0}) (lift (p {1}) (p {2}))).left ≫ thφ G (x3 G) k = (p k.down).left := by
  obtain ⟨h₀, h₁, h₂, h₃, h₄⟩ := hp
  have e : (lift (p {0}) (lift (p {1}) (p {2}))).left ≫ thφ G (x3 G) k =
      (psum G ![p {0}, p {1}, p {2}] k.down).left :=
    congrArg (fun q => q.left) ((psum_hom (preHom (lift (p {0}) (lift (p {1}) (p {2})))) (x3 G) k.down).trans
      (congrArg (fun q => psum G q k.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])))
  refine e.trans (congrArg (fun q : T ⟶ G => q.left) ?_)
  have c : ∀ I : Finset (Fin 3), I = ∅ ∨ I = {0} ∨ I = {1} ∨ I = {2} ∨ I = {0, 1} ∨ I = {0, 2} ∨ I = {1, 2} ∨
      I = {0, 1, 2} := by decide
  generalize k.down = I
  rcases c I with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₀.symm
  · exact _root_.mul_one _
  · exact _root_.mul_one _
  · exact _root_.mul_one _
  · exact (congrArg (p {0} * ·) (_root_.mul_one (p {1}))).trans h₁.symm
  · exact (congrArg (p {0} * ·) (_root_.mul_one (p {2}))).trans h₂.symm
  · exact (congrArg (p {1} * ·) (_root_.mul_one (p {2}))).trans h₃.symm
  · exact ((congrArg (fun q => p {0} * (p {1} * q)) (_root_.mul_one (p {2}))).trans
      (_root_.mul_assoc _ _ _).symm).trans h₄.symm

theorem exists_unit {L : RigLB G} (c : CubicalStr G L) {p : Finset (Fin 3) → (T ⟶ G)} (hp : IsCube p)
    {K : Type} [Fintype K] {φ : Finset (Fin 3) → K → (T.left ⟶ G.left)} {ε : K → ℤ}
    (hφ : ∀ (U : Type) [CommGroup U] (F : (T.left ⟶ G.left) → U), ∃ d : U, ∀ I,
      ∏ k, F (φ I k) ^ ε k = F (p I).left * d)
    (a : ∀ I, LB.Gen (LB.LinComb L.L (φ I) ε)) (ha : ∀ I, (a I).IsGen) :
    ∃ u : Γ(T.left, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good L.L z J →
      val (a {0, 1, 2}) r z J * val (a {0}) r z J * val (a {1}) r z J * val (a {2}) r z J =
        gm r z ⊤ u * (val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t
          (r ≫ (lift (p {0}) (lift (p {1}) (p {2}))).left) z J *
          (val (a {0, 1}) r z J * val (a {0, 2}) r z J * val (a {1, 2}) r z J * val (a ∅) r z J)) := by
  obtain ⟨u, hu⟩ := GlobalTheory.PsiScalUnit.exists_ratio L.isLB
    (u := LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (a {0, 1, 2}) (a {0})) (a {1})) (a {2}))
    (u' := LB.mulGen L.L _ _ _ _
      (LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift (p {0}) (lift (p {1}) (p {2}))).left)
      (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (a {0, 1}) (a {0, 2})) (a {1, 2})) (a ∅)))
    (fun U _ F => by
      obtain ⟨d, hd⟩ := hφ U F
      have e : ∏ k : thK.{0}, F ((lift (p {0}) (lift (p {1}) (p {2}))).left ≫ thφ G (x3 G) k) ^ thε k = _ :=
        (Finset.prod_congr rfl fun k _ => congrArg (fun q => F q ^ thε k) (hp.thφ_eq k)).trans
          (prod_alt (fun I => F (p I).left))
      refine Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) e rfl)).symm
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hd]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (ha _) (ha _)) (ha _)) (ha _))
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ c.isGen _)
      (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (ha _) (ha _)) (ha _)) (ha _)))
  refine ⟨u, fun Z r z J hJ => ?_⟩
  have := hu Z r z J hJ
  rw [val_mul hJ, val_mul hJ, val_mul hJ] at this
  refine this.trans (congrArg (_ * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _) ?_)))
  rw [val_mul hJ, val_mul hJ, val_mul hJ]

end Cube

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

theorem level_cub (U : UnifPre I D A G) {h : Finset (Fin 3) → (𝟙_ (Over (Sp R)) ⟶ G)} (hh : IsCube h)
    {b : Finset (Fin 3) → (𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)} (e : ℕ)
    (hb : ∀ S, hRed I (h S) e ≫ pGl U e = thick R I e ≫ (b S).left)
    (y : Sp (R ⧸ I ^ (e + 1))) {J N} (hJ : Good D.toPre.P.L y J) (hN : Good U.LG.L y N) :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (thick R I e ≫ (lift (b {0}) (lift (b {1}) (b {2}))).left) y J =
      (∏ k : thK.{0}, wv U e (hRed I (h k.down) e) y (J (hRed I (h k.down) e ≫ pGl U e))
        (N (hRed I (h k.down) e ≫ fGl I G e)) ^ thε k) *
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t
        (thick R I e ≫ (lift (h {0}) (lift (h {1}) (h {2}))).left) y N := by
  have := (U.gt e).q_hom
  have := GlobalTheory.TorsionTranslate.mono_fst (I := I) e G
  let x : Fin 3 → (𝟙_ (Over (Sp (R ⧸ I ^ (e + 1)))) ⟶ thickObj R I e G) := fun i =>
    Over.homMk (hRed I (h {i}) e) (pullback.lift_snd _ _ _)
  have l : ∀ {H : Over (Sp R)} (p : Finset (Fin 3) → (𝟙_ (Over (Sp R)) ⟶ H)) (i : Fin 3),
      (lift (p {0}) (lift (p {1}) (p {2}))).left ≫ (x3 H i).left = (p {i}).left := fun p i => by
    have : lift (p {0}) (lift (p {1}) (p {2})) ≫ x3 _ i = p {i} := by fin_cases i <;> simp [x3]
    exact congrArg (fun q => q.left) this
  have g₁ : tri (thick R I e) (fstG I e G) x = thick R I e ≫ (lift (h {0}) (lift (h {1}) (h {2}))).left :=
    hom_ext_triple _ fun i => (tripleProductPoint_comp_projection _ _ _ i).trans ((hRed_fst (h {i}) e).trans
      ((congrArg (thick R I e ≫ ·) (l h i).symm).trans (Category.assoc _ _ _).symm))
  have g₂ : tri (thick R I e) (U.gt e).pG x = thick R I e ≫ (lift (b {0}) (lift (b {1}) (b {2}))).left :=
    hom_ext_triple _ fun i => (tripleProductPoint_comp_projection _ _ _ i).trans ((hb {i}).trans
      ((congrArg (thick R I e ≫ ·) (l b i).symm).trans (Category.assoc _ _ _).symm))
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm
  have f₄ := tri_thφ (thick R I e) (U.gt e).pG x (U.gt e).q rfl
  have ps : ∀ k : thK.{0}, (psum (thickObj R I e G) x k.down).left = hRed I (h k.down) e := fun k => by
    rw [← cancel_mono (fstG I e G).left]
    exact (f₃ k).symm.trans ((congrArg (· ≫ thφ G (x3 G) k) g₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (thick R I e ≫ ·) (hh.thφ_eq k)).trans (hRed_fst _ e).symm)))
  have key := GlobalTheory.PowUnif.w_cub_val U e _ x y hJ hN
  refine (congrArg (fun q => val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε)
    D.toPre.cub.t q y J) g₂).symm.trans (key.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ =>
      congrArg (· ^ thε k) ?_) (congrArg (fun q => val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε)
        U.cubG.t q y N) g₁)))
  rw [f₃, f₄, ps]
  rfl

end Level

section Main

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Sp R)} {D : DegData R I}
  {A : PolAV (Sp (FractionRing R))} [GrpObj G] [IsCommMonObj G]

theorem alg_level {U : Type} [CommGroup U] (f t w : Finset (Fin 3) → U) (ρ u u' cG cD : U)
    (h : ∀ S, t S * w S * f S = ρ)
    (hf : f {0, 1, 2} * f {0} * f {1} * f {2} = u * (cG * (f {0, 1} * f {0, 2} * f {1, 2} * f ∅)))
    (ht : (t {0, 1, 2})⁻¹ * (t {0})⁻¹ * (t {1})⁻¹ * (t {2})⁻¹ =
      u' * (cD * ((t {0, 1})⁻¹ * (t {0, 2})⁻¹ * (t {1, 2})⁻¹ * (t ∅)⁻¹)))
    (hc : cD = w {0, 1, 2} * w {0} * w {1} * w {2} * (w {0, 1} * w {0, 2} * w {1, 2} * w ∅)⁻¹ * cG) : u = u' := by
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E (h {0, 1, 2}); have a₂ := E (h {0}); have a₃ := E (h {1}); have a₄ := E (h {2})
  have a₅ := E (h {0, 1}); have a₆ := E (h {0, 2}); have a₇ := E (h {1, 2}); have a₈ := E (h ∅)
  have b₁ := E hf; have b₂ := E ht; have b₃ := E hc
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ b₁ b₂ b₃
  linear_combination (norm := abel) a₁ + a₂ + a₃ + a₄ - a₅ - a₆ - a₇ - a₈ - b₁ + b₂ + b₃

theorem alg_end {U : Type} [CommGroup U] {fp fm t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ u cG cD : U}
    (hf : fp = u * (cG * fm))
    (ht : t₁⁻¹ * t₂⁻¹ * t₃⁻¹ * t₄⁻¹ = u * (cD * (t₅⁻¹ * t₆⁻¹ * t₇⁻¹ * t₈⁻¹))) :
    fp * (t₁ * t₂ * t₃ * t₄) * cD = cG * fm * (t₅ * t₆ * t₇ * t₈) := by
  apply Additive.ofMul.injective
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have b₁ := E hf; have b₂ := E ht
  simp only [ofMul_mul, ofMul_inv] at b₁ b₂ ⊢
  linear_combination (norm := abel) b₁ - b₂

theorem cube_of_tRel [IsHausdorff I R] (U : UnifPre I D A G) {h : Finset (Fin 3) → (𝟙_ (Over (Sp R)) ⟶ G)}
    (hh : IsCube h) {b : Finset (Fin 3) → (𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)} (hbc : IsCube b)
    (hb : ∀ S e, hRed I (h S) e ≫ pGl U e = thick R I e ≫ (b S).left)
    (f : ∀ S, LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (h S).left) (fun _ => 1)))
    (t : ∀ S, LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, (b S).left] (DegPre.lineε 1)))
    (hf : ∀ S, (f S).IsGen) (ht : ∀ S, (t S).IsGen) (hT : ∀ S e, TRel U (h S) (b S) (f S) (t S) e)
    (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp R))).left) (z : Z) (JG) (JB) (hJG : Good U.LG.L z JG)
    (hJB : Good D.toPre.P.L z JB) :
    (val (f {0, 1, 2}) r z JG * val (f {0}) r z JG * val (f {1}) r z JG * val (f {2}) r z JG) *
        (val (t {0, 1, 2}) r z JB * val (t {0}) r z JB * val (t {1}) r z JB * val (t {2}) r z JB) *
        val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
          (r ≫ (lift (b {0}) (lift (b {1}) (b {2}))).left) z JB =
      val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t
          (r ≫ (lift (h {0}) (lift (h {1}) (h {2}))).left) z JG *
        (val (f {0, 1}) r z JG * val (f {0, 2}) r z JG * val (f {1, 2}) r z JG * val (f ∅) r z JG) *
        (val (t {0, 1}) r z JB * val (t {0, 2}) r z JB * val (t {1, 2}) r z JB * val (t ∅) r z JB) := by
  obtain ⟨u, hu⟩ := exists_unit U.cubG hh (K := Fin 1) (φ := fun S _ => (h S).left) (ε := fun _ => 1)
    (fun W _ F => ⟨1, fun S => by simp⟩) f hf
  obtain ⟨u', hu'⟩ := exists_unit D.toPre.cub hbc (K := Fin 2)
    (φ := fun S => ![(η[D.toPre.P.A]).left, (b S).left]) (ε := fun k => -DegPre.lineε 1 k)
    (fun W _ F => ⟨(F (η[D.toPre.P.A]).left)⁻¹, fun S => by
      rw [Fin.prod_univ_two, mul_comm]
      simp [DegPre.lineε]⟩)
    (fun S => LB.invGen D.toPre.P.L _ _ (t S)) (fun S => invGen_isGen _ _ _ _ (ht S))
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp R))).left) (z : Z) (J), Good D.toPre.P.L z J →
      (val (t {0, 1, 2}) r z J)⁻¹ * (val (t {0}) r z J)⁻¹ * (val (t {1}) r z J)⁻¹ * (val (t {2}) r z J)⁻¹ =
        gm r z ⊤ u' * (val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
          (r ≫ (lift (b {0}) (lift (b {1}) (b {2}))).left) z J *
          ((val (t {0, 1}) r z J)⁻¹ * (val (t {0, 2}) r z J)⁻¹ * (val (t {1, 2}) r z J)⁻¹ * (val (t ∅) r z J)⁻¹)) :=
    fun Z r z J hJ => by
      simp only [← val_inv]
      exact hu' Z r z J hJ
  have e : u = u' := by
    refine Units.ext (GlobalTheory.CoordLinear.fn_eq_of_levels I ⊤ rfl _ _ fun e => appTop_eq_of_gm _ _ u u' fun y => ?_)
    choose J hJ using fun χ : Sp (R ⧸ I ^ (e + 1)) ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
    choose N hN using fun χ : Sp (R ⧸ I ^ (e + 1)) ⟶ G.left => exists_chart U.LG.isLB (χ y)
    refine alg_level (fun S => val (f S) (thick R I e) y N) (fun S => val (t S) (thick R I e) y J)
      (fun S => wv U e (hRed I (h S) e) y (J (hRed I (h S) e ≫ pGl U e)) (N (hRed I (h S) e ≫ fGl I G e)))
      (val (L := D.toPre.P.L) D.toPre.rig (thick R I e) y J) _ _ _ _ (fun S => ?_)
      (hu _ (thick R I e) y N hN) (hv _ (thick R I e) y J hJ)
      ((level_cub U hh e (fun S => hb S e) y hJ hN).trans (congrArg₂ (· * ·) (prod_alt (fun S =>
        wv U e (hRed I (h S) e) y (J (hRed I (h S) e ≫ pGl U e)) (N (hRed I (h S) e ≫ fGl I G e)))) rfl))
    have k := hT S e _ (𝟙 _) y J N hJ hN
    simp only [Category.id_comp] at k
    exact k
  subst e
  exact alg_end (hu Z r z JG hJG) (hv Z r z JB hJB)

end Main

theorem integral_cube : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (h : Finset (Fin 3) → ((𝟙_ (Over (Sp V))) ⟶ G)) (g : Finset (Fin 3) → GtPt D.toPre (𝟙_ (Over (Sp V)))) (f : ∀ S, LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (h S).left) (fun _ => 1))) (t : ∀ S, LB.Gen (LB.LinComb D.toPre.P.L ![(η[D.toPre.P.A]).left, ((g S).b).left] (DegPre.lineε 1))), h ∅ = 1 → h {0, 1} = h {0} * h {1} → h {0, 2} = h {0} * h {2} → h {1, 2} = h {1} * h {2} → h {0, 1, 2} = h {0} * h {1} * h {2} → (g ∅).b = 1 → (g {0, 1}).b = (g {0}).b * (g {1}).b → (g {0, 2}).b = (g {0}).b * (g {2}).b → (g {1, 2}).b = (g {1}).b * (g {2}).b → (g {0, 1, 2}).b = (g {0}).b * (g {1}).b * (g {2}).b → (∀ S, GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator.FormalEq U.toUnifPre (h S) (g S)) → (∀ S, (f S).IsGen) → (∀ S, (t S).IsGen) → (∀ S (e : ℕ), GlobalTheory.Poinc.IntEval.TRel U.toUnifPre (h S) (g S).b (f S) (t S) e) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good U.LG.L z JG → Good D.toPre.P.L z JB → (val (f {0, 1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {0}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {1}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {2}) (toUnit (TF (R := V) (FractionRing V))).left z JG) * (val (t {0, 1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {0}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {1}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {2}) (toUnit (TF (R := V) (FractionRing V))).left z JB) * cubV D.toPre.cub z JB ((toUnit (TF (R := V) (FractionRing V))) ≫ (g {0}).b) ((toUnit (TF (R := V) (FractionRing V))) ≫ (g {1}).b) ((toUnit (TF (R := V) (FractionRing V))) ≫ (g {2}).b) = cubV U.cubG z JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}) * (val (f {0, 1}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {0, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f {1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JG * val (f ∅) (toUnit (TF (R := V) (FractionRing V))).left z JG) * (val (t {0, 1}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {0, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t {1, 2}) (toUnit (TF (R := V) (FractionRing V))).left z JB * val (t ∅) (toUnit (TF (R := V) (FractionRing V))).left z JB) := by
  intro V _ _ _ hV D A G _ _ _ U h g f t h₀ h₁ h₂ h₃ h₄ g₀ g₁ g₂ g₃ g₄ hF hf ht hT z JG JB hJG hJB
  have := hV.2.2.1
  have key := cube_of_tRel U.toUnifPre (h := h) ⟨h₀, h₁, h₂, h₃, h₄⟩ (b := fun S => (g S).b) ⟨g₀, g₁, g₂, g₃, g₄⟩
    (fun S e => hRed_pGl (hF S) e) f t hf ht hT _ (toUnit (TF (R := V) (FractionRing V))).left z JG JB hJG hJB
  exact (congrArg₂ (· * ·) rfl ((val_cub D.toPre.cub _ hJB _ _ _).symm.trans (val_pull hJB _ _ _))).trans
    (key.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·)
      ((val_pull hJG _ _ _).symm.trans (val_cub U.cubG _ hJG _ _ _)) rfl) rfl))

end GlobalTheory.Poinc.IntCube
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_iff_finite_ker' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsFinite f.hom.left ↔ Finite (ptMap f).ker := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_iff_finite_ker | exact GlobalTheory.AV.AbVar.isFinite_iff_finite_ker | (intros; apply GlobalTheory.AV.AbVar.isFinite_iff_finite_ker <;> assumption)
end

