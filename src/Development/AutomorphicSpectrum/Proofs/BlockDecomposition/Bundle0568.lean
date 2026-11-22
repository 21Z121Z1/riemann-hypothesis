import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.IsClosedImmersionLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffineOpenAndIsPushout
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine IsSmoothHerm IsHorizontal divSupp multAt geoNum charOf ptsIntegral
  IsIntersectionFamily IntersectionSystem IsFullIntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat RatRStatement)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem dim_of_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hrange : Set.range j = closure {j (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image j.continuous
    rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  exact topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange

theorem dim_closure_image {X Y : Scheme.{0}} (j : Y ⟶ X) [IsClosedImmersion j] (z : Y) :
    topologicalKrullDim (closure ({j z} : Set X)) = topologicalKrullDim (closure ({z} : Set Y)) := by
  obtain ⟨Z, k, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  exact (dim_of_generic (k ≫ j)).trans (dim_of_generic k).symm

theorem isometric_restr_restr {X Z : Scheme.{0}} (N : HermLB (mpStr ℤ m n)) (i : X ⟶ MP ℤ m n) (j : Z ⟶ X) :
    ((N.restr i).restr j).Isometric (N.pull (j ≫ i) (Category.assoc _ _ _)) := by
  have hm : ∀ (c : ((N.restr i).restr j).B.ι) (x : Z), x ∈ ((N.restr i).restr j).B.U c →
      x ∈ (N.pull (j ≫ i) (Category.assoc _ _ _)).B.U (fun _ => c PUnit.unit PUnit.unit) := fun c x h =>
    (mem_pull (F := j ≫ i) (x := x)).2 ((mem_pull (F := i) (x := j x)).1 ((mem_pull (F := j) (x := x)).1 h))
  refine HermLB.isometric_of_chart (fun c _ => c PUnit.unit PUnit.unit) (fun c x h => hm c x h) (fun x c c' h h' => ?_)
    fun σ c y hy => ?_
  · have h₁ := (mem_pull (F := j) (x := x)).1 h
    have h₁' := (mem_pull (F := j) (x := x)).1 h'
    refine (gm_pull_g (N.B.pull i) j (𝟙 Z) x c c' h h').trans ?_
    refine (gm_pull_g N.B i (𝟙 Z ≫ j) x _ _ h₁ h₁').trans ?_
    refine Eq.trans ?_ (gm_pull_g N.B (j ≫ i) (𝟙 Z) x _ _ (hm c x h) (hm c' x h')).symm
    simp only [Category.assoc]
  · refine ((N.φ σ).pull_φ (j ≫ i) (Category.assoc _ _ _) _ y).trans ?_
    refine Eq.trans ?_ ((((N.φ σ).pull i rfl).pull_φ j rfl c y)).symm
    refine Eq.trans ?_ ((N.φ σ).pull_φ i rfl _ _).symm
    congr 1

theorem archInt_transport {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp ℤ} {L M : HermLB q} (iso : L.Isometric M)
    {r : L.B.ι → Z.functionFieldˣ} (hr : IsRatSec L.B r) :
    ∃ (r' : M.B.ι → Z.functionFieldˣ) (hr' : IsRatSec M.B r'), M.div hr' = L.div hr ∧
      (∀ e, M.archInt M e hr' = L.archInt L e hr) ∧
      ∀ σ, Set.EqOn (GlobalTheory.Cartier.logNorm (M.φ σ) r') (GlobalTheory.Cartier.logNorm (L.φ σ) r) (GlobalTheory.Cartier.offSupp q σ (L.div hr)) := by
  obtain ⟨r', hr', h₁, h₂⟩ := iso.exists_isRatSec hr
  refine ⟨r', hr', h₁, fun e => ?_, h₂⟩
  simp only [HermLB.archInt, h₁, iso.chernInt_eq]
  exact finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (h₂ σ)

theorem rec_eq (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (e : ℕ) (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) e)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1))
    (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r) :
    cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.restr i).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.restr i).archInt (N.restr i) e hr := by
  obtain ⟨f, g, hfg, hrat⟩ := h₅ m n N A hN Z i r hr
  have hcyc := h₆ m n N A hN Z i e hZ r hr f g hfg hrat (cycVal II A e)
  have hint := h₇ m n N N A A hN hN Z i e hZ hA hA r hr f g hfg hrat
  have hrr := hR _ _ (II _ (Bk n)) (hII.1 _ _) _ e (fun _ => A) A f g hP (fun _ => hA) hA hfg
  have hs : (Fin.snoc (fun _ : Fin e => A) A : Fin (e + 1) → HermLine (Bk n)) = fun _ => A := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  rw [hs] at hrr
  rw [hint, hcyc, cycVal, if_pos hP.2.2.1, hrr]
  rfl

theorem mp_var (m : ℕ) (n : Fin (m + 1) → ℕ) : GlobalTheory.IsArithVar (mpStr ℤ m n) (∑ i, n i) :=
  GlobalTheory.Amb.isArithVar_mp ℤ inferInstance m n

theorem not_horizontal_of_dim_zero (h₃ : PtDict) {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (z : X)
    (hz : topologicalKrullDim (closure ({z} : Set X)) = (0 : ℕ)) : ¬ IsHorizontal (ptIdeal (i z)) := by
  obtain ⟨Z, k, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  have hd : topologicalKrullDim Z = (0 : ℕ) := (dim_of_generic k).symm.trans hz
  obtain ⟨-, h2, -, -⟩ := h₃ m n Z (k ≫ i) 0 hd
  intro hh
  have hc : CharZero Γ(Z, ⊤) := h2.1 hh
  exact (mp_var m n).dim_ne_zero (k ≫ i) hc (by exact_mod_cast hd)

theorem curve_eq (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hPt : PtLen)
    (hC : CurveInt) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) 0)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) 1)
    (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r) :
    cycVal II A 1 (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.restr i).div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
        ∑ᶠ σ, ∑ᶠ y : CxPts (i ≫ mpStr ℤ m n) σ, logNorm ((N.restr i).φ σ) r y := by
  rw [rec_eq h₅ h₆ h₇ hR II hII N A hN hA Z i 0 hZ hP r hr, (hC Z _ hZ (N.restr i) (N.restr i) r hr).2]
  refine congrArg (· - _) (finsum_congr fun z => ?_)
  by_cases hz : ((N.restr i).div hr).mult z = 0
  · simp [hz]
  have hd := h₄ Z _ 0 hZ z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
  rw [cycVal, if_neg (not_horizontal_of_dim_zero h₃ i z hd), hPt m n Z i z hd]

theorem rec_eq' (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {q : Z ⟶ Sp ℤ} (hq : i ≫ mpStr ℤ m n = q) (e : ℕ)
    (hZ : GlobalTheory.IsArithVar q e) (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1))
    (r : (N.pull i hq).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.pull i hq).B r) :
    cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.pull i hq).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.pull i hq).archInt (N.pull i hq) e hr := by
  subst hq
  exact rec_eq h₅ h₆ h₇ hR II hII N A hN hA Z i e hZ hP r hr

theorem curve_eq' (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hPt : PtLen)
    (hC : CurveInt) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {q : Z ⟶ Sp ℤ} (hq : i ≫ mpStr ℤ m n = q)
    (hZ : GlobalTheory.IsArithVar q 0) (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) 1)
    (r : (N.pull i hq).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.pull i hq).B r) :
    cycVal II A 1 (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.pull i hq).div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
        ∑ᶠ σ, ∑ᶠ y : CxPts q σ, logNorm ((N.pull i hq).φ σ) r y := by
  subst hq
  exact curve_eq h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z i hZ hP r hr

theorem charP_of_cast {R : Type} [CommRing R] [IsDomain R] {p : ℕ} (hp : p.Prime) (h : (p : R) = 0) : CharP R p := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists R
  rcases (Nat.dvd_prime hp).1 ((CharP.cast_eq_zero_iff R ℓ p).1 h) with rfl | rfl
  · exact absurd ((Nat.cast_one (R := R)).symm.trans ((CharP.cast_eq_zero_iff R 1 1).2 dvd_rfl)) one_ne_zero
  · exact hℓ

theorem heightEq_of (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hV : VertEq)
    (hPt : PtLen) (hC : CurveInt) (hR : RatRStatement) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) :
    HeightEq II := by
  intro m n N A hN hA X _ _ i _ h H z d hd
  induction d using Nat.strong_induction_on generalizing z with
  | _ d ih =>
  obtain ⟨Z, j, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  have hZd : topologicalKrullDim Z = d := (dim_of_generic j).symm.trans hd
  have hmp := mp_var m n
  have hnoeth := hmp.isNoetherian_sub (j ≫ i)
  have hln : IsLocallyNoetherian Z := hnoeth.toIsLocallyNoetherian
  have hcomp : ∀ x, (j ≫ i) x = i (j x) := fun x => by simp
  obtain ⟨-, hp₃, hp₄, hp₅⟩ := h₃ m n Z (j ≫ i) d hZd
  simp only [hcomp] at hp₃ hp₄ hp₅
  by_cases hW : IsHorizontal (ptIdeal (i (j (genericPoint Z))))
  · have hc : CharZero Γ(Z, ⊤) := hp₃.1 hW
    have hP := hp₄ hW
    obtain ⟨r₀, hr₀⟩ := exists_isRatSec ((N.restr i).restr j).isLB
    obtain ⟨r, hr, e₁, e₂, e₃⟩ := archInt_transport (isometric_restr_restr N i j) hr₀
    cases d with
    | zero => exact absurd (by exact_mod_cast hZd) (hmp.dim_ne_zero (j ≫ i) hc)
    | succ e =>
      have hZ₀ : GlobalTheory.IsArithVar ((j ≫ i) ≫ mpStr ℤ m n) e := hmp.of_isClosedImmersion (j ≫ i) hc hZd
      have hZ : GlobalTheory.IsArithVar (j ≫ i ≫ mpStr ℤ m n) e := by
        rw [← Category.assoc]
        exact hZ₀
      rcases Nat.eq_zero_or_pos e with rfl | he
      · have hcv := curve_eq' h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z (j ≫ i) (Category.assoc _ _ _) hZ
          (by simpa only [hcomp] using hP) r hr
        simp only [hcomp] at hcv
        rw [H.point Z j hc hZd r₀ hr₀, hcv, HermLB.curveDeg, e₁]
        refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => (e₃ σ (mem_offSupp.2 ?_)).symm)
        rw [hZ.under_eq_genericPoint]
        exact CartierDiv.genericPoint_notMem_supp _
      · have hrc := rec_eq' h₅ h₆ h₇ hR II hII N A hN hA Z (j ≫ i) (Category.assoc _ _ _) e hZ
          (by simpa only [hcomp] using hP) r hr
        simp only [hcomp] at hrc
        rw [(H.recursion_one j hc he hZd hr₀).2, hrc, e₂, e₁]
        refine congrArg (· - _) (finsum_congr fun z' => ?_)
        by_cases hz : (((N.restr i).restr j).div hr₀).mult z' = 0
        · simp [hz]
        have hdz := h₄ Z _ e hZ z' (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
        rw [ih e (Nat.lt_succ_self e) (j z') ((dim_closure_image j z').trans hdz)]
  · obtain ⟨hpr, hz⟩ := hp₅ hW
    have key : ∀ p : ℕ, p.Prime → ((p : ℕ) : Γ(Z, ⊤)) = 0 → h (j (genericPoint Z)) =
        (geoNum d (ptIdeal (i (j (genericPoint Z)))) (fun _ => A.a) : ℝ) * Real.log p := by
      intro p hp h0
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : CharP Γ(Z, ⊤) p := charP_of_cast hp h0
      letI : Algebra (ZMod p) Γ(Z, ⊤) := ZMod.algebra _ p
      have e₁ := H.vertical Z j (ZMod p) d hZd
      have e₂ : topSelfIntersection (ZMod p) ((N.restr i).B.pull j) d = _ := hV m n N A hN X i Z j p d hZd
      rw [e₁, e₂, Nat.card_zmod]
    rw [key _ hpr hz, cycVal, if_neg hW]

theorem heightEq_holds : PtDict → CodimOne → ExistsRat → CycleOfRat → ArchIntEq → VertEq → PtLen → CurveInt →
    RatRStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → HeightEq II :=
  fun h₃ h₄ h₅ h₆ h₇ hV hPt hC hR II hII => heightEq_of h₃ h₄ h₅ h₆ h₇ hV hPt hC hR II hII

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

open scoped ContDiff Topology

namespace GlobalTheory.CompanionTheory.MPDict.SmoothRep

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

def rt (c : ∀ k, Bk n k) (q : Σ k, Bk n k) : Γ(MP ℤ m n, mchart c) :=
  resG _ (mchart_le c q.1) (pullRatio (prB n q.1) _ (c q.1) le_rfl q.2)

def rtOn (c : ∀ k, Bk n k) (W : (MP ℤ m n).Opens) (h : ∀ k, W ≤ blockChart n k (c k)) (q : Σ k, Bk n k) :
    Γ(MP ℤ m n, W) :=
  pullRatio (prB n q.1) W (c q.1) (h q.1) q.2

theorem closure_ratio (N : ℕ) (i : Fin (N + 1)) : Subring.closure (Set.range (ratio ℤ N i)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨p, rfl⟩ := aeval_ratio_surjective ℤ N i v
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [aeval_C]
    simpa using intCast_mem (Subring.closure (Set.range (ratio ℤ N i))) r
  | add p q hp hq => rw [map_add]; exact add_mem (hp trivial) (hq trivial)
  | mul_X p j hp =>
    rw [map_mul, aeval_X]
    exact mul_mem (hp trivial) (Subring.subset_closure ⟨j, rfl⟩)

theorem eq_top_of_isPushout {R A B C : CommRingCat.{0}} {a : R ⟶ A} {b : R ⟶ B} {f : A ⟶ C} {g : B ⟶ C}
    (H : IsPushout a b f g) (S : Subring C) (hf : ∀ x, f x ∈ S) (hg : ∀ x, g x ∈ S) : S = ⊤ := by
  let ι : CommRingCat.of S ⟶ C := CommRingCat.ofHom S.subtype
  let f' : A ⟶ .of S := CommRingCat.ofHom (f.hom.codRestrict S hf)
  let g' : B ⟶ .of S := CommRingCat.ofHom (g.hom.codRestrict S hg)
  have w : a ≫ f' = b ≫ g' := by
    ext x
    exact congr($(H.w) x)
  let d := H.desc f' g' w
  have e : d ≫ ι = 𝟙 C := H.hom_ext (by rw [H.inl_desc_assoc]; rfl) (by rw [H.inr_desc_assoc]; rfl)
  rw [eq_top_iff]
  intro x _
  have h : ι (d x) = x := congr($e x)
  exact h ▸ (d x).2

theorem mchart_succ {m : ℕ} {n : Fin (m + 2) → ℕ} (c : ∀ k, Bk n k) :
    mchart c = pullback.fst (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ chart ℤ (n 0) (c 0) ⊓
      pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)) ⁻¹ᵁ
        mchart (n := Fin.tail n) (fun k => c k.succ) := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ⟨fun hx => ?_, ?_⟩)
  · exact ⟨Set.mem_iInter.1 hx 0, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k.succ⟩
  · rintro ⟨h0, h1⟩
    refine Set.mem_iInter.2 fun k => ?_
    induction k using Fin.cases with
    | zero => exact h0
    | succ k => exact Set.mem_iInter.1 h1 k

theorem add_one_pow_eq_ringHom_image_add_prime_mul_zero : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) (W : (MP ℤ m n).Opens), W = mchart c →
    ∀ h : ∀ k, W ≤ blockChart n k (c k),
      IsAffineOpen W ∧ Subring.closure (Set.range (rtOn c W h)) = ⊤
  | 0, n, c, W, hW, h => by
    have e : W = (chart ℤ (n 0) (c 0) : (MP ℤ 0 n).Opens) := by
      rw [hW]
      refine TopologicalSpace.Opens.ext (Set.ext fun x => ⟨fun hx => Set.mem_iInter.1 hx 0, fun hx => ?_⟩)
      refine Set.mem_iInter.2 fun k => ?_
      obtain rfl : k = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact hx
    subst e
    refine ⟨isAffineOpen_chart ℤ (n 0) (c 0), ?_⟩
    refine eq_top_iff.2 fun x _ => ?_
    have hx : (x : Γ(PSpace ℤ (n 0), chart ℤ (n 0) (c 0))) ∈
        Subring.closure (Set.range (ratio ℤ (n 0) (c 0))) := by
      rw [closure_ratio]
      trivial
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨j, rfl⟩
    exact ⟨⟨0, j⟩, (resG_self _ _)⟩
  | m + 1, n, c, W, hW, h => by
    obtain ⟨ha, hc⟩ := add_one_pow_eq_ringHom_image_add_prime_mul_zero m (Fin.tail n) (fun k => c k.succ) _ rfl (mchart_le _)
    have H := IsPullback.of_hasPullback (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))
    obtain ⟨h1, h2⟩ := GlobalTheory.Conormal.isAffineOpen_and_isPushout H (U := ⊤) (isAffineOpen_top _) ha
      (isAffineOpen_chart ℤ (n 0) (c 0)) le_top le_top
    obtain rfl := hW.trans (mchart_succ c)
    refine ⟨h1, eq_top_of_isPushout h2 _ (fun x => ?_) (fun x => ?_)⟩
    · have hle : Subring.closure (Set.range (ratio ℤ (n 0) (c 0))) ≤
          (Subring.closure (Set.range (rtOn c _ h))).comap (Scheme.Hom.appLE
            (pullback.fst (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n))) (chart ℤ (n 0) (c 0)) _ inf_le_left).hom := by
        rw [Subring.closure_le]
        rintro _ ⟨j, rfl⟩
        exact Subring.subset_closure ⟨⟨0, j⟩, rfl⟩
      exact hle (closure_ratio (n 0) (c 0) ▸ Subring.mem_top x)
    · have hle : Subring.closure (Set.range (rtOn (n := Fin.tail n) (fun k => c k.succ) _ (mchart_le _))) ≤
          (Subring.closure (Set.range (rtOn c _ h))).comap (Scheme.Hom.appLE
            (pullback.snd (toSpecBase ℤ (n 0)) (mpStr ℤ m (Fin.tail n)))
            (mchart (n := Fin.tail n) (fun k => c k.succ)) _ inf_le_right).hom := by
        rw [Subring.closure_le]
        rintro _ ⟨⟨k, j⟩, rfl⟩
        refine Subring.subset_closure ⟨⟨k.succ, j⟩, ?_⟩
        exact (appLE_pullRatio _ _).symm
      exact hle (hc ▸ Subring.mem_top x)

theorem gen (m : ℕ) (n : Fin (m + 1) → ℕ) (c : ∀ k, Bk n k) :
    IsAffineOpen (mchart c) ∧ Subring.closure (Set.range (rt c)) = ⊤ := by
  obtain ⟨h₁, h₂⟩ := add_one_pow_eq_ringHom_image_add_prime_mul_zero m n c _ rfl (mchart_le c)
  refine ⟨h₁, ?_⟩
  rw [← h₂]
  congr 2
  funext q
  exact resG_pullRatio _

theorem contDiffAt_zpow_of_ne' {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (h0 : f x ≠ 0) (a : ℤ) : ContDiffAt ℝ ∞ (fun y => f y ^ a) x := by
  obtain ⟨b, rfl | rfl⟩ := a.eq_nat_or_neg
  · simpa only [zpow_natCast] using hf.pow b
  · simp only [zpow_neg, zpow_natCast]
    exact (hf.pow b).inv (pow_ne_zero b h0)

theorem contDiffOn_of_holo {ι : Type} [Fintype ι] {B : Set (ι → ℂ)} (hB : IsOpen B) {f : (ι → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f B) : ContDiffOn ℝ ∞ f B := by
  let e : (ι → ℂ) ≃L[ℂ] (Fin (Module.finrank ℂ (ι → ℂ)) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have ha : AnalyticOnNhd ℂ f B := by
    intro z hz
    have h := ReciprocityTheory.AnForm.Osgood.osgood _ (e.symm ⁻¹' B) (f ∘ e.symm)
      (hB.preimage e.symm.continuous)
      (hf.comp e.symm.differentiableOn (fun _ h => h)) (e z) (by simpa using hz)
    have h2 := h.comp (e.analyticAt z)
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hc : ContDiffOn ℂ ∞ f B := (ha.contDiffOn hB.uniqueDiffOn).of_le le_top
  exact hc.restrict_scalars ℝ

theorem mem_mchart {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : IsUnder y z)
    {c : ∀ k, Bk n k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) : y ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) := by
  refine mem_ptsIn.2 (Set.mem_iInter.2 fun k => ?_)
  exact mem_ptsIn.1 ((H k (c k)).1.2 (hc k))

theorem ev_rt {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : IsUnder y z)
    {c : ∀ k, Bk n k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (q : Σ k, Bk n k) :
    CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) (rt c q) y = z q / z ⟨q.1, c q.1⟩ := by
  rw [rt, CxPts.ev_res _ (mem_mchart H hc)]
  exact (H q.1 (c q.1)).2 q.2 ((H q.1 (c q.1)).1.2 (hc q.1))

theorem differentiableOn_ev {c : ∀ k, Bk n k} {s : ((Σ k, Bk n k) → ℂ) → CxPts (mpStr ℤ m n) σ₀}
    (hs : ∀ z, (∀ k, z ⟨k, c k⟩ ≠ 0) → IsUnder (s z) z) (a : Γ(MP ℤ m n, mchart c)) :
    DifferentiableOn ℂ (CxPts.ev (mpStr ℤ m n) σ₀ (mchart c) a ∘ s) {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := by
  have hin : ∀ z, (∀ k, z ⟨k, c k⟩ ≠ 0) → s z ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart c) :=
    fun z hz => mem_mchart (hs z hz) hz
  have ha : a ∈ Subring.closure (Set.range (rt c)) := by
    rw [(gen m n c).2]; trivial
  induction ha using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    have hd : DifferentiableOn ℂ (fun z : (Σ k, Bk n k) → ℂ => z q * (z ⟨q.1, c q.1⟩)⁻¹)
        {z | ∀ k, z ⟨k, c k⟩ ≠ 0} := fun z hz =>
      ((differentiableAt_apply (𝕜 := ℂ) q z).mul
        ((differentiableAt_apply (𝕜 := ℂ) _ z).inv (hz q.1))).differentiableWithinAt
    exact hd.congr fun z hz => (ev_rt (hs z hz) hz q).trans (div_eq_mul_inv _ _)
  | zero =>
    exact (differentiableOn_const 0).congr fun z hz => by
      simp only [Function.comp_apply, ev_eq (hin z hz), map_zero]
  | one =>
    exact (differentiableOn_const 1).congr fun z hz => by
      simp only [Function.comp_apply, ev_eq (hin z hz), map_one]
  | add x y _ _ hx hy =>
    exact (hx.add hy).congr fun z hz => by
      simp only [Function.comp_apply, Pi.add_apply, ev_add]
  | neg x _ hx =>
    exact hx.neg.congr fun z hz => by
      simp only [Function.comp_apply, Pi.neg_apply, ev_eq (hin z hz), map_neg]
  | mul x y _ _ hx hy =>
    exact (hx.mul hy).congr fun z hz => by
      simp only [Function.comp_apply, Pi.mul_apply, ev_mul]

theorem isSmoothHerm_of_isHermRep (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n))
    (A : Geo.HermLine (Bk n)) (hA : IsHermRep M A) : Geo.IsSmoothHerm A := by
  obtain ⟨u, -, -, hu⟩ := hA
  intro z₀ hz₀
  refine ContDiffAt.contDiffWithinAt ?_
  choose c hc using hz₀
  let T : Set ((Σ k, Bk n k) → ℂ) := {z | ∀ k, z ⟨k, c k⟩ ≠ 0}
  have hT : IsOpen T := by
    have : T = ⋂ k, {z | z ⟨k, c k⟩ ≠ 0} := by ext z; simp [T]
    rw [this]
    exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (continuous_apply _) continuous_const
  have hmc : ∀ z ∈ T, ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := fun z hz k => ⟨c k, hz k⟩
  haveI : Nonempty (CxPts (mpStr ℤ m n) σ₀) :=
    ⟨(Under.existsUnique_isUnder m n z₀ (hmc z₀ hc)).exists.choose⟩
  let s : ((Σ k, Bk n k) → ℂ) → CxPts (mpStr ℤ m n) σ₀ := fun z => Classical.epsilon fun y => IsUnder y z
  have hs : ∀ z, (∀ k, z ⟨k, c k⟩ ≠ 0) → IsUnder (s z) z := fun z hz =>
    Classical.epsilon_spec (Under.existsUnique_isUnder m n z (hmc z hz)).exists
  obtain ⟨hcont, hhol⟩ := holo_of_affine (gen m n c).1 hT (fun z hz => mem_mchart (hs z hz) hz)
    (differentiableOn_ev hs)
  have hsc : ContinuousAt s z₀ := hcont.continuousAt (hT.mem_nhds hc)
  obtain ⟨i, hi⟩ := exists_mem_ptsIn M.isLB.cover (s z₀)

  have hev : ∀ (W : (MP ℤ m n).Opens) (f : Γ(MP ℤ m n, W)), s z₀ ∈ ptsIn (mpStr ℤ m n) σ₀ W →
      ContDiffAt ℝ ∞ (fun z => CxPts.ev (mpStr ℤ m n) σ₀ W f (s z)) z₀ := by
    intro W f hW
    have hO : T ∩ s ⁻¹' ptsIn (mpStr ℤ m n) σ₀ W ∈ 𝓝 z₀ :=
      Filter.inter_mem (hT.mem_nhds hc) (hsc.preimage_mem_nhds ((isOpen_ptsIn W).mem_nhds hW))
    obtain ⟨B, hBs, hBo, hzB⟩ := mem_nhds_iff.1 hO
    exact (contDiffOn_of_holo hBo ((hhol W f).mono hBs)).contDiffAt (hBo.mem_nhds hzB)

  have hφ : ContDiffAt ℝ ∞ (fun z => (M.φ σ₀).φ i (s z)) z₀ := by
    obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := M.cInf σ₀ i (s z₀) hi
    have hg : ContDiffAt ℝ ∞ (fun z a => CxPts.ev (mpStr ℤ m n) σ₀ W (g a) (s z)) z₀ :=
      contDiffAt_pi.2 fun a => hev W (g a) h₁
    exact ((h₄.contDiffAt (h₂.mem_nhds h₃)).comp z₀ hg).congr_of_eventuallyEq (hsc.eventually h₅)
  have hiU : s z₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c) :=
    mem_ptsIn_inf.2 ⟨hi, mem_mchart (hs z₀ hc) hc⟩
  have hU : ContDiffAt ℝ ∞ (fun z => ‖CxPts.ev (mpStr ℤ m n) σ₀ (M.B.U i ⊓ mchart c)
      (u i c : Γ(MP ℤ m n, M.B.U i ⊓ mchart c)) (s z)‖) z₀ :=
    (hev _ _ hiU).norm ℝ (ev_ne_zero hiU (u i c).isUnit)
  have hP : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ∏ k, ‖z ⟨k, c k⟩‖ ^ A.a k) z₀ := by
    refine contDiffAt_prod fun k _ => ?_
    have hn : ContDiffAt ℝ ∞ (fun z : (Σ k, Bk n k) → ℂ => ‖z ⟨k, c k⟩‖) z₀ :=
      (contDiff_apply ℝ ℂ (⟨k, c k⟩ : Σ k, Bk n k)).contDiffAt.norm ℝ (hc k)
    exact contDiffAt_zpow_of_ne' hn (norm_ne_zero_iff.2 (hc k)) (A.a k)
  have hE : ContDiffAt ℝ ∞ (fun z => Real.exp ((M.φ σ₀).φ i (s z) / 2)) z₀ :=
    (hφ.div_const 2).exp
  refine ((hP.mul hU).mul hE).congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ z in 𝓝 z₀, z ∈ T ∧ s z ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U i) :=
    (hT.eventually_mem hc).and (hsc.eventually ((isOpen_ptsIn _).eventually_mem hi))
  filter_upwards [hmem] with z hz
  exact hu i c (s z) z (hs z hz.1) (mem_ptsIn_inf.2 ⟨hz.2, mem_mchart (hs z hz.1) hz.1⟩)

end GlobalTheory.CompanionTheory.MPDict.SmoothRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphyIntegralParam
section
open MeasureTheory Filter Topology
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.RgAds

theorem holomorphy_integral_param : HI := by
  intro X _ m U F hU hmeas hdiff hdom
  refine (GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := m)
    (F := fun x s => F s x) hU hmeas (Eventually.of_forall hdiff) ?_).1
  intro s₀ hs₀
  obtain ⟨g, hg, hev⟩ := hdom s₀ hs₀
  exact ⟨{s | ∀ x, ‖F s x‖ ≤ g x}, hev, g, hg, ae_of_all _ fun x s hs => hs x⟩

end GlobalTheory.CompanionTheory.RgAds
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealLatticeToAddSubgroupEqIdealSub
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.EllipticDict

theorem idealLattice_toAddSubgroup_eq_idealSub :
    ∀ {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (I : FractionalIdeal (𝓞 K)⁰ K),
      (GroundTheory.Global.Elliptic.idealLattice (algebraMap K ℂ) I).toAddSubgroup =
        GlobalTheory.EllipticCM.idealSub I := by
  intro K _ _ _ I
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end GlobalTheory.CompanionTheory.EllipticDict
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetFixedVectorLiftStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_fixed_vector_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsAdmissible π → ∀ w ∈ fixed (jac (stdBlocks d hd) π) (KM k N J d hd), ∃ v : fixed π J, (Submodule.Quotient.mk (v : V) : Jacquet π (unipRad k (stdBlocks d hd))) = w := by
  first | exact @GlobalTheory.CompanionTheory.JacquetLemma.jacquet_surjective | exact GlobalTheory.CompanionTheory.JacquetLemma.jacquet_surjective | (intros; apply GlobalTheory.CompanionTheory.JacquetLemma.jacquet_surjective <;> assumption)
end

