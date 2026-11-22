import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3250
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3277
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleEffectiveKltInductionStart
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

namespace GlobalTheory.PairStep

set_option maxHeartbeats 1000000 in

theorem exists_ample_eff_kltAt_start : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (hN₀ : N₀.IsLB) (β : ℚ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → 0 < β →
      ∃ (A F : CartierDiv X) (a : ℕ), IsAmpleLB (toLB A) ∧ 0 < a ∧ toPic F = a • cls N₀ hN₀ ∧
        ∃ (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X), 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ lam < β ∧
          (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧ ∀ y, KltAt p n (Δ + qWeil D₀ m') y := by
  intro hPr X _ _ _ p n hp hn
  letI := algebraΓOfHom p
  intro Δ r N₀ hN₀ β hΔ hklt hr hnef hbig hβ
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hp
  obtain ⟨A, hA⟩ := toPic_surjective (cls H hH.isLB)
  have hAamp : IsAmpleLB (toLB A) := by
    rw [toPic_apply] at hA
    exact hH.of_lbIso (isLB_toLB A) ((cls_eq_iff (isLB_toLB A) hH.isLB).1 hA)
  obtain ⟨a, E₀, ha, hE₀, hKod⟩ := GlobalTheory.KodairaLemma.exists_nsmul_cls_eq_add_toPic_of_isBig ℂ X p hp N₀ (toLB A) hbig hAamp
  obtain ⟨F, hF⟩ := toPic_surjective (a • cls N₀ hN₀)
  obtain ⟨m, G, hm, hG⟩ := GlobalTheory.T.exists_logCanonicalMultiple_of_globally_klt X p n hp hn Δ hΔ hklt
  have hB : IsQCart (qWeil E₀ 1) := ⟨1, E₀, one_pos, hE₀, rfl⟩
  obtain ⟨c₀, hc₀, hc₀k⟩ := GlobalTheory.T.exists_pos_klt_add_smul_effective_divisor hPr X p n hp hn Δ m G (qWeil E₀ 1) hm hG hklt hB
  set q : ℕ := ⌈1 / c₀ + (a : ℚ) * r / β⌉₊ + 1 with hq
  have hqpos : (0 : ℚ) < q := by positivity
  have hqgt : 1 / c₀ + (a : ℚ) * r / β < q := by
    have := Nat.le_ceil (1 / c₀ + (a : ℚ) * r / β)
    rw [hq]; push_cast; linarith
  have hara : (0 : ℚ) ≤ (a : ℚ) * r / β := by positivity
  have hinv : (0 : ℚ) < 1 / c₀ := by positivity
  have h1 : 1 / (q : ℚ) ≤ c₀ := by
    rw [div_le_iff₀ hqpos]
    have : 1 / c₀ < q := by linarith
    rw [div_lt_iff₀ hc₀] at this
    linarith
  have h2 : (a : ℚ) * r / q < β := by
    have : (a : ℚ) * r / β < q := by linarith
    rw [div_lt_iff₀ hβ] at this
    rw [div_lt_iff₀ hqpos]
    linarith
  refine ⟨A, F, a, hAamp, ha, hF, (a : ℚ) * r / q, 1 / q, q, E₀, by omega, hE₀, by positivity, h2, ?_, ?_⟩
  · intro C hC
    have e1 := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (lbPow N₀ a) (toLB A) (toLB E₀)
      (isLB_lbPow hN₀ a) (isLB_toLB A) (isLB_toLB E₀) 1 1 C hC (by
        rw [cls_lbPow hN₀ a, one_smul, one_smul, ← toPic_apply]
        exact hKod)
    have e2 := interNumRed_of_cls_eq_nsmul_add ℂ X p hp (lbPow N₀ a) N₀ N₀
      (isLB_lbPow hN₀ a) hN₀ hN₀ a 0 C hC (by rw [cls_lbPow hN₀ a, zero_smul, add_zero])
    have e3 : (interNumRed ℂ C ![toLB E₀] : ℚ) = a * interNumRed ℂ C ![N₀] - interNumRed ℂ C ![toLB A] := by
      have : interNumRed ℂ C ![toLB E₀] = a * interNumRed ℂ C ![N₀] - interNumRed ℂ C ![toLB A] := by
        rw [e2] at e1; push_cast at e1; linarith
      exact_mod_cast this
    rw [e3]
    have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp
  · intro y
    have k := (kltAt_lcAt_of_le_coeff X p n hp hn Δ (qWeil E₀ 1) (1 / q) c₀ y hB h1).1 (hc₀k y)
    convert k using 2
    funext z
    simp only [qWeil, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, div_one]
    ring

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBaseChangeStableSectionBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.HomFixLocBasis

theorem isIso_compare : ∀ {S S' : Scheme.{0}} (u : S' ⟶ S) (A : Over S) (Ag : Over S') (φ : Ag.left ⟶ A.left), IsPullback φ Ag.hom A.hom u → ∀ (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S), x ≫ u = y → ∀ (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left), h ≫ (snd (Over.mk y) A).left = (snd (Over.mk x) Ag).left ≫ φ → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → IsIso h := by
  intro S S' u A Ag φ hφ R _ x y hxy h h1 h2
  subst hxy
  have P := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (Over.mk x)).paste_horiz hφ
  have Q : IsPullback (snd (Over.mk (x ≫ u)) A).left (fst (Over.mk (x ≫ u)) A).left A.hom (x ≫ u) :=
    GlobalTheory.AbLaw.SecBC.isPullback_snd A (Over.mk (x ≫ u))
  have P' : IsPullback ((snd (Over.mk x) Ag).left ≫ φ) (fst (Over.mk x) Ag).left A.hom (x ≫ u) := P
  have e : h = (P'.isoIsPullback _ _ Q).hom :=
    Q.hom_ext (by rw [h1]; exact (IsPullback.isoIsPullback_hom_fst _ _ P' Q).symm) (by rw [h2]; exact (IsPullback.isoIsPullback_hom_snd _ _ P' Q).symm)
  rw [e]
  infer_instance

theorem exists_basicOpen_le {Rg : Type} [CommRing Rg] (V : (Sp Rg).Opens) (p : Sp Rg) (hpV : p ∈ V) :
    ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧
      ((PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Rg)) ⊆ (V : Set (Sp Rg))) := by
  have hVo : IsOpen (X := PrimeSpectrum Rg) (V : Set (Sp Rg)) := V.isOpen
  have hpV' : (p : PrimeSpectrum Rg) ∈ (V : Set (Sp Rg)) := hpV
  obtain ⟨W, ⟨f, rfl⟩, h1, h2⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := Rg)).exists_subset_of_mem_open
    (a := (p : PrimeSpectrum Rg)) (u := ((V : Set (Sp Rg)) : Set (PrimeSpectrum Rg))) hpV' hVo
  exact ⟨f, h1, h2⟩

theorem exists_factor_away {Rg : Type} [CommRing Rg] (V : (Sp Rg).Opens) (f g : Rg)
    (hfV : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Rg)) ⊆ (V : Set (Sp Rg)))
    (hg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ∃ uV : Sp (Localization.Away g) ⟶ V.toScheme, uV ≫ V.ι = spMap (algebraMap Rg (Localization.Away g)) := by
  have hu : Set.range (spMap (algebraMap Rg (Localization.Away g))) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have h1 : PrimeSpectrum.comap (algebraMap Rg (Localization.Away g)) x ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum Rg)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact ⟨x, rfl⟩
    exact hfV (hg h1)
  exact ⟨_, IsOpenImmersion.lift_fac V.ι _ hu⟩

theorem secBasis_of_factor {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (k : ℕ) (V : (Sp Rg).Opens) (m : ℕ)
    (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)))
    (hb : ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) V).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤)
    {S' : Scheme.{0}} (u : S' ⟶ Sp Rg) (uV : S' ⟶ V.toScheme) (huV : uV ≫ V.ι = u)
    (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (hφ : IsGrpPullback Ag A u φ) :
    ∃ (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver S') ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver S') ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤ := by
  have hAgw : φ ≫ A.hom = Ag.hom ≫ u := hφ.1.w
  have hw : ((snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ) ≫ A.hom =
      ((fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV) ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by
    have e := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (overRes (T := baseOver S') ⊤)).w
    simp only [Category.assoc, hAgw]
    rw [← Category.assoc, e]
    simp [overRes, baseOver, huV]
  obtain ⟨H, hH1, hH2⟩ : ∃ H : (overRes (T := baseOver S') ⊤ ⊗ Ag).left ⟶ (overRes (T := baseOver (Sp Rg)) V ⊗ A).left,
      H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left = (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ ∧
      H ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left = (fst (overRes (T := baseOver S') ⊤) Ag).left ≫ (⊤ : S'.Opens).ι ≫ uV :=
    ⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw⟩
  have hc : ∀ _ : Fin 1, (snd (overRes (T := baseOver S') ⊤) Ag).left ≫ φ = H ≫ (snd (overRes (T := baseOver (Sp Rg)) V) A).left :=
    fun _ => hH1.symm
  refine ⟨fun i => GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left)
    (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i), ?_⟩
  intro R _ t b' hb'
  obtain ⟨t', ht'⟩ : ∃ t' : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) V).left, t' = t ≫ (⊤ : S'.Opens).ι ≫ uV := ⟨_, rfl⟩
  choose b'' hb'' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec A L (k : ℤ) (homAt t') (b i)
  have hB := hb R t' b'' hb''
  have hxy : (t ≫ (overRes (T := baseOver S') ⊤).hom) ≫ u = t' ≫ (overRes (T := baseOver (Sp Rg)) V).hom := by
    rw [ht']
    simp [overRes, baseOver, huV]
  have hw2 : ((snd (baseAt t) Ag).left ≫ φ) ≫ A.hom = (fst (baseAt t) Ag).left ≫ (baseAt t').hom := by
    have e := (GlobalTheory.AbLaw.SecBC.isPullback_snd Ag (baseAt t)).w
    simp only [Category.assoc, hAgw]
    rw [← Category.assoc, e]
    simp [baseAt, overRes, baseOver, ht', huV]
  obtain ⟨h, hh1, hh2⟩ : ∃ h : (baseAt t ⊗ Ag).left ⟶ (baseAt t' ⊗ A).left,
      h ≫ (snd (baseAt t') A).left = (snd (baseAt t) Ag).left ≫ φ ∧
      h ≫ (fst (baseAt t') A).left = (fst (baseAt t) Ag).left :=
    ⟨_, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_fst _ _ hw2, (GlobalTheory.AbLaw.SecBC.isPullback_snd A _).lift_snd _ _ hw2⟩
  have hc' : ∀ _ : Fin 1, (snd (baseAt t) Ag).left ≫ φ = h ≫ (snd (baseAt t') A).left := fun _ => hh1.symm
  refine GlobalTheory.T.sectionBases_transfer_totalSpaceIso A Ag φ L hL (k : ℤ) R _ _ h hc' (isIso_compare u A Ag φ hφ.1 R _ _ hxy h hh1 hh2) hh2 m b'' b' ?_ hB.1 hB.2
  have hcomp : (homAt t ▷ Ag).left ≫ H = h ≫ (homAt t' ▷ A).left := by
    apply (GlobalTheory.AbLaw.SecBC.isPullback_snd A (overRes (T := baseOver (Sp Rg)) V)).hom_ext
    · rw [Category.assoc, hH1, Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, ← Category.assoc, ← GlobalTheory.AbLaw.SecBC.snd_eq, hh1]
    · have e1 := GlobalTheory.AbLaw.SecBC.fst_eq Ag (homAt t)
      have e2 := GlobalTheory.AbLaw.SecBC.fst_eq A (homAt t')
      calc ((homAt t ▷ Ag).left ≫ H) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left
            = ((homAt t ▷ Ag).left ≫ (fst (overRes (T := baseOver S') ⊤) Ag).left) ≫ (⊤ : S'.Opens).ι ≫ uV := by
              rw [Category.assoc, hH2, Category.assoc]
        _ = (fst (baseAt t) Ag).left ≫ t ≫ (⊤ : S'.Opens).ι ≫ uV := by
              rw [e1]
              try simp [homAt]
        _ = (h ≫ (homAt t' ▷ A).left) ≫ (fst (overRes (T := baseOver (Sp Rg)) V) A).left := by
              rw [Category.assoc, e2, reassoc_of% hh2, ht']
              try simp [homAt]
  intro i
  apply GlobalTheory.SecTwist.sec_ext_loc
  intro y
  obtain ⟨j, hj⟩ : ∃ j, y ∈ (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j :=
    exists_chart (LB.isLB_linComb (LB.isLB_pull hL φ) _ _ : (LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).IsLB) y
  refine ⟨j, hj, ?_⟩
  have hj1 := chart_le_res Ag (L.pull φ) (homAt t ▷ Ag) (whiskerRight_snd _ _) (k : ℤ) j hj
  have hj2 : h y ∈ (LPow A L (k : ℤ) (baseAt t')).U (fun k => j k PUnit.unit) := by
    have := (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
      (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc').le j hj
    exact this
  have lhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j) ((b' i).f j) =
      gs ((homAt t ▷ Ag).left ≫ H) y ((LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit))
        ((b i).f (fun k => j k PUnit.unit)) := by
    rw [hb' i j, GlobalTheory.AbLaw.SecBC.gs_rp _ _ (𝟙 _) y hj, Category.id_comp]
    exact GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (overRes (T := baseOver S') ⊤) Ag).left)
      (fun _ : Fin 1 => (snd (overRes (T := baseOver (Sp Rg)) V) A).left) (fun _ => (k : ℤ)) H hc) (b i) (homAt t ▷ Ag).left y j hj1
  have rhs : gs (𝟙 _) y ((LPow Ag (L.pull φ) (k : ℤ) (baseAt t)).U j)
      ((GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
        (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i)).f j) =
      gs (h ≫ (homAt t' ▷ A).left) y ((LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) V)).U (fun k => j k PUnit.unit))
        ((b i).f (fun k => j k PUnit.unit)) := by
    have e1 := GlobalTheory.SecTwist.gs_pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (baseAt t) Ag).left)
        (fun _ : Fin 1 => (snd (baseAt t') A).left) (fun _ => (k : ℤ)) h hc') (b'' i) (𝟙 _) y j hj
    rw [Category.id_comp] at e1
    refine e1.trans ?_
    erw [hb'' i (fun k => j k PUnit.unit)]
    exact GlobalTheory.AbLaw.SecBC.gs_rp _ _ h y hj2 _
  rw [lhs, rhs, hcomp]

theorem exists_basicOpen_secBasis : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.Rigidified A L → Out.RelAmple A L → ∀ k : ℕ, 1 ≤ k → ∀ p : Sp Rg, ∃ f : Rg, p ∈ PrimeSpectrum.basicOpen f ∧ ∀ g : Rg, PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f → ∀ (Ag : Over (Sp (Localization.Away g))) [GrpObj Ag] [IsCommMonObj Ag] (φ : Ag.left ⟶ A.left), IsGrpPullback Ag A (spMap (algebraMap Rg (Localization.Away g))) φ → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (overRes (T := baseOver (Sp (Localization.Away g))) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp (Localization.Away g))) ⊤).left) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) (k : ℤ) (baseAt t))), (∀ i, IsPullSec Ag (L.pull φ) (k : ℤ) (homAt t ▷ Ag) (whiskerRight_snd (homAt t) Ag) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) (k : ℤ) (baseAt t))) = ⊤) := by
  intro Rg _ _ A _ _ L hAb hL hRig hAmp k hk p
  obtain ⟨V, hpV, m, b, hb⟩ := GlobalTheory.AmpleSecBC.secBaseChange_relAmple (Sp Rg) A L hAb hL hRig hAmp k hk p
  have hx := exists_basicOpen_le (Rg := Rg) V p hpV
  refine ⟨hx.choose, hx.choose_spec.1, fun g hg Ag _ _ φ hφ => ⟨m, ?_⟩⟩
  have hu := exists_factor_away V _ g hx.choose_spec.2 hg
  exact secBasis_of_factor A L hL k V m b hb _ hu.choose hu.choose_spec Ag φ hφ

end GlobalTheory.HomFixLocBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoproductThickeningAffineLiftPoincare
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.CopPoincare

theorem isNilpotent_of_isNilDP {B : Type} [CommRing B] {J : Ideal B} {δ : DividedPowers J} (h : IsNilDP δ) :
    IsNilpotent J := by
  obtain ⟨N, hN⟩ := (isDPNilpotent_iff_exists_isLevel δ).1 h
  have key : ∀ (m : ℕ), ∀ x ∈ J ^ m, ∀ l : List (ℕ × B), (∀ p ∈ l, p.2 ∈ J) → N ≤ m + (l.map Prod.fst).sum →
      x * (l.map fun p ↦ δ.dpow p.1 p.2).prod = 0 := by
    intro m
    induction m with
    | zero =>
      intro x _ l hl hs
      rw [(isLev_iff_prod δ N).1 hN l hl (by simpa using hs), mul_zero]
    | succ m ih =>
      intro x hx l hl hs
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ by rw [add_mul, ha, hb, add_zero])
      have := ih a ha ((1, b) :: l) (by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hb
        · exact hl p hp) (by simp only [List.map_cons, List.sum_cons]; omega)
      simpa [δ.dpow_one hb, mul_assoc] using this
  refine ⟨N, ?_⟩
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  intro x hx
  simpa using key N x hx [] (by simp) (by simp)

theorem exists_cop_qAt : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) → ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (G : Thick D.κ D.t) (l : T ⟶ G) (r : Λ.L.obj U ⟶ G), IsCop (n + 1) l r ∧ (KK D.κ D.t).QAt l := by
  intro D Λ n U T hT hU
  obtain ⟨F, G, u, q, r, hu, hF, hq, hJ, hc⟩ := GlobalTheory.T.exists_coproductThickening_quotient_freeThickening D Λ n U T hT hU
  obtain ⟨h1, -, -, -⟩ := GlobalTheory.T.hom_spec_points_levels D Λ
  refine ⟨G, u ≫ q, r, hc, ?_⟩
  haveI := D.sec_smooth U.unop
  have hker : RingHom.ker (q.φ : F.B →+* G.B) ≤ F.J := fun b hb ↦ hJ b (by
    rw [show q.φ b = 0 from hb]; exact G.J.zero_mem)
  have hnil : IsNilpotent (RingHom.ker (q.φ : F.B →+* G.B)) := by
    obtain ⟨N, hN⟩ := isNilpotent_of_isNilDP F.nil
    refine ⟨N, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
    exact Ideal.pow_right_mono hker N
  let y : Sec D.s U.unop.1 →ₐ[D.R] G.B := r.φ.comp (Λ.e U : Sec D.s U.unop.1 →ₐ[D.R] (Λ.L.obj U).B)
  let y' : Sec D.s U.unop.1 →ₐ[D.R] F.B := Algebra.FormallySmooth.liftOfSurjective y q.φ hq hnil
  have hy' : ∀ a, q.φ (y' a) = y a := fun a ↦ Algebra.FormallySmooth.liftOfSurjective_apply y q.φ hq hnil a
  have hbij : Function.Bijective q.φ₀ := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ ?_, fun c ↦ ?_⟩
    · obtain ⟨b, rfl⟩ := F.surj b
      rw [q.comm, G.ker] at hb
      exact (F.ker b).2 (hJ b hb)
    · obtain ⟨c, rfl⟩ := G.surj c
      obtain ⟨b, rfl⟩ := hq c
      exact ⟨F.π b, q.comm b⟩
  haveI : IsIso (spMap q.φ₀) :=
    (inferInstance : IsIso (Spec.map (RingEquiv.ofBijective q.φ₀ hbij).toCommRingCatIso.hom))
  have hy := (h1 U G y).2 ⟨r, fun _ ↦ rfl⟩
  have hpt : spMap (F.π.comp (y' : Sec D.s U.unop.1 →+* F.B)) ≫ affPt D.s U.unop = F.x ≫ D.i := by
    rw [← cancel_epi (spMap q.φ₀), ← Category.assoc, ← Cris.spMap_comp, ← Category.assoc, q.pt, ← hy]
    congr 2
    ext a
    exact (q.comm _).trans (congrArg G.π (hy' a))
  obtain ⟨b', hb'⟩ := (h1 U F y').1 hpt
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := hc.2 F hF u b'
  have hbq : b' ≫ q = r := Thick.hom_ext fun b ↦ by
    obtain ⟨a, rfl⟩ := (Λ.e U).surjective b
    rw [Thick.comp_φ, hb', hy']; rfl
  have hsq : s ≫ q = 𝟙 G := by
    obtain ⟨c, -, huniq⟩ := hc.2 G hc.1 (u ≫ q) r
    refine (huniq _ ⟨?_, ?_⟩).trans (huniq _ ⟨Category.comp_id _, Category.comp_id _⟩).symm
    · rw [← Category.assoc, hs1]
    · rw [← Category.assoc, hs2, hbq]
  exact (GlobalTheory.CxCoh.QAtFormal.qAt_formal _ (KK D.κ D.t)).2.2 T G F (u ≫ q) s q hsq (by rw [hs1]; exact hu)

end GlobalTheory.PDForm.CopPoincare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingSplitPrimeGridLocalTensorPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB alpha beta blk)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf HasExp SplitsFully)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_embedding_splitPrime_gridLocalTensorPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (v : HeightOneSpectrum (𝓞 D.host.F)), (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) →
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → splitPrime τ = w := by
  first | exact @GlobalTheory.LocPlTau.exists_splitPrime_locPl | exact GlobalTheory.LocPlTau.exists_splitPrime_locPl | (intros; apply GlobalTheory.LocPlTau.exists_splitPrime_locPl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedPullbackHomSchemeOfSectionBases
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

noncomputable section

namespace GlobalTheory.HomFixGlob

open TopologicalSpace in

theorem lc_props {Rg : Type} [CommRing Rg] [IsNoetherianRing Rg] {N : ℕ} {X H : Scheme.{0}}
    (c : X ⟶ Sp (MvPolynomial (Fin N) Rg)) (i : H ⟶ X) [IsClosedImmersion c] [IsOpenImmersion i] :
    QuasiCompact (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) ∧
    IsSeparated (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) ∧
    LocallyOfFiniteType (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) := by
  refine ⟨?_, inferInstance, ?_⟩
  · have h1 : NoetherianSpace (Sp (MvPolynomial (Fin N) Rg)) :=
      inferInstanceAs (NoetherianSpace (PrimeSpectrum (MvPolynomial (Fin N) Rg)))
    have h2 : NoetherianSpace H :=
      ((i ≫ c).isEmbedding).isInducing.noetherianSpace
    exact (quasiCompact_iff_compactSpace _).2 inferInstance
  · have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg)))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
      show (algebraMap Rg (MvPolynomial (Fin N) Rg)).FiniteType
      exact RingHom.finiteType_algebraMap.2 inferInstance
    infer_instance

theorem exists_homFixRep_of_secBases : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Rigidified A L → Rigidified B M → RelAmple A L → 1 ≤ k → VeryAmpleAt B M k → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow A L (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow A L (k : ℤ) (baseAt t))), (∀ i, IsPullSec A L (k : ℤ) (homAt t ▷ A) (whiskerRight_snd (homAt t) A) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L (k : ℤ) (baseAt t))) = ⊤) → (∃ (m : ℕ) (b : Fin m → LB.Sec (LPow B M (k : ℤ) (overRes (T := baseOver (Sp Rg)) ⊤))), ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ (overRes (T := baseOver (Sp Rg)) ⊤).left) (b' : Fin m → LB.Sec (LPow B M (k : ℤ) (baseAt t))), (∀ i, IsPullSec B M (k : ℤ) (homAt t ▷ B) (whiskerRight_snd (homAt t) B) (b i) (b' i)) → LinearIndependent Γ((baseAt t).left, ⊤) (fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) ∧ Submodule.span Γ((baseAt t).left, ⊤) (Set.range fun i => (SecM.ofSec B (b' i) : SecM B M (k : ℤ) (baseAt t))) = ⊤) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro Rg _ _ A B _ _ _ _ L M k hA hB hL hM rA rM aL hk vM bA bB
  obtain ⟨N, X, c, H, i, AH, _, BH, _, φA, φB, Φ, hc, hi, pA, pB, hΦ, hiso, hrep⟩ :=
    GlobalTheory.T.exists_locallyClosed_represents_fixedPullback_homs Rg A B L M k hA hB hL hM rA rM aL hk vM bA bB
  obtain ⟨q1, q2, q3⟩ := lc_props c i
  exact ⟨HomFixRep.mk H (i ≫ c ≫ Spec.map (CommRingCat.ofHom (algebraMap Rg (MvPolynomial (Fin N) Rg))))
    AH BH φA φB pA pB Φ hΦ hiso (GlobalTheory.T.homFixedPullbackRep_of_affineTests _ A B L M hL hM H _ AH BH φA φB Φ pA pB hrep), q1, q2, q3⟩

end GlobalTheory.HomFixGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_bundle : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl := by
  first | exact @GlobalTheory.FlagExist.main | exact GlobalTheory.FlagExist.main | (intros; apply GlobalTheory.FlagExist.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverAdditiveFamilyEqLambdaStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flatCover_additiveFamily_eq_lambda : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left) (hN : Fam A N), ∃ (H : Over (Sp R)) (h : H ⟶ T) (x : H ⟶ A), Flat h.left ∧ Surjective h.left ∧ QuasiCompact h.left ∧ (∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H), evc hN.isLB a (y ≫ h) = GlobalTheory.CechPic.pull (a * (y ≫ x)).left (cls L hL) - GlobalTheory.CechPic.pull a.left (cls L hL) - GlobalTheory.CechPic.pull (y ≫ x).left (cls L hL) + GlobalTheory.CechPic.pull (1 : Y ⟶ A).left (cls L hL)) := by
  first | exact @GlobalTheory.DualCover.exists_cover | exact GlobalTheory.DualCover.exists_cover | (intros; apply GlobalTheory.DualCover.exists_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyWeightsBoundedDifferenceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fubiniStudyWeights_bounded_difference : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, 1 ≤ n → ∃ u : SmFn p, IsCan P e n x u ∧ ∀ σ y, |u.u σ y| ≤ B := by
  first | exact @GlobalTheory.HSAmp.exists_isCan_bdd | exact GlobalTheory.HSAmp.exists_isCan_bdd | (intros; apply GlobalTheory.HSAmp.exists_isCan_bdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvertibleSectionValuationNonnegStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invertible_section_valuation_nonneg : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∃ (u u' : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), u ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (GlobalTheory.AllWt.exOf (T.Q.Dw j) 0 1) ∧ t ≠ 0 ∧ u * u' = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v u' := by
  first | exact @GlobalTheory.KeyInvInt.exists_inv_key_integral | exact GlobalTheory.KeyInvInt.exists_inv_key_integral | (intros; apply GlobalTheory.KeyInvInt.exists_inv_key_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledSemiAbelianCoverFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelledSemiAbelianCover_finite_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))) (lab : Labels D₁.toPre A), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ OneTrait D₁.toPre A lab ∧ GalEqN n lab := by
  first | exact @GlobalTheory.Mum.exists_desc_labels | exact GlobalTheory.Mum.exists_desc_labels | (intros; apply GlobalTheory.Mum.exists_desc_labels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodFormAutomorphismUnitaryLabellingsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodForm_automorphism_unitary_labellings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → UIsLab X ct yy' → ∃ κ : ct.T.P.D.toPre.X ≃+ ct.T.P.D.toPre.X, (∀ x, ct.T.be (κ x) (κ x) = ct.T.be x x) ∧ ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (κ μ) := by
  first | exact @GlobalTheory.UPoinc.ULabUniq.main | exact GlobalTheory.UPoinc.ULabUniq.main | (intros; apply GlobalTheory.UPoinc.ULabUniq.main <;> assumption)
end

