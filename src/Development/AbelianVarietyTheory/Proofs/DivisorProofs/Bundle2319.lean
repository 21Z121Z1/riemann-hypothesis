import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0020
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoordLetterEquivApplyConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdDerivationOfMemSpanProdParams
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

theorem dvd_derivation_of_mem_span_prod_params :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (m : ℕ)
      (r : Fin m → R), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m r → ∀ (J : Finset (Fin m))
      (D : Derivation ℤ R R), D (∏ j ∈ J, r j) ∈ Ideal.span {∏ j ∈ J, r j} →
      ∀ j ∈ J, r j ∣ D (r j) := by
  intro R _ _ _ _ m r hrsp J D hD j hj
  have hprime : ∀ i, Prime (r i) :=
    ReciprocityTheory.AnForm.R.prime_of_regular_params r hrsp.1 hrsp.2
  have hnass : ∀ i k, i ≠ k → ¬ Associated (r i) (r k) :=
    (ReciprocityTheory.AnForm.R.regular_params_spec r hrsp.1 hrsp.2).2
  have hsplit : ∏ i ∈ J, r i = r j * ∏ i ∈ J.erase j, r i :=
    (Finset.mul_prod_erase J r hj).symm
  have hdvdD : r j ∣ D (∏ i ∈ J, r i) := by
    have h1 : (∏ i ∈ J, r i) ∣ D (∏ i ∈ J, r i) := Ideal.mem_span_singleton.mp hD
    exact (hsplit ▸ dvd_mul_right (r j) _ : r j ∣ ∏ i ∈ J, r i).trans h1
  rw [hsplit, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hdvdD
  have h2 : r j ∣ (∏ i ∈ J.erase j, r i) * D (r j) :=
    (dvd_add_right (dvd_mul_right (r j) _)).mp hdvdD
  rcases (hprime j).dvd_or_dvd h2 with h3 | h3
  · exfalso
    obtain ⟨k, hk, hdk⟩ := (hprime j).exists_mem_finset_dvd h3
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    exact hnass j k (Ne.symm hkj) ((hprime j).associated_of_dvd (hprime k) hdk)
  · exact h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfLocal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FactorialLocus

open ReciprocityTheory.AnForm.R

theorem exists_affine_gen {X : Scheme.{0}} [IsLocallyNoetherian X] (G : X.IdealSheafData) (x : X)
    (t : X.presheaf.stalk x) (htnzd : t ∈ nonZeroDivisors (X.presheaf.stalk x))
    (ht : FinalTheorems.stalkId G x = Ideal.span {t}) :
    ∃ (U : X.affineOpens) (f : Γ(X, U.1)), x ∈ U.1 ∧ f ∈ nonZeroDivisors Γ(X, U.1) ∧
      G.ideal U = Ideal.span {f} := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  have hx : x ∈ U'.1 := hxU
  rw [ds_stalkId_eq_map G U' x hx] at ht
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U'
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : algebraMap Γ(X, U) (X.presheaf.stalk x) = (X.presheaf.germ U x hx).hom := rfl
  rw [Ideal.map] at ht
  obtain ⟨y, ⟨a, haI, rfl⟩, c, hc⟩ := ds_gen_of_span _ t htnzd ht
  have hmap : (G.ideal U').map (algebraMap Γ(X, U) (X.presheaf.stalk x)) =
      Ideal.span {algebraMap Γ(X, U) (X.presheaf.stalk x) a} := by
    rw [halg, Ideal.map, ht, hc, Ideal.span_singleton_mul_left_unit c.isUnit]
  have hnzd : algebraMap Γ(X, U) (X.presheaf.stalk x) a ∈ nonZeroDivisors (X.presheaf.stalk x) := by
    rw [halg, hc]
    exact mul_mem (IsUnit.mem_nonZeroDivisors c.isUnit) htnzd
  obtain ⟨σ, hσP, hT⟩ := ds_spread (hU.primeIdealOf ⟨x, hx⟩).asIdeal (G.ideal U') a haI hmap hnzd
  haveI := hU.isLocalization_basicOpen σ
  obtain ⟨h1, h2⟩ := hT Γ(X, X.basicOpen σ)
  refine ⟨X.affineBasicOpen (U := U') σ, algebraMap Γ(X, U) Γ(X, X.basicOpen σ) a, ?_, h2, ?_⟩
  · show x ∈ X.basicOpen σ
    rw [X.mem_basicOpen σ x hx]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal σ).2 hσP
  · rw [← G.map_ideal_basicOpen U' σ]
    exact h1

theorem stalkId_eq_span_of_mem {X : Scheme.{0}} (G : X.IdealSheafData) (U : X.affineOpens)
    (f : Γ(X, U.1)) (hf : f ∈ nonZeroDivisors Γ(X, U.1)) (hG : G.ideal U = Ideal.span {f})
    (y : X) (hy : y ∈ U.1) :
    ∃ t ∈ nonZeroDivisors (X.presheaf.stalk y), FinalTheorems.stalkId G y = Ideal.span {t} := by
  refine ⟨X.presheaf.germ U.1 y hy f, ?_, ?_⟩
  · letI : Algebra Γ(X, U.1) (X.presheaf.stalk y) := X.presheaf.algebra_section_stalk ⟨y, hy⟩
    haveI := U.2.isLocalization_stalk ⟨y, hy⟩
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization
      (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl hf
  · rw [ds_stalkId_eq_map G U y hy, hG, Ideal.map_span, Set.image_singleton]

theorem effCartier_comap_of_local {X Y : Scheme.{0}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f]
    (hI : ∀ x : X, ∃ (U : Y.affineOpens) (h : Γ(Y, U.1)), f x ∈ U.1 ∧
      h ∈ nonZeroDivisors Γ(Y, U.1) ∧ I.ideal U = Ideal.span {h}) :
    FinalTheorems.EffCartier (I.comap f) := by
  intro x
  obtain ⟨U, h, hxU, hh, hU⟩ := hI x
  obtain ⟨r, hrle, hxr⟩ := U.2.exists_basicOpen_le (V := f.opensRange) ⟨f x, ⟨x, rfl⟩⟩ hxU
  have himg : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) = Y.basicOpen r := by
    rw [f.image_preimage_eq_opensRange_inf, inf_eq_right.2 hrle]
  have hUX : IsAffineOpen (f ⁻¹ᵁ Y.basicOpen r) := by
    rw [← f.isAffineOpen_iff_of_isOpenImmersion, himg]; exact U.2.basicOpen r
  have hle : f ''ᵁ (f ⁻¹ᵁ Y.basicOpen r) ≤ U.1 := himg.le.trans (Y.basicOpen_le r)
  have hnzd : ∀ (O : Y.Opens) (hO : O = Y.basicOpen r) (hOU : O ≤ U.1),
      Y.presheaf.map (homOfLE hOU).op h ∈ nonZeroDivisors Γ(Y, O) := by
    rintro O rfl hOU
    have := U.2.isLocalization_basicOpen r
    exact algebraMap_mem_nonZeroDivisors_of_isLocalization (Submonoid.powers r) hh
  let e := (f.appIso (f ⁻¹ᵁ Y.basicOpen r)).commRingCatIsoToRingEquiv
  refine ⟨⟨_, hUX⟩, e (Y.presheaf.map (homOfLE hle).op h), hxr, ?_, ?_⟩
  · exact ringEquiv_mem_nonZeroDivisors e (hnzd _ himg hle)
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    rw [← I.map_ideal (U := ⟨_, (f.isAffineOpen_iff_of_isOpenImmersion).2 hUX⟩) (V := U) hle, hU,
      Ideal.map_span, Set.image_singleton]
    rw [show ((f.appIso (f ⁻¹ᵁ Y.basicOpen r)).inv.hom : _ →+* _) = (e.symm : _ →+* _) from rfl,
      Ideal.comap_coe, Ideal.comap_symm, Ideal.map_span, Set.image_singleton]
    rfl

theorem exists_isLocus : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] (V : X.Opens), IsAffineOpen V → (V : Set X).Nonempty → ∃ W : X.Opens, V ≤ W ∧ (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) → x ∈ W) ∧ ∃ c : Pic W.toScheme, IsLocus c (W.ι ⁻¹ᵁ V) := by
  intro X _ _ _ V hV hne
  have hι : IsAffineHom V.ι :=
    haveI : IsAffine V := hV
    haveI : IsAffineHom (V.ι ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  let G := Scheme.IdealSheafData.vanishingIdeal V.compl
  let P : X → Prop := fun x =>
    ∃ t ∈ nonZeroDivisors (X.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}
  have hopen : IsOpen {x | P x} := by
    refine isOpen_iff_forall_mem_open.2 fun x hx => ?_
    obtain ⟨t, ht, htG⟩ := hx
    obtain ⟨U, f, hxU, hf, hG⟩ := exists_affine_gen G x t ht htG
    exact ⟨U.1, fun y hy => stalkId_eq_span_of_mem G U f hf hG y hy, U.1.isOpen, hxU⟩
  let W : X.Opens := ⟨{x | P x}, hopen⟩
  have hVW : V ≤ W := by
    intro x hx
    refine ⟨1, one_mem _, ?_⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ V ↔ (1 : X.presheaf.stalk x) ∉ q.asIdeal := fun q => by
      refine iff_of_true ?_ fun h1 => q.2.ne_top ((Ideal.eq_top_iff_one _).2 h1)
      have hs : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hs
      exact Specializes.mem_open hs V.isOpen hx
    rw [GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl V x 1 h, Ideal.span_singleton_one,
      Ideal.radical_top]
  have hfac : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) → x ∈ W := by
    intro x hufd
    have hd : IsDomain (X.presheaf.stalk x) := inferInstance
    have hn : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
    have hA : IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ V) := by
      have : IsAffineHom (X.fromSpecStalk x ⁻¹ᵁ V).ι :=
        MorphismProperty.of_isPullback (P := @IsAffineHom)
          (isPullback_morphismRestrict (X.fromSpecStalk x) V) hι
      exact isAffine_of_isAffineHom (X.fromSpecStalk x ⁻¹ᵁ V).ι
    have hg : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    obtain ⟨q, hq⟩ := hg
    have hqV : q ∈ X.fromSpecStalk x ⁻¹ᵁ V := by
      change X.fromSpecStalk x q ∈ V
      rw [hq]
      exact ((genericPoint_spec X).mem_open_set_iff V.isOpen).2 (by simpa using hne)
    obtain ⟨a, ha⟩ := @GlobalTheory.exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization
      (X.presheaf.stalk x) (X.presheaf.stalk x).commRing hd hn hufd
      (X.fromSpecStalk x ⁻¹ᵁ V) hA ⟨q, hqV⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ V ↔ a ∉ q.asIdeal := fun q =>
      iff_of_eq (congrArg (fun V => q ∈ V) ha)
    have ha0 : a ≠ 0 := fun h0 => (h q).1 hqV (h0 ▸ zero_mem _)
    show P x
    simp only [P, G]
    rw [GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl V x a h]
    exact GlobalTheory.AffineComplement.exists_radical_span_singleton_eq ha0
  refine ⟨W, hVW, hfac, ?_⟩
  have hE : FinalTheorems.EffCartier (G.comap W.ι) := by
    refine effCartier_comap_of_local G W.ι fun y => ?_
    have hy : P (W.ι y) := y.2
    obtain ⟨t, ht, htG⟩ := hy
    exact exists_affine_gen G _ t ht htG
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hE
  refine ⟨cls D.lb D.isLB_lb, D.lb, D.isLB_lb, D.canonical, rfl, TopologicalSpace.Opens.ext ?_⟩
  refine D.coe_nonzeroLocus_canonical.trans ?_
  rw [hD, Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  ext y
  simp

end GlobalTheory.FactorialLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffectiveGenerationCanonicalNefNumberField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.EffGen

theorem core_gen (hK : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hNN : GlobalTheory.Published.NefNumerics)
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ)
    [SmoothOfRelativeDimension D q] (hq : IsProjOver q) (hD : 1 ≤ D) :
    letI := algebraΓOfHom q
    ∀ (K : CanonLB q D) (N N' B : LB X) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (m : ℕ) (x : X),
      IsClosed ({x} : Set X) → IsNef ℂ N → IsBig ℂ N → IsNef ℂ N' → (D + 1).choose 2 < m →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e → 1 ≤ interNumRed ℂ Z (fun _ : Fin e => N)) →
      cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, x ∈ nonzeroLocus s := by
  letI := algebraΓOfHom q
  intro K N N' B hN hN' hB m x hx hNn hNb hN'n hm hpos hBc
  have hm1 : 1 ≤ m := by omega
  obtain ⟨N₀, h₀, hc₀, hn₀, hb₀⟩ := GlobalTheory.T.exists_nef_big_of_class_eq_smul_add_smul hNN ℂ X q hq N N' hN hN' (2 * m - 1) 2 hNn hNb hN'n (by omega)
  obtain ⟨m', D₀, U, hm', hD₀, hcur, hxU, hklt, hnk⟩ := GlobalTheory.T.exists_isolated_nonKlt_divisor_smooth_projective hK.2 X q D hq hD N₀ 2 x two_pos hn₀ hb₀ hx
    (fun Z e hZ hxZ he hdim => by
      have h1 := hpos Z e hZ hxZ he hdim
      have h2 := GlobalTheory.T.pow_mul_intersection_le_of_nef_class_on_closed hNN ℂ X q hq N N' N₀ hN hN' h₀ (2 * m - 1) 2 Z e hNn hN'n hc₀ hdim
      have h3 : ((2 * m - 1 : ℕ) : ℤ) ^ e ≤ interNumRed ℂ Z (fun _ : Fin e => N₀) := by
        have : (0 : ℤ) ≤ ((2 * m - 1 : ℕ) : ℤ) ^ e := by positivity
        nlinarith
      have h3' : (((2 * m - 1 : ℕ) : ℝ)) ^ e ≤ (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) := by
        exact_mod_cast h3
      have h4 : ((((D + 1).choose 2 : ℕ) : ℝ) * 2) ^ e < ((2 * m - 1 : ℕ) : ℝ) ^ e := by
        refine pow_lt_pow_left₀ ?_ (by positivity) (by omega)
        have : (D + 1).choose 2 * 2 < 2 * m - 1 := by omega
        exact_mod_cast this
      rw [lt_div_iff₀ (by positivity), ← mul_pow]
      push_cast at h4 h3' ⊢
      linarith)
  obtain ⟨J, hJ, hvan⟩ := GlobalTheory.T.nadel_vanishing_canonical_add_boundary hK.1 X q D hq K B N hB D₀ m' 2 hm' two_pos hD₀ hNn hNb
    (fun C hC => by
      have e1 := GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add ℂ X q hq B N N' hB hN hN' m 1 C hC (by rw [hBc, one_smul])
      have e2 := GlobalTheory.T.intersectionNumber_curve_of_class_eq_smul_add ℂ X q hq N₀ N N' h₀ hN hN' (2 * m - 1) 2 C hC hc₀
      have e3 := hcur C hC
      rw [e3, e1, e2]
      have : ((2 * m - 1 : ℕ) : ℚ) = 2 * m - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      push_cast [this]
      ring)
  exact GlobalTheory.T.exists_section_nonvanishing_point ℂ X q hq (tens K.bundle B) (isLB_tens K.isLB hB) J x U hx hxU
    (fun y hy => by
      rw [hJ]
      constructor
      · intro h
        by_contra hne
        exact h (hklt y hy hne)
      · rintro rfl
        exact hnk) (hvan 1 one_pos)

theorem effective_generation : GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.NefNumerics → ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → GeometricallyConnected p → 1 ≤ D → letI := algebraΓOfHom p; ∀ (K : CanonLB p D) (N N' B : LB Y) (hN : N.IsLB) (hN' : N'.IsLB) (hB : B.IsLB) (a m : ℕ) (y : Y), IsNef F N → IsNef F N' → (D + 1).choose 2 < m → (∃ (N₁ N₂ : LB Y) (h₁ : N₁.IsLB) (h₂ : N₂.IsLB), 0 < a ∧ a • cls N hN = cls N₁ h₁ + cls N₂ h₂ ∧ AmpleAt N₁ y ∧ IsNef F N₂) → cls B hB = m • cls N hN + cls N' hN' → ∃ s : (tens K.bundle B).Sec, y ∈ nonzeroLocus s := by
  intro hK hNN F _ _ Y p D _ hproj hgc hD1
  letI := algebraΓOfHom p
  intro K N N' B hN hN' hB a m y hNn hN'n hm hdec hBc
  obtain ⟨N₁, N₂, h₁, h₂, ha, hcls, hamp, hN₂⟩ := hdec
  haveI : Algebra.IsAlgebraic ℚ F := Algebra.IsAlgebraic.of_finite ℚ F
  let σ : F →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := F)).toRingHom
  letI : Algebra F ℂ := σ.toAlgebra
  let π := pullback.fst p (spMap (algebraMap F ℂ))
  let q := pullback.snd p (spMap (algebraMap F ℂ))
  have H : IsPullback π q p (spMap (algebraMap F ℂ)) := IsPullback.of_hasPullback _ _
  obtain ⟨hXi, hXn, hsm, hqp, hsurj⟩ := GlobalTheory.T.baseChange_smooth_projective_variety_properties F ℂ Y _ p q π D H hproj hgc
  haveI := hXi; haveI := hXn; haveI := hsm
  letI := algebraΓOfHom q
  haveI : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  obtain ⟨y', rfl⟩ := hsurj y
  haveI : Smooth q := SmoothOfRelativeDimension.smooth D q
  obtain ⟨m₁, A, s₁, hm₁, hA, hAa, hy⟩ := hamp
  obtain ⟨x, hxc, hyx, hxU⟩ := GlobalTheory.T.exists_closedPoint_specializes_in_open_of_finiteType ℂ _ q (π ⁻¹ᵁ nonzeroLocus s₁) y' hy
  have hAx : AmpleAt (N₁.pull π) x := GlobalTheory.T.ampleModuloEffectiveAwayFromPoint_pull_affine Y _ π N₁ h₁ x ⟨m₁, A, s₁, hm₁, hA, hAa, hxU⟩
  have hNnC := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N hNn
  have hN'nC := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N' hN'n
  have hN₂C := GlobalTheory.T.isNefLineBundle_baseChange_field_extension hNN F ℂ Y _ p q π H hproj N₂ hN₂
  have hc : a • cls (N.pull π) (pull_isLB hN π) = cls (N₁.pull π) (pull_isLB h₁ π) + cls (N₂.pull π) (pull_isLB h₂ π) := by
    rw [cls_pull hN, cls_pull h₁, cls_pull h₂, ← map_nsmul, hcls, map_add]
  have hbig := GlobalTheory.T.isBigLineBundle_of_smul_class_eq_ampleAt_add_nef hNN ℂ _ q hqp (N.pull π) (N₁.pull π) (N₂.pull π) _ _ _ a x hNnC ha hc hAx hN₂C
  have hpos := GlobalTheory.T.one_le_intersectionNumber_subvariety_through_positive hNN ℂ _ q hqp (N.pull π) (N₁.pull π) (N₂.pull π) _ _ _ a x hNnC ha hc hAx hN₂C
  have hcB : cls (B.pull π) (pull_isLB hB π) = m • cls (N.pull π) (pull_isLB hN π) + cls (N'.pull π) (pull_isLB hN' π) := by
    rw [cls_pull hB, cls_pull hN, cls_pull hN', hBc, map_add, map_nsmul]
  obtain ⟨s, hs⟩ := core_gen hK hNN _ q D hqp hD1 (CanonLB.baseChange H K) (N.pull π) (N'.pull π) (B.pull π)
    _ _ _ m x hxc hNnC hbig hN'nC hm hpos hcB
  exact GlobalTheory.T.exists_tensor_section_nonvanishing_of_baseChange F ℂ Y _ p q π H hproj K.bundle B K.isLB hB y' ⟨s, hyx.mem_open (nonzeroLocus s).isOpen hs⟩

end GlobalTheory.EffGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigFrameMatch
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj

namespace GlobalTheory.DetLine.EigParts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Generic

variable {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (x : Sp R ⟶ S) (χ : 𝓞 E → R)

def IsBasG {n : ℕ} (u : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ (∀ i (a : 𝓞 E), u i ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ u i) ∧
    ∀ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ w) →
      ∃! a : Fin n → R, IsCombAtG t x u a w

end Generic

variable {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S}

theorem comb_iff {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) (a : Fin n → R) (w : epsAt x ⟶ t.G) :
    IsCombAt x a v w ↔ IsCombAtG t x (fun i => (v i).left) a w.left :=
  exists_congr fun _ => and_congr Iff.rfl ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h.symm⟩

theorem basis_iff (χ : 𝓞 E →+* R) {n : ℕ} (v : Fin n → (epsAt x ⟶ t.G)) :
    IsEigBasisAt t.act x χ v ↔ IsBasG t x χ (fun i => (v i).left) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨Over.w (v i), (h1 i).1⟩, fun i a => (h1 i).2 a, fun w hw he => ?_⟩
    let w' : epsAt x ⟶ t.G := Over.homMk w hw.1
    exact (existsUnique_congr fun a => comb_iff v a w').1 (h2 w' ⟨hw.2, he⟩)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => ⟨(h1 i).2, h2 i⟩, fun w hw => ?_⟩
    exact (existsUnique_congr fun a => comb_iff v a w).2 (h3 w.left ⟨Over.w w, hw.1⟩ hw.2)

theorem exists_over (χ : 𝓞 E →+* R) {m n : ℕ} (h : m = n) {u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    (hu : IsBasG t x χ u) :
    ∃ v : Fin n → (epsAt x ⟶ t.G), IsEigBasisAt t.act x χ v ∧
      ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k := by
  subst h
  refine ⟨fun i => Over.homMk (u i) (hu.1 i).1, (basis_iff χ _).2 hu, fun i k e => ?_⟩
  obtain rfl : i = k := Fin.ext e
  rfl

theorem exists_left (χ : 𝓞 E →+* R) {m n : ℕ} (h : m = n) {v : Fin n → (epsAt x ⟶ t.G)}
    (hv : IsEigBasisAt t.act x χ v) :
    ∃ u : Fin m → (Sp (DualNumber R) ⟶ t.G.left), IsBasG t x χ u ∧
      ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k := by
  subst h
  refine ⟨fun i => (v i).left, (basis_iff χ _).1 hv, fun i k e => ?_⟩
  obtain rfl : i = k := Fin.ext e
  rfl

theorem eigFrame_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → ∀ (V : Set (gen Y)) (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ gen Y), x ≫ genStr Y = spMap j → Set.range x ⊆ V → ∀ f : EigFrame Y j (x ≫ genι Y), (∃ v w, FrY Y V τ j x v w ∧ Match τ f v w) ∧ ∀ v w, FrY Y V τ j x v w → ∃ f' : EigFrame Y j (x ≫ genι Y), Match τ f' v w := by
  intro E _ _ _ H D l Xo c O _ β Y τ hτ V R _ j x hx hV f
  have hp : D.mult τ = D.p := GlobalTheory.Harm.mult_of_mem D hτ
  have hq : D.mult (conjEmb τ) = D.q := GlobalTheory.Harm.mult_conjEmb_of_mem D hτ
  have hne : conjEmb τ ≠ τ := fun e => (GlobalTheory.Harm.not_mem_hostType_iff H τ).2 (by rw [e]; exact hτ) hτ
  have hf : ∀ σ : E →+* ℂ, IsBasG Y.t (x ≫ genι Y) (FramedFlatCoordinates.chr c σ j) (f.v σ) :=
    fun σ => ⟨f.tan σ, f.eig σ, f.basis σ⟩
  refine ⟨?_, fun v w h => ?_⟩
  · obtain ⟨v, hv, hv'⟩ := exists_over _ hp (hf τ)
    obtain ⟨w, hw, hw'⟩ := exists_over _ hq (hf (conjEmb τ))
    refine ⟨v, w, ⟨hx, hV, hv, ?_⟩, hv', hw'⟩
    rw [comp_chi_bar]
    exact hw
  · obtain ⟨-, -, hv, hw⟩ := h
    rw [comp_chi] at hv
    rw [comp_chi_bar] at hw
    obtain ⟨v₁, a, a'⟩ := exists_left _ hp hv
    obtain ⟨w₁, b, b'⟩ := exists_left _ hq hw
    classical
    let g := Function.update (Function.update f.v τ v₁) (conjEmb τ) w₁
    have g1 : g τ = v₁ := by
      simp only [g, Function.update_of_ne hne.symm, Function.update_self]
    have g2 : g (conjEmb τ) = w₁ := Function.update_self _ _ _
    have hg : ∀ σ : E →+* ℂ, IsBasG Y.t (x ≫ genι Y) (FramedFlatCoordinates.chr c σ j) (g σ) := fun σ => by
      by_cases e2 : σ = conjEmb τ
      · rw [e2, g2]; exact b
      by_cases e1 : σ = τ
      · rw [e1, g1]; exact a
      have : g σ = f.v σ := by simp only [g, Function.update_of_ne e2, Function.update_of_ne e1]
      rw [this]; exact hf σ
    refine ⟨⟨g, fun σ => (hg σ).1, fun σ => (hg σ).2.1, fun σ => (hg σ).2.2⟩, fun i k e => ?_, fun i k e => ?_⟩
    · exact (a' i k e).trans (congrFun g1 k).symm
    · exact (b' i k e).trans (congrFun g2 k).symm

end GlobalTheory.DetLine.EigParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSectionCompatibility
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.FlatModel.GenericPush

theorem one_left_eq {S T : Scheme.{0}} (x : T ⟶ S) (G : Over S) [GrpObj G] :
    (1 : Over.mk x ⟶ G).left = x ≫ η[G].left := rfl

theorem eps_alg' {S : Type} [CommRing S] (a : S) :
    spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
  rw [← Geo.Tor.spMap_comp]
  congr 1
  exact RingHom.ext fun x => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.FlatModel.GenericPush

open GlobalTheory.FlatModel.GenericPush in

theorem GlobalTheory.FlatModel.tan_eig_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (L : Type) [CommRing L] [Algebra c.F L]
    (yL : Sp L ⟶ Xo'.XF c') (σ : E →+* ℂ) (s : 𝓞 E →+* L), (∀ a, algebraMap c.F L (embK c σ a) = s a) →
    ∀ w : Sp (DualNumber L) ⟶ Y.oF.t.G.left, IsTanAtG Y.oF.t yL w → IsEigG Y.t s (w ≫ Y.m.φ) →
      IsTanAt (yL ≫ r ≫ pullback.fst _ _) (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν L _ _ yL σ s hs w hT hE
  have he : η[Y.oF.t.G].left ≫ ν.φ = (r ≫ pullback.fst _ _) ≫ η[Xo.univ.t.G].left := by
    have h0 := ν.cm.e_comm
    rw [ν.base] at h0
    exact h0
  refine ⟨⟨?_, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, ν.cart.1.w, ← Category.assoc, hT.1, Category.assoc]
  · rw [← Category.assoc, hT.2, one_left_eq, one_left_eq, Category.assoc, he]
    simp only [Category.assoc]
  · have key : w ≫ (Y.oF.t.act.act a).left = spMap (epsMul (s a)) ≫ w := by
      apply Y.m.cart.1.hom_ext
      · rw [Category.assoc, Y.m.act, ← Category.assoc, hE a, Category.assoc]
      · rw [Category.assoc, Over.w, Category.assoc, hT.1, ← Category.assoc, eps_alg']
    show (w ≫ ν.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul (algebraMap c.F L (embK c σ a))) ≫ w ≫ ν.φ
    rw [hs, Category.assoc, ← ν.act, ← Category.assoc, key, Category.assoc]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsAffineOpenOfRingKrullDimLeOneStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_isAffineOpen_of_ringKrullDim_le_one' : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] [X.IsSeparated], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ V V' : X.Opens, IsAffineOpen V → V ≤ V' → (∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) → V' = V := by
  first | exact @GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one | exact GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one | (intros; apply GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one <;> assumption)
end

