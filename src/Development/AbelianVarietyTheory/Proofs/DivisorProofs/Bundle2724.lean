import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsDefiniteFormsUpToAut
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.MinSysType

theorem finite_minimiser_systems_upTo_aut : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W →
    ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∃ S : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)),
    ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) →
    ∃ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∀ μ' : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)),
    (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) →
    (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) →
      qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) → μ' ∈ S := by
  intro g φ hφ W hW N _ hN r hr
  classical
  have hX : IsPolFanOn id φ (Fin r → ℤ) := hφ (Fin r → ℤ) (by simpa using hr)
  obtain ⟨S₀, hS₀, hfin⟩ := hX.finite
  set F := hS₀.toFinset with hF
  let ι := Σ m : Fin (F.card + 1), (Fin m.val → F)
  let P : ι → Prop := fun i => IsCone id φ (fun j => ((i.2 j : F) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧
    ∀ x, x ≠ 0 → 0 < ∑ j, ((i.2 j : F) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x
  let T : ι → Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)) := fun i =>
    if h : P i then Classical.choose (GlobalTheory.T.finite_minimiser_systems_smooth_cone φ W hW N hN r i.1.val _ h.1 h.2) else ∅
  refine ⟨Finset.univ.biUnion T, ?_⟩
  intro b hsym hpos
  have hpsd := GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos r b hsym hpos
  obtain ⟨m, γ, cf, hcone, hcf, hb⟩ := GlobalTheory.T.exists_pos_combination_smoothCone_symmIntForm g φ hφ r hr b hsym hpsd
  obtain ⟨e, he⟩ := hfin m γ hcone
  refine ⟨e, fun μ' h1 h2 => ?_⟩
  let γ' : Fin m → F := fun j => ⟨pull e.toLinearMap (γ j), hS₀.mem_toFinset.2 (he j)⟩
  have hcone' := hcone.pull_equiv e
  have hinj : Function.Injective γ' := fun j k hjk => by
    have h := congrArg Subtype.val hjk
    simp only [γ'] at h
    exact hcone'.injective h
  have hm : m < F.card + 1 := by
    have := Fintype.card_le_of_injective γ' hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  let i : ι := ⟨⟨m, hm⟩, γ'⟩
  have hbyy : ∀ y, b y y = ∑ j, (cf j : ℤ) * γ j y y := fun y => by
    rw [hb]; simp [LinearMap.sum_apply]
  have hPi : P i := by
    refine ⟨hcone', fun x hx => ?_⟩
    simp only [i, γ', pull_apply]
    have hex : e x ≠ 0 := by simpa using hx
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ γ j (e x) (e x) := fun j _ => hcone.nonneg j _
    refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
    have := hpos _ hex
    rw [hbyy] at this
    simp [hz] at this
  have hmem : μ' ∈ T i := by
    simp only [T, dif_pos hPi]
    refine Classical.choose_spec (GlobalTheory.T.finite_minimiser_systems_smooth_cone φ W hW N hN r i.1.val _ hPi.1 hPi.2) (pull e.toLinearMap b) 1 cf
      one_pos hcf ?_ μ' h1 h2
    ext a c
    simp [i, γ', pull_apply, hb, LinearMap.sum_apply]
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hmem⟩

end GlobalTheory.Poinc.MinSysType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSetOfFormOrdNeZero
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormOrdFinite

theorem exists_isFrame_genericPoint {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    [IsIntegral X] (p : X ⟶ Sp k) [LocallyOfFiniteType p] (n : ℕ)
    (hn : topologicalKrullDim X = n) :
    ∃ (U : X.Opens) (ω : FormsOn p n U), genericPoint X ∈ U ∧ IsFrame ω := by
  obtain ⟨V, hV, hgV, -⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X) (U := ⊤) trivial
  haveI : Nonempty V := ⟨⟨_, hgV⟩⟩
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).toAlgebra
  have h1 : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p V).FiniteType :=
    (p.finiteType_appLE (isAffineOpen_top _) hV _).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  haveI : Algebra.FiniteType k Γ(X, V) := h1
  have hd : ringKrullDim Γ(X, V) = n := by
    have h2 := GlobalTheory.OpenDim.topologicalKrullDim_open k p V ⟨_, hgV⟩
    rw [hn] at h2
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← h2]
    exact (topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec).symm
  obtain ⟨s, hs, hsm⟩ := GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
    (K := k) (A := Γ(X, V)) hd
  have hloc := hV.isLocalization_basicOpen s
  have h₁ : (algebraMap k (Localization.Away s)).IsStandardSmoothOfRelativeDimension n :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2 hsm
  have h₂ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    (IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
      Γ(X, X.basicOpen s)).toRingEquiv h₁
  have e : ((IsLocalization.algEquiv (Submonoid.powers s) (Localization.Away s)
      Γ(X, X.basicOpen s)).toRingEquiv.toRingHom.comp (algebraMap k (Localization.Away s))) =
      ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (X.basicOpen s) := by
    rw [← resG_comp_algX p (X.basicOpen_le s)]
    ext a
    simp [IsScalarTower.algebraMap_apply k Γ(X, V) (Localization.Away s)]
    rfl
  rw [e] at h₂
  obtain ⟨ω, hω⟩ := GlobalTheory.TopForm.exists_isFreeGen h₂
  have hne : X.basicOpen s ≠ ⊥ := fun h => hs ((AlgebraicGeometry.basicOpen_eq_bot_iff s).1 h)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  exact ⟨X.basicOpen s, ω, gen_mem hx, hV.basicOpen s, hω⟩

theorem finite_setOf_formOrd_ne_zero : ∀ (k : Type) [Field k] [CharZero k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp k) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ η : RatForms p n, η ≠ 0 → {z : X | ∃ E : DivOver p, E.IsAt z ∧ E.formOrd η ≠ 0}.Finite := by
  intro k _ _ X _ _ _ p n hp hn η hη
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hp).1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  obtain ⟨U, ω, hU, hω⟩ := exists_isFrame_genericPoint p n hn
  have hgen := isFreeGen_formOf hU hω
  have h0 : formOf U hU ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨c, hc⟩ := hgen.2 η
  replace hc : c • formOf U hU ω = η := hc
  have hc0 : c ≠ 0 := fun h => hη (by rw [← hc, h, zero_smul])
  obtain ⟨W, hW, hWu⟩ := (unitAt_genericPoint hc0).exists_nhds
  let B : Closeds X := ⟨((U ⊓ W : X.Opens) : Set X)ᶜ, (U ⊓ W).isOpen.isClosed_compl⟩
  have hB : B ≠ ⊤ := fun h => by
    have hm : genericPoint X ∈ (B : Set X) := by rw [h]; trivial
    exact hm ⟨hU, hW⟩
  refine (GlobalTheory.T.finite_codim_one_points_closed X B hB).subset ?_
  rintro z ⟨E, hE, hne⟩
  refine ⟨hE.coheight_eq_one, fun hz => hne ?_⟩
  obtain ⟨hzU, hzW⟩ := hz
  obtain ⟨a, ha, e⟩ := hWu z hzW
  have hord : E.ord (Units.mk0 c hc0) = 0 :=
    E.ord_eq_zero (u := hE.equiv a) (ha.map hE.equiv) e
  have h1 := E.formOrd_smul hn h0 (Units.mk0 c hc0)
  rw [Units.val_mk0, hc, hord, DivOver.formOrd_formOf_eq_zero hzU hE hω] at h1
  simpa using h1

end GlobalTheory.FormOrdFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderDeformationPointsDifferEpsAllOpens
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
open GlobalTheory.CechKS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS.EpsDiff

open GlobalTheory.FlagMod (ev_spMap spMap_ev tau tau_le le_preimage_comp le_preimage_map)

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

variable {B : Type} [CommRing B]

abbrev mkE (ε : B) : B →+* B ⧸ Ideal.span {ε} := Ideal.Quotient.mk _

def FR (ε : B) : Subring (B × DualNumber (B ⧸ Ideal.span {ε})) :=
  RingHom.eqLocus ((mkE ε).comp (RingHom.fst _ _))
    ((TrivSqZeroExt.fstHom (B ⧸ Ideal.span {ε}) _ _).toRingHom.comp (RingHom.snd _ _))

theorem mem_FR {ε : B} {r : B × DualNumber (B ⧸ Ideal.span {ε})} : r ∈ FR ε ↔ mkE ε r.1 = r.2.fst := Iff.rfl

def p1 (ε : B) : FR ε →+* B := (RingHom.fst _ _).comp (FR ε).subtype

def p2 (ε : B) : FR ε →+* DualNumber (B ⧸ Ideal.span {ε}) := (RingHom.snd _ _).comp (FR ε).subtype

theorem FR_ext {ε : B} {r s : FR ε} (h1 : p1 ε r = p1 ε s) (h2 : p2 ε r = p2 ε s) : r = s :=
  Subtype.ext (Prod.ext h1 h2)

theorem epsFibreProduct_quotient_fst_eq_dual_fst {ε : B} (r : FR ε) : mkE ε (p1 ε r) = (p2 ε r).fst := r.2

def liftFR {ε : B} {C : Type} [CommRing C] (a : C →+* B) (b : C →+* DualNumber (B ⧸ Ideal.span {ε}))
    (h : ∀ c, mkE ε (a c) = (b c).fst) : C →+* FR ε := (a.prod b).codRestrict (FR ε) h

theorem fst_comp_liftFR {ε : B} {C : Type} [CommRing C] (a : C →+* B) (b : C →+* DualNumber (B ⧸ Ideal.span {ε}))
    (h : ∀ c, mkE ε (a c) = (b c).fst) : (p1 ε).comp (liftFR a b h) = a := rfl

theorem snd_comp_liftFR {ε : B} {C : Type} [CommRing C] (a : C →+* B) (b : C →+* DualNumber (B ⧸ Ideal.span {ε}))
    (h : ∀ c, mkE ε (a c) = (b c).fst) : (p2 ε).comp (liftFR a b h) = b := rfl

theorem exists_liftFR {ε : B} {C : Type} [CommRing C] (a : C →+* B) (b : C →+* DualNumber (B ⧸ Ideal.span {ε}))
    (h : ∀ c, mkE ε (a c) = (b c).fst) : ∃ q : C →+* FR ε, (p1 ε).comp q = a ∧ (p2 ε).comp q = b :=
  ⟨liftFR a b h, rfl, rfl⟩

def mulE {ε : B} (hε : ε * ε = 0) : (B ⧸ Ideal.span {ε}) →ₗ[B] B :=
  Submodule.liftQ _ (LinearMap.mul B B ε) (by
    intro c hc
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
    simp only [LinearMap.mem_ker, LinearMap.mul_apply']
    rw [← _root_.mul_assoc, _root_.mul_comm ε d, _root_.mul_assoc, hε, MulZeroClass.mul_zero])

theorem mulE_mk {ε : B} (hε : ε * ε = 0) (c : B) : mulE hε (mkE ε c) = ε * c := rfl

def sg {ε : B} (hε : ε * ε = 0) : FR ε →+* B where
  toFun r := p1 ε r + mulE hε (p2 ε r).snd
  map_one' := by simp
  map_zero' := by simp
  map_add' r s := by
    simp only [map_add, TrivSqZeroExt.snd_add]
    ring
  map_mul' r s := by
    obtain ⟨c, hc⟩ : ∃ c, mkE ε c = (p2 ε r).snd := Ideal.Quotient.mk_surjective _
    obtain ⟨d, hd⟩ : ∃ d, mkE ε d = (p2 ε s).snd := Ideal.Quotient.mk_surjective _
    have e : (p2 ε (r * s)).snd = mkE ε (p1 ε r * d + c * p1 ε s) := by
      rw [map_mul, DualNumber.snd_mul, map_add, map_mul, map_mul, hc, hd, epsFibreProduct_quotient_fst_eq_dual_fst, epsFibreProduct_quotient_fst_eq_dual_fst]
    rw [e, ← hc, ← hd, map_mul, mulE_mk, mulE_mk, mulE_mk]
    linear_combination (-(c * d)) * hε

theorem sg_apply {ε : B} (hε : ε * ε = 0) (r : FR ε) : sg hε r = p1 ε r + mulE hε (p2 ε r).snd := rfl

theorem epsFibreProductSnd_surjective (ε : B) : Function.Surjective (p2 ε) := by
  intro w
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective w.fst
  exact ⟨⟨(b, w), hb⟩, rfl⟩

theorem specMap_epsFibreProductSnd_surjective {ε : B} (hε : ε * ε = 0) : Function.Surjective (spMap (p2 ε)) := by
  intro q
  have hk : RingHom.ker (p2 ε) ≤ q.asIdeal := by
    intro r hr
    have hr' : p2 ε r = 0 := hr
    refine q.isPrime.mem_of_pow_mem 2 ?_
    have h1 : mkE ε (p1 ε r) = 0 := by rw [epsFibreProduct_quotient_fst_eq_dual_fst, hr']; rfl
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
    have : r ^ 2 = 0 := by
      apply FR_ext
      · rw [map_pow, ← hd, map_zero]
        linear_combination (d * d) * hε
      · rw [map_pow, hr', map_zero]; simp
    rw [this]; exact zero_mem _
  have := _root_.range_comap_of_surjective _ (p2 ε) (epsFibreProductSnd_surjective ε)
  have hq : q ∈ Set.range (PrimeSpectrum.comap (p2 ε)) := by
    rw [this]; exact hk
  exact hq

theorem top_le_preimage_of_epsFibreSnd_comp {ε : B} (hε : ε * ε = 0) {Y : Scheme.{0}} {T : Sp (FR ε) ⟶ Y} {O : Y.Opens}
    (h : ⊤ ≤ (spMap (p2 ε) ≫ T) ⁻¹ᵁ O) : ⊤ ≤ T ⁻¹ᵁ O := by
  intro p _
  obtain ⟨q, rfl⟩ := specMap_epsFibreProductSnd_surjective hε p
  exact h (Set.mem_univ q)

theorem pt_ext {ε : B} {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {a b : Sp (FR ε) ⟶ Y}
    (ha : ⊤ ≤ a ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ U) (h1 : spMap (p1 ε) ≫ a = spMap (p1 ε) ≫ b)
    (h2 : spMap (p2 ε) ≫ a = spMap (p2 ε) ≫ b) : a = b := by
  have e1 := GlobalTheory.FlagMod.ev_congr h1 U (le_preimage_comp _ ha) (le_preimage_comp _ hb)
  have e2 := GlobalTheory.FlagMod.ev_congr h2 U (le_preimage_comp _ ha) (le_preimage_comp _ hb)
  rw [ev_spMap _ _ _ ha, ev_spMap _ _ _ hb] at e1 e2
  have e : ev a U ha = ev b U hb := RingHom.ext fun f =>
    FR_ext (RingHom.congr_fun e1 f) (RingHom.congr_fun e2 f)
  rw [← spMap_ev a hU ha, ← spMap_ev b hU hb, e]

end GlobalTheory.CechKS.EpsDiff

namespace GlobalTheory.CechKS

open EpsDiff
open GlobalTheory.FlagMod (ev_spMap spMap_ev tau tau_le le_preimage_comp le_preimage_map)

theorem valR_sub_eq_eps_mul_of_affine : ∀ {K : Type} [Field K] {A : Over (Sp K)} {A' : Over (Sp (DualNumber K))} {i : A.left ⟶ A'.left} (hi : i ≫ A'.hom = A.hom ≫ GlobalTheory.DeRham.epsRed K) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) (U : X.affineOpens) (hU' : ⊤ ≤ y1 ⁻¹ᵁ U.1) (Ω : Z.affineOpens) (hΩ : Ω.1 ≤ h ⁻¹ᵁ U.1) {B : Type} [CommRing B] [Algebra (DualNumber K) B] (x : Sp B ⟶ A.left) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (S : Sp (DualNumber B) ⟶ A.left) (hS : S ≫ A.hom = spMap ((algebraMap B (DualNumber B)).comp (baseMap K B))) (hSx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S = x) (l₁ l₂ : Sp B ⟶ A'.left) (hl₁ : l₁ ≫ A'.hom = spMap (algebraMap (DualNumber K) B)) (hl₂ : l₂ ≫ A'.hom = spMap (algebraMap (DualNumber K) B)) (hΩ₁ : ⊤ ≤ (l₁ ≫ m') ⁻¹ᵁ Ω.1) (hΩ₂ : ⊤ ≤ (l₂ ≫ m') ⁻¹ᵁ Ω.1) (h₂ : ∀ f, ∃ c : B, valR (l₂ ≫ m') Ω.1 f = valR (x ≫ m) Ω.1 f + algebraMap (DualNumber K) B DualNumber.eps * c) (h₁₂ : ∀ f, valR (l₁ ≫ m') Ω.1 f - valR (l₂ ≫ m') Ω.1 f = algebraMap (DualNumber K) B DualNumber.eps * (valR (S ≫ m) Ω.1 f).snd) (O : A'.left.Opens) (hxO : ⊤ ≤ x ⁻¹ᵁ (i ⁻¹ᵁ O)) (f : Γ(A'.left, O)), valR l₁ O f - valR l₂ O f = algebraMap (DualNumber K) B DualNumber.eps * (valR S (i ⁻¹ᵁ O) ((i.app O).hom f)).snd := by
  intro K _ A A' i hi X Z h y1 m m' hm' him U hU' Ω hΩ B _ _ x hxΩ S hS hSx l₁ l₂ hl₁ hl₂ hΩ₁ hΩ₂ h₂ h₁₂ O hxO f
  set ε : B := algebraMap (DualNumber K) B DualNumber.eps with hεd
  have hε : ε * ε = 0 := by rw [hεd, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hmkε : mkE ε ε = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self ε)
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := hxΩ
  have hSxm : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ S ≫ m = x ≫ m := by rw [← Category.assoc, hSx]
  have hSm : ⊤ ≤ (S ≫ m) ⁻¹ᵁ Ω.1 := le_preimage_of_red hSxm hxm
  have hSO : ⊤ ≤ S ⁻¹ᵁ (i ⁻¹ᵁ O) := le_preimage_of_red hSx hxO
  have hfst : ∀ g, (ev (S ≫ m) Ω.1 hSm g).fst = ev (x ≫ m) Ω.1 hxm g := fun g => by
    rw [GlobalTheory.FlagMod.ev_congr hSxm.symm Ω.1 hxm (le_preimage_comp _ hSm), ev_spMap _ _ _ hSm]
    rfl
  obtain ⟨q, hqa, hqb⟩ := exists_liftFR (ev (l₂ ≫ m') Ω.1 hΩ₂) ((dualMap (mkE ε)).comp (ev (S ≫ m) Ω.1 hSm))
    (fun g => by
      obtain ⟨c, hc⟩ := h₂ g
      rw [valR_eq_ev _ _ hΩ₂, valR_eq_ev _ _ hxm] at hc
      rw [hc, map_add, map_mul, hmkε, MulZeroClass.zero_mul, add_zero, ← hfst]
      simp [dualMap])
  let j2 : DualNumber K →+* DualNumber (B ⧸ Ideal.span {ε}) :=
    ((dualMap (mkE ε)).comp ((algebraMap B (DualNumber B)).comp (baseMap K B))).comp
      (TrivSqZeroExt.fstHom K K K).toRingHom
  have hj2 : ∀ a, j2 a = TrivSqZeroExt.inl (mkE ε (baseMap K B a.fst)) := fun a => by
    ext <;> simp [j2, dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  obtain ⟨j, hja, hjb⟩ := exists_liftFR (algebraMap (DualNumber K) B) j2 (fun a => by
    have ha : a = algebraMap K (DualNumber K) a.fst + DualNumber.eps * algebraMap K (DualNumber K) a.snd := by
      ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [hj2, TrivSqZeroExt.fst_inl]
    conv_lhs => rw [ha]
    rw [map_add, map_mul, ← hεd, map_add, map_mul, hmkε, MulZeroClass.zero_mul, add_zero]
    rfl)
  have b1 : spMap (p1 ε) ≫ spMap j = l₂ ≫ A'.hom := by rw [spc, hl₂, hja]
  have b2 : spMap (p2 ε) ≫ spMap j = (spMap (dualMap (mkE ε)) ≫ S ≫ i) ≫ A'.hom := by
    rw [Category.assoc, Category.assoc, hi, ← Category.assoc S, hS, ← Category.assoc, spc, spc]
    rw [hjb]
    exact (spc (TrivSqZeroExt.fstHom K K K).toRingHom
      ((dualMap (mkE ε)).comp ((algebraMap B (DualNumber B)).comp (baseMap K B)))).symm
  have b3 : spMap (sg hε) ≫ spMap j = l₁ ≫ A'.hom := by
    rw [spc, hl₁]
    refine congrArg spMap (RingHom.ext fun a => ?_)
    have e1 : p1 ε (j a) = algebraMap (DualNumber K) B a := RingHom.congr_fun hja a
    have e2 : p2 ε (j a) = j2 a := RingHom.congr_fun hjb a
    rw [RingHom.comp_apply, sg_apply, e1, e2, hj2, TrivSqZeroExt.snd_inl, map_zero, add_zero]
  have z1 : spMap (p1 ε) ≫ spMap q ≫ tau Ω.2 = l₂ ≫ m' := by
    rw [← Category.assoc, spc, hqa]
    exact spMap_ev _ Ω.2 hΩ₂
  have z2 : spMap (p2 ε) ≫ spMap q ≫ tau Ω.2 = (spMap (dualMap (mkE ε)) ≫ S ≫ i) ≫ m' := by
    rw [Category.assoc, Category.assoc, him, ← Category.assoc, spc, hqb, ← spc, Category.assoc]
    exact congrArg _ (spMap_ev (S ≫ m) Ω.2 hSm)
  have z3 : spMap (sg hε) ≫ spMap q ≫ tau Ω.2 = l₁ ≫ m' := by
    rw [← Category.assoc, spc]
    have : (sg hε).comp q = ev (l₁ ≫ m') Ω.1 hΩ₁ := by
      refine RingHom.ext fun g => ?_
      have e := h₁₂ g
      rw [valR_eq_ev _ _ hΩ₂, valR_eq_ev _ _ hΩ₁, valR_eq_ev _ _ hSm] at e
      have e' : (dualMap (mkE ε) (ev (S ≫ m) Ω.1 hSm g)).snd = mkE ε (ev (S ≫ m) Ω.1 hSm g).snd := by
        simp [dualMap]
      have e1 : p1 ε (q g) = ev (l₂ ≫ m') Ω.1 hΩ₂ g := RingHom.congr_fun hqa g
      have e2 : p2 ε (q g) = dualMap (mkE ε) (ev (S ≫ m) Ω.1 hSm g) := RingHom.congr_fun hqb g
      rw [RingHom.comp_apply, sg_apply, e1, e2, e', mulE_mk, ← e]
      ring
    rw [this]
    exact spMap_ev _ Ω.2 hΩ₁
  have hw : (spMap q ≫ tau Ω.2) ≫ h = spMap j ≫ y1 := by
    refine pt_ext U.2 (le_preimage_map h hΩ (le_preimage_comp _ (tau_le Ω.2 le_rfl))) (le_preimage_comp _ hU') ?_ ?_
    · rw [← Category.assoc, z1, ← Category.assoc, b1, Category.assoc, Category.assoc, hm'.w]
    · rw [← Category.assoc, z2, ← Category.assoc (spMap (p2 ε)), b2, Category.assoc _ m', Category.assoc _ A'.hom,
        hm'.w]
  obtain ⟨T, T1, T2⟩ : ∃ T : Sp (FR ε) ⟶ A'.left, T ≫ m' = spMap q ≫ tau Ω.2 ∧ T ≫ A'.hom = spMap j :=
    ⟨hm'.lift _ _ hw, hm'.lift_fst _ _ hw, hm'.lift_snd _ _ hw⟩
  have t1 : spMap (p1 ε) ≫ T = l₂ :=
    hm'.hom_ext (by rw [Category.assoc, T1, z1]) (by rw [Category.assoc, T2, b1])
  have t2 : spMap (p2 ε) ≫ T = spMap (dualMap (mkE ε)) ≫ S ≫ i :=
    hm'.hom_ext (by rw [Category.assoc, T1, z2]) (by rw [Category.assoc, T2, b2])
  have t3 : spMap (sg hε) ≫ T = l₁ :=
    hm'.hom_ext (by rw [Category.assoc, T1, z3]) (by rw [Category.assoc, T2, b3])
  have hSi : ⊤ ≤ (S ≫ i) ⁻¹ᵁ O := hSO
  have hT : ⊤ ≤ T ⁻¹ᵁ O := top_le_preimage_of_epsFibreSnd_comp hε (by rw [t2]; exact le_preimage_comp _ hSi)
  have v2 := GlobalTheory.FlagMod.ev_congr t2 O (le_preimage_comp _ hT) (le_preimage_comp _ hSi)
  rw [ev_spMap _ _ _ hT, ev_spMap _ _ _ hSi] at v2
  have v2' : p2 ε (ev T O hT f) = dualMap (mkE ε) (ev (S ≫ i) O hSi f) := RingHom.congr_fun v2 f
  have e' : (dualMap (mkE ε) (ev (S ≫ i) O hSi f)).snd = mkE ε (ev (S ≫ i) O hSi f).snd := by
    simp [dualMap]
  rw [← valR_comp_app, valR_eq_ev _ _ hSi, ← t1, ← t3, valR_eq_ev _ _ (le_preimage_comp _ hT),
    valR_eq_ev _ _ (le_preimage_comp _ hT), ev_spMap _ _ _ hT, ev_spMap _ _ _ hT, RingHom.comp_apply,
    RingHom.comp_apply, sg_apply, v2', e', mulE_mk]
  ring

end GlobalTheory.CechKS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedMemRangeFractionFieldMapGaloisInvariants
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem fixed_mem_range : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ), IsGal ρ → ∀ y : FractionRing R', (∀ σ : Gal ρ, fracAut σ.1 y = y) →
    y ∈ (fracMap ρ hρ).range := by
  classical
  intro R R' _ _ _ _ ρ hρ hG y hy
  obtain ⟨hfin, hinv⟩ := hG
  letI : Fintype (Gal ρ) := Fintype.ofFinite _
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R') y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set P : R' := ∏ σ ∈ (Finset.univ : Finset (Gal ρ)).erase 1, σ.1 b with hP
  set N : R' := ∏ σ : Gal ρ, σ.1 b with hN
  have hNP : N = b * P := by
    rw [hN, hP, ← Finset.mul_prod_erase Finset.univ (fun σ : Gal ρ => σ.1 b) (Finset.mem_univ 1)]
    rfl
  have hσ0 : ∀ σ : Gal ρ, σ.1 b ≠ 0 := fun σ => (map_ne_zero_iff σ.1 σ.1.injective).2 hb0
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.2 fun σ _ => hσ0 σ
  have hNfix : ∀ τ ∈ Gal ρ, τ N = N := by
    intro τ hτ
    rw [hN, map_prod]
    exact Fintype.prod_equiv (Equiv.mulLeft (⟨τ, hτ⟩ : Gal ρ)) _ _ (fun σ => rfl)
  obtain ⟨n, hn⟩ := hinv N hNfix
  have inj := IsFractionRing.injective R' (FractionRing R')
  have hPK : algebraMap R' (FractionRing R') P ≠ 0 := (map_ne_zero_iff _ inj).2 hP0
  have hNK : algebraMap R' (FractionRing R') N ≠ 0 := (map_ne_zero_iff _ inj).2 hN0
  have hy' : algebraMap R' (FractionRing R') a / algebraMap R' (FractionRing R') b
      = algebraMap R' (FractionRing R') (a * P) / algebraMap R' (FractionRing R') N := by
    rw [hNP, map_mul, map_mul, mul_div_mul_right _ _ hPK]
  have hcfix : ∀ τ ∈ Gal ρ, τ (a * P) = a * P := by
    intro τ hτ
    apply inj
    have hyN : algebraMap R' (FractionRing R') (a * P)
        = (algebraMap R' (FractionRing R') a / algebraMap R' (FractionRing R') b) * algebraMap R' (FractionRing R') N := by
      rw [hy', div_mul_cancel₀ _ hNK]
    rw [← fracAut_algebraMap, hyN, map_mul, hy ⟨τ, hτ⟩, fracAut_algebraMap, hNfix τ hτ]
  obtain ⟨m, hm⟩ := hinv (a * P) hcfix
  refine ⟨algebraMap R (FractionRing R) m / algebraMap R (FractionRing R) n, ?_⟩
  rw [map_div₀, fracMap_algebraMap, fracMap_algebraMap, hm, hn, hy']

end GlobalTheory.Mum.GenDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleIntegralBase
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB

open GlobalTheory.QCoh

namespace GlobalTheory.FlagBase

theorem isIntegral_base : ∀ (Y Y₁ : Scheme.{0}) (ρ : Y ⟶ Y₁) (E₁ : Y₁.Modules)
    (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2),
    IsIntegral Y → GlobalTheory.VB.IsVB E₁ 2 → IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) →
      IsIntegral Y₁ := by
  intro Y Y₁ ρ E₁ fl₁ hY hE hfl
  have hsurj : Function.Surjective ρ :=
    GlobalTheory.FlagSurj.isFlagBundle_surjective Y₁ Y ρ Unit (fun _ => E₁) (fun _ => 2) (fun _ => fl₁) (fun _ => hE) hfl
  have : IrreducibleSpace Y₁ := Function.Surjective.irreducibleSpace ρ.continuous hsurj
  have : IsReduced Y₁ := by
    refine @isReduced_of_isReduced_stalk Y₁ ?_
    intro x
    obtain ⟨U, e, hb, he⟩ := hE x
    have hfr := (isFrame_restrict_iff U.ι _).2 (he.res (U.ι_image_le ⊤))
    let φ : freeModule U.toScheme (Fin 2) ≅ (Scheme.Modules.pullback U.ι).obj E₁ :=
      (isFrame_freeFrame _ _).iso hfr ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E₁
    obtain ⟨g', ⟨w, -⟩, -⟩ := hfl U.toScheme U.ι (fun _ => (GlobalTheory.FlagSurj.freeFlag U.toScheme 2).ofIso φ)
    let x' : U.toScheme := ⟨x, hb⟩
    have hopen : IsOpenImmersion (g' ≫ ρ) := w ▸ inferInstance
    have hiso : IsIso ((g' ≫ ρ).stalkMap x') := (IsOpenImmersion.iff_isIso_stalkMap.1 hopen).2 x'
    have h1 : Function.Injective ((g' ≫ ρ).stalkMap x').hom :=
      (ConcreteCategory.bijective_of_isIso ((g' ≫ ρ).stalkMap x')).1
    rw [Scheme.Hom.stalkMap_comp] at h1
    have hinj : Function.Injective (ρ.stalkMap (g' x')).hom :=
      Function.Injective.of_comp (f := (g'.stalkMap x').hom) h1
    have hred : _root_.IsReduced (Y₁.presheaf.stalk (ρ (g' x'))) := isReduced_of_injective _ hinj
    have hx : ρ (g' x') = x := by
      have h : (g' ≫ ρ) x' = U.ι x' := by rw [w]
      exact (Scheme.Hom.comp_apply g' ρ _).symm.trans (h.trans (Scheme.Opens.ι_apply U _))
    exact hx ▸ hred
  exact isIntegral_of_irreducibleSpace_of_isReduced Y₁

end GlobalTheory.FlagBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEachStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_product_of_each : ∀ (k : Type) [CommRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), IsProjOver q → (∀ a, ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π (fun _ : Unit => E a) (fun _ => r a) fl ∧ IsProjOver (π ≫ q)) → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), GlobalTheory.CovTest.IsFlagBundle π E r fl ∧ IsProjOver (π ≫ q) := by
  first | exact @GlobalTheory.FlagFamily.exists_isFlagBundle_isProjOver | exact GlobalTheory.FlagFamily.exists_isFlagBundle_isProjOver | (intros; apply GlobalTheory.FlagFamily.exists_isFlagBundle_isProjOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseClosedImmersionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalClosedSubschemesAlgebraise_closedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (i : W' ⟶ W), IsSeparated f → IsClosedImmersion i → Alg f I → Alg (i ≫ f) I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isClosedImmersion | exact GlobalTheory.FormalAlg.alg_of_isClosedImmersion | (intros; apply GlobalTheory.FormalAlg.alg_of_isClosedImmersion <;> assumption)
end

