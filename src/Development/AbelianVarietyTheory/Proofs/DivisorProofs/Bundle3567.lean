import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3527
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0657
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3519
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3561
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3542
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3423
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3550
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3554
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproximatingElementsNormalCoverUnitary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

theorem range_jK_spMap_subset : ∀ (V R : Type) [CommRing V] [IsDomain V] [CommRing R] [IsDomain R] (ρ : V →+* R), Function.Injective ρ → ∀ (X : Scheme.{0}) (χ : Sp V ⟶ X), Set.range (jK R ≫ spMap ρ ≫ χ) ⊆ Set.range (jK V ≫ χ) := by
  intro V R _ _ _ _ ρ hρ X χ x ⟨p, hp⟩
  let q : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have key : (spMap ρ) ((jK R) p) = (jK V) q := by
    apply PrimeSpectrum.ext
    change Ideal.comap ρ (Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal) =
      Ideal.comap (algebraMap V (FractionRing V)) ⊥
    haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    rw [Ideal.eq_bot_of_prime p.asIdeal, Ideal.comap_comap,
      Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V)),
      Ideal.comap_bot_of_injective _ (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective R (FractionRing R)).comp hρ)]
  refine ⟨q, ?_⟩
  rw [← hp]
  change χ ((jK V) q) = χ ((spMap ρ) ((jK R) p))
  rw [key]

theorem exists_elements_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (φ : InvFun (𝓞 E)), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (d : ℕ) (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → UValOn Xo c C.i φ J d → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Cm : GlobalTheory.UChart.MonoFam Xo c φ V), GlobalTheory.Mum.Base V → ∀ ξ : Sp V ⟶ S, Cm.y ≫ C.iF = jK V ≫ ξ ≫ π → ∀ (N₁ : ℕ) (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)) (Φ : VSys (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) !![(1 : ℤ)] N₁ (M.presheaf.stalk z₁)) (y : Φ.Y) (ρ : V →+* Φ.V y) (e : Φ.X y ≃ₗ[𝓞 E] Cm.P.D.toPre.X) (h : Fin (Φ.m y) ≃ Fin Cm.m) (U : M.Opens), (U : Set M).Nonempty → IsCov C g z₁ ζ → GlobalTheory.GSep.HasTraitsOn ζ Φ.pre U → IsMember ζ Φ Cm (ξ ≫ π) y ρ e h → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → GlobalTheory.UChart.DefOver k₀ (spMap ev ≫ ξ) → ∀ ga : Fin (Φ.m y) → LinearMap.BilinForm ℤ (Φ.X y), (∀ k a b, ga k a b = Cm.δ (h k) (e a) (e b)) → ∃ ev₁ : Φ.V y →+* K, ev₁.comp ρ = ev ∧ GlobalTheory.Poinc.Sep.Elements Φ y φ (2 * d) ga ev₁ k₀ := by
  intro E _ _ _ H Dw hpq l Xo c C φ hφ d J hJ hV S π hπ V _ _ _ Cm hB ξ hξ N₁ M _ g z₁ ζ Φ y ρ e h U hUne hcov htr hmem K _ _ ev k₀ hk₀ hpt hdef ga hga
  obtain ⟨hρi, hρf, hζ, hst, -⟩ := hmem
  obtain ⟨hρl, hext⟩ := GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend V (Φ.V y) K ρ hρi hρf
  obtain ⟨ev₁, hev₁⟩ := hext ev
  have hcov' := hcov
  obtain ⟨-, -, hζg, -⟩ := hcov'
  obtain ⟨S₁, hS₁, p₁, sM, U₁, hft, hqc, hfl, hnorm, hprop, hdom, hcart, hU₁, hlift, hxi⟩ :=
    GlobalTheory.T.exists_normalisedBlowup_finite_normal_cover E H Dw hpq l Xo c C J hJ S π hπ M g z₁ ζ hcov
  haveI := hS₁
  haveI : IsIntegrallyClosed (Φ.V y) := (Φ.cn y).2.1
  have hζ' : (spMap ρ ≫ ξ) ≫ π = spMap (Φ.ev y) ≫ ζ := by rw [hζ, Category.assoc]
  have hgen : Set.range (jK (Φ.V y) ≫ (spMap ρ ≫ ξ) ≫ π) ⊆ Set.range C.iF := by
    intro x hx
    obtain ⟨p, hp⟩ := range_jK_spMap_subset V (Φ.V y) ρ hρi _ (ξ ≫ π) (by simpa only [Category.assoc] using hx)
    simp only [Category.assoc] at hp
    rw [← hξ, Scheme.Hom.comp_apply] at hp
    exact ⟨_, hp⟩
  obtain ⟨ξ₁, hξ₁p, hξ₁⟩ := hxi (Φ.V y) (spMap ρ ≫ ξ) (Φ.ev y) hζ' hgen
  have hcomp : spMap ev₁ ≫ spMap ρ = spMap ev := by
    rw [← hev₁, spMap, spMap, spMap, ← Spec.map_comp]; rfl
  have hpt' : ∀ p, (spMap ev₁ ≫ (spMap ρ ≫ ξ)) p = (spMap ρ ≫ ξ) (closedPoint (Φ.V y)) := by
    intro p
    rw [← Category.assoc, hcomp, hpt]
    change _ = ξ ((spMap ρ) (closedPoint (Φ.V y)))
    rw [spMap, Spec_closedPoint]
  have hdef' : GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ (spMap ρ ≫ ξ)) := by rwa [← Category.assoc, hcomp]
  obtain ⟨hpt₁, hdef₁⟩ := hξ₁ K ev₁ k₀ hk₀ hpt' hdef'
  obtain ⟨b', hb', hid⟩ := GlobalTheory.T.idealAlong_monomialFamily_eq_span_monomial E H Dw hpq l Xo c C φ hφ d J hJ hV S π hπ V Cm hB ξ hξ
  have hU₂ : ((U₁ ⊓ p₁ ⁻¹ᵁ U : S₁.Opens) : Set S₁).Nonempty := by
    have h1 : ((p₁ ⁻¹ᵁ U : S₁.Opens) : Set S₁).Nonempty := by
      obtain ⟨s, hs⟩ := (p₁.denseRange).exists_mem_open U.isOpen hUne
      exact ⟨s, hs⟩
    exact nonempty_preirreducible_inter U₁.isOpen (p₁ ⁻¹ᵁ U).isOpen hU₁ h1
  obtain ⟨g₀, hg₀, happ⟩ := GlobalTheory.T.exists_correction_properNormalCover_powerLocalEquation C.Z M S₁ sM p₁ g J hft hqc hfl hnorm hprop hdom hcart (U₁ ⊓ p₁ ⁻¹ᵁ U) hU₂ z₁ (Φ.V y) (Φ.ev y)
    (Φ.ev_loc y) ξ₁ hξ₁p
  have hpath : ξ₁ ≫ p₁ ≫ g = spMap ρ ≫ (ξ ≫ π ≫ pullback.fst C.z (spMap C.b)) := by
    rw [← Category.assoc, hξ₁p, Category.assoc, ← hζg, ← Category.assoc, hζ]
    simp only [Category.assoc]
  have hkey : Ideal.span {g₀} = Ideal.span {∏ k, Φ.t y k ^ (2 * b' (h k))} := by
    rw [← hg₀, GlobalTheory.TorRef.idlAlong_comap, hpath, GlobalTheory.TraitOrder.idlAlong_comp, hid, Ideal.map_span,
      Set.image_singleton, map_prod]
    congr 2
    exact (Equiv.prod_comp h _).symm.trans (Finset.prod_congr rfl fun j _ => by
      rw [map_pow, ← (hst j).1, ← pow_mul])
  have hδ : ∀ k, Φ.δ y k = GlobalTheory.PolFan.pull e.toLinearMap ((l.M' : ℤ) • Cm.δ (h k)) :=
    fun k => LinearMap.ext₂ fun a b => by rw [(hst k).2 a b]; rfl
  have hev : ∀ k, φ.evalZ (Φ.δ y k) = φ.evalZ ((l.M' : ℤ) • Cm.δ (h k)) := fun k => by
    rw [hδ k, evalZ_pull φ (r := e.toLinearMap) e.surjective]
  have hbdd : BddAct (H.bar : 𝓞 E → 𝓞 E) := (GlobalTheory.Poinc.bddAct_int_and_cm).2 E H
  have hM : 1 ≤ l.M' := GlobalTheory.LevelExist.M'_pos l
  have hδga : ∀ i, Φ.δ y i = ((l.M' : ℕ) : ℤ) • ga i := fun i => LinearMap.ext₂ fun a b => by
    rw [(hst i).2 a b]; simp [hga]
  refine ⟨ev₁, hev₁, (Scheme.stalkClosedPointTo ξ₁).hom.range, g₀, fun k => 2 * b' (h k),
    fun x hx => GlobalTheory.T.stalkValue_closedPoint_definedOver_subfield S₁ (Φ.V y) ξ₁ K ev₁ k₀ hpt₁ hdef₁ x hx, fun k => ?_,
    Ideal.span_singleton_eq_span_singleton.1 hkey, ?_⟩
  · push_cast
    rw [hev k, hb' (h k)]
    ring
  intro D l' a hdom c' e'
  obtain ⟨e₁, he₁⟩ := happ D e'
  obtain ⟨f, hord, hlead⟩ := GlobalTheory.T.exists_approximate_series_leading_term_fourierSystem (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) hbdd (min Dw.p Dw.q) φ hφ 1 !![(1 : ℤ)] Φ.posW N₁ _ Φ y ga
    l.M' hM hδga (D * (2 * d)) l' a hdom c' (max e' e₁)
  have hord' : Φ.OrdGe φ (D * (2 * d)) e₁ f := fun y' hP hm i =>
    (sup_le_sup_left (α := Ideal (Φ.V y')) (Ideal.pow_le_pow_right (le_max_right e' e₁)) _) (hord y' hP hm i)
  obtain ⟨x, hx, hxe⟩ := he₁ f (by
    intro V' _ _ _ _ hc ξ' ev' hl hcomm hU
    have hj : jK V' ≫ spMap ev' = spMap ((algebraMap V' (FractionRing V')).comp ev') := by
      simp only [jK, spMap, ← Spec.map_comp]; rfl
    obtain ⟨y', hy'⟩ := hlift (FractionRing V') (jK V' ≫ ξ') ((algebraMap V' (FractionRing V')).comp ev')
      (by rw [Category.assoc, ← hcomm, ← Category.assoc, hj]) (fun x hx => (hU hx).1)
    have hUM : Set.range (jK V' ≫ spMap ev' ≫ M.fromSpecStalk z₁) ⊆ (U : Set M) := by
      rw [hcomm]
      rintro _ ⟨q, rfl⟩
      have := (hU ⟨q, rfl⟩).2
      rw [Scheme.Hom.comp_apply]
      exact this
    have htr' := GlobalTheory.T.mem_system_of_order_ge_along_traits GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c C φ d J hV M z₁ U ζ N₁ Φ htr V' hc ev' hl hUM y' hy' D e₁ f hord'
    have hpath' : ξ' ≫ p₁ ≫ g = spMap ev' ≫ ζ ≫ pullback.fst C.z (spMap C.b) := by
      rw [hζg, ← Category.assoc (spMap ev'), hcomm, Category.assoc]
    rwa [GlobalTheory.TorRef.idlAlong_comap, hpath'])
  refine ⟨x, hx, ?_⟩
  have h1 : Φ.ev y f - Φ.coefT y a c' * Φ.monoT y a ∈
      Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e' :=
    (sup_le_sup_left (α := Ideal (Φ.V y)) (Ideal.pow_le_pow_right (le_max_left e' e₁)) _) hlead
  have h2 : Φ.ev y f - x * g₀ ^ D ∈
      Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e' :=
    Ideal.mem_sup_right hxe
  have h3 := Ideal.sub_mem _ h1 h2
  convert h3 using 1
  ring

end GlobalTheory.USep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedLatticeDataClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ClosedPt

theorem cpl_isIntegrallyClosed : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), IsIntegrallyClosed (M.Z.presheaf.stalk x) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), IsCpl j → IsIntegrallyClosed R := by
  intro o' Ω _ _ _ hA M x hic R _ _ _ j hC
  obtain ⟨e, -⟩ := hC
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI := hic
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  exact IsIntegrallyClosed.of_equiv e

theorem exists_cong_of_cast {N n : ℕ} (v w : Fin n → ℤ) (h : ∀ i, ((v i : ℤ) : ZMod N) = ((w i : ℤ) : ZMod N)) :
    ∃ k : Fin n → ℤ, v = w + N • k := by
  have : ∀ i, ∃ k : ℤ, v i = w i + N * k := fun i => by
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (w i) (v i) N).1 (h i).symm
    exact ⟨k, by linarith⟩
  choose k hk using this
  exact ⟨k, funext fun i => by simp [hk i, nsmul_eq_mul]⟩

theorem be_le_of_dvd {R V' X : Type} [CommRing R] [CommRing V'] [IsDomain V'] [AddCommGroup X] (g' : R →+* V') {w : V'}
    (hw : Irreducible w) (be : LinearMap.BilinForm ℤ X) {a b : X} {r s : R}
    (ha : 0 ≤ be a a ∧ Associated (g' r ^ 2) (w ^ (be a a).toNat))
    (hb : 0 ≤ be b b ∧ Associated (g' s ^ 2) (w ^ (be b b).toNat)) (hrs : r ∣ s) : be a a ≤ be b b := by
  have h0 : g' r ^ 2 ∣ g' s ^ 2 := pow_dvd_pow_of_dvd (map_dvd g' hrs) 2
  have h1 : w ^ (be a a).toNat ∣ w ^ (be b b).toNat :=
    (ha.2.dvd_iff_dvd_left).1 ((hb.2.dvd_iff_dvd_right).1 h0)
  have h2 := (pow_dvd_pow_iff hw.ne_zero hw.not_isUnit).1 h1
  have := Int.toNat_of_nonneg ha.1
  have := Int.toNat_of_nonneg hb.1
  omega

theorem exists_lattice_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module (𝓞 E) X) (_ : Module.Finite (𝓞 E) X) (_ : Module.Projective (𝓞 E) X) (n : ℕ) (eb : X ≃ₗ[ℤ] (Fin n → ℤ)) (b₀ : LinearMap.BilinForm ℤ X) (μ : (Fin n → ZMod X₁.S.N) → X) (e : (Fin n → ZMod X₁.S.N) → X₁.Ω₁), Module.finrank (𝓞 E) X ≤ min Dw.p Dw.q ∧ b₀ ∈ balForms H.bar X ∧ (∀ y, y ≠ 0 → 0 < b₀ y y) ∧ (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod X₁.S.N) = cl i) ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → b₀ (μ cl) (μ cl) ≤ b₀ α α) ∧ (∀ cl, e cl ≠ 0 ∧ ∃ (T₀ : AddSubgroup X₁.S.Gam) (c' : T₀ →+ ZMod X₁.S.N) (κ : X₁.S.J × (T₀ → ZMod ((X₁.S.r * X₁.S.N) ^ 2))) (x₀ : X₁.S.Gam), X₁.S.IsoFree T₀ ∧ e cl = X₁.S.FF T₀ c' κ / X₁.S.th x₀) ∧ ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : X →ₗ[𝓞 E] T.P.D.toPre.X, Function.Surjective π ∧ (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) → T.be (π (μ cl)) (π (μ cl)) ≤ T.be (π α) (π α)) ∧ ∀ cl, UOrdEq M T ξ (e cl ^ (2 * X₁.S.N)) (T.be (π (μ cl)) (π (μ cl))).toNat := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm hEE x hx
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hC, hpb, hL, hPsi⟩ :=
    GlobalTheory.Poinc.CompletedStalk.exists_completion_unif X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big M U₀ EE out hAdm hEE x hx
  obtain ⟨f, hfm, hfT⟩ := GlobalTheory.T.integerAction_semiAbelian_along_traits_open E H Dw l Xo c C X₁ M U₀ EE out hAdm
  have hR := fun a => GlobalTheory.T.exists_completedLocalRing_endomorphism_character_action X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ M U₀ EE out x R j hB G gm hpb D A U (f a) (hfm a)
  choose fR m hfR using hR
  obtain ⟨T₀, ξ₀, hT₀, hξ₀⟩ := GlobalTheory.T.exists_unitaryTrait_centred_closedPoint E H Dw l Xo c C X₁ M U₀ EE out hAdm x hx
  have tr := GlobalTheory.T.exists_trait_lattice_map_at_closedPoint E H Dw l Xo c C X₁ M U₀ EE out hAdm f hfm hfT x hx R j hB hC G gm hpb D A U hL hPsi m
    (fun a => ⟨fR a, hfR a⟩)
  obtain ⟨V₀, _, _, _, h₀, g₀, ρ₀, -, hirr₀, hsq₀, hsurj₀, hco₀, hlin₀⟩ :=
    tr T₀ ξ₀ hT₀ (by rw [hξ₀])
  haveI : CharZero R := hB.2
  haveI : IsIntegrallyClosed R := cpl_isIntegrallyClosed X₁.o₁ X₁.Ω₁ M x (hAdm.1.normal x).2 R j hC
  have hco : ∀ y, ∃ r, PsiCoord D.toPre y r ∧ (y ≠ 0 → r ∈ maximalIdeal R) := fun y => by
    obtain ⟨r, h1, -, h3, -⟩ := (GlobalTheory.PsiCoordLocal.main R D inferInstance y).1
    exact ⟨r, h1, h3⟩
  obtain ⟨hdvr₀, -, -⟩ := T₀.cdvr
  haveI := hdvr₀
  haveI : IsLocalHom g₀ := GlobalTheory.T.isLocalHom_completedStalk_to_dvr_over_trait X₁.o₁ X₁.Ω₁ M x R j hC T₀.V T₀.ϖ V₀ h₀ g₀ ξ₀ hirr₀ hξ₀ hsq₀
  have hinj : Function.Injective ρ₀ := by
    refine (injective_iff_map_eq_zero ρ₀).2 fun y h0 => by_contra fun hy => ?_
    obtain ⟨r, hr, hrm⟩ := hco y
    obtain ⟨-, has⟩ := hco₀ y r hr
    simp only [h0, map_zero, LinearMap.zero_apply, Int.toNat_zero, pow_zero] at has
    have hu : IsUnit (g₀ r) := (isUnit_pow_iff two_ne_zero).1 (has.isUnit_iff.2 isUnit_one)
    exact (mem_maximalIdeal r |>.1 (hrm hy)) ((isUnit_map_iff g₀ r).1 hu)
  let e₀ : D.toPre.X ≃+ T₀.P.D.toPre.X := AddEquiv.ofBijective ρ₀ ⟨hinj, hsurj₀⟩
  have he₀ : ∀ y, e₀ y = ρ₀ y := fun _ => rfl
  obtain ⟨hbal, hposdef, hfin, hproj, n, ⟨eb⟩⟩ := GlobalTheory.T.balanced_posDef_finite_projective_lattice E H Dw l Xo c T₀
  let ℓ : ZMod X₁.S.N → ℤ := Function.surjInv ZMod.intCast_surjective
  have hℓ : ∀ z, ((ℓ z : ℤ) : ZMod X₁.S.N) = z := Function.surjInv_eq _
  let α₀ : (Fin n → ZMod X₁.S.N) → D.toPre.X := fun cl => e₀.symm (eb.symm (fun i => ℓ (cl i)))
  have hq := fun cl => GlobalTheory.T.exists_minimal_psiCoordinate_associated_fourierPower X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big M U₀ EE out hAdm hEE x hx R j hB hC G gm hpb D A U hL
    hPsi (α₀ cl)
  choose mu hmu1 hmu2 e a he hFF hae hja using hq

  have hcong : ∀ cl (α : T₀.P.D.toPre.X), (∀ i, ((eb α i : ℤ) : ZMod X₁.S.N) = cl i) →
      CongMod X₁.S.N (e₀.symm α) (α₀ cl) := by
    intro cl α hα
    obtain ⟨k, hk⟩ := exists_cong_of_cast (N := X₁.S.N) (eb α) (fun i => ℓ (cl i)) (fun i => by rw [hα, hℓ])
    refine ⟨e₀.symm (eb.symm k), e₀.injective (eb.injective ?_)⟩
    simp only [α₀, map_add, map_nsmul, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hk
  refine ⟨T₀.P.D.toPre.X, inferInstance, inferInstance, hfin, hproj, n, eb, T₀.be, fun cl => ρ₀ (mu cl), e,
    UTrait.finrank_le_min E H Dw l Xo c T₀, hbal, hposdef, ?_, ?_, fun cl => ⟨he cl, hFF cl⟩, ?_⟩
  · intro cl i
    obtain ⟨w, hw⟩ := hmu1 cl
    show ((eb (ρ₀ (mu cl)) i : ℤ) : ZMod X₁.S.N) = cl i
    rw [← he₀, hw, map_add, map_nsmul, AddEquiv.apply_symm_apply, map_add, map_nsmul, LinearEquiv.apply_symm_apply]
    simp [hℓ, nsmul_eq_mul]
  · intro cl α hα
    obtain ⟨r, hr, -⟩ := hco (mu cl)
    obtain ⟨s, hs, -⟩ := hco (e₀.symm α)
    have := be_le_of_dvd g₀ hirr₀ T₀.be (hco₀ _ r hr) (hco₀ _ s hs) (hmu2 cl _ (hcong cl α hα) r s hr hs)
    rwa [← he₀ (e₀.symm α), AddEquiv.apply_symm_apply] at this
  · intro T ξ hT hsp
    obtain ⟨V', _, _, _, h, g', ρT, hh, hirr, hsq, hsurjT, hcoT, hlinT⟩ := tr T ξ hT hsp
    have hsm : ∀ (c' : 𝓞 E) (z : T₀.P.D.toPre.X), ρT (e₀.symm (c' • z)) = c' • ρT (e₀.symm z) := by
      intro c' z
      obtain ⟨a', rfl⟩ := H.bar.surjective c'
      have hz : H.bar a' • z = e₀ (m a' (e₀.symm z)) := by
        rw [he₀, hlin₀, ← he₀, AddEquiv.apply_symm_apply]
      rw [hz, AddEquiv.symm_apply_apply, hlinT]
    let π : T₀.P.D.toPre.X →ₗ[𝓞 E] T.P.D.toPre.X :=
      { toFun := fun z => ρT (e₀.symm z)
        map_add' := fun y z => by simp only [map_add]
        map_smul' := fun c' z => hsm c' z }
    have hπ : ∀ y, π (ρ₀ y) = ρT y := fun y => by
      show ρT (e₀.symm (ρ₀ y)) = ρT y
      rw [← he₀, AddEquiv.symm_apply_apply]
    refine ⟨π, fun z => ?_, ?_, ?_⟩
    · obtain ⟨y, rfl⟩ := hsurjT z
      exact ⟨ρ₀ y, hπ y⟩
    · intro cl α hα
      obtain ⟨r, hr, -⟩ := hco (mu cl)
      obtain ⟨s, hs, -⟩ := hco (e₀.symm α)
      have := be_le_of_dvd g' hirr T.be (hcoT _ r hr) (hcoT _ s hs) (hmu2 cl _ (hcong cl α hα) r s hr hs)
      rwa [hπ, show π α = ρT (e₀.symm α) from rfl]
    · intro cl
      obtain ⟨r, hr, -⟩ := hco (mu cl)
      obtain ⟨-, has⟩ := hcoT (mu cl) r hr
      rw [hπ]
      have hord := GlobalTheory.T.uniformiserOrder_eq_of_associated_stalkImage E H Dw l Xo c X₁.o₁ X₁.Ω₁ M x T ξ hsp R j V' h g' hh hirr hsq (a cl ^ 2) _
        (by rw [map_pow, map_pow]; exact (((hja cl r hr).map g').pow_pow (n := 2)).trans has)
      rwa [map_pow, hae cl, ← pow_mul, mul_comm] at hord

end GlobalTheory.UPoinc.ClosedPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompletionUnif
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GPeriods

theorem exists_completion_unif {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [hA : ArithBase o' Ω]
    {S : ThetaSys o' Ω} {ρ : S.Real} {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE)
    (hO : S.Over₀ M U₀) (x : M.Z) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : M.Z.presheaf.stalk x →+* R)
      (G : Over (Sp R)) (_ : GrpObj G) (_ : IsCommMonObj G) (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R))
      (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ IsSemiAbelian G ∧
      IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm ∧ LBIso U.LG.L (FinalForm.L.L.pull gm) ∧
      ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G) := by
  have hinjΩ := M.stalkHom_injective x
  haveI : IsDomain (M.Z.presheaf.stalk x) := hinjΩ.isDomain
  haveI : CharZero Ω := hA.char
  haveI : CharZero (M.Z.presheaf.stalk x) := (RingHom.charZero_iff hinjΩ).2 inferInstance
  haveI : IsIntegrallyClosed (M.Z.presheaf.stalk x) := (hO.normal x).2
  haveI : Algebra.EssFiniteType ℤ (M.Z.presheaf.stalk x) := GlobalTheory.Poinc.CompletedStalk.essFiniteType_int_stalk M x
  haveI : IsNoetherianRing (M.Z.presheaf.stalk x) := Algebra.EssFiniteType.isNoetherianRing ℤ _
  have fg : (maximalIdeal (M.Z.presheaf.stalk x)).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hRd, hRi⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed (M.Z.presheaf.stalk x)
  haveI hRn : IsNoetherianRing (AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x)) :=
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  set R := AdicCompletion (maximalIdeal (M.Z.presheaf.stalk x)) (M.Z.presheaf.stalk x) with hR
  set φ := algebraMap (M.Z.presheaf.stalk x) R with hφ
  have hcpl : IsAdicComplete (maximalIdeal R) R := by
    rw [hm]
    exact AdicCompletion.isAdicComplete_self _ fg
  have hinj : Function.Injective φ := AdicCompletion.of_injective _ _
  haveI : CharZero R := (RingHom.charZero_iff hinj).1 inferInstance
  set ξ : Sp R ⟶ M.Z := spMap φ ≫ M.Z.fromSpecStalk x with hξ
  have hne : (ξ ⁻¹' abLocus FinalForm.G).Nonempty := by
    let w : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    let p : Sp (M.Z.presheaf.stalk x) := spMap φ w
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap φ ⊥ = ⊥
      rw [← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot φ).1 hinj
    have hgen : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact genericPoint_specializes x
    obtain ⟨q, hq⟩ := hgen
    have hpq : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).1 (by
      show p.asIdeal ≤ q.asIdeal
      rw [hp]
      exact bot_le)
    have hsp : ξ w ⤳ genericPoint M.Z := by
      have := hpq.map (M.Z.fromSpecStalk x).continuous
      rw [hq] at this
      exact this
    refine ⟨w, ?_⟩
    show ξ w ∈ abLocus FinalForm.G
    rw [FinalForm.ab]
    exact le_bot_iff.1 ((S.TT_anti M hsp).trans (ThetaSys.TT_genericPoint S M).le)
  haveI : IsCommMonObj ((Over.pullback ξ).obj FinalForm.G) := Functor.isCommMonObj_obj
  obtain ⟨D, A, U, hL, hP⟩ := FinalForm.unif R hRn hRi hcpl ξ hne
  exact ⟨R, inferInstance, hRd, hloc, φ, (Over.pullback ξ).obj FinalForm.G, inferInstance, inferInstance,
    pullback.fst _ _, D, A, U, ⟨⟨hRn, hRd, hRi, hcpl⟩, inferInstance⟩, isCpl_self _, IsSemiAbelian.pullback ξ FinalForm.G FinalForm.semi,
    isGrpPullback_pullback _ _, hL, hP⟩

end GlobalTheory.UPoinc.GPeriods

theorem GlobalTheory.UPoinc.GPeriods.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R), GlobalTheory.Mum.Base R ∧ IsCpl j ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ y, ∃ k : ℕ, (k : ℤ) = T.be (e y) (e y) ∧ Associated (ψ (p y)) (T.ϖ ^ k) := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hpt x
  obtain ⟨f, hf, hab, hβ⟩ := GlobalTheory.T.integerAction_semiAbelian_along_traits_over_moduli E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hC, hS, hG, hL, hP⟩ :=
    GlobalTheory.UPoinc.GPeriods.exists_completion_unif out hO x
  have hm : ∀ a : 𝓞 E, ∃ m : D.toPre.X →+ D.toPre.X, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧
      EndChar U fR m := by
    intro a
    haveI := hf a
    obtain ⟨fR, hfR, e⟩ := GlobalTheory.PullAction.exists_lift_end hG (f a)
    obtain ⟨m, hm⟩ := GlobalTheory.Poinc.Eq8.endChar_exists_of_isMonHom R hB G hS D A U fR hfR
    exact ⟨m, fR, hfR, e, hm⟩
  choose m hm using hm
  have key := fun (T : UTrait Xo c) (ψ : R →+* T.V) (hψ : IsLocalHom ψ) hc =>
    GlobalTheory.T.exists_traitLattice_equiv_completedLocalRing E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt f hf hab hβ x R j hB hC G gm hS hG D A U hL hP m hm T ψ hψ hc
  haveI : CharZero R := hB.2
  have hco : ∀ y : D.toPre.X, ∃ s, PsiCoord D.toPre y s := fun y =>
    ((GlobalTheory.PsiCoordLocal.main R D hB.1.2.2.1 y).1).imp fun _ h => h.1
  choose s hs using hco
  by_cases hex : ∃ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ ∧
      jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ r = T.y ≫ C.i
  · obtain ⟨T₀, ψ₀, hψ₀, hc₀⟩ := hex
    obtain ⟨ρ₀, -, hρ₀⟩ := key T₀ ψ₀ hψ₀ hc₀
    refine ⟨R, inferInstance, inferInstance, inferInstance, j, T₀.P.D.toPre.X, inferInstance, inferInstance,
      fun y => s (ρ₀.symm y) ^ 2, hB, hC, ?_⟩
    intro T ψ hψ hc
    obtain ⟨ρT, hord, heq⟩ := key T ψ hψ hc
    have hsymm : ∀ (a : 𝓞 E) (v : T₀.P.D.toPre.X), ρ₀.symm (H.bar a • v) = m a (ρ₀.symm v) := fun a v => by
      apply ρ₀.injective
      rw [AddEquiv.apply_symm_apply, hρ₀, AddEquiv.apply_symm_apply]
    let e₀ : T₀.P.D.toPre.X ≃+ T.P.D.toPre.X := ρ₀.symm.trans ρT
    have hlin : ∀ (a : 𝓞 E) (v : T₀.P.D.toPre.X), e₀ (a • v) = a • e₀ v := fun a v => by
      obtain ⟨b, rfl⟩ := H.bar.surjective a
      show ρT (ρ₀.symm (H.bar b • v)) = H.bar b • ρT (ρ₀.symm v)
      rw [hsymm, heq]
    refine ⟨{ e₀ with map_smul' := hlin }, fun y => ?_⟩
    obtain ⟨h0, hA⟩ := hord (ρ₀.symm y) (s (ρ₀.symm y)) (hs _)
    refine ⟨(T.be (ρT (ρ₀.symm y)) (ρT (ρ₀.symm y))).toNat, Int.toNat_of_nonneg h0, ?_⟩
    rw [map_pow]
    exact hA
  · refine ⟨R, inferInstance, inferInstance, inferInstance, j, PUnit, inferInstance, inferInstance, fun _ => 0, hB, hC,
      fun T ψ hψ hc => (hex ⟨T, ψ, hψ, hc⟩).elim⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjugateHeatOperatorPeriodShift
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatDefect

theorem exists_gauge_translate : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])), e.IsGen → ∀ (k : ℕ) (τ : SecM Y.q.left Q.P.L k), ∃ ρ : SecM Y.q.left Q.P.L k, (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval τ (r ≫ (𝟙 Y.H * (toUnit Y.H ≫ x)).left) z J * ((val e r z J) ^ k).val) := by
  intro R _ _ Q O _ _ _ oa Y x e he k τ
  obtain ⟨ρ, hρ⟩ := exists_sec (L := Q.P.L) Q.P.isLB
    (φ' := fun _ : Fin 1 => Y.q.left) (ε' := fun _ => (k : ℤ))
    (by
      intro U _ g
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [zpow_mul, zpow_mul, zpow_one, zpow_neg_one, _root_.mul_comm]
      exact inv_mul_cancel_right _ _)
    (pullMulSec τ (𝟙 Y.H * (toUnit Y.H ≫ x)).left (GeneratorPullback.powGen Q.P.L _ _ e k) (ReciprocityTheory.ChartRestriction.G.DVR.powGen_isGen _ _ _ e he k))
  refine ⟨ρ, fun Z r z J hJ => ?_⟩
  rw [hρ Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ]
  congr 1
  exact congrArg Units.val (map_pow _ _ _)

theorem exists_conj_shift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∀ h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D, IsBasic Y h → ∀ mu : Dd.toPre.X, ∃ (h' : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X →+ R) (π π' : R), IsBasic Y h' ∧ h'.Θ = h.Θ ∧ h'.u = h.u ∧ ∀ (k : ℕ) (α : Dd.toPre.X) (σ : Dd.toPre.SecB k α) (σ₁ σ₁' : Dd.toPre.SecB k (α + k • mu)), 1 ≤ k → ShiftEq Dd.toPre k mu α σ σ₁ 0 σ₁ → TActs Y h k (α + k • mu) σ₁ σ₁' → ∃ σ'' : Dd.toPre.SecB k α, TActs Y h' k α σ σ'' ∧ ShiftEq Dd.toPre k mu α σ'' σ₁' (2 * (k : R) * w α + 2 * (k : R) ^ 2 * π + 2 * (k : R) * π') σ₁ := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hv m t gam hm ht D hD h hb mu
  obtain ⟨x, e, β, w, π, π', he, hwe, hTR⟩ := GlobalTheory.T.thetaShift_fourierTerm_translation_gauge R Dd O oa Y m t gam hm ht D hD mu
  obtain ⟨h', hb', hΘ, hu, hint⟩ :=
    GlobalTheory.T.heatOperator_conj_translation_gauge R Dd.toPre O oa Y n (fun a => v a) dd hv D h hb x e β he hwe
  refine ⟨h', w, π, π', hb', hΘ, hu, ?_⟩
  intro k α σ σ₁ σ₁' hk hs hA
  obtain ⟨τ₁, τ₁', hτ₁, hτ₁', hA₁⟩ := hA
  obtain ⟨σ'', τ, τ'', hτ, hτ'', hA'⟩ := GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R Dd O oa Y n v dd hv D h' hb' k α σ
  obtain ⟨ρ, hρ⟩ := exists_gauge_translate Y x e he k τ₁
  obtain ⟨ρ', hρ'⟩ := exists_gauge_translate Y x e he k τ₁'
  have hAρ := hint k τ₁ τ₁' ρ ρ' hρ hρ' hA₁
  obtain ⟨a, b, -, hab⟩ := hTR k α hk
  obtain ⟨h1, h2⟩ := hab σ σ₁ τ τ₁ ρ hs hτ hτ₁ hρ
  exact ⟨σ'', ⟨τ, τ'', hτ, hτ'', hA'⟩, h2 σ'' σ₁' τ'' τ₁' ρ' hτ'' hτ₁' hρ'
    (GlobalTheory.T.leibniz_along_baseConstants_at_points Y.H Y.q.left Dd.toPre.P.L Dd.toPre.P.isLB (fun a => v a) dd hv D h' k a b ρ τ ρ' τ'' h1 hAρ hA')⟩

end GlobalTheory.HeatDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNatMulFiniteAdeleAwayPIntegralStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral : ∀ (p : ℕ) [Fact p.Prime] (a : AfP p), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ IsIntAf ((j : AfP p) * a) := by
  first | (exact @GlobalTheory.DenAway.exists_coprime_nat_adele) | (exact GlobalTheory.DenAway.exists_coprime_nat_adele) | (intros; apply GlobalTheory.DenAway.exists_coprime_nat_adele  <;> assumption)
end

