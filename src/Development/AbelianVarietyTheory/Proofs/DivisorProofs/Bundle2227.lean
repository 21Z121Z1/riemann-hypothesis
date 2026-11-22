import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2065
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineFunctionWeightedTranslatesUnitAt
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

noncomputable section

namespace GlobalTheory.CharIndepAt

variable {X : Scheme.{0}} [IsIntegral X] {x : X}

def liftStalk (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f)) :
    X.presheaf.stalk x →+* X.presheaf.stalk x where
  toFun s := (h _ ⟨s, rfl⟩).choose
  map_one' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_one, map_one])
  map_mul' s t := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_mul, map_mul, map_mul, (h _ ⟨s, rfl⟩).choose_spec,
      (h _ ⟨t, rfl⟩).choose_spec])
  map_zero' := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_zero, map_zero])
  map_add' s t := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
    rw [(h _ ⟨_, rfl⟩).choose_spec, map_add, map_add, map_add, (h _ ⟨s, rfl⟩).choose_spec,
      (h _ ⟨t, rfl⟩).choose_spec])

theorem algebraMap_liftStalk (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f))
    (s : X.presheaf.stalk x) :
    algebraMap _ X.functionField (liftStalk σ h s) = σ (algebraMap _ X.functionField s) :=
  (h _ ⟨s, rfl⟩).choose_spec

theorem residue_liftStalk_eq_iff (σ : X.functionField →+* X.functionField) (h : ∀ f, RegAt x f → RegAt x (σ f)) :
    (IsLocalRing.residue (X.presheaf.stalk x)).comp (liftStalk σ h) = IsLocalRing.residue (X.presheaf.stalk x) ↔
      ∀ f, RegAt x f → ZeroAt x (σ f - f) := by
  constructor
  · rintro e f ⟨s, rfl⟩
    refine ⟨liftStalk σ h s - s, ?_, by rw [map_sub, algebraMap_liftStalk]⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact RingHom.congr_fun e s
  · intro H
    ext s
    obtain ⟨m, hm, e⟩ := H _ ⟨s, rfl⟩
    have : m = liftStalk σ h s - s := IsFractionRing.injective (X.presheaf.stalk x) X.functionField (by
      rw [e, map_sub, algebraMap_liftStalk])
    subst this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
    exact hm

end GlobalTheory.CharIndepAt

open GlobalTheory.CharIndepAt in

theorem GlobalTheory.CharIndepAt.main : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U → ∀ (x : X) (hx : x ∈ U)
    (ι : Type) [Fintype ι] (σ : ι → X.functionField →+* X.functionField) (u : ι → X.functionField),
    (∀ i f, RegAt x f → RegAt x (σ i f)) → (∀ i f, ZeroAt x f → ZeroAt x (σ i f)) →
    (∀ i, RegAt x (u i)) →
    (∀ i, (∀ f, RegAt x f → ZeroAt x (σ i f - f)) → ZeroAt x (u i - 1)) →
    (∀ n : ℕ, n ≠ 0 → UnitAt x (n : X.functionField)) →
    (∃ i, ∀ f, RegAt x f → ZeroAt x (σ i f - f)) →
    ∃ a : Γ(X, U), UnitAt x (∑ i, σ i (fnOf U (gen_mem hx) a) * u i) := by

  intro X _ U hU x hx ι _ σ u h1 h2 h3 h4 h5 h6
  classical
  let R := X.presheaf.stalk x
  let res := IsLocalRing.residue R
  let g : Γ(X, U) →+* R := (X.presheaf.germ U x hx).hom
  let ψ : ι → (R →+* IsLocalRing.ResidueField R) := fun i => res.comp (liftStalk (σ i) (h1 i))
  let χ : ι → (Γ(X, U) →* IsLocalRing.ResidueField R) := fun i => ((ψ i).comp g : Γ(X, U) →+* _)
  let χ₀ : Γ(X, U) →* IsLocalRing.ResidueField R := (res.comp g : Γ(X, U) →+* _)
  letI : Algebra Γ(X, U) R := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have hl : IsLocalization.AtPrime R (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  have hext : ∀ i, χ i = χ₀ → ψ i = res := by
    intro i e
    refine IsLocalization.ringHom_ext (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl ?_
    ext a
    exact DFunLike.congr_fun e a
  choose t ht using h3
  have hone : ∀ j, χ j = χ₀ → res (t j) = 1 := by
    intro j e
    obtain ⟨m, hm, em⟩ := h4 j ((residue_liftStalk_eq_iff (σ j) (h1 j)).1 (hext j e))
    have : m = t j - 1 := IsFractionRing.injective R X.functionField (by rw [em, map_sub, map_one, ht])
    subst this
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_one, sub_eq_zero] at hm
    exact hm
  obtain ⟨i₀, hi₀⟩ := h6
  have h0 : χ i₀ = χ₀ := by
    have := (residue_liftStalk_eq_iff (σ i₀) (h1 i₀)).2 hi₀
    ext a
    exact RingHom.congr_fun this (g a)
  by_contra hne
  push_neg at hne
  have hsum : ∀ a : Γ(X, U), ∑ i, res (t i) * χ i a = 0 := by
    intro a
    by_contra hz
    refine hne a ⟨∑ i, liftStalk (σ i) (h1 i) (g a) * t i, ?_, ?_⟩
    · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
      intro h
      apply hz
      rw [← h]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, mul_comm]
      rfl
    · rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, algebraMap_liftStalk, ht]
      congr 2
      exact algebraMap_germ hx a
  have hli := linearIndependent_monoidHom Γ(X, U) (IsLocalRing.ResidueField R)
  rw [linearIndependent_iff'] at hli
  let c : (Γ(X, U) →* IsLocalRing.ResidueField R) → IsLocalRing.ResidueField R :=
    fun φ => ∑ i ∈ Finset.univ.filter (fun i => χ i = φ), res (t i)
  have hcomb : ∑ φ ∈ Finset.univ.image χ, c φ • (φ : Γ(X, U) → IsLocalRing.ResidueField R) = 0 := by
    ext a
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hsum a, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image χ) (g := χ)
      (fun i _ => Finset.mem_image_of_mem χ (Finset.mem_univ i))]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  have hc := hli _ c hcomb χ₀ (by rw [← h0]; exact Finset.mem_image_of_mem χ (Finset.mem_univ i₀))
  have hc' : c χ₀ = ((Finset.univ.filter fun i => χ i = χ₀).card : IsLocalRing.ResidueField R) := by
    change ∑ i ∈ Finset.univ.filter (fun i => χ i = χ₀), res (t i) = _
    rw [Finset.sum_congr rfl fun i hi => hone i (Finset.mem_filter.1 hi).2, Finset.sum_const, nsmul_one]
  have hn : (Finset.univ.filter fun i => χ i = χ₀).card ≠ 0 :=
    (Finset.card_pos.2 ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩⟩).ne'
  obtain ⟨s, hs, es⟩ := h5 _ hn
  have : s = ((Finset.univ.filter fun i => χ i = χ₀).card : R) :=
    IsFractionRing.injective R X.functionField (by rw [es, map_natCast])
  subst this
  have := (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hs
  rw [map_natCast, ← hc'] at this
  exact this hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBijectiveStalkMapOverDvrPoint
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

noncomputable section

namespace GlobalTheory.CompHS.Modif

theorem exists_bijective_stalkMap_of_dvr : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F)
    (U : Y.Opens) (d : ℕ) (M : Modif p U d), IsProjOver p → (U : Set Y).Nonempty → ∀ y : Y,
      IsDiscreteValuationRing (Y.presheaf.stalk y) →
      ∃ x : M.X, M.σ x = y ∧ Function.Bijective (M.σ.stalkMap x).hom := by
  intro F _ Y _ p U d M hp hU y hR
  have hprop : ∀ {Z : Scheme.{0}} {s : Z ⟶ Sp F}, IsProjOver s → IsProper s := by
    intro Z s hs
    obtain ⟨N, c, hc, rfl⟩ := hs
    have := isProper_str F N
    infer_instance
  haveI : IsProper p := hprop hp
  haveI : IsProper (M.σ ≫ p) := hprop M.proj
  haveI : IsProper M.σ := IsProper.of_comp M.σ p
  haveI : Nonempty M.X := by
    haveI := M.iso
    obtain ⟨u, hu⟩ := hU
    obtain ⟨z, -⟩ := (M.σ ∣_ U).surjective ⟨u, hu⟩
    exact ⟨z.1⟩
  haveI : IsIntegral M.X := HSApp.ValCrit.isIntegral_X M
  let R := Y.presheaf.stalk y
  haveI : IsDomain R := inferInstanceAs (IsDomain (Y.presheaf.stalk y))
  haveI : IsDiscreteValuationRing R := hR
  let η := genericPoint Y
  have hηU : η ∈ U := ((genericPoint_spec Y).mem_open_set_iff U.isOpen).2 (by simpa using hU)
  let i₂ : Spec R ⟶ Y := Y.fromSpecStalk y

  have hgen : ∀ w : Spec R, (∀ u, w ⤳ u) → i₂ w = η := by
    intro w hw
    have hq : η ∈ Set.range i₂ := by
      rw [Scheme.range_fromSpecStalk]; exact (genericPoint_spec Y).specializes (Set.mem_univ y)
    obtain ⟨q, hq⟩ := hq
    have h1 : i₂ w ⤳ η := hq ▸ (hw q).map i₂.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  let K := FractionRing R
  let j : Spec (.of K) ⟶ Spec R := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have hj : ∀ s : Spec (.of K), ∀ u : Spec R, j s ⤳ u := by
    intro s u
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    change Ideal.comap (algebraMap R K) s.asIdeal ≤ u.asIdeal
    haveI : s.asIdeal.IsPrime := s.isPrime
    rw [Ideal.eq_bot_of_prime s.asIdeal, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  have hKU : ⊤ ≤ (j ≫ i₂) ⁻¹ᵁ U := fun s _ => by
    show i₂ (j s) ∈ U
    rw [hgen (j s) (hj s)]
    exact hηU
  obtain ⟨i₁, hi₁, -⟩ := M.existsUnique_lift (j ≫ i₂) hKU
  have hE : ValuativeCriterion.Existence M.σ := by
    have h : UniversallyClosed M.σ := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨⟨L⟩⟩ := hE (@ValuativeCommSq.mk _ _ M.σ R inferInstance ‹IsDomain R› inferInstance K inferInstance
    inferInstance inferInstance i₁ i₂ ⟨hi₁⟩)
  let c := IsLocalRing.closedPoint R
  have hfr : L.l ≫ M.σ = i₂ := L.fac_right
  refine ⟨L.l c, ?_, ?_⟩
  · show (L.l ≫ M.σ) c = y
    rw [hfr]
    exact Scheme.fromSpecStalk_closedPoint

  have key : ∀ g : Spec R ⟶ Y, g = i₂ → Function.Bijective (g.stalkMap c).hom := by
    rintro _ rfl
    have e : i₂.stalkMap c ≫ (stalkClosedPointIso R).hom = (Y.presheaf.stalkCongr _).hom :=
      Scheme.stalkClosedPointTo_fromSpecStalk y
    haveI : IsIso (i₂.stalkMap c ≫ (stalkClosedPointIso R).hom) := by rw [e]; infer_instance
    haveI : IsIso (i₂.stalkMap c) := IsIso.of_isIso_comp_right _ (stalkClosedPointIso R).hom
    exact ConcreteCategory.bijective_of_isIso _
  have hb := key _ hfr
  have e₀ := Scheme.Hom.stalkMap_comp L.l M.σ c
  have hb2 : Function.Bijective (M.σ.stalkMap (L.l c) ≫ L.l.stalkMap c).hom := by rw [← e₀]; exact hb
  replace hb : Function.Bijective ((L.l.stalkMap c).hom ∘ (M.σ.stalkMap (L.l c)).hom) := hb2

  let t := genericPoint (Spec R)
  have ht : ∀ u : Spec R, t ⤳ u := fun u => (genericPoint_spec (Spec R)).specializes (Set.mem_univ u)
  have hσt : M.σ (L.l t) = η := by
    show (L.l ≫ M.σ) t = η
    rw [hfr]; exact hgen t ht
  have hσg : M.σ (genericPoint M.X) = η := by
    have h1 : M.σ (genericPoint M.X) ⤳ η :=
      hσt ▸ ((genericPoint_spec M.X).specializes (Set.mem_univ (L.l t))).map M.σ.continuous
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hlt : L.l t = genericPoint M.X := by
    haveI := M.iso
    have m1 : L.l t ∈ M.opn := show M.σ (L.l t) ∈ U from hσt ▸ hηU
    have m2 : genericPoint M.X ∈ M.opn := show M.σ (genericPoint M.X) ∈ U from hσg ▸ hηU
    have e : (M.σ ∣_ U) ⟨L.l t, m1⟩ = (M.σ ∣_ U) ⟨genericPoint M.X, m2⟩ :=
      Subtype.ext ((morphismRestrict_base_coe M.σ U ⟨L.l t, m1⟩).trans
        ((hσt.trans hσg.symm).trans (morphismRestrict_base_coe M.σ U ⟨genericPoint M.X, m2⟩).symm))
    exact congrArg Subtype.val ((M.σ ∣_ U).isOpenEmbedding.injective e)

  have hBinj : Function.Injective (L.l.stalkMap c).hom := by
    have hsp : t ⤳ c := ht c
    have nat := Scheme.Hom.stalkSpecializes_stalkMap L.l t c hsp
    have hf : IsField (M.X.presheaf.stalk (L.l t)) := by
      rw [hlt]; exact Field.toIsField M.X.functionField
    have i1 : Function.Injective (L.l.stalkMap t).hom := by
      letI := hf.toField
      exact RingHom.injective _
    have i2 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous)).hom := by
      refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
      obtain ⟨V, hV, f, rfl⟩ := M.X.presheaf.germ_exist a
      have e := congrArg (fun φ => φ.hom f) (M.X.presheaf.germ_stalkSpecializes hV (hsp.map L.l.continuous))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
      rw [e] at ha
      rw [germ_injective_of_isIntegral M.X _ _ (ha.trans (map_zero _).symm), map_zero]
    have i3 : Function.Injective (((Spec R).presheaf.stalkSpecializes hsp).hom ∘ (L.l.stalkMap c).hom) := by
      have h4 : Function.Injective (M.X.presheaf.stalkSpecializes (hsp.map L.l.continuous) ≫ L.l.stalkMap t).hom :=
        i1.comp i2
      rw [nat] at h4
      exact h4
    exact i3.of_comp
  refine ⟨hb.1.of_comp, fun a => ?_⟩
  obtain ⟨b, hb'⟩ := hb.2 ((L.l.stalkMap c).hom a)
  exact ⟨b, hBinj hb'⟩

end GlobalTheory.CompHS.Modif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierSectionGeneratesAtVanishesAtFinset
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

noncomputable section

namespace GlobalTheory.Cartier.CommonEqnOpen

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_pow {x : X} {f : X.functionField} (h : UnitAt x f) (n : ℕ) : UnitAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact unitAt_one x
  | succ n ih => rw [pow_succ]; exact ih.mul h

theorem exists_pow_mul_eq {U : X.Opens} (hU : IsAffineOpen U) (hg : genericPoint X ∈ U) (t : Γ(X, U))
    (ht : genericPoint X ∈ X.basicOpen t) {f : X.functionField}
    (h : ∀ z ∈ X.basicOpen t, RegAt z f) :
    ∃ (n : ℕ) (a : Γ(X, U)), fnOf U hg t ^ n * f = fnOf U hg a := by
  obtain ⟨b, rfl⟩ := exists_fnOf_eq ht h
  have := hU.isLocalization_basicOpen t
  obtain ⟨n, a, e⟩ := IsLocalization.Away.surj t b
  refine ⟨n, a, ?_⟩
  have e' := congrArg (fnOf _ ht) e
  rw [map_mul, map_pow] at e'
  have k (c : Γ(X, U)) : fnOf _ ht (algebraMap Γ(X, U) Γ(X, X.basicOpen t) c) =
      fnOf U hg c := fnOf_resG (X.basicOpen_le t) ht c
  rw [k, k] at e'
  rw [← e', mul_comm]

theorem exists_regularAt {U : X.Opens} (hU : IsAffineOpen U) {D : CartierDiv X} {x : X}
    (hxU : x ∈ U) {g : X.functionFieldˣ} (hg : D.IsEqn x g) {y : X} (hyU : y ∈ U) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      D.RegularAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) := by
  obtain ⟨W, hW, hgW⟩ := hg.exists_nhds
  obtain ⟨V, hV, g', hgV⟩ := D.exists_isEqn_nhds y
  obtain ⟨t, htW, ht⟩ := hU.exists_basicOpen_le ⟨x, hW⟩ hxU
  obtain ⟨t', htV, ht'⟩ := hU.exists_basicOpen_le ⟨y, hV⟩ hyU
  have hgen : genericPoint X ∈ X.basicOpen (t * t') := by
    rw [X.basicOpen_mul]; exact ⟨gen_mem ht, gen_mem ht'⟩
  obtain ⟨n, a, e⟩ := exists_pow_mul_eq hU (gen_mem hxU) (t * t') hgen
    (f := (g' : X.functionField) / g) fun z hz => by
      rw [X.basicOpen_mul] at hz
      exact ((hgW z (htW hz.1)).iff_unitAt.1 (hgV z (htV hz.2))).regAt
  have hu : UnitAt y (fnOf U (gen_mem hxU) (t' ^ n)) := by
    rw [map_pow]; exact unitAt_pow ((unitAt_fnOf_iff hyU _ _).2 ht') n
  refine ⟨t ^ n, (unitAt_fnOf_iff hxU (gen_mem hxU) _).1 (by
    rw [map_pow]; exact unitAt_pow ((unitAt_fnOf_iff hxU _ _).2 ht) n), g', hgV y hV, ?_⟩
  have := (regAt_fnOf hyU (gen_mem hxU) a).mul hu.inv.regAt
  rw [← e] at this
  convert this using 1
  have h0 := hu.ne_zero
  rw [map_pow] at h0
  rw [map_mul, map_pow, map_pow, mul_pow]
  field_simp

theorem exists_vanishesAt {U : X.Opens} (hU : IsAffineOpen U) {D : CartierDiv X} {x : X}
    (hxU : x ∈ U) {g : X.functionFieldˣ} (hg : D.IsEqn x g) {y : X} (hyU : y ∈ U)
    (hxy : x ∉ closure ({y} : Set X)) :
    ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧
      D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) := by
  obtain ⟨s, hs, hreg⟩ := exists_regularAt hU hxU hg hyU
  obtain ⟨t, htU, ht⟩ := hU.exists_basicOpen_le
    (V := ⟨(closure ({y} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩) ⟨x, hxy⟩ hxU
  have hz : ZeroAt y (fnOf U (gen_mem hxU) t) := zeroAt_iff.2 ⟨regAt_fnOf hyU _ _,
    fun h => htU ((unitAt_fnOf_iff hyU _ _).1 h) (subset_closure rfl)⟩
  refine ⟨t * s, by rw [X.basicOpen_mul]; exact ⟨ht, hs⟩, ?_⟩
  obtain ⟨g', hg', hr⟩ := hreg
  refine ⟨g', hg', ?_⟩
  rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (fnOf U (gen_mem hxU) s)]
  exact hz.mul hr

theorem exists_generatesAt_vanishesAt : ∀ (X : Scheme.{0}) [IsIntegral X] (U : X.Opens), IsAffineOpen U →
    ∀ (D : CartierDiv X) (x : X), x ∈ U →
    ∀ (T : Finset X), (∀ y ∈ T, y ∈ U) → (∀ y ∈ T, y ≠ x → x ∉ closure ({y} : Set X)) →
    ∃ f : X.functionField, D.GeneratesAt x f ∧ ∀ y ∈ T, y ≠ x → D.VanishesAt y f := by
  intro X _ U hU D x hxU T hTU hT
  classical
  obtain ⟨g, hg⟩ := D.exists_isEqn x
  suffices ∃ s : Γ(X, U), x ∈ X.basicOpen s ∧ ∀ y ∈ T, y ≠ x →
      D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹) by
    obtain ⟨s, hs, h⟩ := this
    refine ⟨_, ⟨g, hg, ?_⟩, h⟩
    rw [mul_assoc, inv_mul_cancel₀ g.ne_zero, mul_one]
    exact (unitAt_fnOf_iff hxU _ _).2 hs
  have key (y : X) (hyU : y ∈ U) (s t : Γ(X, U))
      (h : D.VanishesAt y (fnOf U (gen_mem hxU) s * (g : X.functionField)⁻¹)) :
      D.VanishesAt y (fnOf U (gen_mem hxU) (s * t) * (g : X.functionField)⁻¹) := by
    obtain ⟨g', hg', hr⟩ := h
    refine ⟨g', hg', ?_⟩
    have := hr.mul (regAt_fnOf hyU (gen_mem hxU) t)
    convert this using 1
    rw [map_mul]; ring
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simpa using hxU, by simp⟩
  | insert y T _ ih =>
    obtain ⟨s, hs, h⟩ := ih (fun z hz => hTU z (Finset.mem_insert_of_mem hz))
      fun z hz => hT z (Finset.mem_insert_of_mem hz)
    by_cases hyx : y = x
    · refine ⟨s, hs, fun z hz hzx => ?_⟩
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact (hzx hyx).elim
      · exact h z hz hzx
    have hyU := hTU y (Finset.mem_insert_self _ _)
    obtain ⟨t, ht, h'⟩ := exists_vanishesAt hU hxU hg hyU (hT y (Finset.mem_insert_self _ _) hyx)
    refine ⟨s * t, by rw [X.basicOpen_mul]; exact ⟨hs, ht⟩, fun z hz hzx => ?_⟩
    rcases Finset.mem_insert.1 hz with rfl | hz
    · rw [mul_comm s]; exact key _ hyU _ _ h'
    · exact key _ (hTU z (Finset.mem_insert_of_mem hz)) _ _ (h z hz hzx)

end GlobalTheory.Cartier.CommonEqnOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationThetaSectionNonvanishingFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.DegTheta

theorem resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (z : Γ(X, U)) :
    resG X h (resG X h' z) = resG X (h.trans h') z := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem resG_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (z : Γ(X, U)) : resG X h z = z := by
  change (X.presheaf.map (homOfLE h).op).hom z = z
  rw [show (homOfLE h).op = 𝟙 (Opposite.op U) from Subsingleton.elim _ _, X.presheaf.map_id]
  rfl

theorem basicOpen_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (z : Γ(X, U)) :
    X.basicOpen (resG X h z) = V ⊓ X.basicOpen z :=
  Scheme.basicOpen_res X z (homOfLE h).op

def secOfSecOn {X : Scheme.{0}} {L : LB X} {V : X.Opens} (hV : ∀ x : X, x ∈ V) (θ : ∀ i, Γ(X, V ⊓ L.U i))
    (hθ : θ ∈ secOn L V) : L.Sec where
  f i := resG X (le_inf (fun x _ => hV x) le_rfl) (θ i)
  compat i j := by
    have e := congrArg (resG X (le_inf (le_inf (fun x _ => hV x) inf_le_left) inf_le_right : L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hθ i j)
    simp only [map_mul, resG_resG] at e
    change resG X _ (resG X _ (θ i)) = _ * resG X _ (resG X _ (θ j))
    rw [resG_resG, resG_resG, e, resG_self]

end GlobalTheory.DegTheta

namespace GlobalTheory.DegTheta

theorem exists_sec_nonvanishing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N), ∃ th : D.P.L.Sec, (∀ s : Sp R, ∃ x : D.P.A.left, D.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th) ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i) := by
  intro R _ _ _ _ D F _ _ N ν
  obtain ⟨V, θ, hxV, hθ, H⟩ := GlobalTheory.SecFamily.exists_secOn_nonvanishing GlobalTheory.abelianSchemeLaws_all.1 (Sp R) D.P
    (IsLocalRing.closedPoint R)
  have hVtop : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hxV
  have hV : ∀ a : D.P.A.left, a ∈ D.P.A.hom ⁻¹ᵁ V := fun a => by rw [hVtop]; trivial
  let θ' : D.P.L.Sec := secOfSecOn hV θ hθ
  obtain ⟨r, hr⟩ := ν.th_gen (DVR.toH0 θ')
  refine ⟨DVR.secOfH0 ν.th, fun s => ?_, fun i h => ?_⟩
  · obtain ⟨a, i, has, ha⟩ := H s (by rw [hVtop]; trivial)
    refine ⟨a, has, ?_⟩
    have haU : a ∈ D.P.L.U i := (D.P.A.left.basicOpen_le (θ i) ha).2
    have e := hr (fun _ => i)
    have h1 : a ∈ D.P.A.left.basicOpen ((DVR.toH0 θ').f (fun _ => i)) := by
      have eq1 : (DVR.toH0 θ').f (fun _ => i) = resG _ ((DVR.h0_le (fun _ => i)).trans
          (le_inf (fun x _ => hV x) le_rfl)) (θ i) := resG_resG _ _ _
      rw [eq1]
      exact (basicOpen_resG _ (θ i)).ge ⟨DVR.chart_le_weighted_chart_single i haU, ha⟩
    rw [e, Scheme.basicOpen_mul] at h1
    have h2 : a ∈ D.P.A.left.basicOpen ((DVR.secOfH0 ν.th).f i) := by
      have eq2 : (DVR.secOfH0 ν.th).f i = resG _ (DVR.chart_le_weighted_chart_single i) (ν.th.f (fun _ => i)) := rfl
      rw [eq2]
      exact (basicOpen_resG (DVR.chart_le_weighted_chart_single i) _).ge ⟨haU, h1.2⟩
    exact (le_iSup (fun k => D.P.A.left.basicOpen ((DVR.secOfH0 ν.th).f k)) i) h2
  · exact ((resG_resG h (DVR.chart_le_weighted_chart_single i) _).trans (resG_self _ _)).symm

end GlobalTheory.DegTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveFieldStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoint_liesOn_component_cmCurve_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (hle : c.F ≤ K), GlobalTheory.CompRat.CurveOver H K l.M' → ∀ Z : Comp Xo c, (letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra; ∃ y : FrPt Xo c K, LiesOn Z y) := by
  first | exact @GlobalTheory.FixedPoint.exists_frPt_liesOn | exact GlobalTheory.FixedPoint.exists_frPt_liesOn | (intros; apply GlobalTheory.FixedPoint.exists_frPt_liesOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRationalityAtPlaceStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_rationality_at_place : TraceOfAt := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.traceOfAt | exact GlobalTheory.BigOn.Exp.SerBase.traceOfAt | (intros; apply GlobalTheory.BigOn.Exp.SerBase.traceOfAt <;> assumption)
end

