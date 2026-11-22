import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0977
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFrameCongruenceSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedBundleSpecialFibreGenerator
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem natCast_eq_zero_reducedSpecialFibre {F : Type} [Field F] (V : ValuationSubring F)
    [IsDiscreteValuationRing V] (p : ℕ) (hp : (p : F) ∈ V.nonunits) {X : Scheme.{0}} (s : X ⟶ Sp V)
    (U : (reducedSpecialFibre s).Opens) : (p : Γ(reducedSpecialFibre s, U)) = 0 := by
  obtain ⟨ha, hm⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hp
  have hpV : ((p : V) : V) ∈ IsLocalRing.maximalIdeal V := by
    convert hm using 1
    ext
    simp
  have hk : (p : IsLocalRing.ResidueField V) = 0 := by
    rw [← map_natCast (IsLocalRing.residue V) p]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hpV
  let q : reducedSpecialFibre s ⟶ Spec (.of (IsLocalRing.ResidueField V)) :=
    (specialFibre s).nilradical.subschemeι ≫ pullback.snd _ _
  have e : (p : Γ(reducedSpecialFibre s, U)) =
      ((reducedSpecialFibre s).presheaf.map (homOfLE le_top).op).hom
        (q.appTop.hom ((Scheme.ΓSpecIso (.of (IsLocalRing.ResidueField V))).inv.hom
          (p : IsLocalRing.ResidueField V))) := by
    simp only [map_natCast]
  rw [e, hk]
  simp only [map_zero]

theorem pullU_reducedSpecialι_eq_one {F : Type} [Field F] (V : ValuationSubring F)
    [IsDiscreteValuationRing V] (p : ℕ) (hp : (p : F) ∈ V.nonunits) {X : Scheme.{0}} (s : X ⟶ Sp V)
    (W : X.Opens) (u : Γ(X, W)ˣ) (hu : ((u : Γ(X, W)) - 1) ∈ (Ideal.span {(p : Γ(X, W))}).radical) :
    pullU (reducedSpecialι s) W u = 1 := by
  haveI : IsReduced (reducedSpecialFibre s) := GlobalTheory.RedFibreField.isReduced_nilradical_subscheme _
  obtain ⟨n, hn⟩ := hu
  rw [Ideal.mem_span_singleton] at hn
  have h0 : (((reducedSpecialι s).app W).hom (u : Γ(X, W)) - 1) ^ n = 0 := by
    have hd := map_dvd ((reducedSpecialι s).app W).hom hn
    rw [map_natCast, natCast_eq_zero_reducedSpecialFibre V p hp s, map_pow, map_sub, map_one] at hd
    exact zero_dvd_iff.1 hd
  have h1 : ((reducedSpecialι s).app W).hom (u : Γ(X, W)) - 1 = 0 :=
    IsReduced.eq_zero _ ⟨n, h0⟩
  ext
  exact sub_eq_zero.1 h1

theorem gU_ratioProp {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens}
    {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]} (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X)
    (hR : ∃ u, RatioProp h x y u) : RatioProp h x y (gU h x y) := by
  unfold gU
  rw [dif_pos hR]
  exact hR.choose_spec

theorem glueLB_reducedSpecial_gen : ∀ (F : Type) [Field F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → ∃ t : ((glueLB h).pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.reducedSpecialι s)).Gen, t.IsGen := by
  intro F _ V _ p _ hp X s Xw K h hR
  refine ⟨⟨fun _ => 1⟩, ?_⟩
  intro i j
  rw [map_one, map_one, _root_.mul_one]
  symm
  have key : ∀ (W : (reducedSpecialFibre s).Opens) (k : PUnit)
      (hh : W ≤ reducedSpecialι s ⁻¹ᵁ ((glueLB h).U (i k) ⊓ (glueLB h).U (j k))),
      res hh (pullU (reducedSpecialι s) _ ((glueLB h).g (i k) (j k))) ^ (1 : ℤ) = 1 := by
    intro W k hh
    rw [pullU_reducedSpecialι_eq_one V p hp s (W := (glueLB h).U (i k) ⊓ (glueLB h).U (j k))
      (u := (glueLB h).g (i k) (j k)) (gU_ratioProp h _ _ (hR _ _)).2, map_one, one_zpow]
  exact @Finset.prod_eq_one PUnit (Γ(reducedSpecialFibre s,
    LB.wchart (glueLB h) (fun _ : PUnit => reducedSpecialι s) i ⊓
      LB.wchart (glueLB h) (fun _ : PUnit => reducedSpecialι s) j)ˣ) Finset.univ _ _ (fun k _ => key _ k _)

end GlobalTheory.UnitGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedGeneratorIsGenerator
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits

theorem mem_genericι_preimage_Xp (F : Type) [Field F] [NumberField F] (V : ValuationSubring F)
    [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V)
    (y : genericFibre s) : y ∈ genericι s ⁻¹ᵁ Xp X p := by
  have hK : IsUnit ((p : ℕ) : FractionRing V) := by
    refine IsUnit.mk0 _ ?_
    rw [← map_natCast (algebraMap V (FractionRing V))]
    refine (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 ?_
    intro h0
    have := congrArg (fun v : V => (v : F)) h0
    simp at this
    exact (Fact.out : p.Prime).ne_zero this
  have hU : IsUnit ((p : ℕ) : Γ(genericFibre s, genericι s ⁻¹ᵁ ⊤)) := by
    have := hK.map (((genericFibre s).presheaf.map
      (homOfLE (le_top : genericι s ⁻¹ᵁ ⊤ ≤ genericStr s ⁻¹ᵁ ⊤)).op).hom.comp
      (((genericStr s).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom))
    simpa only [map_natCast] using this
  show y ∈ genericι s ⁻¹ᵁ X.basicOpen ((p : ℕ) : Γ(X, ⊤))
  rw [Scheme.preimage_basicOpen, map_natCast, Scheme.basicOpen_of_isUnit _ hU]
  trivial

theorem germ_res_res_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {A : X.Opens} {W W' : Y.Opens} (h1 : W ≤ W')
    (h2 : W' ≤ f ⁻¹ᵁ A) (c : Γ(X, A)ˣ) (y : Y) (hy : y ∈ W) :
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU y hy (res h1 (res h2 (pullU f A c))) =
      Units.map (f.stalkMap y).hom (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU (f.base y) (h2 (h1 hy)) c) := by
  rw [ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res,
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_pullU]

theorem germ_res_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {A : X.Opens} {W : Y.Opens}
    (h2 : W ≤ f ⁻¹ᵁ A) (c : Γ(X, A)ˣ) (y : Y) (hy : y ∈ W) :
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU y hy (res h2 (pullU f A c)) =
      Units.map (f.stalkMap y).hom (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU (f.base y) (h2 hy) c) := by
  rw [ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_pullU]

theorem sigGen_isGen_of_ratio : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), (∀ x y : X, ∃ u, RatioProp h x y u) → (sigGen h s).IsGen := by
  intro F _ _ V _ p _ X s Xw K h hR
  have hc : ∀ j : PUnit → X, LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j ≤
      genericι s ⁻¹ᵁ (Uc h (j PUnit.unit) ⊓ Xp X p) := fun j y hy =>
    ⟨Set.mem_iInter.1 hy PUnit.unit, mem_genericι_preimage_Xp F V p X s y⟩
  intro (i : PUnit → X) (j : PUnit → X)
  have hsi : (sigGen h s).s i = res (hc i) (pullU (genericι s) _ (Cx h (i PUnit.unit))) := dif_pos (hc i)
  have hsj : (sigGen h s).s j = res (hc j) (pullU (genericι s) _ (Cx h (j PUnit.unit))) := dif_pos (hc j)
  have hg : GlobalTheory.UnitGlue.gU h (i PUnit.unit) (j PUnit.unit) = (hR (i PUnit.unit) (j PUnit.unit)).choose :=
    dif_pos (hR _ _)
  have hr := ((hR (i PUnit.unit) (j PUnit.unit)).choose_spec).1
  rw [← hg] at hr
  rw [hsi, hsj]
  apply ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.unit_ext
  intro y hy
  have hxi : (genericι s).base y ∈ Uc h (i PUnit.unit) := Set.mem_iInter.1 hy.1 PUnit.unit
  have hxj : (genericι s).base y ∈ Uc h (j PUnit.unit) := Set.mem_iInter.1 hy.2 PUnit.unit
  have hx : (genericι s).base y ∈ Uc h (i PUnit.unit) ⊓ Uc h (j PUnit.unit) ⊓ Xp X p := ⟨⟨hxi, hxj⟩, mem_genericι_preimage_Xp F V p X s y⟩
  have hr' := congrArg (ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU _ hx) hr
  simp only [map_mul, ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gU_res] at hr'
  have hle : ((glueLB h).pull (genericι s)).U i ⊓ ((glueLB h).pull (genericι s)).U j ≤
      genericι s ⁻¹ᵁ (Uc h (i PUnit.unit) ⊓ Uc h (j PUnit.unit)) := fun z hz =>
    ⟨Set.mem_iInter.1 hz.1 PUnit.unit, Set.mem_iInter.1 hz.2 PUnit.unit⟩
  have hgl : ((glueLB h).pull (genericι s)).g i j =
      res hle (pullU (genericι s) _ (GlobalTheory.UnitGlue.gU h (i PUnit.unit) (j PUnit.unit))) :=
    by
      have e := Fintype.prod_unique (fun k : PUnit => (res (fun z hz => ⟨Set.mem_iInter.1 hz.1 k, Set.mem_iInter.1 hz.2 k⟩ :
        LB.wchart (glueLB h) (fun _ : PUnit => genericι s) i ⊓ LB.wchart (glueLB h) (fun _ : PUnit => genericι s) j ≤
          genericι s ⁻¹ᵁ (Uc h (i k) ⊓ Uc h (j k)))
        (pullU (genericι s) (Uc h (i k) ⊓ Uc h (j k)) (GlobalTheory.UnitGlue.gU h (i k) (j k)))) ^ (1:ℤ))
      exact e.trans (zpow_one _)
  rw [hgl, map_mul]
  refine (germ_res_res_pull (genericι s) _ _ _ y hy).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (germ_res_pull (genericι s) hle _ y hy).symm
    (germ_res_res_pull (genericι s) _ _ _ y hy).symm)
  rw [← map_mul, ← hr']

end GlobalTheory.UnitGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GluedLineBundleInvertible
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue.IsLBProof

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (u : Γ(X, U)ˣ) :
    res h2 (res h1 u) = res (h2.trans h1) u := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_inj {X : Scheme.{0}} [IsIntegral X] (P : X.Opens) (hP : (P : Set X).Nonempty) (V : X.Opens) :
    Function.Injective (res (inf_le_left : V ⊓ P ≤ V)) := by
  by_cases hV : (V : Set X).Nonempty
  · have hne : ((V ⊓ P : X.Opens) : Set X).Nonempty := by
      obtain ⟨z, _, hz⟩ := (PreirreducibleSpace.isPreirreducible_univ (X := X)) _ _ V.isOpen P.isOpen
        (by simpa using hV) (by simpa using hP)
      exact ⟨z, hz⟩
    haveI : Nonempty (V ⊓ P : X.Opens) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    intro a b hab
    have hi := map_injective_of_isIntegral X (homOfLE (inf_le_left : V ⊓ P ≤ V))
    ext
    apply hi
    have := congrArg (fun w : Γ(X, V ⊓ P)ˣ => (w : Γ(X, V ⊓ P))) hab
    simpa [res] using this
  · have hb : V = ⊥ := by
      ext z; simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hz; exact hV ⟨z, hz⟩
    subst hb
    intro a b _
    exact Subsingleton.elim a b

theorem ratio_res {p : ℕ} [Fact p.Prime] {X : Scheme.{0}} {Xw : X.Opens} {K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]}
    (h : ∀ x : X, UnitChartAt p Xw K x) (x y : X) (u : Γ(X, Uc h x ⊓ Uc h y)ˣ) (hu : RatioProp h x y u)
    (W : X.Opens) (hW : W ≤ Uc h x ⊓ Uc h y ⊓ Xp X p) :
    res (hW.trans inf_le_left) u *
      res (hW.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (Cx h y) =
    res (hW.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)) (Cx h x) := by
  have := congrArg (res hW) hu.1
  rwa [map_mul, res_res', res_res', res_res'] at this

end GlobalTheory.UnitGlue.IsLBProof

namespace GlobalTheory.UnitGlue

open GlobalTheory.UnitGlue.IsLBProof in

theorem glueLB_isLB : ∀ (p : ℕ) [Fact p.Prime] (X : Scheme.{0}) (Xw : X.Opens) (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]) (h : ∀ x : X, UnitChartAt p Xw K x), IsIntegral X → (Xw : Set X).Nonempty → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (∀ x y : X, ∃ u, RatioProp h x y u) → (glueLB h).IsLB := by
  intro p _ X Xw K h hI hw hle hex
  have hP : ((Xp X p : X.Opens) : Set X).Nonempty := hw.mono hle
  have hR : ∀ x y, RatioProp h x y (gU h x y) := fun x y => by
    unfold gU; rw [dif_pos (hex x y)]; exact (hex x y).choose_spec
  refine ⟨?_, fun (i : X) => ?_, fun (i j k : X) => ?_⟩
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    refine ⟨x, ?_⟩
    obtain ⟨y, hy⟩ := (c_spec h x).2.1
    show x ∈ ((cξ h x ''ᵁ ⊤ : X.Opens) : Set X)
    exact ⟨y, trivial, hy⟩
  · show res (le_inf le_rfl le_rfl : Uc h i ≤ Uc h i ⊓ Uc h i) (gU h i i) = 1
    apply res_inj (Xp X p) hP (Uc h i)
    rw [res_res', map_one]
    have hW : Uc h i ⊓ Xp X p ≤ Uc h i ⊓ Uc h i ⊓ Xp X p := le_inf (le_inf inf_le_left inf_le_left) inf_le_right
    have h1 := ratio_res h i i _ (hR i i) _ hW
    have h2 : res (hW.trans inf_le_left) (gU h i i) = 1 := by
      have h3 := h1
      rw [mul_eq_right] at h3
      exact h3
    exact h2
  · show res (inf_le_left : Uc h i ⊓ Uc h j ⊓ Uc h k ≤ Uc h i ⊓ Uc h j) (gU h i j) *
      res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : Uc h i ⊓ Uc h j ⊓ Uc h k ≤ Uc h j ⊓ Uc h k) (gU h j k) =
      res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : Uc h i ⊓ Uc h j ⊓ Uc h k ≤ Uc h i ⊓ Uc h k) (gU h i k)
    apply res_inj (Xp X p) hP _
    rw [map_mul, res_res', res_res', res_res']
    have hT : Uc h i ⊓ Uc h j ⊓ Uc h k ⊓ Xp X p ≤ Uc h i ⊓ Uc h j ⊓ Xp X p :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hT2 : Uc h i ⊓ Uc h j ⊓ Uc h k ⊓ Xp X p ≤ Uc h j ⊓ Uc h k ⊓ Xp X p :=
      le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right)) (inf_le_left.trans inf_le_right)) inf_le_right
    have hT3 : Uc h i ⊓ Uc h j ⊓ Uc h k ⊓ Xp X p ≤ Uc h i ⊓ Uc h k ⊓ Xp X p :=
      le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)) inf_le_right
    have hij := ratio_res h i j _ (hR i j) _ hT
    have hjk := ratio_res h j k _ (hR j k) _ hT2
    have hik := ratio_res h i k _ (hR i k) _ hT3
    apply mul_right_cancel (b := res (hT2.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)) (Cx h k))
    rw [_root_.mul_assoc, hjk, hij, hik]

end GlobalTheory.UnitGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramFrameCongruenceSubgroupStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_frame_congruence_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ Ψ' : Finset (E →+* ℂ)) (G G' : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (x' : Frame Ψ' r) (p0 : Ψ → ℕ) (p1 : ℕ) (Γ : Subgroup (GL (Fin r) E)), Ψ' = Ψ → G' = -G → (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → (∀ τ : Ψ', gram τ.1 G' (mat x' τ) = Matrix.diagonal fun a : Fin r => ((sgn p1 (a : ℕ) : ℝ) : ℂ)) → covolume (inReal Ψ G Γ) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ' G' Γ) (realSU Ψ' G') (riemHaar Ψ' G' x') := by
  first | exact @GlobalTheory.CovolNegFrame.covolume_neg_frame | exact GlobalTheory.CovolNegFrame.covolume_neg_frame | (intros; apply GlobalTheory.CovolNegFrame.covolume_neg_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentUniqueness
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstDeform

theorem objMap_const : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ o : Obj Dw l (baseKA l) (x' ≫ Xo.s), Nonempty (ObjMap o Xo.univ x') → Nonempty (ObjMap o Xo.univ (constPt x')) := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o ⟨m⟩
  have hw : m.cm.F ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ x' := m.cart.1.w
  let g : o.t.G.left ⟶ A'.left := hπ'.1.lift m.cm.F o.t.G.hom hw
  have hg : g ≫ π' = m.cm.F := hπ'.1.lift_fst _ _ _
  have hgw : g ≫ A'.hom = o.t.G.hom := hπ'.1.lift_snd _ _ _
  have hgc : IsGrpPullback o.t.G A' (𝟙 _) g :=
    hπ'.cancel (m.cart.congr (Category.id_comp _).symm hg.symm) (by rw [hgw, Category.comp_id])
  have hred : spMap (algebraMap K (DualNumber K)) ≫ y.x = constPt x' := by
    rw [← hT.2]; rfl
  have hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π) :=
    (hgc.comp (hq.comp hπ)).congr (by rw [Category.id_comp, hred]) rfl
  haveI : CharZero K := (RingHom.charZero_iff (algebraMap c.F K).injective).1 inferInstance
  have hgq := hgc.comp hq
  have hcomm : ∀ (T : Over (Sp K)) (x y : T ⟶ A), x * y = y * x := by
    intro T x y
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · have e1 := hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl
      have e2 := hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl
      rw [← e1, ← e2, _root_.mul_comm]
    · rw [Over.w (x * y), Over.w (y * x)]

  have key : ∀ (σ : 𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G) (τ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (n : ℕ),
      0 < n → σ ^ n = 1 → σ.left ≫ m.cm.F = x' ≫ τ.left →
      σ.left ≫ (g ≫ q ≫ π) = constPt x' ≫ τ.left := by
    intro σ τ n hn hσ hστ
    let u := pushHom hgq (𝟙_ (Over (Sp (DualNumber K)))) σ
    have hu : u ^ n = 1 := by rw [← map_pow, hσ, map_one]
    have e := GlobalTheory.T.torsion_dualNumber_point_eq_constant_charZero K A _ (by simp) (hcomm _) u n hn hu
    have hul : u.left = σ.left ≫ g ≫ q := by
      show σ.left ≫ (g ≫ q) = _; rfl
    rw [hul] at e
    let w := spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ g
    have hw' : w ≫ A'.hom = 𝟙 _ ≫ GlobalTheory.DeRham.epsRed K := by
      simp only [w, Category.assoc, hgw, Category.id_comp]
      rw [Over.w σ]; rfl
    let s₀ := hi.1.lift w (𝟙 _) hw'
    have hs₀ : s₀ ≫ i = w := hi.1.lift_fst _ _ _
    calc σ.left ≫ (g ≫ q ≫ π) = (σ.left ≫ g ≫ q) ≫ π := by simp only [Category.assoc]
      _ = (spMap (algebraMap K (DualNumber K)) ≫ w ≫ q) ≫ π := by rw [e]; simp only [w, Category.assoc]
      _ = spMap (algebraMap K (DualNumber K)) ≫ s₀ ≫ i ≫ π' := by
          rw [← hs₀]; simp only [Category.assoc]; rw [reassoc_of% hiq, hiπ]
      _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ σ.left ≫ m.cm.F := by
          rw [reassoc_of% hs₀]; simp only [w, Category.assoc, hg]
      _ = constPt x' ≫ τ.left := by rw [hστ]; rfl
  have hpow : ∀ (f : Dw.La → (𝟙_ (Over (Sp (DualNumber K))) ⟶ o.t.G)), (∀ a b, f (a + b) = f a * f b) →
      ∀ (n : ℕ) a, f (n • a) = f a ^ n := by
    intro f hf n a
    induction n with
    | zero =>
      have h0 := hf 0 0
      rw [add_zero] at h0
      rw [zero_smul, pow_zero]
      exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
    | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]
  have hM : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb := by
    have h1 : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left (I := l.Mb) (J := l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) h1
  exact ⟨{
    cm := cubeMapOf hF
    cart := hF
    base := rfl
    act := GlobalTheory.T.group_lift_tangent_Phi_linear hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    lin := GlobalTheory.T.group_lift_tangent_Phi_additive hP hGD E H Dw l Xo c K y x' hpq hT A A' π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF
    eta := fun a => key (o.eta a) (Xo.univ.eta a) l.M (by have := l.three_le; omega)
      (by rw [← hpow _ o.eta_add]; exact o.eta_ker _ (by
        rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]; exact Submodule.smul_mem_smul hM Submodule.mem_top))
      (m.eta a)
    etaA := fun a => key (o.etaA a) (Xo.univ.etaA a) l.A l.A_pos
      (by rw [← hpow _ o.etaA_add]; exact o.etaA_ker a) (m.etaA a) }⟩

end GlobalTheory.ConstDeform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CharPMatrix

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]

def redHom : ℤ_[p] →+* k := (ZMod.castHom (dvd_refl p) k).comp PadicInt.toZMod

lemma exists_nat_add (z : ℤ_[p]) : ∃ n : ℕ, ∃ w : ℤ_[p], z = n + p * w := by
  have h := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨PadicInt.zmodRepr z, w, by rw [mul_comm, hw]; ring⟩

variable (B : Type) [Ring B] [Algebra k B]

def tensorPadicEquiv : B ⊗[ℤ] ℤ_[p] ≃ₐ[k] B :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (AlgHom.id k B)
      (((algebraMap k B).comp (redHom p k)).toIntAlgHom)
      (by intro x y; exact Algebra.commute_algebraMap_right _ _))
    Algebra.TensorProduct.includeLeft
    (by ext b; simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply]; erw [Algebra.TensorProduct.lift_tmul]; simp)
    (by
      apply Algebra.TensorProduct.ext'
      intro b z
      obtain ⟨n, w, rfl⟩ := exists_nat_add p z
      have hp : (p : B) = 0 := by
        rw [← map_natCast (algebraMap k B), CharP.cast_eq_zero, map_zero]
      simp [redHom, Algebra.TensorProduct.lift_tmul]
      have h1 : b ⊗ₜ[ℤ] ((p : ℤ_[p]) * w) = 0 := by
        rw [show ((p : ℤ_[p]) * w) = (p : ℤ) • w by simp, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, eq_intCast, Int.cast_natCast, hp, zero_mul,
          TensorProduct.zero_tmul]
      have h2 : b ⊗ₜ[ℤ] (n : ℤ_[p]) = (b * n) ⊗ₜ[ℤ] 1 := by
        rw [show (n : ℤ_[p]) = (n : ℤ) • (1 : ℤ_[p]) by simp, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, eq_intCast, Int.cast_natCast, Nat.cast_comm]
      rw [TensorProduct.tmul_add, h1, h2, add_zero])

def matrixBaseChange (R : Type) [CommRing R] (K : Type) [CommRing K] [Algebra R K]
    (n : Type) [Fintype n] [DecidableEq n] : K ⊗[R] Matrix n n R ≃ₐ[K] Matrix n n K :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n R K).symm.toRingEquiv) (by
    intro c
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Algebra.algebraMap_eq_smul_one])

end GlobalTheory.CharPMatrix

namespace GlobalTheory.UPel.HT

open GlobalTheory.CharPMatrix in

theorem Datum.charP_tensor_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k]
    [CharP k p] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  intro p _ D k _ _ _
  obtain ⟨e⟩ := D.splitP
  have E0 : k ⊗[𝓞 D.F] (𝓞 D.F ⊗[ℤ] ℤ_[p]) ≃ₐ[k] k :=
    (Algebra.TensorProduct.cancelBaseChange ℤ (𝓞 D.F) k k ℤ_[p]).trans (tensorPadicEquiv p k k)
  have E1 := (Algebra.TensorProduct.assoc ℤ (𝓞 D.F) (𝓞 D.F) D.O (𝓞 D.F) ℤ_[p]).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid (𝓞 D.F) (𝓞 D.F) D.O) (AlgEquiv.refl (R := ℤ) (A₁ := ℤ_[p])))
  have E2 := E1.trans e
  exact ⟨(Algebra.TensorProduct.congr E0.symm (AlgEquiv.refl (R := 𝓞 D.F) (A₁ := D.O))).trans
    ((Algebra.TensorProduct.assoc (𝓞 D.F) (𝓞 D.F) k k (𝓞 D.F ⊗[ℤ] ℤ_[p]) D.O).trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl
      ((Algebra.TensorProduct.comm (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]) D.O).trans
        (E2.trans (matrixEquivTensor (Fin D.m) (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]))))).trans
    ((Algebra.TensorProduct.assoc (𝓞 D.F) (𝓞 D.F) k k (𝓞 D.F ⊗[ℤ] ℤ_[p])
      (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F))).symm.trans
    ((Algebra.TensorProduct.congr E0 AlgEquiv.refl).trans
    (matrixBaseChange (𝓞 D.F) k (Fin D.m))))))⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDualNumberCoordsOfAdicSumStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_dualNumber_coords_of_adicSum : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V] (I : Ideal V) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V I C → ∀ {Ix : Type} (x : Ix → DualNumber V) (s : DualNumber V), GlobalTheory.UT.SumI I x s → HasSum (fun i => toF V C (x i).fst) (toF V C s.fst) ∧ HasSum (fun i => toF V C (x i).snd) (toF V C s.snd) := by
  first | exact @GlobalTheory.AdicDual.hasSum_fst_snd | exact GlobalTheory.AdicDual.hasSum_fst_snd | (intros; apply GlobalTheory.AdicDual.hasSum_fst_snd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapInfOfFlatStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_comap_inf_of_flat : ∀ (W V : Scheme.{0}) (g : V ⟶ W), Flat g → ∀ a b : W.IdealSheafData, (a ⊓ b).comap g = a.comap g ⊓ b.comap g := by
  first | exact @GlobalTheory.FlatInf.comap_inf_of_flat | exact GlobalTheory.FlatInf.comap_inf_of_flat | (intros; apply GlobalTheory.FlatInf.comap_inf_of_flat <;> assumption)
end

