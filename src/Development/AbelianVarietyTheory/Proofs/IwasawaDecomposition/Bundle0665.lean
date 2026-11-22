import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0614
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0622
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0612
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplexPointDerivationSeparatingParamsChar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtDerivSep

open IsLocalRing

theorem exists_der_of_rsp {k R : Type} [Field k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra k R] [Algebra.FormallySmooth k (ResidueField R)] (ψ : R →+* ℂ) [IsLocalHom ψ] (m : ℕ)
    (f : Fin m → R) (hf : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m f) (l : Fin m → ℂ) (hl : l ≠ 0) :
    ∃ D : R →+ ℂ, (∀ a : k, D (algebraMap k R a) = 0) ∧
      (∀ x y, D (x * y) = ψ x * D y + ψ y * D x) ∧ ∑ i, l i * D (f i) ≠ 0 := by
  classical
  obtain ⟨hspan, hdim⟩ := hf
  have hfm : ∀ i, f i ∈ maximalIdeal R := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  let v : Fin m → CotangentSpace R := fun i => (maximalIdeal R).toCotangent ⟨f i, hfm i⟩
  have hv : Submodule.span (ResidueField R) (Set.range v) = ⊤ := by
    have e : Set.range v = (maximalIdeal R).toCotangent '' Set.range
        (fun i => (⟨f i, hfm i⟩ : maximalIdeal R)) := by
      rw [← Set.range_comp]; rfl
    rw [e, CotangentSpace.span_image_eq_top_iff]
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hspan
  have hfr : Module.finrank (ResidueField R) (CotangentSpace R) = m := by
    apply le_antisymm
    · rw [← finrank_top (ResidueField R) (CotangentSpace R), ← hv]
      exact (finrank_range_le_card v).trans (by simp)
    · have h1 := ringKrullDim_le_spanFinrank_maximalIdeal R
      rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, ← hdim] at h1
      exact_mod_cast h1
  have hli : LinearIndependent (ResidueField R) v :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [hfr])
  let b := Module.Basis.mk hli hv.ge
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hl

  let emb : ResidueField R →+* ℂ := ResidueField.lift ψ
  have hemb : ∀ r : R, emb (residue R r) = ψ r := fun r => ResidueField.lift_residue_apply ψ r
  let g : R ⧸ maximalIdeal R ^ 2 →ₐ[k] ResidueField R :=
    Ideal.Quotient.liftₐ (maximalIdeal R ^ 2) (IsScalarTower.toAlgHom k R (ResidueField R))
      (fun a ha => (residue_eq_zero_iff a).2 (Ideal.pow_le_self two_ne_zero ha))
  have hgr : ∀ r : R, g (Ideal.Quotient.mk _ r) = residue R r := fun r => rfl
  have hg : Function.Surjective g := by
    intro c
    obtain ⟨r, rfl⟩ := residue_surjective c
    exact ⟨Ideal.Quotient.mk _ r, hgr r⟩
  have hnil : IsNilpotent (RingHom.ker g) := by
    refine ⟨2, le_bot_iff.1 ?_⟩
    rw [pow_two (RingHom.ker g), Ideal.mul_le]
    intro x hx y hy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hr : r ∈ maximalIdeal R := (residue_eq_zero_iff r).1 ((hgr r).symm.trans (RingHom.mem_ker.1 hx))
    have hs : s ∈ maximalIdeal R := (residue_eq_zero_iff s).1 ((hgr s).symm.trans (RingHom.mem_ker.1 hy))
    rw [← map_mul, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul hr hs
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k (ResidueField R)) g hg hnil
  have hs : ∀ c, g (s c) = c := fun c =>
    congrArg (fun φ : ResidueField R →ₐ[k] ResidueField R => φ c)
      (Algebra.FormallySmooth.comp_liftOfSurjective (AlgHom.id k (ResidueField R)) g hg hnil)
  let t : ResidueField R → R := fun c => Function.surjInv Ideal.Quotient.mk_surjective (s c)
  have ht : ∀ c, Ideal.Quotient.mk (maximalIdeal R ^ 2) (t c) = s c := fun c =>
    Function.surjInv_eq Ideal.Quotient.mk_surjective (s c)
  have hrt : ∀ c, residue R (t c) = c := fun c => by rw [← hgr, ht, hs]
  let e : R → R := fun r => r - t (residue R r)
  have he : ∀ r, e r ∈ maximalIdeal R := fun r =>
    (residue_eq_zero_iff _).1 (by simp only [e, map_sub, hrt, sub_self])
  have hmk : ∀ a : R, Ideal.Quotient.mk (maximalIdeal R ^ 2) a = 0 → a ∈ maximalIdeal R ^ 2 :=
    fun a h => Ideal.Quotient.eq_zero_iff_mem.1 h
  have hcot : ∀ (a a' : R) (ha : a ∈ maximalIdeal R) (ha' : a' ∈ maximalIdeal R),
      a - a' ∈ maximalIdeal R ^ 2 →
      (maximalIdeal R).toCotangent ⟨a, ha⟩ = (maximalIdeal R).toCotangent ⟨a', ha'⟩ :=
    fun a a' ha ha' h => (Ideal.toCotangent_eq _).2 h
  let D0 : R → ℂ := fun r => emb (b.repr ((maximalIdeal R).toCotangent ⟨e r, he r⟩) j)
  have hadd : ∀ x y, D0 (x + y) = D0 x + D0 y := by
    intro x y
    have h1 : (maximalIdeal R).toCotangent ⟨e (x + y), he (x + y)⟩ =
        (maximalIdeal R).toCotangent ⟨e x + e y, add_mem (he x) (he y)⟩ := by
      refine hcot _ _ _ _ (hmk _ ?_)
      simp only [e, map_sub, map_add, ht]
      ring
    have h2 := map_add (maximalIdeal R).toCotangent ⟨e x, he x⟩ ⟨e y, he y⟩
    simp only [D0, h1]
    rw [show (⟨e x + e y, add_mem (he x) (he y)⟩ : maximalIdeal R) = ⟨e x, he x⟩ + ⟨e y, he y⟩ from rfl,
      h2, map_add, Finsupp.add_apply, map_add]
  have hmul : ∀ x y, D0 (x * y) = ψ x * D0 y + ψ y * D0 x := by
    intro x y
    have hm2 : ∀ a b : R, a ∈ maximalIdeal R → b ∈ maximalIdeal R → a * b ∈ maximalIdeal R ^ 2 :=
      fun a b ha hb => by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    have h1 : (maximalIdeal R).toCotangent ⟨e (x * y), he (x * y)⟩ =
        (maximalIdeal R).toCotangent (t (residue R x) • (⟨e y, he y⟩ : maximalIdeal R) +
          t (residue R y) • (⟨e x, he x⟩ : maximalIdeal R)) := by
      refine hcot _ _ _ _ ?_
      have q : e (x * y) - (t (residue R x) * e y + t (residue R y) * e x) =
          e x * e y + (t (residue R x) * t (residue R y) - t (residue R (x * y))) := by
        simp only [e]; ring
      change e (x * y) - (t (residue R x) * e y + t (residue R y) * e x) ∈ _
      rw [q]
      refine add_mem (hm2 _ _ (he x) (he y)) (hmk _ ?_)
      rw [map_sub, map_mul, ht, ht, ht, map_mul, map_mul, sub_self]
    simp only [D0, h1, map_add, map_smul]
    rw [← algebraMap_smul (ResidueField R) (t (residue R x)),
      ← algebraMap_smul (ResidueField R) (t (residue R y)), map_smul, map_smul,
      Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
      map_add, map_mul, map_mul, ResidueField.algebraMap_eq, hrt, hrt, hemb, hemb]
  let D : R →+ ℂ := AddMonoidHom.mk' D0 hadd
  refine ⟨D, fun a => ?_, hmul, ?_⟩
  · change D0 _ = 0
    have h1 : (maximalIdeal R).toCotangent ⟨e (algebraMap k R a), he _⟩ =
        (maximalIdeal R).toCotangent ⟨0, zero_mem _⟩ := by
      refine hcot _ _ _ _ (hmk _ ?_)
      have r1 : residue R (algebraMap k R a) = algebraMap k (ResidueField R) a :=
        (IsScalarTower.algebraMap_apply k R (ResidueField R) a).symm
      show Ideal.Quotient.mk _ (algebraMap k R a - t (residue R (algebraMap k R a)) - 0) = 0
      rw [sub_zero, map_sub, ht, r1, AlgHom.commutes, Ideal.Quotient.mk_algebraMap, sub_self]
    simp only [D0, h1]
    rw [show (⟨0, zero_mem _⟩ : maximalIdeal R) = 0 from rfl, map_zero, map_zero, Finsupp.zero_apply,
      map_zero]
  · have hfi : ∀ i, D0 (f i) = emb (Finsupp.single i 1 j) := by
      intro i
      have h1 : (maximalIdeal R).toCotangent ⟨e (f i), he _⟩ = b i := by
        rw [Module.Basis.mk_apply]
        refine hcot _ _ _ _ (hmk _ ?_)
        have r0 : residue R (f i) = 0 := (residue_eq_zero_iff _).2 (hfm i)
        show Ideal.Quotient.mk _ (f i - t (residue R (f i)) - f i) = 0
        rw [r0, sub_sub_cancel_left, map_neg, ht, map_zero, neg_zero]
      simp only [D0, h1, Module.Basis.repr_self]
    change ∑ i, l i * D0 (f i) ≠ 0
    simp only [hfi]
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [Finsupp.single_apply, if_neg hi, map_zero, mul_zero])
      (fun h => (h (Finset.mem_univ j)).elim), Finsupp.single_eq_same, map_one, _root_.mul_one]
    exact hj

end GlobalTheory.PtDerivSep

namespace GlobalTheory.PtDerivSep

open IsLocalRing

theorem exists_ptDer_sep : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (n : ℕ) (σ : k →+* ℂ), SmoothOfRelativeDimension n p → ∀ (x₀ : CxPts p σ) (U : Y.affineOpens) (hy : x₀.1 (IsLocalRing.closedPoint ℂ) ∈ U.1) (m : ℕ) (f : Fin m → Γ(Y, U.1)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) m (fun i => Y.presheaf.germ U.1 _ hy (f i)) → ∀ l : Fin m → ℂ, l ≠ 0 → ∃ δ : Γ(Y, U.1) →+ ℂ, (∀ a : k, δ (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1 a) = 0) ∧ (∀ g h : Γ(Y, U.1), δ (g * h) = CxPts.ev p σ U.1 g x₀ * δ h + CxPts.ev p σ U.1 h x₀ * δ g) ∧ ∑ i, l i * δ (f i) ≠ 0 := by
  intro k _ _ Y p n σ hsm x₀ U hy m f hR l hl
  haveI := hsm
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  let c : k →+* Γ(Y, U.1) := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U.1
  have hft : c.FiniteType := (p.finiteType_appLE (isAffineOpen_top _) U.2 le_top).comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  let germ : Γ(Y, U.1) →+* Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)) :=
    (Y.presheaf.germ U.1 _ hy).hom
  have hloc : germ.EssFiniteType := by
    letI := Y.presheaf.algebra_section_stalk (⟨_, hy⟩ : U.1)
    haveI := U.2.isLocalization_stalk ⟨_, hy⟩
    exact Algebra.EssFiniteType.of_isLocalization (Y.presheaf.stalk _)
      (U.2.primeIdealOf ⟨_, hy⟩).asIdeal.primeCompl
  have hnoeth : IsNoetherianRing (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) := by
    letI := c.toAlgebra
    haveI : Algebra.FiniteType k Γ(Y, U.1) := hft
    haveI : IsNoetherianRing Γ(Y, U.1) := Algebra.FiniteType.isNoetherianRing k _
    letI := Y.presheaf.algebra_section_stalk (⟨_, hy⟩ : U.1)
    haveI := U.2.isLocalization_stalk ⟨_, hy⟩
    exact IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨_, hy⟩).asIdeal.primeCompl _ inferInstance
  letI : Algebra k (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) := (germ.comp c).toAlgebra
  haveI : Algebra.EssFiniteType k (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ))) :=
    RingHom.essFiniteType_algebraMap.1 (hft.essFiniteType.comp hloc)
  haveI : Algebra.EssFiniteType k (ResidueField (Y.presheaf.stalk (x₀.1 (IsLocalRing.closedPoint ℂ)))) :=
    .of_surjective (IsScalarTower.toAlgHom k _ _) residue_surjective
  let ψ := (Scheme.stalkClosedPointTo (R := CommRingCat.of ℂ) x₀.1).hom
  obtain ⟨D, h1, h2, h3⟩ := exists_der_of_rsp (k := k) ψ m _ hR l hl
  have hx : x₀ ∈ CxPts.ptsIn p σ U.1 := CxPts.mem_ptsIn.2 hy
  have hψ : ∀ g, ψ (germ g) = CxPts.ev p σ U.1 g x₀ := by
    intro g
    rw [CxPts.ev_eq hx, CxPts.evHom, ← GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap x₀.1 U.1 hx]
    rfl
  refine ⟨D.comp germ.toAddMonoidHom, fun a => h1 a, fun g h => ?_, h3⟩
  simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_mul, h2, hψ]

end GlobalTheory.PtDerivSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDeRhamFlag
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

section Retype

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F} {M : Model Xo c V.subtype}
  {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

theorem sameFlag_insert_zero {X₀ : Scheme.{0}} {t : SAB H X₀} {R : Type} [CommRing R] (x : Sp R ⟶ X₀)
    (u u' : Vecs Dw t R) : SameFlag (fun σ => insert 0 (ty σ)) t x u u' ↔ SameFlag ty t x u u' := by
  refine ⟨fun h σ k hk => h σ k (Finset.mem_insert_of_mem hk), fun h σ k hk i hi => ?_⟩
  rcases Finset.mem_insert.1 hk with rfl | hk
  · exact absurd hi (Nat.not_lt_zero _)
  · exact h σ k hk i hi

theorem flagAt_insert_zero (A : PreAtlas M X) {K : Type} [Field K] (w : Sp K ⟶ X) (u : Vecs Dw M.t K) :
    A.FlagAt π (fun σ => insert 0 (ty σ)) w u ↔ A.FlagAt π ty w u := by
  simp only [PreAtlas.FlagAt, sameFlag_insert_zero]

def Atlas.addZero (A : Atlas M π ty) : Atlas M π (fun σ => insert 0 (ty σ)) where
  toPreAtlas := A.toPreAtlas
  cover := A.cover
  alg_s := A.alg_s
  smooth := A.smooth
  frame := A.frame
  glue k _ a a' φ φ' h := (sameFlag_insert_zero _ _ _).2 (A.glue k a a' φ φ' h)
  bij k _ f y hy u hu := by
    simp only [flagAt_insert_zero]
    exact A.bij k f y hy u hu

end Retype

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def PiLocalization₂ (Z : Mdl Y i₀) (k : (E →+* ℂ) → ℕ) : Prop :=
  ∃ (X : Scheme.{0}) (π : X ⟶ (Y Z.i).X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas (Y Z.i) π ty) (f : X ⟶ Z.X),
    Geo (Y Z.i) π ∧ f ≫ Z.π = π ∧ (∀ σ, Z.ty σ ⊆ ty σ) ∧ (∀ σ, ty σ ⊆ Finset.range (Dw.mult σ + 1)) ∧
    (∀ σ, Finset.range (k σ + 1) ⊆ ty σ) ∧ (∀ σ, IntStep A σ (k σ)) ∧
    (∀ (K : Type) [Field K] (w : Sp K ⟶ X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u → (atlasOf Z).FlagAt (w ≫ f) u) ∧
    ∀ Z'' : Mdl Y i₀, HasDR Z'' → (∃ g, IsMap Z'' Z g) → ∃ h, MapsTo Z'' A h

theorem stage_zero (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀)
    (hZ : ∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) : PiLocalization₂ Z fun _ => 0 := by
  have := isDiscreteValuationRing_V Z.i.c W hp hW
  refine ⟨Z.X, Z.π, _, (atlasOf Z).addZero, 𝟙 _, geoOf Z, Category.id_comp _, fun σ => Finset.subset_insert _ _,
    fun σ => Finset.insert_subset (by simp) (hZ σ), fun σ => by simp, fun σ => GlobalTheory.T.atlas_integral_at_index_zero E H Dw _ _ _ _ _ _ _ _ _ σ,
    fun K _ w u h => ?_, fun Z'' _ ⟨g, hg⟩ => ⟨g, fun k _ w hw => ?_⟩⟩
  · rw [Category.comp_id]
    exact (flagAt_insert_zero _ w u).1 h
  · obtain ⟨τ, mu, u, h1, h2, h3, h4⟩ := hg.2 k w hw
    exact ⟨τ, mu, u, h1, h2, h3, (flagAt_insert_zero _ _ _).2 h4⟩

theorem stage_succ (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) {k k' : (E →+* ℂ) → ℕ} (σ : E →+* ℂ)
    (hk : k σ < Dw.mult σ) (h₁ : k' σ = k σ + 1) (h₂ : ∀ σ', σ' ≠ σ → k' σ' = k σ') (h : PiLocalization₂ Z k) : PiLocalization₂ Z k' := by
  classical
  have := isDiscreteValuationRing_V Z.i.c W hp hW
  have : CharZero Z.i.c.F := RingHom.charZero Z.i.c.F.val.toRingHom
  obtain ⟨X, π, ty, A₀, f, geo, hf, s₁, s₂, s₃, int, fl, mn⟩ := h
  obtain ⟨D₀, N, hEm⟩ := GlobalTheory.T.exists_adapted_embedding E H Dw _ _ _ _ _ _ _ _ A₀ σ (k σ) geo
    (GlobalTheory.T.nonempty_adapted_of_intStep E H Dw _ _ _ _ _ _ _ _ A₀ σ (k σ) geo (int σ))
  obtain ⟨A, hA, α, hα⟩ := GlobalTheory.T.exists_atlas_refining_cocycle E H Dw _ _ _ _ _ _ _ _ A₀ D₀.C
  let D : Adapted A σ (k σ) :=
    ⟨D₀.C, D₀.b, fun a K _ w hw u hu => D₀.int a K w hw u ((hA K w _).1 hu), D₀.coord⟩
  have ex : ∃ r, k σ + r + 1 ∈ ty σ ∨ k σ + r + 1 = Dw.mult σ := ⟨Dw.mult σ - k σ - 1, Or.inr (by omega)⟩
  let r := Nat.find ex
  have hr : k σ + r + 1 ∈ ty σ ∨ k σ + r + 1 = Dw.mult σ := Nat.find_spec ex
  have hj : k σ + r + 1 ≤ Dw.mult σ := by
    rcases hr with h | h
    · exact Nat.lt_succ_iff.1 (Finset.mem_range.1 (s₂ σ h))
    · exact h.le
  have gap : ∀ e ∈ ty σ, e ≤ k σ ∨ k σ + r + 1 ≤ e := fun e he => by
    by_cases h : e ≤ k σ
    · exact Or.inl h
    · have : r ≤ e - k σ - 1 := Nat.find_min' ex (Or.inl (by rwa [show k σ + (e - k σ - 1) + 1 = e by omega]))
      exact Or.inr (by omega)
  obtain ⟨Sb, hSb⟩ := GlobalTheory.T.adapted_next_step_type E H Dw _ _ _ _ _ _ _ _ A σ (k σ) r D hj hr α hα
  obtain ⟨Cl⟩ := GlobalTheory.T.nonempty_closure_of_embedding _ X (π ≫ (Y Z.i).s) geo.proj geo.normal geo.flat D.C N hEm A.ch r Sb
  let ty' := Function.update ty σ (insert (k σ + 1) (ty σ))
  have t₁ : ty' σ = insert (k σ + 1) (ty σ) := Function.update_self _ _ _
  have t₂ : ∀ σ', σ' ≠ σ → ty' σ' = ty σ' := fun σ' h => Function.update_of_ne h _ _
  obtain ⟨A', rel⟩ := GlobalTheory.T.adapted_substep_closure E H Dw _ _ _ _ _ _ _ _ A σ (k σ) r D hj hk Sb Cl ty' hSb hr gap t₁ t₂
  have down : ∀ (K : Type) [Field K] (w : Sp K ⟶ Cl.Z') (u : Vecs Dw (Y Z.i).t K), A'.FlagAt w u →
      A₀.FlagAt (w ≫ Cl.f) u := fun K _ w u hu => by
    obtain ⟨a, φ, -, hfr, -⟩ := id hu
    rw [← Category.assoc] at hfr
    obtain ⟨U, rfl⟩ := exists_up fun σ i => (hfr.1 σ i).1
    exact (hA K _ _).1 ((rel K w U).1 hu).1
  have geo' : Geo (Y Z.i) (Cl.f ≫ π) :=
    ⟨by rw [Category.assoc]; exact Cl.proj, Cl.normal, by rw [Category.assoc]; exact Cl.flat, A'.cover ▸ by
      rw [A'.cover, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, ← A.cover, ← Cl.carrier_eq]
      exact Cl.dense⟩
  have s₂' : ∀ σ', ty' σ' ⊆ Finset.range (Dw.mult σ' + 1) := fun σ' => by
    by_cases e : σ' = σ
    · subst e
      rw [t₁]
      exact Finset.insert_subset (Finset.mem_range.2 (by omega)) (s₂ _)
    · rw [t₂ σ' e]; exact s₂ σ'
  refine ⟨Cl.Z', Cl.f ≫ π, ty', A', Cl.f ≫ f, geo', by rw [Category.assoc, hf], fun σ' => ?_, s₂', fun σ' => ?_,
    fun σ' => ?_, fun K _ w u hu => ?_, fun Z'' hd hg => ?_⟩
  · by_cases e : σ' = σ
    · subst e
      rw [t₁]
      exact (s₁ _).trans (Finset.subset_insert _ _)
    · rw [t₂ σ' e]; exact s₁ σ'
  · by_cases e : σ' = σ
    · subst e
      rw [t₁, h₁, Finset.range_add_one]
      exact Finset.insert_subset_insert _ (s₃ _)
    · rw [t₂ σ' e, h₂ σ' e]; exact s₃ σ'
  · by_cases e : σ' = σ
    · subst e
      rw [h₁]
      exact GlobalTheory.T.adapted_linear_pullback E H Dw _ _ _ _ _ _ _ _ A σ' (k σ') D hk _ Cl.f Cl.L ty' A' rel
    · rw [h₂ σ' e]
      exact GlobalTheory.T.atlas_pullback_preserves_step E H Dw _ _ _ _ _ _ _ _ A₀ σ' (k σ') _ Cl.f ty' A' down (int σ')
  · rw [← Category.assoc]
    exact fl K _ u (down K w u hu)
  · obtain ⟨g, hg'⟩ := mn Z'' hd hg
    obtain ⟨g₀, hc, -⟩ := hg
    have hg'' : MapsTo Z'' A g := fun K _ w hw => by
      obtain ⟨τ, mu, u, h1, h2, h3, h4⟩ := hg' K w hw
      exact ⟨τ, mu, u, h1, h2, h3, (hA K _ _).2 h4⟩
    exact GlobalTheory.T.atlas_model_comparison E H Dw Xo p W Y i₀ Z.i _ _ ty' A' Z'' hp hW geo' hc.2.1 (fun σ' => hd.1 σ' ▸ s₂' σ')
      (GlobalTheory.T.adapted_closure_local_system E H Dw Xo p W Y i₀ Z.i X π ty A σ (k σ) r D hk Sb Cl ty' A' Z'' g rel hd hg'')

theorem stage_all (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀)
    (hZ : ∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) (n : ℕ) :
    ∀ k : (E →+* ℂ) → ℕ, (∀ σ, k σ ≤ Dw.mult σ) → ∑ σ, k σ = n → PiLocalization₂ Z k := by
  classical
  induction n with
  | zero =>
    intro k _ h
    obtain rfl : k = fun _ => 0 := funext fun σ => Finset.sum_eq_zero_iff.1 h σ (Finset.mem_univ _)
    exact stage_zero hp hW Z hZ
  | succ n ih =>
    intro k hk h
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h ▸ n.succ_ne_zero : ∑ σ, k σ ≠ 0)
    have e₁ : Function.update k σ (k σ - 1) σ = k σ - 1 := Function.update_self _ _ _
    refine stage_succ hp hW Z (k := Function.update k σ (k σ - 1)) σ (by have := hk σ; omega) (by omega)
      (fun σ' e => (Function.update_of_ne e _ _).symm) (ih _ (fun σ' => ?_) ?_)
    · by_cases e : σ' = σ
      · subst e; have := hk σ'; omega
      · rw [Function.update_of_ne e]; exact hk σ'
    · rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ), Finset.erase_eq] at h
      omega

theorem exists_isDRFlag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ Z : Mdl Y i₀, (∀ σ, Z.ty σ ⊆ Finset.range (Dw.mult σ + 1)) → ∃ Z', IsDRFlag Z Z' := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z hZ
  obtain ⟨X, π, ty, A, f, geo, hf, s₁, s₂, s₃, int, fl, mn⟩ := stage_all hp hW Z hZ _ Dw.mult (fun _ => le_rfl) rfl
  obtain ⟨Z', e, hi, hty, m₁, m₂, m₃⟩ := GlobalTheory.T.exists_model_of_atlas E H Dw Xo p W Y i₀ Z.i X π ty A Z.dvd Z.le geo
  have full : ∀ σ, Z'.ty σ = Finset.range (Dw.mult σ + 1) := fun σ => hty ▸ (s₂ σ).antisymm (s₃ σ)
  refine ⟨Z', hi, GlobalTheory.T.hasDR_of_full_intStep E H Dw Xo p W Y i₀ Z' full fun σ => m₃ σ _ (int σ),
    ⟨e.hom ≫ f, ⟨hi ▸ ⟨dvd_rfl, le_rfl, dvd_rfl⟩, hi ▸ le_rfl, hty ▸ s₁⟩, m₂ _ _ _ (atlasOf Z) f hf fl⟩,
    fun Z'' hd hg => ?_⟩
  obtain ⟨h, hh⟩ := mn Z'' hd hg
  obtain ⟨g, hc, -⟩ := hg
  exact ⟨h ≫ e.inv, ⟨hi ▸ hc.1, hi ▸ hc.2.1, fun σ => by rw [full, hd.1]⟩, m₁ Z'' h hh⟩

end GlobalTheory.DRFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrLiftThroughEtaleChart
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.ChartLift

theorem eq_of_stalkClosedPointTo : ∀ {X : Scheme.{0}} {R W V : Type} [CommRing R] [IsLocalRing R] [CommRing W] [IsLocalRing W] [CommRing V] [IsLocalRing V] (ξ : Sp R ⟶ X) (χ : Sp W ⟶ X) (h : ξ (closedPoint R) = χ (closedPoint W)) (ψ : R →+* V) (f : W →+* V), IsLocalHom ψ → IsLocalHom f → ψ.comp (Scheme.stalkClosedPointTo ξ).hom = f.comp ((X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ).hom → spMap f ≫ χ = spMap ψ ≫ ξ := by
  intro X R W V _ _ _ _ _ _ ξ χ h ψ f hψ hf hc
  have key : ∀ (x y : X) (hxy : x = y) (g : X.presheaf.stalk y ⟶ CommRingCat.of V),
      Spec.map ((X.presheaf.stalkCongr (Inseparable.of_eq hxy)).hom ≫ g) ≫ X.fromSpecStalk x =
        Spec.map g ≫ X.fromSpecStalk y := by
    intro x y hxy g
    subst hxy
    simp
  have hc' : Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom ψ =
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Scheme.stalkClosedPointTo χ ≫ CommRingCat.ofHom f := by
    ext a
    exact congrArg (fun g : _ →+* V => g a) hc
  conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk χ]
  conv_rhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
  simp only [spMap, ← Category.assoc, ← Spec.map_comp]
  rw [hc', key _ _ h]

theorem exists_lift_to_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) {k : Type} [Field k] {m e : ℕ} (ξ : Sp (ChartRing k m e) ⟶ gen Y), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Y.X), χ (closedPoint W) = genι Y (ξ (closedPoint _)) → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V) (ψ : ChartRing k m e →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ ∧ spMap f ≫ χ = spMap ψ ≫ ξ ≫ genι Y := by
  intro E _ _ _ H D l Xo c Y k _ m e ξ hξ W _ _ _ hW χ hχ
  have hiso : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
    rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
    infer_instance
  haveI : IsIso (genι Y) := inferInstance
  let χ' : Sp W ⟶ gen Y := χ ≫ inv (genι Y)
  have hχχ : χ' ≫ genι Y = χ := by simp [χ']
  have hpt : ξ (closedPoint (ChartRing k m e)) = χ' (closedPoint W) := by
    have h1 : genι Y (χ' (closedPoint W)) = χ (closedPoint W) := by
      rw [← hχχ]; rfl
    apply (genι Y).isOpenEmbedding.injective
    rw [h1, hχ]
  let φ : (gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e))) →+* ChartRing k m e := (Scheme.stalkClosedPointTo ξ).hom
  let α : (gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e))) →+* W := (((gen Y).presheaf.stalkCongr (Inseparable.of_eq hpt)).hom ≫ Scheme.stalkClosedPointTo χ').hom
  haveI : IsLocalHom α := by
    simp only [α, CommRingCat.hom_comp]
    infer_instance
  haveI : IsLocalHom φ := Scheme.isLocalHom_stalkClosedPointTo' ξ
  obtain ⟨hflat, hmax, hfin⟩ := hξ
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hch0 : CharZero (ResidueField ((gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e))))) := by
    let g : c.F →+* ResidueField ((gen Y).presheaf.stalk (ξ (closedPoint (ChartRing k m e)))) :=
      (residue _).comp ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫
        (Sp c.F).presheaf.germ ⊤ ((genStr Y) (ξ (closedPoint _))) trivial ≫
        (genStr Y).stalkMap (ξ (closedPoint _))).hom
    exact (RingHom.charZero_iff g.injective).1 inferInstance
  obtain ⟨V, _, _, _, f, hV, hfinj, hfloc, σ, hσ⟩ := GlobalTheory.T.exists_dvr_residue_extension (ResidueField.map φ) hfin' hch0 W hW α inferInstance
  haveI := hV.2.1
  have : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI hCA : IsAdicComplete (maximalIdeal (ChartRing k m e)) (ChartRing k m e) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  obtain ⟨θ, q, hqm, hqθ, hqd, hgen, hind⟩ := GlobalTheory.T.exists_primitive_element_complete φ hfin' hch0
  obtain ⟨η, hη, -⟩ := GlobalTheory.T.exists_hensel_root_residue φ (f.comp α) σ (fun a => by rw [RingHom.comp_apply, ← hσ a, ResidueField.map_residue]) θ q hqm hqθ hqd
  have hgp := GlobalTheory.T.polynomial_approx_pow_maximal φ hmax θ hgen
  have hip := GlobalTheory.T.polynomial_approx_uniqueness φ hflat hmax θ q hqm hqθ hgp hind
  obtain ⟨ψ, hψ, hψl⟩ := GlobalTheory.T.hensel_roots_compatible φ (f.comp α) inferInstance θ η q hqm hqθ hη hgp hip
  refine ⟨V, inferInstance, inferInstance, inferInstance, f, ψ, hV, hfinj, hfloc, hψl, ?_⟩
  have hg := eq_of_stalkClosedPointTo ξ χ' hpt ψ f hψl hfloc hψ
  rw [← hχχ, ← Category.assoc, hg, Category.assoc]

end GlobalTheory.ChartLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfPhaseOneOverLawfulCoreStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometricHalf_phase_one_over_lawful_core : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → T.pb = R.C.P.pb → PreChar R → ValKs R → FrameKs T.Q.c.F R.MW → Formalism.L2.Host.ValLL D R.C → Finite T0 → QGuard R → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∃ dict mu chiW x₀ cE nW FW, ∃ B : GeoHalf (reCore T dict mu chiW x₀ cE) (updFW R nW FW) (fun _ => 1), B.κ = kapTop D ∧ InGeo B ∧ Fired (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) ∧ (∀ i, OneMapRowR (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) i) ∧ IoExt (updFW R nW FW) ∧ PreChar (updFW R nW FW) ∧ (updFW R nW FW).grp_chiW ∧ (updFW R nW FW).LUnif ∧ (updFW R nW FW).LIntegral ∧ LawsCore (reCore T dict mu chiW x₀ cE).toCore := by
  first | exact @GlobalTheory.GeoHalfTop.exists_geoHalf | exact GlobalTheory.GeoHalfTop.exists_geoHalf | (intros; apply GlobalTheory.GeoHalfTop.exists_geoHalf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicFibreExponentialsNearCentreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_fibre_exponentials_near_centre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n : ℕ) (e0 : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)), (0 : Fin n → ℂ) ∈ e0.target → IsHolTo e0.target (fun z => (e0.symm z).1) → ∃ (g : ℕ) (ρ : ℝ) (ex : ExpMaps Z σ g), 0 < ρ ∧ Metric.ball 0 ρ ⊆ e0.target ∧ IsHolTo (Metric.ball 0 ρ ×ˢ Set.univ) (fun zw : (Fin n → ℂ) × (Fin g → ℂ) => (ex (e0.symm zw.1) zw.2).left) ∧ ∀ x ∈ e0.source, ‖e0 x‖ < ρ → Function.Surjective (ex x) ∧ IsExpAt Z.t (x.1 ≫ genι Z) (ex x) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exists_expMaps_near_chart_centre | exact GlobalTheory.ShFam.Hor.LogCh.exists_expMaps_near_chart_centre | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exists_expMaps_near_chart_centre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallFieldStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_value_mem_smallField_of_infPart_eq_one : ∀ (X : Stages) (f : Fr X.B.toPre), Fld.charField f ≤ X.B.KsC → Formalism.L2.Host.ValLL0 X.toD7 (Fr.at X f) → VolTieG X.toD7 → ∃ (C : CoreJ X.toD7) (_ : Algebra C.Q.c.F X.toD7.what₂.LL), CorePin C.toCore (Fr.at X f).P.pb ∧ (∀ y : C.Q.c.F, X.B.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) = (y : ℂ)) ∧ (∀ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y ∈ X.B.LL0) ∧ (∀ x ∈ X.B.Ks, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = x) ∧ (∀ x : X.toD7.host.E, ∃ y : C.Q.c.F, algebraMap C.Q.c.F X.toD7.what₂.LL y = X.toD7.embE x) ∧ LawsJ C ∧ Formalism.IndefR.FWT.AlgTie C ∧ Formalism.L2.Host.ValLL X.toD7 (Fr.at X f) ∧ ∀ (T' : Type) (L : Formalism.IndefR.Links.LevCh X.toD7 T') (μ : T'), L.Is μ → L.C = Fr.at X f → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 → ∃ y : C.Q.c.F, ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap C.Q.c.F X.toD7.what₂.LL y) := by
  first | exact @GlobalTheory.CoreExact.exists_core_exact | exact GlobalTheory.CoreExact.exists_core_exact | (intros; apply GlobalTheory.CoreExact.exists_core_exact <;> assumption)
end

