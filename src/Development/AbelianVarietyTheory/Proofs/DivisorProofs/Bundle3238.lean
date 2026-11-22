import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2965
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitMulClauseOfGeneratesIffNonzero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0818
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2841
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationProductOfUniformisedGroups
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitModulusRationalPhaseMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitInverseExpansionEquivariantLabels
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem traitInv_eqv_value : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ lab E, LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (s : Fam D.toPre F (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), F₀.Over s → T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J J', Good C.P.L.L z J → Good C.A.L z J' → sval σ p z J = (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (J (p ≫ T.β)) (J' (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z J' := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hem
  obtain ⟨f, hfi, hf1, hf2⟩ := GlobalTheory.T.exists_fibre_iso_genericFibre_cover R hR D C W T F hem
  obtain ⟨lab', hq, hm⟩ := GlobalTheory.T.exists_torsionLabels_genericFibre_trait R hR D C j W T F em hem f hfi hf1 hf2
  have hW := T.cdvr
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have : CharZero R := hR.2
  have hcW : CharZero W := charZero_of_injective_ringHom T.inj
  have hsemi : IsSemiAbelian T.G := GlobalTheory.isSemiAbelian_of_unifPre_dvr W T.D' T.A T.G T.U.toUnifPre
  obtain ⟨w₀, hw₀⟩ := T.U.ext
  have hodd : Odd (C.n ^ j) := C.n_odd.pow
  obtain ⟨E', hE', hx⟩ := GlobalTheory.T.exists_equivariant_inverse_thetaExpansion W (maximalIdeal W) hW' hcW T.D' T.A T.G T.U hsemi F (C.n ^ j) hodd w₀ hw₀ lab' hq
  obtain ⟨lab, E, Φ, hlab, hE, hΦ, hrel⟩ := GlobalTheory.T.trait_equivariant_bijection_transport_cover R hR D C j wA hwA W T F em hem f hfi hf1 hf2 w₀ hw₀ lab' hm E' hE'
  refine ⟨lab, E, hlab, hE, ?_⟩
  intro F₀ s σ hs hσ Z p p' hβ hG z J J' hJ hJ'
  obtain ⟨JG, hJG⟩ := GlobalTheory.UU.exists_good_pt T.U.LG.isLB z
  obtain ⟨Jt, hJt⟩ := GlobalTheory.UU.exists_good_pt T.A.isLB z
  have hq1 : (p' ≫ inv f) ≫ f = p' := by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hG' : p ≫ T.G.hom = (p' ≫ inv f) ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [hG, ← hf1]; simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  have hβ' : p ≫ T.β = (p' ≫ inv f) ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β := by
    rw [hβ, ← hf2, Category.assoc, IsIso.inv_hom_id_assoc]
  exact (GlobalTheory.T.traitSection_integralExpansion_mem_range_inverseExpansion R hR D C j W T F w₀ hw₀ E' hx F₀ (Φ s) σ (hΦ s F₀ hs) hσ Z p (p' ≫ inv f) hβ' hG' z J JG Jt hJ hJG hJt).trans
    (hrel s Z p p' (p' ≫ inv f) hq1 hβ hG' z J J' JG Jt hJ hJ' hJG hJt).symm

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.TraitUniq

theorem form_of_assoc {V V' W : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [CommRing W] [IsDomain W]
    {Dg : DegPre V} {Dg' : DegPre V'} {ϖ : V} {ϖ' : V'} {β : LinearMap.BilinForm ℤ Dg.X}
    {β' : LinearMap.BilinForm ℤ Dg'.X} (hβ : ∀ a b, β a b = β b a) (hβ' : ∀ a b, β' a b = β' b a)
    (hm : IsMonomial Dg ![ϖ] ![β]) (hm' : IsMonomial Dg' ![ϖ'] ![β']) (f : V →+* W) (f' : V' →+* W)
    (ε : Dg.X ≃+ Dg'.X) {w : W} (hw : Irreducible w) {m m' : ℕ} (h : Associated (f ϖ) (w ^ m))
    (h' : Associated (f' ϖ') (w ^ m'))
    (hε : ∀ y r r', PsiCoord Dg y r → PsiCoord Dg' (ε y) r' → Associated (f r ^ 2) (f' r' ^ 2)) :
    ∀ a b, (m : ℤ) * β a b = m' * β' (ε a) (ε b) := by
  have key : ∀ a, (m : ℤ) * β a a = m' * β' (ε a) (ε a) := by
    intro a
    obtain ⟨u₁, n₁, hn₁, c₁⟩ := hm a
    obtain ⟨u₂, n₂, hn₂, c₂⟩ := hm' (ε a)
    have a₁ : Associated (f (u₁ * ∏ i, ![ϖ] i ^ n₁ i)) (w ^ (m * n₁ 0)) := by
      rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, pow_mul]
      exact (associated_unit_mul_left _ _ (u₁.isUnit.map f)).trans h.pow_pow
    have a₂ : Associated (f' (u₂ * ∏ i, ![ϖ'] i ^ n₂ i)) (w ^ (m' * n₂ 0)) := by
      rw [Fin.prod_univ_one, Matrix.cons_val_zero, map_mul, map_pow, pow_mul]
      exact (associated_unit_mul_left _ _ (u₂.isUnit.map f')).trans h'.pow_pow
    have a₃ := (a₁.pow_pow (n := 2)).symm.trans ((hε a _ _ c₁ c₂).trans (a₂.pow_pow (n := 2)))
    rw [← pow_mul, ← pow_mul] at a₃
    have e := GlobalTheory.SiegLoc.TraitOrd.eq_of_associated_pow hw a₃
    have h₀ : β a a = 2 * n₁ 0 := by simpa using hn₁ 0
    have h₀' : β' (ε a) (ε a) = 2 * n₂ 0 := by simpa using hn₂ 0
    rw [h₀, h₀']
    have e' := congrArg (fun x : ℕ => (x : ℤ)) e
    push_cast at e'
    linarith
  intro a b
  have k := key (a + b)
  have ka := key a
  have kb := key b
  simp only [map_add, LinearMap.add_apply] at k
  rw [hβ b a, hβ' (ε b) (ε a)] at k
  simp only [mul_add] at k
  linarith

theorem extIso {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {G₁ G₂ : Over (Sp W)} [GrpObj G₁]
    [GrpObj G₂] (h₁ : IsSemiAbelian G₁) (h₂ : IsSemiAbelian G₂)
    (e : (Over.pullback (jK W)).obj G₁ ≅ (Over.pullback (jK W)).obj G₂) (he : IsMonHom e.hom) :
    ∃ E : G₁ ≅ G₂, IsMonHom E.hom ∧ (Over.pullback (jK W)).map E.hom = e.hom := by
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₁ G₂ h₁ h₂ e.hom he
  obtain ⟨F₁, ⟨hF₁, hF₁'⟩, -⟩ :=
    GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₂ G₁ h₂ h₁ e.inv inferInstance
  refine ⟨⟨F, F₁, ?_, ?_⟩, hF, hF'⟩
  · exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₁ G₁ h₁ h₁ (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, hF', hF₁', e.hom_inv_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
  · exact (GlobalTheory.semiAbelian_hom_extends_uniquely_dvr W (FractionRing W) G₂ G₂ h₂ h₂ (𝟙 _) inferInstance).unique
      ⟨inferInstance, by rw [Functor.map_comp, hF₁', hF', e.inv_hom_id]⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem genFib (T : Trait F) {W : Type} [CommRing W] [IsDomain W] (f : T.V →+* W)
    (fK : FractionRing T.V →+* FractionRing W) (hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap W _ (f a)) :
    ∃ κ : ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).left ⟶ T.A.A.left,
      IsGrpPullback ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)) T.A.A (spMap fK) κ ∧
      κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) =
        pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ pullback.fst T.G.hom (spMap f) :=
  GlobalTheory.T.exists_genericFibre_pullback_siegelTrait_model g n o ζ F T W f fK hfK

theorem lamPull (T : Trait F) {W : Type} [CommRing W] [IsDomain W] (fK : FractionRing T.V →+* FractionRing W)
    (G'' : Over (Sp W)) [GrpObj G''] (β : G''.left ⟶ T.G.left)
    (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left)
    (hκ : IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ)
    (hκβ : κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β)
    (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left) (hα₂ : IsSquare (κ ≫ T.α) α₂) :
    LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') (T.U.LG.L.pull (pullback.fst G''.hom (jK W) ≫ β)))
      (F.univ.P.pull α₂) :=
  GlobalTheory.T.mumfordBundle_trait_fibre_eq_universal g n o ζ F T W fK G'' β κ hκ hκβ α₂ hα₂

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem isCN (T : Trait F) : GlobalTheory.TorRef.IsCN T.V := ⟨inferInstance, inferInstance, T.complete, T.char⟩

theorem isCN_of_base {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (h : GlobalTheory.Mum.Base W) : GlobalTheory.TorRef.IsCN W :=
  ⟨h.1.1, h.1.2.2.1, h.1.2.2.2, h.2⟩

theorem pull (T : Trait F) {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.TorRef.IsCN W) (f : T.V →+* W)
    (hf : Function.Injective f) (hl : IsLocalHom f) (fK : FractionRing T.V →+* FractionRing W)
    (G'' : Over (Sp W)) [GrpObj G''] [IsCommMonObj G''] (β : G''.left ⟶ T.G.left)
    (hβ : IsGrpPullback G'' T.G (spMap f) β) (κ : ((Over.pullback (jK W)).obj G'').left ⟶ T.A.A.left)
    (hκ : IsGrpPullback ((Over.pullback (jK W)).obj G'') T.A.A (spMap fK) κ)
    (hκβ : κ ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK T.V) = pullback.fst G''.hom (jK W) ≫ β)
    (α₂ : (G2 ((Over.pullback (jK W)).obj G'')).left ⟶ (G2 F.univ.A).left) (hα₂ : IsSquare (κ ≫ T.α) α₂) :
    ∃ (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G'')
      (ε : D'.toPre.X ≃+ T.D.toPre.X) (L : LB ((Over.pullback (jK W)).obj G'').left), L.IsLB ∧
      LBIso L (U'.LG.L.pull (pullback.fst G''.hom (jK W))) ∧
      LBIso (abelian₂ ((Over.pullback (jK W)).obj G'') L) (F.univ.P.pull α₂) ∧
      ∀ y r, PsiCoord T.D.toPre (ε y) r → ∃ u : Wˣ, PsiCoord D'.toPre y (u * f r) := by
  have hΛ := lamPull T fK G'' β κ hκ hκβ α₂ hα₂
  have gB := (isGrpPullback_pullback G'' (jK W)).comp hβ
  obtain ⟨hr, hs⟩ := GlobalTheory.T.rigidified_symmetric_lineBundle_groupPullback _ _ _ T.G _ _ gB T.U.LG T.U.symG T.U.symG_gen
  have hα := hκ.comp T.cart
  obtain ⟨ha, hamp, hkt⟩ := GlobalTheory.T.principalPolarization_of_mumfordBundle_siegelFibre o ζ g n F _ (spMap fK ≫ T.y) _ (κ ≫ T.α) α₂ hα hα₂ _
    (pull_isLB T.U.LG.isLB _) hr hs hΛ
  have hϖ : f T.ϖ ≠ 0 := fun h => T.irr.ne_zero (hf (h.trans (map_zero f).symm))
  obtain ⟨D', A', U', ε, hL, hc⟩ := GlobalTheory.T.exists_uniformisation_baseChange_with_coordinates T.V W (isCN T) hW f hl T.G T.semi T.D T.A T.U
    {p | T.ϖ ∉ p.asIdeal} (PrimeSpectrum.isOpen_basicOpen (a := T.ϖ))
    (fun y => T.mono.psiUnitOn y fun p hp => by simpa using hp) (fun h => hϖ (RingHom.mem_ker.1 h)) G'' β hβ ha hr hs
    hamp hkt
  exact ⟨D', A', U', ε, _, pull_isLB T.U.LG.isLB _, hL, hΛ, hc⟩

end GlobalTheory.Poinc.TraitUniq

namespace GlobalTheory.Poinc.TraitUniq

theorem traitUniq : TraitUniqSt := by
  intro g n o _ ζ F T T' W _ _ _ f f' fK fK' hW hdvr hf hf' hl hl' hK hK' hy w m m' hw hm hm'
  haveI := hdvr
  have hWC := isCN_of_base hW
  have hs₁ : IsSemiAbelian ((Over.pullback (spMap f)).obj T.G) := IsSemiAbelian.pullback (spMap f) T.G T.semi
  have hs₂ : IsSemiAbelian ((Over.pullback (spMap f')).obj T'.G) := IsSemiAbelian.pullback (spMap f') T'.G T'.semi
  obtain ⟨κ₁, hκ₁, hκβ₁⟩ := genFib T f fK hK
  obtain ⟨κ₂, hκ₂, hκβ₂⟩ := genFib T' f' fK' hK'
  have hα₁ := hκ₁.comp T.cart
  have hα₂ := (hκ₂.comp T'.cart).congr hy.symm rfl
  obtain ⟨e, he, heα⟩ := grpPullback_iso hα₁ hα₂
  obtain ⟨E, hE, hEe⟩ := extIso hs₁ hs₂ e he
  have w₁ := hα₁.1.w
  let α₂ := pullback.map ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).hom
    ((Over.pullback (jK W)).obj ((Over.pullback (spMap f)).obj T.G)).hom F.univ.A.hom F.univ.A.hom
    (κ₁ ≫ T.α) (κ₁ ≫ T.α) (spMap fK ≫ T.y) w₁.symm w₁.symm
  have hsq : IsSquare (κ₁ ≫ T.α) α₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hβ' : IsGrpPullback ((Over.pullback (spMap f)).obj T.G) T'.G (spMap f')
      (E.hom.left ≫ pullback.fst T'.G.hom (spMap f')) :=
    ((isGrpPullback_of_iso E).comp (isGrpPullback_pullback T'.G (spMap f'))).congr (Category.id_comp _) rfl
  have hκ' := ((isGrpPullback_of_iso e).comp hκ₂).congr (Category.id_comp _) rfl
  have hκβ' : (e.hom.left ≫ κ₂) ≫ T'.U.gen.inv.left ≫ pullback.fst T'.G.hom (jK T'.V) =
      pullback.fst ((Over.pullback (spMap f)).obj T.G).hom (jK W) ≫ E.hom.left ≫ pullback.fst T'.G.hom (spMap f') := by
    rw [Category.assoc, hκβ₂, ← Category.assoc, ← Category.assoc, ← hEe]
    congr 1
    exact pullback.lift_fst _ _ _
  have hsq' : IsSquare ((e.hom.left ≫ κ₂) ≫ T'.α) α₂ := by rw [Category.assoc, heα]; exact hsq
  obtain ⟨E₁, A₁, U₁, ε₁, L₁, l₁, i₁, m₁, c₁⟩ := pull T hWC f hf hl fK _ _ (isGrpPullback_pullback T.G (spMap f))
    κ₁ hκ₁ hκβ₁ α₂ hsq
  obtain ⟨E₂, A₂, U₂, ε₂, L₂, l₂, i₂, m₂, c₂⟩ := pull T' hWC f' hf' hl' fK' _ _ hβ' _ hκ' hκβ' α₂ hsq'
  have hΛ : LBIso (abelian₂ _ L₂) (abelian₂ _ L₁) :=
    LBIso.trans (DVR.linComb_isLB _ l₂ _ _) (pull_isLB F.univ.isLB _) (DVR.linComb_isLB _ l₁ _ _) m₂ m₁.symm
  obtain ⟨ε, hε⟩ := GlobalTheory.SqUnifCoord.main W hWC _ hs₁ E₂ E₁ A₂ A₁ U₂ U₁
    (GlobalTheory.squares_iso_of_lam_generic W hWC _ hs₁ E₂ E₁ A₂ A₁ U₂ U₁ L₂ L₁ l₂ l₁ i₂ i₁ hΛ)
  let ε₀ : T.D.toPre.X ≃+ T'.D.toPre.X := (ε₁.symm.trans ε).trans ε₂
  have hε₀ : ∀ z r₁ r₂, PsiCoord T.D.toPre z r₁ → PsiCoord T'.D.toPre (ε₀ z) r₂ →
      Associated (f r₁ ^ 2) (f' r₂ ^ 2) := by
    intro z r₁ r₂ h₁ h₂
    obtain ⟨u₁, k₁⟩ := c₁ (ε₁.symm z) r₁ (by rwa [AddEquiv.apply_symm_apply])
    obtain ⟨u₂, k₂⟩ := c₂ (ε (ε₁.symm z)) r₂ h₂
    have := hε _ _ _ k₂ k₁
    rw [mul_pow, mul_pow] at this
    exact ((associated_unit_mul_left _ _ (u₁.isUnit.pow 2)).symm.trans this.symm).trans
      (associated_unit_mul_left _ _ (u₂.isUnit.pow 2))
  exact ⟨ε₀, form_of_assoc T.symm T'.symm T.mono T'.mono f f' ε₀ hw hm hm' hε₀⟩

end GlobalTheory.Poinc.TraitUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelFiniteFlatSurjectiveOverBaseStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedKernel_finite_flat_surjective_over_base : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left], LocallyOfFiniteType T.hom → ∀ N : LB (A ⊗ T).left, Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧ IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧ ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  first | exact @GlobalTheory.TwistKernel.twisted_kernel | exact GlobalTheory.TwistKernel.twisted_kernel | (intros; apply GlobalTheory.TwistKernel.twisted_kernel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPullbackSymmetricClassIntegralCombination
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.QuadSum

variable {K : Type} [Field K]

theorem hom_finset_sum {B A : AbVar K} {J : Type} (s : Finset J) (g : J → (B ⟶ A)) :
    Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i ∈ s, g i) = ∏ i ∈ s, (g i).hom := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, add_hom, ih]

theorem lam_symm {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) :
    AbVar.lam c x y = AbVar.lam c y x := by
  unfold AbVar.lam
  rw [mul_comm x y]
  abel

theorem lam_prod_right {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x : Y ⟶ A.X) {J : Type}
    (s : Finset J) (y : J → (Y ⟶ A.X)) :
    AbVar.lam c x (∏ j ∈ s, y j) = ∑ j ∈ s, AbVar.lam c x (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x 1 1 0).2.2.1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x (y a) _ 0).1, ih]

theorem lam_prod_left {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} {J : Type}
    (s : Finset J) (x : J → (Y ⟶ A.X)) (y : Y ⟶ A.X) :
    AbVar.lam c (∏ i ∈ s, x i) y = ∑ i ∈ s, AbVar.lam c (x i) y := by
  rw [lam_symm, lam_prod_right]
  exact Finset.sum_congr rfl (fun i _ => lam_symm c y (x i))

theorem lam_zpow_zpow {A : AbVar K} (c : Pic A.X.left) {Y : Over (Sp K)} (x y : Y ⟶ A.X) (m n : ℤ) :
    AbVar.lam c (x ^ m) (y ^ n) = (m * n) • AbVar.lam c x y := by
  rw [(GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y (x ^ m) y y n).2.2.2.2, (GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c Y x y y m).2.2.2.1, smul_smul,
    mul_comm n m]

end GlobalTheory.AV.QuadSum

theorem GlobalTheory.AV.QuadSum.pull_sum_smul : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (n : ℕ) (f : Fin n → (B ⟶ A)) (m : Fin n → ℤ), 2 • CechPic.pull (Hom.hom (A := B) (B := A) (show B ⟶ A from ∑ i, m i • f i)).left c = ∑ i, ∑ j, (m i * m j) • AbVar.lam c (f i).hom (f j).hom := by
  intro K _ B A c hc n f m
  rw [← (GlobalTheory.T.mumfordClass_symmetric_pullback_quadratic K B A c hc (∑ i, m i • f i) 1).1, QuadSum.hom_finset_sum, QuadSum.lam_prod_left]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [QuadSum.lam_prod_right]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [zsmul_hom, zsmul_hom, QuadSum.lam_zpow_zpow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationMovesAlongDvrInjectionGivenFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_moves_along_dvr_injection_given_fibre : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'], IsAdicComplete (maximalIdeal V) V → IsAdicComplete (maximalIdeal V') V' → ∀ (φ : V →+* V') (φK : FractionRing V →+* FractionRing V'), φK.comp (algebraMap V _) = (algebraMap V' _).comp φ → (maximalIdeal V).map φ ≤ maximalIdeal V' → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (A' : PolAV (Sp (FractionRing V'))) (ψ : A'.A.left ⟶ A.A.left), IsGrpPullback A'.A A.A (spMap φK) ψ → LBIso A'.L (A.L.pull ψ) → A'.g = A.g → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra (FractionRing V') F], (algebraMap (FractionRing V') F).comp φK = algebraMap (FractionRing V) F → ∃ (D' : DegData V' (maximalIdeal V')) (hD : IsPullDeg φ D.toPre D'.toPre) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (U' : Unif (maximalIdeal V') D' A' G'), IsSemiAbelian G' ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (q : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), QkToAkU U.toUnifPre F k q x → ∃ (q' : QkPt D'.toPre F k) (x' : TFK (R := V') F ⟶ A'.A), hD.xe q'.y = q.y ∧ x'.left ≫ ψ = x.left ∧ QkToAkU U'.toUnifPre F k q' x' := by
  first | exact @GlobalTheory.UnifMoveGiven.move_given | exact GlobalTheory.UnifMoveGiven.move_given | (intros; apply GlobalTheory.UnifMoveGiven.move_given <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationProductOfUniformisedGroupsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_product_of_uniformisedGroups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), IsProdUnif U₁.toUnifPre U₂.toUnifPre U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ := by
  first | exact @GlobalTheory.ProdUnifExists.main | exact GlobalTheory.ProdUnifExists.main | (intros; apply GlobalTheory.ProdUnifExists.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupClosedFibreFinsetInAffineOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_closedFibre_finset_in_affineOpen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R) → ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  first | exact @GlobalTheory.Mum.finite_closedFibre_subset_isAffineOpen | exact GlobalTheory.Mum.finite_closedFibre_subset_isAffineOpen | (intros; apply GlobalTheory.Mum.finite_closedFibre_subset_isAffineOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitModulusRationalPhaseMemCoefficientFieldStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_modulus_rational_phase_mem_coefficient_field : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A)
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (t : D.ntw.Tw) (j : Fin D.R.m)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RatHyp T Rl F κ v₀ O t j hV →
  ∀ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
  ∀ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j (sg0 D A3.A) τ) →
  (∀ k, Rl.phs k = 1) → T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ →
  ∀ ph : ℂ, ‖ph‖ = 1 → IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph → ∃ c : D.what₂.LL, sg0 D A3.A c = ph := by
  first | exact @GlobalTheory.PhaseOneOnto.phase_mem_coefField | exact GlobalTheory.PhaseOneOnto.phase_mem_coefField | (intros; apply GlobalTheory.PhaseOneOnto.phase_mem_coefField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionNearClosedFibreDescendsToBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitSection_near_closedFibre_descends_to_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → Set.range (1 : Over.mk (𝟙 S) ⟶ G').left ⊆ Set.range N.u → ∃ e : Sp R ⟶ N.U.left, e ≫ N.U.hom = 𝟙 _ ∧ N.Pt (𝟙 S) (π ≫ e) (1 : Over.mk (𝟙 S) ⟶ G').left := by
  first | exact @GlobalTheory.UnitDescent.unit_descends | exact GlobalTheory.UnitDescent.unit_descends | (intros; apply GlobalTheory.UnitDescent.unit_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAutFormsWeightLevelFiniteSumFixedVectors
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.BCT.forms_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → FiniteDimensional ℂ (forms S lam K') ∧ ∃ (ι : Type) (_ : Fintype ι) (π : ι → Submodule ℂ (UA E n → ℂ)), (∀ i, IsAutRepU (π i) ∧ (∀ v, HasWeightAt (π i) v.embedding (lam v)) ∧ π i ⊓ fixed (RF E n) (globLev S K') ≠ ⊥) ∧ iSupIndep (fun i => π i ⊓ fixed (RF E n) (globLev S K')) ∧ (⨆ i, π i ⊓ fixed (RF E n) (globLev S K')) = forms S lam K' ∧ ∀ π₀, IsAutRepU π₀ → (∀ v, HasWeightAt π₀ v.embedding (lam v)) → π₀ ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ → ∃ i, ∀ w (σ : SmIrr (UL n w)), IsCompU π₀ w σ → IsCompU (π i) w σ := by
  intro E _ _ _ hU n _ S _ lam K' hK
  have hLo := GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK
  obtain ⟨C, hCf, hC⟩ := GlobalTheory.T.exists_finiteDimensional_archRestriction_space_of_weight E n lam
  have hcls : ∀ L : Subgroup (finU E n), IsOpen (L : Set (finU E n)) → ∃ S : Finset (UA E n), ∀ g : UA E n,
      ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ k ∈ L, ∃ y ∈ infU E n, g = γ * s * (k : UA E n) * y := by
    intro L hL
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n L hL
    refine ⟨S₀, fun g => ?_⟩
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS₀ g
    exact ⟨γ, hγ, s, hs, k, hk, x, hx, by rw [mul_assoc (γ * s) x, ← GlobalTheory.DefU.fin_mul_inf k.2 hx, ← mul_assoc]⟩
  have hfin := GlobalTheory.UnitaryBC.finiteDimensional_levelForms E n hcls _ hLo C hCf
  have hmemF : ∀ φ : UA E n → ℂ, φ ∈ fixed (RF E n) (globLev S K') ↔ ∀ k ∈ globLev S K', RU E n (k : UA E n) φ = φ := by
    intro φ
    change (∀ h : globLev S K', _) ↔ _
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k.1 k.2⟩
  have hle : forms S lam K' ≤ Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧
      (∀ k ∈ globLev S K', ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C} := by
    refine iSup₂_le fun π hπ φ hφ => Submodule.subset_span ⟨(hπ.1.aut φ hφ.1).left, fun k hk g => ?_, hC π hπ.1 hπ.2 φ hφ.1⟩
    exact congrFun ((hmemF φ).1 hφ.2 k hk) g
  haveI : FiniteDimensional ℂ (forms S lam K') := Submodule.finiteDimensional_of_le hle
  refine ⟨inferInstance, ?_⟩
  obtain ⟨ι, hι, π, h1, h2, h3, h4⟩ := GlobalTheory.T.fixed_vectors_irreducible_subrep_decomposition (RU E n) {x | ∃ k ∈ globLev S K', x = ((k : finU E n) : UA E n)}
    (fixed (RF E n) (globLev S K')) (fun φ => by
      rw [hmemF]
      exact ⟨fun h x ⟨k, hk, e⟩ => e ▸ h k hk, fun h k hk => h _ ⟨k, hk, rfl⟩⟩)
    {π | IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam v)}
    (fun P hP => ⟨hP.1.ne_bot, hP.1.stable, hP.1.irred⟩) (by assumption)
  refine ⟨ι, hι, π, fun i => ⟨(h1 i).1.1, (h1 i).1.2, (h1 i).2⟩, h2, h3, fun π₀ hπ₀ hw₀ hne => ?_⟩
  obtain ⟨i, T, hT1, hT2, hT3⟩ := h4 π₀ ⟨hπ₀, hw₀⟩ hne
  refine ⟨i, fun w σ ⟨p, hp, hirr, f, hf0, hfπ, hfe⟩ => ⟨p, hp, hirr, T ∘ₗ f, fun h => hf0 ?_, fun v => hT1 _ (hfπ v), fun x v => ?_⟩⟩
  · ext v : 1
    exact hT2 _ (hfπ v) (LinearMap.congr_fun h v)
  · rw [LinearMap.comp_apply, hfe x v]
    exact hT3 _ _ (hfπ v)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorFormTensorRangeLeUnitaryAutFormsWeightLeveStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectorFormTensor_range_le_unitaryAutFormsWeightLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → LinearMap.range (Phi S lam K') ≤ forms S lam K' := by
  first | exact @GlobalTheory.BCT.TrKer.range_Phi_le_forms | exact GlobalTheory.BCT.TrKer.range_Phi_le_forms | (intros; apply GlobalTheory.BCT.TrKer.range_Phi_le_forms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeLineLatticeTrivialMod
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.LKGeo.ModLim

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem isIntAf_one : IsIntAf (1 : AfP p) := fun v => by rw [map_one]; exact one_mem _

omit [Fact p.Prime] in
theorem isIntAf_mul {a c : AfP p} (ha : IsIntAf a) (hc : IsIntAf c) : IsIntAf (a * c) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hc v)

theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, isIntAf_one, rfl⟩

theorem smul_mem_laHat (D : Datum p) {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * c, x, isIntAf_mul ha hc, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

noncomputable def inAfHom (D : Datum p) : D.La →+ AfP p ⊗[ℚ] VQ D where
  toFun := inAf D
  map_zero' := by simp [inAf]
  map_add' x y := by simp [inAf, TensorProduct.tmul_add]

theorem exists_limit : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ → D.La →+ D.La), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → ∀ x, ∃ z, g (n * m) x = g n x + n • z) → ∃ h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D), (∀ v ∈ LaHat D, h₀ v ∈ LaHat D) ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, h₀ (inAf D x) = inAf D (g n x) + n • w := by
  first
  | exact @_root_.GlobalTheory.AdelicLimitCompactness.main
  | exact _root_.GlobalTheory.AdelicLimitCompactness.main
  | (apply _root_.GlobalTheory.AdelicLimitCompactness.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdelicLimitCompactness.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdelicLimitCompactness.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdelicLimitCompactness.main ..)

end GlobalTheory.LKGeo.ModLim
end

