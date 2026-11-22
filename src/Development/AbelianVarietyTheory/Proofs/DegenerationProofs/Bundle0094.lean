import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsAdicCompleteOfNe
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThickIsoOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IntegralSectionsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0087
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralPointOfTorusPointValuationZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.GtDescent

variable {p : ℕ} [Fact p.Prime]

theorem existsUnique_ext {X S : Scheme.{0}} (q : X ⟶ S) [hp : IsProper q] (c : Sp (OO p) ⟶ S)
    (x : Sp (PadicAlgCl p) ⟶ X) (hx : x ≫ q = gPt p ≫ c) : ∃! y : Sp (OO p) ⟶ X, y ≫ q = c ∧ gPt p ≫ y = x := by
  have hv : ValuativeCriterion q := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let Q : ValuativeCommSq q := { R := OO p, K := PadicAlgCl p, i₁ := x, i₂ := c, commSq := ⟨hx⟩ }
  obtain ⟨U⟩ := hv Q
  refine ⟨U.default.l, ⟨U.default.fac_right, U.default.fac_left⟩, fun ψ hψ => ?_⟩
  exact congrArg CommSq.LiftStruct.l (U.uniq ⟨ψ, hψ.2, hψ.1⟩)

theorem exists_ring {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (j : V →+* OO p) [IsLocalHom j]
    (hj : Function.Injective j) (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (hK : ∀ x, (j x : PadicAlgCl p) ∈ K) (s : Finset (OO p)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (f : V →+* W) (κ : W →+* OO p), Function.Injective κ ∧
      IsLocalHom κ ∧ κ.comp f = j ∧ (∀ x ∈ s, x ∈ κ.range) ∧
      IsAdicComplete ((IsLocalRing.maximalIdeal V).map f) W := by
  let K₁ := IntermediateField.adjoin ℚ_[p] ((s.image (OO p).subtype : Finset _) : Set (PadicAlgCl p))
  have : FiniteDimensional ℚ_[p] K₁ :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E : IntermediateField ℚ_[p] (PadicAlgCl p) := K ⊔ K₁
  have : FiniteDimensional ℚ_[p] E := IntermediateField.finiteDimensional_sup K K₁
  have hd : IsDiscreteValuationRing (integralClosure ℤ_[p] E) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr ℤ_[p] ℚ_[p] E
  have hf : Module.Finite ℤ_[p] (integralClosure ℤ_[p] E) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] E _
  have := CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[p] (integralClosure ℤ_[p] E)
  let κ := integralClosureToPadicAlgClIntegers E
  have hl : IsLocalHom κ := isLocalHom_integralClosureToPadicAlgClIntegers E
  have hκ : Function.Injective κ := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : OO p => (z : PadicAlgCl p)) h))
  let f₁ : V →+* E := ((OO p).subtype.comp j).codRestrict E fun x => (le_sup_left : K ≤ E) (hK x)
  let f : V →+* integralClosure ℤ_[p] E := f₁.codRestrict (integralClosure ℤ_[p] E) fun x =>
    (mem_integralClosure_padicInt_iff E _).2 ((mem_OO_iff _).1 (j x).2)
  have hc : κ.comp f = j := RingHom.ext fun x => rfl
  refine ⟨integralClosure ℤ_[p] E, inferInstance, inferInstance, f, κ, hκ, hl, hc, fun x hx => ?_,
    isAdicComplete_of_ne (fun h => ?_) (fun h => ?_)⟩
  · exact ⟨⟨⟨x, (le_sup_right : K₁ ≤ E) (IntermediateField.subset_adjoin _ _ (by simpa using hx))⟩,
      (mem_integralClosure_padicInt_iff E _).2 ((mem_OO_iff _).1 x.2)⟩, rfl⟩
  · have hi : Function.Injective f := fun a b h => hj (by rw [← hc]; exact congrArg κ h)
    exact IsDiscreteValuationRing.not_a_field V ((Ideal.map_eq_bot_iff_of_injective hi).1 h)
  · have : (IsLocalRing.maximalIdeal V).map f ≤ IsLocalRing.maximalIdeal _ :=
      Ideal.map_le_iff_le_comap.2 fun x hx hu => hx (IsLocalHom.map_nonunit (f := j) x (hu.map κ))
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h ▸ this))

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem gPt_j : gPt p ≫ spMap u.j = (TF (R := u.V) (PadicAlgCl p)).hom := by
  change _ = jFK (R := u.V) (PadicAlgCl p) ≫ jK u.V
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem exists_intGood : ∃ J, u.IntGood J := by
  have : IsProper u.D.toPre.P.A.hom := u.D.toPre.P.isAb.proper
  have hL := u.D.toPre.P.isLB
  have H : ∀ x : Sp (PadicAlgCl p) ⟶ u.D.toPre.P.A.left, ∃ i, ∀ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left,
      ψ ≫ u.D.toPre.P.A.hom = spMap u.j → gPt p ≫ ψ = x → ⊤ ≤ ψ ⁻¹ᵁ u.D.toPre.P.L.U i := fun x => by
    by_cases h : ∃ ψ : Sp (OO p) ⟶ u.D.toPre.P.A.left, ψ ≫ u.D.toPre.P.A.hom = spMap u.j ∧ gPt p ≫ ψ = x
    · obtain ⟨ψ, h₁, h₂⟩ := h
      obtain ⟨i, hi⟩ := exists_chart hL (ψ (cpt (OO p)))
      refine ⟨i, fun ψ' h₁' h₂' => ?_⟩
      obtain rfl : ψ' = ψ := (existsUnique_ext u.D.toPre.P.A.hom (spMap u.j) x
        (by rw [← h₂, Category.assoc, h₁])).unique ⟨h₁', h₂'⟩ ⟨h₁, h₂⟩
      exact (top_le_iff_cpt _ _).2 hi
    · obtain ⟨i, -⟩ := exists_chart hL (x (cpt (PadicAlgCl p)))
      exact ⟨i, fun ψ h₁ h₂ => (h ⟨ψ, h₁, h₂⟩).elim⟩
  choose J hJ using H
  exact ⟨J, fun ψ h => hJ _ ψ h rfl⟩

theorem spMap_cpt {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B) [IsLocalHom f] :
    spMap f (cpt B) = cpt A := IsLocalRing.comap_closedPoint f

theorem gtφT_over {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    (b : T ⟶ D.P.A) (χ : D.X) (k : Fin 4) : DegPre.gtφT D T b χ k ≫ D.P.A.hom = T.hom := by
  fin_cases k <;> exact Over.w _

theorem exists_model (hl : IsLocalHom u.j) (hj : Function.Injective u.j) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] (hK : ∀ x, (u.j x : PadicAlgCl p) ∈ K) (g : GtPtF u.D.toPre (PadicAlgCl p))
    (hg : u.GtN g 0) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsLocalRing W) (f : u.V →+* W) (κ : W →+* OO p),
      IsLocalHom κ ∧ κ.comp f = u.j ∧ IsAdicComplete ((IsLocalRing.maximalIdeal u.V).map f) W ∧
      ∃ ξ : GtPt u.D.toPre (Over.mk (spMap f)), spMap ((OO p).subtype.comp κ) ≫ ξ.b.left = g.b.left ∧
        ∀ χ z J, Good u.D.toPre.P.L z J →
          val (ξ.s χ) (spMap ((OO p).subtype.comp κ)) z J = val (g.s χ) (𝟙 _) z J := by
  have : IsProper u.D.toPre.P.A.hom := u.D.toPre.P.isAb.proper
  have hL := u.D.toPre.P.isLB
  obtain ⟨J, hJ⟩ := exists_intGood u
  obtain ⟨b₀, ⟨hb₁, hb₂⟩, -⟩ := existsUnique_ext u.D.toPre.P.A.hom (spMap u.j) g.b.left
    ((Over.w g.b).trans (gPt_j u).symm)
  obtain ⟨s₀, hs₀⟩ := exists_factor u.D.toPre.P.A.hom u.j b₀ hb₁
  have : AddGroup.FG u.D.toPre.X := Module.Finite.iff_addGroup_fg.1 inferInstance
  obtain ⟨X₀, hX₀⟩ := (AddGroup.fg_iff_addMonoid_fg.1 this).fg_top
  have hv : ∀ χ, ‖valF (𝟙 (Sp (PadicAlgCl p))) _
      ((g.s χ).s (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))).val‖ = 1 := fun χ => by
    rw [hg J hJ χ]; simp
  let v : u.D.toPre.X → OO p := fun χ => ⟨_, (mem_OO_iff _).2 (hv χ).le⟩
  have hu : ∀ χ, IsUnit (v χ) := fun χ => by
    by_contra h
    exact ((not_isUnit_OO_iff _).1 h).ne (hv χ)
  obtain ⟨W, _, _, f, κ, hκ, hκl, hc, hs, hW⟩ := exists_ring u.j hj K hK (s₀ ∪ X₀.image v)
  obtain ⟨b', hb₃, hb₄⟩ := hs₀ W f κ hκ hc fun x hx => hs x (Finset.mem_union_left _ hx)
  have eκ : spMap ((OO p).subtype.comp κ) = gPt p ≫ spMap κ := by
    rw [← Spec.map_comp]; rfl
  have ef : spMap κ ≫ spMap f = spMap u.j := by
    rw [← Spec.map_comp, ← hc]; rfl
  let π : TF (R := u.V) (PadicAlgCl p) ⟶ Over.mk (spMap f) := Over.homMk (spMap ((OO p).subtype.comp κ)) (by
    rw [← gPt_j, ← ef, eκ]; exact Category.assoc _ _ _)
  let b : Over.mk (spMap f) ⟶ u.D.toPre.P.A := Over.homMk b' hb₃
  have hb : spMap ((OO p).subtype.comp κ) ≫ b' = g.b.left := by rw [eκ, Category.assoc, hb₄, hb₂]
  let ξ' : GtPt u.D.toPre (TF (R := u.V) (PadicAlgCl p)) := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩
  obtain ⟨ξ, h₁, h₂⟩ := exists_descend π (appTop_injective _ (Subtype.val_injective.comp hκ)) ξ' b
    (Over.OverMorphism.ext hb) X₀ hX₀ fun χ hχ => by
      obtain ⟨a, ha⟩ := hs (v χ) (Finset.mem_union_right _ (Finset.mem_image_of_mem v hχ))
      have hau : IsUnit a := IsLocalHom.map_nonunit (f := κ) a (ha ▸ hu χ)
      have hφ : ∀ k, spMap ((OO p).subtype.comp κ) ≫ DegPre.gtφT u.D.toPre _ b χ k =
          DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k := fun k => by
        have := (TorusCoord.comp_eq_of_left b g.b (spMap ((OO p).subtype.comp κ)) (𝟙 _)
          (hb.trans (Category.id_comp _).symm)).1 χ k
        rw [Category.id_comp, ← TorusCoord.gtφT_eq] at this
        exact this
      refine exists_gen_extend hL ((OO p).subtype.comp κ) hφ (g.s χ) (g.isGen χ)
        (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k)) ?_ hau.unit (congrArg Subtype.val ha)
      refine (top_le_iff_cpt (𝟙 (Sp W)) (LB.wchart u.D.toPre.P.L (DegPre.gtφT u.D.toPre _ b χ)
        (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k)))).2 ?_
      refine Set.mem_iInter.2 fun k => ?_
      have h3 := (top_le_iff_cpt _ _).1 (hJ (spMap κ ≫ DegPre.gtφT u.D.toPre _ b χ k)
        ((Category.assoc _ _ _).trans ((congrArg _ (gtφT_over b χ k)).trans ef)))
      rw [← Category.assoc, ← eκ, hφ k, Scheme.Hom.comp_apply, spMap_cpt] at h3
      exact h3
  exact ⟨W, inferInstance, inferInstance, f, κ, hκl, hc, hW, ξ, by rw [h₁]; exact hb, h₂⟩

theorem exists_integral_point : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (g : GtPtF u.D.toPre (PadicAlgCl p)), u.GtN g 0 → ∃ c : Sp (OO p) ⟶ u.G.left, c ≫ u.G.hom = spMap u.j ∧ u.Lev c g := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u g hg
  obtain ⟨-, hl, hj, K, hK, hK'⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  obtain ⟨W, _, _, f, κ, hκ, hc, hW, ξ, h₁, h₂⟩ := exists_model u hl hj K (fun x => by
    rw [← SetLike.mem_coe, hK']; exact ⟨_, rfl⟩) g hg
  have hL := u.D.toPre.P.isLB
  obtain ⟨x, hx, -⟩ := FormalPoint.existsUnique_isPointOf u.U.toUnifPre ξ
  have eκ : spMap ((OO p).subtype.comp κ) = gPt p ≫ spMap κ := by
    rw [← Spec.map_comp]; rfl
  have ef : spMap κ ≫ spMap f = spMap u.j := by
    rw [← Spec.map_comp, ← hc]; rfl
  refine ⟨spMap κ ≫ x.left, (Category.assoc _ _ _).trans ((congrArg _ (Over.w x)).trans ef),
    spMap κ ≫ ξ.b.left, by rw [← Category.assoc, ← eκ, h₁], fun e ce hce => ?_⟩
  obtain ⟨a₁, a₂⟩ := (FormalPoint.hasCoords_iff _ _ _ _ _).1
    (hx e _ (spMap (Ideal.Quotient.mk (u.lev e)) ≫ spMap κ) ce (hce.trans (Category.assoc _ _ _).symm))
  refine ⟨a₁.trans (Category.assoc _ _ _), fun χ jj hjj => ?_⟩
  have hne : u.lev e ≠ ⊤ := fun h => by
    have : u.lev e ≤ IsLocalRing.maximalIdeal _ := Ideal.map_le_iff_le_comap.2 fun x hx hu =>
      Ideal.pow_le_self e.succ_ne_zero hx (IsLocalHom.map_nonunit (f := u.j) x hu)
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 (h ▸ this))
  have : Nontrivial (OO p ⧸ u.lev e) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (OO p ⧸ u.lev e) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk (u.lev e)) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hφ := (TorusCoord.comp_eq_of_left ξ.b (u.U.gt e).pG _ ce a₁.symm).1 χ
  have hφ' : ∀ k, spMap ((OO p).subtype.comp κ) ≫ DegPre.gtφT u.D.toPre _ ξ.b χ k =
      𝟙 _ ≫ DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k := fun k => by
    have := (TorusCoord.comp_eq_of_left ξ.b g.b (spMap ((OO p).subtype.comp κ)) (𝟙 _)
      (h₁.trans (Category.id_comp _).symm)).1 χ k
    rw [← TorusCoord.gtφT_eq] at this
    exact this
  have hm := mem_wchart_of_eq _ _ (fun k => (hφ k).symm) _ ((top_le_iff_cpt _ _).1 hjj)
  rw [Scheme.Hom.comp_apply, spMap_cpt] at hm
  have ht := (top_le_iff_cpt (spMap κ) _).2 hm
  obtain ⟨t₁, v₁⟩ := CrdCalc.valR_spMap (OO p).subtype (spMap κ) _ ht
  obtain ⟨t₂, v₂⟩ := CrdCalc.valR_spMap (Ideal.Quotient.mk (u.lev e)) (spMap κ) _ ht
  refine ⟨valR (spMap κ) _ ((ξ.s χ).s jj).val, (v₁ _).symm.trans ?_, (v₂ _).symm.trans ?_⟩
  · rw [← eκ] at t₁ ⊢
    exact valR_transfer hL (ξ.isGen χ) (g.isGen χ) _ (𝟙 _) hφ' (h₂ χ) t₁
  · exact valR_transfer hL (ξ.isGen χ) ((u.U.gt e).t_gen χ) _ ce hφ (fun z J hJ => (a₂ χ z J hJ).symm) t₂

end GlobalTheory.GtDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoSpecialise
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.IsoFinite

open GlobalTheory.Spread GlobalTheory.HomDescent

variable {k : Type} [CommRing k] {C : Type} [CommRing C] [Algebra k C] {A A' : Over (Sp k)}

theorem comm_bcMap (R : Subalgebra k C)
    (f : (Over.pullback (spMap (algebraMap k C))).obj A ⟶ (Over.pullback (spMap (algebraMap k C))).obj A')
    (g : (Over.pullback (spMap (algebraMap k R))).obj A ⟶ (Over.pullback (spMap (algebraMap k R))).obj A')
    (h : bcMap A.hom R.val ≫ g.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _) :
    f.left ≫ bcMap A'.hom R.val = bcMap A.hom R.val ≫ g.left := by
  have hf : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  have hg : g.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w g
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (f.left ≫ ·) (bcMap_fst A'.hom R.val)).trans
      (h.symm.trans (Category.assoc _ _ _).symm))
  · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    have a₁ := congrArg (f.left ≫ ·) (bcMap_snd A'.hom R.val)
    have a₂ := congrArg (bcMap A.hom R.val ≫ ·) hg
    have a₃ := congrArg (· ≫ spMap R.val.toRingHom) hf
    exact a₁.trans ((Category.assoc _ _ _).symm.trans
      (a₃.trans ((bcMap_snd A.hom R.val).symm.trans a₂.symm)))

variable [GrpObj A] [GrpObj A']

theorem exists_fg_iso [QuasiCompact A.hom] [IsSeparated A.hom] [Flat A.hom] [LocallyOfFinitePresentation A.hom]
    [QuasiCompact A'.hom] [IsSeparated A'.hom] [Flat A'.hom] [LocallyOfFinitePresentation A'.hom]
    (e : (Over.pullback (spMap (algebraMap k C))).obj A ≅ (Over.pullback (spMap (algebraMap k C))).obj A')
    [IsMonHom e.hom] :
    ∃ (R : Subalgebra k C)
      (g : (Over.pullback (spMap (algebraMap k R))).obj A ≅ (Over.pullback (spMap (algebraMap k R))).obj A'),
      R.FG ∧ IsMonHom g.hom := by
  obtain ⟨R₁, f₁, hR₁, _, h₁⟩ := exists_fg_isMonHom e.hom
  obtain ⟨R₂, f₂, hR₂, _, h₂⟩ := exists_fg_isMonHom e.inv
  let R : Subalgebra k C := R₁ ⊔ R₂
  obtain ⟨g₁, m₁, k₁⟩ := exists_specialise f₁ (Subalgebra.inclusion (le_sup_left : R₁ ≤ R))
  obtain ⟨g₂, m₂, k₂⟩ := exists_specialise f₂ (Subalgebra.inclusion (le_sup_right : R₂ ≤ R))
  have c₁ := comm_bcMap R e.hom g₁ ((congrArg (_ ≫ ·) k₁).trans
    ((bcMap_comp_of_eq_assoc A.hom _ _ R₁.val (fun _ => rfl) _).trans h₁))
  have c₂ := comm_bcMap R e.inv g₂ ((congrArg (_ ≫ ·) k₂).trans
    ((bcMap_comp_of_eq_assoc A'.hom _ _ R₂.val (fun _ => rfl) _).trans h₂))
  have := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom R.val.toRingHom)
    Subtype.val_injective
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
    inferInstanceAs (Flat (pullback.snd _ _))
  have : Flat ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
    inferInstanceAs (Flat (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A).hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsSeparated ((Over.pullback (spMap (algebraMap k R))).obj A').hom :=
    inferInstanceAs (IsSeparated (pullback.snd _ _))
  have : IsIso g₁ := ExtUnique.isIso_of_isPullback (isGrpPullback_bcMap A R.val).1
    (isGrpPullback_bcMap A' R.val).1 e g₁ g₂ c₁ c₂
  exact ⟨R, asIso g₁, hR₁.sup hR₂, m₁⟩

theorem exists_iso_specialise {R S : Type} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (g : (Over.pullback (spMap (algebraMap k R))).obj A ≅ (Over.pullback (spMap (algebraMap k R))).obj A')
    [IsMonHom g.hom] (ρ : R →ₐ[k] S) :
    ∃ e : (Over.pullback (spMap (algebraMap k S))).obj A ≅ (Over.pullback (spMap (algebraMap k S))).obj A',
      IsMonHom e.hom := by
  obtain ⟨a, ha, -⟩ := grpPullback_iso (isGrpPullback_bcMap A ρ) (isGrpPullback_pullback _ _)
  obtain ⟨b, hb, -⟩ := grpPullback_iso (isGrpPullback_pullback _ _) (isGrpPullback_bcMap A' ρ)
  exact ⟨a ≪≫ (Over.pullback (spMap ρ.toRingHom)).mapIso g ≪≫ b,
    inferInstanceAs (IsMonHom (a.hom ≫ (Over.pullback (spMap ρ.toRingHom)).map g.hom ≫ b.hom))⟩

theorem exists_finite_iso : ∀ (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] (T T' : Over (Spec (CommRingCat.of k))) [GrpObj T] [GrpObj T'], IsAffineHom T.hom → IsAffineHom T'.hom → LocallyOfFiniteType T.hom → LocallyOfFiniteType T'.hom → (∃ e : fieldBaseChange k Ω T ≅ fieldBaseChange k Ω T', IsMonHom e.hom) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k') (_ : FiniteDimensional k k') (e : fieldBaseChange k k' T ≅ fieldBaseChange k k' T'), IsMonHom e.hom := by
  intro k Ω _ _ _ T T' _ _ _ _ _ _ ⟨e, he⟩
  have : LocallyOfFinitePresentation T.hom := inferInstance
  have : LocallyOfFinitePresentation T'.hom := inferInstance
  obtain ⟨R, g, hR, hg⟩ := exists_fg_iso (k := k) (C := Ω) (A := T) (A' := T') e
  have : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (R ⧸ m) := .of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  have : Module.Finite k (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  obtain ⟨e', he'⟩ := exists_iso_specialise g (Ideal.Quotient.mkₐ k m)
  exact ⟨R ⧸ m, inferInstance, inferInstance, this, e', he'⟩

end GlobalTheory.IsoFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.RigidSections GlobalTheory.FamFieldPull

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I D' A' G')
  (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G)

def LevelIso : Prop :=
  ∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧
    (U'.gt e).pG.left ≫ prA hD = (j e).hom.left ≫ (U.gt e).pG.left ∧
    ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ prA hD =
        (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧
      PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x)
        ((U.gt e).t (hD.xe x)) (j e).hom.left

def AgreeAll (k : ℕ) (σ : H0 U.LG.L k) (σ' : H0 U'.LG.L k) : Prop :=
  ∀ e : ℕ, Agree U U' hD e k (j e).hom.left σ σ'

def Enough : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∀ σ₀ : H0 U.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧
      (∀ i, σ.f i = resTop _ (scal G.hom c) * σ₀.f i) ∧ AgreeAll U U' hD j k σ σ') ∧
    ∀ σ₀ : H0 U'.LG.L k, ∃ (c : R) (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), c ≠ 0 ∧
      (∀ i, σ'.f i = resTop _ (scal G'.hom c) * σ₀.f i) ∧ AgreeAll U U' hD j k σ σ'

def GenericRel (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G)
    (w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R)))
      (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))) : Prop :=
  w.IsGen ∧ ∀ k : ℕ, 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), AgreeAll U U' hD j k σ σ' →
    ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL →
      (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' →
      gs (r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL))
          (σ.f (fun _ => jL)) =
        (Geo.Tor.gw w r z jL (fun _ => jL') ^ k).val *
          gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL'))
            (σ'.f (fun _ => jL'))

open ThickIso TorusCoordPull in
theorem exists_levelIso (hG : GlobalFnsSt) : ∃ j, LevelIso U U' hD j := by
  choose j hm hj using fun e : ℕ => exists_iso hD (U.gt e) (U'.gt e) hG
  refine ⟨j, fun e => ?_⟩
  have h₀ := hj e _ (𝟙 _)
  have hp : (U'.gt e).pG.left ≫ abMap hD = (j e).hom.left ≫ (U.gt e).pG.left := by
    simpa only [Category.id_comp] using h₀.1
  have hO := Oφ_pull hD (U.gt e).pG (U'.gt e).pG (j e).hom.left hp
  refine ⟨hm e, (hj (e + 1) _ (thickMap R I e G')).unique_right ?_, hp, fun x => ⟨hO x,
    pmaps_of_good ((isGen_iff hD.w).1 hD.w_gen) D.toPre.P.isLB D'.toPre.P.isLB (hO x) ((U'.gt e).t_gen x)
      ((U.gt e).t_gen _) fun y J J' hJ hJ' => h₀.2 x y J J' hJ hJ'⟩⟩
  simpa only [Category.id_comp] using h₀.succ (U.gt_q e) (U.gt_t e) (U'.gt_q e) (U'.gt_t e)

variable {U U' hD j}

theorem LevelIso.agreeAll (hj : LevelIso U U' hD j) {k : ℕ} {σ : H0 U.LG.L k} {σ' : H0 U'.LG.L k}
    {f : ∀ α, D.toPre.SecB k α} {f' : ∀ α, D'.toPre.SecB k α} (hE : ∀ e, U.ExpandsAt e k σ f)
    (hE' : ∀ e, U'.ExpandsAt e k σ' f')
    (hf : ∀ x, IsSecPull hD.w (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (f' x)
      (f (hD.xe x))) : AgreeAll U U' hD j k σ σ' := fun e =>
  agree_of_expandsAt _ _ hD e k _ (hj e).2.2.1 (fun x => ((hj e).2.2.2 x).1) (fun x => ((hj e).2.2.2 x).2)
    (hE e) (hE' e) hf

theorem LevelIso.enough (hj : LevelIso U U' hD j) (hG : GlobalFnsSt) (hU : ∀ k, 1 ≤ k → U.ExpBij k)
    (hU' : ∀ k, 1 ≤ k → U'.ExpBij k) : Enough U U' hD j := by
  intro k hk
  constructor
  · intro σ₀
    obtain ⟨s, hs⟩ := exists_restrict U k σ₀
    obtain ⟨F, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (hU k hk).1 s
    obtain ⟨F', hF⟩ := exists_pull hD _ hG k F
    obtain ⟨s', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (hU' k hk).2 F'
    exact ⟨r' * r, _, _, mul_ne_zero hr' hr, scale_of_restrict _ hs h₁ r', hj.agreeAll
      (fun e => expandsAt_scale _ (h₃ e) _) (fun e => expandsAt_scale _ (h₃' e) _) (integral_rel hD _ hF h₂ h₂')⟩
  · intro σ₀
    obtain ⟨s', hs⟩ := exists_restrict U' k σ₀
    obtain ⟨F', ⟨r', hr', σ', f', h₁', h₂', h₃'⟩, -⟩ := (hU' k hk).1 s'
    obtain ⟨F, hF⟩ := exists_push hD _ hG k F'
    obtain ⟨s, ⟨r, hr, σ, f, h₁, h₂, h₃⟩, -⟩ := (hU k hk).2 F
    exact ⟨r * r', _, _, mul_ne_zero hr hr', scale_of_restrict _ hs h₁' r, hj.agreeAll
      (fun e => expandsAt_scale _ (h₃ e) _) (fun e => expandsAt_scale _ (h₃' e) _) (integral_rel hD _ hF h₂ h₂')⟩

open LinearUnifIso in

theorem LevelIso.act_comm (hj : LevelIso U U' hD j) (hG : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O]
    [Module O D.toPre.X] [Module O D'.toPre.X] {o : D.OAct O} {o' : D'.OAct O} {oA : A.OAct O} {oA' : A'.OAct O}
    {oG : RingAct G O} {oG' : RingAct G' O} (lin : U.OLinear O o oA oG) (lin' : U'.OLinear O o' oA' oG')
    (hx : ∀ (x : O) y, hD.xe (x • y) = x • hD.xe y)
    (hB : ∀ x, o'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (o.onB.act x))
    (a : O) (e : ℕ) : (Over.pullback (thick R I e)).map (oG'.act a) ≫ (j e).hom =
      (j e).hom ≫ (Over.pullback (thick R I e)).map (oG.act a) := by
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  have P : ∀ {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of R)) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback t).map c).left ≫ pullback.fst Y.hom t =
        pullback.fst X.hom t ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : o'.onB.act a ≫ ψ = ψ ≫ o.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ, Category.assoc, ← P, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, hB])
  obtain ⟨hm, -, hp, ht⟩ := hj e
  have hq : (j e).hom ≫ (U.gt e).q = (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
    refine Over.OverMorphism.ext ?_
    rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
      Category.assoc, Category.assoc, P, eψ]
    exact hp.symm.trans (Category.assoc _ _ _)
  obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
    (fun x => (ht x).2)
  obtain ⟨t, tc, ti⟩ := lin.i_lin e a
  obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
  have := oG.hom a
  have := oG'.hom a
  have hts : t' ≫ s = s ≫ t := by
    refine PowTorus.torus_ext _ _ fun χ z => ?_
    obtain ⟨x, rfl⟩ := hD.xe.surjective χ
    rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
      ← gm_torusEnd tc', Category.id_comp]
  refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
      ← Functor.map_comp, ← Functor.map_comp, hψa]
  · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]

end GlobalTheory.GenericIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalThetaSectionFibreNonzeroStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localThetaSection_fibreNonzero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), Q.LocTheta → ∀ z : M.Z, ∃ (N : M.Z.Opens) (σ : Q.SecFam N), z ∈ N ∧ σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) ∧ Q.FibNe N σ := by
  first | exact @GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe | exact GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe | (intros; apply GlobalTheory.ZH.LocThetaConv.exists_secFam_fibNe <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMemNonzeroLocusFibreOfSecBasisStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_nonzeroLocus_fibre_of_secBasis : SecBaseChangeAnySt → ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsSecBasis _ (fun _ : Fin 1 => th) → ∀ s : Sp R, ∃ y ∈ nonzeroLocus th, P.A.hom ((snd (baseOver (Sp R)) P.A).left y) = s := by
  first | exact @GlobalTheory.ThetaFibre.exists_mem_nonzeroLocus_fibre | exact GlobalTheory.ThetaFibre.exists_mem_nonzeroLocus_fibre | (intros; apply GlobalTheory.ThetaFibre.exists_mem_nonzeroLocus_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPadicLiftTorsionPointInvertibleOrderStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicLift_torsionPoint_invertibleOrder : ∀ (p : ℕ) [Fact p.Prime] (B : Scheme.{0}) (G : Over B) [GrpObj G], IsSemiAbelian G → ∀ (y : Sp (OO p) ⟶ B) (n : ℕ), IsUnit (n : Γ(B, ⊤)) → ∀ t : Over.mk (spMap (IsLocalRing.residue (OO p)) ≫ y) ⟶ G, t ^ n = 1 → ∃ b : Over.mk y ⟶ G, b ^ n = 1 ∧ spMap (IsLocalRing.residue (OO p)) ≫ b.left = t.left := by
  first | exact @GlobalTheory.ZJ.exists_torsion_lift_of_residue | exact GlobalTheory.ZJ.exists_torsion_lift_of_residue | (intros; apply GlobalTheory.ZJ.exists_torsion_lift_of_residue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionReductionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pureWeight_section_reduction : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ α : Φ.E.X, UFib.GenWt Φ.D.i t α → ∀ φ : (Φ.H 1).Sec, Φ.Pure α φ → ∃ b : LB.Sec (LB.LinComb L ψ ε), UFib.Red Φ c t b φ := by
  first | exact @GlobalTheory.ZH.UFib.exists_red_of_pure | exact GlobalTheory.ZH.UFib.exists_red_of_pure | (intros; apply GlobalTheory.ZH.UFib.exists_red_of_pure <;> assumption)
end

