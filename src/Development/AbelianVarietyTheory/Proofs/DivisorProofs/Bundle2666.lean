import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0298
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionPowScales
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.SelfInterPow

theorem isSelfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (a : ℝ), L.IsSelfInter a → ∀ e : ℕ,
      (L.pow e).IsSelfInter ((e : ℝ) ^ (D + 1) * a) := by
  intro hC k _ X _ p D hX L a ha e
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).1
  have h₁ := (((hC.arIso k X p D hX).2 Unit _ Φ hΦ).1 ()).unique hX ha
  obtain ⟨H, hH, he⟩ := hΦ.1 fun _ => (e : ℤ)
  refine ⟨H, (hC.arIso k X p D hX).1 _ _ H (GlobalTheory.ArInt.isometric_comb_unit_pow k X p L e) hH, he.trans ?_⟩
  rw [← h₁, ← smul_eq_mul, ← map_smul, ArInt.lin, Fintype.sum_unique, mul_pow, ← map_pow, MvPolynomial.smul_eq_C_mul]
  simp

end GlobalTheory.SelfInterPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianEndomorphismUniqueOverDegenerationDat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumUniq

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem isAbelianScheme_thick (D : DegPre R) (e : ℕ) : IsAbelianScheme (thickObj R I e D.P.A) := by
  have : IsProper D.P.A.hom := D.P.isAb.proper
  exact
    { comm := inferInstance
      smooth := by have := D.P.isAb.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := D.P.isAb.geomConnected
        show GeometricallyConnected (pullback.snd _ _)
        infer_instance }

theorem eq_of_q_of_i (g : GtCoord I D e G) (b₁ b₂ : thickObj R I e G ⟶ thickObj R I e G)
    [IsMonHom b₁] [IsMonHom b₂] (aB : thickObj R I e D.P.A ⟶ thickObj R I e D.P.A)
    (h₁ : b₁ ≫ g.q = g.q ≫ aB) (h₂ : b₂ ≫ g.q = g.q ≫ aB) (hi : g.i ≫ b₁ = g.i ≫ b₂) :
    b₁ = b₂ := by
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have hk := g.isKernel
  have : Mono g.i := by
    have : Mono (η[thickObj R I e D.P.A]) := ⟨fun _ _ _ => toUnit_unique _ _⟩
    exact (MorphismProperty.monomorphisms _).of_isPullback hk.flip (.infer_property _)
  have hc : IsMonHom (b₁ / b₂) := by
    rw [div_eq_mul_inv]; exact GlobalTheory.Serre.isMonHom_mul _ _
  have hcq : (b₁ / b₂) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [GrpObj.div_comp, h₁, h₂, div_self', Hom.one_def]
  let τ := hk.lift (b₁ / b₂) (toUnit _) hcq
  have hτ : τ ≫ g.i = b₁ / b₂ := hk.lift_fst _ _ _
  have : IsMonHom (τ ≫ g.i) := hτ ▸ hc
  have : IsMonHom τ := GlobalTheory.EndTorus.isMonHom_of_mono τ g.i
  have hiτ : g.i ≫ τ = toUnit _ ≫ η := by
    rw [← cancel_mono g.i, Category.assoc, hτ, GrpObj.comp_div, hi, div_self', Category.assoc,
      IsMonHom.one_hom, Hom.one_def]
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.eq_toUnit_comp_of_const_on_fibres _ _ _ (isAbelianScheme_thick D e) g.q
    g.q_flat g.q_surj inferInstance D.X τ
    (fun Z x y hxy => GlobalTheory.FlatQuotient.comp_eq_of_kills_kernel g.q g.i τ hk hiτ x y hxy)
  have hτ1 : τ = toUnit _ ≫ η := by
    have h := IsMonHom.one_hom τ
    rw [ha₀, ← Category.assoc, toUnit_unique (η ≫ toUnit _) (𝟙 _), Category.id_comp] at h
    rw [ha₀, h]
  have : b₁ / b₂ = 1 := by rw [← hτ, hτ1, Category.assoc, IsMonHom.one_hom, Hom.one_def]
  exact div_eq_one.1 this

end GlobalTheory.MumUniq

namespace GlobalTheory.MumUniq

theorem stalk_eq_of_thick : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Spec (CommRingCat.of R))), LocallyOfFiniteType G.hom → ∀ (b b' : G ⟶ G), (∀ e : ℕ, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → ∀ x : G.left, G.hom x = closedPoint R → G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left := GlobalTheory.T.fromSpecStalk_comp_eq_of_agree_on_closedThickenings

theorem irreducible_of_smooth : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))), Smooth G.hom → GeometricallyConnected G.hom → Nonempty G.left → IrreducibleSpace G.left := GlobalTheory.T.irreducibleSpace_of_smooth_geometricallyConnected_domain

theorem eq_of_stalk {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R)) [Smooth G.hom]
    [IsSeparated G.hom] [GeometricallyConnected G.hom] (b b' : G ⟶ G) (x : G.left)
    (h : G.left.fromSpecStalk x ≫ b.left = G.left.fromSpecStalk x ≫ b'.left) : b = b' := by
  have : IrreducibleSpace G.left := irreducible_of_smooth R G inferInstance inferInstance ⟨x⟩
  have : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  have : IsDominant (G.left.fromSpecStalk x) := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.range_fromSpecStalk, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    exact closure_mono (Set.singleton_subset_iff.2 (genericPoint_specializes x))
      ((genericPoint_spec G.left).def ▸ Set.mem_univ y)
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w b, Over.w b'])
    (G.left.fromSpecStalk x) h)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X), (∀ b b', FormalEnd U.toUnifPre a h' b → FormalEnd U.toUnifPre a h' b' → b = b') ∧ ∀ b b' : G ⟶ G, (∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → b = b' := by
  intro R _ _ _ hR D A G _ _ hG U a h'
  refine ⟨fun b b' hb hb' => funext fun e => ?_, fun b b' hbb => ?_⟩
  · obtain ⟨hm, -, hq, ht⟩ := hb
    obtain ⟨hm', -, hq', ht'⟩ := hb'
    have := hm e
    have := hm' e
    obtain ⟨t, htt, hti⟩ := ht e
    obtain ⟨t', htt', hti'⟩ := ht' e
    obtain rfl := GlobalTheory.LinearUnifCheck.torusEndOf_unique htt htt'
    exact eq_of_q_of_i (U.gt e) (b e) (b' e) _ (hq e) (hq' e) (hti.trans hti'.symm)
  · have := hG.smooth
    have := hG.separated
    have := hG.geomConnected
    have : IsNoetherianRing R := hR.1
    have hw : (η[G]).left ≫ G.hom = 𝟙 _ := Over.w (η[G])
    have hx : G.hom ((η[G]).left (closedPoint R : (𝟙_ (Over (Sp R))).left)) = closedPoint R := by
      show ((η[G]).left ≫ G.hom) (closedPoint R : (𝟙_ (Over (Sp R))).left) = _
      rw [hw]
      rfl
    exact eq_of_stalk G b b' _ (stalk_eq_of_thick R G inferInstance b b' hbb _ hx)

end GlobalTheory.MumUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianLocusNonemptyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianExtension_abelianLocus_nonempty : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (abLocus Zh.G).Nonempty := by
  first | exact @GlobalTheory.ZHAbLocusNonempty.abLocus_nonempty | exact GlobalTheory.ZHAbLocusNonempty.abLocus_nonempty | (intros; apply GlobalTheory.ZHAbLocusNonempty.abLocus_nonempty <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericEndomorphismExtends
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem genericEnd_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ f : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom f → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = f := by
  intro R _ _ _ hR G _ _ hG f hf
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hR
  haveI := hN
  haveI := hIC
  haveI := hf
  obtain ⟨g, ⟨hg, hg'⟩, -⟩ := GlobalTheory.Published.SemiAbelianHomExtension.fractionField GlobalTheory.semiAbelianHomExtension_holds R
    (FractionRing R) G G hG hG f
  exact ⟨g, hg, hg'⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsAtStalkAgreeingOnOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.StalkExt

theorem exists_agree_of_generic {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G]
    [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H)
    (hf : IsMonHom f) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (t : Sp R ⟶ S) [Mono t] (k : Sp (FractionRing R) ⟶ U) (hk : k ≫ j = Out.jK R ≫ t) :
    ∃ g : pullback G.hom t ⟶ H.left, g ≫ H.hom = pullback.fst G.hom t ≫ G.hom ∧
      GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom t) g := by
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing R (FractionRing R)

  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G (Out.jK R ≫ t))
    (((isGrpPullback_pullback ((Over.pullback j).obj G) k).comp (isGrpPullback_pullback G j)).congr hk rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (isGrpPullback_pullback H (Out.jK R ≫ t))
    (((isGrpPullback_pullback ((Over.pullback j).obj H) k).comp (isGrpPullback_pullback H j)).congr hk rfl)
  haveI := ha; haveI := hb; haveI := hf
  have hfK : IsMonHom (a.hom ≫ (Over.pullback k).map f ≫ b.inv) := inferInstance
  have hρ : (a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k) ≫ pullback.fst G.hom j =
      pullback.fst G.hom (Out.jK R ≫ t) := (Category.assoc _ _ _).trans ha'
  have hb2 : b.inv.left ≫ pullback.fst H.hom (Out.jK R ≫ t) =
      pullback.fst ((Over.pullback j).obj H).hom k ≫ pullback.fst H.hom j := by
    rw [← hb', ← Category.assoc, ← Over.comp_left, b.inv_hom_id, Over.id_left, Category.id_comp]
  have hK : (a.hom ≫ (Over.pullback k).map f ≫ b.inv).left ≫ pullback.fst H.hom (Out.jK R ≫ t) =
      (a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k) ≫ f.left ≫ pullback.fst H.hom j := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb2, ← Category.assoc (((Over.pullback k).map f).left),
      GlobalTheory.ExtUnique.pullback_map_left_fst, Category.assoc, Category.assoc]

  obtain ⟨g, hg, hA⟩ := GlobalTheory.DedekindExt.exists_agree_of_extend (k := Out.jK R) (t := t) rfl G H
    (a.hom ≫ (Over.pullback k).map f ≫ b.inv) fun f' hf' => by
      obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.T.semiAbelian_hom_extends_from_generic_fibre R ((Over.pullback t).obj G) ((Over.pullback t).obj H)
        (IsSemiAbelian.pullback t G hG) (IsSemiAbelian.pullback t H hH) f' hf'
      exact ⟨F, hF⟩

  have hw : f.left ≫ pullback.snd H.hom j = pullback.snd G.hom j := Over.w f
  have hf₀ : (f.left ≫ pullback.fst H.hom j) ≫ H.hom = pullback.fst G.hom j ≫ G.hom := by
    refine (Category.assoc _ _ _).trans ?_
    rw [pullback.condition, pullback.condition, ← hw]
    exact (Category.assoc _ _ _).symm
  let c : pullback G.hom (Out.jK R ≫ t) ⟶ pullback G.hom t :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Out.jK R) (by rw [pullback.condition, Category.assoc])
  have hc₁ : c ≫ pullback.fst G.hom t = pullback.fst G.hom (Out.jK R ≫ t) := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd G.hom t = pullback.snd G.hom (Out.jK R ≫ t) ≫ Out.jK R := pullback.lift_snd _ _ _
  have sq : IsPullback c (pullback.snd G.hom (Out.jK R ≫ t)) (pullback.snd G.hom t) (Out.jK R) := by
    refine IsPullback.of_right ?_ hc₂ (IsPullback.of_hasPullback G.hom t)
    rw [hc₁]
    exact IsPullback.of_hasPullback G.hom (Out.jK R ≫ t)
  have : QuasiCompact c := MorphismProperty.of_isPullback sq.flip ‹_›
  have : IsSchemeTheoreticallyDominant c := .of_isPullback sq.flip
  refine ⟨g, hg, GlobalTheory.DedekindExt.Agree.of_dominant G.hom H.hom hf₀ hg c fun T u u' e => ?_⟩
  have h₁ := hA T (u ≫ c) u (by rw [Category.assoc, hc₁])
  have hu : u' = u ≫ a.hom.left ≫ pullback.fst ((Over.pullback j).obj G).hom k := by
    rw [← cancel_mono (pullback.fst G.hom j), ← e, Category.assoc, Category.assoc, hc₁, ← hρ, Category.assoc]
  rw [hu, ← Category.assoc, h₁, hK, Category.assoc, Category.assoc, Category.assoc]

theorem exists_agree_at_stalk : ∀ {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f → ∀ (s : S) [IsDomain (S.presheaf.stalk s)] [IsNoetherianRing (S.presheaf.stalk s)] [IsIntegrallyClosed (S.presheaf.stalk s)] (k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U), k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s → ∃ g : pullback G.hom (S.fromSpecStalk s) ⟶ H.left, g ≫ H.hom = pullback.fst G.hom (S.fromSpecStalk s) ≫ G.hom ∧ GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom (S.fromSpecStalk s)) g := by
  intro U S j _ G H _ _ hG hH f hf s i₁ i₂ i₃ k hk
  haveI := i₁; haveI := i₂; haveI := i₃
  exact @exists_agree_of_generic U S j _ G H _ _ hG hH f hf (S.presheaf.stalk s) _ i₁ i₂ i₃ (S.fromSpecStalk s) _ k hk

end GlobalTheory.StalkExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermInjectiveClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LocalInj

theorem base_to_stalk_injective : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, Function.Injective ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) := by
  intro R' _ _ _ _ G₁ _ _ hG x
  haveI : Smooth G₁.hom := hG.smooth
  haveI : Flat G₁.hom := inferInstance

  have hst : Function.Injective (G₁.hom.stalkMap x).hom := by
    have h := Flat.stalkMap G₁.hom x
    letI := (G₁.hom.stalkMap x).hom.toAlgebra
    haveI : Module.Flat ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x) := h
    have : IsLocalHom (algebraMap ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (G₁.hom.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp R').presheaf.stalk (G₁.hom x))
      (B := G₁.left.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective ((Sp R').presheaf.stalk (G₁.hom x)) (G₁.left.presheaf.stalk x)

  have hgerm : Function.Injective ((Sp R').presheaf.germ ⊤ (G₁.hom x) trivial).hom := by
    have hU := isAffineOpen_top (Sp R')
    let _ := (Sp R').presheaf.algebra_section_stalk (U := ⊤) ⟨G₁.hom x, trivial⟩
    have := hU.isLocalization_stalk ⟨G₁.hom x, trivial⟩
    haveI : IsDomain Γ(Sp R', ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv.toMulEquiv.isDomain_iff.mpr inferInstance
    exact IsLocalization.injective (M := (hU.primeIdealOf ⟨G₁.hom x, trivial⟩).asIdeal.primeCompl)
      (S := (Sp R').presheaf.stalk ((⟨G₁.hom x, trivial⟩ : (⊤ : (Sp R').Opens)) : Sp R'))
      (Ideal.primeCompl_le_nonZeroDivisors _)
  have hiso : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).1
  have e : ⇑((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) =
      ⇑(G₁.hom.stalkMap x).hom ∘ ⇑((Sp R').presheaf.germ ⊤ (G₁.hom x) trivial).hom ∘
        ⇑(Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom := by
    funext a
    exact (Scheme.Hom.germ_stalkMap_apply G₁.hom ⊤ x trivial _).symm
  rw [e]
  exact hst.comp (hgerm.comp hiso)

end GlobalTheory.Mum.LocalInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermPrimeIdealMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem ideal_map_stalk_isPrime_of_closedPoint : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, G₁.hom x = closedPoint R' → ∀ q : Ideal R', q.IsPrime → (Ideal.map ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) q).IsPrime := by
  intro R' _ _ _ _ G₁ _ _ hG x hx q hq
  have := hG.smooth
  have := hG.geomConnected
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp G₁.left.isBasis_affineOpens
    (show x ∈ (⊤ : G₁.left.Opens) from trivial)
  replace hU : IsAffineOpen U := hU
  let A := Γ(G₁.left, U)
  let ψ : R' →+* A := (G₁.left.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp
    ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)
  have hφ : (G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom) = (G₁.left.presheaf.germ U x hxU).hom.comp ψ := by
    ext r
    rw [← TopCat.Presheaf.germ_res G₁.left.presheaf (homOfLE le_top : U ⟶ ⊤) x hxU]
    rfl
  rw [hφ, ← Ideal.map_map]
  letI : Algebra R' A := ψ.toAlgebra

  have hnu : ∀ r ∈ q, ¬ IsUnit ((G₁.left.presheaf.germ U x hxU).hom (ψ r)) := by
    intro r hr hu
    have key := DFunLike.congr_fun hφ r
    simp only [RingHom.comp_apply] at key
    rw [← key] at hu
    have hu := (Scheme.mem_basicOpen G₁.left _ x (show x ∈ (⊤ : G₁.left.Opens) from trivial)).mpr hu
    rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at hu
    change G₁.hom x ∈ PrimeSpectrum.basicOpen r at hu
    rw [hx] at hu
    exact hu (IsLocalRing.le_maximalIdeal hq.ne_top hr)
  set P := hU.primeIdealOf ⟨x, hxU⟩
  letI : Algebra A (G₁.left.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk G₁.left.presheaf ⟨x, hxU⟩
  haveI := hU.isLocalization_stalk ⟨x, hxU⟩
  have hle : Ideal.map ψ q ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (G₁.left.presheaf.stalk x) P.asIdeal]
    exact hnu r hr
  have hI : (Ideal.map ψ q).IsPrime := by
    haveI := hq
    have hne : Ideal.map ψ q ≠ ⊤ := fun h => P.isPrime.ne_top (top_le_iff.mp (h ▸ hle))
    let e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := R') A q
    haveI : Nontrivial (A ⧸ Ideal.map (algebraMap R' A) q) := Ideal.Quotient.nontrivial_iff.mpr hne
    haveI : Nontrivial (TensorProduct R' A (R' ⧸ q)) := e.symm.toEquiv.nontrivial
    have eSp : Spec.map (CommRingCat.ofHom (algebraMap R' A)) = hU.fromSpec ≫ G₁.hom := by
      apply ext_of_isAffine
      have h1 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R' A))
      rw [← Iso.eq_comp_inv] at h1
      rw [h1, Scheme.Hom.comp_appTop]
      change _ = _ ≫ hU.fromSpec.app ⊤
      rw [IsAffineOpen.fromSpec_app_of_le hU ⊤ le_top]
      rw [show (homOfLE le_top : hU.fromSpec ⁻¹ᵁ ⊤ ⟶ ⊤) = 𝟙 _ from rfl]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
      ext r
      simp [ψ, RingHom.algebraMap_toAlgebra]
    haveI : IsIntegral (Spec (CommRingCat.of (R' ⧸ q))) :=
      (affine_isIntegral_iff _).mpr (inferInstanceAs (IsDomain (R' ⧸ q)))
    haveI : IsIntegral (pullback G₁.hom (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⧸ q))))) :=
      GlobalTheory.isIntegral_pullback_of_smooth _ _
    let j := (pullbackSpecIso R' A (R' ⧸ q)).inv ≫ (pullback.congrHom eSp rfl).hom ≫
      (pullbackRightPullbackFstIso G₁.hom _ hU.fromSpec).inv ≫ pullback.snd _ _
    haveI : Nonempty (Spec (CommRingCat.of (TensorProduct R' A (R' ⧸ q)))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum _))
    haveI := isIntegral_of_isOpenImmersion j
    haveI hdom := (affine_isIntegral_iff _).mp this
    haveI : IsDomain (A ⧸ Ideal.map (algebraMap R' A) q) := MulEquiv.isDomain _ e.toRingEquiv.toMulEquiv
    exact (Ideal.Quotient.isDomain_iff_prime _).mp this
  exact IsLocalization.isPrime_of_isPrime_disjoint P.asIdeal.primeCompl _ _ hI
    (Set.disjoint_left.mpr fun a ha h => ha (hle h))

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearDualBasisBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory

theorem dualBasis_baseChange : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') (hf : Function.Bijective (liftSemi f)) {n : ℕ}
    (b : Module.Dual R M ≃ₗ[R] (Fin n → R)) (x : Fin n → Module.Dual R' M')
    (hx : ∀ k c, x k (f c) = algebraMap R R' (b.symm (Pi.single k 1) c)),
   LinearIndependent R' x ∧ Submodule.span R' (Set.range x) = ⊤ := by
  intro R R' _ _ _ M _ _ _ _ M' _ _ f hf n b x hx
  classical
  let B : Module.Basis (Fin n) R (Module.Dual R M) := Module.Basis.ofEquivFun b
  have hB : ∀ k, B k = b.symm (Pi.single k 1) := fun k => by simp [B]
  let C : Module.Basis (Fin n) R M := B.dualBasis.map (Module.evalEquiv R M).symm
  have hC : ∀ k l, B k (C l) = if k = l then 1 else 0 := fun k l => by
    have e : B k (C l) = Module.evalEquiv R M (C l) (B k) := rfl
    rw [e]
    simp only [C, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Module.Basis.dualBasis_apply_self]
  let D : Module.Basis (Fin n) R' M' :=
    (Algebra.TensorProduct.basis R' C).map (LinearEquiv.ofBijective (liftSemi f) hf)
  have hD : ∀ k, D k = f (C k) := fun k => by
    simp [D, Algebra.TensorProduct.basis_apply]
  have hxD : ∀ k, x k = D.dualBasis k := fun k => by
    refine D.ext fun l => ?_
    rw [hD, hx, ← hB, hC, ← hD, D.dualBasis_apply_self]
    by_cases h : k = l
    · subst h; simp
    · simp [h, Ne.symm h]
  have : x = ⇑D.dualBasis := funext hxD
  rw [this]
  exact ⟨D.dualBasis.linearIndependent, D.dualBasis.span_eq⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpEighthPowerRelativeDimensionEqEightMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharpRef_relDim : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → D.P.g = 8 * Q.g := by
  intro W V V₁ _ _ _ _ Q ρ D e h
  obtain ⟨pr, w, hmon, huniv, -⟩ := h
  have lim : IsLimit (Fan.mk D.P.A pr) :=
    mkFanLimit _ (fun s => (huniv s.pt s.proj).choose)
      (fun s i => (huniv s.pt s.proj).choose_spec.1 i)
      (fun s m hm => (huniv s.pt s.proj).unique hm (huniv s.pt s.proj).choose_spec.1)
  let eI : D.P.A ≅ powObj ((Over.pullback (spMap ρ)).obj Q.B) 8 :=
    lim.conePointUniqueUpToIso (powIsLimit _ 8)
  have hB : SmoothOfRelativeDimension Q.g ((Over.pullback (spMap ρ)).obj Q.B).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback Q.B.hom (spMap ρ)) Q.smoothDim
  have h8 := GlobalTheory.smoothOfRelativeDimension_powObj _ Q.g hB 8
  have hne : Nonempty (Sp V₁) := inferInstance
  exact GlobalTheory.relDim_unique_of_iso_grp (Sp V₁) hne D.P.A _ eI.hom inferInstance _ _ D.P.smoothDim h8

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionDualNumberFibreProductAffineMilnorStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallExtension_dualNumber_fibreProduct_affineMilnorSquare : ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∃ (P : Type) (_ : CommRing P) (i : C →+* P) (p σ : P →+* C) (q : P →+* DualNumber (IsLocalRing.ResidueField C)), p.comp i = RingHom.id C ∧ σ.comp i = RingHom.id C ∧ q.comp i = (dnInl _).comp (IsLocalRing.residue C) ∧ IsClosedImmersion (spMap σ) ∧ Surjective (spMap σ) ∧ Milnor (spMap p) (spMap σ) (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e}))) ∧ Milnor (spMap p) (spMap q) (spMap (IsLocalRing.residue C)) (spMap (dnFst _)) := by
  first | exact @GlobalTheory.DualOpen.smallExt_fibre_ring | exact GlobalTheory.DualOpen.smallExt_fibre_ring | (intros; apply GlobalTheory.DualOpen.smallExt_fibre_ring <;> assumption)
end

