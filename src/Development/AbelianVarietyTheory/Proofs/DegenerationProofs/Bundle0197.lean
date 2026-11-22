import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0195
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelMapKernelEqIntegralTorsion

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AdaptedBasisRowsHaveClassWeightStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedBasis_rows_have_class_weight : GlobalTheory.UT.LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (f : S.J → ∀ α, u.D.toPre.SecB S.N α), u.Basis l S.N σ cls f → ∀ b : Matrix S.J S.J (FractionRing u.V), u.Link σ b → ∀ i, ((S.proj _ (l.wt (cls i))).map fun a => y₀ (algebraMap o S.R a)).mulVec (b.map (algebraMap _ (PadicAlgCl p)) i) = b.map (algebraMap _ (PadicAlgCl p)) i := by
  first | exact @GlobalTheory.ZH.ClassWeight.row_weight | exact GlobalTheory.ZH.ClassWeight.row_weight | (intros; apply GlobalTheory.ZH.ClassWeight.row_weight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CompatibleLineBundlesFormalThickeningStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_line_bundles_formal_thickening : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Smooth (Y e).hom) → (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left), GlobalTheory.AbLaw.IsProjBy B.hom ∧ Smooth B.hom ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  first | exact @GlobalTheory.FormalAlgebraise.algebraisation | exact GlobalTheory.FormalAlgebraise.algebraisation | (intros; apply GlobalTheory.FormalAlgebraise.algebraisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenyOfNcard
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.PrincIsog

theorem pow_eq_one_of_etale {k : Type} [Field k] [IsAlgClosed k] {A B : Over (Sp k)} [GrpObj A] [GrpObj B]
    [IsSeparated A.hom] [LocallyOfFiniteType A.hom] (ψ : A ⟶ B) [Etale ψ.left] (n : ℕ)
    (h : ∀ y : Over.mk (𝟙 (Sp k)) ⟶ A, y ≫ ψ = 1 → y ^ n = 1) (T : Over (Sp k)) (x : T ⟶ A)
    (hx : x ≫ ψ = 1) : x ^ n = 1 := by
  let K := pullback ψ η[B]
  let inc : K ⟶ A := pullback.fst ψ η[B]
  have hinc : inc ≫ ψ = 1 := by
    rw [pullback.condition, toUnit_unique (pullback.snd ψ η[B]) (toUnit K)]; rfl
  have hp := (IsPullback.of_hasPullback ψ η[B]).map (Over.forget (Sp k))
  have he : Etale (pullback.snd ψ η[B]).left := MorphismProperty.of_isPullback (P := @Etale) hp ‹_›
  have hw : (pullback.snd ψ η[B]).left = K.hom := by
    simpa using Over.w (pullback.snd ψ η[B])
  rw [hw] at he
  have : IsReduced K.left := GlobalTheory.isReduced_of_smooth_of_isReduced K.hom
  have key : inc ^ n = 1 := by
    refine Over.OverMorphism.ext ?_
    have : LocallyOfFiniteType ((inc ^ n).left ≫ A.hom) := by rw [Over.w]; infer_instance
    refine ext_of_apply_eq A.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
      ((Over.w _).trans (Over.w _).symm)
    let p : Over.mk (𝟙 (Sp k)) ⟶ K := Over.homMk (pointOfClosedPoint K.hom z hz) (pointOfClosedPoint_comp _ _ _)
    have e : p ≫ inc ^ n = p ≫ 1 := by
      rw [MonObj.comp_pow, MonObj.comp_one]
      exact h _ (by rw [Category.assoc, hinc, MonObj.comp_one])
    have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint k)) e
    have hz' : p.left (IsLocalRing.closedPoint k) = z := pointOfClosedPoint_apply K.hom z hz _
    simp only [Over.comp_left] at e'
    rw [← hz']
    exact e'
  have hx' : x ≫ ψ = toUnit T ≫ η[B] := hx
  rw [← pullback.lift_fst x (toUnit T) hx', ← MonObj.comp_pow]
  change _ ≫ inc ^ n = 1
  rw [key, MonObj.comp_one]

theorem exists_lift_point {F : Type} [Field F] [IsAlgClosed F] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f]
    [Surjective f] (x : Sp F ⟶ Y) : ∃ b : Sp F ⟶ X, b ≫ f = x := by
  have : CompactSpace ↥(pullback f x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  obtain ⟨p, -⟩ := (pullback.snd f x).surjective (default : PrimeSpectrum F)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem exists_isogeny_of_ncard (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (g N : ℕ) :
    ∀ (A : Over (Sp k)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      L.IsLB → Out.RelAmple A L → {x : 𝟙_ (Over (Sp k)) ⟶ A | GlobalTheory.MemKL A L x}.ncard = N →
      ∃ (B : Over (Sp k)) (_ : GrpObj B) (M : LB B.left) (i : A ⟶ B) (r : B ⟶ A) (m : ℕ),
        IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ M.IsLB ∧ Out.RelAmple B M ∧ Out.KTriv B M ∧
          IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A _ L hA hg hL hamp hN
  obtain ⟨hfin, hmul, htriv⟩ := GlobalTheory.KTrivPoints.finite_mul_kTriv k A hA L hL hamp
  by_cases h1 : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, GlobalTheory.MemKL A L x → x = 1
  · exact ⟨A, inferInstance, L, 𝟙 A, 𝟙 A, 1, hA, hg, hL, hamp, htriv h1, inferInstance, inferInstance, le_rfl,
      by simp⟩
  push Not at h1
  obtain ⟨x, hxK, hx1⟩ := h1
  have hfin' : {x : 𝟙_ (Over (Sp k)) ⟶ A | GlobalTheory.MemKL A L x}.Finite := hfin
  have hord : IsOfFinOrder x := by
    refine finite_powers.1 (hfin'.subset ?_)
    rintro _ ⟨j, rfl⟩
    induction j with
    | zero => simpa using GlobalTheory.memKL_one hL _
    | succ j hj => simpa [pow_succ] using hmul _ _ hj hxK
  have hn : 1 ≤ orderOf x := hord.orderOf_pos
  obtain ⟨A', _, ψ, hA', hψ, hψf, hψe, hψs, hker⟩ :=
    GlobalTheory.exists_quotient_abelian_by_finite_points k A hA (Subgroup.zpowers x) (finite_zpowers.2 hord)
  obtain ⟨M, hM, hLM⟩ := GlobalTheory.CyclicDescent.exists_descent k A A' hA L hL x _ hn rfl hxK ψ hψ hψf hψe hψs hker
  have hamp' := GlobalTheory.SS.relAmple_of_finite_etale_isogeny k A A' hA hA' ψ hψ hψf hψe hψs L M hL hM hLM hamp
  have := hA.proper
  have := hA'.proper
  have := hA.comm
  have := hA'.comm
  have hg' : SmoothOfRelativeDimension g A'.hom :=
    GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover k _ _ ψ.left A'.hom g hψe hψs inferInstance
      (by rw [Over.w]; exact hg)
  have hxψ : x ≫ ψ = 1 := (hker k (𝟙 _) x).2 ⟨x, Subgroup.mem_zpowers x, by
    rw [show toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 (𝟙_ (Over (Sp k))) from toUnit_unique _ _]
    exact (Category.id_comp x).symm⟩
  have hlt : {y : 𝟙_ (Over (Sp k)) ⟶ A' | GlobalTheory.MemKL A' M y}.ncard < N := by
    rw [← hN]
    refine lt_of_le_of_lt ?_ (Set.ncard_sdiff_singleton_lt_of_mem (a := x) hxK hfin')
    refine (Set.ncard_le_ncard ?_ ((hfin'.sdiff).image (· ≫ ψ))).trans (Set.ncard_image_le hfin'.sdiff)
    intro y hy
    obtain ⟨b, hb⟩ := exists_lift_point (F := k) ψ.left y.left
    let b' : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk b (by
      rw [← Over.w ψ, ← Category.assoc, hb]; exact Over.w _)
    have hb' : b' ≫ ψ = y := Over.OverMorphism.ext hb
    by_cases hbx : b' = x
    · exact ⟨1, ⟨GlobalTheory.memKL_one hL _, fun h => hx1 (Eq.symm h)⟩, by
        rw [← hb', hbx, hxψ]; exact MonObj.one_comp ψ⟩
    · exact ⟨b', ⟨GlobalTheory.memKL_of_hom _ A A' ψ hψ L M hL hM hLM _ b' (hb' ▸ hy), hbx⟩, hb'⟩
  obtain ⟨B, _, M', i, r, m, hB, hgB, hM', hampB, hK, hi, hr, hm, hri⟩ := ih _ hlt A' M hA' hg' hM hamp' rfl
  have hmon : IsMonHom (𝟙 A ^ orderOf x) := GlobalTheory.GrpTangent.mulN_eq_pow A _ ▸ GlobalTheory.GrpTangent.isMonHom_mulN A _
  obtain ⟨⟨ψ', hψ', hc⟩, hepi⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A A' A ψ (𝟙 A ^ orderOf x) hψ hmon
    inferInstance hψs inferInstance fun T z hz => by
      rw [MonObj.comp_pow, Category.comp_id]
      refine pow_eq_one_of_etale ψ _ (fun y hy => ?_) T z hz
      obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := (hker k (𝟙 _) y).1 hy
      rw [← MonObj.comp_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow, MonObj.comp_one]
  have hc' : ψ' ≫ ψ = 𝟙 A' ^ orderOf x := by
    rw [← cancel_epi ψ, ← Category.assoc, hc, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp,
      Category.comp_id]
  refine ⟨B, inferInstance, M', ψ ≫ i, r ≫ ψ', m * orderOf x, hB, hgB, hM', hampB, hK, inferInstance,
    inferInstance, Nat.mul_pos hm hn, ?_⟩
  rw [Category.assoc, ← Category.assoc ψ', hc', MonObj.pow_comp, Category.id_comp, MonObj.comp_pow, hri, pow_mul]

theorem exists_isogeny_kTriv : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (B : Over (Sp k)) (_ : GrpObj B) (M : LB B.left) (i : A ⟶ B) (r : B ⟶ A) (m : ℕ), IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ M.IsLB ∧ Out.RelAmple B M ∧ Out.KTriv B M ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m := by
  intro k _ _ _ A _ g hA hg
  obtain ⟨L, m, s, hL, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple k A hA
  have := hA.proper
  exact exists_isogeny_of_ncard k g _ A L hA hg hL
    ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hL).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)) rfl

end GlobalTheory.SS.PrincIsog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPrimitiveBundleTranslateLocalRingStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_primitiveBundle_translate_localRing : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (P : PolAV (Spec (CommRingCat.of A))) (O : LB P.A.left), O.IsLB → (∃ u : LB.Gen (abelian₂ P.A O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ P.A, LBIso O (LB.LinComb P.L (K := Fin 2) ![((toUnit P.A ≫ x) * 𝟙 P.A).left, 𝟙 P.A.left] ![1, -1]) := by
  first | exact @GlobalTheory.PrimitiveOverLocalRing.exists_section_translate | exact GlobalTheory.PrimitiveOverLocalRing.exists_section_translate | (intros; apply GlobalTheory.PrimitiveOverLocalRing.exists_section_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemTestSectionsOnGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

open GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

theorem exists_secsOver : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∃ rig e th s, SecsOver u x rig e th s := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u x hx
  obtain ⟨w, hw⟩ := u.lb
  have hp := u.cart
  have hL₀ := ρ.P.isLB
  have hL₁ := u.A.isLB
  have := u.A.isAb.comm
  have := ρ.P.isAb.comm
  let τ : (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have hτ : τ ≫ (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun q => spMap q) u.fac.symm
  have hx' : ∀ a, (x a).left ≫ u.φ = τ ≫ (ρ.pt a).left := hx
  obtain ⟨rig, hrig, Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec u.A.A) (φ := fun _ => eSec ρ.P.A)
    (ε := fun _ => 1) (h := spMap u.yK) hw hL₀ hL₁ (fun _ => PolBaseChange.eSec_comm hp) ρ.rig ρ.rig_gen
  choose e he He using fun a => exists_gen_through (φ' := fun _ : Fin 1 => (x a).left) (h := τ) hw hL₀ hL₁
    (fun _ => hx' a) (ρ.fr a) (ρ.fr_tors a).2.1
  have hfr : ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) := fun a =>
    FrameMove.isTorsFrame_move hp hw
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx' a) (ρ.fr_tors a) (he a) (fun z J J' hJ hJ' => by
        have := He a _ (𝟙 _) z J J' hJ hJ'
        rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this)
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ ρ.th₁
  choose s hs using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (ρ.s i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  have hpow : ∀ (n : ℕ) a, ρ.pt (n • a) = ρ.pt a ^ n := fun n a => by
    induction n with
    | zero =>
      have h := ρ.pt_add 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 h
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hN : ∀ a, x (S.r • a) ^ S.N = 1 := fun a => FrameMove.pow_eq_one_of hp (hx' _) (by
    rw [hpow, ← pow_mul]
    exact (ρ.fr_tors a).1)
  refine ⟨rig, e, th, s, hrig, hfr, fun a z J hJ => ?_, fun i a z J hJ => ?_,
    ⟨α, hα, ThetaGeom.norm_move hp τ hτ hL₀ hL₁ Hr vα ρ.α_norm,
      isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) hα vα hth (hs ρ.i₀) ρ.s_zero⟩, fun a => ?_⟩
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx' a).symm (He a) hth (ρ.th_val a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    rw [ThetaGeom.val_powFrame, Nat.cast_one, zpow_one]
    exact q
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx' a).symm (ThetaGeom.genThrough_pow τ (He a) S.N) (hs i)
      (ρ.ev_val i a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    exact q
  · obtain ⟨θ, hθ, H⟩ := ClassWeight.symLift_act_move hp τ hτ hw hL₀ hL₁ (hx' _).symm (hN a) (ρ.U_sym a)
      (fun l i => fn (algebraMap o S.R (S.ρ a l i))) (fun l i => cF u.V (y₀ (algebraMap o S.R (S.ρ a l i))))
      (fun l i => spMap_appTop_fn y₀ _) hs (ρ.U_act a)
    exact ⟨θ, hθ, fun i σ h => (ThetaGeom.comb_iff _ _ _).2 (H i σ h)⟩

end GlobalTheory.TestFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValLeOfValuedSumAgainstCharactersStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_val_le_of_valuedSum_against_characters : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X T : Type) [Fintype T] (χ : T → X → F) (cf : X → F) (ζ w : T → F) (α : X) (q : ℚ), (∀ t, SumV v (fun β => χ t β * cf β) (ζ t * w t)) → (∀ t, v (ζ t) = 0) → (∀ t β, v (χ t β) = 0) → v ((Fintype.card T : ℕ) : F) = 0 → v (cf α) = (q : WithTop ℚ) → (∀ β, β ≠ α → ∑ t, (χ t α)⁻¹ * χ t β = 0 ∨ (q : WithTop ℚ) < v (cf β)) → ∃ t, v (w t) ≤ (q : WithTop ℚ) := by
  first | exact @GlobalTheory.TestFibre.exists_val_le_of_sumV_characters | exact GlobalTheory.TestFibre.exists_val_le_of_sumV_characters | (intros; apply GlobalTheory.TestFibre.exists_val_le_of_sumV_characters <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreSectionLinearCombExistsUniqueThetaAction
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.SecComb

theorem equiv_sum {K M J : Type} [CommRing K] [AddCommGroup M] [Module K M] [Fintype J] (ρ : M ≃ₗ[K] M)
    (c : J → K) (v w : J → M) (h : ∀ i, ρ (v i) = w i) : ρ (∑ i, c i • v i) = ∑ i, c i • w i := by
  simp only [map_sum, map_smul, h]

variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

omit [IsDomain R] in
theorem ofSec_inj {t t' : SecA A F k}
    (h : (SecM.ofSec A.A t : SecM A.A A.L (k : ℤ) (TFK (R := R) F)) = SecM.ofSec A.A t') : t = t' := by
  have h' : t.f = t'.f := congrArg Subtype.val h
  cases t; cases t'; cases h'; rfl

theorem isComb_iff {J : Type} [Fintype J] (s : J → SecA A F k) (b : J → F) (t : SecA A F k) :
    IsComb A s b t ↔ (SecM.ofSec A.A t : SecM A.A A.L (k : ℤ) (TFK (R := R) F)) =
      ∑ l, cF R (b l) • SecM.ofSec A.A (s l) := by
  have e : ∀ j, ((∑ l, cF R (b l) • SecM.ofSec A.A (s l) : SecM A.A A.L (k : ℤ) (TFK (R := R) F)).1 j) =
      ∑ l, liftFun A.A _ (cF R (b l)) * (s l).f j := fun j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  exact ⟨fun H => Subtype.ext (funext fun j => (H j).trans (e j).symm),
    fun H j => (congrFun (congrArg Subtype.val H) j).trans (e j)⟩

omit [IsDomain R] in
theorem exists_rho (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) :
    ∃ ρ : SecM A.A A.L (k : ℤ) (TFK (R := R) F) ≃ₗ[Γ((TFK (R := R) F).left, ⊤)]
      SecM A.A A.L (k : ℤ) (TFK (R := R) F), ∀ s s' : SecA A F k,
      IsActOf A.A A.L k θ s s' ↔ ρ (SecM.ofSec A.A s) = SecM.ofSec A.A s' := by
  have hL := A.isLB
  obtain ⟨ρ, hρ⟩ := ThetaAct.exists_equiv hL θ
  refine ⟨ρ, fun s s' => ?_⟩
  rw [ThetaAct.isActOf_iff hL]
  exact ⟨fun H => ThetaAct.sv_ext hL fun y J hJ => (hρ _ _ _ _ _ hJ).trans (H y J hJ).symm,
      fun H y J hJ => H ▸ hρ _ _ _ _ _ hJ⟩

end GlobalTheory.SecComb

namespace GlobalTheory

open SecComb in

theorem secComb_thetaAct : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (J : Type) [Fintype J] (s : J → SecA A F k) (b : J → F), (∃ t, IsComb A s b t) ∧ (∀ t t', IsComb A s b t → IsComb A s b t' → t = t') ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (s' : J → SecA A F k) t t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb A s b t → (IsActOf A.A A.L k θ t t' ↔ IsComb A s' b t')) ∧ (∀ (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) (t : SecA A F k), ∃! t', IsActOf A.A A.L k θ t t') ∧ ∀ (I : Type) [Fintype I] (M : I → J → F) (r : I → SecA A F k) (a : I → F) (t : SecA A F k), (∀ i, IsComb A s (M i) (r i)) → IsComb A r a t → IsComb A s (fun j => ∑ i, M i j * a i) t := by
  intro R _ _ A F _ _ k J _ s b
  refine ⟨⟨SecM.toSec A.A (∑ l, cF R (b l) • SecM.ofSec A.A (s l) : SecM A.A A.L (k : ℤ) (TFK (R := R) F)),
    (isComb_iff A _ _ _).2 rfl⟩, fun t t' h h' => ?_, fun θ s' t t' hs h => ?_, fun θ t => ?_,
    fun I _ M r a t hr h => ?_⟩
  · exact ofSec_inj A (((isComb_iff A _ _ _).1 h).trans ((isComb_iff A _ _ _).1 h').symm)
  · obtain ⟨ρ, hρ⟩ := exists_rho A θ
    have e := (congrArg ρ ((isComb_iff A _ _ _).1 h)).trans
      (equiv_sum ρ (fun l => cF R (b l)) _ _ fun i => (hρ _ _).1 (hs i))
    exact ⟨fun H => (isComb_iff A _ _ _).2 (((hρ _ _).1 H).symm.trans e),
      fun H => (hρ _ _).2 (e.trans ((isComb_iff A _ _ _).1 H).symm)⟩
  · obtain ⟨ρ, hρ⟩ := exists_rho A θ
    refine ⟨SecM.toSec A.A (ρ (SecM.ofSec A.A t)), (hρ _ _).2 rfl, fun t' h => ofSec_inj A ?_⟩
    exact ((hρ _ _).1 h).symm
  · rw [isComb_iff] at h ⊢
    rw [h]
    simp only [fun i => (isComb_iff A _ _ _).1 (hr i), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    have e : cF R (∑ i, M i j * a i) = ∑ i, cF R (M i j * a i) := map_sum _ _ _
    rw [e]
    exact Finset.sum_congr rfl fun i _ => (_root_.mul_comm _ _).trans (map_mul _ _ _).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HvHolds
section
namespace GlobalTheory.Ex

theorem hv_holds : GlobalTheory.Ex.HV :=
  GlobalTheory.TestFibre.laws_all GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1

end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFibreSectionLinearCombIffExpansionSum
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem isComb_iff_expandsF_sum : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (J : Type) [Fintype J] (s : J → SecA A F k) (Φ : J → Fam D.toPre F k) (b : J → F) (t : SecA A F k), (∀ i, U.ExpandsF F k w₀ (s i) (Φ i)) → (IsComb A s b t ↔ U.ExpandsF F k w₀ t (∑ i, b i • Φ i)) := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ k hk w₀ hw J _ s Φ b t hs
  obtain ⟨hb, hl⟩ := GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hI D A G hG U
  obtain ⟨h₁, h₂⟩ := hb F k hk w₀ hw
  have h0 : U.ExpandsF F k w₀ (SecOps.secZero : SecA A F k) (0 : Fam D.toPre F k) := by
    obtain ⟨σ, hσ⟩ := (h₁ (SecOps.secZero : SecA A F k)).exists
    have h := hl F k w₀ SecOps.secZero SecOps.secZero SecOps.secZero σ σ (-1) hσ hσ (fun j => ((add_zero _).trans (mul_zero _)).symm)
    rwa [neg_one_smul, neg_add_cancel] at h
  have key : ∀ S : Finset J, ∃ u : SecA A F k,
      (∀ j, u.f j = ∑ l ∈ S, liftFun A.A _ (cF R (b l)) * (s l).f j) ∧
        U.ExpandsF F k w₀ u (∑ i ∈ S, b i • Φ i) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨SecOps.secZero, fun j => by rw [Finset.sum_empty]; rfl, by rw [Finset.sum_empty]; exact h0⟩
    | insert a S ha ih =>
      obtain ⟨u, hu, eu⟩ := ih
      refine ⟨SecOps.secAdd (SecOps.secScale ((fst (TFK (R := R) F) A.A).left.appTop.hom (cF R (b a))) (s a)) u,
        fun j => ?_, ?_⟩
      · rw [Finset.sum_insert ha, ← hu j]; rfl
      · rw [Finset.sum_insert ha]
        exact hl F k w₀ (s a) u _ (Φ a) _ (b a) (hs a) eu (fun j => rfl)
  obtain ⟨u, hu, eu⟩ := key Finset.univ
  constructor
  · intro h
    obtain rfl : t = u := SecOps.sec_ext fun j => (h j).trans (hu j).symm
    exact eu
  · intro h
    obtain rfl : t = u := (h₂ _).unique h eu
    exact hu

end GlobalTheory.TestFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelMapKernelEqIntegralTorsionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_map_kernel_eq_integral_torsion : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range), Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ a, a ∈ yy.ker ↔ u.Integral a := by
  first | exact @GlobalTheory.ZH.LabelKernel.main | exact GlobalTheory.ZH.LabelKernel.main | (intros; apply GlobalTheory.ZH.LabelKernel.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyGeometricSpecialFibreUniformisedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_geometric_special_fibre_uniformised : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (N : ℕ), 1 ≤ N → Nonempty (u.FibOf N) := by
  first | exact @GlobalTheory.ZH.UFib.nonempty_fibOf | exact GlobalTheory.ZH.UFib.nonempty_fibOf | (intros; apply GlobalTheory.ZH.UFib.nonempty_fibOf <;> assumption)
end

