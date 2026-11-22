import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3349
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3350
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3275
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2297
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3250
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientFiniteCommGroupSchemeClosedSubgrou
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamRelationsTotalDetectZero
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDForm

universe u

section Gen

variable {C : Type u} [Category.{0} C]

theorem cx_H1_mk_eq_zero_iff (K : Cx C) (x : K.Z1) :
    (QuotientAddGroup.mk x : K.H1) = 0 ↔ ∃ g, K.D0 g = x.1 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

theorem cx_H2_mk_eq_zero_iff (K : Cx C) (x : K.Z2) :
    (QuotientAddGroup.mk x : K.H2) = 0 ↔ ∃ g, K.D1 g = x.1 := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]

variable {R : Type} [CommRing R] (F : C ⥤ CommAlgCat.{0} R)

theorem single1_mem (f : GlobalTheory.CatCoh.Z1 F) :
    ((f.1 : (Coef.ofAlg F).c1), (fun _ ↦ PUnit.unit : (Coef.zero C).c0)) ∈ (Cx.single (Coef.ofAlg F)).Z1 := by
  show Cx.D1 _ _ = 0
  refine Prod.ext ?_ (Prod.ext (funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ rfl) (funext fun _ ↦ rfl))
  funext T T' T'' φ ψ
  have := f.2 φ ψ
  change (mp F ψ) (f.1 T T' φ) - f.1 T T'' (φ ≫ ψ) + f.1 T' T'' ψ = 0
  rw [this]; abel

theorem single_H1_mk_eq_zero_iff (x : (Cx.single (Coef.ofAlg F)).Z1) :
    (QuotientAddGroup.mk x : (Cx.single (Coef.ofAlg F)).H1) = 0 ↔ ∃ g, GlobalTheory.CatCoh.d0 F g = x.1.1 := by
  rw [cx_H1_mk_eq_zero_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, by rw [← hg]; rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Prod.ext (by rw [← hg]; rfl) (Subsingleton.elim _ _)⟩

end Gen

section Gen2

variable {C : Type u} [Category.{0} C] {R : Type} [CommRing R] (F : C ⥤ CommAlgCat.{0} R)

theorem single_fst_mem_Z1 (x : (Cx.single (Coef.ofAlg F)).Z1) : x.1.1 ∈ GlobalTheory.CatCoh.Z1 F := by
  intro T T' T'' φ ψ
  have h : Cx.D1 _ x.1 = 0 := x.2
  have := congrArg (fun c ↦ c.1 T T' T'' φ ψ) h
  change (mp F ψ) (x.1.1 T T' φ) - x.1.1 T T'' (φ ≫ ψ) + x.1.1 T' T'' ψ = 0 at this
  linear_combination -this

theorem single2_mem (z : GlobalTheory.CatCoh.Z2 F) :
    ((z.1 : (Coef.ofAlg F).c2), (fun _ _ _ ↦ PUnit.unit : (Coef.zero C).c1), (fun _ ↦ PUnit.unit : (Coef.zero C).c0))
      ∈ (Cx.single (Coef.ofAlg F)).Z2 :=
  ⟨fun T T' T'' T''' φ ψ χ ↦ z.2 φ ψ χ, fun _ _ _ _ _ ↦ Subsingleton.elim _ _, fun _ _ _ ↦ Subsingleton.elim _ _,
    fun _ ↦ Subsingleton.elim _ _⟩

theorem single_fst_mem_Z2 (x : (Cx.single (Coef.ofAlg F)).Z2) : x.1.1 ∈ GlobalTheory.CatCoh.Z2 F :=
  fun _ _ _ _ φ ψ χ ↦ x.2.1 _ _ _ _ φ ψ χ

theorem single_H2_mk_eq_zero_iff (x : (Cx.single (Coef.ofAlg F)).Z2) :
    (QuotientAddGroup.mk x : (Cx.single (Coef.ofAlg F)).H2) = 0 ↔ ∃ g, GlobalTheory.CatCoh.d1 F g = x.1.1 := by
  rw [cx_H2_mk_eq_zero_iff]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1, by rw [← hg]; rfl⟩
  · rintro ⟨g, hg⟩
    exact ⟨(g, fun _ ↦ PUnit.unit), Prod.ext (by rw [← hg]; rfl) (Subsingleton.elim _ _)⟩

end Gen2

section Lift

variable {D : Data} (Λ : Lift D)

theorem smoothLiftThickenings_restrictionOne_sub {k k' : ((KK D.κ D.t).res Λ.L).T1} {w w' : Tot1 (OAff D.s)} (h : Λ.Res1 k w)
    (h' : Λ.Res1 k' w') : Λ.Res1 (k - k') (w - w') := by
  refine ⟨fun U V a ↦ ?_, fun U ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, h.1 U V a, h'.1 U V a, map_sub]
  · simp only [Prod.snd_sub, Pi.sub_apply, h.2 U, h'.2 U, map_sub, Submodule.Quotient.mk_sub]

theorem smoothLiftThickenings_restrictionTwo_sub {k k' : ((KK D.κ D.t).res Λ.L).T2} {w w' : Tot2 (OAff D.s)} (h : Λ.Res2 k w)
    (h' : Λ.Res2 k' w') : Λ.Res2 (k - k') (w - w') := by
  refine ⟨fun U V W a b ↦ ?_, fun U V a ↦ ?_, fun U ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, h.1 U V W a b, h'.1 U V W a b, map_sub]
  · simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, h.2.1 U V a, h'.2.1 U V a, map_sub,
      Submodule.Quotient.mk_sub]
  · simp only [Prod.snd_sub, Pi.sub_apply, h.2.2 U, h'.2.2 U, map_sub, Submodule.Quotient.mk_sub]

end Lift

section Main

variable (D : Data) (Λ : Lift D)

theorem crystallineCechDeRham_degreeOne_relation_total : (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧
    ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0) := by
  have hfn := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ D.X₀ D.t D.X D.i).1.1
  have hres := (GlobalTheory.T.lift_restriction_bijective_low_degrees D Λ).1
  obtain ⟨hW, hK, hZ⟩ := GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift.1 D Λ
  have key : ∀ k : (KK D.κ D.t).Z1, (∃ g, GlobalTheory.CatCoh.d0 (O D.κ D.t) g = k.1.1) ↔
      ∃ g, ((KK D.κ D.t).res Λ.L).D0 g = ((KK D.κ D.t).resMap Λ.L).p1 k.1 := fun k ↦ by
    have e := (map_eq_zero_iff _ hfn.1 (x := (QuotientAddGroup.mk k : (KK D.κ D.t).H1))).trans
      (map_eq_zero_iff _ hres.1).symm
    exact ((single_H1_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z1 k)).symm.trans e).trans
      (cx_H1_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z1 k))
  refine ⟨fun c ↦ ?_, fun h ↦ ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
    obtain ⟨x, hx⟩ := hfn.2 (QuotientAddGroup.mk ⟨_, single1_mem (O D.κ D.t) f⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (single_H1_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z1 k - ⟨_, single1_mem _ f⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w, hw, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p1 k.1)
    have hwZ : w ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((hZ _ _ hw).1).1 (((KK D.κ D.t).resMap Λ.L).z1 k).2
    refine ⟨Hyp1.mk _ ⟨w, hwZ⟩, k, ⟨k.1.1, single_fst_mem_Z1 _ ((KK D.κ D.t).fnMap.z1 k)⟩, ⟨w, hwZ⟩, ?_, rfl, rfl, hw⟩
    rw [← sub_eq_zero, ← map_sub, GlobalTheory.CatCoh.H1.mk_eq_zero]
    exact ⟨g, hg⟩
  · obtain ⟨w, rfl⟩ := Hyp1.mk_surjective _ h
    obtain ⟨k0, hk0, -⟩ := hK w.1
    have hk0Z : k0 ∈ ((KK D.κ D.t).res Λ.L).Z1 := ((hZ _ _ hk0).1).2 w.2
    obtain ⟨x, hx⟩ := hres.2 (QuotientAddGroup.mk ⟨k0, hk0Z⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (cx_H1_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z1 k - ⟨k0, hk0Z⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w1, hw1, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p1 k.1)
    have hw1Z : w1 ∈ cechDeRhamTotalCocyclesOne (OAff D.s) := ((hZ _ _ hw1).1).1 (((KK D.κ D.t).resMap Λ.L).z1 k).2
    obtain ⟨g', hg'⟩ := (hZ _ _ (smoothLiftThickenings_restrictionOne_sub Λ hw1 hk0)).2.1 ⟨g, hg⟩
    refine ⟨GlobalTheory.CatCoh.H1.mk _ ⟨k.1.1, single_fst_mem_Z1 _ ((KK D.κ D.t).fnMap.z1 k)⟩, k, _, ⟨w1, hw1Z⟩, rfl, ?_,
      rfl, hw1⟩
    rw [← sub_eq_zero, ← map_sub, Hyp1.mk_eq_zero]
    exact ⟨g', hg'⟩
  · rintro c h ⟨k, f, w, rfl, rfl, hkf, hR⟩
    rw [GlobalTheory.CatCoh.H1.mk_eq_zero, Hyp1.mk_eq_zero, ← hkf]
    exact (key k).trans (hZ _ _ hR).2

set_option maxHeartbeats 1000000 in

theorem crystallineCechDeRham_degreeTwo_relation_total : (∀ c, ∃ h, Λ.Rel2 c h) ∧ (∀ h, ∃ c, Λ.Rel2 c h) ∧
    ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) := by
  have hfn := (GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ D.X₀ D.t D.X D.i).1.2
  have hres := (GlobalTheory.T.lift_restriction_bijective_low_degrees D Λ).2
  obtain ⟨hW, hK, hZ⟩ := GlobalTheory.T.compatibleFormsCochains_eq_deRhamCochains_smoothLift.2 D Λ
  have key : ∀ k : (KK D.κ D.t).Z2, (∃ g, GlobalTheory.CatCoh.d1 (O D.κ D.t) g = k.1.1) ↔
      ∃ g, ((KK D.κ D.t).res Λ.L).D1 g = ((KK D.κ D.t).resMap Λ.L).p2 k.1 := fun k ↦ by
    have e := (map_eq_zero_iff _ hfn.1 (x := (QuotientAddGroup.mk k : (KK D.κ D.t).H2))).trans
      (map_eq_zero_iff _ hres.1).symm
    exact ((single_H2_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z2 k)).symm.trans e).trans
      (cx_H2_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z2 k))
  refine ⟨fun c ↦ ?_, fun h ↦ ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H2.mk_surjective _ c
    obtain ⟨x, hx⟩ := hfn.2 (QuotientAddGroup.mk ⟨_, single2_mem (O D.κ D.t) f⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (single_H2_mk_eq_zero_iff (O D.κ D.t) ((KK D.κ D.t).fnMap.z2 k - ⟨_, single2_mem _ f⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w, hw, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p2 k.1)
    have hwZ : w ∈ cechDeRhamTotalCocyclesTwo (OAff D.s) := ((hZ _ _ hw).1).1 (((KK D.κ D.t).resMap Λ.L).z2 k).2
    refine ⟨Hyp2.mk _ ⟨w, hwZ⟩, k, ⟨k.1.1, single_fst_mem_Z2 _ ((KK D.κ D.t).fnMap.z2 k)⟩, ⟨w, hwZ⟩, ?_, rfl, rfl, hw⟩
    rw [← sub_eq_zero, ← map_sub, GlobalTheory.CatCoh.H2.mk_eq_zero]
    exact ⟨g, hg⟩
  · obtain ⟨w, rfl⟩ := Hyp2.mk_surjective _ h
    obtain ⟨k0, hk0, -⟩ := hK w.1
    have hk0Z : k0 ∈ ((KK D.κ D.t).res Λ.L).Z2 := ((hZ _ _ hk0).1).2 w.2
    obtain ⟨x, hx⟩ := hres.2 (QuotientAddGroup.mk ⟨k0, hk0Z⟩)
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨g, hg⟩ := (cx_H2_mk_eq_zero_iff _ (((KK D.κ D.t).resMap Λ.L).z2 k - ⟨k0, hk0Z⟩)).1
      (by rw [QuotientAddGroup.mk_sub]; exact sub_eq_zero.2 hx)
    obtain ⟨w1, hw1, -⟩ := hW (((KK D.κ D.t).resMap Λ.L).p2 k.1)
    have hw1Z : w1 ∈ cechDeRhamTotalCocyclesTwo (OAff D.s) := ((hZ _ _ hw1).1).1 (((KK D.κ D.t).resMap Λ.L).z2 k).2
    have hR : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1 - k0) (w1 - w.1) := smoothLiftThickenings_restrictionTwo_sub Λ hw1 hk0
    have hE := ((hZ _ _ hR).2).1
    obtain ⟨g', hg'⟩ := hE ⟨g, by rw [hg, AddSubgroup.coe_sub]; rfl⟩
    refine ⟨GlobalTheory.CatCoh.H2.mk _ ⟨k.1.1, single_fst_mem_Z2 _ ((KK D.κ D.t).fnMap.z2 k)⟩, k, _, ⟨w1, hw1Z⟩, rfl, ?_,
      rfl, hw1⟩
    rw [← sub_eq_zero, ← map_sub, Hyp2.mk_eq_zero]
    exact ⟨g', hg'⟩
  · rintro c h ⟨k, f, w, rfl, rfl, hkf, hR⟩
    rw [GlobalTheory.CatCoh.H2.mk_eq_zero, Hyp2.mk_eq_zero, ← hkf]
    exact (key k).trans (hZ _ _ hR).2

end Main

theorem rel_total_zero : (∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧
    ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel2 c h) ∧
    (∀ h, ∃ c, Λ.Rel2 c h) ∧ ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) :=
  ⟨crystallineCechDeRham_degreeOne_relation_total, crystallineCechDeRham_degreeTwo_relation_total⟩

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeRepresentingPolarizedHomsLocNoet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomFixGlue

theorem homFix_finiteType : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro S _ A B _ _ _ _ L M hA hB hL hM rA rB aA aB
  refine GlobalTheory.T.homFixedPullback_representable_glue GlobalTheory.T.rigidifiedBundle_pullbackIso_of_localIso_abelianHom S A B L M hA hB hL hM rA rB S.affineOpens (fun U => Sp Γ(S, U)) (fun U => U.2.fromSpec)
    (fun U => IsAffineOpen.isOpenImmersion_fromSpec U.2) ?_ ?_
  · intro s
    obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hU.range_fromSpec.ge hs⟩
  · intro U
    haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian U
    obtain ⟨A', _, _, φA, gA, hA', hL', rA', aA'⟩ := GlobalTheory.T.exists_abelianScheme_restrict_openImmersion S A L hA hL rA aA _ U.2.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec U.2)
    obtain ⟨B', _, _, φB, gB, hB', hM', rB', aB'⟩ := GlobalTheory.T.exists_abelianScheme_restrict_openImmersion S B M hB hM rB aB _ U.2.fromSpec (IsAffineOpen.isOpenImmersion_fromSpec U.2)
    obtain ⟨R, h1, h2, h3⟩ := GlobalTheory.T.exists_finiteType_scheme_representing_polarizedHoms Γ(S, U) A' B' (L.pull φA) (M.pull φB) hA' hB' hL' hM' rA' rB' aA' aB'
    exact ⟨A', B', _, _, φA, φB, R, gA, gB, h1, h2, h3⟩

end GlobalTheory.HomFixGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectExtendOfPIsogenyDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogDVR

theorem exists_obj_extend_of_isPIsog : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (c : ℕ) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (v : Sp V ⟶ Sp R) (o : Obj b N v) (oK o₁ : Obj b N (spMap (algebraMap V K) ≫ v)) (m : ObjMap oK o (spMap (algebraMap V K))) (ψ : oK.A ⟶ o₁.A), IsPIsog c oK o₁ ψ → ∃ o' : Obj b N v, Nonempty (ObjMap o₁ o' (spMap (algebraMap V K))) := by
  intro p _ D R _ b N _ _ c V K _ _ _ _ _ _ v o o₀ o₀' m ψ₀ h
  have hc := h.pos
  obtain ⟨-, hhom, -, -, -, ψ', hhom', h1, h2⟩ := id h
  obtain ⟨hf, hfl⟩ := GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse _ o₀.A o₀'.A o₀.ab o₀'.ab ψ₀ ψ' c hc.ne'
    hhom hhom' h1 h2
  have hsc : Surjective (ψ'.left ≫ ψ₀.left) := by
    rw [← Over.comp_left, h2]; exact GlobalTheory.AbelianLimit.surjective_pow o₀'.A o₀'.ab c hc
  have hs : Surjective ψ₀.left := Surjective.of_comp ψ'.left ψ₀.left
  have hcomm := o.ab.comm
  obtain ⟨B, _, φB, hB, hφB⟩ := exists_model V K o.A o.ab o₀.A o₀'.A m.φ ψ₀ c m.cart o₀'.ab hc
    (fun T x hx => by
      have : x ≫ ψ₀ ≫ ψ' = 1 := by rw [← Category.assoc, hx, MonObj.one_comp]
      rwa [h1, MonObj.comp_pow, Category.comp_id] at this)
  exact exists_obj V K v _ rfl o₀' B φB hB hφB

end GlobalTheory.UPel.HT.ES.IsogDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedLcCentreOfZeroLcThreshold
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem GlobalTheory.PairStep.exists_isolated_of_lcCut_zero : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → N₀.IsLB → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e ≤ 1 →
      ∀ (A : CartierDiv X) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X), IsAmpleLB (toLB A) → 0 < m' → D₀.Eff → 0 < μ →
        (lam : ℝ) < ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e →
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) →
        LcCut p n (Δ + qWeil D₀ m') x 0 →
      ∃ (m : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m ∧ D₀.Eff ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C →
          (interNumRed ℂ C ![toLB D₀] : ℚ) / m = interNumRed ℂ C ![N₀] / r) ∧
        x ∈ U ∧ (∀ y ∈ U, LcAt p n (Δ + qWeil D₀ m) y) ∧
        (∀ y ∈ U, y ≠ x → KltAt p n (Δ + qWeil D₀ m) y) ∧ ¬ KltAt p n (Δ + qWeil D₀ m) x := by
  intro hPr X _ _ _ p n hp hn hn1
  letI := algebraΓOfHom p
  intro Δ r N₀ x c hΔ hklt hr hN₀ hnef hbig hx hc hcZ hsum A lam μ m' D₀ hA hm' hD₀ hμ hlam hnum hcut
  obtain ⟨m, G, hm, hG⟩ := GlobalTheory.T.exists_logCanonicalMultiple_of_globally_klt X p n hp hn Δ hΔ hklt
  have hG' := GlobalTheory.isLogCanonicalMultiple_add_qWeil X p n Δ m m' G D₀ hm hm' hG
  obtain ⟨U, hxU, hlc, hkl⟩ := GlobalTheory.T.exists_open_klt_off_isolated_lcCentre hPr X p n hp hn (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) x
    (Nat.mul_pos hm hm') hG' hx hcut
  have hlam1 : lam ≤ 1 := by
    have : (lam : ℝ) ≤ 1 := (hlam.trans_le hsum).le
    exact_mod_cast this
  obtain ⟨M, E, hM, hE, hxE, hEnum⟩ := GlobalTheory.T.exists_effective_QDivisor_offPoint_ampleClass X p hp N₀ A x r lam μ hN₀ hnef hA hr hlam1 hμ
  obtain ⟨hD, hqW, hDnum⟩ := GlobalTheory.T.cartierDivToWeilQDivisor_add_of_effective X p hp D₀ E m' M hm' hM hD₀ hE
  have hoff : ∀ y, y ∉ E.supp → Off (qWeil E M) y := fun y hy =>
    (GlobalTheory.T.weilQDivisorAvoidsPoint_cartier_iff_notMem_supp X E M y hE hM).2 hy
  have heq : Δ + qWeil (M • D₀ + m' • E) (m' * M) = (Δ + qWeil D₀ m') + (1 : ℚ) • qWeil E M := by
    rw [hqW, one_smul, add_assoc]
  let V : X.Opens := ⟨(E.supp : Set X)ᶜ, E.supp.isClosed.isOpen_compl⟩
  refine ⟨m' * M, M • D₀ + m' • E, U ⊓ V, Nat.mul_pos hm' hM, hD, ?_, ⟨hxU, hxE⟩, ?_, ?_, ?_⟩
  · intro C hC
    have h1 := hDnum C hC
    have h2 := hnum C hC
    have h3 := hEnum C hC
    push_cast at h1 ⊢
    rw [h1, h2, h3]
    ring
  · intro y hy
    rw [heq]
    exact ((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 y (hoff y hy.2)).2.1).2 (hlc y hy.1)
  · intro y hy hyx
    rw [heq]
    exact ((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 y (hoff y hy.2)).1).2 (hkl y hy.1 hyx)
  · rw [heq]
    exact fun h => hcut.2.1 (((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 x (hoff x hxE)).1).1 h)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledUniformisedModelThetaSystemTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem traitLabels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (u' : Sp S.R ⟶ F.X), IsDiagEnd F W ρ.P u' ε → ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ χ, l.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * ((qW W T.β (j χ) : ℤ) : ℝ)) ∧ ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε E).left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  intro g n F W hW o Ω _ _ _ _ S ρ ε u' hD p _ y₀ T ι hι hsp hint
  obtain ⟨T', ι', yK, e, k, hι', hfac, hy', hϖ, hβ⟩ := GlobalTheory.T.exists_trait_finiteExtension_classicalPoint_factors g n F o Ω S u' p y₀ T ι hι hsp
  obtain ⟨A, φ, cart, lb, εA, hDA, huniq⟩ := GlobalTheory.T.exists_pullback_eighth_power_endomorphisms_field_point g n F W S.R ρ.P ε u' hD (FractionRing T'.V) yK
  rw [hy'] at hDA
  obtain ⟨G', _, _, hsemi, D', U', j', hpsi, hcong⟩ := GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight g n F W hW T' A εA hDA
  letI : Algebra (FractionRing T'.V) (PadicAlgCl p) := ι'.toAlgebra
  let u : ρ.UTest p y₀ := { V := T'.V, complete := T'.complete, norm_le := hι', yK := yK, fac := hfac, A := A, φ := φ, cart := cart, lb := lb, G := G', semi := hsemi, D := D', U := U' }
  obtain ⟨l⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p y₀ u hint
  let jj : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X) := j'.trans (AddEquiv.piCongrRight fun _ => e)
  refine ⟨u, l, jj, ?_, ?_⟩
  · intro χ

    obtain ⟨v, hv⟩ := hpsi χ
    obtain ⟨jc, hjc, hval⟩ := GlobalTheory.T.psi_value_fractionRing_of_psiCoord T'.V D'.toPre χ _ hv
    have hq := l.q_eq χ jc hjc
    change ‖algebraMap (FractionRing T'.V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing T'.V))) _ ((D'.toPre.psi χ).s jc).val)‖ = _ at hq
    rw [hval, RingHom.algebraMap_toAlgebra] at hq

    have hunit : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ = 1 := by
      have h1 : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ ≤ 1 := (hι' _).2 ⟨_, rfl⟩
      have h2 : ‖ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V))‖ ≤ 1 := (hι' _).2 ⟨_, rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (v : T'.V))), norm_nonneg (ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V)))]
    set a := ‖ι' (algebraMap T'.V _ T'.ϖ)‖ with ha
    have hq0 : 0 ≤ qW W T'.β (j' χ) :=
      qW_nonneg_of_posW W hW.1 T'.β T'.symm (GlobalTheory.Poinc.Basic₂.trait_nonneg T') (j' χ)
    have hsc : qW W T'.β (j' χ) = (k : ℤ) * qW W T.β (jj χ) := by
      simp only [qW, hβ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [jj, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply]
      ring
    rw [map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hq
    rw [← ha] at hq
    have hN : ((qW W T'.β (j' χ)).toNat : ℝ) = ((k : ℤ) : ℝ) * (qW W T.β (jj χ) : ℝ) := by
      rw [← Int.cast_mul, ← hsc]
      exact_mod_cast Int.toNat_of_nonneg hq0
    have hapos : 0 < a := by
      rw [ha, norm_pos_iff]
      intro h0
      have : algebraMap T'.V (FractionRing T'.V) T'.ϖ = 0 := ι'.injective (by rw [h0, map_zero])
      exact T'.irr.ne_zero (IsFractionRing.injective T'.V (FractionRing T'.V) (by rw [this, map_zero]))
    have hl : -l.q χ = ((qW W T'.β (j' χ)).toNat : ℝ) * Real.log a := by
      rw [← Real.log_pow, hq, Real.log_exp]
    rw [hϖ, Real.log_pow]
    rw [hN] at hl
    push_cast at hl ⊢
    linarith
  · intro m pk pk' x x' E hm h1 h2 hx
    have hc := hcong (PadicAlgCl p) m pk pk' x x' E hm h1 h2 (huniq _ x x' E hx)
    obtain ⟨w, hw⟩ := hc
    refine ⟨fun a => e (w a), ?_⟩
    funext a
    have := congrFun hw a
    simp only [jj, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply] at this ⊢
    rw [this, map_add, map_sum, map_nsmul]
    simp [map_zsmul]

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivLabelledLatticesUnitaryTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.UPoinc.exists_linearEquiv_labelled_of_uIsLabW : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (wi : UWit X), IsProjOver X.M.s → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct ct' : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X) (yy' : X.S.Gam →+ ModN (X.S.r * X.S.N) ct'.T.P.D.toPre.X), UIsLabW X wi ct yy → UIsLabW X wi ct' yy' → ∃ e : ct.T.P.D.toPre.X ≃ₗ[𝓞 E] ct'.T.P.D.toPre.X, ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (e μ) := by
  intro E _ _ _ H Dw hpq l Xo cf C X wi hproj p _ z ct ct' yy yy' hl hl'
  obtain ⟨Y, U₀, EE, G, q, hO, hE, hqp, hpt, hconn, hlift⟩ :=
    GlobalTheory.UPoinc.exists_zhModel_proper_over_uSetup E H Dw hpq l Xo cf C X hproj
  obtain ⟨y, hy⟩ := hlift p z ct
  obtain ⟨y', hy'⟩ := hlift p z ct'
  obtain ⟨θ, hθ, hsm⟩ := GlobalTheory.T.labelledUnitaryTraits_lattices_equiv_connectedFibre E H Dw hpq l Xo cf C X wi Y U₀ EE G q hO hE hqp hpt p z (hconn z)
    ct ct' y y' hy hy' yy yy' hl hl'
  exact ⟨θ.toLinearEquiv hsm, hθ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionLocalVanishingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logResolution_localVanishing : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (Z : Closeds X), η ≠ 0 → 0 < m → Z ≠ ⊤ → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y) (s : Y ⟶ X) (_ : IsDominant s) (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y) (N : CartierDiv X), IsLogRes p n η m G s K B ∧ (∀ y, s y ∈ Z → y ∈ B) ∧ (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) ∧ (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) := by
  first | exact @GlobalTheory.Discrepancy.exists_logRes_subsingleton_cohOn_one | exact GlobalTheory.Discrepancy.exists_logRes_subsingleton_cohOn_one | (intros; apply GlobalTheory.Discrepancy.exists_logRes_subsingleton_cohOn_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointRefinementsCompareUnifStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderTwo_point_refinements_compare_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ D₂' : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₂'.toPre) ∧ Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D₂'.toPre) := by
  first | exact @GlobalTheory.MumCmp.point_and_compare | exact GlobalTheory.MumCmp.point_and_compare | (intros; apply GlobalTheory.MumCmp.point_and_compare <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientFiniteCommGroupSchemeClosedSubgrouStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_finiteCommGroupScheme_closedSubgroup : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : A →ₐc[k] C), Function.Surjective π → ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra k B) (_ : IsCocomm k B) (_ : Module.Finite k B) (j : B →ₐc[k] A), Function.Injective j ∧ kerIdeal j = RingHom.ker π ∧ ∀ (D : Type) [CommRing D] [Bialgebra k D] (f : D →ₐc[k] A), kerIdeal f ≤ RingHom.ker π → ∀ d, f d ∈ Set.range j := by
  first | exact @GlobalTheory.HopfQuot.exists_quotient | exact GlobalTheory.HopfQuot.exists_quotient | (intros; apply GlobalTheory.HopfQuot.exists_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepresentingFamilyOfAuxiliaryRepresentatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_representingFamily_of_auxiliaryRepresentation : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → M.Coprime e → (∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) → HasLevelStructureOfLevel b N (Module.finrank ℤ D.La / 2) M → ∃ F : RepFam b N, IsQProjOver F.s := by
  first | (exact @GlobalTheory.HTQuot.exists_representing_family_of_level_structure) | (exact GlobalTheory.HTQuot.exists_representing_family_of_level_structure) | (intros; apply GlobalTheory.HTQuot.exists_representing_family_of_level_structure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiabelianModelProperOverThetaSetupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiabelianModel_proper_over_thetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (_ : ZHOut X₁.ρ Y U₀ EE) (q : Y.Z ⟶ X₁.M.Z), X₁.S.Over₀ Y U₀ ∧ X₁.S.IsEE Y U₀ EE ∧ IsProper q ∧ Y.pt ≫ q = X₁.M.pt ∧ (∀ z₁ : X₁.M.Z, _root_.IsPreconnected (q.base ⁻¹' {z₁})) ∧ ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ y : Sp (OO p) ⟶ Y.Z, y ≫ q = c.y := by
  first | exact @GlobalTheory.Poinc.exists_zhModel_proper_over_setup | exact GlobalTheory.Poinc.exists_zhModel_proper_over_setup | (intros; apply GlobalTheory.Poinc.exists_zhModel_proper_over_setup <;> assumption)
end

