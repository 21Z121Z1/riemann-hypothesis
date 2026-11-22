import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0662
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFactorOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3488
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleIsoOfLinearDegenerationDataIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LinDataTriple

open GlobalTheory.LinearUnifIso in

theorem act_comm_noeth : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom bc.hom → IsPullUnif (RingHom.id R) hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' → (∀ (x : O) (y : D'.toPre.X), hD.xe (x • y) = x • hD.xe y) → (∀ x, (ιD'.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ (ιD.onB.act x).left) → ∀ x, ιG'.act x ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (ιG.act x) := by
  intro hG R _ _ _ _ I hI D D' A A' G G' _ _ _ _ sG' U U' hD bc hbc hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    lin lin' hx hB a
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨φ, hφ, eφ⟩ := exists_hom_of_pullback_id hs bc
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').1 hU
  have P : ∀ (e : ℕ) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback (thick R I e)).map c).left ≫ pullback.fst Y.hom (thick R I e) =
        pullback.fst X.hom (thick R I e) ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : ιD'.onB.act a ≫ ψ = ψ ≫ ιD.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ]; exact hB a)
  have key : ιG'.act a ≫ φ = φ ≫ ιG.act a := by
    have := sG'.smooth
    have := sG'.geomConnected
    have := U.separated
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I
      (hI ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥) G').2 G _ _ fun e => ?_
    obtain ⟨h, hf, ⟨hp, ht⟩, -⟩ := H e
    obtain rfl : h = ((Over.pullback (thick R I e)).map φ).left := by
      rw [← cancel_mono (pullback.fst G.hom (thick R I e)), P, eφ]
      exact hf
    have hq : (Over.pullback (thick R I e)).map φ ≫ (U.gt e).q =
        (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
      refine Over.OverMorphism.ext ?_
      rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
        Category.assoc, Category.assoc, P, eψ]
      exact hp.symm.trans (Category.assoc _ _ _)
    obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
      (fun x => (ht x).2)
    obtain ⟨t, tc, ti⟩ := lin.i_lin e a
    obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
    have := ιG.hom a
    have := ιG'.hom a
    have hts : t' ≫ s = s ≫ t := by
      refine PowTorus.torus_ext _ _ fun χ z => ?_
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
        ← gm_torusEnd tc', Category.id_comp]
    have E : (Over.pullback (thick R I e)).map (ιG'.act a) ≫ (Over.pullback (thick R I e)).map φ =
        (Over.pullback (thick R I e)).map φ ≫ (Over.pullback (thick R I e)).map (ιG.act a) := by
      refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
          ← Functor.map_comp, ← Functor.map_comp, hψa]
      · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]
    rw [← Functor.map_comp, ← Functor.map_comp] at E
    exact (P e _).symm.trans ((congrArg (fun c => c.left ≫ pullback.fst G.hom (thick R I e)) E).trans (P e _))
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (ιG.act a)).left ≫
      pullback.fst G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (ιG.act a).left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, ← eφ, ← Category.assoc, ← eφ,
    ← Over.comp_left, key, Over.comp_left]

end GlobalTheory.LinDataTriple

theorem GlobalTheory.triple_iso_of_linear_data_iso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (t t' : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (P' : PELUnif (maximalIdeal V) t') (hD : IsPullDeg (RingHom.id V) P.D.toPre P'.D.toPre), (∀ (x : 𝓞 E) y, hD.xe (x • y) = x • hD.xe y) → (letI := H.starRing; ∀ x, P'.oD.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id V))).map (P.oD.onB.act x)) → Nonempty (SABMap t' t (𝟙 _)) := by
  intro E _ _ _ H V _ _ _ hB t t' P P' hD hx hB'
  letI := H.starRing
  have hR : AdmBase V (maximalIdeal V) := hB.1
  have := hR.1
  obtain ⟨ψ, bc, -, hψm, hbcm, hbc', hP, -⟩ := GlobalTheory.unif_determined_by_data_normal V hR P.D P.A t.G t.semi P.U
    P'.D P'.A t'.G t'.semi P'.U hD
  have hL := GlobalTheory.firstFiveLaws.1
  have hBl : ∀ x, (P'.oD.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) =
      (hD.e.hom.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) ≫ (P.oD.onB.act x).left := by
    intro x
    have e := congrArg (fun c => c.left ≫ pullback.fst P.D.toPre.P.A.hom (specOf (RingHom.id V))) (hB' x)
    simp only [Over.comp_left, Category.assoc] at e
    rw [e]
    exact congrArg (hD.e.hom.left ≫ ·) (pullback.lift_fst _ _ _)
  have hact := GlobalTheory.LinDataTriple.act_comm_noeth hL.globalFns V (maximalIdeal V) rfl P.D P'.D P.A P'.A t.G t'.G
    t'.semi P.U P'.U hD bc hbcm hP (𝓞 E) P.oD P'.oD P.oA P'.oA t.act.toRingAct t'.act.toRingAct P.lin P'.lin hx hBl
  have hact' : ∀ a, (t'.act.act a).left ≫ ψ.hom.left = ψ.hom.left ≫ (t.act.act a).left := by
    intro a
    have e := congrArg (fun c => c.left ≫ pullback.fst t.G.hom (specOf (RingHom.id V))) (hact a)
    simp only [Over.comp_left, Category.assoc] at e
    rw [← hbc', Category.assoc]
    exact e.trans (congrArg (bc.hom.left ≫ ·) (pullback.lift_fst _ _ _))
  have hLB : LBIso t'.PP.L (t.PP.L.pull ψ.hom.left) := by
    obtain ⟨w, hw, -⟩ := hP.lg
    rw [← P.bundle, ← P'.bundle, ← hbc']
    exact ⟨w, hw⟩
  have := P'.U.gen_hom
  have hp : IsProper (pullback.snd t'.G.hom (jK V)) :=
    MorphismProperty.of_isPullback (P := @IsProper) (isGrpPullback_of_iso P'.U.gen).1 P'.A.isAb.proper
  have hab := GlobalTheory.RigCube.genericPoints_subset_abLocus t'.G t'.semi hp
  obtain ⟨ν, -⟩ := GlobalTheory.exists_sabMap_of_lbIso E H (Sp V) (Sp V) t t' (𝟙 _) ψ.hom.left ⟨inferInstance, hab⟩
    (isGrpPullback_of_iso ψ) hact' hLB
  exact ⟨ν⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalAbelianSchemeTorsionRationalFieldPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.XFTorsion

open GlobalTheory.FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem zeta_pow (l : Geo.Tor.Level H) : zeta l.M' ^ (l.M' / l.A) = zeta l.A := by
  obtain ⟨m, hm⟩ := A_dvd_M' l
  have hM := M'_pos l
  have hm0 : (m : ℂ) ≠ 0 := by
    rintro h
    rw [Nat.cast_eq_zero] at h
    subst h
    omega
  have hA : (l.A : ℂ) ≠ 0 := Nat.cast_ne_zero.2 l.A_pos.ne'
  rw [hm, Nat.mul_div_cancel_left _ l.A_pos, zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem torsion_fixed {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {b : Base l B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S)
    (β : B →+* k) (hx : x ≫ s = spMap β) (z : kˣ) (hz : IsPrimitiveRoot z l.M')
    (hzA : (z : k) ^ (l.M' / l.A) = β b.ζ) (σ : k ≃+* k) (hσ : spMap (σ : k →+* k) ≫ x = x) (hσz : σ z = z)
    (w : Over.mk x ⟶ o.t.G) (hw : w ^ l.M' = 1) : spMap (σ : k →+* k) ≫ w.left = w.left := by
  obtain ⟨ev, ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩, hu⟩ := exists_unique_fullLevel o k x β hx z hz hzA
  have hid : spMap (RingHom.id k) = 𝟙 (Sp k) := Spec.map_id _
  have e1 : spMap (σ.symm : k →+* k) ≫ spMap (σ : k →+* k) = 𝟙 _ := by
    rw [spMap_comp, ← hid]; congr 1; ext a; simp
  have e2 : spMap (σ : k →+* k) ≫ spMap (σ.symm : k →+* k) = 𝟙 _ := by
    rw [spMap_comp, ← hid]; congr 1; ext a; simp
  have hσ' : spMap (σ.symm : k →+* k) ≫ x = x := by
    conv_lhs => rw [← hσ, ← Category.assoc, e1, Category.id_comp]
  let g : (Over.mk x : Over S) ⟶ Over.mk x := Over.homMk (spMap (σ : k →+* k)) hσ
  let g' : (Over.mk x : Over S) ⟶ Over.mk x := Over.homMk (spMap (σ.symm : k →+* k)) hσ'
  have gg' : g ≫ g' = 𝟙 _ := Over.OverMorphism.ext e2
  have g'g : g' ≫ g = 𝟙 _ := Over.OverMorphism.ext e1
  have key : (fun a => g ≫ ev a) = ev := by
    refine (hu _ ⟨⟨fun a c => ?_, fun c a => ?_, fun a => ?_, fun u => ?_, fun a c => ?_⟩, fun a => ?_, fun a ha => ?_⟩).trans
      (hu ev ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7⟩).symm
    · show g ≫ ev (a + c) = (g ≫ ev a) * (g ≫ ev c)
      rw [h1, MonObj.comp_mul]
    · show g ≫ ev (c • a) = (g ≫ ev a) ≫ o.t.act.act c
      rw [h2, Category.assoc]
    · show g ≫ ev a = 1 ↔ _
      rw [← h3]
      refine ⟨fun h => ?_, fun h => by rw [h, MonObj.comp_one]⟩
      rw [← Category.id_comp (ev a), ← g'g, Category.assoc, h, MonObj.comp_one]
    · refine ⟨fun h => ?_, ?_⟩
      · obtain ⟨a, ha⟩ := (h4 (g' ≫ u)).1 (by rw [← MonObj.comp_pow, h, MonObj.comp_one])
        refine ⟨a, ?_⟩
        show g ≫ ev a = u
        rw [ha, ← Category.assoc, gg', Category.id_comp]
      · rintro ⟨a, rfl⟩
        show (g ≫ ev a) ^ l.M' = 1
        rw [← MonObj.comp_pow, (h4 _).2 ⟨a, rfl⟩, MonObj.comp_one]
    · have h₁ := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.SemiRigid.globalFns (GlobalTheory.ObjDim.isAbelianScheme o) o.t.PP.isLB g
        (h5 a c)
      have e' : Units.map g.left.appTop.hom.toMonoidHom (unitOn (z ^ D.EF a c)) =
          unitOn (Units.map (σ : k →+* k).toMonoidHom (z ^ D.EF a c)) :=
        Units.ext (congrArg (fun q => q.hom (z ^ D.EF a c).val)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : k →+* k)))).symm
      have e'' : Units.map (σ : k →+* k).toMonoidHom (z ^ D.EF a c) = z ^ D.EF a c := by
        rw [map_zpow]
        congr 1
        exact Units.ext hσz
      rw [e''] at e'
      exact (congrArg (WeilIs o.t.G o.t.PP.L (l.M' : ℕ) (g ≫ ev a) (g ≫ ev c)) e').mp h₁
    · show (g ≫ ev a) ^ (l.M' / l.A) = toUnit _ ≫ o.etaA a
      rw [← MonObj.comp_pow, h6, comp_toUnit_assoc]
    · show (g ≫ ev a) ^ (l.M' / l.M) = toUnit _ ≫ o.eta a
      rw [← MonObj.comp_pow, h7 a ha, comp_toUnit_assoc]
  obtain ⟨a, rfl⟩ := (h4 w).1 hw
  exact congrArg CommaMorphism.left (congrFun key a)

theorem torsion_rational : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (K K' : Type) [Field K] [Field K'] [IsAlgClosed K'] (κ : K →+* K') (y : Sp K ⟶ Xo.XF c) (x : Over.mk (spMap κ ≫ y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G), x ^ l.M' = 1 → ∃ x₀ : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G, x₀ ^ l.M' = 1 ∧ x.left = spMap κ ≫ x₀.left := by
  intro E _ _ _ H Dw l Xo c _ K K' _ _ _ κ y x hx
  obtain ⟨bF, hbF⟩ : ∃ bF : c.F →+* K, y ≫ pullback.snd _ _ = spMap bF :=
    ⟨(Spec.preimage (y ≫ pullback.snd _ _)).hom, (Spec.map_preimage _).symm⟩
  haveI : CharZero K := RingHom.charZero_iff bF.injective |>.1 inferInstance
  letI : Algebra K K' := κ.toAlgebra
  let inc := (IntermediateField.inclusion c.le).toRingHom
  have hs : (spMap κ ≫ y ≫ pullback.fst _ _) ≫ Xo.s = spMap (κ.comp (bF.comp inc)) := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc y, hbF, spMap_comp, spMap_comp]
  let z₀ : c.F := ⟨zeta l.M', c.zeta_mem⟩
  have hz₀ : IsPrimitiveRoot z₀ l.M' := IsPrimitiveRoot.of_map_of_injective (f := c.F.val.toRingHom)
    (Complex.isPrimitiveRoot_exp l.M' (M'_pos l).ne') Subtype.val_injective
  have hz₁ : IsPrimitiveRoot (κ (bF z₀)) l.M' := (hz₀.map_of_injective bF.injective).map_of_injective κ.injective
  let z : K'ˣ := (hz₁.isUnit (M'_pos l).ne').unit
  have hz : IsPrimitiveRoot z l.M' := IsPrimitiveRoot.coe_units_iff.1 hz₁
  have hzA : (z : K') ^ (l.M' / l.A) = (κ.comp (bF.comp inc)) (baseKA l).ζ := by
    show κ (bF z₀) ^ _ = κ (bF (inc _))
    rw [← map_pow, ← map_pow]
    congr 2
    exact Subtype.ext (zeta_pow l)
  obtain ⟨p, hp, -⟩ := GlobalTheory.FixedPoint.existsUnique_factor_of_isAlgClosed (K₀ := K) (L := K') x.left fun σ =>
    torsion_fixed Xo.univ K' _ _ hs z hz hzA σ.toRingEquiv (by
      rw [← Category.assoc, spMap_comp]
      congr 2
      ext a
      exact σ.commutes a) (σ.commutes (bF z₀)) x hx
  haveI : Epi (spMap κ) := GlobalTheory.FixedPoint.epi_specAlg (K₀ := K) (K₁ := K')
  have hp' : spMap κ ≫ p = x.left := hp
  have hpo : p ≫ Xo.univ.t.G.hom = y ≫ pullback.fst _ _ := by
    rw [← cancel_epi (spMap κ), ← Category.assoc, hp']
    exact Over.w x
  let x₀ : Over.mk (y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G := Over.homMk p hpo
  let g : (Over.mk (spMap κ ≫ y ≫ pullback.fst _ _) : Over Xo.X) ⟶ Over.mk (y ≫ pullback.fst _ _) :=
    Over.homMk (spMap κ) rfl
  have hg : g ≫ x₀ = x := Over.OverMorphism.ext hp'
  refine ⟨x₀, Over.OverMorphism.ext ?_, hp'.symm⟩
  have h : g ≫ x₀ ^ l.M' = g ≫ 1 := by rw [MonObj.comp_pow, hg, hx, MonObj.comp_one]
  exact (cancel_epi (spMap κ)).1 (congrArg CommaMorphism.left h)

end GlobalTheory.XFTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalVectorFieldUniqueCombinationBasis
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertSpan

open GlobalTheory.Points (le_preimage_mono)

theorem exists_epsPt : ∀ (Z : Scheme.{0}) (W : Z.Opens) (e : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)), IsField W e → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ Z), ⊤ ≤ g₀ ⁻¹ᵁ W → ∃ w : Sp (DualNumber S) ⟶ Z, spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ ∧ ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (O : Z.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(Z, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = valR (spMap ρ ≫ g₀) O (e O f) := GlobalTheory.T.exists_dualNumberPoint_of_vectorField

theorem exists_coeffs : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ → w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom → ∃ c : Fin n → S, ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), (valR (spMap (dualMap ρ) ≫ w) O f).snd = ∑ a, ρ (c a) * (valR (wt a) O f).snd := GlobalTheory.T.exists_coeffs_tangentVector_translatedBasis

theorem coeffs_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ t.G.left) (W : t.G.left.Opens), W ≤ t.G.hom ⁻¹ᵁ U.1 → ⊤ ≤ g₀ ⁻¹ᵁ W → ∀ c : Fin n → S, (∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S') (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)), (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) → ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O), ∑ a, ρ (c a) * (valR (wt a) O f).snd = 0) → c = 0 := GlobalTheory.T.tangent_basis_translate_coefficients_zero

theorem vert_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (W : t.G.left.Opens) (hW : W ≤ t.G.hom ⁻¹ᵁ U.1) (e : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), IsField W e → (∀ r : Γ(X, U.1), e W ((t.G.hom.appLE U.1 W hW).hom r) = 0) → ∃! c : Fin n → Γ(t.G.left, W), ∀ (O : t.G.left.Opens) (hO : O ≤ W) (f : Γ(t.G.left, O)), e O f = ∑ a, resG t.G.left hO (c a) * δ a O f := by
  intro E _ _ _ H X t U n v hv hb δ hδF hδ0 hδv W hW e he he0
  classical
  have hφ : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left), ⊤ ≤ g ⁻¹ᵁ W →
      ∃ φ : Γ(X, U.1) →+* S, g ≫ t.G.hom = spMap φ ≫ chart U := fun S _ g hg =>
    ⟨_, (GlobalTheory.Points.specMap_valMap_fromSpec U.2 (g ≫ t.G.hom) (le_preimage_mono g hW hg)).symm⟩
  have hE : ∀ (S : Type) [CommRing S] (g₀ : Sp S ⟶ t.G.left), ⊤ ≤ g₀ ⁻¹ᵁ W → ∃ c : Fin n → S,
      ∀ (S' : Type) [CommRing S'] (ρ : S →+* S') (φ' : Γ(X, U.1) →+* S')
        (wt : Fin n → (Sp (DualNumber S') ⟶ t.G.left)),
        (spMap ρ ≫ g₀) ≫ t.G.hom = spMap φ' ≫ chart U → (∀ a, IsTranslate t φ' (spMap ρ ≫ g₀) (v a) (wt a)) →
        ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ (spMap ρ ≫ g₀) ⁻¹ᵁ O → ∀ f : Γ(t.G.left, O),
          valR (spMap ρ ≫ g₀) O (e O f) = ∑ a, ρ (c a) * (valR (wt a) O f).snd := by
    intro S _ g₀ hg
    obtain ⟨φ, hφg⟩ := hφ S g₀ hg
    obtain ⟨w, hred, hw⟩ := exists_epsPt t.G.left W e he S g₀ hg
    have hwW : ⊤ ≤ w ⁻¹ᵁ W := GlobalTheory.CechKS.le_preimage_of_red hred hg
    have hid : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
    have hid' : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
      have : dualMap (RingHom.id S) = RingHom.id _ := by
        refine RingHom.ext fun z => ?_
        ext <;> simp [dualMap]
      rw [this]
      exact Spec.map_id _
    have hover : w ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom := by
      have hU1 : ⊤ ≤ (w ≫ t.G.hom) ⁻¹ᵁ U.1 := le_preimage_mono w hW hwW
      have hU0 : ⊤ ≤ (g₀ ≫ t.G.hom) ⁻¹ᵁ U.1 := le_preimage_mono g₀ hW hg
      have hU2 : ⊤ ≤ (spMap (algebraMap S (DualNumber S)) ≫ g₀ ≫ t.G.hom) ⁻¹ᵁ U.1 :=
        fun p _ => hU0 (Set.mem_univ (spMap (algebraMap S (DualNumber S)) p))
      refine GlobalTheory.Points.ext_of_valR U.2 hU1 hU2 fun r => ?_
      rw [← GlobalTheory.Points.valR_appLE w t.G.hom hW hwW r, GlobalTheory.Points.valR_spMap_comp _ _ _ hU0,
        ← GlobalTheory.Points.valR_appLE g₀ t.G.hom hW hg r]
      have h₁ := GlobalTheory.Points.valR_spMap_comp (TrivSqZeroExt.fstHom S S S).toRingHom w W hwW
        ((t.G.hom.appLE U.1 W hW).hom r)
      rw [hred] at h₁
      have h₂ := hw S (RingHom.id S) W le_rfl (by rw [hid, Category.id_comp]; exact hg)
        ((t.G.hom.appLE U.1 W hW).hom r)
      rw [hid, hid', Category.id_comp, Category.id_comp, he0, GlobalTheory.Points.valR_zero _ _ hg] at h₂
      ext
      · rw [h₁]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rw [h₂]
        simp [TrivSqZeroExt.algebraMap_eq_inl]
    obtain ⟨c, hc⟩ := exists_coeffs E H X t U n v hv hb S φ g₀ w hφg hred hover
    exact ⟨c, fun S' _ ρ φ' wt h₁ h₂ O hO hgO f => by
      rw [← hw S' ρ O hO hgO f, hc S' ρ φ' wt h₁ h₂ O hgO f]⟩
  let F : ∀ (S : Type) [CommRing S], (Sp S ⟶ t.G.left) → Fin n → S := fun S _ g =>
    if h : ⊤ ≤ g ⁻¹ᵁ W then (hE S g h).choose else 0
  have hF : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left) (h : ⊤ ≤ g ⁻¹ᵁ W), F S g = (hE S g h).choose :=
    fun S _ g h => dif_pos h
  have hrel : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left) (hg : ⊤ ≤ g ⁻¹ᵁ W) (φ : Γ(X, U.1) →+* S)
      (wt : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g ≫ t.G.hom = spMap φ ≫ chart U →
      (∀ a, IsTranslate t φ g (v a) (wt a)) → ∀ (O : t.G.left.Opens), O ≤ W → ⊤ ≤ g ⁻¹ᵁ O →
      ∀ f : Γ(t.G.left, O), valR g O (e O f) = ∑ a, F S g a * (valR (wt a) O f).snd := by
    intro S _ g hg φ wt h₁ h₂ O hO hgO f
    have hid : spMap (RingHom.id S) ≫ g = g := by
      rw [show spMap (RingHom.id S) = 𝟙 _ from Spec.map_id _, Category.id_comp]
    have := (hE S g hg).choose_spec S (RingHom.id S) φ wt (by rw [hid]; exact h₁) (by rw [hid]; exact h₂) O hO
      (by rw [hid]; exact hgO) f
    rw [hid] at this
    rw [this, hF S g hg]
    rfl
  have hnat : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ρ : S →+* S') (g : Sp S ⟶ t.G.left),
      ⊤ ≤ g ⁻¹ᵁ W → F S' (spMap ρ ≫ g) = fun a => ρ (F S g a) := by
    intro S S' _ _ ρ g hg
    have hg' : ⊤ ≤ (spMap ρ ≫ g) ⁻¹ᵁ W := fun p _ => hg (Set.mem_univ (spMap ρ p))
    have hz := coeffs_eq_zero E H X t U n v hv hb S' (spMap ρ ≫ g) W hW hg'
      (fun a => F S' (spMap ρ ≫ g) a - ρ (F S g a)) (fun S'' _ ρ' φ' wt h₁ h₂ O hO hgO f => by
        have hc : spMap (ρ'.comp ρ) ≫ g = spMap ρ' ≫ spMap ρ ≫ g := by
          rw [← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
        have e₁ := (hE S' (spMap ρ ≫ g) hg').choose_spec S'' ρ' φ' wt h₁ h₂ O hO hgO f
        have e₂ := (hE S g hg).choose_spec S'' (ρ'.comp ρ) φ' wt (by rw [hc]; exact h₁) (by rw [hc]; exact h₂) O hO
          (by rw [hc]; exact hgO) f
        rw [hc, ← hF S g hg] at e₂
        rw [← hF S' (spMap ρ ≫ g) hg'] at e₁
        simp only [RingHom.comp_apply] at e₂
        simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
        rw [← e₁, ← e₂, sub_self])
    funext a
    exact sub_eq_zero.1 (congrFun hz a)
  choose cs hcs using fun a => GlobalTheory.LogKSLin.exists_sec W (fun S _ g => F S g a)
    (fun S S' _ _ ρ g hg => congrFun (hnat S S' ρ g hg) a)
  have hval : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left) (φ : Γ(X, U.1) →+* S)
      (wt : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g ≫ t.G.hom = spMap φ ≫ chart U →
      (∀ a, IsTranslate t φ g (v a) (wt a)) → ∀ (O : t.G.left.Opens) (hO : O ≤ W), ⊤ ≤ g ⁻¹ᵁ O →
      ∀ (c : Fin n → Γ(t.G.left, W)) (f : Γ(t.G.left, O)),
        valR g O (∑ a, resG t.G.left hO (c a) * δ a O f) = ∑ a, valR g W (c a) * (valR (wt a) O f).snd := by
    intro S _ g φ wt hφg hwt O hO hgO c f
    rw [GlobalTheory.Points.valR_eq _ _ hgO, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← GlobalTheory.Points.valR_eq _ _ hgO, GlobalTheory.Points.valR_mul _ _ hgO, GlobalTheory.Points.valR_res _ hO hgO,
      hδv a O (hO.trans hW) f S φ g (wt a) hφg hgO (hwt a)]
  have hex : ∀ (O : t.G.left.Opens) (hO : O ≤ W) (f : Γ(t.G.left, O)),
      e O f = ∑ a, resG t.G.left hO (cs a) * δ a O f := by
    intro O hO f
    refine GlobalTheory.CechInv.ext_of_valR O _ _ fun S _ g hg => ?_
    have hgW := le_preimage_mono g hO hg
    obtain ⟨φ, hφg⟩ := hφ S g hgW
    choose wt hwt using fun a => (existsUnique_isTranslate t φ hφg (hv a)).exists
    rw [hrel S g hgW φ wt hφg hwt O hO hg f, hval S g φ wt hφg hwt O hO hg cs f]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hcs a S g hgW]
  refine ⟨cs, hex, fun c' hc' => ?_⟩
  have key : ∀ (S : Type) [CommRing S] (g : Sp S ⟶ t.G.left), ⊤ ≤ g ⁻¹ᵁ W →
      (fun a => valR g W (c' a) - valR g W (cs a)) = 0 := by
    intro S _ g hg
    refine coeffs_eq_zero E H X t U n v hv hb S g W hW hg _ fun S' _ ρ φ' wt h₁ h₂ O hO hgO f => ?_
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← GlobalTheory.Points.valR_spMap_comp ρ g W hg]
    rw [← hval S' (spMap ρ ≫ g) φ' wt h₁ h₂ O hO hgO c' f, ← hval S' (spMap ρ ≫ g) φ' wt h₁ h₂ O hO hgO cs f,
      ← hc' O hO f, ← hex O hO f, sub_self]
  funext a
  exact GlobalTheory.CechInv.ext_of_valR W _ _ fun S _ g hg => sub_eq_zero.1 (congrFun (key S g hg) a)

end GlobalTheory.VertSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelFirstCoordEquations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section
open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.ZarhinFam

namespace GlobalTheory.ZarhinKerA

variable {S : Scheme.{0}}

theorem mkZ_pa' {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S}
    (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) : mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa, lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb' {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B] {T : Over S}
    (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) : mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb, lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem pull_zCls {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (w w' : Y ⟶ Zob A B) :
    CechPic.pull (lift w w').left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (w ≫ pa A B i) (w' ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (w ≫ pa A B i) (w' ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (w' ≫ pa A B i) (w ≫ pb A B j)) +
      ∑ j, evc hQ (w' ≫ pb A B j ≫ mu) (w ≫ pb A B j) := by
  simp only [zCls, map_add, map_sum, map_zsmul, evc, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc]

theorem zarhinBundle_kernel : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i ≫ la) * ∏ j, (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ GlobalTheory.ZarhinFam.quat d j i = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx i
  have hP := c.isLB
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hQd : IsDual c.A B Q := hZ.2.1
  have hQd' : IsDual B c.A (swap Q) := hZ.2.2.1
  have hs : (swap Q).IsLB := hQd'.isLB
  haveI : IsMonHom mu := hZ.2.2.2.2.1

  have h0 : CechPic.pull (lift (snd (Zob c.A B) T ≫ x) (fst (Zob c.A B) T)).left
      (zCls c.A B c.isLB hQ d mu) = 0 := by
    rw [← cls_zP c.A B c.isLB hQ d mu, ← cls_pull (zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _
      (pull_isLB (zarhinBundle_isLineBundle c.A B c.isLB hQ d mu) _)]
    exact (cls_eq_zero_iff _).2 hx

  let inc : c.A ⟶ Zob c.A B := mkZ c.A B (fun k => if k = i then 𝟙 c.A else 1) (fun _ => 1)
  have h1 := congrArg (CechPic.pull (lift (fst c.A T ≫ inc) (snd c.A T)).left) h0
  rw [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst, pull_zCls] at h1
  have hpa : ∀ k, (fst c.A T ≫ inc) ≫ pa c.A B k = if k = i then fst c.A T else 1 := by
    intro k
    rw [Category.assoc, mkZ_pa']
    split_ifs <;> simp [MonObj.comp_one]
  have hpb : ∀ j, (fst c.A T ≫ inc) ≫ pb c.A B j = 1 := by
    intro j
    rw [Category.assoc, mkZ_pb', MonObj.comp_one]
  have z1 : ∀ {Y : Over S} (a : Y ⟶ c.A), evc hP a (1 : Y ⟶ c.A) = 0 := fun a => evc_one_right hP c.rig₂ a
  have z2 : ∀ {Y : Over S} (a : Y ⟶ c.A), evc hQ a (1 : Y ⟶ B) = 0 := fun a => evc_one_right hQ hQd.zero a
  have z3 : ∀ {Y : Over S} (b : Y ⟶ B), evc hQ (1 : Y ⟶ c.A) b = 0 := fun b => hQd.additive.evc_one hQ b
  have s1 : (∑ k, evc hP ((snd c.A T ≫ x) ≫ pa c.A B k) ((fst c.A T ≫ inc) ≫ pa c.A B k)) =
      evc hP ((snd c.A T ≫ x) ≫ pa c.A B i) (fst c.A T) := by
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [hpa, if_neg hk, z1]) (fun hi => absurd (Finset.mem_univ i) hi),
      hpa, if_pos rfl]
  have s2 : (∑ k, ∑ j, quat d j k • evc hQ ((snd c.A T ≫ x) ≫ pa c.A B k) ((fst c.A T ≫ inc) ≫ pb c.A B j)) = 0 := by
    simp only [hpb, z2, smul_zero, Finset.sum_const_zero]
  have s3 : (∑ k, ∑ j, quat d j k • evc hQ ((fst c.A T ≫ inc) ≫ pa c.A B k) ((snd c.A T ≫ x) ≫ pb c.A B j)) =
      ∑ j, quat d j i • evc hQ (fst c.A T) ((snd c.A T ≫ x) ≫ pb c.A B j) := by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp only [hpa, if_neg hk, z3, smul_zero, Finset.sum_const_zero])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [hpa, if_pos rfl]
  have s4 : (∑ j, evc hQ ((fst c.A T ≫ inc) ≫ pb c.A B j ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j)) = 0 := by
    simp only [← Category.assoc _ (pb c.A B _) mu, hpb, MonObj.one_comp, z3, Finset.sum_const_zero]
  rw [s1, s2, s3, s4, add_zero, add_zero] at h1

  have eS : cls c.P hP = evc hP (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff hP (pull_isLB hP _)).2 c.symm
  have eL : cls c.P hP = evc hQ (fst c.A c.A) (snd c.A c.A ≫ la) :=
    (cls_eq_iff hP (pull_isLB hQ _)).2 hZ.2.2.2.2.2.2.2
  have ePQ : ∀ {Y : Over S} (u a : Y ⟶ c.A), evc hP u a = evc hQ a (u ≫ la) := by
    intro Y u a
    have e1 := congrArg (CechPic.pull (lift u a).left) eS
    have e2 := congrArg (CechPic.pull (lift a u).left) eL
    rw [pull_evc, lift_snd, lift_fst] at e1
    rw [pull_evc, lift_fst, lift_snd_assoc] at e2
    exact e1.trans e2

  have hadd : ∀ {Y : Over S} (a : Y ⟶ c.A) (b b' : Y ⟶ B), evc hQ a (b * b') = evc hQ a b + evc hQ a b' := by
    intro Y a b b'
    rw [← evc_swap hQ hs, ← evc_swap hQ hs, ← evc_swap hQ hs]
    exact (isAdditive_iff hs).1 hQd'.additive Y b b' a
  let φ : (T ⟶ B) →* Multiplicative (Pic (c.A ⊗ T).left) :=
    MonoidHom.mk' (fun b => Multiplicative.ofAdd (evc hQ (fst c.A T) (snd c.A T ≫ b))) fun b b' => by
      simp only [MonObj.comp_mul, hadd, ofAdd_add]
  refine (hQd.isPerfect hQd').ker_right T _ ((triv_ev_iff hQ _ _).2 ?_)
  have key : Multiplicative.toAdd (φ ((x ≫ pa c.A B i ≫ la) * ∏ j, (x ≫ pb c.A B j) ^ quat d j i)) =
      evc hQ (fst c.A T) (snd c.A T ≫ ((x ≫ pa c.A B i ≫ la) * ∏ j, (x ≫ pb c.A B j) ^ quat d j i)) := rfl
  rw [← key, map_mul, map_prod, toAdd_mul, toAdd_prod]
  simp only [map_zpow, toAdd_zpow, φ, MonoidHom.mk'_apply, toAdd_ofAdd]
  rw [← Category.assoc, ← Category.assoc, ← ePQ]
  simpa only [Category.assoc] using h1

end GlobalTheory.ZarhinKerA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinLevelAdditiveKilledByLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinLevel_additive_killed_by_level : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∀ (κ : Fin 8 → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), GlobalTheory.ZarhinFam.KappaOK h M d κ → (∀ a b, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) (a + b) = (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a * (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) b) ∧ ∀ a, (GlobalTheory.ZarhinFam.levZ c.lev (GlobalTheory.ZarhinFam.incZ c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) (GlobalTheory.ZarhinFam.oMat d) κ) a ^ M = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors) | (exact GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors) | (intros; apply GlobalTheory.ZarhinFam.LevAlg.levZ_add_tors  <;> assumption)
end

