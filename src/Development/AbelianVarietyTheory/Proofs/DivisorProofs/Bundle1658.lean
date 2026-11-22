import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelsOfChain
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorAtOriginEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFiniteFlat
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IwLevel.HTTorsionFF

theorem exists_gen_idem {R : Type} [CommRing R] [IsDedekindDomain R] (w : Ideal R) (hw : w ≠ ⊥) :
    ∃ α x : R, α ≠ 0 ∧ α ∈ w ∧ x ∈ w ∧ x * x - x ∈ Ideal.span {α} ∧ w = Ideal.span {α, x} := by
  have hw2 : w ^ 2 ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, pow_eq_zero_iff two_ne_zero, Ideal.zero_eq_bot]; exact hw
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.pow_le_self two_ne_zero : w ^ 2 ≤ w) hw2
  obtain ⟨α, hα0, hα⟩ : ∃ α : R, α ≠ 0 ∧ w ^ 2 ⊔ Ideal.span {α} = w := by
    by_cases h0 : y = 0
    · subst h0
      rw [Ideal.span_singleton_eq_bot.2 rfl, sup_bot_eq] at hy
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw2
      exact ⟨z, hz0, by rw [sup_eq_left.2 ((Ideal.span_singleton_le_iff_mem _).2 hz), hy]⟩
    · exact ⟨y, h0, hy⟩
  have hαw : α ∈ w := by
    rw [← hα]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self α)
  have hidem : IsIdempotentElem (w.map (Ideal.Quotient.mk (Ideal.span {α}))) := by
    unfold IsIdempotentElem
    conv_rhs => rw [← hα]
    rw [Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, sq, Ideal.map_mul]
  have hfg : (w.map (Ideal.Quotient.mk (Ideal.span {α}))).FG := Ideal.FG.map (IsNoetherian.noetherian w) _
  obtain ⟨e, he, hwe⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).1 hidem
  have he_mem : e ∈ w.map (Ideal.Quotient.mk (Ideal.span {α})) := by
    rw [hwe]; exact Submodule.mem_span_singleton_self e
  obtain ⟨x, hxw, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 he_mem
  refine ⟨α, x, hα0, hαw, hxw, ?_, le_antisymm (fun c hc => ?_) ?_⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, he.eq, sub_self]
  · have hc' : Ideal.Quotient.mk (Ideal.span {α}) c ∈
        (R ⧸ Ideal.span {α}) ∙ (Ideal.Quotient.mk (Ideal.span {α}) x) := by
      rw [← hwe]; exact Ideal.mem_map_of_mem _ hc
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hc'
    obtain ⟨d', rfl⟩ := Ideal.Quotient.mk_surjective d
    have h1 : c - d' * x ∈ Ideal.span {α} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← smul_eq_mul, hd, sub_self]
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
    have h2 : c = a * α + d' * x := by rw [ha]; ring
    rw [h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ rfl)))
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact hαw
    · exact hxw

theorem ringHom_flat_of_retract {A B C : CommRingCat.{0}} (ψ : A ⟶ C) (σ : C ⟶ B) (π : B ⟶ C)
    (h : σ ≫ π = 𝟙 C) (hf : (ψ ≫ σ).hom.Flat) : ψ.hom.Flat := by
  letI := ψ.hom.toAlgebra
  letI := (ψ ≫ σ).hom.toAlgebra
  have hB : Module.Flat A B := hf
  have hπσ : ∀ z, π.hom (σ.hom z) = z := fun z => by
    rw [← CommRingCat.comp_apply, h, CommRingCat.id_apply]
  show Module.Flat A C
  let s : C →ₗ[A] B :=
    { toFun := σ.hom
      map_add' := map_add _
      map_smul' := fun a c => by
        simp only [Algebra.smul_def, RingHom.id_apply, map_mul, RingHom.algebraMap_toAlgebra,
          CommRingCat.hom_comp, RingHom.comp_apply] }
  let q : B →ₗ[A] C :=
    { toFun := π.hom
      map_add' := map_add _
      map_smul' := fun a c => by
        simp only [Algebra.smul_def, RingHom.id_apply, map_mul, RingHom.algebraMap_toAlgebra,
          CommRingCat.hom_comp, RingHom.comp_apply, hπσ] }
  exact Module.Flat.of_retract s q (LinearMap.ext fun z => hπσ z)

theorem flat_of_retract {X Y S : Scheme.{0}} (f : X ⟶ S) (i : X ⟶ Y) (r : Y ⟶ X) (h : i ≫ r = 𝟙 X)
    [Flat (r ≫ f)] : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  have hx : r (i x) = x := by
    rw [← Scheme.Hom.comp_apply, h]; rfl
  haveI : IsIso (i ≫ r) := by rw [h]; infer_instance
  haveI : IsOpenImmersion (i ≫ r) := inferInstance
  haveI : IsIso ((i ≫ r).stalkMap x) := inferInstance
  have key : (f.stalkMap (r (i x))).hom.Flat := by
    have e1 : r.stalkMap (i x) ≫ i.stalkMap x = (i ≫ r).stalkMap x := (Scheme.Hom.stalkMap_comp i r x).symm
    haveI hg : IsIso (r.stalkMap (i x) ≫ i.stalkMap x) := by rw [e1]; exact this
    have e2 : r.stalkMap (i x) ≫ (i.stalkMap x ≫ CategoryTheory.inv (r.stalkMap (i x) ≫ i.stalkMap x)) = 𝟙 _ := by
      rw [← Category.assoc, IsIso.hom_inv_id]
    refine ringHom_flat_of_retract (f.stalkMap (r (i x))) (r.stalkMap (i x)) _ e2 ?_
    · rw [← Scheme.Hom.stalkMap_comp]
      exact Flat.stalkMap (r ≫ f) (i x)
  rwa [hx] at key

open GlobalTheory.UPel.HT in

theorem oActN_natCast {S : Scheme.{0}} {O : Type} [Ring O] {G : Over S} [GrpObj G] (act : OActN O G) (n : ℕ) :
    act.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.1 h
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

open GlobalTheory.UPel.HT in

theorem act_finite_flat {S : Scheme.{0}} [IsLocallyNoetherian S] {F O : Type} [Field F] [NumberField F] [Ring O]
    [Algebra (𝓞 F) O] (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) (act : OActN O A)
    (c : 𝓞 F) (hc : c ≠ 0) :
    IsFinite (act.act (algebraMap (𝓞 F) O c)).left ∧ Flat (act.act (algebraMap (𝓞 F) O c)).left := by
  have he : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
  have hcomp : act.act (algebraMap (𝓞 F) O c) ≫ act.act (algebraMap (𝓞 F) O a) =
      𝟙 A ^ Ideal.absNorm (Ideal.span {c}) := by
    rw [← act.mul, ← map_mul, ha, map_natCast, oActN_natCast]
  obtain ⟨hfe, -⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul S A hA _ (Nat.one_le_iff_ne_zero.2 he)
  have hpr := hA.proper
  have hsm := hA.smooth
  haveI : IsSeparated ((act.act (algebraMap (𝓞 F) O a)).left ≫ A.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated (act.act (algebraMap (𝓞 F) O a)).left := IsSeparated.of_comp _ A.hom
  haveI : IsFinite ((act.act (algebraMap (𝓞 F) O c)).left ≫ (act.act (algebraMap (𝓞 F) O a)).left) := by
    rw [← Over.comp_left, hcomp]; exact hfe
  have hf : IsFinite (act.act (algebraMap (𝓞 F) O c)).left := IsFinite.of_comp _ (act.act (algebraMap (𝓞 F) O a)).left
  refine ⟨hf, GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres S A A _ inferInstance inferInstance hf fun K _ _ t => ?_⟩
  have hm := act.hom (algebraMap (𝓞 F) O c)
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    (Out.TLinPf.isAb_pullback t A hA) _ inferInstance
    (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hf)).1

open KerGrp in

theorem exists_torsion_finite_flat : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (w : Ideal (𝓞 D.F)) (S : Scheme.{0}) [IsLocallyNoetherian S]
    (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s), w ≠ ⊥ → ∃ (K : Over S) (_ : GrpObj K) (i : K ⟶ o.A),
      IsMonHom i ∧ Mono i ∧ IsFinite K.hom ∧ Flat K.hom ∧ ∀ (T : Over S) (x : T ⟶ o.A),
        GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) x := by
  intro p _ D R _ b N w S _ s o hw
  obtain ⟨α, x, hα0, -, -, hxx, hwx⟩ := exists_gen_idem w hw
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hxx
  have hA := o.ab
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O α)
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O x)
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O t)
  have comm : o.act.act (algebraMap (𝓞 D.F) D.O α) ≫ o.act.act (algebraMap (𝓞 D.F) D.O x) =
      o.act.act (algebraMap (𝓞 D.F) D.O x) ≫ o.act.act (algebraMap (𝓞 D.F) D.O α) := by
    rw [← o.act.mul, ← o.act.mul, ← map_mul, ← map_mul, mul_comm]
  have idem : o.act.act (algebraMap (𝓞 D.F) D.O x) ≫ o.act.act (algebraMap (𝓞 D.F) D.O x) =
      o.act.act (algebraMap (𝓞 D.F) D.O x) *
        (o.act.act (algebraMap (𝓞 D.F) D.O α) ≫ o.act.act (algebraMap (𝓞 D.F) D.O t)) := by
    rw [← o.act.mul, ← o.act.mul, ← o.act.add, ← map_mul, ← map_mul, ← map_add, ht]
    congr 2; ring

  set fα := o.act.act (algebraMap (𝓞 D.F) D.O α) with hfα
  set fx := o.act.act (algebraMap (𝓞 D.F) D.O x) with hfx
  set ft := o.act.act (algebraMap (𝓞 D.F) D.O t) with hft
  obtain ⟨hfinα, hflα⟩ := act_finite_flat o.A hA o.act α hα0
  letI gH : GrpObj (ker fα) := grp fα
  haveI : IsMonHom (pullback.fst fα η[o.A]) := isMonHom_fst fα
  have hPB := (IsPullback.of_hasPullback fα η[o.A]).map (Over.forget S)
  have hHfin : IsFinite (ker fα).hom := by
    rw [← Over.w (pullback.snd fα η[o.A])]
    haveI : IsFinite (pullback.snd fα η[o.A]).left := MorphismProperty.of_isPullback (P := @IsFinite) hPB hfinα
    exact inferInstanceAs (IsFinite (_ ≫ 𝟙 S))
  have hHflat : Flat (ker fα).hom := by
    rw [← Over.w (pullback.snd fα η[o.A])]
    haveI : Flat (pullback.snd fα η[o.A]).left := MorphismProperty.of_isPullback (P := @Flat) hPB hflα
    exact inferInstanceAs (Flat (_ ≫ 𝟙 S))

  set jH := pullback.fst fα η[o.A] with hjH
  have hj : jH ≫ fα = 1 := fst_comp fα
  let g : ker fα ⟶ ker fα := lift fα (jH ≫ fx) (by
    rw [Category.assoc, ← comm, ← Category.assoc, hj, MonObj.one_comp])
  have hg : g ≫ jH = jH ≫ fx := lift_fst _ _ _
  have hxx' : jH ≫ fx ≫ fx = jH ≫ fx := by
    rw [idem, MonObj.comp_mul, ← Category.assoc jH fα ft, hj, MonObj.one_comp, _root_.mul_one]
  letI gK : GrpObj (ker (jH ≫ fx)) := grp (jH ≫ fx)
  haveI : IsMonHom (pullback.fst (jH ≫ fx) η[o.A]) := isMonHom_fst (jH ≫ fx)
  set iK := pullback.fst (jH ≫ fx) η[o.A] with hiK
  have hk : iK ≫ jH ≫ fx = 1 := fst_comp (jH ≫ fx)
  have hrk : (𝟙 (ker fα) / g) ≫ jH ≫ fx = 1 := by
    rw [← Category.assoc, GrpObj.div_comp, Category.id_comp, hg, GrpObj.div_comp, Category.assoc, hxx',
      div_self']
  let r : ker fα ⟶ ker (jH ≫ fx) := lift (jH ≫ fx) (𝟙 (ker fα) / g) hrk
  have hr : r ≫ iK = 𝟙 (ker fα) / g := lift_fst _ _ _
  have hiKg : iK ≫ g = 1 := hom_ext fα (by
    rw [Category.assoc, hg, hk, MonObj.one_comp])
  have hir : iK ≫ r = 𝟙 _ := hom_ext (jH ≫ fx) (by
    rw [Category.assoc, hr, GrpObj.comp_div, Category.comp_id, hiKg, div_one, Category.id_comp])
  have hirl : iK.left ≫ r.left = 𝟙 _ := by rw [← Over.comp_left, hir, Over.id_left]

  have hKfin : IsFinite (ker (jH ≫ fx)).hom := by
    haveI : IsFinite (r.left ≫ (ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHfin
    haveI : IsSeparated (r.left ≫ (ker (jH ≫ fx)).hom) := by rw [Over.w r]; infer_instance
    haveI : IsSeparated r.left := IsSeparated.of_comp _ (ker (jH ≫ fx)).hom
    haveI : IsFinite (iK.left ≫ r.left) := by rw [hirl]; infer_instance
    haveI : IsFinite iK.left := IsFinite.of_comp _ r.left
    rw [← Over.w iK]; infer_instance
  have hKflat : Flat (ker (jH ≫ fx)).hom := by
    haveI : Flat (r.left ≫ (ker (jH ≫ fx)).hom) := by rw [Over.w r]; exact hHflat
    exact flat_of_retract _ iK.left r.left hirl
  refine ⟨ker (jH ≫ fx), gK, iK ≫ jH, inferInstance, inferInstance, hKfin, hKflat, fun T z => ?_⟩
  rw [hwx, Ideal.map_span, Set.image_pair, GlobalTheory.IwLevel.killedBy_span]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, GlobalTheory.IwLevel.htAct_act]
  refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
  · rintro ⟨y, rfl⟩
    refine ⟨?_, ?_⟩
    · show ((y ≫ iK) ≫ jH) ≫ fα = 1
      rw [Category.assoc, hj, MonObj.comp_one]
    · show ((y ≫ iK) ≫ jH) ≫ fx = 1
      rw [Category.assoc, Category.assoc, hk, MonObj.comp_one]
  · refine ⟨lift (jH ≫ fx) (lift fα z h1) (by rw [← Category.assoc, KerGrp.lift_fst, h2]), ?_⟩
    rw [← Category.assoc, KerGrp.lift_fst, KerGrp.lift_fst]

end GlobalTheory.IwLevel.HTTorsionFF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMeasureDensityExists
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder ENNReal

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {w ρ : AlgChart p σ 1 → CxPts p σ → ℝ}

theorem IsDens.setLIntegral_part [SecondCountableTopology (CxPts p σ)] (h : IsDens w)
    (c : AlgChart p σ 1) {A : Set (CxPts p σ)} (hA : MeasurableSet A) (hc : A ⊆ c.e.source)
    {f : CxPts p σ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in A, f y ∂(part w) =
      ∫⁻ v in c.e '' A, ENNReal.ofReal (w c (c.e.symm v)) * f (c.e.symm v) := by
  have hS := ChartGlue.measurableSet_image c.e hA hc
  have hSt : c.e '' A ⊆ c.e.target := (Set.image_mono hc).trans c.e.image_source_eq_target.subset
  have hsym : AEMeasurable c.e.symm (volume.restrict (c.e '' A)) :=
    (c.e.continuousOn_symm.mono hSt).aemeasurable hS
  have hφ : AEMeasurable (fun v => ENNReal.ofReal (w c (c.e.symm v)))
      (volume.restrict (c.e '' A)) :=
    (((h.2 c).mono hSt).aemeasurable hS).ennreal_ofReal
  have hsym' := hsym.mono_ac (withDensity_absolutelyContinuous (volume.restrict (c.e '' A))
    fun v => ENNReal.ofReal (w c (c.e.symm v)))
  have key : (part w).restrict A = Measure.map c.e.symm
      ((volume.restrict (c.e '' A)).withDensity fun v => ENNReal.ofReal (w c (c.e.symm v))) := by
    ext B hB
    rw [Measure.restrict_apply hB, h.part_apply c (hB.inter hA) (Set.inter_subset_right.trans hc),
      Measure.map_apply_of_aemeasurable hsym' hB, withDensity_apply',
      Measure.restrict_restrict' hS]
    congr 2
    ext v
    constructor
    · rintro ⟨y, ⟨hyB, hyA⟩, rfl⟩
      exact ⟨by rwa [Set.mem_preimage, c.e.left_inv (hc hyA)], ⟨y, hyA, rfl⟩⟩
    · rintro ⟨hv, ⟨y, hyA, rfl⟩⟩
      rw [Set.mem_preimage, c.e.left_inv (hc hyA)] at hv
      exact ⟨y, ⟨hv, hyA⟩, rfl⟩
  rw [key, lintegral_map' hf.aemeasurable hsym']
  exact lintegral_withDensity_eq_lintegral_mul₀ hφ (hf.comp_aemeasurable hsym)

theorem IsDens.isFiniteMeasure_part [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    [SecondCountableTopology (CxPts p σ)] (h : IsDens w)
    (cov : ∀ y, ∃ c : AlgChart p σ 1, y ∈ c.e.source) : IsFiniteMeasure (part w) := by
  have hfin : ∀ y, (part w).FiniteAtFilter (𝓝 y) := fun y => by
    obtain ⟨c, hy⟩ := cov y
    obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.1 c.e.open_target _ (c.e.map_source hy)
    set B := Metric.closedBall (c.e y) (ε / 2) with hBdef
    have hBt : B ⊆ c.e.target := (Metric.closedBall_subset_ball (by linarith)).trans hεt
    set T := c.e.symm '' B with hTdef
    have hTc : IsCompact T :=
      (isCompact_closedBall _ _).image_of_continuousOn (c.e.continuousOn_symm.mono hBt)
    have hTs : T ⊆ c.e.source := by
      rintro _ ⟨v, hv, rfl⟩; exact c.e.map_target (hBt hv)
    have hTB : c.e '' T = B := by
      rw [hTdef, Set.image_image]
      exact (Set.image_congr fun v hv => c.e.right_inv (hBt hv)).trans (Set.image_id' B)
    refine ⟨T, ?_, ?_⟩
    · refine mem_of_superset ((c.e.isOpen_inter_preimage Metric.isOpen_ball).mem_nhds
        ⟨hy, Metric.mem_ball_self (half_pos hε)⟩) fun z hz => ⟨c.e z, ?_, c.e.left_inv hz.1⟩
      exact Metric.ball_subset_closedBall hz.2
    · rw [h.part_apply c hTc.isClosed.measurableSet hTs, hTB]
      exact (((h.2 c).mono hBt).integrableOn_compact (isCompact_closedBall _ _)).lintegral_lt_top
  refine ⟨?_⟩
  simpa using isCompact_univ.measure_lt_top_of_nhdsWithin fun y _ =>
    (hfin y).filter_mono nhdsWithin_le_nhds

theorem IsDens.noAtoms_part [SecondCountableTopology (CxPts p σ)] [T2Space (CxPts p σ)]
    (h : IsDens w) (cov : ∀ y, ∃ c : AlgChart p σ 1, y ∈ c.e.source) : NoAtoms (part w) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨c, hy⟩ := cov y
  rw [h.part_apply c (measurableSet_singleton y) (Set.singleton_subset_iff.2 hy),
    Set.image_singleton]
  exact setLIntegral_measure_zero _ _ (measure_singleton _)

theorem IsDens.exists_quotient (hw : IsDens w) (hpos : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, 0 < w c y)
    (cov : ∀ y, ∃ c : AlgChart p σ 1, y ∈ c.e.source) (hρ : IsDens ρ) :
    ∃ g : CxPts p σ → ℝ, Continuous g ∧ ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source,
      ρ c y = g y * w c y := by
  choose pick hpick using cov
  have hval : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source,
      ρ c y = ρ (pick y) y / w (pick y) y * w c y := fun c y hy => by
    have hne := (hpos (pick y) y (hpick y)).ne'
    rw [hρ.1 c (pick y) y hy (hpick y), hw.1 c (pick y) y hy (hpick y)]
    field_simp
  refine ⟨fun y => ρ (pick y) y / w (pick y) y, continuous_iff_continuousAt.2 fun y => ?_, hval⟩
  have hcont : ∀ τ : AlgChart p σ 1 → CxPts p σ → ℝ, IsDens τ →
      ContinuousOn (τ (pick y)) (pick y).e.source := fun τ hτ =>
    ((hτ.2 (pick y)).comp (pick y).e.continuousOn (pick y).e.mapsTo).congr fun z hz => by
      simp [(pick y).e.left_inv hz]
  have ho := (pick y).e.open_source.mem_nhds (hpick y)
  refine (((hcont ρ hρ).continuousAt ho).div ((hcont w hw).continuousAt ho)
    (hpos _ y (hpick y)).ne').congr ?_
  filter_upwards [ho] with z hz
  rw [Pi.div_apply, hval (pick y) z hz, mul_div_assoc, div_self (hpos _ z hz).ne', mul_one]

theorem IsDens.part_eq_withDensity [SecondCountableTopology (CxPts p σ)] (hw : IsDens w)
    (hpos : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, 0 < w c y)
    (cov : ∀ y, ∃ c : AlgChart p σ 1, y ∈ c.e.source) {g : CxPts p σ → ℝ} (hg : Continuous g)
    (hρ : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = g y * w c y) :
    part ρ = (part w).withDensity fun y => ENNReal.ofReal (g y) := by
  have hd : IsDens ρ := (hw.mul hg).congr hρ
  refine ChartGlue.ext_of_cover (fun c : AlgChart p σ 1 => c.e.source) (fun c => c.e.open_source)
    cov fun c A hA hc => ?_
  rw [hd.part_apply c hA hc, withDensity_apply _ hA,
    hw.setLIntegral_part c hA hc hg.measurable.ennreal_ofReal]
  refine setLIntegral_congr_fun (ChartGlue.measurableSet_image c.e hA hc) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv (hc hy)]
  rw [hρ c y (hc hy), ENNReal.ofReal_mul' (hpos c y (hc hy)).le, mul_comm]

theorem IsDens.total_eq_integral [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)]
    [SecondCountableTopology (CxPts p σ)] (hw : IsDens w)
    (hpos : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, 0 < w c y)
    (cov : ∀ y, ∃ c : AlgChart p σ 1, y ∈ c.e.source) {g : CxPts p σ → ℝ} (hg : Continuous g)
    (hρ : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = g y * w c y) :
    total ρ = ∫ y, g y ∂(part w) := by
  haveI := hw.isFiniteMeasure_part cov
  have hI : Integrable g (part w) :=
    integrableOn_univ.1 (hg.continuousOn.integrableOn_compact isCompact_univ)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI, total,
    hw.part_eq_withDensity hpos cov hg hρ,
    hw.part_eq_withDensity (ρ := fun c y => -ρ c y) (g := fun y => -g y) hpos cov hg.neg
      fun c y hy => by rw [hρ c y hy, neg_mul],
    withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem exists_refMeasure : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)],
    Nonempty (AnRead p σ 1) → ∃ (ν : Measure (CxPts p σ)) (w : AlgChart p σ 1 → CxPts p σ → ℝ),
      IsFiniteMeasure ν ∧ NoAtoms ν ∧
      (∀ ρ : AlgChart p σ 1 → CxPts p σ → ℝ, IsDens ρ → ∃ g : CxPts p σ → ℝ, Continuous g ∧
        ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = g y * w c y) ∧
      ∀ (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) (g : CxPts p σ → ℝ), Continuous g →
        (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = g y * w c y) →
        part ρ = ν.withDensity (fun y => ENNReal.ofReal (g y)) ∧ total ρ = ∫ y, g y ∂ν := by
  intro k _ X p σ _ _ _ hR
  obtain ⟨w, hw, hpos⟩ := GlobalTheory.T.positive_density_exists k X p σ hR
  obtain ⟨R⟩ := hR
  have cov : ∀ y, ∃ c : AlgChart p σ 1, y ∈ c.e.source := fun y =>
    let ⟨i, hi⟩ := R.cover y
    ⟨R.chart i, hi⟩
  exact ⟨part w, w, hw.isFiniteMeasure_part cov, hw.noAtoms_part cov,
    fun ρ hρ => hw.exists_quotient hpos cov hρ, fun ρ g hg hρ =>
      ⟨hw.part_eq_withDensity hpos cov hg hρ, hw.total_eq_integral hpos cov hg hρ⟩⟩

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteFlatGeometricFibresOverBaseStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_finite_flat_geometric_fibres_over_base : ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom →
    LocallyOfFinitePresentation Y.hom → IsFinite f.left →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Flat ((Over.pullback t).map f).left) →
    Flat f.left := by
  first | (exact @GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over) | (exact GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over) | (intros; apply GlobalTheory.flat_of_isFinite_of_flat_geometric_fibres_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoefficientMapExtremalEqPhaseSmulLettersStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockCoefficientMap_extremal_eq_phase_smul_letters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → IoExt R → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∀ (lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank → FVar D (Wc D i).rank (Vc D i).rank), (∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (t : T0) (v : VsV D i O.c'.F), R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (O.c0' v)) = ka • pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (fun _ => 1) (onb (R.MW i (sg0 D A))) (R.vP i t) (MvPolynomial.rename lt (MvPolynomial.map (inC O.c') (O.io v))) := by
  first | exact @GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core | exact GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core | (intros; apply GlobalTheory.AdTh.PhaseMapCore.io_eq_phase_smul_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetsUnitVacuumEqScaledThetaJets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPos

theorem applyAt0_monomial' (D : D7) {N N' : ℕ} (k : Formalism.MainNotions.GL3Theta.Idx D N N' →₀ ℕ) (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G = (k.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G k := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl,
    one_mul]

theorem taylor_comp_smul' (D : D7) {N N' : ℕ} (G : Formalism.MainNotions.TaylorLogMetric.VC D N N' → ℂ) (hG : Differentiable ℂ G) (a : ℂ) (α : Formalism.MainNotions.TaylorLogMetric.Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => G (a • z)) α = a ^ (α.sum fun _ n => n) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  unfold Formalism.MainNotions.TaylorLogMetric.taylor
  have key := iteratedFDeriv_comp_const_smul (𝕜 := ℂ) (i := Multiset.card (Finsupp.toMultiset α)) (f := G) a ((ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_diff hG).of_le (by exact_mod_cast le_top))
  rw [key]
  simp only [smul_zero, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]
  congr 2
  exact Finsupp.card_toMultiset α

theorem fock_jets_eq_theta : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ f, IsVacO ψ θ S T sS sT (colLat frS : Set _) (colLat frT : Set _) f → ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank) ∧ Θ ≠ 0 ∧ ∀ k : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T sS sT (fun τ => frS.1.map (tauE D τ)) (fun τ => frT.1.map (tauE D τ)) f (MvPolynomial.monomial k 1) 0 = (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ := by
  intro D ψ θ S T sS sT frS frT hS hT hcS hcT δ hC hδ f hf
  have hsS := cart_one frS hS hcS
  have hsT := cart_one frT hT hcT
  subst hsS hsT
  obtain ⟨Φ, hΦd, hreal⟩ := GlobalTheory.T.fockVacuum_real_restriction_gaussian_entire ψ θ S T frS frT _ _ hS hT f hf
  have hTh := GlobalTheory.T.unit_vacuum_entire_factor_isThetaFunction_standard ψ θ S T frS frT hS hT δ hC hδ f hf Φ hΦd hreal
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Θ = fun Y => Φ (δ⁻¹ • Y) := ⟨_, rfl⟩
  rw [← hΘ] at hTh
  have hΦeq : Φ = fun z => Θ (δ • z) := by
    funext z
    simp only [hΘ, smul_smul, inv_mul_cancel₀ hδ, one_smul]
  refine ⟨Θ, hTh, ?_, fun k => ?_⟩
  · intro h0
    obtain ⟨w, hw, hfw⟩ := GlobalTheory.T.exists_finitePartZero_ne_of_isVacuum_orientedModel ψ θ S T _ _ _ _ f hf
    apply hfw
    have h1 : Φ (zCo θ frS frT w) = 0 := by
      rw [hΦeq]
      exact congrFun h0 _
    rw [hreal w hw, h1, mul_zero]
  · have hdiff : Differentiable ℂ Θ := hTh.1
    have hj := GlobalTheory.T.fockMonomial_at_origin_gaussian_entire_orthonormal ψ θ S T frS frT hf.1 hf.2.inf hS hT f Φ hΦd hreal k
    change pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.FockPos.frAt frS) (GlobalTheory.FockPos.frAt frT) f (MvPolynomial.monomial k 1) 0 = _
    rw [hj, hΦeq, applyAt0_monomial', applyAt0_monomial', taylor_comp_smul' D _ hdiff]
    have hper : ∀ τ : D.what₂.Tau, GlobalTheory.FunObj.period δ τ = δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹) := by
      intro τ
      rw [GlobalTheory.FunObj.period, GlobalTheory.AdTh.Fock.norm_embedding_hostFormConstant_eq, div_eq_mul_inv]
    have hprod : (k.prod fun v n => GlobalTheory.FunObj.period δ v.1 ^ n) =
        (δ * (((Real.sqrt (2 * Real.pi * Formalism.L2.Pj.xiR D) : ℝ) : ℂ)⁻¹)) ^ (k.sum fun _ n => n) := by
      simp only [hper, Finsupp.prod, Finsupp.sum]
      exact Finset.prod_pow_eq_pow_sum _ _ _
    rw [hprod, mul_pow]
    ring

end GlobalTheory.FockPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaSpanFiniteDimensionalDualPairStatement
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_span_finiteDimensional_dualPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → FiniteDimensional ℂ (GlobalTheory.FockKFin.vacSp M B.emb) := by
  first | exact @GlobalTheory.FockKFin.vacSp_finiteDimensional | exact GlobalTheory.FockKFin.vacSp_finiteDimensional | (intros; apply GlobalTheory.FockKFin.vacSp_finiteDimensional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTraceSeparatingElementStatement
section
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_trace_separating_element : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (C : Type) [Field C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∃ δ : C, δ ≠ 0 ∧ ∀ φ : E →+* C, (∃ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E), ∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then δ else 0) ∧ ∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v δ := by
  first | exact @GlobalTheory.InvDifferentArith.indicator_inverseDifferent | exact GlobalTheory.InvDifferentArith.indicator_inverseDifferent | (intros; apply GlobalTheory.InvDifferentArith.indicator_inverseDifferent <;> assumption)
end

