import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Statements.HeckeInFamilies.GenericMemChart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelDescentCoefficientField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevelMapField

private theorem KA_mono_of_A_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l₀ l : Level H} (h : l₀.A ∣ l.A) : KA l₀ ≤ KA l := by
  unfold KA
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rcases hx with rfl | rfl
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [GlobalTheory.LevelCover.zeta_dvd l.A_pos h]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (by simp)) _

private theorem M'_dvd_of_level_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {l₀ l : Level H} (h : l₀.Dvd l) : l₀.M' ∣ l.M' := by
  unfold Level.Dvd at h
  unfold Level.M'
  exact Nat.lcm_dvd (h.1.trans (Nat.dvd_lcm_left _ _)) (h.2.2.trans (Nat.dvd_lcm_right _ _))

private theorem M'_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (l : Level H) : 0 < l.M' := by
  unfold Level.M'
  have h3 := l.three_le
  exact Nat.lcm_pos (by omega) l.A_pos

theorem exists_levelMap : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l), ToroidalLevelCompatibility (H := H) (D := D) → ∀ (l₀ l : Level H) (c : Coeff l) (o : Obj D l (baseKA l) (pullback.fst (Xo l).s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ (Xo l).s)) (_ : ObjMap o (Xo l).univ (pullback.fst _ _)), l₀.Dvd l → ∃ (k : KA l₀ →+* c.F) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap o.t (Xo l₀).univ.t r) (hr : r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k), IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k ∧ LevComp o (Xo l₀).univ r ν ∧ IsFinite (pullback.lift r _ hr) ∧ Etale (pullback.lift r _ hr) ∧ Surjective (pullback.lift r _ hr) := by
  intro _ _ _ E _ _ _ H D Xo hN l₀ l c o mo hd
  have hA : l₀.A ∣ l.A := by
    unfold Level.Dvd at hd
    exact hd.2.2
  have hle : KA l₀ ≤ c.F := (KA_mono_of_A_dvd hA).trans c.le
  have hz : zeta l₀.M' ∈ c.F := by
    rw [GlobalTheory.LevelCover.zeta_dvd (M'_pos' l) (M'_dvd_of_level_dvd hd)]
    exact pow_mem c.zeta_mem _
  obtain ⟨r₀, -, m, -, -, hm1, hm2, -, hF⟩ := hN l₀ l (Xo l₀) (Xo l) hd
  obtain ⟨rF, h1, h2, hfin, het, hsurj, -⟩ := hF ⟨c.F, c.fin, c.conj, hz, hle⟩ c rfl
  have hid : spMap (IntermediateField.inclusion (le_refl c.F)).toRingHom = 𝟙 (Sp c.F) :=
    GlobalTheory.LevelCover.spMap_inclusion_self _
  have hr : (rF ≫ pullback.fst _ _) ≫ (Xo l₀).s =
      pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h2]
    erw [hid, Category.comp_id]
  have hlift : pullback.lift (rF ≫ pullback.fst _ _) (pullback.snd _ _) hr = rF := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd, h2]
      erw [hid, Category.comp_id]
  obtain ⟨ν, hν⟩ := GlobalTheory.LevelCover.sab_comp mo.toSABMap m (e := rF ≫ pullback.fst _ _) h1.symm
  refine ⟨(IntermediateField.inclusion hle).toRingHom, rF ≫ pullback.fst _ _, ν, hr,
    fun x => rfl, ?_, ?_, ?_, ?_⟩
  · unfold LevComp
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hν, ← Category.assoc,
        GlobalTheory.LevelCover.sec_pow mo.toSABMap (o.eta a) ((Xo l).univ.eta a) (mo.eta a),
        Category.assoc, hm1 a, ← Category.assoc, ← h1]
    · rw [hν, ← Category.assoc,
        GlobalTheory.LevelCover.sec_pow mo.toSABMap (o.etaA a) ((Xo l).univ.etaA a) (mo.etaA a),
        Category.assoc, hm2 a, ← Category.assoc, ← h1]
  · rw [hlift]; exact hfin
  · rw [hlift]; exact het
  · rw [hlift]; exact hsurj

end GlobalTheory.LevelMapField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleGenericFibreSpreadsOut
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericLB

theorem algHom_eq_val {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Subalgebra R K) (u : S →ₐ[R] K) (x : S) : u x = x := by
  obtain ⟨⟨a, b⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) (x : K)
  have hb : algebraMap R K (b : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hS : x * algebraMap R S (b : R) = algebraMap R S a := by
    apply Subtype.ext
    simpa using hx
  have hu : u x * algebraMap R K (b : R) = algebraMap R K a := by
    simpa only [map_mul, AlgHom.commutes] using congrArg u hS
  exact mul_right_cancel₀ hb (hu.trans hx.symm)

theorem mono_fst_localization {R : Type} [CommRing R] (M : Submonoid R) (A : Type) [CommRing A] [Algebra R A]
    [IsLocalization M A] {B : Scheme.{0}} (pB : B ⟶ Sp R) :
    Mono (pullback.fst pB (spMap (algebraMap R A))) := by
  haveI hepi : Epi (CommRingCat.ofHom (algebraMap R A)) :=
    ⟨fun g h e => CommRingCat.hom_ext (IsLocalization.ringHom_ext M (by
      simpa using congrArg CommRingCat.Hom.hom e))⟩
  haveI hsp : Mono (spMap (algebraMap R A)) :=
    (inferInstance : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R A)).op))
  infer_instance

end GenericLB

theorem lb_generic_spreads_out : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B : Scheme.{0}) (pB : B ⟶ Sp R) (M : LB (pullback pB (spMap (algebraMap R K)))), QuasiCompact pB → QuasiSeparated pB → M.IsLB → ∃ (f : R) (_ : f ≠ 0) (M' : LB (pullback pB (spMap (algebraMap R (Localization.Away f))))), M'.IsLB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → LBIso M (M'.pull j) := by
  intro R K _ _ _ _ _ _ B pB M hqc hqs hM
  classical
  haveI := hqc
  haveI := hqs
  obtain ⟨s, M₀, hM₀, -, hfac⟩ := LBLimit.exists_lb_of_isLimit (Spread.bcDiagram pB K)
    (fun i => (Spread.bcCone pB K).π.app i) (fun g => (Spread.bcCone pB K).w g)
    (Spread.isLimitBcCone pB K) M hM
  obtain ⟨f, hf0, hlift⟩ := GenericLB.exists_denom (R := R) (K := K) s.unop
  obtain ⟨ψ, hψ⟩ := hlift (Localization.Away f) (algebraMap R (Localization.Away f))
    (IsLocalization.Away.algebraMap_isUnit f)
  let ψa : Algebra.adjoin R (s.unop : Set K) →ₐ[R] Localization.Away f :=
    { ψ with commutes' := fun r => RingHom.congr_fun hψ r }
  refine ⟨f, hf0, M₀.pull (Spread.bcMap pB ψa), pull_isLB hM₀ _, fun jm hjm => ?_⟩
  have hfK : IsUnit (algebraMap R K f) :=
    isUnit_iff_ne_zero.mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hf0))
  let χ : Localization.Away f →ₐ[R] K :=
    { IsLocalization.Away.lift f hfK with
      commutes' := fun r => IsLocalization.lift_eq _ r }
  haveI := GenericLB.mono_fst_localization (Submonoid.powers f) (Localization.Away f) pB
  have hj : jm = Spread.bcMap pB χ := by
    rw [← cancel_mono (pullback.fst pB (spMap (algebraMap R (Localization.Away f)))), hjm,
      Spread.bcMap_fst]
  have hcomp : jm ≫ Spread.bcMap pB ψa = (Spread.bcCone pB K).π.app s := by
    rw [hj, Spread.bcMap_comp]
    show _ = Spread.bcMap pB (Algebra.adjoin R (s.unop : Set K)).val
    congr 1
    exact AlgHom.ext fun x => GenericLB.algHom_eq_val _ _ x
  exact hfac _ jm (Spread.bcMap pB ψa) hcomp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocallyQuasiFiniteOfTrivialOnFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.AmpleFibre

open TopologicalSpace GlobalTheory.MulFinite

theorem exists_fn {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (N : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1))) (r : Z ⟶ X)
    (t : (L.pull r).Gen) (ht : t.IsGen) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ Out.nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => r ⁻¹ᵁ L.U j
  have l₁ : ∀ j, V j ≤ r ⁻¹ᵁ LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  have l₂ : ∀ j, V j ≤ LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j)) *
        ((gm (𝟙 Z) z (LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j)) (t.s (fun _ => j)))⁻¹).val ^ N := by
    refine ⟨fun j => (r.appLE _ _ (l₁ j)).hom (s.f (fun _ => j)) *
      (Z.presheaf.map (homOfLE (l₂ j)).op).hom ((t.s (fun _ => j))⁻¹).val ^ N, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) (gs_appLE r z _ _ _ hz _)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))
    refine congrArg (· ^ N) ((gs_res (𝟙 Z) z _ hz _).trans ?_)
    exact (gs_unit (𝟙 Z) z _ (l₂ j hz) _).trans (congrArg Units.val (map_inv _ _))
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart hL (r z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_trans s r z (l₁ j hz.1) (l₁ j' hz.2),
        gen_trans ht (𝟙 Z) z (l₂ j hz.1) (l₂ j' hz.2)]
      have t₁ : trF (L := L) (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1) r z (fun _ => j) (fun _ => j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') ^ N := by simp [trF]
      have t₂ : trF (L := L) (K := PUnit) (fun _ => r) (fun _ => 1) (𝟙 Z) z (fun _ => j) (fun _ => j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') := by simp [trF]
      rw [t₁, t₂]
      simpa only [pow_one] using pow_aux _ _ _ 1 N)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := exists_chart hL (r z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔
      IsUnit (gs r z (LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j))) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨fun _ => j, (isUnit_gs r z _ (l₁ j hj) _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ Out.nonzeroLocus s from h)
    have hk' : r z ∈ LB.wchart L (K := Fin N) (fun _ => 𝟙 X) k := X.basicOpen_le _ hk
    rw [sec_trans s r z (l₁ j hj) hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isAffineHom_of_field {k : Type} [Field k] {Y : Scheme.{0}} (y : Sp k ⟶ Y) : IsAffineHom y := by
  refine ⟨fun U _ => ?_⟩
  have : Subsingleton ↥(Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  by_cases h : ∃ p, p ∈ y ⁻¹ᵁ U
  · obtain ⟨p, hp⟩ := h
    have : y ⁻¹ᵁ U = ⊤ := top_unique fun x _ => by rwa [Subsingleton.elim x p]
    rw [this]; exact isAffineOpen_top _
  · have : y ⁻¹ᵁ U = ⊥ := bot_unique fun x hx => (h ⟨x, hx⟩).elim
    rw [this]; exact isAffineOpen_bot _

theorem exists_integral_closedImmersion {P : Scheme.{0}} (Z : Set P) (hc : IsClosed Z)
    (hi : IsIrreducible Z) :
    ∃ (C : Scheme.{0}) (_ : IsIntegral C) (i : C ⟶ P), IsClosedImmersion i ∧ Set.range i = Z := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := P) ⟨Z, hc⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace I.subscheme := by
    have e := I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
    have : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [hr]; exact Subtype.irreducibleSpace hi
    exact e.irreducibleSpace_iff.2 this
  exact ⟨I.subscheme, isIntegral_of_irreducibleSpace_of_isReduced _, I.subschemeι, inferInstance, hr⟩

theorem locallyQuasiFinite_of_trivial_on_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (A : LB X), IsProper f → A.IsLB → (∀ x : X, ∃ (d : ℕ) (s : LB.Sec (LB.LinComb A (K := Fin d) (fun _ => 𝟙 X) (fun _ => 1))), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (C : Scheme.{0}) [IsIntegral C] (i : C ⟶ pullback f y), IsFinite i → ∃ t : (A.pull (i ≫ pullback.fst f y)).Gen, t.IsGen) → LocallyQuasiFinite f := by
  intro X Y f A hf hA hs ht
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  let Ω := AlgebraicClosure (Y.residueField y)
  let y' : Sp Ω ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y
  have hy : y ∈ Set.range y' := by
    obtain ⟨z⟩ : Nonempty ↥(Spec (.of Ω)) := inferInstance
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩
  clear_value y'
  have hy' := isAffineHom_of_field y'
  have h₁ : IsAffineHom (pullback.fst f y') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback f y').flip hy'
  have h₂ : IsLocallyNoetherian (pullback f y') :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f y')
  have h₃ : CompactSpace ↥(pullback f y') := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f y')
  have h₄ : IsNoetherian (pullback f y') := {}
  have hP : (Set.univ : Set ↥(pullback f y')).Finite := by
    rw [← sUnion_irreducibleComponents]
    refine NoetherianSpace.finite_irreducibleComponents.sUnion fun Z hZ => ?_
    obtain ⟨C, _, i, hi, rfl⟩ := exists_integral_closedImmersion Z
      (isClosed_of_mem_irreducibleComponents Z hZ) hZ.1
    obtain ⟨t, ht⟩ := ht Ω y' C i inferInstance
    choose d s hx ha using hs
    choose a ha' using fun x => exists_fn A hA (d x) (s x) _ t ht
    have : LocallyQuasiFinite (i ≫ pullback.snd f y') := by
      refine locallyQuasiFinite_of_cover (K := Ω) _ a (top_unique fun c _ => ?_) fun x => ?_
      · refine Opens.mem_iSup.2 ⟨(i ≫ pullback.fst f y') c, ?_⟩
        rw [ha']
        exact hx _
      · rw [ha']
        exact (ha x).preimage _
    have : Subsingleton ↥(Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    obtain ⟨p⟩ : Nonempty ↥(Sp Ω) := inferInstance
    have hC : Finite C := Set.finite_univ_iff.1
      (((i ≫ pullback.snd f y').finite_preimage_singleton p).subset fun c _ => Subsingleton.elim _ _)
    exact Set.finite_range i
  have := Set.finite_univ_iff.1 hP
  refine (Set.finite_range (pullback.fst f y')).subset ?_
  rw [Scheme.Pullback.range_fst]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hy)

end GlobalTheory.AmpleFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevUniq

theorem exists_sab_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem map_to_univ_unique : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l₀ l : Level H) (Xo : Moduli D l₀) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (r r' : S ⟶ Xo.X) (ν : SABMap o.t Xo.univ.t r) (ν' : SABMap o.t Xo.univ.t r'), IsReduced S → r ≫ Xo.s = r' ≫ Xo.s → LevComp o Xo.univ r ν → LevComp o Xo.univ r' ν' → r = r' ∧ ν.φ = ν'.φ := by
  intro hL _ _ E _ _ _ H D l₀ l Xo B _ b S s o r r' ν ν' hS hs hν hν'
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l₀ (KA l₀) (KA l₀) (baseKA l₀) (baseKA l₀) (RingHom.id _) Xo.X S Xo.s
    (r ≫ Xo.s) r rfl rfl (by
      rw [show spMap (RingHom.id (KA l₀)) = 𝟙 (Sp (KA l₀)) from Spec.map_id _, Category.comp_id]) Xo.univ
  obtain ⟨n₁, hn₁⟩ := exists_sab_cast m₁.toSABMap (Category.id_comp r).symm
  obtain ⟨k, hk⟩ := ObjMaps.exists_sab_cancel ν n₁
  have hk' : m₁.toSABMap.φ = k.φ ≫ ν.φ := hn₁.symm.trans hk
  have pk : IsPullback k.φ o₁.t.G.hom o.t.G.hom (𝟙 S) := k.cart.1
  have pν : IsPullback ν.φ o.t.G.hom Xo.univ.t.G.hom r := ν.cart.1
  have key : ∀ (x : 𝟙_ (Over S) ⟶ o₁.t.G) (y : 𝟙_ (Over S) ⟶ o.t.G),
      x.left ≫ m₁.toSABMap.φ = y.left ≫ ν.φ → x.left ≫ k.φ = y.left := by
    intro x y h
    refine pν.hom_ext ?_ ?_
    · rw [Category.assoc, ← hk', h]
    · rw [Category.assoc, pk.w, Category.comp_id, Over.w x, Over.w y]
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp ν' k
  obtain ⟨n₃, hn₃⟩ := exists_sab_cast n₂ (Category.id_comp r')
  have h₃ : n₃.φ = k.φ ≫ ν'.φ := hn₃.trans hn₂
  have e₁ : ∀ a, (o₁.eta a).left ≫ n₃.φ = r' ≫ (Xo.univ.eta a).left := by
    intro a
    rw [h₃, ← Category.assoc, key _ _ ((m₁.eta a).trans (hν.1 a).symm), hν'.1 a]
  have e₂ : ∀ a, (o₁.etaA a).left ≫ n₃.φ = r' ≫ (Xo.univ.etaA a).left := by
    intro a
    rw [h₃, ← Category.assoc, key _ _ ((m₁.etaA a).trans (hν.2 a).symm), hν'.2 a]
  have hr : r = r' := (Xo.rep S (r ≫ Xo.s) hS o₁).unique ⟨rfl, ⟨m₁⟩⟩ ⟨hs.symm, ⟨⟨n₃, e₁, e₂⟩⟩⟩
  subst hr
  refine ⟨rfl, ?_⟩
  have hφ : m₁.toSABMap.φ = n₃.φ :=
    obj_rigid_closed hL E H D l₀ (KA l₀) (KA l₀) (baseKA l₀) (baseKA l₀) Xo.X S Xo.s (r ≫ Xo.s) Xo.univ o₁ r
      (Or.inl hS) m₁.toSABMap n₃ (fun a => ⟨_, m₁.eta a, e₁ a⟩)
  have : IsIso k.φ := pk.isIso_fst_of_isIso
  rw [← cancel_epi k.φ, ← hk', ← h₃, hφ]

end GlobalTheory.LevUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MonoOfUnramifiedOfPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.ModuliEmbed

theorem mono_of_unramified_of_points {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f]
    (h : ∀ (k : Type) [Field k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y') : Mono f := by
  have hs : Surjective (pullback.diagonal f) := by
    exact ((tfae_universallyInjective f).out 1 3).1 fun (k : Type) [Field k] y y' e => h k y y' e
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem objMap_of_comp_eq {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S T Z : Scheme.{0}} {s : S ⟶ Sp B} {s' : T ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {t : SAB H Z}
    {f : S ⟶ Z} (ν : SABMap o.t t f) {u uA : D.La → (𝟙_ (Over Z) ⟶ t.G)}
    (h₁ : ∀ x, (o.eta x).left ≫ ν.φ = f ≫ (u x).left) (h₂ : ∀ x, (o.etaA x).left ≫ ν.φ = f ≫ (uA x).left)
    {y y' : T ⟶ S} (e : y ≫ f = y' ≫ f) (m : ObjMap o' o y) : Nonempty (ObjMap o' o y') := by
  have hn : ∃ n : SABMap o'.t t (y' ≫ f), n.φ = m.toSABMap.φ ≫ ν.φ := by
    rw [← e]; exact ObjMaps.exists_sab_comp ν m.toSABMap
  obtain ⟨n, hn⟩ := hn
  obtain ⟨m', hm'⟩ := ObjMaps.exists_sab_cancel ν n
  have k : m'.cm.F ≫ ν.cm.F = m.cm.F ≫ ν.cm.F := hm'.symm.trans hn
  exact ⟨⟨m', fun a => ObjComp.sec_cancel ν.cart.1 m'.cart.1.w (Over.w (o.eta a)) (Over.w (o'.eta a)) (h₁ a)
      (by rw [k, ← e]; exact ObjComp.sec_comp (h₁ a) (m.eta a)),
    fun a => ObjComp.sec_cancel ν.cart.1 m'.cart.1.w (Over.w (o.etaA a)) (Over.w (o'.etaA a)) (h₂ a)
      (by rw [k, ← e]; exact ObjComp.sec_comp (h₂ a) (m.etaA a))⟩⟩

end GlobalTheory.ModuliEmbed

namespace GlobalTheory

theorem moduli_isClosedImmersion : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (o : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s)) (_ : ObjMap o Xo.univ (pullback.fst _ _)) (Z : Scheme.{0}) (sZ : Z ⟶ Sp c.F) (t : SAB H Z) (f : Xo.XF c ⟶ Z) (ν : SABMap o.t t f) (η' ηA : D.La → (𝟙_ (Over Z) ⟶ t.G)), f ≫ sZ = pullback.snd _ _ → (∀ x, (o.eta x).left ≫ ν.φ = f ≫ (η' x).left) → (∀ x, (o.etaA x).left ≫ ν.φ = f ≫ (ηA x).left) → IsFinite f → IsClosedImmersion f := by
  intro _ _ _ E _ _ _ H D l Xo c o m0 Z sZ t f ν u uA hf h₁ h₂ hfin
  have key : ∀ (T : Scheme.{0}) (y y' : T ⟶ Xo.XF c), y ≫ f = y' ≫ f →
      y ≫ pullback.snd _ _ = y' ≫ pullback.snd _ _ ∧
      ∃ o' : Obj D l (baseKA l) ((y ≫ pullback.fst _ _) ≫ Xo.s),
        Nonempty (ObjMap o' Xo.univ (y ≫ pullback.fst _ _)) ∧
        Nonempty (ObjMap o' Xo.univ (y' ≫ pullback.fst _ _)) := by
    intro T y y' e
    refine ⟨by rw [← hf, ← Category.assoc, e, Category.assoc], ?_⟩
    obtain ⟨o', ⟨m⟩⟩ := obj_pull E H D l (KA l) (KA l) (baseKA l) (baseKA l) (RingHom.id _) _ T _
      ((y ≫ pullback.fst _ _) ≫ Xo.s) y rfl rfl
      ((Category.assoc _ _ _).symm.trans ((Category.comp_id _).symm.trans
        (congrArg (((y ≫ pullback.fst _ _) ≫ Xo.s) ≫ ·) (Spec.map_id _).symm))) o
    obtain ⟨m'⟩ := ModuliEmbed.objMap_of_comp_eq ν h₁ h₂ e m
    exact ⟨o', ⟨(ObjComp.objMap_comp m0 m).choose⟩, ⟨(ObjComp.objMap_comp m0 m').choose⟩⟩
  have hu : FormallyUnramified f := by
    refine TangentCrit.formallyUnramified_of_tangent f fun k _ _ w hw => ?_
    obtain ⟨e, o', m, m'⟩ := key _ w (constPt w) (hw.trans (by simp only [constPt, Category.assoc]))
    refine pullback.hom_ext ?_ e
    have e' : constPt w ≫ pullback.fst _ _ = constPt (w ≫ pullback.fst _ _) := by
      simp only [constPt, Category.assoc]
    rw [e'] at m'
    exact (Xo.unram k _ o' m m').trans e'.symm
  have hm : Mono f := by
    refine ModuliEmbed.mono_of_unramified_of_points f fun k _ y y' e => ?_
    obtain ⟨e₂, o', m, m'⟩ := key _ y y' e
    refine pullback.hom_ext ?_ e₂
    refine (Xo.rep _ _ inferInstance o').unique ⟨rfl, m⟩ ⟨?_, m'⟩
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← e₂, Category.assoc]
  exact (IsClosedImmersion.iff_isFinite_and_mono f).2 ⟨hfin, hm⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.PushInv

theorem pushInvertible_of_model : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B F O : Type) [CommRing B] [Field F] [CommRing O] (b : Base l B) (U : Scheme.{0}) (s : U ⟶ Sp B) (o : Obj D l b s) (c : U ⟶ Sp F) (β : O →+* F) (C : Cpt c o.t β), IsDedFrac β → HasTheta C.t.G C.t.PP.L → PushInvertible C.t.G C.t.PP.L := by
  intro hL hL2 hL3 E _ _ _ H D l B F O _ _ _ b U s o c β C hβ hθ
  have hS : Out.SecBaseChangeAnySt := by cases hL; cases hL2; cases hL3; assumption
  have hH : Out.GlobalSectionsRankAlgClosed := by cases hL; cases hL2; cases hL3; assumption
  obtain ⟨⟨hDom, hDed⟩, -, hFr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  obtain ⟨hN, -, -, hPre, hFl, hDo, hQC⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hPB : IsPullback C.m.φ o.t.G.hom C.t.G.hom (C.jQ ≫ pullback.fst C.s (spMap β)) := C.m.cart.1
  obtain ⟨w, hw, -⟩ := C.m.lin
  have hIso : LBIso o.t.PP.L (C.t.PP.L.pull C.m.φ) := ⟨w, hw⟩
  have hSm : Smooth C.t.G.hom := by
    have sa := C.t.semi
    first | infer_instance | exact sa.1 | (cases sa; assumption)
  have hGI : GeometricallyIntegral C.t.G.hom := by
    have sa := C.t.semi
    have _ := hSm
    have _ : GeometricallyConnected C.t.G.hom := by
      first | infer_instance | (cases sa; assumption)
    exact GlobalTheory.grpObj_geometricallyIntegral_of_smooth C.X C.t.G
  exact @GlobalTheory.PushInv.pushInvertible_of_densePart C.X U hN (C.jQ ≫ pullback.fst C.s (spMap β)) C.normal hPre hFl hDo hQC
    C.t.G o.t.G C.m.φ C.t.PP.L o.t.PP.L hSm hGI hPB C.t.PP.isLB o.t.PP.isLB hIso
    (GlobalTheory.PushInv.pushInvertible_any hS hH U (GlobalTheory.Obj.toPolAV o)) hθ

end GlobalTheory.PushInv
end

