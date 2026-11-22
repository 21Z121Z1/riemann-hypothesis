import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixOrderActionOnPower
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.MatrixRosati

theorem oneGen_isGen {X Y : Scheme.{0}} (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := fun _ _ =>
  (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm

theorem rosatiAdj_one {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left)
    (hL : L.IsLB) : RosatiAdj A L 1 1 := by
  intro s
  refine ⟨⊤, trivial, ?_⟩
  let W : (A ⊗ A).left.Opens := (A ⊗ A).hom ⁻¹ᵁ ⊤
  let T : Over S := Over.mk (W.ι ≫ (A ⊗ A).hom)
  let ρ : T ⟶ A ⊗ A := Over.homMk W.ι rfl
  obtain ⟨x, y, hxy⟩ : ∃ x y : T ⟶ A, (lift x y).left = W.ι :=
    ⟨ρ ≫ fst A A, ρ ≫ snd A A, congrArg (fun q => q.left) (lift_comp_fst_snd ρ)⟩
  obtain ⟨u, hu, -⟩ := exists_gen hL (φ' := fun i => W.ι ≫ rosatiφ A 1 1 i) (ε' := rosatiε)
    (fun V _ k => by
      refine Eq.trans ?_ ((prod_ros 1 1 x y k).symm.trans
        (Finset.prod_congr rfl fun i _ => by rw [hxy]))
      rw [MonObj.comp_one, MonObj.comp_one, _root_.one_mul, _root_.mul_one]
      simp [mul_comm, mul_left_comm])
    (LB.oneGen L (Y := W)) (oneGen_isGen _)
  exact ⟨u, hu⟩

theorem rosatiAdj_prod {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A)
    (c : CubicalStr A L) {κ : Type} (s : Finset κ) (f g : κ → (A ⟶ A))
    (h : ∀ k ∈ s, RosatiAdj A L.L (f k) (g k)) :
    RosatiAdj A L.L (∏ k ∈ s, f k) (∏ k ∈ s, g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rosatiAdj_one A L.L L.isLB
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact GlobalTheory.rosatiAdj_mul S A L c _ _ _ _ (h i (Finset.mem_insert_self _ _))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem exists_matrix_oAct : ∀ (S : Scheme.{0}) (P P' : PolAV S) (j : ℕ) (p : IsPowGrp P'.A P.A j) (w : LB.Iso P'.L (boxLB P.L p.pr)), w.IsGen → ∀ (L' : RigLB P'.A), L'.L = P'.L → Nonempty (CubicalStr P'.A L') → ∀ (O : Type) [Ring O] [StarRing O] (ιA : P.OAct O), ∃ ι' : P'.OAct (Matrix (Fin j) (Fin j) O), (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ι'.act m ≫ p.pr i = ∏ l, p.pr l ≫ ιA.act (m i l)) := by
  intro S P P' j p w hw L' hL' ⟨c⟩ O _ _ ιA
  obtain ⟨ρ, hρ⟩ := GlobalTheory.MatrixAction.exists_matrix_ringAct S P.A P'.A j p O ιA.toRingAct
  have hs : ∀ (i l : Fin j) (a : O) (s : Fin j), ρ.act (Matrix.single i l a) ≫ p.pr s
      = if s = i then p.pr l ≫ ιA.act a else 1 := by
    intro i l a s
    rw [hρ]
    split_ifs with h
    · subst h
      rw [Finset.prod_eq_single l]
      · rw [Matrix.single_apply_same]
      · intro t _ ht
        rw [Matrix.single_apply_of_col_ne _ _ ht.symm, GlobalTheory.MatrixAction.act_zero, MonObj.comp_one]
      · intro h
        exact absurd (Finset.mem_univ l) h
    · refine Finset.prod_eq_one fun t _ => ?_
      rw [Matrix.single_apply_of_row_ne (Ne.symm h), GlobalTheory.MatrixAction.act_zero, MonObj.comp_one]
  refine ⟨⟨ρ, fun m => ?_⟩, hρ⟩
  have e1 : m = ∑ k : Fin j × Fin j, Matrix.single k.1 k.2 (m k.1 k.2) := by
    rw [Fintype.sum_prod_type]
    exact Matrix.matrix_eq_sum_single m
  have e2 : star m = ∑ k : Fin j × Fin j, Matrix.single k.2 k.1 (star (m k.1 k.2)) := by
    rw [Fintype.sum_prod_type_right]
    exact Matrix.matrix_eq_sum_single (star m)
  rw [e2]
  conv => enter [3, 2]; rw [e1]
  rw [GlobalTheory.MatrixAction.act_sum, GlobalTheory.MatrixAction.act_sum, ← hL']
  refine rosatiAdj_prod P'.A L' c _ _ _ fun k _ => ?_
  rw [hL']
  exact GlobalTheory.T.rosati_adjoint_of_box_projections S P.A P'.A j p P.L P'.L P.isLB P'.isLB w hw _ _ _ _ k.1 k.2
    (hs _ _ _) (hs _ _ _) (ιA.rosati _)

end GlobalTheory.MatrixRosati
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullbackSectionNonzeroLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolTranslate

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_pullback_section_nonzero_locus {X X' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) (n : ℕ) (θ : H0 L n) :
    ∃ θ' : H0 (L.pull F) n, ∀ y : X', y ∈ nonzeroLocus θ' ↔ F y ∈ nonzeroLocus θ := by
  have hL' := pull_isLB hL F
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  have hP := linComb_isLB L hL (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))
  have hP' := linComb_isLB (L.pull F) hL' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => (n : ℤ))
  obtain ⟨W, hW⟩ := LBIso.chartPull (chartPullId _) (chartPullOut L (fun _ : Fin 1 => 𝟙 X) (fun _ => (n : ℤ)) F _
    fun _ => (Category.id_comp F).trans (Category.comp_id F).symm)
    (iso_linComb hw (fun _ : Fin 1 => 𝟙 X') (fun _ => (n : ℤ)))
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff W).1 hW) hP hP' θ
  refine ⟨s', fun y => ?_⟩
  refine (mem_nonzeroLocus _ y).trans
    (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (F y)).symm)
  · obtain ⟨j, hj⟩ := exists_chart hP (F y)
    have e := hs' _ (𝟙 _) y j k hj hk
    rw [Category.id_comp, gs_stalkMap F y _ hj] at e
    exact ⟨j, hj, (isUnit_map_iff (F.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
  · obtain ⟨k, hk⟩ := exists_chart hP' y
    have e := hs' _ (𝟙 _) y j k hj hk
    rw [Category.id_comp] at e
    exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap F y _ hj _).symm.trans e)).mp (u.map _))⟩

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

noncomputable def transl (x : 𝟙_ (Over S) ⟶ A) : A ⟶ A := 𝟙 A * (toUnit A ≫ x)

theorem comp_transl (x : 𝟙_ (Over S) ⟶ A) {T : Over S} (y : T ⟶ A) : y ≫ transl x = y * (toUnit T ≫ x) := by
  rw [transl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem toUnit_mul_self {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) (T : Over S) :
    (toUnit T ≫ x) * (toUnit T ≫ x) = 1 := by
  rw [← MonObj.comp_mul, hx, MonObj.comp_one]

theorem transl_transl {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) : transl x ≫ transl x = 𝟙 A := by
  rw [comp_transl, transl, _root_.mul_assoc, toUnit_mul_self hx, _root_.mul_one]

theorem inv_transl [IsCommMonObj A] {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) :
    (GrpObj.inv : A ⟶ A) ≫ transl x = transl x ≫ (GrpObj.inv : A ⟶ A) := by
  rw [comp_transl, ← Hom.inv_def, transl, mul_inv, inv_eq_of_mul_eq_one_right (toUnit_mul_self hx A), Hom.inv_def,
    Category.id_comp]

theorem exists_restrict {X Y : Scheme.{0}} (p : X ⟶ Y) (h : X ⟶ X) (e : h ≫ p = p) (V : Y.Opens) :
    ∃ n : (p ⁻¹ᵁ V).toScheme ⟶ (p ⁻¹ᵁ V).toScheme, n ≫ (p ⁻¹ᵁ V).ι = (p ⁻¹ᵁ V).ι ≫ h :=
  ⟨IsOpenImmersion.lift _ ((p ⁻¹ᵁ V).ι ≫ h) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (congrArg (fun q => q y.1 ∈ V) e).mpr y.2), IsOpenImmersion.lift_fac _ _ _⟩

theorem sym_transl [IsCommMonObj A] {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) {L : LB A.left} (h : Sym A L) :
    Sym A (L.pull (transl x).left) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := h s
  obtain ⟨n, hn⟩ := exists_restrict A.hom (transl x).left (Over.w _) U
  refine ⟨U, hU, _, LBxP.isGen_pullAlong L (transl x).left n _ _ _ (fun k => ?_) t ht⟩
  fin_cases k
  · show (_ ≫ _) ≫ _ = n ≫ _ ≫ _
    rw [← Category.assoc n, hn, Category.assoc, Category.assoc]
    exact congrArg (fun q => _ ≫ q.left) (inv_transl hx)
  · exact hn.symm

theorem kTriv_transl {x : 𝟙_ (Over S) ⟶ A} (hx : x * x = 1) {L : LB A.left} (hL : L.IsLB) (h : KTriv A L) :
    KTriv A (L.pull (transl x).left) := by
  intro R _ t y hy
  refine h R t y fun p => ?_
  obtain ⟨V, hV, c, hc⟩ := hy p
  refine ⟨V, hV, ?_⟩
  have hL' := pull_isLB hL (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let T : Over S := Over.mk t
  obtain ⟨n, hn⟩ := exists_restrict (fst T A).left (T ◁ transl x).left
    (congrArg (fun q => q.left) (whiskerLeft_fst T (transl x))) V
  have k₂ : T ◁ transl x ≫ snd T A ≫ transl x = snd T A := by
    rw [whiskerLeft_snd_assoc, transl_transl hx, Category.comp_id]
  have k₃ : T ◁ transl x ≫ ((fst T A ≫ y) * snd T A) ≫ transl x = (fst T A ≫ y) * snd T A := by
    rw [← Category.assoc, MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd, comp_transl, comp_transl,
      _root_.mul_assoc, _root_.mul_assoc, toUnit_mul_self hx, _root_.mul_one]
  obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn (L.pull (transl x).left) _ _ _) c hc
  obtain ⟨c₂, h₂, -⟩ := exists_up hw hL hL' c₁ h₁
  refine gen_chartPull (chartPullOut L _ _ _ _ fun k => ?_) _ (pullGen_isGen _ _ _ c₂ h₂ n)
  show n ≫ (_ ≫ _) ≫ (transl x).left = _
  rw [Category.assoc, ← Category.assoc n, hn, Category.assoc]
  fin_cases k
  exacts [congrArg (fun q => _ ≫ q.left) k₃, congrArg (fun q => _ ≫ q.left) k₂]

theorem exists_translate : ∀ (K : Type) [Field K] (A : PolAV (Spec (CommRingCat.of K))) (x : 𝟙_ _ ⟶ A.A), x * x = 1 →
    ∀ θ : H0 A.L 1, ∃ (A' : PolAV (Spec (CommRingCat.of K))) (e : A'.A ≅ A.A) (θ' : H0 A'.L 1), IsMonHom e.hom ∧
      A'.g = A.g ∧ ∀ a : A'.A.left, a ∈ nonzeroLocus θ' ↔ (e.hom * (toUnit _ ≫ x)).left a ∈ nonzeroLocus θ := by
  intro K _ A x hx θ
  have hL' := pull_isLB A.isLB (transl x).left
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  have e : (transl x).left ≫ (transl x).left = 𝟙 _ := congrArg (fun q => q.left) (transl_transl hx)
  have : IsIso (transl x).left := ⟨⟨(transl x).left, e, e⟩⟩
  have hp : IsPullback (transl x).left A.A.hom A.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w _).trans (Category.comp_id _).symm⟩
  obtain ⟨θ', hθ'⟩ := exists_pullback_section_nonzero_locus A.isLB (transl x).left 1 θ
  exact ⟨{ A := A.A, isAb := A.isAb, g := A.g, smoothDim := A.smoothDim, L := A.L.pull (transl x).left, isLB := hL'
           rigid := exists_gen_of_local (V := K) _ hL' (K := PUnit) (fun _ => eSec A.A) (fun _ => 1)
           sym := sym_transl hx A.sym
           ample := relAmple_pull hp A.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) A.ample
           ktriv := kTriv_transl hx A.isLB A.ktriv },
    Iso.refl _, θ', inferInstanceAs (IsMonHom (𝟙 _)), rfl, hθ'⟩

end GlobalTheory.PolTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteSublevel
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefVal
open TWM TWO SectionScalarValuation

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)

theorem isPullback_jO : IsPullback (jO hϖ hv (D := D)).left (fst (TF (R := V) F) D.toPre.P.A).left
    (fst (TO hϖ hv) D.toPre.P.A).left (Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F))) := by
  have H₁ : IsPullback (snd (TO hϖ hv) D.toPre.P.A).left (fst (TO hϖ hv) D.toPre.P.A).left D.toPre.P.A.hom
      (TO hϖ hv).hom := (IsPullback.of_hasPullback (TO hϖ hv).hom D.toPre.P.A.hom).flip
  have H₀ : IsPullback (DegPre.prB D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left D.toPre.P.A.hom
      (TF (R := V) F).hom := (IsPullback.of_hasPullback (TF (R := V) F).hom D.toPre.P.A.hom).flip
  rw [← jO_snd hϖ hv, ← Over.w (ιS hϖ hv)] at H₀
  exact H₀.of_right (jO_fst hϖ hv) H₁

include hϖ hv in

theorem exists_vge (hTW : TwistBCSpanStatement) {k : ℕ} (hk : 1 ≤ k) {α : D.toPre.X}
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k))) : ∃ r : ℚ, VGe D F v k α s r := by
  have hL := D.toPre.P.isLB
  have := D.toPre.P.isAb.proper
  have hp : IsProper (fst (TO hϖ hv) D.toPre.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TO hϖ hv).hom D.toPre.P.A.hom))
  have : CompactSpace (TO hϖ hv).left := inferInstanceAs (CompactSpace (Spec (CommRingCat.of (Ov v))))
  have : QuasiSeparatedSpace (TO hϖ hv).left := inferInstanceAs (QuasiSeparatedSpace (Spec (CommRingCat.of (Ov v))))
  have : CompactSpace (TO hϖ hv ⊗ D.toPre.P.A).left :=
    QuasiCompact.compactSpace_of_compactSpace (fst (TO hϖ hv) D.toPre.P.A).left
  have : QuasiSeparatedSpace (TO hϖ hv ⊗ D.toPre.P.A).left :=
    (quasiSeparated_iff_quasiSeparatedSpace (fst (TO hϖ hv) D.toPre.P.A).left).mp inferInstance
  obtain ⟨s₁, hs₁⟩ := exists_sec hL (φ' := fun i => (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) (ε' := DegPre.famε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      rw [GC.famφ_eq, ← jO_snd hϖ hv, Category.assoc]) s
  obtain ⟨t, ht, S, hS⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors (Ov v)) (isPullback_jO hϖ hv (D := D)) hL
    (fun i => (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) s₁
  obtain ⟨n, rr, σ, hσ⟩ := hTW V D.toPre k hk α (Ov v) (fO v hϖ hv) inferInstance S
  choose σF hσF using fun i => FamInt.exists_pull (D := D) (F := F) (σ i)
  have ht0 : (t : F) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := F) ht
  obtain ⟨r, hr⟩ := wt_coe_of_ne (v := v) (inv_ne_zero ht0)
  refine ⟨r, n, fun i => (t : F)⁻¹ * ιr (v := v) (rr i), σ, σF, hσF, fun i => ?_, fun j => ?_⟩
  · rw [AddValuation.map_mul, hr]
    exact le_add_of_nonneg_right (v_ιr _)
  refine (sec_ext_val hL (s' := FamInt.secLin (fun i => gF D.toPre F ((t : F)⁻¹ * ιr (v := v) (rr i))) σF)
    (fun y J hJ => ?_) j).trans rfl
  rw [sval_lin (s := FamInt.secLin _ _) (fun i => gF D.toPre F ((t : F)⁻¹ * ιr (v := v) (rr i))) σF (fun _ => rfl) _ y hJ]
  have e₁ : sval S (𝟙 _ ≫ (jO hϖ hv (D := D)).left) y J = gs (𝟙 _) y ⊤ (gF D.toPre F t) * sval s (𝟙 _) y J := by
    rw [← hs₁ _ _ y J hJ, sval_of S (𝟙 _ ≫ (jO hϖ hv (D := D)).left) y J (fun a => J (𝟙 _ ≫ (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α a)) (fun a => by rw [Category.assoc])]
    refine (hS _ (𝟙 _) y _ (hJ.mem (fun a => (jO hϖ hv (D := D)).left ≫
      (snd (TO hϖ hv) D.toPre.P.A).left ≫ D.toPre.famφB α a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)
    have e := gs_jO hϖ hv (D := D) (𝟙 _) y ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom t)
    rw [show ιr (v := v) ((Scheme.ΓSpecIso (CommRingCat.of (Ov v))).inv.hom t) = (t : F) by simp [ιr]] at e
    rw [← e, ← Category.assoc]
    exact (gs_pull _ _ y ⊤ trivial _).symm
  have e₂ := sval_lin (fun l => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (rr l))
      (fun l => pullSec D.toPre.P.L _ _ (σ l) (snd (TO hϖ hv) D.toPre.P.A).left) (fun j => hσ j)
      (𝟙 _ ≫ (jO hϖ hv).left) y hJ
  have g : ∀ a b : F, gs (𝟙 _) y ⊤ (gF D.toPre F (a * b)) =
      gs (𝟙 _) y ⊤ (gF D.toPre F a) * gs (𝟙 _) y ⊤ (gF D.toPre F b) := fun a b => by
    rw [map_mul, gs_mul _ y ⊤ trivial]
  have g₁ : gs (𝟙 _) y ⊤ (gF D.toPre F (t : F)⁻¹) * gs (𝟙 _) y ⊤ (gF D.toPre F t) = 1 := by
    rw [← g, inv_mul_cancel₀ ht0, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]
  rw [← _root_.one_mul (sval s _ y J), ← g₁, _root_.mul_assoc, ← e₁, e₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g, gs_jO, sval_pullSec _ _ _ _ _ y hJ, Category.assoc, jO_snd, secScal_sval (hσF i) _ y hJ, _root_.mul_assoc]

include hϖ hv in

theorem exists_nuGe (hTW : TwistBCSpanStatement) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k)
    (s : Fam D.toPre F k) : ∃ r : ℚ, NuGe D Q F v k s r := by
  classical
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X k hk
  choose r hr using fun i => exists_vge hϖ hv hTW hk (s.s (e i))
  obtain ⟨m, hm⟩ := (Set.finite_range fun i => (Q (e i) : ℚ) / k - r i).bddAbove
  refine ⟨-m, ?_⟩
  rw [n1a V ϖ hϖ D Q hQ _ _ hv k hk (Finset.univ.image e) (fun χ => by
    obtain ⟨i, hi, -⟩ := he χ
    exact ⟨e i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) s]
  intro α hα
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hα
  have := hm ⟨i, rfl⟩
  exact VGe.mono (hr i) (by linarith)

include hϖ in

theorem finite_sublevel {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {k : ℕ} (hk : 1 ≤ k) (l : D.toPre.X →+ ℚ)
    (q : ℚ) : {χ | (Q χ : ℚ) / k + l χ ≤ q}.Finite := by
  let β : LinearMap.BilinForm ℤ D.toPre.X := LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ D hQ a b)
    (fun a a' b => by simp) (fun c a b => by simp) (fun a b b' => by simp) (fun c a b => by simp)
  have hβ : ∀ a, β a a = 2 * Q a := fun a => (QForm.two_Q_eq hϖ D hQ a).symm
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  refine (ClassMin.finite_affine_sublevel (ClassMin.realExtension_ofIntBilin_posDef (β := β)
    (fun a b => QForm.bOf_comm D a b) (fun a ha => by have := QForm.Q_pos hϖ D hQ ha; rw [hβ]; omega))
    (inv_pos.2 hk') ((Rat.castHom ℝ).toAddMonoidHom.comp l) q).subset fun χ hχ => ?_
  have h : (((Q χ : ℚ) / k + l χ : ℚ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hχ
  show (k : ℝ)⁻¹ * ClassMin.ofIntBilin β χ + (l χ : ℝ) ≤ q
  rw [ClassMin.ofIntBilin_apply, hβ]
  push_cast at h ⊢
  refine le_of_eq_of_le ?_ h
  field_simp

end GlobalTheory.UT.CoefVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjectiveStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiExpansion_overField_injective : (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ) t t' s s', U.ExpF F k t s → U.ExpF F k t' s' → (t = t' ↔ s = s')) := by
  first | exact @GlobalTheory.UU.ExpFUniq.main | exact GlobalTheory.UU.ExpFUniq.main | (intros; apply GlobalTheory.UU.ExpFUniq.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducesFrobeniusOnSectionsTranslationIffImage
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT

theorem exists_twist_iff {S : Scheme.{0}} {A T : Over S} [GrpObj A] (L : LB A.left) (ψ : T ⊗ A ⟶ T ⊗ A)
    (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (n : ℤ) {W : Type} (g : W → Prop)
    (P : W → (LB.Sec (LPow A L n T) → LB.Sec (LPow A L n T) → Prop) → Prop) :
    (∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n])) (w : W),
      α.IsGen ∧ g w ∧ P w (IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α)) ↔
    ∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![n, -n])) (w : W),
      α.IsGen ∧ g w ∧ P w (IsTwistPull A L ψ m hm n n α) := by
  subst hm
  rfl

theorem exists_smul_of_pt_eq (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R]
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℤ)
    (x : TFK (R := R) F ⟶ A.A) (α β : LB.Gen (thetaLB A.A A.L n x)) (hα : α.IsGen) (hβ : β.IsGen) :
    ∃ c : F, c ≠ 0 ∧ ∀ (t : LB.Sec (LPow A.A A.L n (TFK (R := R) F)))
      (u u' : FieldBaseChange.SecOver (FieldBaseChange.abelianBase A F) (LPow A.A A.L n (TFK (R := R) F))),
      IsActOf A.A A.L n ⟨x, α, hα⟩ t u → IsActOf A.A A.L n ⟨x, β, hβ⟩ t u' → u' = c • u := by
  obtain ⟨a, ha⟩ := H1.exists_const A.L A.isLB (fst (TFK (R := R) F) A.A).left (BoxTheta.surj_fst hG A.isAb _)
    (LB.mulGen A.L ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x).left] ![n, -n] _ _ β
      (LB.invGen A.L ![(snd (TFK (R := R) F) A.A).left, (translPt A.A x).left] ![n, -n] α))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hβ (DVR.invGen_isGen _ _ _ _ hα)) (fun U _ h => by
      simp [Fintype.prod_sum_type, Fin.prod_univ_two])
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 a
  refine ⟨c, ?_, fun t u u' hu hu' => ?_⟩
  · rintro rfl
    let z : (TFK (R := R) F).left := (default : PrimeSpectrum F)
    choose J hJ using fun χ : (TFK (R := R) F).left ⟶ A.A.left => exists_chart A.isLB (χ z)
    refine Units.ne_zero _ ((ha _ (lift (𝟙 _) x).left z J hJ).trans ?_)
    exact (congrArg _ (map_zero _)).trans (FieldBaseChange.gs_zero' _ z ⊤ trivial)
  · refine FieldBaseChange.SecOver.ext _ _ fun j => sec_ext_val A.isLB (fun y J hJ => ?_) j
    have e := (congrArg Units.val ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _)))).symm.trans
      (ha _ (𝟙 _) y J hJ)
    refine (BoxTheta.act_val _ t u' hu' (𝟙 _) y hJ).trans (Eq.trans ?_
      (FieldBaseChange.sval_smul' hJ (𝟙 _) c u).symm)
    refine Eq.trans ?_ (congrArg₂ (· * ·) e (BoxTheta.act_val _ t u hu (𝟙 _) y hJ).symm)
    exact (congrArg (fun v : ((TFK (R := R) F ⊗ A.A).left.presheaf.stalk y)ˣ => v.val * _)
      (inv_mul_cancel_right _ _).symm).trans ((congrArg (· * _) (Units.val_mul _ _)).trans (_root_.mul_assoc _ _ _))

theorem indAt_translT_iff : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) (x : TFK (R := R) F ⟶ A.A), IndAt U.toUnifPre F N p (translT A.A x) ↔ QkToAkU U.toUnifPre F N p x := by
  intro hL R _ _ _ I _ D A G _ _ _ U F _ _ _ N hN p x
  have hG := hL.1.globalFns
  have key := fun w₀ : W0 U.toUnifPre => exists_twist_iff A.L (translT A.A x) (translPt A.A x) (lift_snd _ _) (N : ℤ)
    (W := Frm D.toPre F N p.g.b) (fun w => w.IsGen) (fun w Q => ∀ (t t' : SecA A F N) s s',
      U.toUnifPre.ExpandsF F N w₀ t s → U.toUnifPre.ExpandsF F N w₀ t' s' → Q t t' → PhiRel D.toPre F N p w s s')
  constructor
  · rintro ⟨-, H⟩ w₀ hw₀
    obtain ⟨α, w, hα, hw, h⟩ := (key w₀).1 (H w₀ hw₀)
    refine ⟨(hL.1.kerPow _ A N hN _ x).1 fun _ => ⟨⊤, trivial, exists_isGen_pull _ α hα _⟩, ?_⟩
    rintro ⟨y, β, hβ⟩ rfl
    obtain ⟨c, hc, hcs⟩ := exists_smul_of_pt_eq hG A F (N : ℤ) _ α β hα hβ
    obtain ⟨w', hw', hΦ⟩ := ProdTorsion.exists_phiRel_smul hG p w hw c hc
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨w', hw', fun t t' s s' hs hs' ht => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := (lift_snd _ _ : translT A.A y ≫ _ = _)) A.isLB hα t
    have e₁ := hΦ _ _ (h t u s _ hs ((he u _).2 rfl) hu)
    have e₂ : s' = c • e u := ((he _ _).1 hs').symm.trans ((congrArg e (hcs t u t' hu ht)).trans (e.map_smul c u))
    exact e₂ ▸ e₁
  · intro H
    refine ⟨lift_fst _ _, fun w₀ hw₀ => (key w₀).2 ?_⟩
    haveI : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
    haveI : Nonempty (TFK (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
    obtain ⟨θ, rfl⟩ := BoxTheta.exists_theta hL.1.kerPow A hN x (H w₀ hw₀).1
    obtain ⟨w, hw, h⟩ := (H w₀ hw₀).2 θ rfl
    exact ⟨θ.φ, w, θ.isGen, hw, h⟩

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInMaximalIdealOfNeZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem psiIn_maximalIdeal_of_ne_zero : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V), D.TauBimult → D.PsiEven → {χ : D.X | ¬ D.PsiIn χ (IsLocalRing.maximalIdeal V ^ 1)}.Finite → ∀ χ : D.X, χ ≠ 0 → D.PsiIn χ (IsLocalRing.maximalIdeal V) := by
  intro V _ _ _ hV D hT hE hfin χ hχ
  have : IsDiscreteValuationRing V := hV.1
  obtain ⟨ga, a, ha⟩ := exists_psiScal V D
  have hc := GlobalTheory.T.psiScalars_relations_up_to_baseUnits V D ga a ha
  have hm : IsLocalRing.maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  have hiff := fun x => psiIn_iff_scalar_mem V D ga a ha x _ hm
  rw [hiff]
  refine cubeRel_scalars_mem_maximalIdeal V D.X a (hc.1 hT) (hc.2 hE) ?_ χ hχ
  refine hfin.subset ?_
  intro x hx
  show ¬ _
  rw [pow_one, hiff]
  exact hx

end GlobalTheory
end

