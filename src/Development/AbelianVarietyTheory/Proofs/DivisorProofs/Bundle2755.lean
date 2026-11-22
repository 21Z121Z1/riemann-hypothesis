import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2659
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.TorsExtend

theorem exists_section_of_isFinite {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {Z : Scheme.{0}} (p : Z ⟶ Sp R) [IsFinite p] (y : Sp K ⟶ Z)
    (h : y ≫ p = spMap (algebraMap R K)) : ∃ x : Sp R ⟶ Z, spMap (algebraMap R K) ≫ x = y ∧ x ≫ p = 𝟙 _ := by
  first
  | exact @_root_.GlobalTheory.FactorAndSection.exists_section
  | exact _root_.GlobalTheory.FactorAndSection.exists_section
  | (apply _root_.GlobalTheory.FactorAndSection.exists_section <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorAndSection.exists_section <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorAndSection.exists_section <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorAndSection.exists_section ..)

theorem pow_eq_one_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) {T : Over S} (z : T ⟶ G) :
    z ^ n = 1 ↔ z.left ≫ (mulA G n).left = T.hom ≫ (η[G]).left := by
  have e : (1 : T ⟶ G).left = T.hom ≫ (η[G]).left := by
    rw [Hom.one_def]; simp
  rw [← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, ← e]
  exact ⟨fun h => by rw [h], fun h => Over.OverMorphism.ext h⟩

theorem exists_torsion_section (hL : Laws) {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) {n : ℕ} (hn : 1 ≤ n)
    {s : Sp K ⟶ Sp R} (hs : s = spMap (algebraMap R K)) (y : Over.mk s ⟶ P.A) (hy : y ^ n = 1) :
    ∃ x : baseOver (Sp R) ⟶ P.A, x ^ n = 1 ∧ spMap (algebraMap R K) ≫ x.left = y.left := by
  subst hs
  haveI := (hL.mulN _ P n hn).1
  let e : Sp R ⟶ P.A.left := (η[P.A]).left
  have he : e ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  obtain ⟨x, h₁, h₂⟩ := exists_section_of_isFinite (pullback.snd (mulA P.A n).left e)
    (pullback.lift y.left (spMap (algebraMap R K)) ((pow_eq_one_iff _ _ _).1 hy)) (pullback.lift_snd _ _ _)
  have h₃ : (x ≫ pullback.fst (mulA P.A n).left e) ≫ (mulA P.A n).left = e := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, h₂, Category.id_comp]
  refine ⟨Over.homMk (x ≫ pullback.fst _ _) ?_, (pow_eq_one_iff _ _ _).2 (h₃.trans (Category.id_comp _).symm), ?_⟩
  · rw [← Over.w (mulA P.A n), ← Category.assoc, h₃]
    exact he
  · show _ ≫ x ≫ pullback.fst _ _ = _
    rw [← Category.assoc, h₁, pullback.lift_fst]

theorem torsion_section_eq (hL : Laws) {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K]
    (P : PolAV (Sp R)) {n : ℕ} (hn : 1 ≤ n) (hu : IsUnit (n : R)) {x y : baseOver (Sp R) ⟶ P.A} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (s : Sp K ⟶ Sp R) (h : s ≫ x.left = s ≫ y.left) : x = y := by
  haveI := (hL.mulN _ P n hn).1
  haveI := (hL.mulN _ P n hn).2.2.2.1 (by simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  haveI : PreconnectedSpace (Sp R) := inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
  exact Over.OverMorphism.ext (eq_of_preconnected_of_unramified (T := Sp R) (mulA P.A n).left
    (((pow_eq_one_iff _ _ _).1 hx).trans ((pow_eq_one_iff _ _ _).1 hy).symm) s h)

theorem exists_labelled (hL : Laws) {R R₀ Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field Ω] [Algebra R Ω] [IsFractionRing R Ω] [CommRing R₀] (j₀ : R₀ →+* Ω)
    (P : PolAV (Sp R₀)) (P' : PolAV (Sp R)) (P₀ : PolAV (Sp Ω)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left)
    (ha : IsGrpPullback P₀.A P.A (spMap j₀) a) (ha' : IsGrpPullback P₀.A P'.A (spMap (algebraMap R Ω)) a')
    (hl : LBIso P₀.L (P.L.pull a)) (hl' : LBIso P₀.L (P'.L.pull a')) {n : ℕ} (hn : 1 ≤ n) (hu : IsUnit (n : R))
    {M : Type} [AddCommGroup M] (hM : ∀ x : M, n • x = 0) (pt : M → (baseOver (Sp R₀) ⟶ P.A))
    (add : ∀ x y, pt (x + y) = pt x * pt y)
    (bij : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R₀) (z : Over.mk x ⟶ P.A), z ^ n = 1 →
      ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R₀)) ≫ pt c = z) :
    ∃ pt' : M → (baseOver (Sp R) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧
      (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P'.A), z ^ n = 1 →
        ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt' c = z) ∧
      (∀ x y (c₀ : R₀ˣ) (c : Rˣ), j₀ c₀ = algebraMap R Ω c → WeilIs P.A P.L n (pt x) (pt y) (unitOn c₀) →
        WeilIs P'.A P'.L n (pt' x) (pt' y) (unitOn c)) ∧
      ∀ x, ∃ w0 : Sp Ω ⟶ P₀.A.left, w0 ≫ a = spMap j₀ ≫ (pt x).left ∧
        w0 ≫ a' = spMap (algebraMap R Ω) ≫ (pt' x).left := by
  haveI := P₀.isAb.comm
  haveI := P'.isAb.proper
  have hi := IsFractionRing.injective R Ω
  have hb := GenericKTriv.pushHom_bijective ha (baseOver (Sp Ω))
  have hb' := GenericKTriv.pushHom_bijective ha' (baseOver (Sp Ω))
  let h₀ : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap j₀) ⟶ baseOver (Sp R₀) := Over.homMk (spMap j₀) (by simp)
  let h : Over.mk ((baseOver (Sp Ω)).hom ≫ spMap (algebraMap R Ω)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R Ω)) (by simp)
  have zero : pt 0 = 1 := by
    have := add 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have smul : ∀ (k : ℕ) x, pt (k • x) = pt x ^ k := fun k x => by
    induction k with
    | zero => rw [zero_smul, zero, pow_zero]
    | succ k ih => rw [succ_nsmul, add, ih, pow_succ]
  have tor : ∀ x, pt x ^ n = 1 := fun x => by rw [← smul, hM, zero]
  choose w hw using fun x => hb.2 (h₀ ≫ pt x)
  have torw : ∀ x, w x ^ n = 1 := fun x => hb.1 (by
    rw [map_pow, hw, map_one, ← MonObj.comp_pow, tor, MonObj.comp_one])
  have addw : ∀ x y, w (x + y) = w x * w y := fun x y => hb.1 (by
    rw [map_mul, hw, hw, hw, add, MonObj.comp_mul])
  choose pt' tor' hpt' using fun x => exists_torsion_section hL P' hn (Category.id_comp _)
    (pushHom ha' (baseOver (Sp Ω)) (w x)) (by rw [← map_pow, torw, map_one])
  have hpt : ∀ x, h ≫ pt' x = pushHom ha' (baseOver (Sp Ω)) (w x) := fun x => Over.OverMorphism.ext (hpt' x)
  have e₀ : ∀ x, (w x).left ≫ a = spMap j₀ ≫ (pt x).left := fun x => congrArg (fun q => q.left) (hw x)
  have e₁ : ∀ x, (w x).left ≫ a' = spMap (algebraMap R Ω) ≫ (pt' x).left := fun x => (hpt' x).symm
  let F := AlgebraicClosure Ω
  let t : Sp F ⟶ Sp Ω := spMap (algebraMap Ω F)
  let g : Over.mk (t ≫ spMap j₀) ⟶ baseOver (Sp R₀) := Over.homMk (t ≫ spMap j₀) (by simp)
  have torg : ∀ x, (g ≫ pt x) ^ n = 1 := fun x => by rw [← MonObj.comp_pow, tor, MonObj.comp_one]
  have inj : Function.Injective pt' := fun x y e => by
    have e₂ : w x = w y := hb'.1 (by rw [← hpt, ← hpt, e])
    refine (bij F (t ≫ spMap j₀) (g ≫ pt y) (torg y)).unique (Over.OverMorphism.ext ?_) rfl
    show (t ≫ spMap j₀) ≫ (pt x).left = (t ≫ spMap j₀) ≫ (pt y).left
    rw [Category.assoc, Category.assoc, ← e₀, ← e₀, e₂]
  have ne : ∀ (K : Type) [Field K] (s : Sp K ⟶ Sp R), (n : K) ≠ 0 := fun K _ s => by
    have := hu.map (Spec.preimage s).hom
    rw [map_natCast] at this
    exact this.ne_zero
  have card : Nat.card M = n ^ (2 * P'.g) := by
    rw [← (hL.mulN _ P' n hn).2.2.2.2 F (t ≫ spMap (algebraMap R Ω)) (ne F (t ≫ spMap (algebraMap R Ω))),
      GenericKTriv.card_torsion ha' t rfl, ← GenericKTriv.card_torsion ha t rfl]
    refine Nat.card_eq_of_bijective (fun x => ⟨g ≫ pt x, torg x⟩) ⟨fun x y e => ?_, fun z => ?_⟩
    · exact (bij F (t ≫ spMap j₀) (g ≫ pt y) (torg y)).unique (congrArg Subtype.val e) rfl
    · obtain ⟨c, hc, -⟩ := bij F (t ≫ spMap j₀) z.1 z.2
      exact ⟨c, Subtype.ext hc⟩
  refine ⟨pt', fun x y => ?_, fun K _ _ s z hz => ?_, fun x y c₀ c hc H => ?_, fun x => ⟨(w x).left, e₀ x, e₁ x⟩⟩
  · have e : h ≫ pt' (x + y) = h ≫ (pt' x * pt' y) := by
      rw [MonObj.comp_mul, hpt, hpt, hpt, addw, map_mul]
    exact over_points_ext_of_injective _ P'.A R Ω _ hi _ _ _ (congrArg (fun q => q.left) e)
  · have hc := (hL.mulN _ P' n hn).2.2.2.2 K s (ne K s)
    let Φ : M → {x : Over.mk s ⟶ P'.A // x ^ n = 1} := fun c =>
      ⟨(Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ pt' c, by
        rw [← MonObj.comp_pow, tor', MonObj.comp_one]⟩
    have hΦ : Function.Injective Φ := fun c c' e =>
      inj (torsion_section_eq hL P' hn hu (tor' c) (tor' c') s (congrArg (fun q => q.1.left) e))
    have : Finite {x : Over.mk s ⟶ P'.A // x ^ n = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    obtain ⟨c, e⟩ := (hΦ.bijective_of_nat_card_le (by rw [hc, card])).2 ⟨z, hz⟩
    exact ⟨c, congrArg Subtype.val e, fun c' e' => hΦ ((Subtype.ext e').trans e.symm)⟩
  · refine MumPair.weilIs_of_spread Ω R _ hi P₀ P' a' ha' hl' n (w x) (w y) _ _ c hn (e₁ x) (e₁ y) (tor' x) (tor' y) ?_
    have H₁ := CommPairing.weilIs_pull hL.globalFns P.isAb P.isLB h₀ H
    have H₂ := (weilIs_grpPullback_of_comm' (Sp R₀) (Sp Ω) P.A P₀.A (spMap j₀) a P.L P₀.L P.isLB P₀.isLB ha hl
      (baseOver (Sp Ω)) n (w x) (w y) (h₀ ≫ pt x) (h₀ ≫ pt y) _ (e₀ x).symm (e₀ y).symm).2 H₁
    have e := SpreadLevel.appTop_unitOn j₀ c₀ (Units.map (algebraMap R Ω).toMonoidHom c) hc
    exact e ▸ H₂

theorem isIntegrallyClosed_ringOn {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) :
    IsIntegrallyClosed (M.ringOn U) := by
  haveI := RatModel.isFractionRing_ringOn hU hne
  refine (isIntegrallyClosed_iff Ω).2 fun {x} hx => ⟨⟨x, RatModel.mem_ringOn.2 fun z hz => ?_⟩, rfl⟩
  have := RatModel.isIntegrallyClosed_O hM z
  letI : Algebra (M.ringOn U) (M.O z) := (Subalgebra.inclusion (RatModel.ringOn_le_O hz)).toRingHom.toAlgebra
  haveI : IsScalarTower (M.ringOn U) (M.O z) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hx.tower_top (A := M.O z))
  exact hy ▸ y.2

theorem exists_labelled_on_chart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (U : X₁.M.Z.Opens) (P' : PolAV (Sp (X₁.M.ringOn U))) (P₀ : PolAV (Sp X₁.Ω₁)) (a : P₀.A.left ⟶ X₁.ρ.P.A.left) (a' : P₀.A.left ⟶ P'.A.left), IsAffineOpen U → (U : Set X₁.M.Z).Nonempty → IsGrpPullback P₀.A X₁.ρ.P.A (spMap X₁.S.R.val.toRingHom) a → IsGrpPullback P₀.A P'.A (spMap (X₁.M.ringOn U).val.toRingHom) a' → LBIso P₀.L (X₁.ρ.P.L.pull a) → LBIso P₀.L (P'.L.pull a') → ∃ pt' : X₁.S.Gam → (baseOver (Sp (X₁.M.ringOn U)) ⟶ P'.A), (∀ x y, pt' (x + y) = pt' x * pt' y) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp (X₁.M.ringOn U)) (z : Over.mk x ⟶ P'.A), z ^ (X₁.S.r * X₁.S.N) = 1 → ∃! c, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp (X₁.M.ringOn U))) ≫ pt' c = z) ∧ (∀ x y (c : (X₁.M.ringOn U)ˣ), (c : (X₁.M.ringOn U)) = algebraMap X₁.o₁ (X₁.M.ringOn U) (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)) → WeilIs P'.A P'.L (X₁.S.r * X₁.S.N : ℕ) (pt' x) (pt' y) (unitOn c)) ∧ (∀ x, ∃ w0 : Sp X₁.Ω₁ ⟶ P₀.A.left, w0 ≫ a = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w0 ≫ a' = spMap (X₁.M.ringOn U).val.toRingHom ≫ (pt' x).left) := by
  intro g n F W Z i X₁ U P' P₀ a a' hU hne ha ha' hl hl'
  obtain ⟨⟨hL, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  haveI := RatModel.isFractionRing_ringOn hU hne
  haveI := isIntegrallyClosed_ringOn X₁.M ((isNormalScheme_iff_pred _).1 X₁.normal) hU hne
  haveI := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
  haveI : IsNoetherianRing (X₁.M.ringOn U) := isNoetherianRing_of_fg (fg_ringOn_of_isAffineOpen _ _ X₁.M U hU hne)
  have hn : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (le_trans one_le_two X₁.S.N_ge)
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : X₁.M.ringOn U) := by
    have := X₁.S.unit.map (algebraMap X₁.o₁ (X₁.M.ringOn U))
    rwa [map_natCast] at this
  obtain ⟨pt', h₁, h₂, h₃, h₄⟩ := exists_labelled hL X₁.S.R.val.toRingHom X₁.ρ.P P' P₀ a a' ha ha' hl hl' hn hu
    (M := X₁.S.Gam) (fun x => by ext k; simp [nsmul_eq_mul, -Nat.cast_mul]) X₁.ρ.pt X₁.ρ.pt_add X₁.ρ.pt_bij
  refine ⟨pt', h₁, h₂, fun x y c hc => ?_, h₄⟩
  obtain ⟨c₀, hc₀⟩ := ((X₁.S.prim.isUnit (by positivity)).pow (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ x y).val)).map
    (algebraMap X₁.o₁ X₁.S.R)
  refine h₃ x y c₀ c ?_ (X₁.ρ.weil x y c₀ hc₀)
  rw [hc₀, hc]
  rfl

end GlobalTheory.Poinc.TorsExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfIsGrpPullbackOfInjectiveDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_eq_one_of_isGrpPullback_of_injective_domain : ∀ (Ω T : Type) [Field Ω] [CommRing T] [IsDomain T] (jT : T →+* Ω), Function.Injective jT → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → ∀ (x : baseOver (Sp Ω) ⟶ A.A) (y : baseOver (Sp T) ⟶ P.A) (k : ℕ), x.left ≫ φ = spMap jT ≫ y.left → x ^ k = 1 → y ^ k = 1 := by
  first | exact @GlobalTheory.Mum.pow_eq_one_of_isGrpPullback_of_injective | exact GlobalTheory.Mum.pow_eq_one_of_isGrpPullback_of_injective | (intros; apply GlobalTheory.Mum.pow_eq_one_of_isGrpPullback_of_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowNotMemMaximalIdealPowSucc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ReducedFibre

theorem pow_notMem_maximalIdeal_pow_succ {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) (hreg : π ∈ nonZeroDivisors R) (k : ℕ) :
    π ^ k ∉ maximalIdeal R ^ (k + 1) := by
  intro h
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have h1 : π ^ k * (1 - π * c) = 0 := by
    linear_combination hc
  have h2 : 1 - π * c = 0 := (mul_left_mem_nonZeroDivisors_eq_zero_iff (pow_mem hreg k)).mp h1
  have hmem : π ∈ maximalIdeal R := by rw [hπ]; exact Ideal.mem_span_singleton_self π
  exact (mem_maximalIdeal π).mp hmem (isUnit_iff_exists_inv.mpr ⟨c, by linear_combination -h2⟩)

theorem adicCompletion_dvr {R : Type*} [CommRing R] [IsLocalRing R] {π : R}
    (hπ : maximalIdeal R = Ideal.span {π}) (hreg : π ∈ nonZeroDivisors R)
    (fg : (maximalIdeal R).FG) :
    haveI := AdicCompletion.isLocalRing_of_fg fg
    ∃ _ : IsDomain (AdicCompletion (maximalIdeal R) R),
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal R) R) ∧
      Irreducible (algebraMap R (AdicCompletion (maximalIdeal R) R) π) := by
  haveI := AdicCompletion.isLocalRing_of_fg fg
  haveI := AdicCompletion.isAdicComplete_of_fg fg
  refine GlobalTheory.isDiscreteValuationRing_of_maximalIdeal_eq_span ?_ ?_
  · rw [AdicCompletion.maximalIdeal_eq_map_of_fg fg, hπ, Ideal.map_span, Set.image_singleton]
  · rintro ⟨k, hk⟩
    rw [← map_pow] at hk
    have h := congrArg (AdicCompletion.eval (maximalIdeal R) R (k + 1)) hk
    rw [show algebraMap R (AdicCompletion (maximalIdeal R) R) (π ^ k) =
      AdicCompletion.of (maximalIdeal R) R (π ^ k) from rfl, AdicCompletion.eval_of, map_zero,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top] at h
    exact pow_notMem_maximalIdeal_pow_succ hπ hreg k h

end GlobalTheory.ReducedFibre

namespace GlobalTheory.ReducedFibre

theorem exists_notMem_mul_eq_zero {A : Type*} [CommRing A] [IsReduced A]
    {Q : Ideal A} (hQ : Q ∈ minimalPrimes A) {x : A} (hx : x ∈ Q) :
    ∃ s : A, s ∉ Q ∧ s * x = 0 := by
  haveI : Q.IsPrime := hQ.1.1
  have hsub := IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes Q hQ
    (Localization.AtPrime Q)
  have hmem : algebraMap A (Localization.AtPrime Q) x ∈ maximalIdeal _ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ hx
  have hnil : IsNilpotent (algebraMap A (Localization.AtPrime Q) x) := by
    rw [nilpotent_iff_mem_prime]
    intro Q' hQ'
    have h1 : (⟨Q', hQ'⟩ : PrimeSpectrum (Localization.AtPrime Q)) =
        ⟨maximalIdeal _, inferInstance⟩ := Subsingleton.elim _ _
    rw [show Q' = maximalIdeal _ from congrArg PrimeSpectrum.asIdeal h1]
    exact hmem
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff Q.primeCompl _ x).mp hnil.eq_zero
  exact ⟨s, s.2, hs⟩

theorem exists_cdvr_of_flat_of_isReduced :
    ∀ (V C : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing C] [Algebra V C]
      [Module.Flat V C], Nontrivial (C ⧸ (maximalIdeal V).map (algebraMap V C)) →
      IsReduced (C ⧸ (maximalIdeal V).map (algebraMap V C)) →
      ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V')
        (h : C →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
        ∀ ϖ : V, Irreducible ϖ → Irreducible (h (algebraMap V C ϖ)) := by
  intro V C _ _ _ _ _ _ hnt hred
  set J : Ideal C := (maximalIdeal V).map (algebraMap V C) with hJ
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (C ⧸ J)
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal (C ⧸ J)) ≤ M)
  haveI : Q.IsPrime := hQ.1.1
  set P : Ideal C := Q.comap (Ideal.Quotient.mk J) with hP
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  let R := Localization.AtPrime P
  have hJP : J ≤ P := fun x hx => by
    rw [hP, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Q.zero_mem
  have hmax : maximalIdeal R = (maximalIdeal V).map (algebraMap V R) := by
    rw [IsScalarTower.algebraMap_eq V C R, ← Ideal.map_map, ← hJ,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    refine le_antisymm ?_ (Ideal.map_mono hJP)
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨s', hs', hs'a⟩ := exists_notMem_mul_eq_zero hQ (show Ideal.Quotient.mk J a ∈ Q from ha)
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
    have hsP : s ∈ P.primeCompl := hs'
    have hsa : s * a ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_mul]; exact hs'a)
    rw [Ideal.mem_comap]
    have hu : IsUnit (algebraMap C R s) := IsLocalization.map_units R (⟨s, hsP⟩ : P.primeCompl)
    have := Ideal.mem_map_of_mem (algebraMap C R) hsa
    rw [map_mul] at this
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp this
  have hspan : ∀ ϖ : V, Irreducible ϖ → maximalIdeal R = Ideal.span {algebraMap V R ϖ} := by
    intro ϖ hϖ
    rw [hmax, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hreg : ∀ v : V, v ≠ 0 → algebraMap V R v ∈ nonZeroDivisors R := by
    intro v hv
    haveI : Module.Flat V R := Module.Flat.trans V C R
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) (mem_nonZeroDivisors_of_ne_zero hv)
    rw [mem_nonZeroDivisors_iff]
    refine ⟨fun x hx => h ?_, fun x hx => h ?_⟩
    · show v • x = v • (0 : R)
      rw [smul_zero, Algebra.smul_def, hx]
    · show v • x = v • (0 : R)
      rw [smul_zero, Algebra.smul_def, mul_comm, hx]
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible V
  have fg : (maximalIdeal R).FG := ⟨{algebraMap V R ϖ₀}, by rw [hspan ϖ₀ hϖ₀]; simp⟩
  haveI := AdicCompletion.isLocalRing_of_fg fg
  obtain ⟨hd, hdvr, -⟩ := adicCompletion_dvr (hspan ϖ₀ hϖ₀) (hreg ϖ₀ hϖ₀.ne_zero) fg
  refine ⟨AdicCompletion (maximalIdeal R) R, inferInstance, hd, hdvr,
    (algebraMap R (AdicCompletion (maximalIdeal R) R)).comp (algebraMap C R),
    AdicCompletion.isAdicComplete_of_fg fg, fun ϖ hϖ => ?_⟩
  obtain ⟨-, -, hirr⟩ := adicCompletion_dvr (hspan ϖ hϖ) (hreg ϖ hϖ.ne_zero) fg
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  exact hirr

end GlobalTheory.ReducedFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGlue

open GlobalTheory.Cartier

variable {X : Scheme.{0}} [IsIntegral X]

def ModPFrames (p : ℕ) {ι : Type} {N : ℕ} (U : ι → X.Opens) (M : ι → Matrix (Fin N) (Fin N) X.functionField)
    (c : ι → Fin N → X.functionFieldˣ) : Prop :=
  (∀ x : X, ¬ IsUnit (p : X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
  (∀ a, ∀ x ∈ U a, ¬ IsUnit (p : X.presheaf.stalk x) → (∀ i k, RegAt x (M a i k)) ∧ UnitAt x (M a).det) ∧
  ∀ a b, ∀ x ∈ U a, x ∈ U b → ¬ IsUnit (p : X.presheaf.stalk x) → ∀ i,
    UnitAt x ((c a i / c b i : X.functionFieldˣ) : X.functionField) ∧
    (∀ k, k < i → ZeroAt x (((M a)⁻¹ * M b) i k)) ∧
    ZeroAt x (((M a)⁻¹ * M b) i i - ((c a i / c b i : X.functionFieldˣ) : X.functionField))

def PowOfFrames (p : ℕ) {ι : Type} (U : ι → X.Opens) (c : ι → X.functionFieldˣ) (m : ℕ) (L : LB X) : Prop :=
  ∃ s : L.ι → X.functionFieldˣ, IsRatSec L s ∧ ∀ a k, ∀ x ∈ U a, x ∈ L.U k → ¬ IsUnit (p : X.presheaf.stalk x) →
    UnitAt x ((s k / c a ^ m : X.functionFieldˣ) : X.functionField)

end GlobalTheory.FrameGlue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisationDataIsEvenCubicalOnClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preUniformisationData_isEvenCubicalOnClosedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), EvenOn U.P := by
  first | exact @GlobalTheory.Mum.PreEven.evenOn_preU | exact GlobalTheory.Mum.PreEven.evenOn_preU | (intros; apply GlobalTheory.Mum.PreEven.evenOn_preU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreconnectedSpaceOfFinGenSubfieldBaseChangesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preconnectedSpace_of_finGen_subfield_baseChanges : ∀ (F : Type) [Field F] (X : Scheme.{0}) (f : X ⟶ Sp F), QuasiCompact f → QuasiSeparated f →
      ∀ (K : Type) [Field K] (i₀ : F →+* K),
        (∀ (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) (n : ℕ) (c : Fin n → K),
          L = Subfield.closure (Set.range i₀ ∪ Set.range c) →
          PreconnectedSpace (pullback f (spMap (i₀.codRestrict L hL)) : Scheme.{0})) →
        PreconnectedSpace (pullback f (spMap i₀) : Scheme.{0}) := by
  first | exact @GlobalTheory.GeomConnDesc.preconnectedSpace_of_finGen | exact GlobalTheory.GeomConnDesc.preconnectedSpace_of_finGen | (intros; apply GlobalTheory.GeomConnDesc.preconnectedSpace_of_finGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverOrdEqSumAdaptedMonomialStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeDivisorOver_ord_eq_sum_adaptedMonomial : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [GlobalTheory.IsNormalScheme Y] {q : Y ⟶ Sp k} (E : DivOver q) (y : Y), E.Through y →
    ∀ {ι : Type} [Fintype ι] (w : ι → Y) (u : ι → Y.functionFieldˣ), Function.Injective w →
    (∀ j, w j ⤳ y) → (∀ j, Order.coheight (w j) = 1) →
    (∀ j, Scheme.ord (u j : Y.functionField) (w j) = 1) →
    (∀ j v, v ⤳ y → Order.coheight v = 1 → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0) →
    ∀ φ : Y.functionFieldˣ,
      (∀ v, v ⤳ y → Order.coheight v = 1 → (∀ j, v ≠ w j) → Scheme.ord (φ : Y.functionField) v = 0) →
      E.ord φ = ∑ j, Scheme.ord (φ : Y.functionField) (w j) * E.ord (u j) := by
  first | exact @GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial | exact GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial | (intros; apply GlobalTheory.Discrepancy.MonoOrd.ord_eq_sum_of_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveBundleEqTranslateAmpleNoetherianLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_bundle_eq_translate_ample_noetherian_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (g : ℕ) (L O : LB B.left), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → L.IsLB → RelAmple B L → KTriv B L → (∃ t : LB.Gen (Theta B L), t.IsGen) → O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∃ x : 𝟙_ _ ⟶ B, LBIso O (LB.LinComb L (K := Fin 2) ![((toUnit B ≫ x) * 𝟙 B).left, 𝟙 B.left] ![1, -1]) := by
  first | exact @GlobalTheory.PrimitiveAmpleLocal.exists_section_translate | exact GlobalTheory.PrimitiveAmpleLocal.exists_section_translate | (intros; apply GlobalTheory.PrimitiveAmpleLocal.exists_section_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalOfConnectedDensity
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem princSt_of_connSt_propZ_densSt : ConnSt → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.PropZ → DensSt → PrincSt := by
  intro hConn hZ hDens F _ _ V p _ hp X s Xw hXi hXn hproj hflat hXw hirr K hK hU
  by_cases hT : ∃ yb, IsTest p Xw yb
  swap
  · exact ⟨0, fun yb h => absurd ⟨yb, h⟩ hT⟩
  obtain ⟨yb₀, hyb₀⟩ := hT
  have hne : (Xw : Set X).Nonempty := (Set.range_nonempty _).mono hyb₀.2
  haveI : IsDiscreteValuationRing V :=
    (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V (Fact.out : p.Prime).ne_zero hp).1
  obtain ⟨D, hD, ht, sig, hsig, hval⟩ := GlobalTheory.T.exists_charts_normal_projective_covering GlobalTheory.T.exists_charts_normal_projective hDens F V p hp X s Xw hXi hXn hproj hflat hXw hne K hK hU
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hprop : IsProper s := by
    obtain ⟨N, i, hi, hs⟩ := hproj
    have := isProper_str V N
    rw [← hs]
    infer_instance
  have hHyp : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.Hyp s D :=
    ⟨hXi, fun z => (hXn z).2, hprop, hflat, hConn F V X s Xw hXi hXn hproj hflat hirr, hD, ht⟩
  obtain ⟨M, n, hM, -, hVC⟩ := hZ V ϖ hϖ X s D hHyp sig hsig
  obtain ⟨r, hr⟩ := GlobalTheory.T.norm_uniformizer_constant F V p hp ϖ hϖ
  refine ⟨(r ^ n) ^ ((M : ℝ)⁻¹), fun yb hyb κ hκ => ?_⟩
  obtain ⟨φ, hφi, hφl, hφs, y, hy⟩ := GlobalTheory.T.test_point_generic_fibre F V p hp X s Xw hXw yb hyb
  obtain ⟨⟨e, cc, he, hco⟩, hall⟩ := hVC 𝓞_ℂ_[p] ℂ_[p] ℝ≥0 (Valued.v : Valuation ℂ_[p] ℝ≥0)
    (PadicComplexInt.integers p) φ hφi hφl yb hφs y hy
  have h1 := hall e cc he hco
  have h2 := hval yb hyb y hy e cc he hco κ hκ
  have h3 : ‖(cc : ℂ_[p])‖ ^ M = r ^ n := by
    have := congrArg (fun t : ℝ≥0 => (t : ℝ)) h1
    simp only [NNReal.coe_pow, NNReal.coe_zpow, coe_valued] at this
    rw [this, ← hr φ]
    rfl
  rw [← h2, ← h3, Real.pow_rpow_inv_natCast (norm_nonneg _) (by omega)]

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumComponentDegreesDivLeLatticeSlopeStatement
section
open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_component_degrees_div_le_latticeSlope : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → ∀ (la : Weight (T.Q.Dw j)), Y.GoodAt (wtOf (T.Q.Dw j) la 0) → Finite (Comp Y.d.Xo₂ Y.d.c₂) → (∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) la 0)) → 2 * ((∑ᶠ Z, Y.degC la Z) / ∑ᶠ Z, Y.rkC la Z) ≤ Y.mu (wtOf (T.Q.Dw j) la 0) := by
  first | exact @GlobalTheory.CovSum.sum_deg_div_le_mu | exact GlobalTheory.CovSum.sum_deg_div_le_mu | (intros; apply GlobalTheory.CovSum.sum_deg_div_le_mu <;> assumption)
end

