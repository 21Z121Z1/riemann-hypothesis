import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0186
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsHomAlgebraisationOfReductionTower
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MorAlgTower

theorem step_comm {C : Type*} [Category C] {Y Y' B S S' T : C} {p : B ⟶ T} {t : S ⟶ T}
    {t' : S' ⟶ T} [HasPullback p t] [HasPullback p t'] {τ : S ⟶ S'} {β : Y ⟶ Y'} {b : Y ⟶ B}
    {b' : Y' ⟶ B} {y : Y ⟶ S} {y' : Y' ⟶ S'} (hb : IsPullback b y p t)
    (hb' : IsPullback b' y' p t') (h₁ : β ≫ b' = b) (h₂ : β ≫ y' = y ≫ τ)
    (e₁ : p ≫ 𝟙 T = 𝟙 B ≫ p) (e₂ : t ≫ 𝟙 T = τ ≫ t') {Z : C} {c : Y ⟶ Z} {c' : Y' ⟶ Z}
    (hc : β ≫ c' = c) :
    pullback.map p t p t' (𝟙 _) τ (𝟙 _) e₁ e₂ ≫ hb'.isoPullback.inv ≫ c'
      = hb.isoPullback.inv ≫ c := by
  have key : β ≫ hb'.isoPullback.hom
      = hb.isoPullback.hom ≫ pullback.map p t p t' (𝟙 _) τ (𝟙 _) e₁ e₂ := by
    apply pullback.hom_ext
    · simp [h₁, pullback.map, pullback.lift_fst]
    · simp [h₂, pullback.map, pullback.lift_snd]
  rw [Iso.eq_inv_comp, ← Category.assoc, ← key, Category.assoc, Iso.hom_inv_id_assoc, hc]

theorem base_comm {C : Type*} [Category C] {Y B S T Z : C} {p : B ⟶ T} {t : S ⟶ T}
    [HasPullback p t] {b : Y ⟶ B} {y : Y ⟶ S} (hb : IsPullback b y p t) {c : Y ⟶ Z} {z : Z ⟶ T}
    (hc : c ≫ z = y ≫ t) : (hb.isoPullback.inv ≫ c) ≫ z = pullback.fst p t ≫ p := by
  rw [← hb.isoPullback_inv_fst, Category.assoc, Category.assoc, hc, hb.w]

theorem final_comm {C : Type*} [Category C] {Y B S T Z : C} {p : B ⟶ T} {t : S ⟶ T}
    [HasPullback p t] {b : Y ⟶ B} {y : Y ⟶ S} (hb : IsPullback b y p t) {c : Y ⟶ Z} {g : B ⟶ Z}
    (hg : pullback.fst p t ≫ g = hb.isoPullback.inv ≫ c) : b ≫ g = c := by
  have h := hb.isoPullback_hom_fst
  calc b ≫ g = (hb.isoPullback.hom ≫ pullback.fst p t) ≫ g := by rw [h]
    _ = c := by rw [Category.assoc, hg, Iso.hom_inv_id_assoc]

theorem exists_hom_of_tower : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (B : Over (Spec (CommRingCat.of R))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ Z : Over (Spec (CommRingCat.of R)), IsProjBy Z.hom → ∀ c : ∀ e, (Y e).left ⟶ Z.left, (∀ e, c e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ c (e + 1) = c e) → ∃ g : B ⟶ Z, ∀ e, b e ≫ g.left = c e := by
  intro R _ _ _ I hI hc Y β hβ B b hB hfl hb hβb Z hZ c hcZ hβc
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_hom_algebraising_thickenings_projective R I hI hc B Z hB hZ hfl (fun e => (hb e).isoPullback.inv ≫ c e)
    (fun e => base_comm (hb e) (hcZ e))
    (fun e => step_comm (hb e) (hb (e + 1)) (hβb e) (hβ e).w _ _ (hβc e))
  exact ⟨g, fun e => final_comm (hb e) (hg e)⟩

end GlobalTheory.MorAlgTower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfThetaUnitInEveryCoset
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.CosetGood

theorem subsingleton_of_forall_hom {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ} (hn : n.Prime)
    (h : ∀ (l : X →+ ZMod n) (y : X), l y = 0) : Subsingleton X := by
  haveI : Fact n.Prime := ⟨hn⟩
  let b := Module.Free.chooseBasis ℤ X
  haveI : IsEmpty (Module.Free.ChooseBasisIndex ℤ X) := ⟨fun i => by
    have := h ((Int.castAddHom (ZMod n)).comp (b.coord i).toAddMonoidHom) (b i)
    simp at this⟩
  exact b.repr.toEquiv.subsingleton

theorem subsingleton_of_labels {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    [IsAlgClosed C] (N : NumD C) (Q : QuadraticMap ℤ N.X ℝ) (hQ : N.Int Q) {n g j : ℕ} (hn : n.Prime) (ho : Odd n)
    (h1 : ‖(n : C)‖ = 1) (hT : N.Tors n g) (hj : 2 ≤ j) {La : Type} [AddCommGroup La]
    (r : N.QT ((n ^ j) ^ 2) → La → Prop) (tot : ∀ a, ∃ q, r q a) (cot : ∀ q, ∃ a, r q a)
    (mul : ∀ q q' a a', r q a → r q' a' → r (q * q') (a + a')) (inj : ∀ q q' a, r q a → r q' a → N.QEq q q')
    (v : La → C) (hv : ∀ q : La → N.QT ((n ^ j) ^ 2), (∀ a, r (q a) a) → ∃ c : C, ∀ a, v a = c * N.tx (n ^ j) (q a))
    (hle : ∀ a, ‖v a‖ ≤ 1) (hco : ∀ a, ∃ h, ‖v (a + n ^ (j - 1) • h)‖ = 1) : Subsingleton N.X := by
  classical
  obtain ⟨hA, hB, -⟩ := GlobalTheory.T.tx_coset_norm_one_and_ne_zero C N Q hQ n g hn ho h1 hT j (by omega)
  obtain ⟨q₀, -, -, hq₀⟩ := hB 1 rfl
  obtain ⟨a₀, ha₀⟩ := cot (1 * q₀)
  have tot' : ∀ a, ∃ q, r q a ∧ (a = a₀ → q = 1 * q₀) := fun a => by
    by_cases e : a = a₀
    · exact ⟨_, e ▸ ha₀, fun _ => rfl⟩
    · obtain ⟨q, hq⟩ := tot a
      exact ⟨q, hq, fun e' => absurd e' e⟩
  choose q hq hq' using tot'
  obtain ⟨c, hc⟩ := hv q hq
  have c1 : ‖c‖ ≤ 1 := by
    have := hle a₀
    rwa [hc, hq' a₀ rfl, norm_mul, hq₀, _root_.mul_one] at this
  have hu : ∀ a, ‖v a‖ = 1 → ‖N.tx (n ^ j) (q a)‖ = 1 := fun a ha => by
    rw [hc, norm_mul] at ha
    have := (hA (q a)).1
    nlinarith [norm_nonneg c, norm_nonneg (N.tx (n ^ j) (q a))]
  refine subsingleton_of_forall_hom hn fun l y => ?_
  have hl : ∀ (i : ℕ) (z : N.X), i ≠ 0 → l (n ^ i • z) = 0 := fun i z hi => by
    rw [map_nsmul, nsmul_eq_mul, Nat.cast_pow, ZMod.natCast_self, zero_pow hi, zero_mul]
  have he : ∀ p p' : N.QT ((n ^ j) ^ 2), N.QEq p p' → l p'.1.1.toAdd = l p.1.1.toAdd := by
    rintro p p' ⟨z, hz, -⟩
    rw [hz, map_add, show (n ^ j) ^ 2 • z = n ^ (j * 2) • z by rw [pow_mul], hl _ _ (by omega), add_zero]
  let Y : La →+ ZMod n := AddMonoidHom.mk' (fun a => l (q a).1.1.toAdd) fun a a' =>
    (he _ _ (inj _ _ _ (mul _ _ _ _ (hq a) (hq a')) (hq (a + a')))).trans (map_add l _ _)
  have hY : ∀ a, Y a = 0 := fun a => by
    obtain ⟨h, hh⟩ := hco a
    obtain ⟨z, hz⟩ := (hA _).2 (hu _ hh)
    have e : Y (a + n ^ (j - 1) • h) = 0 := (congrArg l hz).trans (hl _ _ (by omega))
    rwa [map_add, map_nsmul, nsmul_eq_mul, Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega), zero_mul,
      add_zero] at e
  have hn0 : (n : C) ≠ 0 := fun e => by rw [e, norm_zero] at h1; exact zero_ne_one h1
  have hs := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hn0 hT (j * 2)).2.2.1 y
  rw [pow_mul] at hs
  obtain ⟨p, rfl⟩ := hs
  obtain ⟨a, ha⟩ := cot p
  exact (he _ _ (inj _ _ _ (hq a) ha)).trans (hY a)

theorem exists_unitBall (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 :=
  ⟨(NormedField.valuation (K := C)).valuationSubring, fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    rfl⟩

theorem subsingleton_lattice (hV : HV) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C]
    (o : Full D C) (M : Mdl o) {n j : ℕ} (hn : n.Prime) (ho : Odd n) (h1 : ‖(n : C)‖ = 1) (hj : 2 ≤ j) (v : D.La → C)
    (hv : o.Theta (n ^ j) v) (hle : ∀ x, ‖v x‖ ≤ 1) (hco : ∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) :
    Subsingleton M.P.D.toPre.X := by
  letI := H.starRing
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff M.W).1 M.cdv
  have hR : AdmBase M.W (IsLocalRing.maximalIdeal M.W) := ⟨inferInstance, inferInstance, inferInstance, hcomp⟩
  have hev := M.P.D.psi_even
  have hbi := M.P.D.tau_bimult
  obtain ⟨S, hS⟩ := exists_unitBall C
  obtain ⟨N, ν, hν⟩ := GlobalTheory.ValuesExist.exists_integral_values hL M.W M.P.D.toPre hev hbi C S
    fun r => (hS _).2 (M.ext.1 r)
  have hI : ν.IntN := ⟨S, hS, hν⟩
  obtain ⟨Q, hQ⟩ := GlobalTheory.T.degenerationValues_int_of_admissibleBase M.W _ hR M.P.D C M.ext N ν hI
  have hT := GlobalTheory.T.abelianPartValues_torsion_pairing_separation_integral hL hL2 (GlobalTheory.T.abelianPartValues_of_expansionLaws hL) M.W M.P.D.toPre hev hbi C
    ⟨M.ext.1, fun r hr => M.ext.2 r (bot_le (a := IsLocalRing.maximalIdeal M.W) hr)⟩ N ν hI n hn ho h1
  obtain ⟨g₁, g₂, g₃, -, g₅⟩ := GlobalTheory.T.torus_torsion_points_correspond_values M.W M.P.D.toPre hev hbi C N ν
  have hk : 0 < (n ^ j) ^ 2 := pow_pos (pow_pos hn.pos _) _
  obtain ⟨g₆, g₇, g₈⟩ := g₅ ((n ^ j) ^ 2)
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hV.1 M.W _ hR M.P.D M.P.A M.t.G M.t.semi M.P.U C _ hk
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback M.cart (𝟙 (Sp C)) (jFK (R := M.W) C) (Category.id_comp _).symm
  let x : D.La → (TFK (R := M.W) C ⟶ M.P.A.A) := fun a => e (o.I.ev ((n ^ j) ^ 2) a)
  have hp : ∀ a, o.I.ev ((n ^ j) ^ 2) a ^ (n ^ j) ^ 2 = 1 := fun a => (o.I.onto _ hk _).2 ⟨a, rfl⟩
  have hx : ∀ a, x a ^ (n ^ j) ^ 2 = 1 := fun a => (map_pow e _ _).symm.trans ((congrArg e (hp a)).trans (map_one e))
  have hv' : IsThetaPt M.P.A (n ^ j) x fun a => fnOf (v a) := by
    have key : ∀ (s : Sp C ⟶ (TK M.W).left) (_ : s = 𝟙 _ ≫ jFK (R := M.W) C) (y : D.La → (Over.mk s ⟶ M.P.A.A)),
        (∀ a, (y a).left = (o.I.ev ((n ^ j) ^ 2) a).left ≫ M.φ) → IsThetaPt M.P.A (n ^ j) y fun a => fnOf (v a) := by
      rintro s rfl y hy
      exact (ThetaPtUp.isThetaPt_iff (T := baseOver (Sp C)) M.cart M.lb hy hp _).1 hv
    exact key _ (Category.id_comp _).symm x fun a => he _
  have hm : ((n ^ j : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.2 (pow_pos hn.pos _).ne'
  obtain ⟨-, c₂, c₃, -⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C _ M.P.A (jFK (R := M.W) C) (n ^ j) ho.pow hm D.La x hx
  haveI := subsingleton_of_labels N Q hQ hn ho h1 hT hj (fun q a => ∃ p, ν.QPt p q ∧ f p = x a) (fun a => ?_)
    (fun q => ?_) ?_ ?_ v (fun q hq => ?_) hle hco
  · exact ν.eX.symm.toEquiv.subsingleton
  · obtain ⟨p, hp⟩ := f₂ _ (hx a)
    obtain ⟨q, hq, -⟩ := g₆ p
    exact ⟨q, p, hq, hp⟩
  · obtain ⟨p, hp⟩ := g₇ q
    obtain ⟨w, hw⟩ := M.P.U.toUnifPre.ext
    have h₀ : f p ^ (n ^ j) ^ 2 = 1 := ((f₁ p (f p)).2 rfl w hw).1
    obtain ⟨a, ha⟩ := (o.I.onto _ hk (e.symm (f p))).1
      ((map_pow e.symm _ _).symm.trans ((congrArg e.symm h₀).trans (map_one e.symm)))
    exact ⟨a, p, hp, ((congrArg e ha).trans (e.apply_symm_apply _)).symm⟩
  · rintro q q' a a' ⟨p, hp, e₁⟩ ⟨p', hp', e₂⟩
    obtain ⟨p'', hp''⟩ := g₇ (q * q')
    refine ⟨p'', hp'', (f₄ p p' p'' ⟨p'', ?_, (g₃ _ _ _ _ _ _ hp.2 hp'.2 hp''.2).2 rfl, qk_equiv_refl hbi _⟩).trans ?_⟩
    · rw [← hp''.1, ← hp.1, ← hp'.1, ← map_add]; rfl
    · rw [e₁, e₂]
      exact ((congrArg e (o.I.add _ a a')).trans (map_mul e _ _)).symm
  · rintro q q' a ⟨p, hp, e₁⟩ ⟨p', hp', e₂⟩
    exact (g₈ p p' q q' hp hp').1 ((f₃ p p').1 (e₁.trans e₂.symm))
  · choose p hp hp' using hq
    have ht := GlobalTheory.T.theta_constants_eq_degeneration_series hV GlobalTheory.T.torus_torsion_points_correspond_values (GlobalTheory.T.families_values_correspond hL hL2) M.W _ M.cdv rfl M.P.D M.P.A M.t.G M.t.semi M.P.U C M.ext
      N ν (n ^ j) ho.pow D.La p q x (fun a => (f₁ _ _).2 (hp' a).symm) hp
    obtain ⟨c, hc⟩ := (c₂ 1 _ v ((c₃ _).1 ht)).1 ((c₃ _).1 hv')
    exact ⟨c, fun a => congrFun hc a⟩

theorem isProper_of_unit_in_cosets : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] (o : Full D C) (M : Mdl o) (n j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 2 ≤ j → ∀ v, o.Theta (n ^ j) v → (∀ x, ‖v x‖ ≤ 1) → (∀ x, ∃ h, ‖v (x + n ^ (j - 1) • h)‖ = 1) → IsProper M.t.G.hom := by
  intro hV _ _ _ _ _ _ E _ _ _ H D C _ _ _ _ _ o M n j hn ho h1 hj v hv hle hco
  obtain ⟨hdvr, hcomp, hchar⟩ := (GlobalTheory.LN.cDvr_iff M.W).1 M.cdv
  exact (isAbelianScheme_of_unif_of_subsingleton hV.1.1 hV.1.2.1 M.W hcomp M.P.D M.P.A M.t.G M.t.semi M.P.U
    (subsingleton_lattice hV o M hn ho h1 hj v hv hle hco)).proper

end GlobalTheory.CosetGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationDataStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_points_eq_of_same_degeneration_data : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (I : Ideal R) (f : O' →+* R) (u : R), AdmBase R I → I ≠ ⊤ → Function.Injective f → ∀ (χ χ' : Sp R ⟶ Y.X) (y y' : Sp (FractionRing R) ⟶ Xo.XF c), y ≫ Y.j = jK R ≫ χ → y' ≫ Y.j = jK R ≫ χ' → χ ≫ Y.s = spMap f ≫ spMap b → χ' ≫ Y.s = spMap f ≫ spMap b → Y.HasArcData a I f u χ → Y.HasArcData a I f u χ' → χ = χ' := by
  first | exact @GlobalTheory.ArcUnique.eq_of_hasArcData | exact GlobalTheory.ArcUnique.eq_of_hasArcData | (intros; apply GlobalTheory.ArcUnique.eq_of_hasArcData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianReductionOfIsogeny
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.Isog

open IsLocalRing

theorem spMap_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := GlobalTheory.ModelDescent.spMap_comp_eq rfl

theorem isModel_pullback {K W L W' L' : Type} [Field K] [CommRing W] [Field L] [CommRing W'] [Field L']
    [Algebra K L] [Algebra W L] [Algebra K L'] [Algebra W' L'] (c : W →+* W') (b : L →+* L')
    (e : (algebraMap W' L').comp c = b.comp (algebraMap W L)) (e' : b.comp (algebraMap K L) = algebraMap K L')
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (h : IsModel (L := L) A G) :
    IsModel (L := L') A ((Over.pullback (spMap c)).obj G) := by
  obtain ⟨e₀, he₀⟩ := h
  have hW : spMap (algebraMap W' L') ≫ spMap c = spMap b ≫ spMap (algebraMap W L) := by
    rw [spMap_comp, spMap_comp, e]
  have hK : spMap (algebraMap K L') = spMap b ≫ spMap (algebraMap K L) := by
    rw [spMap_comp, e']
  have key : ∀ (φ : Sp L' ⟶ Sp W) (ψ : Sp L' ⟶ Sp K), φ = spMap b ≫ spMap (algebraMap W L) →
      ψ = spMap b ≫ spMap (algebraMap K L) →
      ∃ f : (Over.pullback φ).obj G ≅ (Over.pullback ψ).obj A, IsMonHom f.hom := by
    rintro φ ψ rfl rfl
    refine ⟨pullCompIso _ _ G ≪≫ (Over.pullback (spMap b)).mapIso e₀ ≪≫ (pullCompIso _ _ A).symm, ?_⟩
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    infer_instance
  obtain ⟨f, hf⟩ := key _ _ hW hK
  show ∃ e : _ ≅ _, IsMonHom e.hom
  refine ⟨(pullCompIso _ _ G).symm ≪≫ f, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

theorem pullback_map_id_pow {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) [GrpObj B] (m : ℕ) :
    (Over.pullback f).map (𝟙 B ^ m) = 𝟙 ((Over.pullback f).obj B) ^ m := by
  simpa using map_pow ((Over.pullback f).homMonoidHom) (𝟙 B) m

theorem exists_model_of_isogeny (K R K' : Type) [Field K] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K']
    [Algebra R K'] [Algebra K K'] (hSH : SH R K') (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g m : ℕ)
    (hA : IsAbelianScheme A) (hP : GlobalTheory.AbLaw.IsProjBy A.hom) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (i : A ⟶ B) (r : B ⟶ A) [IsMonHom i] [IsMonHom r] (hm : 1 ≤ m)
    (hri : r ≫ i = 𝟙 _ ^ m) (G' : Over (Sp R)) [GrpObj G'] (hG' : IsSemiAbelian G') (hmod : IsModel (L := K') B G') :
    ∃ (G : Over (Sp R)) (_ : GrpObj G), SmConn G ∧ IsModel (L := K') A G ∧
      Nonempty (TorusExtension (spFibre G)) := by
  obtain ⟨e, he⟩ := hmod
  haveI := he
  have hbc : ∀ (X : Over (Sp K)), SmoothOfRelativeDimension g X.hom →
      SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj X).hom := fun X hX =>
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback X.hom (spMap (algebraMap K K'))) hX
  have hA' : IsAbelianScheme ((Over.pullback (spMap (algebraMap K K'))).obj A) := by
    obtain ⟨h1, h2, h3, h4⟩ := hA
    exact ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd A.hom (spMap (algebraMap K K')))),
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))) h3,
      inferInstanceAs (GeometricallyConnected (pullback.snd A.hom (spMap (algebraMap K K'))))⟩
  have hP' : GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K K'))).obj A).hom :=
    GlobalTheory.AbLaw.isProjBy_baseChange K K' (algebraMap K K') A.left _ A.hom _ _
      (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K'))) hP
  have hgA' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj A).hom := hbc A hgA
  haveI hgB' : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap K K'))).obj B).hom := hbc B hgB
  have hgG : SmoothOfRelativeDimension g ((Over.pullback (spMap (algebraMap R K'))).obj G').hom := by
    haveI : IsIso e.hom.left := ⟨e.inv.left, by simp [← Over.comp_left], by simp [← Over.comp_left]⟩
    have h : SmoothOfRelativeDimension (0 + g) (e.hom.left ≫ ((Over.pullback (spMap (algebraMap K K'))).obj B).hom) := inferInstance
    rw [zero_add, Over.w e.hom] at h
    exact h
  have hri' : (e.hom ≫ (Over.pullback (spMap (algebraMap K K'))).map r) ≫ ((Over.pullback (spMap (algebraMap K K'))).map i ≫ e.inv) = 𝟙 _ ^ m := by
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hri, pullback_map_id_pow, MonObj.pow_comp, MonObj.comp_pow]
    simp
  obtain ⟨G, _, e₂, hsc, he₂, ht⟩ := GlobalTheory.T.semiAbelian_reduction_along_isogeny_strict_henselian R K' hSH ((Over.pullback (spMap (algebraMap K K'))).obj A) G' g m hA' hP' hG' hgA' hgG
    ((Over.pullback (spMap (algebraMap K K'))).map i ≫ e.inv) (e.hom ≫ (Over.pullback (spMap (algebraMap K K'))).map r) inferInstance inferInstance hm hri'
  exact ⟨G, inferInstance, hsc, show ∃ _, _ from ⟨e₂, he₂⟩, ht⟩

end GlobalTheory.SS.Isog

namespace GlobalTheory.SS

open Isog IsLocalRing in

theorem potModel_semiAbelian_of_isogeny : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g m : ℕ), IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (i : A ⟶ B) (r : B ⟶ A), IsMonHom i → IsMonHom r → 1 ≤ m → r ≫ i = 𝟙 _ ^ m → PotModel V K B (fun _ _ _ G _ => IsSemiAbelian G) → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ A B _ _ g m hA hP hgA hgB i r hi hr hm hri hB
  haveI := hi
  haveI := hr
  obtain ⟨W, L, _, _, _, _, _, _, _, _, hc, hfin, hloc, hcomp, G, _, hmod, hG⟩ := hB
  have hG' : IsSemiAbelian G := hG
  haveI : IsAdicComplete (maximalIdeal W) W := hcomp
  haveI : CharZero L := (RingHom.charZero_iff (algebraMap K L).injective).1 inferInstance
  haveI : CharZero W := (RingHom.charZero_iff (IsFractionRing.injective W L)).2 inferInstance
  haveI : CharZero V := (RingHom.charZero_iff (IsFractionRing.injective V K)).2 inferInstance
  obtain ⟨R, _, _, _, _, hinj, hint, hac⟩ := GlobalTheory.T.exists_integral_ext_isAlgClosed_residueField' W
  obtain ⟨-, hhen, -⟩ := GlobalTheory.T.henselian_iUnion_complete_of_integral_over_complete_dvr W R hinj hint
  have hWK : Function.Injective ((algebraMap R (FractionRing R)).comp (algebraMap W R)) :=
    (IsFractionRing.injective R (FractionRing R)).comp hinj
  obtain ⟨b, hbW⟩ : ∃ b : L →+* FractionRing R,
      (algebraMap R (FractionRing R)).comp (algebraMap W R) = b.comp (algebraMap W L) :=
    ⟨IsFractionRing.lift hWK, RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := L) hWK x).symm⟩
  letI : Algebra K (FractionRing R) := (b.comp (algebraMap K L)).toAlgebra
  have hSH : SH R (FractionRing R) := by
    show _ ∧ _ ∧ _ ∧ _
    exact ⟨inferInstance, hhen, hac, inferInstance⟩
  have hmodR : IsModel (L := FractionRing R) B ((Over.pullback (spMap (algebraMap W R))).obj G) :=
    isModel_pullback (algebraMap W R) b hbW rfl B G hmod
  have hsemiR : IsSemiAbelian ((Over.pullback (spMap (algebraMap W R))).obj G) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (spMap (algebraMap W R)) G hG'
  obtain ⟨GR, _, hsc, hmodA, ht⟩ := exists_model_of_isogeny K R (FractionRing R) hSH A B g m hA hP hgA hgB
    i r hm hri _ hsemiR hmodR
  letI : Algebra V R := ((algebraMap W R).comp (algebraMap V W)).toAlgebra
  have hVR : (algebraMap R (FractionRing R)).comp (algebraMap V R) =
      (algebraMap K (FractionRing R)).comp (algebraMap V K) := by
    change (algebraMap R (FractionRing R)).comp ((algebraMap W R).comp (algebraMap V W)) =
      (b.comp (algebraMap K L)).comp (algebraMap V K)
    rw [← RingHom.comp_assoc, hbW, RingHom.comp_assoc, hc, RingHom.comp_assoc]
  obtain ⟨s, hs⟩ := GlobalTheory.smConn_model_descends V K R (FractionRing R) hVR A hA GR hsc hmodA
  have hVW : Function.Injective (algebraMap V W) := by
    have h2 : Function.Injective ((algebraMap K L).comp (algebraMap V K)) :=
      (algebraMap K L).injective.comp (IsFractionRing.injective V K)
    rw [← hc, RingHom.coe_comp] at h2
    exact h2.of_comp
  haveI : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
  have hVRi : (algebraMap V R).IsIntegral :=
    RingHom.IsIntegral.trans (f := algebraMap V W) (g := algebraMap W R)
      (fun x => Algebra.IsIntegral.isIntegral (R := V) x) (fun x => hint.isIntegral x)
  have hVRinj : Function.Injective (algebraMap V R) := hinj.comp hVW
  obtain ⟨hlocVR, -, hdescV⟩ := GlobalTheory.T.henselian_iUnion_complete_of_integral_over_complete_dvr V R hVRinj ⟨fun x => hVRi x⟩
  obtain ⟨W', _, hsW, hcW, hfW, hlW⟩ := hdescV s
  obtain ⟨GW, _, _, ε, hscW, hε, hcompW, hmodW⟩ := hs W' inferInstance hsW hlW
  haveI := hε
  have hlVW : IsLocalHom (algebraMap V W') := by
    refine ⟨fun x hx => ?_⟩
    have h1 : IsUnit (W'.val.toRingHom (algebraMap V W' x)) := hx.map _
    exact IsLocalHom.map_nonunit (f := algebraMap V R) x h1
  let ρ : W' →+* ResidueField R := (residue R).comp W'.val.toRingHom
  have hker : RingHom.ker ρ = maximalIdeal W' := by
    rw [← RingHom.comap_ker, ker_residue, maximalIdeal_comap]
  have hρi : ρ.IsIntegral :=
    RingHom.IsIntegral.trans (f := W'.val.toRingHom) (g := residue R)
      (RingHom.IsIntegral.tower_top (f := algebraMap V W') (g := W'.val.toRingHom) hVRi)
      (RingHom.isIntegral_of_surjective _ residue_surjective)
  have htor : Nonempty (TorusExtension ((Over.pullback (spMap ρ)).obj GW)) := by
    obtain ⟨T⟩ := ht
    have hρ : spMap ρ = spMap (residue R) ≫ spMap W'.val.toRingHom := (Isog.spMap_comp _ _).symm
    rw [hρ]
    let Z := pullCompIso (spMap (residue R)) (spMap W'.val.toRingHom) GW ≪≫ (Over.pullback _).mapIso ε
    haveI : IsMonHom Z.symm.hom := by
      dsimp only [Z, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv]
      infer_instance
    exact ⟨torusExtOfIso Z.symm T⟩
  have hprop : IsProper ((Over.pullback (spMap (algebraMap W' (FractionRing W')))).obj GW).hom := by
    obtain ⟨e, -⟩ := hmodW
    haveI : IsProper A.hom := hA.proper
    haveI : IsProper ((Over.pullback (spMap (algebraMap K (FractionRing W')))).obj A).hom :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap K (FractionRing W')))) (inferInstanceAs (IsProper A.hom))
    haveI : IsIso e.hom.left := ⟨e.inv.left, by simp [← Over.comp_left], by simp [← Over.comp_left]⟩
    rw [← Over.w e.hom]
    infer_instance
  have hsemiW : IsSemiAbelian GW :=
    isSemiAbelian_of_proper_generic_of_torusExtension W' (FractionRing W') GW hscW hprop
      (ResidueField R) ρ hker hρi htor
  unfold PotModel
  exact ⟨W', FractionRing W', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcompW, hfW, hlVW, hcW, GW, inferInstance, hmodW, hsemiW⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisationStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiUnitOn_abelian_locus_uniformisation : Laws → Laws2 → Laws3 → Laws4 → Laws5 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, IsOpen (abLocus G) → ∀ y, PsiUnitOn D.toPre y (abLocus G) := by
  first | exact @GlobalTheory.PsiAbelian.psiUnitOn_abLocus | exact GlobalTheory.PsiAbelian.psiUnitOn_abLocus | (intros; apply GlobalTheory.PsiAbelian.psiUnitOn_abLocus <;> assumption)
end

