import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2657
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2758
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.FibMove

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso (L.pull (g ≫ f)) ((L.pull f).pull g) :=
  LBIso.chartPull (RigidBundleGlue.chartPullComp L f g _ rfl) (chartPullId _)
    ⟨idIso _, idIso_isGen (pull_isLB (pull_isLB hL f) g)⟩

theorem polFib_move : ∀ (S S' : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (A : Over S') [GrpObj A] (L' : LB A.left) (f : S' ⟶ S) (φ : A.left ⟶ G.left), L.IsLB → L'.IsLB → IsGrpPullback A G f φ → LBIso L' (L.pull φ) → ∀ (g : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S'), (PolFib A L' g x ↔ PolFib G L g (x ≫ f)) ∧ ∀ (R' : Type) [CommRing R'] (i : R →+* R'), PolFib A L' g x → PolFib A L' g (spMap i ≫ x) := by
  intro S S' G _ L A _ L' f φ hL hL' hφ hLL' g R _ x
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨P, α, hg, hα, hPL⟩
    refine ⟨P, α ≫ φ, hg, hα.comp hφ, ?_⟩
    exact LBIso.trans P.isLB (pull_isLB hL' α) (pull_isLB hL _) hPL
      (LBIso.trans (pull_isLB hL' α) (pull_isLB (pull_isLB hL φ) α) (pull_isLB hL _)
        (RigidBundleGlue.LBIso.pull hLL' α) (lbIso_pull_comp hL φ α).symm)
  · rintro ⟨P, β, hg, hβ, hPL⟩
    have w : β ≫ G.hom = P.A.hom ≫ (x ≫ f) := hβ.1.w
    let α : P.A.left ⟶ A.left := hφ.1.lift β (P.A.hom ≫ x) (by rw [w, Category.assoc])
    have e₁ : α ≫ φ = β := hφ.1.lift_fst _ _ _
    have e₂ : α ≫ A.hom = P.A.hom ≫ x := hφ.1.lift_snd _ _ _
    refine ⟨P, α, hg, IsGrpPullback.cancel hφ (hβ.congr rfl e₁.symm) e₂, ?_⟩
    have h1 : LBIso P.L (L.pull (α ≫ φ)) := by rw [e₁]; exact hPL
    exact LBIso.trans P.isLB (pull_isLB hL _) (pull_isLB hL' α) h1
      (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL φ) α) (pull_isLB hL' α)
        (lbIso_pull_comp hL φ α) (RigidBundleGlue.LBIso.pull hLL'.symm α))
  · rintro R' _ i ⟨P, α, hg, hα, hPL⟩
    obtain ⟨P', ψ, hg', hψ, hPL'⟩ := exists_isPolFibre polBaseChange_holds i P
    refine ⟨P', ψ ≫ α, hg'.trans hg, hψ.comp hα, ?_⟩
    exact LBIso.trans P'.isLB (pull_isLB P.isLB ψ) (pull_isLB hL' _) hPL'.symm
      (LBIso.trans (pull_isLB P.isLB ψ) (pull_isLB (pull_isLB hL' α) ψ) (pull_isLB hL' _)
        (RigidBundleGlue.LBIso.pull hPL ψ) (lbIso_pull_comp hL' α ψ).symm)

end GlobalTheory.UMin.FibMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductTorusFactorAppellHumbert
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.PullHermitian in

theorem GlobalTheory.TorusRM.char_axis_eq_one_of_herm_axis_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L₀ : LB A.left) (g : ℕ) (u : HolUnif A L₀ g)
    (L : LB (A ⊗ A).left), L.IsLB → HasGen (L.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
    ∀ (U : HolUnif (A ⊗ A) L (g + g)) (H : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) (χ' : U.Λ → ℂ),
    (∀ x y, U.ex (Fin.append x y) = lift (u.ex x) (u.ex y)) → GlobalTheory.TorusRM.IsFactorAH U H χ' →
    (∀ z w : Fin g → ℂ, hermForm H (Fin.append z 0) (Fin.append w 0) = 0) →
    ∀ (m : U.Λ) (l : Fin g → ℂ), (m : Fin (g + g) → ℂ) = Fin.append l 0 → χ' m = 1 := by
  intro A _ L₀ g u L hL ht0 U H χ' hU hF hH0 m l hm
  set φ := (lift (𝟙 A) (1 : A ⟶ A)).left with hφ
  obtain ⟨t, ht⟩ := ht0
  have e0 : u.ex 0 = 1 := by
    have h := u.ex_add 0 0
    simpa using h
  have comp1 : ∀ {X : Over (Sp ℂ)} (f : X ⟶ A), f ≫ (1 : A ⟶ A) = 1 := fun f => by
    rw [Hom.one_def, Hom.one_def]; simp
  have hx : ∀ z, (U.ex (Fin.append z 0)).left = (u.ex z).left ≫ φ := fun z => by
    rw [hU, e0, hφ, ← Over.comp_left, comp_lift, Category.comp_id, comp1]
  have hmem : ∀ l' : Fin g → ℂ, Fin.append l' 0 ∈ U.Λ ↔ l' ∈ u.Λ := by
    intro l'
    rw [← U.ker, ← u.ker, hU, e0]
    constructor
    · intro h
      have := congrArg (· ≫ fst A A) h
      simpa using this
    · intro h
      rw [h]
      first | simp | (ext <;> simp) | rfl
  have hper : ∀ (l' : u.Λ) z, u.ex (z + l') = u.ex z := fun l' z => by
    rw [u.ex_add, (u.ker l').2 l'.2, _root_.mul_one]
  have happ : ∀ z w : Fin g → ℂ, Fin.append z 0 + Fin.append w 0 = Fin.append (z + w) (0 : Fin g → ℂ) := by
    intro z w
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left, Pi.add_apply]
    · simp only [Fin.append_right, Pi.add_apply, Pi.zero_apply, add_zero]
  have hapd : Differentiable ℂ (fun z : Fin g → ℂ => Fin.append z (0 : Fin g → ℂ)) := by
    refine differentiable_pi.2 fun i => ?_
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using differentiable_apply j
    · simpa only [Fin.append_right, Pi.zero_apply] using differentiable_const (0 : ℂ)
  set V : L.ι → Set (Fin g → ℂ) := fun p => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.pull φ).U (fun _ => p)} with hV
  have hVsub' : ∀ p z, z ∈ V p → ⊤ ≤ ((u.ex z).left ≫ φ) ⁻¹ᵁ L.U p := fun p z hz q hq =>
    Set.mem_iInter.1 (hz hq) PUnit.unit
  have hVsub : ∀ p z, z ∈ V p → ⊤ ≤ (U.ex (Fin.append z 0)).left ⁻¹ᵁ L.U p := fun p z hz => by
    rw [hx]; exact hVsub' p z hz
  have hVof : ∀ p z, ⊤ ≤ (U.ex (Fin.append z 0)).left ⁻¹ᵁ L.U p → z ∈ V p := fun p z h =>
    wchart_of (u.ex z).left L φ p (hx z ▸ h)
  obtain ⟨r, hr, hrφ⟩ := exists_glue V
    (fun p => (u.hol _ 0).1)
    (fun z => by
      obtain ⟨p, hp⟩ := exists_chart (U.ex (Fin.append z 0)).left hL
      exact ⟨p, hVof p z hp⟩)
    (fun p z => valAt' (u.ex z).left ((L.pull φ).U (fun _ => p)) (t.s (fun _ => p)).val /
      U.fr p (Fin.append z 0))
    (fun p => by
      have d1 := (u.hol ((L.pull φ).U (fun _ => p)) (t.s (fun _ => p)).val).2
      have d2 : DifferentiableOn ℂ (fun z => U.fr p (Fin.append z 0)) (V p) := (U.fr_hol p).comp (s := V p) hapd.differentiableOn fun z hz => hVsub p z hz
      simp only [div_eq_mul_inv]
      exact d1.mul (d2.inv fun z hz => U.fr_ne p _ (hVsub p z hz)))
    (fun p q z hp hq => by
      have hpq := inf_of (u.ex z).left hp hq
      have h1 := ht (fun _ => p) (fun _ => q)
      have h2 := congrArg (unitVal (u.ex z).left hpq) h1
      rw [map_mul, unitVal_res (u.ex z).left _ hpq hp, unitVal_res (u.ex z).left _ hpq hq] at h2
      have h3 := unitVal_linComb (u.ex z).left L φ 1 p q hpq (inf_of _ (hVsub' p z hp) (hVsub' q z hq))
      have h4 := U.fr_compat p q (Fin.append z 0) (inf_of _ (hVsub p z hp) (hVsub q z hq))
      rw [hx] at h4
      rw [valAt'_eq_unitVal _ hp, valAt'_eq_unitVal _ hq, h4,
        valAt'_eq_unitVal _ (inf_of _ (hVsub' p z hp) (hVsub' q z hq)), h2, h3]
      have h5 := U.fr_ne q _ (hVsub q z hq)
      simp only [Units.val_mul, zpow_one]
      field_simp)
  haveI := u.discrete
  have key := appellHumbert_trivial_of_nowhere_vanishing g u.Λ u.full 0
    (fun l' => χ' ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩) r Matrix.isHermitian_zero
    (fun l' => hF.2.1 _) hr
    (fun z => by
      obtain ⟨p, hp⟩ := exists_chart (U.ex (Fin.append z 0)).left hL
      have hp' := hVof p z hp
      rw [hrφ p z hp', valAt'_eq_unitVal _ hp']
      exact div_ne_zero (Units.ne_zero _) (U.fr_ne p _ hp))
    (fun l' z => by
      obtain ⟨p, hp⟩ := exists_chart (U.ex (Fin.append z 0)).left hL
      have hz := hVof p z hp
      have hz' : z + l' ∈ V p := by
        show ⊤ ≤ (u.ex (z + l')).left ⁻¹ᵁ _
        rw [hper]; exact hz
      rw [hrφ p _ hz', hrφ p z hz, hper]
      have hf := hF.2.2 ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩ p (Fin.append z 0) hp
      have e1 : Fin.append z 0 ⬝ᵥ H.mulVec (star (Fin.append (l' : Fin g → ℂ) 0)) = 0 := hH0 z l'
      have e2 : Fin.append (l' : Fin g → ℂ) 0 ⬝ᵥ H.mulVec (star (Fin.append (l' : Fin g → ℂ) 0)) = 0 :=
        hH0 l' l'
      simp only [e1, e2, mul_zero, add_zero, Complex.exp_zero, _root_.mul_one, happ] at hf
      have hc : χ' ⟨Fin.append (l' : Fin g → ℂ) 0, (hmem _).2 l'.2⟩ ≠ 0 :=
        norm_ne_zero_iff.1 (by rw [hF.2.1]; exact one_ne_zero)
      have h6 := U.fr_ne p _ (hVsub p _ hz')
      simp only [hermForm, Matrix.zero_mulVec, dotProduct_zero, mul_zero, add_zero, Complex.exp_zero,
        _root_.mul_one]
      rw [hf]
      field_simp)
  have hm' : m = ⟨Fin.append l 0, hm ▸ m.2⟩ := Subtype.ext hm
  rw [hm']
  exact key.2.1 ⟨l, (hmem l).1 (hm ▸ m.2)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsBasicProperties
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.CrdBasic

theorem pCrd_basic : (∀ (o R R' : Type) [CommRing o] [CommRing R] [CommRing R'] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (i : R →+* R'), PCrd x v → PCrd (spMap i ≫ x) (fun j => i (v j))) ∧ (∀ (o R : Type) [CommRing o] [CommRing R] (n : ℕ) (x : Sp R ⟶ PSpace o n) (v : Fin (n + 1) → R) (a : R), IsUnit a → PCrd x v → PCrd x (fun j => a * v j)) ∧ ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n), (∃ v, PCrd x v) ∧ ∀ v, PCrd x v → ∃ j, v j ≠ 0 := by
  refine ⟨fun o R R' _ _ _ n x v i h => ?_, fun o R _ _ n x v a ha h => ?_, fun o K _ _ n x => ⟨?_, fun v h => ?_⟩⟩
  · exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) h).1 R' i
  · exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) h).2.1 ha.unit
  · exact GlobalTheory.ZM.FieldPoint.exists_secCoord o n K x
  · obtain ⟨c, hc⟩ := RepUniq.exists_spMap (x ≫ PSpace.str o n)
    obtain ⟨hv, -⟩ := GlobalTheory.ZM.ProjExt.eq_pt_of_secCoord c x hc v h
    by_contra h0
    push_neg at h0
    have : Ideal.span (Set.range v) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨j, rfl⟩
      exact h0 j
    rw [this] at hv
    exact bot_ne_top hv

end GlobalTheory.UMin.CrdBasic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveHomogeneousCoordsFieldDetermineDescend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.CrdUniq

theorem exists_spMap' {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ c : A →+* B, spMap c = f :=
  ⟨(Spec.preimage f).hom, by simp [spMap]⟩

theorem pCrd_iff {o R : Type} [CommRing o] [CommRing R] {n : ℕ} (x : Sp R ⟶ PSpace o n) (c : o →+* R)
    (hx : x ≫ PSpace.str o n = spMap c) (v : Fin (n + 1) → R) :
    PCrd x v ↔ ∃ hv : Ideal.span (Set.range v) = ⊤, x = ProjSpace.pt c v hv := by
  have h := ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) c x (by rw [Category.comp_id]; exact hx) v
  have h2 := RepBC.secCoord_pull (ProjSpace.O1 o n) (ProjSpace.coord o n) (𝟙 _) x v
  rw [Category.comp_id] at h2
  simp only [Equiv.refl_symm, Equiv.coe_refl, Function.comp_id, Category.comp_id] at h
  exact h2.symm.trans h

theorem eq_of_pCrd {o R : Type} [CommRing o] [CommRing R] {n : ℕ} {x x' : Sp R ⟶ PSpace o n} {v : Fin (n + 1) → R}
    (hs : x ≫ PSpace.str o n = x' ≫ PSpace.str o n) (h : PCrd x v) (h' : PCrd x' v) : x = x' := by
  obtain ⟨c, hc⟩ := exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, e⟩ := (pCrd_iff x c hc.symm v).1 h
  obtain ⟨hv', e'⟩ := (pCrd_iff x' c (hs ▸ hc.symm) v).1 h'
  rw [e, e']

theorem exists_ne_zero_of_pCrd {o K : Type} [CommRing o] [Field K] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v : Fin (n + 1) → K} (h : PCrd x v) : ∃ k, v k ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_spMap' (x ≫ PSpace.str o n)
  obtain ⟨hv, -⟩ := (pCrd_iff x c hc.symm v).1 h
  by_contra hn
  push_neg at hn
  have : Set.range v ⊆ {0} := by rintro _ ⟨k, rfl⟩; exact hn k
  have h0 : Ideal.span (Set.range v) = ⊥ := by
    rw [Ideal.span_eq_bot]; intro y hy; exact this hy
  rw [h0] at hv
  exact bot_ne_top hv

theorem scalar_of_pCrd {o K : Type} [CommRing o] [Field K] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v w : Fin (n + 1) → K} (hv : PCrd x v) (hw : PCrd x w) : ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j := by
  obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hv).2.2 w hw
  exact ⟨u, u.ne_zero, hu⟩

theorem pCrd_of_map {o K K' : Type} [CommRing o] [Field K] [Field K'] {n : ℕ} {x : Sp K ⟶ PSpace o n}
    {v : Fin (n + 1) → K} (i : K →+* K') (h : PCrd (spMap i ≫ x) (fun j => i (v j))) : PCrd x v := by
  obtain ⟨w, hw⟩ := FieldPoint.exists_secCoord o n K x
  have hw' := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw).1 K' i
  obtain ⟨u, hu⟩ := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw').2.2 _ h
  obtain ⟨k, hk⟩ := exists_ne_zero_of_pCrd h
  have hvk : v k ≠ 0 := fun e => hk (by simp only [e, map_zero])
  have hwk : w k ≠ 0 := fun e => hk (by rw [hu k]; simp only [e, map_zero, mul_zero])
  have hua : (u : K') = i (v k / w k) := by
    rw [map_div₀, eq_div_iff ((map_ne_zero i).2 hwk), hu k]
  have hvj : ∀ j, v j = (v k / w k) * w j := fun j => by
    apply i.injective
    rw [hu j, hua, map_mul]
  have hs := (Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ (ProjSpace.O1_isLB o n) hw).2.1
    (Units.mk0 (v k / w k) (div_ne_zero hvk hwk))
  have e : (fun j => ((Units.mk0 (v k / w k) (div_ne_zero hvk hwk) : Kˣ) : K) * w j) = v :=
    funext fun j => (hvj j).symm
  rw [e] at hs
  exact hs

theorem main : (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x x' : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K), x ≫ PSpace.str o n = x' ≫ PSpace.str o n → PCrd x v → PCrd x' v → x = x') ∧ (∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v w : Fin (n + 1) → K), PCrd x v → PCrd x w → ∃ a : K, a ≠ 0 ∧ ∀ j, w j = a * v j) ∧ ∀ (o K K' : Type) [CommRing o] [Field K] [Field K'] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (i : K →+* K'), PCrd (spMap i ≫ x) (fun j => i (v j)) → PCrd x v :=
  ⟨fun _ _ _ _ _ _ _ _ hs h h' => eq_of_pCrd hs h h',
   fun _ _ _ _ _ _ _ _ hv hw => scalar_of_pCrd hv hw,
   fun _ _ _ _ _ _ _ _ _ i h => pCrd_of_map i h⟩

end GlobalTheory.UMin.CrdUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUniv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullDegTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem psi_val_on {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') {W : (Sp R).Opens}
    (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) (x : D'.X) (z : (TK R').left)
    {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (ψW.psi (h.xe x)) g z J = (om h.w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J' := by
  have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
  have ag : val (ψW.psi (h.xe x)) g z J = val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J :=
    ArcSpecialise.psiOn_agree ψW h.psiW _ _ _ (by rw [hg, Category.id_comp, h.g_comm]) hJ
  change _ = (om h.w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ * _ at v
  rw [ag, v, Category.id_comp]

def reopen {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') {W : (Sp R).Opens}
    (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) : IsPullDeg φ D D' :=
  { h with
    W := W
    psiW := ψW
    g := g
    g_comm := hg
    psi_pr := fun x => by
      obtain ⟨b, hb, hc⟩ := h.psi_pr x
      refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc (𝟙 _)).trans ?_⟩
      rw [val_pull hJ, val_pull hJ]
      exact ArcSpecialise.psiOn_agree h.psiW ψW _ _ _ (by
        rw [Category.id_comp, Category.id_comp, hg, h.g_comm]) hJ }

theorem exists_top {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D')
    (hU : ∀ y, PsiUnitOn D y Set.univ) : ∃ h' : IsPullDeg φ D D', h'.W = ⊤ ∧ proj h' = proj h ∧ h'.xe = h.xe := by
  obtain ⟨ψ⟩ := nonempty_psiOn_top D hU
  exact ⟨reopen h ψ ((jK R' ≫ specOf φ) ≫ (Sp R).topIso.inv) (by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]), rfl, rfl, rfl⟩

theorem psiUnitOn_univ {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D')
    (hU : ∀ y, PsiUnitOn D y Set.univ) (x : D'.X) : PsiUnitOn D' x Set.univ := by
  obtain ⟨h', hW, -, -⟩ := exists_top h hU
  obtain ⟨ψ, -⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull h'
  have := GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn _ _ _ ψ x
  rw [hW] at this
  exact this

theorem act_iff {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') (f : D.P.A ⟶ D.P.A)
    (f' : D'.P.A ⟶ D'.P.A) :
    f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf φ)).map f ↔ f'.left ≫ proj h = proj h ≫ f.left := by
  have a : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := by
    simp [Over.pullback_map_left, pullback.lift_fst]
  constructor
  · intro H
    have := congrArg (fun q => q.left ≫ pullback.fst D.P.A.hom (specOf φ)) H
    simp only [Over.comp_left, Category.assoc] at this
    rw [a] at this
    exact this.trans (Category.assoc _ _ _).symm
  · intro H
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [a]
      exact H.trans (Category.assoc _ _ _)
    · exact (Over.w (f' ≫ h.e.hom)).trans (Over.w (h.e.hom ≫ (Over.pullback (specOf φ)).map f)).symm

theorem exists_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p₀ : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hU : ∀ y, PsiUnitOn D y Set.univ) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p₀ ∧ ∀ x, r.xe x = p₀.xe (q.xe x) := by
  obtain ⟨p, hW, e₁, e₂⟩ := exists_top p₀ hU
  rw [← e₁, ← e₂]
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ, hv⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg' : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg' gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := psi_val_on q ψ g hg x z hJ' hJ''
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg, Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

theorem exists_cancel {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} {θ : R₀ →+* R₂} (hθ : β.comp α = θ)
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂}
    (h₀ : IsPullDeg α D₀ D₁) (h : IsPullDeg θ D₀ D) (hU : ∀ y, PsiUnitOn D₀ y Set.univ) :
    ∃ h' : IsPullDeg β D₁ D, proj h' ≫ proj h₀ = proj h ∧ ∀ x, h₀.xe (h'.xe x) = h.xe x := by
  subst hθ
  obtain ⟨h₁, hW₁, e₁', e₂'⟩ := exists_top h₀ hU
  rw [← e₁', ← e₂']
  have hW : specOf α ⁻¹ᵁ h₁.W = ⊤ := by rw [hW₁]; rfl
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW, hv⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull h₁
  obtain ⟨g, hg⟩ : ∃ g : (TK R₂).left ⟶ (specOf α ⁻¹ᵁ h₁.W).toScheme,
      g ≫ (specOf α ⁻¹ᵁ h₁.W).ι = jK R₂ ≫ specOf β :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨hD, k₁, k₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW D₁ D ψW g hg gp w hw hr xe hc
    (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ₀ hJ
    have v₁ := hv (xe x) _ g z J₀ J₁ hJ₀ hJ₁
    have ag : val (h₁.psiW.psi (h.xe x)) (g ≫ (specOf α ∣_ h₁.W)) z J₀ =
        val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J₀ :=
      ArcSpecialise.psiOn_agree h₁.psiW h.psiW _ _ _ (by
        rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, Category.id_comp, h.g_comm, Category.assoc]
        exact congrArg (jK R₂ ≫ ·) sc) hJ₀
    have hx : D.xK x ≫ Φ = g ≫ (specOf α ⁻¹ᵁ h₁.W).ι ≫ (D₁.c (xe x)).left := by
      show (jK R₂ ≫ (D.c x).left) ≫ Φ = _
      rw [Category.assoc, hc, ← Category.assoc g, hg, Category.assoc]
    change _ = (om h.w z J₀ J (𝟙 _ ≫ D.xK x))⁻¹ * _ at v
    rw [hxe, ag, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD, by rw [k₁, e₁], fun x => by rw [k₂, hxe]⟩

theorem main : (∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (_ : IsPullDeg φ D D'), (∀ y, PsiUnitOn D y Set.univ) → ∀ x, PsiUnitOn D' x Set.univ) ∧ (∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') (f : D.P.A ⟶ D.P.A) (f' : D'.P.A ⟶ D'.P.A), f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf φ)).map f ↔ f'.left ≫ h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = (h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ f.left) ∧ (∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), (∀ y, PsiUnitOn D y Set.univ) → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x)) ∧ (∀ {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} {θ : R₀ →+* R₂}, β.comp α = θ → ∀ {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂} (h₀ : IsPullDeg α D₀ D₁) (h : IsPullDeg θ D₀ D), (∀ y, PsiUnitOn D₀ y Set.univ) → ∃ h' : IsPullDeg β D₁ D, (h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf β)) ≫ h₀.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf α) = h.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ) ∧ ∀ x, h₀.xe (h'.xe x) = h.xe x) :=
  ⟨fun h hU x => psiUnitOn_univ h hU x, fun h f f' => act_iff h f f', fun p q hU => exists_comp p q hU,
    fun e _ _ _ h₀ h hU => exists_cancel e h₀ h hU⟩

end GlobalTheory.PullDegTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientAbelianSchemeDescendsStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_abelian_scheme_descends : ∀ (A₀ : Over (Sp Qb)) [GrpObj A₀] (A X : Over (Sp ℂ)) [GrpObj A] [GrpObj X] (p : A.left ⟶ A₀.left) (g : ℕ),
    IsAbelianScheme A₀ → SmoothOfRelativeDimension g A₀.hom → IsGrpPullback A A₀ (spMap (algebraMap Qb ℂ)) p →
    IsAbelianScheme X → SmoothOfRelativeDimension g X.hom → ∀ ψ : A ⟶ X, IsMonHom ψ →
    (∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ X, ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = y) →
  ∃ (X₀ : Over (Sp Qb)) (_ : GrpObj X₀) (q : X.left ⟶ X₀.left), IsAbelianScheme X₀ ∧ SmoothOfRelativeDimension g X₀.hom ∧
    IsGrpPullback X X₀ (spMap (algebraMap Qb ℂ)) q := by
  first | exact @GlobalTheory.IsogModel.exists_model_of_surjective | exact GlobalTheory.IsogModel.exists_model_of_surjective | (intros; apply GlobalTheory.IsogModel.exists_model_of_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSquaringPathsRigidOfFibreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSquaringPathsRigid_of_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], ∀ (Ω : Type) [Field Ω] [CharZero Ω] (b : Sp Ω ⟶ S), RatRigid ((Over.pullback b).obj G) (𝟙 (Sp Ω)) → RatRigid G b := by
  first | exact @GlobalTheory.Nef.ratRigid_of_fibre | exact GlobalTheory.Nef.ratRigid_of_fibre | (intros; apply GlobalTheory.Nef.ratRigid_of_fibre <;> assumption)
end

