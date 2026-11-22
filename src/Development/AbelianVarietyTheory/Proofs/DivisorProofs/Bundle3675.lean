import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3673
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3651
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3666
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationThetaEquivariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemClassSumsUnboundedLevelsOneInde
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeCardKernelEqNormPowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_card_kernel_eq_norm_pow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (h ℓ : ℕ), ℓ.Prime → (ℓ : k) ≠ 0 → (∀ j : ℕ, ∃ f : (Fin h → 𝓞 F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) → (Over.mk x ⟶ A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 F)}) c • a) = f a ≫ act.act c) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g) → ∀ c : 𝓞 F, c ≠ 0 → (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → Nat.card {g : Over.mk x ⟶ A // g ≫ act.act c = 1} = (Algebra.norm ℤ c).natAbs ^ h := by
  first | (exact @GlobalTheory.AVCount.card_ker_eq_norm_pow) | (exact GlobalTheory.AVCount.card_ker_eq_norm_pow) | (intros; apply GlobalTheory.AVCount.card_ker_eq_norm_pow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelNefOfAmpleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHilbertSamuel_nef_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → GlobalTheory.Published.ArithHilbertSamuel := by
  first | exact @GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS | exact GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS | (intros; apply GlobalTheory.HSNef.arithHilbertSamuel_of_ampleHS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantRatio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConstRatio

theorem bottomTri_factor (hPr : GlobalTheory.FunPr.Hypotheses₂) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) (hL : LNe) :
    GBig fun {D} T _ _ G _ _ _ _ => ∀ W : G.Weil, IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri T A A' WW), IsBottomTri W i j X → ∃ lam : T → ℂ, GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam := by
  obtain ⟨c, h⟩ := GlobalTheory.T.bottom_triangle_polynomial_surjection hPr.minguezThetaGL hPr hK hM
  obtain ⟨c', h'⟩ := GlobalTheory.T.bottom_triangle_integrals_ne_zero hPr hK hM hL
  refine ⟨max c c', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  refine ⟨max C0 C1, max x0 x1, fun C hC D large₂ a b r T Lc μ hLc G W hW i j A A' WW X hX => ?_⟩
  obtain ⟨Pi, p, p', J, hs, hJ, hlam, hI'⟩ :=
    h C (le_of_max_le_left hC) D large₂ a (le_of_max_le_left b) r T Lc μ hLc G W hW i j A A' WW X hX
  have hnv := h' C (le_of_max_le_right hC) D large₂ a (le_of_max_le_right b) r T Lc μ hLc G W i j A A' WW X hX
  obtain ⟨P', g', hg'⟩ := (hnv μ).2
  have hP' : p' P' ≠ 0 := fun h0 => hg' (by rw [hI' μ P', h0]; simp)
  choose lam hlam using hlam
  have key : ∀ t, lam t ≠ 0 ∧ Function.Injective (J t) := fun t => by
    obtain ⟨P, g, hPg⟩ := (hnv t).1
    rw [hlam t P] at hPg
    refine ⟨fun h0 => hPg (by simp [h0]), (hJ t).resolve_left fun h0 => hPg (by simp [h0])⟩
  refine ⟨lam, fun t => (key t).1, Pi, p, p', J, hs, fun t => (key t).2, fun t P g => (hX.integrable t).1 P g,
    fun t P => hlam t P, fun t P' _ => hI' t P', P', hP', fun t g => (hX.integrable t).2 P' g⟩

end GlobalTheory.ConstRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyPullbackLocalUniformised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.CanonPull

theorem lam_isLB {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) :
    (abelian₂ G L).IsLB :=
  ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _

end GlobalTheory.Mum.CanonPull

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mum.canon_pull_unif : ∀ (R V' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V'] [IsDomain V'] [IsLocalRing V'] (θ : R →+* V'), IsCN R → IsCN V' → IsLocalHom θ → ∀ (Q : Data R) (W : (Sp R).Opens) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (P : LB (G2 G₁).left), IsSemiAbelian G₁ → CanonOn Q W G₁ P → spMap θ (genericPoint (Sp V')) ∈ W → ∀ (D' : DegData V' (maximalIdeal V')) (ex : D'.toPre.X ≃+ Q.X), PullData Q θ (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex → ∃ (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (π₂ : (G2 G').left ⟶ (G2 G₁).left) (A : PolAV (Sp (FractionRing V'))) (U : Unif (maximalIdeal V') D' A G'), IsGrpPullback G' G₁ (spMap θ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂)
:= by
  intro R V' _ _ _ _ _ _ θ hR hV hθ Q W G₁ _ _ P hG hC hW D' ex hP
  obtain ⟨hPl, D₀, F, A₀, G₀, i₀, c₀, U₀, oA, oG, inc, pr, hψ, hG₀, lin, mi, mp, hip, hpi, hL⟩ := hC
  have bR : Base R := ⟨⟨hR.1, inferInstance, hR.2.1, hR.2.2.1⟩, hR.2.2.2⟩
  have bV : Base V' := ⟨⟨hV.1, inferInstance, hV.2.1, hV.2.2.1⟩, hV.2.2.2⟩
  obtain ⟨D₁, hD, A₁, U₁, m, o₁, oA₁, oG₁, hL₁, hx, ho, ha, lin₁⟩ :=
    GlobalTheory.T.linearUniformisation_pullback_localHom R V' θ bR bV hθ D₀ A₀ G₀ hG₀ U₀ F.O F.o oA oG lin W hψ hW
  obtain ⟨β, gβ, hc, H⟩ := GlobalTheory.T.polarisedIdempotentFactor_pairing_periods_pullback R V' θ Q D₀.toPre F D₁.toPre hD o₁ hx ho (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex hP
  obtain ⟨inc', pr', xi, xp, h₁, h₂, b₁, b₂, b₃, b₄, b₅, b₆, b₇, b₈, b₉⟩ :=
    GlobalTheory.T.polarisedFactor_algebraic_part_pullback R V' θ Q D₀.toPre F D₁.toPre hD o₁ hx ho (GlobalTheory.PolDeg.Wit.ofDeg D'.toPre D'.tau_bimult) ex β gβ hc
  obtain ⟨w, hw, hτ⟩ := H inc' xi h₁ h₂ b₇
  let F₁ : Factor D'.toPre D₁.toPre :=
    { O := F.O, o := o₁, e := F.e, f := F.f, inc := inc', pr := pr', xi := xi, xp := xp, w := w, idem := F.idem,
      inc_hom := b₁, pr_hom := b₂, inc_pr := b₃, pr_inc := b₄, xp_xi := b₅, xi_xp := b₆, c_xi := b₇, inj := b₈,
      onto := b₉, w_gen := hw,
      tau := fun a b z J J' hJ hJ' =>
        ((GlobalTheory.PolDeg.Wit.exists_tau D'.toPre a b).choose_spec.2 _ _ z J' hJ').symm.trans (hτ a b z J J' hJ hJ') }
  obtain ⟨π₂, sq, hl⟩ := GlobalTheory.T.mumfordPairingRetract_baseChange _ _ (specOf θ) G₁ G₀ inc (oG.act F.f) U₀.LG.L U₁.LG.L P U₀.LG.isLB U₁.LG.isLB hPl hL₁ hL
  obtain ⟨A, U, hU⟩ := GlobalTheory.T.idempotent_image_uniformised_by_factor_data V' bV D' D₁ F₁ F.alg A₁ _ (IsSemiAbelian.pullback _ G₀ hG₀) U₁ oA₁ oG₁ lin₁
    ((Over.pullback (specOf θ)).obj G₁) (IsSemiAbelian.pullback _ G₁ hG) ((Over.pullback (specOf θ)).map inc)
    ((Over.pullback (specOf θ)).map pr) inferInstance inferInstance
    (by rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id])
    (by rw [← CategoryTheory.Functor.map_comp, hpi]; exact (ha _).symm)
  refine ⟨(Over.pullback (specOf θ)).obj G₁, inferInstance, inferInstance, _, π₂, A, U, isGrpPullback_pullback G₁ (specOf θ), sq, ?_⟩
  rw [show oG₁.act F₁.f = (Over.pullback (specOf θ)).map (oG.act F.f) from ha _] at hU
  exact LBIso.trans (GlobalTheory.Mum.CanonPull.lam_isLB _ U.LG.isLB)
    (pull_isLB (GlobalTheory.Mum.CanonPull.lam_isLB _ U₁.LG.isLB) _) (pull_isLB hPl _) hU hl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalMumfordFamilyUniformisesRefinements
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum.CanonFam

theorem gm_iso {X : Scheme.{0}} {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (x : X) (p q : B.ι × A.ι)
    (hp : x ∈ B.U p.1 ⊓ A.U p.2) (hq : x ∈ B.U q.1 ⊓ A.U q.2) :
    gm (𝟙 X) x _ (w.s p) =
      gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ * gm (𝟙 X) x _ (w.s q) := by
  have hm : (𝟙 X : X ⟶ X) x ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2) := ⟨hp, hq⟩
  have e := congrArg (gm (𝟙 X) x (B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2))) (hw p q)
  exact (gm_res _ x _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) x p q hm) (gm_res _ x _ hm _))))

theorem lbIso_trans {X : Scheme.{0}} {A B C : LB X} (hA : A.IsLB) (hB : B.IsLB) (H : LBIso A B) (H' : LBIso B C) :
    LBIso A C := by
  obtain ⟨w, hw⟩ := H
  obtain ⟨w', hw'⟩ := H'

  have cself : ∀ (x : X) (r : C.ι) (p : B.ι), x ∈ C.U r → x ∈ B.U p →
      gm (𝟙 X) x (C.U r ⊓ C.U r) (C.g r r) = 1 := by
    intro x r p hr hp
    have e := gm_iso hw' x (r, p) (r, p) ⟨hr, hp⟩ ⟨hr, hp⟩
    rw [gm_self hB (𝟙 X) x hp, inv_one, _root_.mul_one] at e
    exact mul_eq_right.1 e.symm
  have glue : ∀ (r : C.ι) (i : A.ι), ∃ s : Γ(X, C.U r ⊓ A.U i)ˣ, ∀ (x : X) (p : B.ι), x ∈ C.U r → x ∈ B.U p →
      x ∈ A.U i → gm (𝟙 X) x _ s = gm (𝟙 X) x _ (w'.s (r, p)) * gm (𝟙 X) x _ (w.s (p, i)) := by
    intro r i
    let W : B.ι → X.Opens := fun p => C.U r ⊓ B.U p ⊓ A.U i
    have l₀ : ∀ p, W p ≤ C.U r ⊓ A.U i := fun p x hx => ⟨hx.1.1, hx.2⟩
    have l₁ : ∀ p, W p ≤ C.U r ⊓ B.U p := fun p x hx => hx.1
    have l₂ : ∀ p, W p ≤ B.U p ⊓ A.U i := fun p x hx => ⟨hx.1.2, hx.2⟩
    let u : ∀ p, Γ(X, W p)ˣ := fun p => res (l₁ p) (w'.s (r, p)) * res (l₂ p) (w.s (p, i))
    have hu : ∀ (x : X) (p : B.ι) (hx : x ∈ W p), gm (𝟙 X) x (W p) (u p) =
        gm (𝟙 X) x _ (w'.s (r, p)) * gm (𝟙 X) x _ (w.s (p, i)) := fun x p hx =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x (l₁ p) hx _) (gm_res _ x (l₂ p) hx _))
    obtain ⟨s, hs⟩ := glue_unit (C.U r ⊓ A.U i) W l₀ (fun x hx => by
        obtain ⟨p, hp⟩ := exists_chart hB x
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, ⟨⟨hx.1, hp⟩, hx.2⟩⟩) u (fun p p' x hx => by
        rw [hu x p hx.1, hu x p' hx.2]
        have hr : x ∈ C.U r := hx.1.1.1
        have hp : x ∈ B.U p := hx.1.1.2
        have hp' : x ∈ B.U p' := hx.2.1.2
        have hi : x ∈ A.U i := hx.1.2
        rw [gm_iso hw' x (r, p) (r, p') ⟨hr, hp⟩ ⟨hr, hp'⟩, gm_iso hw x (p, i) (p', i) ⟨hp, hi⟩ ⟨hp', hi⟩]
        simp only []
        rw [cself x r p hr hp, gm_self hA (𝟙 X) x hi, inv_one]
        simp only [_root_.one_mul, _root_.mul_one]
        rw [_root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun x p hr hp hi => ?_⟩
    have hx : x ∈ W p := ⟨⟨hr, hp⟩, hi⟩
    exact (gm_res _ x (l₀ p) hx s).symm.trans ((congrArg (gm (𝟙 X) x (W p)) (hs p)).trans (hu x p hx))
  choose s hs using glue
  refine ⟨⟨fun q => s q.1 q.2⟩, fun q q' => unit_ext fun x hx => ?_⟩
  obtain ⟨p, hp⟩ := exists_chart hB x
  have hr : x ∈ C.U q.1 := hx.1.1
  have hi : x ∈ A.U q.2 := hx.1.2
  have hr' : x ∈ C.U q'.1 := hx.2.1
  have hi' : x ∈ A.U q'.2 := hx.2.2
  have hm : (𝟙 X : X ⟶ X) x ∈ C.U q.1 ⊓ A.U q.2 ⊓ (C.U q'.1 ⊓ A.U q'.2) := hx
  refine (gm_res _ x _ hx _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A C (𝟙 X) x q q' hm) (gm_res _ x _ hx _))).symm)
  show gm (𝟙 X) x _ (s q.1 q.2) = _ * _ * gm (𝟙 X) x _ (s q'.1 q'.2)
  rw [hs q.1 q.2 x p hr hp hi, hs q'.1 q'.2 x p hr' hp hi',
    gm_iso hw' x (q.1, p) (q'.1, p) ⟨hr, hp⟩ ⟨hr', hp⟩, gm_iso hw x (p, q.2) (p, q'.2) ⟨hp, hi⟩ ⟨hp, hi'⟩]
  simp only []
  rw [gm_self hB (𝟙 X) x hp, inv_one]
  simp only [_root_.one_mul, _root_.mul_one]
  ac_rfl

theorem base_of_isCN {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) : Base R :=
  ⟨⟨h.1, inferInstance, h.2.1, h.2.2.1⟩, h.2.2.2⟩

end GlobalTheory.Mum.CanonFam

open GlobalTheory.Mum.CanonFam in

theorem GlobalTheory.Mum.CanonFam.exists_unif_refines : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsSemiAbelian G → Canon Q G P → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε → ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G.left) (π₂ : (G2 G').left ⟶ (G2 G).left) (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G'), IsGrpPullback G' G (spMap ρ) π ∧ IsSquare π π₂ ∧ LBIso (abelian₂ G' U.LG.L) (P.pull π₂) := by
  intro R _ _ _ hR Q G _ _ P hG hC R' _ _ _ ρ hR' hinj hfin D ε hRef
  obtain ⟨D', F, hF, A', G', _, _, U', oA, oG, G₁, _, _, inc, pr, π, π₂, hG', hlin, hG₁, hinc, hpr, hip, hpi, hpb, hsq,
    hlb⟩ := GlobalTheory.T.refinement_isFactor_baseChange_canonicalMumfordFamily R hR Q G P hG hC R' ρ hR' hinj hfin D ε hRef
  obtain ⟨A, U, hU⟩ := GlobalTheory.T.idempotent_image_uniformised_by_factor_data R' (base_of_isCN hR') D D' F hF A' G' hG' U' oA oG hlin G₁ hG₁ inc pr hinc hpr hip hpi
  refine ⟨G₁, inferInstance, inferInstance, π, π₂, A, U, hpb, hsq, ?_⟩
  have l1 : (abelian₂ G₁ U.LG.L).IsLB := DVR.linComb_isLB _ U.LG.isLB _ _
  have l2 : (abelian₂ G' U'.LG.L).IsLB := DVR.linComb_isLB _ U'.LG.isLB _ _
  exact lbIso_trans l1 (pull_isLB l2 _) hU hlb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerOfLogDerivationChartStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencer_of_logDerivation_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∃ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ := by
  first | exact @GlobalTheory.LogKSChart.exists_isKS_of_logDer | exact GlobalTheory.LogKSChart.exists_isKS_of_logDer | (intros; apply GlobalTheory.LogKSChart.exists_isKS_of_logDer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTrianglePolynomialStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stage_triangle_polynomial : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  first | exact @GlobalTheory.StageSmall.small_stage | exact GlobalTheory.StageSmall.small_stage | (intros; apply GlobalTheory.StageSmall.small_stage <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_zarhin_data : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (B : Over S) (_ : GrpObj B) (_ : IsCommMonObj B) (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A), GlobalTheory.ZarhinFam.ZData c d B Q la mu := by
  first | (exact @GlobalTheory.ZarhinExist.exists_zData) | (exact GlobalTheory.ZarhinExist.exists_zData) | (intros; apply GlobalTheory.ZarhinExist.exists_zData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemClassSumsUnboundedLevelsOneIndeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTermSystem_class_sums_unbounded_levels_one_index : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (W : Matrix (Fin 1) (Fin 1) ℤ) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : O → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), GlobalTheory.GSep.IsAct X₁ act → GlobalTheory.GSep.Deep X₁ act → (∀ m : ℕ, m ≠ 0 → IsUnit (m : X₁.M.Z.presheaf.stalk z₁)) → ∀ (x₀ : X₁.S.Gam) (Φ : VPre bar q W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam) [IsDomain (X₁.M.Z.presheaf.stalk z₁)], GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ lab → Φ.ClassSums (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.GSep.DeepSums.classSums_deeper | exact GlobalTheory.GSep.DeepSums.classSums_deeper | (intros; apply GlobalTheory.GSep.DeepSums.classSums_deeper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftSquareZeroArtinian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.UPel.HT

theorem exists_sqZero_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (t : Sp C ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ t)), ∃ o : GlobalTheory.UPel.HT.Obj b N t, Nonempty (GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)) := by
  intro p _ D R _ b N hN C C₀ _ _ _ _ π hπ hsq' t o₀
  have hsq : RingHom.ker π ^ 2 = 0 := by rw [hsq']; rfl
  obtain ⟨tR, rfl⟩ : ∃ tR : R →+* C, t = spMap tR :=
    ⟨(Spec.preimage t).hom, by simp [spMap]⟩
  obtain ⟨E, hEc, hEf, hEs, hEi, hEl⟩ := GlobalTheory.T.harrisTaylor_exists_isotropic_stable_summand p D R b N C C₀ π hπ hsq tR o₀
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.T.harrisTaylor_exists_lift_orderAction_hodge_summand p D R b N C C₀ π hπ hsq tR o₀ E hEc hEf hEs
  haveI : IsCommMonObj A := hA.comm
  subst hE
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEi
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ := GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hN P φ₂ hP hsq2 hpol
  exact ⟨{ A := A
           ab := hA
           act := act
           P := P
           isLB := hP
           rig₁ := r1
           rig₂ := r2
           symm := hsym
           ample := hamp
           kerP := hker
           rosati := hros
           lie := fun R' _ β x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEl R' β x hx v hv
           lieRank := fun k _ _ x β hx j => GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift p D R b N C C₀ π hπ hsq tR o₀ A i h act hact k x β hx j
           eta := eta
           eta_add := e1
           eta_lin := e2
           eta_ker := e3
           geom := e4 },
    ⟨{ φ := i
       φ₂ := φ₂
       cart := h
       sq := hsq2
       act := hact
       pol := hpol
       eta := e5 }⟩⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsSquareZeroLiftOfFiltrationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_squareZero_lift_of_filtration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (t : Sp C ⟶ Sp R) (t₀ : Sp C₀ ⟶ Sp R), t = spMap tR → t₀ = spMap π ≫ t → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N t₀) (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr e y) → (∀ (c : D.O), ∀ e ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (e)) ∈ E) → (∀ Φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P Φ → ∀ x ∈ E, ∀ y ∈ E, Φ x y = 0) → (∀ e : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - tR b.ρ • e ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ e - ∑ i, w i ∈ E) → ∃ (o : GlobalTheory.UPel.HT.Obj b N t) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), liftFil (divided₂ hsq) m.cart = E := by
  first | (exact @GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil) | (exact GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil) | (intros; apply GlobalTheory.UPel.HT.exists_sqZero_lift_of_fil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorKodairaSpencerDirectionsDimStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_kodairaSpencer_directions_dim : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → KSDim (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  first | (exact @GlobalTheory.HTCount.ksDim_at_point) | (exact GlobalTheory.HTCount.ksDim_at_point) | (intros; apply GlobalTheory.HTCount.ksDim_at_point  <;> assumption)
end

