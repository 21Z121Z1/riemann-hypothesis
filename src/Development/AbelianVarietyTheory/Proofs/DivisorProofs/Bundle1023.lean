import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0987
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0825
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDescentDegreeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0998
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.AwayOrb

variable {p : ℕ} [Fact p.Prime]

def compL (G : HTGroup p) (w : AwayP p) : G.GAf →* UPts G.star (w.1.adicCompletion ℚ) :=
  ubcMap (AfP.eval w)

def coordL (G : HTGroup p) (w : AwayP p) (a : w.1.adicCompletion ℚ ⊗[ℚ] G.C) :
    Fin (Module.finrank ℚ G.C) → w.1.adicCompletion ℚ :=
  (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) (Module.finBasis ℚ G.C)).repr a

def intPts (G : HTGroup p) (w : AwayP p) : Set (UPts G.star (w.1.adicCompletion ℚ)) :=
  {h | (∀ i, coordL G w (((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 :
          (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) i ∈
        w.1.adicCompletionIntegers ℚ) ∧
      (∀ i, coordL G w ((((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1)⁻¹ :
          (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) i ∈
        w.1.adicCompletionIntegers ℚ) ∧
      (((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2 : (w.1.adicCompletion ℚ)ˣ) :
        w.1.adicCompletion ℚ) ∈ w.1.adicCompletionIntegers ℚ ∧
      ((((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2)⁻¹ : (w.1.adicCompletion ℚ)ˣ) :
        w.1.adicCompletion ℚ) ∈ w.1.adicCompletionIntegers ℚ}

example (G : HTGroup p) (w : AwayP p) : compL G w 1 = 1 := map_one _

end GlobalTheory.AwayOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorThetaRefinementProof
section
namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.L2.Ker

theorem coset_refinement : CosetRefinement := by
  intro X A a b S Md _ _ hOdd hLa
  exact indAdd_of A a b S Md hOdd.pos (lattice_classes_finite_refinement X a b S) (indTieD_of_la A a b S Md hOdd.pos hLa)

end GlobalTheory.ColNorms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairUnitVacuumRealPointNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_pair_unit_vacuum_real_point_ne_zero : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (W : G.Weil) {U : Set T} (N : GlobalTheory.FunObj.Std G U) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart W.θ σ → ∀ (t : T) (j : ℕ), j + 1 ≤ D.R.m → ∀ f, IsVacO W.ψ W.θ _ _ (G.cartS W.cart (.top t j)) (G.onT W.cart (.top t j)) (N.latS (.top t j) : Set _) (N.latT (.top t j) : Set _) f → ∃ z : GlobalTheory.FockCompare.RW (G.pT (.top t j)) (G.pS (.top t j)), f (GlobalTheory.FockCompare.iotaW σ (G.pT (.top t j)) (G.pS (.top t j)) z) ≠ 0 := by
  first | exact @GlobalTheory.VacRealForm.vacuum_real_ne_zero | exact GlobalTheory.VacRealForm.vacuum_real_ne_zero | (intros; apply GlobalTheory.VacRealForm.vacuum_real_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeOfPullbackLePowFiniteEtale
section
open CategoryTheory AlgebraicGeometry NumberField MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.DegCmp
variable {X : Scheme.{0}}

theorem pull_pw_g (H : LB X) (φ : X ⟶ X) (t : ℤ) (j j' : PUnit.{1} → H.ι) :
    ((GlobalTheory.AbLaw.pw H t).pull φ).g j j' = ((H.pull φ).g j j') ^ t := by
  simp only [LB.pull, LB.LinComb, GlobalTheory.AbLaw.pw, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  erw [map_zpow, map_zpow]
  rfl

abbrev E (H : LB X) (φ : X ⟶ X) (q : ℕ) : LB X := ReciprocityTheory.ChartRestriction.G.Semi.LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)

def loc (H : LB X) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p : H.ι × (PUnit.{1} → H.ι)) : Γ(X, (E H φ q).U p) :=
  σ.f p ^ t *
    rs X (le_inf le_top inf_le_right : (E H φ q).U p ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2) (GlobalTheory.LB.coord a p.2)

theorem units_id {U₁ U₂ W : X.Opens} (q t : ℕ) (u : Γ(X, U₁)ˣ) (v w : Γ(X, U₂)ˣ) (hw : w = v ^ (t : ℤ))
    (h₁ : W ≤ U₁) (h₂ : W ≤ U₂) :
    (res h₁ (u ^ (q : ℤ)) * (res h₂ v)⁻¹) ^ t * res h₂ w = res h₁ (u ^ ((q * t : ℕ) : ℤ)) := by
  subst hw
  simp only [map_zpow, ← zpow_natCast, mul_zpow, inv_zpow, ← zpow_mul, Nat.cast_mul]
  group

theorem loc_compat (H : LB X) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p p' : H.ι × (PUnit.{1} → H.ι)) :
    rs X (inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p) (loc H φ q t σ a p) =
      rs X (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        ((GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)).g p.1 p'.1).val *
      rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (loc H φ q t σ a p') := by
  have e1 : rs X (inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p) (σ.f p) =
      ((E H φ q).g p p').val *
      rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (σ.f p') := by
    have := GlobalTheory.LB.sec_rel σ p p' (W := (E H φ q).U p ⊓ (E H φ q).U p') inf_le_left inf_le_right le_rfl
    rw [this]
    congr 1
    exact rs_self _ _
  have e2 : rs X (le_inf le_top (inf_le_left.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2) (GlobalTheory.LB.coord a p.2) =
      rs X (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2).val *
      rs X (le_inf le_top (inf_le_right.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2) (GlobalTheory.LB.coord a p'.2) :=
    GlobalTheory.LB.coord_rel a p.2 p'.2 _ _ _
  have key : ((E H φ q).g p p') ^ t *
      res (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2) =
      res (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        (H.g p.1 p'.1 ^ ((q * t : ℕ) : ℤ)) :=
    units_id q t (H.g p.1 p'.1) ((H.pull φ).g p.2 p'.2) _ (pull_pw_g H φ t p.2 p'.2) _ _
  have kv : ((E H φ q).g p p').val ^ t *
      rs X (inf_le_inf inf_le_right inf_le_right :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ((GlobalTheory.AbLaw.pw H t).pull φ).U p.2 ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2)
        (((GlobalTheory.AbLaw.pw H t).pull φ).g p.2 p'.2).val =
      rs X (inf_le_inf inf_le_left inf_le_left : (E H φ q).U p ⊓ (E H φ q).U p' ≤ H.U p.1 ⊓ H.U p'.1)
        ((GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)).g p.1 p'.1).val := by
    have := congrArg Units.val key
    rw [Units.val_mul, Units.val_pow_eq_pow_val] at this
    exact this
  unfold loc
  simp only [map_mul, map_pow, rs_rs]
  rw [e1, e2, mul_pow]
  linear_combination (rs X (inf_le_right : (E H φ q).U p ⊓ (E H φ q).U p' ≤ (E H φ q).U p') (σ.f p')) ^ t *
    rs X (le_inf le_top (inf_le_right.trans inf_le_right) :
        (E H φ q).U p ⊓ (E H φ q).U p' ≤ ⊤ ⊓ ((GlobalTheory.AbLaw.pw H t).pull φ).U p'.2) (GlobalTheory.LB.coord a p'.2) * kv
end GlobalTheory.DegCmp

namespace GlobalTheory.DegCmp
variable {X : Scheme.{0}}

theorem top_le_iSup_E {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q : ℕ) : (⊤ : X.Opens) ≤ ⨆ p, (E H φ q).U p := by
  intro x _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (trivial : x ∈ (⊤ : X.Opens)))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (trivial : φ x ∈ (⊤ : X.Opens)))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, fun _ => j), hi, Set.mem_iInter.2 fun _ => hj⟩

theorem existsUnique_img {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) :
    ∃! b : SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤, ∀ p : H.ι × (PUnit.{1} → H.ι),
      rs X (le_inf le_top inf_le_left : (E H φ q).U p ≤ ⊤ ⊓ H.U p.1) (GlobalTheory.LB.coord b p.1) = loc H φ q t σ a p :=
  SecOn.existsUnique_of_local (isLB_pw hH ((q * t : ℕ) : ℤ)) (fun p : H.ι × (PUnit.{1} → H.ι) => (E H φ q).U p) (fun _ => le_top)
    (top_le_iSup_E hH φ q) (fun p => p.1) (fun _ => inf_le_left) (loc H φ q t σ a)
    (fun p p' => loc_compat H φ q t σ a p p')

def img {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) : SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ :=
  (existsUnique_img hH φ q t σ a).exists.choose

theorem img_spec {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (a : SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) (p : H.ι × (PUnit.{1} → H.ι)) :
    rs X (le_inf le_top inf_le_left : (E H φ q).U p ≤ ⊤ ⊓ H.U p.1) (GlobalTheory.LB.coord (img hH φ q t σ a) p.1) =
      loc H φ q t σ a p :=
  (existsUnique_img hH φ q t σ a).exists.choose_spec p

def imgLin {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q)) :
    SecOn ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤ →ₗ[Γ(X, ⊤)] SecOn (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ where
  toFun := img hH φ q t σ
  map_add' a b := by
    refine (existsUnique_img hH φ q t σ (a + b)).unique (img_spec hH φ q t σ (a + b)) fun p => ?_
    erw [GlobalTheory.LB.coord_add, map_add, img_spec, img_spec]
    unfold loc
    erw [GlobalTheory.LB.coord_add, map_add]
    ring
  map_smul' r a := by
    refine (existsUnique_img hH φ q t σ (r • a)).unique (img_spec hH φ q t σ (r • a)) fun p => ?_
    erw [GlobalTheory.LB.coord_smul, map_mul, rs_rs, img_spec]
    unfold loc
    erw [GlobalTheory.LB.coord_smul, map_mul, rs_rs]
    simp only [RingHom.id_apply]
    ring

theorem imgLin_injective [IsIntegral X] {H : LB X} (hH : H.IsLB) (φ : X ⟶ X) (q t : ℕ) (σ : LB.Sec (E H φ q))
    (hσ : ∃ p : H.ι × (PUnit.{1} → H.ι), σ.f p ≠ 0) : Function.Injective (imgLin hH φ q t σ) := by
  obtain ⟨p₀, hp₀⟩ := hσ
  have hne : Nonempty ((E H φ q).U p₀) := by
    by_contra hc
    have hb : (E H φ q).U p₀ = ⊥ := by
      ext x
      exact ⟨fun hx => (hc ⟨⟨x, hx⟩⟩).elim, fun hx => hx.elim⟩
    have : Subsingleton Γ(X, (E H φ q).U p₀) := by rw [hb]; infer_instance
    exact hp₀ (Subsingleton.elim _ _)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h0 : loc H φ q t σ a p₀ = 0 := by
    rw [← img_spec hH φ q t σ a p₀]
    change rs X _ (GlobalTheory.LB.coord (imgLin hH φ q t σ a) p₀.1) = 0
    rw [ha]
    erw [GlobalTheory.LB.coord_zero, map_zero]
  unfold loc at h0
  have h1 := (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ hp₀)
  have hz := GlobalTheory.SecGrowth.sec_eq_zero (M := (GlobalTheory.AbLaw.pw H t).pull φ) (SecOn.topEquiv _ a) (k₀ := p₀.2)
    (W := (E H φ q).U p₀) inf_le_right (by erw [SecOn.topEquiv_f, rs_rs]; exact h1)
  apply (SecOn.topEquiv ((GlobalTheory.AbLaw.pw H t).pull φ)).injective
  rw [map_zero]
  exact GlobalTheory.LB.f_injective (funext hz)

end GlobalTheory.DegCmp

namespace GlobalTheory.DegCmp

theorem finite_finrank_pull_le {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) (φ : X ⟶ X) (hφf : φ ≫ f = f) {H : LB X} (hH : H.IsLB) (q t : ℕ)
    (σ : LB.Sec (E H φ q)) (hσ : ∃ p : H.ι × (PUnit.{1} → H.ι), σ.f p ≠ 0)
    (hfin : Module.Finite K (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤)) :
    Module.Finite K (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ∧
      Module.finrank K (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ≤
        Module.finrank K (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤) := by
  rw [hφf]
  have hinj : Function.Injective (SecOnR.lin f (imgLin hH φ q t σ)) := imgLin_injective hH φ q t σ hσ
  exact ⟨Module.Finite.of_injective _ hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩

end GlobalTheory.DegCmp

namespace GlobalTheory

open GlobalTheory.DegCmp in

theorem degree_le_of_pull_le_pow : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Etale φ], φ ≫ f = f → ∀ (D q : ℕ), 1 ≤ q → (∀ x, φ.finrank x = D) → (∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ))) (j : (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)).ι), σ.f j ≠ 0) → D ≤ C * q ^ g := by
  intro k _ X _ f g hg H m s hH hs
  obtain ⟨hfin, -, c, C₀, -, hgrow⟩ := GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k X f g hg H m s hH hs
  refine ⟨c * C₀ * 2 ^ g, fun φ _ _ hφf D q hq hD hσ => ?_⟩
  obtain ⟨σ, j, hj⟩ := hσ
  have hW : ∀ t : ℕ, Module.Finite k (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ∧
      Module.finrank k (SecOnR (φ ≫ f) ((GlobalTheory.AbLaw.pw H t).pull φ) ⊤) ≤
        Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤) := fun t =>
    finite_finrank_pull_le f φ hφf hH q t σ ⟨j, hj⟩ (hfin (q * t))
  obtain ⟨a, ha⟩ := GlobalTheory.finrank_sec_pull_sandwich k X X f φ H m s hH hs D hD hfin fun t => (hW t).1
  have h1 := (hgrow (a + 1) (by omega)).1
  have h2 := (ha (a + 1)).1
  have h3 := (hW (a + 1 + a)).2
  have h4 := (hgrow (q * (a + 1 + a)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).2
  have hpos : 0 < (a + 1) ^ g := by positivity
  have key : D * (a + 1) ^ g ≤ (c * C₀ * 2 ^ g * q ^ g) * (a + 1) ^ g :=
    calc D * (a + 1) ^ g ≤ D * (c * Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((a + 1 : ℕ) : ℤ)) ⊤)) :=
          Nat.mul_le_mul_left _ h1
      _ = c * (D * Module.finrank k (SecOnR f (GlobalTheory.AbLaw.pw H ((a + 1 : ℕ) : ℤ)) ⊤)) := by ring
      _ ≤ c * (C₀ * (q * (a + 1 + a)) ^ g) := Nat.mul_le_mul_left _ (h2.trans (h3.trans h4))
      _ ≤ c * (C₀ * (q * (2 * (a + 1))) ^ g) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) g))
      _ = (c * C₀ * 2 ^ g * q ^ g) * (a + 1) ^ g := by rw [mul_pow, mul_pow]; ring
  exact Nat.le_of_mul_le_mul_right key hpos

end GlobalTheory

example : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of k)) (g : ℕ), SmoothOfRelativeDimension g f → ∀ (H : LB X) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ C : ℕ, ∀ (φ : X ⟶ X) [IsFinite φ] [Etale φ], φ ≫ f = f → ∀ (D q : ℕ), 1 ≤ q → (∀ x, φ.finrank x = D) → (∃ (σ : LB.Sec (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ))) (j : (LB.div (GlobalTheory.AbLaw.pw H (q : ℤ)) (H.pull φ)).ι), σ.f j ≠ 0) → D ≤ C * q ^ g :=
  GlobalTheory.degree_le_of_pull_le_pow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenBoundCombinePadicPrimeToPStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.den_bound_combine_padic_primeToP : ∀ (p D K k : ℕ), p.Prime → ∀ q : ℚ, (∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ K * m : ℕ) : ℚ) * q = a) → (∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = a) → ∃ a : ℤ, ((D * p ^ K : ℕ) : ℚ) * q = a := by
  first | (exact @GlobalTheory.den_comb) | (exact GlobalTheory.den_comb) | (intros; apply GlobalTheory.den_comb  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentEqualizerDegreeZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_equalizer_degree_zero : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'], Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) → ∀ (j : ℤ) (b : Ht q (sp A') 0 j), pull _ (spMap (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b = pull _ (spMap (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b → ∃ a : Ht q (sp A) 0 j, pull _ (spMap (algebraMap A A')) _ 0 a = b := by
  first | (exact @GlobalTheory.EtC.DescZero.desc_zero) | (exact GlobalTheory.EtC.DescZero.desc_zero) | (intros; apply GlobalTheory.EtC.DescZero.desc_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneOfMemBase
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.OneMapExact.det_eq_one_of_mem_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (h : R.IsGrp F) :
    ∀ u : F.P0, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1 := by
  intro u PP
  obtain ⟨ψ, -, h0, -⟩ := h.levels
  have h1 : F.P0.comap R.eG.symm.toMonoidHom = Subgroup.pi Set.univ (fun v : R.Pg => unip (kP v.1) D.R.r) :=
    congrArg LevelP.H h0
  have h2 : R.eG u ∈ F.P0.comap R.eG.symm.toMonoidHom := by
    rw [Subgroup.mem_comap]; simp
  rw [h1] at h2
  rw [← Matrix.GeneralLinearGroup.val_det_apply, GlobalTheory.TraceIncl.gl_det_eq_one_of_mem_unip (h2 PP (Set.mem_univ _)),
    Units.val_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetProductDepthInChartEqSumFactorDepths
section
set_option autoImplicit false

namespace GlobalTheory.FactorDepthProd

section General

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {κ : Type} [Fintype κ] {d : κ → ℕ}
  (G : ∀ b, LogFGL v (d b)) {ι : κ → Type} [∀ b, Fintype (ι b)] (u : ∀ b, ι b → Fin (d b) → C)

omit [Fintype κ] in

theorem constantCoeff_expAlong (x : Σ b, Fin (d b)) : constantCoeff (expAlong G u x) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (by simp)) (by simp) ((isExp_expOf _).1 _)

theorem derivAt0_one_subst (f : MvPowerSeries (Σ b, Fin (d b)) C) :
    derivAt0 1 (subst (expAlong G u) f) = constantCoeff f := by
  classical
  have hs : HasSubst (expAlong G u) := hasSubst_of_constantCoeff_zero (constantCoeff_expAlong G u)
  have h0 : constantCoeff (subst (expAlong G u) (f - (constantCoeff f) • 1)) = 0 :=
    constantCoeff_subst_eq_zero hs (constantCoeff_expAlong G u) (by simp)
  rw [← coe_substAlgHom hs, map_sub, map_smul, map_one, coe_substAlgHom hs] at h0
  unfold derivAt0
  rw [MvPolynomial.support_one, Finset.sum_singleton]
  simpa [mfact, sub_eq_zero] using h0

theorem depth_one : depth G u 1 = 0 := by
  classical
  unfold depth
  refine le_antisymm (iInf_le_of_le ⟨1, fun α => ?_⟩ ?_) (le_iInf fun f => ?_)
  · unfold IsIntV; rw [coeff_one]; split_ifs <;> simp
  · rw [derivAt0_one_subst, map_one, AddValuation.map_one]; rfl
  · rw [derivAt0_one_subst]
    have h : (0 : WithTop ℝ) ≤ v (constantCoeff f.1) := f.2 0
    exact WithBot.coe_le_coe.2 h

theorem depth_prod [CharZero C] [DecidableEq κ] [∀ b, DecidableEq (ι b)] {F : Type} (col : κ → F)
    (P : F → MvPolynomial (Σ b, ι b) C) (hP : ∀ f, ∀ x ∈ (P f).vars, col x.1 = f) (s : Finset F) :
    depth G u (∏ f ∈ s, P f) = ∑ f ∈ s, depth G u (P f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using depth_one G u
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
    refine GlobalTheory.T.formalGroupOperatorDepth_mul_disjoint_columns C v κ d G ι u {b | col b = a} _ _ (hP a) fun x hx h => ?_
    obtain ⟨f, hf, hxf⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hx)
    exact ha ((show col x.1 = a from h) ▸ hP f x hxf ▸ hf)

theorem depth_prod_detPow [CharZero C] {n : ℕ} (G₀ : LogFGL v n) {F : Type} [Fintype F] (r : F → ℕ)
    (w : ∀ f, Fin (r f) → Fin n → C) (cx : F → ℕ) :
    depth (fun _ : (Σ f : F, Fin (r f)) => G₀) (fun b => w b.1)
      (∏ f : F, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (r f), Fin (r f)) =>
        (⟨⟨f, ℓ.1⟩, ℓ.2⟩ : Σ b : (Σ f : F, Fin (r f)), Fin (r b.1))) (detPow C (r f) (cx f))) =
      ∑ f : F, detDepth G₀ (w f) (cx f) := by
  classical
  rw [depth_prod _ _ (fun b : (Σ f : F, Fin (r f)) => b.1)]
  · refine Finset.sum_congr rfl fun f _ => ?_
    have h := GlobalTheory.T.differentialOperatorDepth_restrict_columns C v (Σ f : F, Fin (r f)) (fun _ => n) (fun _ => G₀)
      (fun b => Fin (r b.1)) (fun b => w b.1) (Fin (r f)) ⟨fun b => ⟨f, b⟩, fun _ _ h => eq_of_heq (Sigma.mk.inj h).2⟩
      (detPow C (r f) (cx f))
    unfold detDepth
    refine Eq.trans ?_ (h.trans ?_)
    · congr 1
    · congr 1
  · intro f x hx
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ hx)
    rfl

end General

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CharDepth GlobalTheory.FactorDepth

theorem nuProdC_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), nuProdC Ch X cx = ∑ f : Lt1 Dw, nuFacC Ch X f (cx f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ T io y Ch X cx
  exact depth_prod_detPow (fgl Ch X) rk (frame Ch X) cx

end GlobalTheory.FactorDepthProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalSignOfPositiveEigenvectorOnePositive
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem diag_sign_of_pos_eigenvector : ∀ {n : ℕ} (A h g : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (W Z : GL (Fin n) ℂ) (lam : Fin n → ℂ) (d : Fin n → ℝ), A.det ≠ 0 → sigPosH hA = 1 → h = (W : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (W : Matrix (Fin n) (Fin n) ℂ) → (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) → Function.Injective lam → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∀ (i₀ : Fin n) (x : Fin n → ℂ), g *ᵥ x = lam i₀ • x → 0 < (star x ⬝ᵥ (h *ᵥ x)).re → 0 < d i₀ ∧ ∀ i, i ≠ i₀ → d i < 0 := by
  intro n A h g hA W Z lam d hdet hsig hh hZ hlam hg i₀ x hx hxpos
  have key : ∀ (N B : Matrix (Fin n) (Fin n) ℂ) (u u' : Fin n → ℂ),
      star (N *ᵥ u) ⬝ᵥ B *ᵥ (N *ᵥ u') = star u ⬝ᵥ (Nᴴ * B * N) *ᵥ u' := by
    intro N B u u'
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  set M : Matrix (Fin n) (Fin n) ℂ := (W : Matrix (Fin n) (Fin n) ℂ) * (Z : Matrix (Fin n) (Fin n) ℂ) with hM
  have hMd : Mᴴ * A * M = diagonal (fun i => (d i : ℂ)) := by
    rw [← hZ, hh, hM, conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨y, rfl⟩ : ∃ y, x = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y :=
    ⟨(↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ x, by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]⟩
  have hy : ∀ i, i ≠ i₀ → y i = 0 := by
    have h1 : (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (diagonal lam *ᵥ y)
        = (Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ (lam i₀ • y) := by
      rw [mulVec_mulVec, ← hg, ← mulVec_mulVec, hx, mulVec_smul]
    have h2 : diagonal lam *ᵥ y = lam i₀ • y := by
      have := congrArg (fun v => (↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) h1
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, one_mulVec] using this
    intro i hi
    have h3 := congrFun h2 i
    rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at h3
    have h4 : (lam i - lam i₀) * y i = 0 := by rw [sub_mul, h3, sub_self]
    rcases mul_eq_zero.mp h4 with h5 | h5
    · exact absurd (hlam (sub_eq_zero.mp h5)) hi
    · exact h5
  have hform : star ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y) ⬝ᵥ h *ᵥ ((Z : Matrix (Fin n) (Fin n) ℂ) *ᵥ y)
      = ((d i₀ * Complex.normSq (y i₀) : ℝ) : ℂ) := by
    rw [key, hZ]
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
    rw [Finset.sum_eq_single i₀ (fun i _ hi => by simp [hy i hi]) (by simp)]
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  rw [hform, Complex.ofReal_re] at hxpos
  have hd0 : 0 < d i₀ := by
    by_contra hc
    push_neg at hc
    nlinarith [Complex.normSq_nonneg (y i₀)]
  refine ⟨hd0, fun i hi => ?_⟩
  have hNM : ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) * M = 1 := by
    rw [hM, Matrix.mul_assoc, ← Matrix.mul_assoc (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ), Units.inv_mul,
      Matrix.one_mul, Units.inv_mul]
  have hval : ∀ j k : Fin n, star (M *ᵥ Pi.single j 1) ⬝ᵥ A *ᵥ (M *ᵥ Pi.single k 1)
      = if j = k then (d j : ℂ) else 0 := by
    intro j k
    rw [key, hMd]
    by_cases hjk : j = k
    · subst hjk; simp [dotProduct, mulVec_diagonal, Pi.single_apply]
    · simp [dotProduct, mulVec_diagonal, Pi.single_apply, hjk]
      intro hkj; exact absurd hkj.symm hjk
  have hne : M *ᵥ Pi.single i (1 : ℂ) ≠ 0 := by
    intro h0
    have := congrArg (fun v => ((↑Z⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (↑W⁻¹ : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) h0
    simp only [mulVec_mulVec, hNM, one_mulVec, mulVec_zero] at this
    have := congrFun this i
    simp at this
  have hneg := re_form_neg_of_orth_of_sigPosH_eq_one A hA hdet hsig (M *ᵥ Pi.single i₀ 1)
    (M *ᵥ Pi.single i 1) (by rw [hval]; simpa using hd0) (by rw [hval, if_neg (Ne.symm hi)]) hne
  rw [hval, if_pos rfl, Complex.ofReal_re] at hneg
  exact hneg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharacterTrivialOnPrincipalLevelStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_character_trivial_on_principal_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ k ∈ T.Kf ((i : ℕ) + 1) σ, T.mu ((i : ℕ) + 1) σ k = 1 := by
  first | exact @GlobalTheory.MuLevel.mu_eq_one_of_mem_level | exact GlobalTheory.MuLevel.mu_eq_one_of_mem_level | (intros; apply GlobalTheory.MuLevel.mu_eq_one_of_mem_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormalStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeriesModel_unitary_irreducible_orthonormal : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), CompleteSpace (M.H τ) ∧ IsURepOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ IsIrredOn (Formalism.QuantumDeterminants.UH (gramAt D V τ)) (M.rep τ) ∧ (HolShape M → OrthFr (gramAt D V τ) (nNeg (M.ε τ)) (x0Mat M τ) ∧ ∀ a c, x0Mat M τ * Matrix.single a c 1 * (x0Mat M τ)⁻¹ = (M.fr τ)⁻¹ * Matrix.single (arr (nNeg (M.ε τ)) a) (arr (nNeg (M.ε τ)) c) 1 * M.fr τ) := by
  first | exact @GlobalTheory.HolDict.ModelRep.model_rep | exact GlobalTheory.HolDict.ModelRep.model_rep | (intros; apply GlobalTheory.HolDict.ModelRep.model_rep <;> assumption)
end

