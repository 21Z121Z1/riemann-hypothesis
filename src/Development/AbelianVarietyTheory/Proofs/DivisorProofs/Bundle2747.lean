import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0529
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatchingExistsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matching_exists : GlobalTheory.ThK.KP → GlobalTheory.ThK.MatchEx := by
  first | exact @GlobalTheory.ThK.matchEx_of_classicalTheorems | exact GlobalTheory.ThK.matchEx_of_classicalTheorems | (intros; apply GlobalTheory.ThK.matchEx_of_classicalTheorems <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSquareFactorizationSectionsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_square_factorization_sections : ∀ (X : Scheme.{0}) (L2 : LB X) (h : L2.Sec) (x : X) (j₀ : L2.ι) (hx : x ∈ L2.U j₀) (u : (X.presheaf.stalk x)ˣ) (a : X.presheaf.stalk x), a ≠ 0 → (X.presheaf.germ (L2.U j₀) x hx).hom (h.f j₀) = u * a ^ 2 → ∃ V : X.Opens, x ∈ V ∧ ∃ a : Γ(X, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(X, V ⊓ L2.U j)ˣ, (X.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(X, V ⊓ L2.U j)) * (X.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  first | exact @GlobalTheory.Mum.unit_mul_sq_spread | exact GlobalTheory.Mum.unit_mul_sq_spread | (intros; apply GlobalTheory.Mum.unit_mul_sq_spread <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationTensorPrimeComapCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_tensor_prime_comap_compat : ∀ (A C B Ω : Type) [CommRing A] [CommRing C] [CommRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [Field Ω] [Algebra A Ω] (Q : Ideal B) [Q.IsPrime] (Q' : Ideal (TensorProduct A Ω B)) [Q'.IsPrime] (f : TensorProduct A Ω B), Q'.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] TensorProduct A Ω B) = Q → f ∉ Q' → ((algebraMap (TensorProduct A Ω B) (Localization.Away f)).comp (Algebra.TensorProduct.map (AlgHom.id A Ω) (IsScalarTower.toAlgHom A C B)).toRingHom).Etale → Function.Bijective ((KaehlerDifferential.mapBaseChange A C B).lTensor Q.ResidueField) := by
  first | exact @GlobalTheory.Mum.mapBaseChange_residueField_bijective_of_etale_fibre | exact GlobalTheory.Mum.mapBaseChange_residueField_bijective_of_etale_fibre | (intros; apply GlobalTheory.Mum.mapBaseChange_residueField_bijective_of_etale_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivativeTransitionUnitsIsoLineBundles
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

namespace GlobalTheory.CechKS

theorem dlog_of_mul_eq {B : Type} [CommRing B] (a₁ a₂ l g : DualNumber B) (i₁ i₂ il ig : B)
    (h : a₁ * l = g * a₂) (h₁ : a₁.fst * i₁ = 1) (h₂ : a₂.fst * i₂ = 1) (hl : l.fst * il = 1)
    (hg : g.fst * ig = 1) : g.snd * ig = l.snd * il + (a₁.snd * i₁ - a₂.snd * i₂) := by
  have h0 : a₁.fst * l.fst = g.fst * a₂.fst := by simpa using congrArg TrivSqZeroExt.fst h
  have h1 : a₁.fst * l.snd + a₁.snd * l.fst = g.fst * a₂.snd + g.snd * a₂.fst := by
    have := congrArg TrivSqZeroExt.snd h
    rwa [DualNumber.snd_mul, DualNumber.snd_mul] at this
  have e1 : a₁.fst * ig * i₂ = il := by
    linear_combination (ig * i₂ * il) * h0 - (a₁.fst * ig * i₂) * hl + (a₂.fst * i₂ * il) * hg + il * h₂
  have e2 : l.fst * ig * i₂ = i₁ := by
    linear_combination (ig * i₂ * i₁) * h0 - (l.fst * ig * i₂) * h₁ + (a₂.fst * i₂ * i₁) * hg + i₁ * h₂
  linear_combination (-(ig * i₂)) * h1 + l.snd * e1 + a₁.snd * e2 - (a₂.snd * i₂) * hg - (g.snd * ig) * h₂

theorem valR_fst_mul_inv {Y : Scheme.{0}} {B : Type} [CommRing B] {x : Sp B ⟶ Y} {w : Sp (DualNumber B) ⟶ Y}
    (hw : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) {O : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ O) (u : Γ(Y, O)ˣ) :
    (valR w O u.val).fst * valR x O u⁻¹.val = 1 := by
  have h' := le_preimage_of_red hw h
  subst hw
  have e : (valR w O u.val).fst = ev _ O h u.val := by
    rw [valR_eq_ev _ _ h', GlobalTheory.FlagMod.ev_spMap _ w O h']
    rfl
  rw [e, valR_eq_ev _ _ h, ← map_mul, Units.mul_inv, map_one]

theorem valR_iso_compat {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M)
    (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {S : Type} [CommRing S] (z : Sp S ⟶ Y)
    (h₁ : ⊤ ≤ z ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ z ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))) :
    valR z _ (wg.s (p₁, fun _ => j₁)).val * valR (z ≫ m) _ (L.g j₁ j₂).val =
      valR z _ (M.g p₁ p₂).val * valR z _ (wg.s (p₂, fun _ => j₂)).val := by
  have e := hwg (p₁, fun _ => j₁) (p₂, fun _ => j₂)
  have hz := GlobalTheory.FlagMod.le_preimage_inf h₁ h₂
  have hP : ⊤ ≤ z ⁻¹ᵁ ((L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂)) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_right h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_right h₂)
  have hM : ⊤ ≤ z ⁻¹ᵁ (M.U p₁ ⊓ M.U p₂) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₂)
  have hle : (L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂) ≤ m ⁻¹ᵁ (L.U j₁ ⊓ L.U j₂) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₁) PUnit.unit))
      (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₂) PUnit.unit))
  have hg : (L.pull m).g (fun _ => j₁) (fun _ => j₂) = res hle (pullU m _ (L.g j₁ j₂)) := by
    show ∏ _k : PUnit, (res hle (pullU m _ (L.g j₁ j₂))) ^ (1 : ℤ) = _
    simp
  have hl : valR (z ≫ m) _ (L.g j₁ j₂).val = valR z _ ((L.pull m).g (fun _ => j₁) (fun _ => j₂)).val := by
    rw [hg, valR_comp_app]
    exact (valR_resG z hle hP _).symm
  rw [hl]
  have hle₁ : (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) ⊓ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) ≤ M.U p₁ ⊓ M.U p₂ :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have hle₂ : (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) ⊓ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) ≤
      (L.pull m).U (fun _ => j₁) ⊓ (L.pull m).U (fun _ => j₂) :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have e' : res (U := M.U p₁ ⊓ (L.pull m).U (fun _ => j₁)) inf_le_left (wg.s (p₁, fun _ => j₁)) =
      res hle₁ (M.g p₁ p₂) * (res hle₂ ((L.pull m).g (fun _ => j₁) (fun _ => j₂)))⁻¹ *
        res (U := M.U p₂ ⊓ (L.pull m).U (fun _ => j₂)) inf_le_right (wg.s (p₂, fun _ => j₂)) := e
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq] at e'
  have e2 := congrArg (fun u : Γ(Y, _)ˣ => ev z _ hz u.val) e'
  simp only [Units.val_mul, map_mul] at e2
  rw [← valR_eq_ev, ← valR_eq_ev, ← valR_eq_ev, ← valR_eq_ev] at e2
  exact (congrArg₂ (· * ·) (valR_resG z _ hz _) (valR_resG z _ hz _)).symm.trans
    (e2.trans (congrArg₂ (· * ·) (valR_resG z _ hz _) (valR_resG z _ hz _)))

theorem dlog_transition_iso : ∀ {Y Z : Scheme.{0}} (m : Y ⟶ Z) (L : LB Z) (M : LB Y) (wg : LB.Iso (L.pull m) M) (hwg : wg.IsGen) (j₁ j₂ : L.ι) (p₁ p₂ : M.ι) {B : Type} [CommRing B] (x : Sp B ⟶ Y) (w : Sp (DualNumber B) ⟶ Y) (hwx : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ w = x) (h₁ : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ (L.pull m).U (fun _ => j₁))) (h₂ : ⊤ ≤ x ⁻¹ᵁ (M.U p₂ ⊓ (L.pull m).U (fun _ => j₂))), (valR w _ (M.g p₁ p₂).val).snd * valR x _ (M.g p₁ p₂)⁻¹.val = (valR (w ≫ m) _ (L.g j₁ j₂).val).snd * valR (x ≫ m) _ (L.g j₁ j₂)⁻¹.val + ((valR w _ (wg.s (p₁, fun _ => j₁)).val).snd * valR x _ (wg.s (p₁, fun _ => j₁))⁻¹.val - (valR w _ (wg.s (p₂, fun _ => j₂)).val).snd * valR x _ (wg.s (p₂, fun _ => j₂))⁻¹.val) := by
  intro Y Z m L M wg hwg j₁ j₂ p₁ p₂ B _ x w hwx h₁ h₂
  have hM : ⊤ ≤ x ⁻¹ᵁ (M.U p₁ ⊓ M.U p₂) :=
    GlobalTheory.FlagMod.le_preimage_inf (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₁)
      (GlobalTheory.FlagMod.le_preimage_mono inf_le_left h₂)
  have hL : ⊤ ≤ (x ≫ m) ⁻¹ᵁ (L.U j₁ ⊓ L.U j₂) :=
    GlobalTheory.FlagMod.le_preimage_inf
      (GlobalTheory.FlagMod.le_preimage_map m
        (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₁) PUnit.unit)) h₁)
      (GlobalTheory.FlagMod.le_preimage_map m
        (inf_le_right.trans (LB.wchart_le L (K := PUnit) (fun _ => m) (fun _ => j₂) PUnit.unit)) h₂)
  have hwm : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (w ≫ m) = x ≫ m := by
    rw [← Category.assoc, hwx]
  exact dlog_of_mul_eq _ _ _ _ _ _ _ _
    (valR_iso_compat m L M wg hwg j₁ j₂ p₁ p₂ w (le_preimage_of_red hwx h₁) (le_preimage_of_red hwx h₂))
    (valR_fst_mul_inv hwx h₁ _) (valR_fst_mul_inv hwx h₂ _) (valR_fst_mul_inv hwm hL _) (valR_fst_mul_inv hwx hM _)

end GlobalTheory.CechKS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerDetEqConstMulHorizontalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logKodairaSpencer_det_eq_const_mul_horizontal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (s : ℚ), s ≠ 0 → KSCompare TF s → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (b : Fin Dw.dim → LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U), (∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (b j).1 (GlobalTheory.LogKSDiv.symPair e (ε j))) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)), ∃ a : ℚ, a ≠ 0 ∧ ∀ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (K : Type) [Field K] [Algebra c.F K] (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1) (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), (∀ σ, (g σ).det = 1) → GlobalTheory.Frames.FrChg g 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (w : HIx Dw (psiSet H) → FrPt Xo c (DualNumber K)) (hw : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1), (∀ b, IsDef P (w b) ∧ FlagTan.IsKS (psiSet H) P (w b).x (Pi.single b 1)) → ev (frX P₀ ≫ TF.Y.j) U.1 hU (logDet (fun j => (b j).1) x) = (a : K) * (Matrix.of fun i j => (ev (frX (w (o j)) ≫ TF.Y.j) U.1 (hw _) (x i)).snd).det := by
  first | exact @GlobalTheory.LogPole.logDet_eq_hor | exact GlobalTheory.LogPole.logDet_eq_hor | (intros; apply GlobalTheory.LogPole.logDet_eq_hor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInfEqOfReductionsJacobsonInductionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_inf_eq_of_reductions_jacobson_induction : ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (J : Ideal C), J ≤ Ideal.jacobson ⊥ → ∀ (W' : Scheme.{0}) (π : W' ⟶ Spec (CommRingCat.of C)) (U : (Spec (CommRingCat.of C)).Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K τ : (Spec (CommRingCat.of C)).IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : (Spec (CommRingCat.of C)).IdealSheafData), (∀ e : ℕ, T' ⊔ baseIdeal π (J ^ (e + 1)) = (τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1))).comap π) → (∀ e : ℕ, T'' ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) = τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) ⊔ K ^ k) → T'.map π ⊓ T'' = τ := by
  first | exact @GlobalTheory.FormalAlg.map_inf_eq_of_reductions | exact GlobalTheory.FormalAlg.map_inf_eq_of_reductions | (intros; apply GlobalTheory.FormalAlg.map_inf_eq_of_reductions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixWeightedPairBundleRigidifiedAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.CechPic

noncomputable section
namespace GlobalTheory.PowFormProps

def preQ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left) (hQ : QHyp A Q) :
    SiegPre 0 1 (0 : ℤ) (specZIsTerminal.from S) where
  A := A
  ab := hQ.1
  P := Q
  isLB := hQ.2.1
  rig₁ := hQ.2.2.1
  rig₂ := hQ.2.2.2.1
  symm := hQ.2.2.2.2.1
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := fun k _ _ x β z _ hz => by
    rw [map_zero] at hz
    exact absurd hz z.ne_zero

theorem formLB_props : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), QHyp A Q →
    ∀ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
      IsAbelianScheme (Out.powObj A r) ∧ (formLB A Q (Out.powPr A (n := r)) W).IsLB ∧
      Out.Rigidified (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) ∧
      Out.RelAmple (Out.powObj A r) (formLB A Q (Out.powPr A (n := r)) W) := by
  intro S A _ _ Q hQ r W hW
  let c := preQ A Q hQ
  have hA' : Out.RelAmple c.A c.diag := hQ.2.2.2.2.2
  let pr : Fin r → (Out.powObj A r ⟶ A) := Out.powPr A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin r → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A r, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit A r).lift (Fan.mk T y), fun u => (Out.powIsLimit A r).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A r).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (formLB A Q pr W).IsLB := LB.isLB_linComb hQ.2.1 _ _
  have hLW : cls (formLB A Q pr W) hL = PrincipalIntegral.quad (cls c.P c.isLB) W pr := cls_linComb hQ.2.1 _ _ _
  have hadd := PrincipalIntegral.pair_mul c SemiRigid.globalFns hA'
  exact ⟨GlobalTheory.isAbelianScheme_powObj_of_isAbelianScheme A hQ.1 r, hL,
    PrincipalIntegral.rigidified hadd hmon hL hLW,
    PosDefAmple.relAmple_linComb_of_posDef SemiRigid.globalFns 0 1 r ℤ 0 S _ c (Out.powObj A r) pr W hmon huniv hA' hW⟩

end GlobalTheory.PowFormProps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximumEstimateStatement
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BigOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem maxSt : MaxSt := by
  refine Formalism.MainNotions.Closed.of_all fun Fm _ => ⟨0, fun x hx _ i p hR hM v hv j => ?_⟩
  have hL := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC := hL.1
  have hv' : v ∈ (R2 p).twPl := hv
  have hdel : ∀ y, ((((R2 p).C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 y : ℂˣ) : ℂ) ∈ (Fm.D x i).what₂.embLL.range := fun y => by
    obtain ⟨z, hz⟩ := FO_le _ (hM.2.1.delAt_mem (Formalism.EigenvalueLevelCeiling.plc v) y)
    exact ⟨z, hz⟩
  exact GlobalTheory.TraceClassRank.spanOverClasses_of
    (GlobalTheory.T.baseThetaKernel_series_unique _ _ _ _ _ _ (R2 p) (F2 p) ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ j v hv' hC.tup.mu_on)
    (GlobalTheory.T.kernel_thetaSeries_span_over_class_representatives _ _ _ _ _ _ (R2 p) (F2 p) ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩ j v hv' hC.tup.mu_on hdel
      _ _ _)

end GlobalTheory.BigOn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureModuliFibreOfMonomialPeriodPreChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_moduliFibre_of_monomialPeriodPreChart : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) [IsNoetherianRing o] [Smooth s], PreChart F s j φ BD d x → x ∈ closure (Set.range j ∩ s ⁻¹' {s x}) := by
  first | exact @GlobalTheory.FibreDense.mem_closure_fibre | exact GlobalTheory.FibreDense.mem_closure_fibre | (intros; apply GlobalTheory.FibreDense.mem_closure_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEmbHOfClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

theorem exists_trait_point {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (M : Modif R) (x : M.S)
    (hx : M.π x = closedPoint R) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
      GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x := by
  have : IsNoetherianRing R := hR.1.1
  have : CharZero R := hR.2
  have := M.proper
  have := M.integral
  have := M.dominant
  have : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (M.S.fromSpecStalk x ≫ M.π)
  have hψp : ∀ q : Spec (M.S.presheaf.stalk x), Spec.map ψ q = M.π (M.S.fromSpecStalk x q) := fun q => by
    rw [hψ, Scheme.Hom.comp_apply]
  have hloc : IsLocalHom ψ.hom := by
    rw [isLocalHom_iff_comap_closedPoint]
    have := hψp (closedPoint _)
    rw [Scheme.fromSpecStalk_closedPoint, hx] at this
    exact this

  let t₀ : Sp (FractionRing R) := closedPoint (FractionRing R)
  have hsp : M.gp t₀ ⤳ x := by
    rw [specializes_iff_mem_closure]
    have h1 : Set.range M.gp ⊆ {M.gp t₀} := by
      rintro _ ⟨t, rfl⟩
      rw [Subsingleton.elim t t₀]; rfl
    exact closure_mono h1 ((IsDominant.denseRange (f := M.gp)).closure_eq ▸ Set.mem_univ x)
  have hr : M.gp t₀ ∈ Set.range (M.S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hsp
  obtain ⟨q, hq⟩ := hr
  have e1 : Spec.map ψ q = jK R t₀ := by
    rw [hψp, hq, ← Scheme.Hom.comp_apply, M.gp_π]
  have h2 : Ideal.comap ψ.hom q.asIdeal = ⊥ := by
    have := congrArg (fun p : Sp R => (p : PrimeSpectrum R).asIdeal) e1
    change Ideal.comap ψ.hom q.asIdeal = Ideal.comap (algebraMap R (FractionRing R)) t₀.asIdeal at this
    rw [this, @Ideal.eq_bot_of_prime _ _ t₀.asIdeal t₀.isPrime]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
  have hinj : Function.Injective ψ.hom := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap ψ.hom q.asIdeal := by
      rw [Ideal.mem_comap, ha]; exact q.asIdeal.zero_mem
    rw [h2] at this
    exact this
  have : CharZero (M.S.presheaf.stalk x) := charZero_of_injective_ringHom hinj
  have key : ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (χ : M.S.presheaf.stalk x →+* W),
      GlobalTheory.LN.CDvr W ∧ Function.Injective χ ∧ IsLocalHom χ := by
    by_cases h : IsField (M.S.presheaf.stalk x)
    · letI := h.toField
      refine ⟨PowerSeries (M.S.presheaf.stalk x), inferInstance, inferInstance, inferInstance, PowerSeries.C,
        ⟨inferInstance, ?_, ?_⟩, PowerSeries.C_injective, inferInstance⟩
      · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
      · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := M.S.presheaf.stalk x)) (RingHom.injective _)
    · obtain ⟨O, _, _, _, _, χ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating _ h
      have : CharZero O := charZero_of_injective_ringHom h1
      exact ⟨O, inferInstance, inferInstance, inferInstance, χ, ⟨inferInstance, inferInstance, inferInstance⟩, h1, h2⟩
  obtain ⟨W, _, _, _, χ, hW, hχ, hχl⟩ := key
  refine ⟨W, inferInstance, inferInstance, inferInstance, χ.comp ψ.hom, Spec.map (CommRingCat.ofHom χ) ≫ M.S.fromSpecStalk x,
    hW, hχ.comp hinj, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]; rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x) (IsLocalRing.comap_closedPoint χ)) Scheme.fromSpecStalk_closedPoint)

end GlobalTheory.Mum.SecEmb

namespace GlobalTheory.Mum.SecEmb

theorem mem_embH_of_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    ∀ g : G.left, M.π (G.hom g) = closedPoint R → g ∈ GlobalTheory.Mum.SecEmb.embH s := by
  intro R _ _ _ hR M G _ _ B L _ _ N s θ Y _ _ j _ _ O hT g hg
  obtain ⟨W, _, _, _, φ, ξ, hW, hφ, hl, hξ, hξx⟩ := exists_trait_point hR M (G.hom g) hg
  obtain ⟨W', _, _, _, io, G', _, β, κ, e, hW', hio, hfin, hcart, -, -, hpts⟩ := hT W hW φ ξ hφ hl hξ
  have hiol : IsLocalHom io := by
    letI := io.toAlgebra
    have : Module.Finite W W' := hfin
    have : FaithfulSMul W W' := (faithfulSMul_iff_algebraMap_injective W W').2 hio
    exact (inferInstance : IsLocalHom (algebraMap W W'))
  have hc : (spMap io ≫ ξ) (closedPoint W') = G.hom g :=
    (Scheme.Hom.comp_apply _ _ _).trans ((congrArg ξ (IsLocalRing.comap_closedPoint io)).trans hξx)
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap io ≫ ξ) g
    (closedPoint W') hc.symm
  have hg1 : β (hcart.1.isoPullback.inv z) = g := by
    rw [← Scheme.Hom.comp_apply, hcart.1.isoPullback_inv_fst, hz1]
  have hg2 : G'.hom (hcart.1.isoPullback.inv z) = closedPoint W' := by
    rw [← Scheme.Hom.comp_apply, hcart.1.isoPullback_inv_snd, hz2]
  obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := spMap (residue W'))
    (hcart.1.isoPullback.inv z) (closedPoint (ResidueField W'))
    (hg2.trans (IsLocalRing.comap_closedPoint (residue W')).symm)
  let F := ((Over.pullback (spMap (residue W'))).obj G').left
  let q' : F := q
  obtain ⟨⟨hs, -⟩, -⟩ := hpts (F.residueField q') (F.fromSpecResidueField q')
    (F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W')))
    (F.fromSpecResidueField q' ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ)) rfl rfl
  have hm : closedPoint (F.residueField q') ∈
      ⨆ i, nonzeroLocus (GlobalTheory.secPull (s i) ((F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β)) := by
    rw [hs]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  rw [GlobalTheory.nonzeroLocus_secPull] at hi
  have hpt : ((F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) ≫ β)
      (closedPoint (F.residueField q')) = g := by
    have h1 : (F.fromSpecResidueField q' ≫ pullback.fst G'.hom (spMap (residue W'))) (closedPoint (F.residueField q')) =
        hcart.1.isoPullback.inv z :=
      (Scheme.Hom.comp_apply _ _ _).trans
        ((congrArg (pullback.fst G'.hom (spMap (residue W'))) (Scheme.fromSpecResidueField_apply q' _)).trans hq1)
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg β h1).trans hg1)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  rw [← hpt]
  exact hi

end GlobalTheory.Mum.SecEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationOneOfAbsoluteFrobeniusPullZero
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

theorem eq_sub_of_pow_eq_sub (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [IsReduced B]
    (hB : (p : B) = 0) {c x y : B} (h : c ^ p = x ^ p - y ^ p) : c = x - y := by
  have e : (c - (x - y)) ^ p = 0 := by
    rw [← frobR_apply p B hB, map_sub, map_sub, frobR_apply, frobR_apply, frobR_apply, h, sub_self]
  exact sub_eq_zero.1 (IsReduced.eq_zero _ ⟨p, e⟩)

theorem mem_hodgeFiltrationOne_of_absoluteFrobenius_pull_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 k) s (dp0 k) s (frobR p k hk) (GlobalTheory.VB.frob X p hX)) (c : FirstDeRham s), h.pull1 c = 0 → c ∈ F1 s := by
  intro p _ k _ _ hk X _ s _ hX h c hc
  obtain ⟨f, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ c
  obtain ⟨u, hu, hf⟩ := GlobalTheory.T.exists_closed_pow_transition_of_frobenius_kills_class p k hk X s hX h f hc
  choose w hw using fun U : GlobalTheory.CechDR.AffOp X ↦ GlobalTheory.T.exists_pow_eq_of_kaehlerD_eq_zero_smooth_affineOpen p k hk X s U.unop (u U) (hu U)
  refine LinearMap.mem_ker.2 (GlobalTheory.CechDR.cmpO_injective k X s ?_)
  rw [map_zero, ← GlobalTheory.CechDR.structureSheaf_comparison_comm, GlobalTheory.CechDR.comparison_mk]
  refine GlobalTheory.CatCoh.H1.mk_eq_zero.2 ⟨w, funext fun U ↦ funext fun V ↦ funext fun a ↦ ?_⟩
  have : IsReduced (GlobalTheory.CechDR.Sec s V.unop.1) :=
    inferInstanceAs (_root_.IsReduced Γ(X, V.unop.1))
  have hp : (p : GlobalTheory.CechDR.Sec s V.unop.1) = 0 := by
    rw [← map_natCast (algebraMap k (GlobalTheory.CechDR.Sec s V.unop.1)), hk, map_zero]
  have e := hf U V a
  rw [← hw V, ← hw U, map_pow] at e
  exact (eq_sub_of_pow_eq_sub p hp e).symm

end GlobalTheory.ConjSeq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedPointsClosedFibreMemStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_closedPoints_closedFibre_mem' : ∀ (R : Type) [CommRing R] [IsLocalRing R] (T : Scheme.{0}) (q : T ⟶ Sp R), LocallyOfFiniteType q → ∀ U : T.Opens, (∀ x : T, IsClosed ({x} : Set T) → q x = closedPoint R → x ∈ U) → ∀ x : T, q x = closedPoint R → x ∈ U := by
  first | exact @GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem | exact GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem | (intros; apply GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem <;> assumption)
end

