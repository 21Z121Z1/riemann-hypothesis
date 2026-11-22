import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3489
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3494
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3413
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3501
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0657
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIdentificationsAgreeConstantTangentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_identifications_agree_constant_tangent : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R) (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.P.A.left ⟶ B₀.left), IsGrpPullback Q.P.A B₀ (spMap ιb) β → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (GlobalTheory.RigChart.constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ ≫ β = π₂ ≫ β := by
  first | exact @GlobalTheory.RigHom.comp_eq_of_const | exact GlobalTheory.RigHom.comp_eq_of_const | (intros; apply GlobalTheory.RigHom.comp_eq_of_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeModuleActionHomomorphismStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_module_action_homomorphism : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (x : X → (𝟙_ (Over (Sp V)) ⟶ B)), (∀ y z, x (y + z) = x y * x z) → (∀ (o : O) y, x (o • y) = x y ≫ a.act o) → ∀ n : ℕ, IsUnit (n : V) → ∃ x' : X → (𝟙_ (Over (Sp V)) ⟶ B), (∀ y z, x' (y + z) = x' y * x' z) ∧ (∀ (o : O) y, x' (o • y) = x' y ≫ a.act o) ∧ ∀ y, x' (n • y) = x y := by
  first | exact @GlobalTheory.AbDivLocal.exists_divided_linear | exact GlobalTheory.AbDivLocal.exists_divided_linear | (intros; apply GlobalTheory.AbDivLocal.exists_divided_linear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionsOrderFiniteUnramifiedScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

theorem GlobalTheory.EndLoc.actRep_finite_unramified : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π ∧ FormallyUnramified R.π := by
  intro S _ A _ _ Q hA hQ h1 h2 hs ha O _ bar r e W d hbar hspan hW hd hcas
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_finite_scheme_adjoint_actions_abelian S A Q hA hQ h1 h2 hs ha O bar r e W d hbar hspan hW hd hcas
  exact ⟨R, hR, GlobalTheory.T.formallyUnramified_adjointRingAction_scheme S A Q O bar R hA⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationWeightBound
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.Vanishing.H0

namespace GlobalTheory.CuspTransfer

theorem exists_cusp_germ : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed Xo c → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw), FlagTan.kap Dw + b = s → vanBd TF.X Z s ≤ space TF.X Z U s → ∃ F : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤ → Cusp Z U s, ∀ (z : M.X) (hz : z ∈ M.off) (j : (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).ι) (hj : z ∈ (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).U j) (i : (L₀ TF.X Z s).ι) (hi : M.σ z ∈ (L₀ TF.X Z s).U i), ∃ u : (M.X.presheaf.stalk z)ˣ, ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, germ j z (memTop z) hj g = u.val * (M.σ.stalkMap z).hom (germ i (M.σ z) (M.off_eq.le hz) hi (cuspSec TF.X Z U s (F g))) := by
  intro hP hG E _ _ _ H Dw l Xo c TF Z r U hF M ω b s hs hvs
  set C := ((common₀ TF.X Z).pull M.σ).canChart M.K.isLB hs with hC
  have key : ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, ∃ f : Cusp Z U s,
      C.mul ω.ω (M.pullOff (cuspSec TF.X Z U s f)) = H0.restr le_top g := by
    intro g
    obtain ⟨m, hm⟩ := (M.bijective_pullOff (isLB_L₀ TF.X Z s)).2 ((C.mulEquiv ω.unit).symm (H0.restr le_top g))
    have hm' : C.mul ω.ω (M.pullOff m) = H0.restr le_top g := by
      rw [hm, ← ProdChart.mulEquiv_apply C ω.unit, LinearEquiv.apply_symm_apply]
    obtain ⟨g', hv, hr⟩ := (GlobalTheory.T.canonical_ideal_weight_section hP hG E H Dw l Xo c TF Z hF M ω b s hs m).2 ⟨g, hm'.symm⟩
    refine ⟨ofSpace TF.X Z U s ⟨g', hvs hv⟩, ?_⟩
    rw [cuspSec_ofSpace]
    exact (congrArg (fun x => C.mul ω.ω (M.pullOff x)) hr).trans hm'
  refine ⟨fun g => (key g).choose, ?_⟩
  intro z hz j hj i hi
  obtain ⟨t, ha, hb, hc⟩ := C.cover z
  have hω : IsUnit (H0.germ (C.a t) z hz ha ω.ω) := ω.unit z hz (C.a t) ha
  refine ⟨tr _ z j (C.c t) * hω.unit *
      Units.map (M.σ.stalkMap z).hom.toMonoidHom (tr (L₀ TF.X Z s) (M.σ z) (C.b t PUnit.unit) i), ?_⟩
  intro g
  have hg := (key g).choose_spec
  rw [H0.germ_change j (C.c t) z (memTop z) hj hc g, ← H0.germ_restr le_top (C.c t) z hz hc g, ← hg,
    C.germ_mul ω.ω _ t z hz ha hb hc]
  change _ = _ * (M.σ.stalkMap z).hom _
  have e2 := H0.germ_pull M.σ M.off_eq.le (C.b t) z hz hb (cuspSec TF.X Z U s (key g).choose)
  change _ * (_ * H0.germ (C.b t) z hz hb (H0.pull M.σ M.off_eq.le (cuspSec TF.X Z U s (key g).choose))) = _
  rw [e2]
  erw [H0.germ_change (B := L₀ TF.X Z s) (C.b t PUnit.unit) i (M.σ z) (M.off_eq.le hz) _ hi, map_mul]
  simp only [Units.val_mul, IsUnit.unit_spec, Units.coe_map]
  simp only [mul_assoc]
  rfl

end GlobalTheory.CuspTransfer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleMemCoboundaryAddMaximalSmulStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_mem_coboundary_add_maximal_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1) (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) (ι : A.left ⟶ t.G.left), IsPullback ι A.hom t.G.hom (spMap (Ideal.Quotient.mk m) ≫ chart U) → ∀ (c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → (∃ h' : ∀ i, Γ(A.left, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i') (fun _ hx => hx)).hom (c i i') = resG A.left inf_le_left (h' i) - resG A.left inf_le_right (h' i')) → ∃ (h : ∀ i : J, Γ(t.G.left, W i)) (N : ℕ) (r : Fin N → Γ(X, U.1)) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k, r k ∈ m) ∧ (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  first | exact @GlobalTheory.CechBCInj.cocycle_mem_coboundary_add_smul | exact GlobalTheory.CechBCInj.cocycle_mem_coboundary_add_smul | (intros; apply GlobalTheory.CechBCInj.cocycle_mem_coboundary_add_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1FiniteGenerationAffineStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_h1_finite_generation_affine : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → ∀ (U : X.affineOpens) (J : Type) (W : J → t.G.left.Opens), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → ∀ (hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1), ∃ (N : ℕ) (e : Fin N → ∀ i i' : J, Γ(t.G.left, W i ⊓ W i')), (∀ k i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (e k i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (e k i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (e k i i'')) ∧ ∀ c : ∀ i i' : J, Γ(t.G.left, W i ⊓ W i'), (∀ i i' i'', resG t.G.left (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') + resG t.G.left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (c i' i'') = resG t.G.left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (c i i'')) → ∃ (r : Fin N → Γ(X, U.1)) (h : ∀ i : J, Γ(t.G.left, W i)), ∀ i i', c i i' = resG t.G.left inf_le_left (h i) - resG t.G.left inf_le_right (h i') + ∑ k, (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (r k) * e k i i' := by
  first | exact @GlobalTheory.CechFin.cech_h1_finite | exact GlobalTheory.CechFin.cech_h1_finite | (intros; apply GlobalTheory.CechFin.cech_h1_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterValueMemLocalUnitsMulSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG

open GlobalTheory.Poinc.Sep.Coef (om tele root_mem prod_mem)

theorem chi_mem : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (a : D.X) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ χ : LB.Gen (LB.LinComb D.P.L ![(D.c a * b).left, (D.c a).left, b.left, (η[D.P.A]).left] DegPre.gtε),
      (χ.IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c a) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χ T.hom z J ^ N₁) →
    ∃ c ∈ k₀, (val χ (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ *
        GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ N₁ hN a b hb hbdef χ hχ
  obtain ⟨-, hM₀, hpb, hw, hc, -, -⟩ := hFB
  have h2 : spMap ev ≫ spMap ib = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  have hP : Coef.Idx.PowPts ib (fun _ : PUnit => β) := by
    intro T' g hg
    obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hpb T'.hom g hg
    exact ⟨e.trans (MulEquiv.piUnique fun _ : PUnit => (Over.mk g ⟶ B₀)).symm, fun x u => by cases u; exact he x⟩
  have hone : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (1 : Over.mk (spMap ev) ⟶ D.P.A).left := by
    intro _
    obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hpb (spMap ev) _ h2
    have e1 := he 1
    rw [map_one] at e1
    rw [← e1]
    exact defOver_comp k₀ (defOver_spMap k₀ (ev.comp ib) hk) _
  have H : Coef.Idx.Desc ib (fun _ : PUnit => β) ev k₀ w :=
    ⟨hk₀, hP, hk, hM₀, hw, fun _ _ _ h i => h i, hone⟩
  have pc : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (toUnit (Over.mk (spMap ev)) ≫ D.c a).left := by
    intro _
    show DefOver k₀ ((spMap ev ≫ GlobalTheory.UChart.cpt D a) ≫ β)
    rw [Category.assoc, hc a, ← Category.assoc, h2]
    exact defOver_comp k₀ (defOver_spMap k₀ (ev.comp ib) hk) _
  have pb : Coef.Idx.RatP (fun _ : PUnit => β) k₀ (toUnit (Over.mk (spMap ev)) ≫ b).left := by
    intro _
    show DefOver k₀ ((spMap ev ≫ b.left) ≫ β)
    rw [Category.assoc]; exact hbdef
  have pbi : ∀ i : ℕ, Coef.Idx.RatP (fun _ : PUnit => β) k₀ ((toUnit (Over.mk (spMap ev)) ≫ b) ^ i).left := by
    intro i
    induction i with
    | zero => rw [pow_zero]; exact hone
    | succ i ih => rw [pow_succ]; exact Coef.Idx.ratP_mul hP hk ih pb
  set x := toUnit (Over.mk (spMap ev)) ≫ D.c a with hx
  set y := toUnit (Over.mk (spMap ev)) ≫ b with hy
  have hyN : y ^ N₁ = 1 := by rw [hy, ← MonObj.comp_pow, hb, MonObj.comp_one]
  have hcub := hχ.2 (Over.mk (spMap ev)) z J hJ
  simp only [MonObj.comp_pow] at hcub
  choose c hc' ec using fun i : ℕ => Coef.Idx.cub_mem H x (y ^ i) y pc (pbi i) pb z J J₀ hJ hJ₀
  set h : (Over.mk (spMap ev) ⟶ D.P.A) → ((Sp K).presheaf.stalk z)ˣ := fun p => om (Z := Sp K) w z J J₀ p.left with hh
  set G := h (x * y) * (h x)⁻¹ * (h y)⁻¹ * h 1 with hG
  obtain ⟨c₁, hc₁, e₁⟩ := prod_mem (Finset.range N₁) (fun i => ⟨c i, hc' i, ec i⟩)
  have key : (∏ i ∈ Finset.range N₁, ((h (x * y ^ i * y) * (h (x * y ^ i))⁻¹ * (h (x * y))⁻¹ * (h (y ^ i * y))⁻¹ *
      h x * h (y ^ i) * h y * (h 1)⁻¹) * @id ((Sp K).presheaf.stalk z)ˣ (cubV D.cub (T := Over.mk (spMap ev)) z J x (y ^ i) y))) =
      (G⁻¹ * val χ (spMap ev) z J) ^ N₁ := by
    rw [Finset.prod_mul_distrib, tele h x y N₁ hyN]
    have e3 : (∏ i ∈ Finset.range N₁, @id ((Sp K).presheaf.stalk z)ˣ (cubV D.cub (T := Over.mk (spMap ev)) z J x (y ^ i) y)) =
        val χ (spMap ev) z J ^ N₁ := hcub
    have e4 : ∀ A B C E : ((Sp K).presheaf.stalk z)ˣ, A⁻¹ * B * C * E⁻¹ = (A * B⁻¹ * C⁻¹ * E)⁻¹ :=
      fun A B C E => by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
    rw [e3, e4, ← mul_pow]
  rw [key] at e₁
  obtain ⟨c₂, hc₂, e₂⟩ := root_mem hk₀ (z := z) (s := (G⁻¹ * val χ (spMap ev) z J).val) (n := N₁) (by omega) ⟨c₁, hc₁, by rw [← Units.val_pow_eq_pow_val]; exact e₁⟩
  refine ⟨c₂, hc₂, ?_⟩
  have hGe : G = gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ *
      (gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ * gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left) := by
    rw [hG, hh, hx, hy, ← MonObj.comp_mul]
    rfl
  rw [← hGe, ← e₂, ← Units.val_mul, mul_inv_cancel_left]

end GlobalTheory.USep.EvG
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointOfValuesInSmallAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_of_values_in_small_algClosed : ∀ (F A R K : Type) [Field F] [NumberField F] [CommRing A] [IsDomain A] [CommRing R] [IsLocalRing R] [Field K] (b : F →+* A), b.EssFiniteType → ∀ ψ : A →+* R, GlobalTheory.TChart.IsComplAt ψ → ∀ (ev : R →+* K) (k₀ : Subfield K), Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) → (∀ a, ev (ψ a) ∈ k₀) → (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀ := by
  first | exact @GlobalTheory.PointAlg.closed_point_of_values | exact GlobalTheory.PointAlg.closed_point_of_values | (intros; apply GlobalTheory.PointAlg.closed_point_of_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

namespace GlobalTheory.USepTrait

theorem sp_comp {R S U : Type} [CommRing R] [CommRing S] [CommRing U] (f : R →+* S) (g : S →+* U) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem comap_map_eq {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Injective f) [IsLocalHom f] (I : Ideal R) :
    (I.map f).comap f = I := by
  letI := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Module.Flat R S := inferInstance
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I

end GlobalTheory.USepTrait
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromTautBaseOfRescaledPullbackMonomialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial : ∀ {o W : Type} [CommRing o] [CommRing W] [IsDomain W] [IsLocalRing W] (T : TautBase o W) (n : ℕ) (D₀ : DegPre W), D₀.PsiEven → D₀.TauBimult → (∀ y, PsiUnitOn D₀ y Set.univ) → ∀ (ib : D₀.X ≃+ (Fin T.r → ℤ)) (β : D₀.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ T.B T.M.L).pull ββ)), From T (RingHom.id W) (fun _ : Empty => (1 : W)) (fun _ => 0) n D₀ ib β ββ w → ∀ (V : Type) [CommRing V] [IsDomain V] (iw : W →+* V), Function.Injective iw → ∀ (Q : DegPre V) (g : Q.X → (FractionRing V)ˣ) (hD : IsPullDeg iw D₀ (rescale Q g)) {I : Type} [Fintype I] (s : I → V) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (e : Q.X ≃+ (Fin T.r → ℤ)), (∀ y : Q.X, e y = ib (hD.xe y)) → (∀ a a' : Q.X, (((g (a + a'))⁻¹ * g a * g a' : (FractionRing V)ˣ) : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ((n : ℤ) * ε i (e a) (e a'))) → ∃ (β' : Q.P.A.left ⟶ T.B.left) (ββ' : (G2 Q.P.A).left ⟶ (G2 T.B).left) (w' : LB.Iso (abelian₂ Q.P.A Q.P.L) ((abelian₂ T.B T.M.L).pull ββ')), From T iw s ε n Q e β' ββ' w' := by
  first | exact @GlobalTheory.TInj.from_rescale_pull | exact GlobalTheory.TInj.from_rescale_pull | (intros; apply GlobalTheory.TInj.from_rescale_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesOfCommutesDualNumberAgreeClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutes_of_commutes_dualNumber_agree_closed : ∀ (k : Type) [Field k] {S : Scheme.{0}} (G' : Over (Sp (DualNumber k))) [GrpObj G'], IsAbelianScheme G' → ∀ (G : Over S) [GrpObj G] (g₂ : Sp (DualNumber k) ⟶ S) (φ₁ φ₂ : G'.left ⟶ G.left), IsGrpPullback G' G g₂ φ₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ G'.left) (y : Z ⟶ Sp k), x ≫ G'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ φ₁ = x ≫ φ₂) → ∀ (u : G' ⟶ G') [IsMonHom u] (v : G ⟶ G) [IsMonHom v], u.left ≫ φ₁ = φ₁ ≫ v.left → u.left ≫ φ₂ = φ₂ ≫ v.left := by
  first | exact @GlobalTheory.EpsRigid.comm_of_comm | exact GlobalTheory.EpsRigid.comm_of_comm | (intros; apply GlobalTheory.EpsRigid.comm_of_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingHeatOperatorsActOnValuesStatement
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
theorem _root_.GlobalTheory.T.commuting_heatOperators_act_on_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) u' p p' k s)) := by
  first | exact @GlobalTheory.Heat.heat_acts_on_values | exact GlobalTheory.Heat.heat_acts_on_values | (intros; apply GlobalTheory.Heat.heat_acts_on_values <;> assumption)
end

