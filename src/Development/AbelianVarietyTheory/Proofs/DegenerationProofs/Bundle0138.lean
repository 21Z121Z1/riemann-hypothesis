import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCommonField
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStarNormLEOfIsCMField
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesOfStrictPullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

noncomputable section
namespace GlobalTheory.ValuesStrictPull
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport
open GlobalTheory.PsiEvenPull (proj)
open ReciprocityTheory.ChartRestriction.G.DVR (cP)

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm

theorem vF_congr {X' Y' : Scheme.{0}} {L' : LB X'} {K' : Type} [Fintype K'] {φ' : K' → (Y' ⟶ X')} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {r : Sp F ⟶ Y} {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J)
    {t' : LB.Gen (LB.LinComb L' φ' ε')} {r' : Sp F ⟶ Y'} {J' : (Sp F ⟶ X') → L'.ι} (hJ' : Good L' z J')
    (h : val t r z J = val t' r' z J') : vF t r J = vF t' r' J' :=
  (stalkConst z).injective ((const_vF t r hJ).trans ((congrArg Units.val h).trans (const_vF t' r' hJ').symm))
end Val

theorem exists_numOf_strict_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D'), Strict hD.w → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F], (∀ x, algebraMap (FractionRing R') F (algebraMap R' _ (φ x)) = algebraMap (FractionRing R) F (algebraMap R _ x)) → ∀ (N : NumD F) (ν : NumOf D F N) (th' : H0 D'.P.L 1), (∀ s : H0 D'.P.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal D'.P.A.hom r) * th'.f j) → (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι), Good D.P.L z J → Good D'.P.L z J' → sval ν.th (r ≫ PsiEvenPull.proj hD) z J = (gw hD.w r z (J (r ≫ PsiEvenPull.proj hD)) (J' r)).val * sval th' r z J') → ∃ ν' : NumOf D' F N, (∀ y, hD.xe (ν'.eX y) = ν.eX y) ∧ ∀ x, (ν'.eA x).left ≫ PsiEvenPull.proj hD = (ν.eA x).left := by
  intro hG R R' _ _ _ _ φ D D' hD hS F _ _ _ hF N ν th' hgen hth
  obtain ⟨c, hc⟩ := hS
  have hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom := base_comm fun r => (hF r).symm
  have hj : jFK (R := R') F ≫ jK R' ≫ spMap φ = jFK (R := R) F ≫ jK R := (Category.assoc _ _ _).symm.trans hT
  let z : Sp F := IsLocalRing.closedPoint F
  let J' : (Sp F ⟶ D'.P.A.left) → D'.P.L.ι := fun ψ => c (ν.J (ψ ≫ proj hD))
  have hJ : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial
  have good' : ∀ ψ : Sp F ⟶ D'.P.A.left, ⊤ ≤ ψ ⁻¹ᵁ D'.P.L.U (J' ψ) := fun ψ y _ =>
    (hc _ ψ y _ (ν.good (ψ ≫ proj hD) (x := y) trivial)).1
  have hJ' : Good D'.P.L z J' := fun ψ => good' ψ trivial
  have one : ∀ ψ : Sp F ⟶ D'.P.A.left, Geo.Tor.gw hD.w ψ z (ν.J (ψ ≫ proj hD)) (J' ψ) = 1 := fun ψ =>
    (hc _ ψ z _ (hJ (ψ ≫ proj hD))).2
  have one' : ∀ ψ : Sp F ⟶ D'.P.A.left, om hD.w z ν.J J' ψ = 1 := one
  have one'' : ∀ x : TF (R := R') F ⟶ D'.P.A, wVal hD.w z ν.J J' x = 1 := fun x => one x.left
  let P : (TF (R := R') F ⟶ D'.P.A) ≃* (TF (R := R) F ⟶ D.P.A) :=
    MulEquiv.ofBijective (MonoidHom.mk' (pushF (pull_grp hD) hT) (pushF_mul _ _))
      ⟨pushF_injective (pull_grp hD) hT, pushF_surjective (pull_grp hD) hT⟩
  obtain ⟨eA, heA⟩ : ∃ eA : N.A ≃* (TF (R := R') F ⟶ D'.P.A), ∀ x, pushF (pull_grp hD) hT (eA x) = ν.eA x :=
    ⟨ν.eA.trans P.symm, fun x => P.apply_symm_apply _⟩
  have hl : ∀ x, (eA x).left ≫ proj hD = (ν.eA x).left := fun x => congrArg (fun q => q.left) (heA x)
  obtain ⟨eX, heX⟩ : ∃ eX : N.X ≃+ D'.X, ∀ y, hD.xe (eX y) = ν.eX y :=
    ⟨ν.eX.trans hD.xe.symm, fun y => hD.xe.apply_symm_apply _⟩
  have rig : vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom ν.J =
      vF (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (TF (R := R') F).hom J' := by
    have e := ArcPull.rig_val hD (Z := Sp F) _ _ hj hJ hJ'
    rw [one', _root_.one_mul] at e
    exact vF_congr hJ hJ' ((val_pull hJ _ _ _).symm.trans (e.trans (val_pull hJ' _ _ _)))
  refine ⟨{
    J := J', good := good', th := th', th_gen := hgen, eA := eA, eX := eX
    c_eq := fun χ => ?_, θ_eq := fun x y u => ?_, σ_eq := fun x => ?_, th_eq := fun x => ?_
    ψ_eq := fun χ => ?_ }, heX, hl⟩
  · apply pushF_injective (pull_grp hD) hT
    rw [heA, ν.c_eq, ← heX]
    exact Over.OverMorphism.ext ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
      (hT.trans (Category.id_comp _).symm) _).trans (Category.id_comp _)).symm
  · have k := thS_push (pull_grp hD) hT ((isGen_iff _).1 hD.w_gen) hG hJ hJ' (eA x) (eA y) (eA u)
    simp only [one'', heA, inv_one, _root_.one_mul] at k
    exact (ν.θ_eq x y u).trans (vF_congr hJ hJ' k)
  · have k := PsiEvenPull.sym_pull hG hD (Z := Sp F) (eA x).left z hJ hJ'
    rw [one, one, inv_one, _root_.one_mul, _root_.one_mul] at k
    refine (ν.σ_eq x).trans (vF_congr hJ hJ' (Eq.trans ?_ k))
    exact congrArg (fun q => val (Z := Sp F) D.sym q z ν.J) (hl x).symm
  · have k := hth (Sp F) (eA x).left z ν.J J' hJ hJ'
    rw [one, Units.val_one, _root_.one_mul] at k
    rw [← rig, ν.th_eq x]
    refine (stalkConst z).injective ((const_sF _ _ hJ).trans (Eq.trans ?_ (k.trans (const_sF _ _ hJ').symm)))
    exact congrArg (fun q => sval (Z := Sp F) ν.th q z ν.J) (hl x).symm
  · have k := ArcPull.psi_val hD (Z := Sp F) _ _ hj hJ hJ' (eX χ)
    rw [one', inv_one, _root_.one_mul, heX] at k
    rw [← rig, ν.ψ_eq χ]
    exact congrArg (· * _) (vF_congr hJ hJ' k)

end GlobalTheory.ValuesStrictPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesOverSubfield
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ValuesSubfield
open GlobalTheory.TorusExt GlobalTheory.ArcExt

theorem exists_numOf_th {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N : NumD F} (ν : NumOf D F N) (th : H0 D.P.L 1)
    (hth : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j) :
    ∃ (N₁ : NumD F) (ν₁ : NumOf D F N₁), ν₁.J = ν.J ∧ ν₁.th = th :=
  ⟨{ N with th := fun x => sF th (ν.eA x).left ν.J / rigVal ν },
    { ν with th := th, th_gen := hth, th_eq := fun _ => div_mul_cancel₀ _ (vF_ne_zero ν.good _ _) }, rfl, rfl⟩

theorem exists_values_subfield : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F F' : Type) [Field F] [Field F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ (N' : NumD F') (ν' : NumOf D F' N'), ∃ (N : NumD F) (ν : NumOf D F N) (I : NumD.Hom f N N'), (∀ y, ν'.eX (I.e y) = ν.eX y) ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (c : N.Gt) (c' : N'.Gt), QkExt f p p' → ν.Pt p.g c → ν'.Pt p'.g c' → I.Rel c c' := by
  intro hG R _ _ D he hb F F' _ _ _ _ f hf N' ν'
  obtain ⟨N₀, ν₀, h₀⟩ := ValuesExist.exists_numOf D F hG he hb ν'.th ν'.th_gen (fun ψ => ν'.J (spMap f ≫ ψ))
    fun ψ z _ => (Subsingleton.elim (α := PrimeSpectrum F) (spMap f (IsLocalRing.closedPoint F')) z) ▸
      ν'.good (spMap f ≫ ψ) (Set.mem_univ (IsLocalRing.closedPoint F'))
  obtain ⟨N, ν, h₁, h₂⟩ := exists_numOf_th ν₀ ν'.th ν'.th_gen
  have hJ : ∀ ψ, ν'.J (spMap f ≫ ψ) = ν.J ψ := fun ψ => by rw [h₁, h₀]
  refine ⟨N, ν, numHom f hf ν ν' hJ h₂.symm, eX_numHom f hf ν ν' hJ h₂.symm, fun k p p' c c' h hc hc' => ?_⟩
  obtain rfl := (qkExt_iff hb f hf p p').1 h
  exact numHom_rel f hf ν ν' hJ h₂.symm hc hc'

end GlobalTheory.ValuesSubfield
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalAdjoinAlgebraicStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integrally_closed_extension_of_adjoin : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (s : AlgebraicClosure (FractionRing R)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R →+* R₂) (h' : FractionRing R →+* FractionRing R₂) (e : FractionRing R₂ →+* AlgebraicClosure (FractionRing R)), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R _ r) = algebraMap R₂ _ (h r)) ∧ e.comp h' = algebraMap _ _ ∧ (∃ s₂, e s₂ = s) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (g : FractionRing R₂ →+* F), ∃ g' : AlgebraicClosure (FractionRing R) →+* F, g'.comp e = g := by
  first | exact @GlobalTheory.exists_finite_normal_adjoin_algebraic | exact GlobalTheory.exists_finite_normal_adjoin_algebraic | (intros; apply GlobalTheory.exists_finite_normal_adjoin_algebraic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteNormalExtContainingAlgebraicElements
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis

theorem exists_extend_of_isAlgebraic {A B F : Type} [Field A] [Field B] [Field F] [IsAlgClosed F] [Algebra A B]
    [Algebra.IsAlgebraic A B] (g : A →+* F) : ∃ σ : B →+* F, ∀ x, σ (algebraMap A B x) = g x := by
  letI : Algebra A F := g.toAlgebra
  let σ : B →ₐ[A] F := IsAlgClosed.lift
  exact ⟨(σ : B →+* F), fun x => σ.commutes x⟩

theorem exists_finite_normal_containing : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [CharZero R₁], IsIntegrallyClosed R₁ → ∀ (I : Type) [Finite I] (Φ : I → AlgebraicClosure (FractionRing R₁)), ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (h : R₁ →+* R₂) (h' : FractionRing R₁ →+* FractionRing R₂) (j : FractionRing R₂ →+* AlgebraicClosure (FractionRing R₁)) (Φ₂ : I → FractionRing R₂), Function.Injective h ∧ h.Finite ∧ IsIntegrallyClosed R₂ ∧ (∀ r, h' (algebraMap R₁ _ r) = algebraMap R₂ _ (h r)) ∧ (∀ x, j (h' x) = algebraMap (FractionRing R₁) _ x) ∧ (∀ i, j (Φ₂ i) = Φ i) ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] (ga : FractionRing R₂ →+* F), ∃ σ : AlgebraicClosure (FractionRing R₁) →+* F, ∀ x, σ (j x) = ga x := by
  intro R₁ _ _ _ _ hIC I _ Φ
  let K := FractionRing R₁
  let L := AlgebraicClosure K
  let K₂ : IntermediateField K L := IntermediateField.adjoin K (Set.range Φ)
  haveI : Finite (Set.range Φ) := (Set.finite_range Φ).to_subtype
  haveI : FiniteDimensional K K₂ :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : CharZero K := IsFractionRing.charZero_of_isFractionRing R₁
  haveI : Algebra.IsSeparable K K₂ := inferInstance
  let R₂ := integralClosure R₁ K₂
  haveI : IsFractionRing R₂ K₂ := IsIntegralClosure.isFractionRing_of_finite_extension R₁ K K₂ R₂
  haveI hfin : Module.Finite R₁ R₂ := IsIntegralClosure.finite R₁ K K₂ R₂
  let e : FractionRing R₂ ≃ₐ[R₂] K₂ := FractionRing.algEquiv R₂ K₂
  have hinj : Function.Injective (algebraMap R₁ K₂) := by
    rw [IsScalarTower.algebraMap_eq R₁ K K₂]
    exact (algebraMap K K₂).injective.comp (IsFractionRing.injective R₁ K)
  refine ⟨R₂, inferInstance, inferInstance, algebraMap R₁ R₂,
    (e.symm : K₂ →+* FractionRing R₂).comp (algebraMap K K₂),
    (algebraMap K₂ L).comp (e : FractionRing R₂ →+* K₂),
    fun i => e.symm ⟨Φ i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    apply hinj
    rw [IsScalarTower.algebraMap_apply R₁ R₂ K₂ a, IsScalarTower.algebraMap_apply R₁ R₂ K₂ b, hab]
  · exact RingHom.finite_algebraMap.mpr hfin
  · exact integralClosure.isIntegrallyClosedOfFiniteExtension K
  · intro r
    change e.symm (algebraMap K K₂ (algebraMap R₁ K r)) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₁ R₂ K₂, AlgEquiv.commutes]
  · intro x
    change algebraMap K₂ L (e (e.symm (algebraMap K K₂ x))) = _
    rw [e.apply_symm_apply, ← IsScalarTower.algebraMap_apply]
  · intro i
    change algebraMap K₂ L (e (e.symm _)) = _
    rw [e.apply_symm_apply]; rfl
  · intro F _ _ ga
    haveI : Algebra.IsAlgebraic K₂ L := Algebra.IsAlgebraic.tower_top (K := K) K₂
    obtain ⟨σ, hσ⟩ := exists_extend_of_isAlgebraic (A := K₂) (B := L) (ga.comp (e.symm : K₂ →+* FractionRing R₂))
    refine ⟨σ, fun x => (hσ (e x)).trans ?_⟩
    exact congrArg ga (e.symm_apply_apply x)

end GlobalTheory.OneBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullAll
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.AllLevels

theorem isThetaPt_comp {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I I' : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) (f : I' → I) : IsThetaPt P k (fun i => x (f i)) fun i => v (f i) := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H.2.2 p
  exact ⟨V, hV, th, s1, α, τ, fun i => U (f i), fun i => s2 (f i), fun i => w (f i), u, a1, a2, a3, a4,
    fun i => a5 _, fun i => a6 _, fun i => a7 _, fun i => a8 _⟩

theorem isThetaPt_mul {S : Scheme.{0}} {P : PolAV S} {k : ℕ} {T : Over S} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : IsThetaPt P k x v) : IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4,
    a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem ev_nsmul {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso D k Q act e) (M r : ℕ) (a : D.La) : I.ev M (r • a) = I.ev M a ^ r := by
  induction r with
  | zero =>
    have := I.add M 0 0
    rw [add_zero] at this
    rw [zero_smul, pow_zero]
    exact left_eq_mul.1 this
  | succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem theta_down (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] (o : Full D K) {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    {v v' : D.La → K} (c : Kˣ) (hc : ∀ x, v (r • x) = c * v' x) (h : o.Theta (r * m) v) : o.Theta m v' := by
  have e : ∀ a, o.I.ev ((r * m) ^ 2) (r • a) ^ r = o.I.ev (m ^ 2) a := fun a => by
    rw [ev_nsmul, ← pow_mul, ← o.I.tower (m ^ 2) (r * r) (by positivity) (by positivity)]
    congr 2; ring
  have h₁ := GlobalTheory.T.isThetaPt_pow_of_isThetaPt_mul hL K o.P r m D.La _ _ (fun a => by
    rw [e]; exact (o.I.onto _ (by positivity) _).2 ⟨a, rfl⟩) (isThetaPt_comp h fun a => r • a)
  have h₂ := isThetaPt_mul (fnOf ((c⁻¹ : Kˣ) : K)) ((c⁻¹).isUnit.map _) h₁
  simp only [e] at h₂
  unfold Full.Theta
  convert h₂ using 2 with a
  rw [hc]
  exact (congrArg fnOf (Units.inv_mul_cancel_left c (v' a)).symm).trans (map_mul _ _ _)

theorem exists_iso (hL : Laws) (h₁ : ThetaPtDeterminesSt) (h₂ : EndDeterminedOnTorsionSt) (D : Datum H) {n : ℕ}
    (hn : n.Prime) (ho : Odd n) : ∃ J₀, ∀ J, J₀ ≤ J → ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (v : D.La → K),
      o.I.ζ ((n ^ J) ^ 2) = o'.I.ζ ((n ^ J) ^ 2) → o.Theta (n ^ J) v → o'.Theta (n ^ J) v →
      ∃ φ : o.P.A ≅ o'.P.A, IsPolIso o.P o'.P φ ∧
        (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) := by
  letI := H.starRing
  obtain ⟨bas, hbas⟩ := GlobalTheory.ZM.exists_isSympBasis E H D
  generalize Module.finrank ℚ E / 2 * (D.p + D.q) = g at bas hbas
  choose cn hcn using exists_starNormLE_of_isCMField E (fun a => H.bar_eq a)
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  let B := ((n ^ 2) ^ 2) ^ g * g.factorial + 4 ^ g * g.factorial * (2 * s.sup cn)
  refine ⟨B + 4, fun J hJ K _ _ o o' v hζ hv hv' => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 4 := ⟨J - 4, by omega⟩
  have hB : B < n ^ (j + 4) := lt_of_le_of_lt (by omega) (Nat.lt_pow_self hn.one_lt)
  have hp : 0 < n ^ (j + 4) := pow_pos hn.pos _
  set M := (n ^ (j + 4)) ^ 2 with hM
  have hM0 : 0 < M := pow_pos hp _
  haveI : NeZero M := ⟨hM0.ne'⟩
  haveI := o.charZero
  obtain ⟨hg, lev, hb, hl⟩ := GlobalTheory.T.exists_level_of_full' hL E H D g bas hbas K o M hM0
  have Q := GlobalTheory.T.exists_level_of_full' hL E H D g bas hbas K o' M hM0
  rw [← hζ] at Q
  obtain ⟨hg', lev', hb', hl'⟩ := Q
  let lab : (Fin (2 * g) → ZMod M) → D.La := fun a => bas fun i => ((a i).val : ℤ)
  have hlab : ∀ a : Fin (2 * g) → ZMod M, (fun i => (((a i).val : ℤ) : ZMod M)) = a := fun a => funext fun i => by simp
  have e : levelPoint lev hg = fun a => o.I.ev M (lab a) := funext fun a => by rw [← hl, hlab]
  have e' : levelPoint lev' hg' = fun a => o'.I.ev M (lab a) := funext fun a => by rw [← hl', hlab]
  have key : ∀ c, c ≤ s.sup cn → 4 ^ g * g.factorial * (2 * c) < M ^ 2 := fun c hc =>
    calc 4 ^ g * g.factorial * (2 * c) ≤ B := le_add_left (by gcongr)
      _ < n ^ (j + 4) := hB
      _ ≤ M := Nat.le_self_pow two_ne_zero _
      _ ≤ M ^ 2 := Nat.le_self_pow two_ne_zero _
  obtain ⟨φ, hφ, hφb⟩ := h₁ g n 2 j _ (n ^ (j + 4)) hn ho le_rfl rfl (by ring) (lt_of_le_of_lt (Nat.le_add_right _ _) hB) K
    (Nat.cast_ne_zero.2 hn.pos.ne') o.P o'.P hg hg' _ lev lev' (fun a => fnOf (v (lab a)))
    (e ▸ isThetaPt_comp hv lab) (e' ▸ isThetaPt_comp hv' lab)
  haveI := hφ.1
  have hev : ∀ a, o.I.ev M a ≫ φ.hom = o'.I.ev M a := fun a => by
    obtain ⟨c, rfl⟩ := bas.surjective a
    rw [← hl, ← hl', ThetaPtDet.levelPoint_eq, ThetaPtDet.levelPoint_eq, ThetaPtDet.linComb_comp]
    exact congrArg (linComb · _) (funext hφb)
  refine ⟨φ, hφ, fun x => ?_⟩
  have hx : x ∈ Submodule.span ℤ (s : Set (𝓞 E)) := hs ▸ Submodule.mem_top
  have add : ∀ a b, o.oa.act (a + b) = o.oa.act a * o.oa.act b := o.oa.map_add
  have add' : ∀ a b, o'.oa.act (a + b) = o'.oa.act a * o'.oa.act b := o'.oa.map_add
  let f : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (o.oa.act a ≫ φ.hom))
    fun a b => by rw [add, MonObj.mul_comp]; rfl
  let f' : 𝓞 E →+ Additive (o.P.A ⟶ o'.P.A) := AddMonoidHom.mk' (fun a => Additive.ofMul (φ.hom ≫ o'.oa.act a))
    fun a b => by rw [add', MonObj.comp_mul]; rfl
  have : f = f' := AddMonoidHom.eq_of_eqOn_dense (s := (s : Set (𝓞 E)))
    (by rw [← Submodule.span_int_eq_addSubgroupClosure, hs]; rfl) fun a ha => by
    refine congrArg Additive.ofMul (h₂ g (cn a) M (key _ (Finset.le_sup ha)) K (Nat.cast_ne_zero.2 hM0.ne') o.P o'.P hg hg'
      φ hφ _ o.oa o'.oa a (hcn a) fun y hy => ?_)
    obtain ⟨b, rfl⟩ := (o.I.onto M hM0 y).1 hy
    have l := o.I.lin M a b
    have l' := o'.I.lin M a b
    rw [← Category.assoc, ← Category.assoc, ← l, hev, hev, l']
  exact Additive.ofMul.injective (DFunLike.congr_fun this x)

theorem exists_full_all (hL : Laws) (h₁ : ThetaPtDeterminesSt) (h₂ : EndDeterminedOnTorsionSt) {K : Type} [Field K]
    [IsAlgClosed K] (ρ : K) (ζ : ℕ → Kˣ) (hζ : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) (v : ℕ → D.La → K)
    (hv : ∀ r m, Odd r → Odd m → ∃ c : Kˣ, ∀ x, v (r * m) (r • x) = c * v m x) {n : ℕ} (hn : n.Prime) (ho : Odd n)
    (h : ∀ j, 2 ≤ j → ∃ o : Full D K, o.ρ = ρ ∧ o.I.ζ ((n ^ j) ^ 2) = ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (v (n ^ j))) :
    ∃ o : Full D K, o.ρ = ρ ∧ ∀ j, o.I.ζ (n ^ j) = ζ (n ^ j) ∧ o.Theta (n ^ j) (v (n ^ j)) := by
  obtain ⟨J, hJ⟩ := exists_iso hL h₁ h₂ D hn ho
  choose o hρ hz ht using fun j => h (J + 2 + j) (by omega)
  have hp : ∀ i, 0 < n ^ i := fun i => pow_pos hn.pos i
  have th : ∀ j i, i ≤ J + 2 + j → (o j).Theta (n ^ i) (v (n ^ i)) := fun j i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hi
    obtain ⟨c, hc⟩ := hv (n ^ d) (n ^ i) ho.pow ho.pow
    refine theta_down hL (o j) (hp d) (hp i) c hc ?_
    rw [← pow_add, ← hd]; exact ht j
  have ze : ∀ j i, i ≤ 2 * (J + 2 + j) → (o j).I.ζ (n ^ i) = ζ (n ^ i) := fun j i hi => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    have := hz j
    rw [← pow_mul, mul_comm, hd, pow_add] at this
    rw [← (o j).I.ζ_pow _ _ (hp i) (hp d), this, hζ _ _ (hp i) (hp d)]
  have ze' : ∀ j i, i ≤ J + 2 + j → (o j).I.ζ ((n ^ i) ^ 2) = ζ ((n ^ i) ^ 2) := fun j i hi => by
    rw [← pow_mul]; exact ze j _ (by omega)
  choose φ hφ hact using fun j => hJ (J + 2) (by omega) K (o j) (o 0) _
    ((ze' j _ (by omega)).trans (ze' 0 _ le_rfl).symm) (th j _ (by omega)) (th 0 _ le_rfl)
  choose I hIζ _ hI using fun j => GlobalTheory.T.exists_tateIso_of_isPolIso hL E H D K (o j) (o 0) (φ j) (hφ j) (hact j)
  obtain ⟨I', hI'⟩ := GlobalTheory.T.exists_limitPoint_tateIso_sequence E H D K _ _ _ I
  refine ⟨{ o 0 with I := I' }, hρ 0, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj, -, e⟩ := hI' _ (hp i) i
    exact e.trans ((congrFun (hIζ j) _).trans (ze j i (by omega)))
  · obtain ⟨j, hj, e, -⟩ := hI' _ (pow_pos (hp i) 2) i
    have := hI j _ _ (th j i (by omega))
    unfold Full.Theta at this ⊢
    dsimp only at this ⊢
    rw [e]; exact this

end GlobalTheory.Ex.AllLevels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_normalised_unit (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a b c : ℤ)
    (hc : c = a - b)
    (α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (h₀ : α₀.IsGen) :
    ∃ (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -b])) (d : Γ(T.left, ⊤)ˣ),
      α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT A 1).left) (rigT A L ρ T c) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        val α r z J = gm (r ≫ (fst T A).left) z ⊤ d * val α₀ r z J := by
  have hγ := DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ (ptSecT A 1).left)) (NormTheta.rigT_isGen (T := T) hρ c)
  obtain ⟨d, hd⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero]) hγ
  obtain ⟨α, hα, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ m).left]) (ε' := ![a, -b])
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, hc]
      rw [← zpow_add, ← zpow_add, show -a + - -b + (a - b) = 0 by ring, zpow_zero, _root_.mul_one])
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (ptSecT A 1).left)) (rigT A L ρ T c)) (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ hγ _))
  refine ⟨α, d, hα, corr_of_val hL fun y J hJ => ?_, fun Z r z J hJ => ?_⟩
  · rw [val_pull hJ, hv _ _ y J hJ, val_mul hJ, val_pull hJ, Category.assoc, NormTheta.ptSec_fst, Category.comp_id,
      val_mul hJ, val_inv, val_pull hJ, mul_inv_cancel_left]
  · rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, hd _ _ z J hJ, Category.comp_id, mul_comm]

theorem isGenSec_smul {k : ℤ} {th : LB.Sec (LPow A L k T)} (H : IsGenSec A L k th) (e : Γ(T.left, ⊤)ˣ) :
    IsGenSec A L k (SecM.toSec A ((e : Γ(T.left, ⊤)) • SecM.ofSec A th)) := fun s => by
  obtain ⟨r, hr⟩ := H s
  have e₁ : SecM.ofSec A s = r • SecM.ofSec A th := Subtype.ext (funext hr)
  have e₂ : SecM.ofSec A s = (r * (e⁻¹ : Γ(T.left, ⊤)ˣ)) • ((e : Γ(T.left, ⊤)) • SecM.ofSec A th) := by
    rw [← mul_smul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one, e₁]
  exact ⟨_, fun j => congrArg (fun q => q.1 j) e₂⟩

theorem exists_thG (hL : L.IsLB) {ρ : LB.Gen (L.pull (eSec A))} (hρ : ρ.IsGen) (m : ℕ) (a : ℤ)
    (ha : a = ((m ^ 2 : ℕ) : ℤ)) {I : Type} {x : I → (T ⟶ A)} (hx : ∀ i, x i ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L ((1 : ℕ) : ℤ) T)} {s₁ : LB.Sec (LPow A L a T)}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ A).left) (fun _ => a))}
    {U : I → ThetaGrp A L a T} {s₂ : I → LB.Sec (LPow A L a T)} {w : I → Γ(T.left, ⊤)}
    (hα : α.IsGen) (hτ : τ.IsGen)
    (h₁ : IsTwistPull A L (mulT A T m) (snd T A ^ m) (lift_snd _ _) a ((1 : ℕ) : ℤ) α th s₁)
    (hU : ∀ i, SymLift A L a (m ^ 2) (x i) (U i)) (h₂ : ∀ i, IsActOf A L a (U i) s₁ (s₂ i))
    (hw : ∀ i, IsValueAt A L a (s₂ i) 1 τ (w i)) :
    ∃ e : Γ(T.left, ⊤)ˣ, ∀ i, ThG A L ρ m th (x i) (e * w i) := by
  subst ha
  obtain ⟨α', d, hα', hn, hv⟩ := exists_normalised_unit hL hρ m _ _ (((m ^ 2 : ℕ) : ℤ) - 1) rfl α hα
  obtain ⟨b, hb⟩ := SymLiftOdd.exists_const hL (𝟙 T.left) (𝟙 T.left) (Category.comp_id _) (fun v => ⟨v, rfl⟩)
    (fun U _ f => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, NormTheta.one_left, zpow_neg,
        mul_inv_cancel])
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (NormTheta.rigT_isGen (T := T) hρ ((m ^ 2 : ℕ) : ℤ))))
  refine ⟨d * b, fun i => ⟨hx i, SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i)), α',
    SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁), U i, hα', hn, ?_, hU i, ?_, fun y J hJ => ?_⟩⟩
  · refine VVRank.isTwistPull_of_sv A hL hα' fun y J hJ => ?_
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁)) (t := s₁) (c := d) (fun j => rfl) _ y hJ,
      VVRank.sv_of_isTwistPull A h₁ (𝟙 _) y hJ, hv _ _ y J hJ, gs_unit _ _ ⊤ trivial, Units.val_mul, _root_.mul_assoc]
  · refine VVRank.isTwistPull_of_sv A hL (U i).isGen fun y J hJ => ?_
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A s₁)) (t := s₁) (c := d) (fun j => rfl) _ y hJ,
      sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i))) (t := s₂ i) (c := d) (fun j => rfl) _ y hJ,
      VVRank.sv_of_isTwistPull A (h₂ i) (𝟙 _) y hJ, Category.assoc, ← Over.comp_left, translT, lift_fst, mul_left_comm]
  · have q := ThetaPtMove.sv_of_isValueAt (hw i) (𝟙 _) y hJ
    have q' := hb _ (𝟙 _) y J hJ
    rw [val_mul hJ, val_inv, Category.comp_id, mul_inv_eq_iff_eq_mul] at q'
    rw [Category.id_comp, q', Units.val_mul, ← gs_unit _ _ ⊤ trivial] at q
    rw [sv_of_eq_mul (s := SecM.toSec A ((d : Γ(T.left, ⊤)) • SecM.ofSec A (s₂ i))) (t := s₂ i) (c := d) (fun j => rfl) _ y hJ,
      q, ptSecT_fst, Units.val_mul, gs_mul _ y ⊤ trivial, gs_mul _ y ⊤ trivial]
    ring

end

theorem exists_gen_thG_of_isThetaPt : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (ρ : LB.Gen (P.L.pull (eSec P.A))), ρ.IsGen → ∀ (m : ℕ) (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → K), (∀ i, x i ^ (m ^ 2) = 1) → IsThetaPt P m x (fun i => fnOf (v i)) → ∃ th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))), IsGenSec P.A P.L ((1 : ℕ) : ℤ) th ∧ ∀ i, ThG P.A P.L ρ m th (x i) (fnOf (v i)) := by
  intro K _ P ρ hρ m Ix x v hx H
  have : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, h₁, hU, h₂, hw, hv⟩ := ThetaCoord.isThetaPtOver_of_subsingleton P H
  obtain ⟨e, he⟩ := exists_thG P.isLB hρ m ((m : ℤ) ^ 2) (Nat.cast_pow m 2).symm hx (th := th) (α := α) hα hτ h₁ hU h₂ hw
  refine ⟨_, isGenSec_smul hth (u * e⁻¹), fun i => ?_⟩
  have q := ThG.smul P.isLB (a := ((u * e⁻¹ : Γ((baseOver (Sp K)).left, ⊤)ˣ) : Γ((baseOver (Sp K)).left, ⊤)))
    (th' := SecM.toSec P.A (((u * e⁻¹ : Γ((baseOver (Sp K)).left, ⊤)ˣ) : Γ((baseOver (Sp K)).left, ⊤)) • SecM.ofSec P.A th))
    rfl (he i)
  rw [Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, ← hv i] at q
  exact q

end GlobalTheory.Ex.OneGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeometricTestMapClassicalPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometricTest_map_classicalPoint : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), S.Big → ρ.HasGeo → (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u), Nonempty (Q.TMap t c)) ∧ ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y := by
  first | exact @GlobalTheory.ZH.exists_geoTest_tMap_and_centre | exact GlobalTheory.ZH.exists_geoTest_tMap_and_centre | (intros; apply GlobalTheory.ZH.exists_geoTest_tMap_and_centre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValuesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_degeneration_values : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∃ (N : NumD F) (ν : NumOf D F N), ν.Integral S := by
  first | exact @GlobalTheory.ValuesExist.exists_integral_values | exact GlobalTheory.ValuesExist.exists_integral_values | (intros; apply GlobalTheory.ValuesExist.exists_integral_values <;> assumption)
end

