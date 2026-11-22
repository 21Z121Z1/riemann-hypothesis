import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0119
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesExist
open GlobalTheory.TorusExt GlobalTheory.IndivisibleSection

section Sym
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)
  {s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])}

theorem prod_sym {T : Over S} (x : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ k : Fin 2, h (x.left ≫ ![(ι[A]).left, 𝟙 A.left] k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h (x⁻¹).left * (h x.left)⁻¹ := by
  rw [Fin.prod_univ_two]
  simp [Hom.inv_def]

theorem val_sym_one (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L))
    {T : Over S} {z : T.left} {J} (hJ : Good L.L z J) : val s (1 : T ⟶ A).left z J = 1 := by
  have := val_corr hJ hr (toUnit T).left
  rw [val_one, val_pull hJ] at this
  exact this

theorem val_sym_mul (hs : Function.Surjective (A ⊗ A).hom.appTop.hom) (hg : s.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L))
    {T : Over S} {z : T.left} {J} (hJ : Good L.L z J) (x y : T ⟶ A) :
    val s (x * y).left z J * cubV c z J x x⁻¹ y⁻¹ = val s x.left z J * val s y.left z J * cubV c z J y y⁻¹ x := by
  have vs : ∀ {T : Over S} {z : T.left} {J} (_ : Good L.L z J) (r : T ⟶ A ⊗ A) (a : A ⊗ A ⟶ A),
      val (LB.pullGen L.L _ _ s a.left) r.left z J = val s (r ≫ a).left z J := fun hJ r a => val_pull hJ _ _ _
  have v : ∀ {T : Over S} {z : T.left} {J} (_ : Good L.L z J) (x y : T ⟶ A),
      val (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ s (fst A A * snd A A).left)
        (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (fst A A) (lift (fst A A)⁻¹ (snd A A)⁻¹)).left)) (lift x y).left z J =
        val s (x * y).left z J * cubV c z J x x⁻¹ y⁻¹ ∧
      val (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ s (fst A A).left)
        (LB.pullGen L.L _ _ s (snd A A).left))
        (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (snd A A) (lift (snd A A)⁻¹ (fst A A))).left)) (lift x y).left z J =
        val s x.left z J * val s y.left z J * cubV c z J y y⁻¹ x := fun hJ x y => by
    refine ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs hJ _ _) (val_cub c _ hJ _ _ _))).trans ?_,
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (vs hJ _ _) (vs hJ _ _))) (val_cub c _ hJ _ _ _))).trans ?_⟩ <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]
  rw [← (v hJ x y).1, ← (v hJ x y).2]
  refine gen_unique' L.isLB (fun U _ h => ?_) (A ⊗ A).hom (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left
    (Over.w _) hs
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg _) (DVR.pullGen_isGen _ _ _ _ c.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg _)
      (DVR.pullGen_isGen _ _ _ _ hg _)) (DVR.pullGen_isGen _ _ _ _ c.isGen _)) (fun w I hI => ?_) _ _ z J hJ
  · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) (prod_sym _ h) (prod_sym _ h))) (prod_cub _ _ _ h))).trans
      (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_sym _ h) (prod_cub _ _ _ h))).symm)
    simp only [mul_inv_cancel, _root_.one_mul, mul_inv, mul_comm (snd A A) (fst A A), mul_comm (snd A A)⁻¹ (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (v (T := 𝟙_ (Over S)) hI 1 1).1.trans (Eq.trans ?_ (v (T := 𝟙_ (Over S)) hI 1 1).2.symm)
    simp only [_root_.mul_one, inv_one, val_sym_one (T := 𝟙_ (Over S)) hr hI]
end Sym

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem coe_val (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    ((stalkUnits z).symm (val t r z J) : F) = vF t r J := by
  refine (stalkConst z).injective ?_
  rw [← stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)
end Val

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_th (hS : SecBaseChangeSt) [IsLocalRing R] [IsNoetherianRing R] :
    ∃ th : H0 D.P.L 1, ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j := by
  have hL := D.P.isLB
  obtain ⟨b, hb⟩ := exists_generator D hS
  obtain ⟨th, hth⟩ := exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left) (ε' := fun _ => ((1 : ℕ) : ℤ))
    (fun U _ h => by rw [prod_fam_zero]; simp) b
  refine ⟨th, fun s => ?_⟩
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := D.famφB 0) (ε' := DegPre.famε 1)
    (fun U _ h => by rw [prod_fam_zero]; simp) s
  obtain ⟨a, ha, -⟩ := hb s'
  refine ⟨a, secIsMul_of_sval hL fun y J hJ => ?_⟩
  rw [← hs' _ _ y J hJ, sval_of_secIsMul ha _ y hJ, hth _ _ y J hJ, Category.id_comp]

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem exists_ext (S : ValuationSubring F) (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S)
    (x : TF (R := R) F ⟶ D.P.A) : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left := by
  haveI := D.P.isAb.proper
  have hE : ValuativeCriterion.Existence D.P.A.hom := by
    have h : UniversallyClosed D.P.A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let f : R →+* S := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).codRestrict S hS
  let Q : ValuativeCommSq D.P.A.hom :=
    { R := S, K := F, i₁ := x.left, i₂ := Spec.map (CommRingCat.ofHom f),
      commSq := ⟨by
        refine (Over.w x).trans ?_
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, h1, -⟩⟩ := hE Q
  exact ⟨l, h1⟩

theorem exists_gauge (S : ValuationSubring F) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
    ∃ J : (Sp F ⟶ X) → L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) ∧ ∀ ψ, (∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ) →
      ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ L.U (J ψ) := by
  have key : ∀ ψ : Sp F ⟶ X, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j ∧ ((∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ) →
      ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ L.U j) := fun ψ => by
    by_cases h : ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := exists_chart hL (x₀ (IsLocalRing.closedPoint S))
      have e : x₀ ⁻¹ᵁ L.U j = ⊤ := DVR.eq_top_of_closedPoint_mem _ hj
      exact ⟨j, fun w _ => e.ge (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, e.ge⟩⟩
    · obtain ⟨j, hj⟩ := exists_chart hL (ψ (IsLocalRing.closedPoint F))
      exact ⟨j, (DVR.eq_top_of_closedPoint_mem (ψ ⁻¹ᵁ L.U j) hj).ge, fun h' => (h h').elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, h₂⟩

theorem exists_numOf (hG : GlobalFnsSt) (he : D.PsiEven) (hb : D.TauBimult) (th : H0 D.P.L 1)
    (hth : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j)
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (good : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) :
    ∃ (N : NumD F) (ν : NumOf D F N), ν.J = J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ : Good D.P.L z J := fun ψ => good ψ trivial
  let e := (stalkUnits z).symm
  have C : IsCub (cubV D.cub (T := TF (R := R) F) z J) := isCub_cubV D.cub (T := TF (R := R) F) hJ
  have sj : Function.Surjective (D.P.A ⊗ D.P.A).hom.appTop.hom := by
    rw [← Over.w (snd D.P.A D.P.A)]
    exact surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2
  let ρ : ((Sp F).presheaf.stalk z)ˣ := val (Z := Sp F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom z J
  let p : D.X → ((Sp F).presheaf.stalk z)ˣ := fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z J
  have hτ : ∀ a b, val (Z := Sp F) (D.tau a b) (jFK (R := R) F) z J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _)))
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))
  have hx : ∀ χ, jFK (R := R) F ≫ D.xK χ = (DegPre.cF D F χ).left := fun χ => (Category.assoc _ _ _).symm
  let N : NumD F :=
    { A := TF (R := R) F ⟶ D.P.A
      θ := fun x y u => e (cubV D.cub (T := TF (R := R) F) z J x y u)
      cub := ⟨fun x y => by rw [C.face, map_one], fun x y u => by rw [C.s01], fun x y u => by rw [C.s12],
        fun x x' x'' y => by rw [← map_mul, ← map_mul, C.coc]⟩
      σ := fun x => e (val D.sym x.left z J)
      σ_one := (congrArg e (val_sym_one (L := ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩) D.sym_rig
        (T := TF (R := R) F) hJ)).trans (map_one e)
      σ_mul := fun x y => by
        rw [← map_mul, ← map_mul, ← map_mul]
        exact congrArg e (val_sym_mul D.cub sj D.sym_gen D.sym_rig (T := TF (R := R) F) hJ x y)
      th := fun x => sF th x.left J * ((e ρ)⁻¹ : Fˣ)
      X := D.X
      c := DegPre.cF D F
      c_add := fun a b => by
        rw [DegPre.cF, D.c_add]
        exact MonObj.comp_mul _ _ _
      ψ := fun χ => e (p χ * ρ)
      even := fun χ => by
        have h := val_corr hJ (he χ) (jFK (R := R) F)
        rw [val_mul hJ, val_pull hJ, hx] at h
        rw [← map_mul, mul_right_comm]
        exact congrArg (fun q => e (q * ρ)) h
      bimult := fun a a' b => by
        have h := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hτ _ _) (val_pull hJ _ _ _))).symm.trans
          ((val_corr hJ (hb a a' b) (jFK (R := R) F)).trans
            ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hτ _ _) (hτ _ _))))
        have h3 : jFK (R := R) F ≫ D.pt3 a a' b =
            (lift (DegPre.cF D F a) (lift (DegPre.cF D F a') (DegPre.cF D F b))).left := by
          let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
          refine congrArg CommaMorphism.left (show κ ≫ lift _ (lift _ _) = _ from ?_)
          simp only [comp_lift, comp_toUnit_assoc]
        rw [h3] at h
        simp only [← map_div, ← map_mul]
        refine congrArg e ?_
        have k : ∀ u v w, (u * ρ) / (v * ρ) / (w * ρ) = u * v⁻¹ * w⁻¹ * ρ⁻¹ := fun u v w => by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_div]
          abel
        rw [k, k, k]
        exact h }
  have hρ : (e ρ : F) = vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
    (TF (R := R) F).hom J := coe_val _ _ hJ
  exact ⟨N,
    { J := J, good := good, th := th, th_gen := hth, eA := MulEquiv.refl _, eX := AddEquiv.refl _
      c_eq := fun _ => rfl
      θ_eq := fun x y u => coe_val _ _ hJ
      σ_eq := fun x => coe_val _ _ hJ
      th_eq := fun x => by
        rw [← hρ]
        exact Units.inv_mul_cancel_right _ _
      ψ_eq := fun χ => by
        rw [← hρ, ← coe_val _ _ hJ]
        exact (congrArg Units.val (map_mul e _ _)).trans (Units.val_mul _ _) }, rfl⟩

theorem exists_integral_values : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∃ (N : NumD F) (ν : NumOf D F N), ν.Integral S := by
  intro hL R _ _ _ _ D he hb F _ _ S hS
  obtain ⟨th, hth⟩ := exists_th D hL.secBaseChange
  obtain ⟨J, good, hJ⟩ := exists_gauge F S D.P.isLB
  obtain ⟨N, ν, rfl⟩ := exists_numOf D F hL.globalFns he hb th hth J good
  exact ⟨N, ν, fun x => hJ _ (exists_ext D F S hS x)⟩

end GlobalTheory.ValuesExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.GaugeHom
open GlobalTheory.TorusExt GlobalTheory.ArcExt

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {L : LB X}
  {J J' : (Sp F ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) (hJ' : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ))
include hJ hJ'

theorem exists_trans : ∃ T : (Sp F ⟶ X) → Fˣ, ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y), sF s r J = (∏ k, T (r ≫ φ k) ^ ε k : Fˣ) * sF s r J' := by
  let y : Sp F := IsLocalRing.closedPoint F
  have hm : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ (L.U (J ψ) ⊓ L.U (J' ψ)) := fun ψ z hz => ⟨hJ ψ hz, hJ' ψ hz⟩
  have hv : ∀ ψ : Sp F ⟶ X, (gm ψ y (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ))).val =
      stalkConst y (valF ψ (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)).val) := fun ψ =>
    (gs_unit ψ y _ (hm ψ trivial) _).symm.trans (gs_eq_stalkConst ψ y (hm ψ) _)
  have hne : ∀ ψ : Sp F ⟶ X, valF ψ (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)).val ≠ 0 := fun ψ h =>
    (((Units.isUnit _).map _).map _).ne_zero ((dif_pos (hm ψ)).symm.trans h)
  refine ⟨fun ψ => Units.mk0 _ (hne ψ), fun Y K _ φ ε s r => (stalkConst y).injective ?_⟩
  have e : ∀ ψ : Sp F ⟶ X, gm ψ y (L.U (J ψ) ⊓ L.U (J' ψ)) (L.g (J ψ) (J' ψ)) =
      Units.map (stalkConst y).toMonoidHom (Units.mk0 _ (hne ψ)) := fun ψ => Units.ext (hv ψ)
  have a := sec_trans s r y (top_le_chart hJ φ r trivial) (top_le_chart hJ' φ r trivial)
  rw [map_mul]
  refine (gs_eq_stalkConst r y (top_le_chart hJ φ r) _).symm.trans
    (a.trans (congrArg₂ (· * ·) ?_ (gs_eq_stalkConst r y (top_le_chart hJ' φ r) _)))
  show _ = (Units.map (stalkConst y).toMonoidHom _).val
  rw [map_prod, trF]
  refine congrArg Units.val (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_zpow, e]

end Val

theorem exists_trans_ext {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {J : (Sp F ⟶ X) → L.ι} {J' : (Sp F' ⟶ X) → L.ι} (hJ : ∀ ψ : Sp F ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
    (hJ' : ∀ ψ : Sp F' ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J' ψ)) : ∃ T : (Sp F ⟶ X) → F'ˣ,
    (∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y),
      sF s (spMap f ≫ r) J' = (∏ k, T (r ≫ φ k) ^ ε k : F'ˣ) * f (sF s r J)) ∧
    ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ r : Sp F ⟶ Y,
      vF t (spMap f ≫ r) J' = (∏ k, T (r ≫ φ k) ^ ε k : F'ˣ) * f (vF t r J) := by
  obtain ⟨J₀, h₀, e₀⟩ := exists_gauge f hL hJ
  obtain ⟨T, hT⟩ := exists_trans hJ' h₀
  have k : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
      (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y),
      sF s (spMap f ≫ r) J' = (∏ k, T (spMap f ≫ r ≫ φ k) ^ ε k : F'ˣ) * f (sF s r J) := fun Y K _ φ ε s r => by
    rw [hT, sF_ext f hJ e₀]
    simp only [Category.assoc]
  exact ⟨fun ψ => T (spMap f ≫ ψ), k, fun Y K _ φ ε t ht r => k Y K φ ε (genSec t ht) r⟩

theorem exists_hom (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F]
    [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F')
    (hf : f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F') (N : NumD F) (N' : NumD F')
    (ν : NumOf D F N) (ν' : NumOf D F' N') (hth : ν'.th = ν.th) :
    ∃ I : NumD.Hom f N N', I.lam = 1 ∧ (∀ y, ν'.eX (I.e y) = ν.eX y) ∧
      ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (q : N.QT k) (q' : N'.QT k), QkExt f p p' → ν.QPt p q →
        ν'.QPt p' q' → q'.1.1.toAdd = I.e q.1.1.toAdd ∧ I.Rel q.1.2 q'.1.2 := by
  obtain ⟨T, hs, hg⟩ := exists_trans_ext f D.P.isLB ν.good ν'.good
  have hr : rigVal ν' = T (1 : TF (R := R) F ⟶ D.P.A).left * f (rigVal ν) := by
    have := hg _ _ (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig D.rig_gen (TF (R := R) F).hom
    rw [Fintype.prod_unique, zpow_one] at this
    refine Eq.trans ?_ this
    exact congrArg (fun r => vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r ν'.J)
      (Over.w (extMap (R := R) f hf)).symm
  have h0 : rigVal ν ≠ 0 := vF_ne_zero ν.good _ _
  let I : NumD.Hom f N N' :=
    { φ := ptHom f hf ν ν'
      h := fun x => T (ν.eA x).left / T (1 : TF (R := R) F ⟶ D.P.A).left
      h_one := by rw [map_one, div_self']
      θ_eq := fun x y u => by
        have e : N'.θ (ptHom f hf ν ν' x) (ptHom f hf ν ν' y) (ptHom f hf ν ν' u) =
            (∏ I : thK, T ((lift (ν.eA x) (lift (ν.eA y) (ν.eA u))).left ≫ thφ D.P.A (x3 D.P.A) I) ^ thε I) *
              Units.map f.toMonoidHom (N.θ x y u) := by
          refine Units.ext ?_
          show _ = _ * f (N.θ x y u : F)
          rw [ν'.θ_eq, ν.θ_eq, eA_ptHom, eA_ptHom, eA_ptHom, ← comp_lift, ← comp_lift]
          exact hg _ _ _ _ _ D.cub.isGen _
        rw [e, prod_cub]
        simp only [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
      σ_eq := fun x => by
        have e : N'.σ (ptHom f hf ν ν' x) = (T (ν.eA x)⁻¹.left * (T (ν.eA x).left)⁻¹) *
            Units.map f.toMonoidHom (N.σ x) := by
          refine Units.ext ?_
          show _ = _ * f (N.σ x : F)
          rw [ν'.σ_eq, ν.σ_eq, eA_ptHom]
          refine (hg _ _ _ _ _ D.sym_gen _).trans (congrArg (fun z : F'ˣ => z.val * _) ?_)
          rw [Fin.prod_univ_two]
          show T ((ν.eA x)⁻¹).left ^ (1 : ℤ) * T ((ν.eA x).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
          rw [Category.comp_id, zpow_one, zpow_neg, zpow_one]
        rw [e, map_inv]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel
      lam := 1
      th_eq := fun x => by
        have a : N'.th (ptHom f hf ν ν' x) * rigVal ν' = _ := ν'.th_eq _
        have b : N.th x * rigVal ν = _ := ν.th_eq _
        have c := hs _ _ _ _ ν.th (ν.eA x).left
        rw [Fintype.prod_unique, Category.comp_id, ← b, zpow_natCast, pow_one, map_mul] at c
        rw [eA_ptHom, hth, hr] at a
        have d := a.trans c
        have h1 : f (rigVal ν) ≠ 0 := (map_ne_zero f).2 h0
        rw [← _root_.mul_assoc, ← _root_.mul_assoc] at d
        have d' := mul_right_cancel₀ h1 d
        rw [_root_.one_mul, Units.val_div_eq_div_val, div_mul_eq_mul_div, ← d', mul_div_cancel_right₀ _ (Units.ne_zero _)]
      e := ν.eX.trans ν'.eX.symm
      c_eq := fun χ => ν'.eA.injective (by
        rw [ν'.c_eq, eA_ptHom, ν.c_eq, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
        exact (DVR.comp_cP D (extMap f hf) _).symm)
      ψ_eq := fun χ => by
        have e : N'.ψ (ν.eX.trans ν'.eX.symm χ) = ((T (ν.eA (N.c χ)).left)⁻¹ * T (1 : TF (R := R) F ⟶ D.P.A).left) *
            Units.map f.toMonoidHom (N.ψ χ) := by
          refine Units.ext ?_
          show _ = ((T (ν.eA (N.c χ)).left)⁻¹).val * (T (1 : TF (R := R) F ⟶ D.P.A).left).val * f (N.ψ χ : F)
          rw [ν'.ψ_eq, ν.ψ_eq, map_mul, AddEquiv.trans_apply, AddEquiv.apply_symm_apply, _root_.mul_mul_mul_comm]
          refine congrArg₂ (· * ·) ?_ hr
          have c := hg _ _ _ _ _ (D.psi_gen (ν.eX χ)) (jFK (R := R) F)
          rw [Fintype.prod_unique, zpow_neg, zpow_one] at c
          refine (congrArg (fun r => vF (D.psi (ν.eX χ)) r ν'.J)
            ((extMap_jFK f hf).trans (Category.id_comp _)).symm).trans (c.trans ?_)
          refine congrArg (fun z => ((T z)⁻¹).val * _) ?_
          rw [ν.c_eq]
          exact congrArg (fun z => z.left) (DVR.comp_cP D
            (Over.homMk (jFK (R := R) F) rfl : TF (R := R) F ⟶ TK R) _)
        rw [e]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel }
  have hX : ∀ y, ν'.eX (I.e y) = ν.eX y := fun y => ν'.eX.apply_symm_apply _
  refine ⟨I, rfl, hX, fun k p p' q q' h hq hq' => ⟨ν'.eX.injective (hq'.1.trans (h.1.trans (hq.1.symm.trans (hX _).symm))),
    ν'.eA.injective (hq'.2.1.trans (Over.OverMorphism.ext ?_)), fun χ => ?_⟩⟩
  · rw [h.2.1, ← hq.2.1]
    exact (congrArg (fun z => z.left) (eA_ptHom f hf ν ν' _)).symm
  · have e : q'.1.2.s (I.e χ) = (∏ i, T (DegPre.gtφ D F p.g.b (ν.eX χ) i) ^ DegPre.gtε i) *
        Units.map f.toMonoidHom (q.1.2.s χ) := by
      refine Units.ext ?_
      show _ = _ * f (q.1.2.s χ : F)
      rw [hq'.2.2, hq.2.2, hX]
      have c := hg _ _ _ _ _ (p.g.isGen (ν.eX χ)) (𝟙 (Sp F))
      simp only [Category.id_comp, Category.comp_id] at c
      refine Eq.trans ?_ c
      let y : Sp F' := IsLocalRing.closedPoint F'
      have hJ : Good D.P.L y ν'.J := fun ψ => ν'.good ψ trivial
      refine (stalkConst y).injective ((val_eq_vF ν'.good _ _ y).symm.trans (Eq.trans ?_ (val_eq_vF ν'.good _ _ y)))
      refine congrArg Units.val ((val_corr hJ (h.2.2 _) _).trans ((val_pull hJ _ _ _).trans ?_))
      rw [Category.id_comp]
    rw [e, prod_gt]
    show _ * (T (ν.eA (N.c χ * q.1.2.b)).left / _) = _ * (T (ν.eA (N.c χ)).left / _) * (T (ν.eA q.1.2.b).left / _)
    rw [map_mul, hq.2.1, ν.c_eq]
    show _ * (T (DVR.cP D (TF (R := R) F) (ν.eX χ) * p.g.b).left / _) =
      _ * (T (DVR.cP D (TF (R := R) F) (ν.eX χ)).left / _) * _
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div, ofMul_inv]; abel

end GlobalTheory.GaugeHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

theorem GlobalTheory.LN.exists_polAV_of_polAt : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)), PolAt t (jK R) → letI := H.starRing; ∃ (A : PolAV (Sp (FractionRing R))) (oA : A.OAct (𝓞 E)) (gen : (Over.pullback (jK R)).obj t.G ≅ A.A), IsMonHom gen.hom ∧ LBIso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) ∧ ∀ x, (Over.pullback (jK R)).map (t.act.act x) ≫ gen.hom = gen.hom ≫ oA.act x := by
  intro _ _ E _ _ _ H R _ _ t ⟨hp, hA, hK⟩
  let := H.starRing
  obtain ⟨PP', cub, sym, adj, prim, m₁, hm₁⟩ := sabPull CubePf.cubePull (jK R) t
  let t' : SAB H (Spec (CommRingCat.of (FractionRing R))) :=
    ⟨(Over.pullback (jK R)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      Geo.Tor.OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩
  let m₀ : SABMap t' t (jK R) := m₁
  have hm₀ : m₀.cm.F = pullback.fst t.G.hom (jK R) := hm₁
  obtain ⟨w, hw, -⟩ := m₀.lin
  have hL : LBIso t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := hm₀ ▸ ⟨w, hw⟩
  have hM := pull_isLB t.PP.isLB (pullback.fst t.G.hom (jK R))
  have hL' : LBIso t'.PP.L ((t.PP.L.pull (pullback.fst t.G.hom (jK R))).pull (𝟙 t'.G.left)) :=
    LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl) hL
  obtain ⟨v, hv⟩ := hL'
  have : IsMonHom (Iso.refl t'.G).hom := inferInstanceAs (IsMonHom (𝟙 t'.G))
  have hid : IsGrpPullback t'.G t'.G (𝟙 _) (𝟙 t'.G.left) := isGrpPullback_of_iso (Iso.refl t'.G)
  have hA' : RelAmple t'.G t'.PP.L :=
    relAmple_pull hid.1 hM t'.PP.isLB ((isGen_iff v).1 hv) ⊤ (isAffineOpen_top _) (fun _ => trivial) hA
  have hK' : KTriv t'.G t'.PP.L := kTriv_pull hid hM t'.PP.isLB ((isGen_iff v).1 hv) hK
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  have : ConnectedSpace ↥t'.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t'.G.hom) (𝟙 _) (𝟙 _) t'.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected t'.G.hom (Classical.arbitrary _)
  refine ⟨GenericPol.toPolAV t' g hg hp hA' hK', ⟨t'.act.toRingAct, GenericPol.rosatiAdj t'⟩, Iso.refl _,
    inferInstanceAs (IsMonHom (𝟙 t'.G)), ?_,
    fun a => ?_⟩
  · exact LBIso.chartPull (Geo.Tor.chartPullPull t'.PP.L (𝟙 _) (𝟙 _) rfl) (Geo.Tor.chartPullId _) hL
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationSpreadFromGenericFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidification_spread_from_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Rigidified A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Rigidified G' L' := by
  first | exact @GlobalTheory.GenSpread.exists_rigidified | exact GlobalTheory.GenSpread.exists_rigidified | (intros; apply GlobalTheory.GenSpread.exists_rigidified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSmoothOfRelativeDimensionSpreadFromGenericStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothOfRelativeDimension_spread_from_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ) (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → IsProper f → SmoothOfRelativeDimension n f₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), IsPullback π f' f (spMap g) → SmoothOfRelativeDimension n f' := by
  first | exact @GlobalTheory.GenSpread.exists_smoothOfRelativeDimension | exact GlobalTheory.GenSpread.exists_smoothOfRelativeDimension | (intros; apply GlobalTheory.GenSpread.exists_smoothOfRelativeDimension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ModelData

def Labels {O : Type} [CommRing O] (N : NumD O) {La : Type} [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La)
    (ζ : ℕ → Oˣ) (lab : ∀ k : ℕ, La → N.QT k) : Prop :=
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a * lab k b) (lab k (a + b))) ∧
  (∀ k, 0 < k → ∀ a b, N.QEq (lab k a) (lab k b) ↔ ∃ e, a = b + k • e) ∧
  (∀ k, 0 < k → ∀ p, ∃ a, N.QEq (lab k a) p) ∧
  (∀ k m, 0 < k → 0 < m → ∀ a (p : N.QT k), p.1.1 = (lab (k * m) a).1.1 → p.1.2 = (lab (k * m) a).1.2 ^ m →
    N.QEq p (lab k a)) ∧
  ∀ k, 0 < k → ∀ a b, N.wp (lab k a) (lab k b) = ζ k ^ EF a b

def Strict {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) : Prop :=
  ∃ c : L.ι → L'.ι, ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι), F (r z) ∈ L.U j →
    r z ∈ L'.U (c j) ∧ gw w r z j (c j) = 1

theorem exists_strict {X X' : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : X' ⟶ X) :
    ∃ w : LB.Iso (L.pull F) (L.pull F), w.IsGen ∧ Strict w := by
  have hL' := pull_isLB hL F
  refine ⟨⟨fun j => (L.pull F).g j.1 j.2⟩, (isGen_iff _).2 fun Y f y j j' k k' hj hj' hk hk' => ?_,
    fun j _ => j, fun Z r z j hj => ⟨mem_pull.2 hj, gm_self hL' r z (mem_pull.2 hj)⟩⟩
  have a := gm_cocycle hL' f y (i := fun _ => j) (j := fun _ => j') (k := k') (mem_pull.2 hj) (mem_pull.2 hj') hk'
  have b := gm_cocycle hL' f y (i := fun _ => j) (j := k) (k := k') (mem_pull.2 hj) hk hk'
  have c := gm_pull_g L F f y (fun _ => j) (fun _ => j') (mem_pull.2 hj) (mem_pull.2 hj')
  rw [c, ← b] at a
  show gm f y _ ((L.pull F).g (fun _ => j) k) = _ * _ * gm f y _ ((L.pull F).g (fun _ => j') k')
  rw [mul_right_comm, a, mul_inv_cancel_right]

end GlobalTheory.ModelData
end

