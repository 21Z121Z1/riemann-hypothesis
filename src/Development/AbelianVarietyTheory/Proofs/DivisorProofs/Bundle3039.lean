import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2966
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2906
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2967
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2886
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedExpansion_adicSums_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j : ℤ) (τ : SecE U.toUnifPre b n j) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)) (F : ∀ β, SecT D.toPre a n j β), Small (maximalIdeal R) s → IsSum (maximalIdeal R) s F → TExp U.toUnifPre τ s → TExp U.toUnifPre τ (w := id) F := by
  first | exact @GlobalTheory.TwFam.texp_sum | exact GlobalTheory.TwFam.texp_sum | (intros; apply GlobalTheory.TwFam.texp_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionMulOfMemberProductsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedExpansion_mul_of_memberProducts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ (e : ℕ) (b : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G), ∀ (n j n' j' n'' j'' : ℤ), n'' = n + n' → j'' = j + j' → ∀ (f : ∀ β, SecT D.toPre a n j β) (g : ∀ β, SecT D.toPre a n' j' β) (p : ∀ q : D.toPre.X × D.toPre.X, SecT D.toPre a n'' j'' (q.1 + q.2)) (τ : SecE U.toUnifPre b n j) (τ' : SecE U.toUnifPre b n' j') (τ'' : SecE U.toUnifPre b n'' j''), Small (maximalIdeal R) (w := id) f → Small (maximalIdeal R) (w := id) g → (∀ q : D.toPre.X × D.toPre.X, IsProdT (f q.1) (g q.2) (p q)) → TExp U.toUnifPre τ (w := id) f → TExp U.toUnifPre τ' (w := id) g → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ'' x z J' = sval τ x z J' * sval τ' x z J') → TExp U.toUnifPre τ'' (w := fun q : D.toPre.X × D.toPre.X => q.1 + q.2) p := by
  first | exact @GlobalTheory.TwFam.texp_mul_of_prod | exact GlobalTheory.TwFam.texp_mul_of_prod | (intros; apply GlobalTheory.TwFam.texp_mul_of_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGeneratStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (h : D.toPre.X →+ D.toPre.X), IsMonHom a → (∀ y, D.toPre.c (h y) = D.toPre.c y ≫ a) → ∀ (n j : ℤ) (mu β β' : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j))), u₀.IsGen → (∃ u, IsFac D.toPre a h n j mu β β' u) ∧ (∀ u u', IsFac D.toPre a h n j mu β β' u → IsFac D.toPre a h n j mu β β' u' → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → val u x z J = val u' x z J) ∧ ∀ u : LB.Gen (LB.LinComb D.toPre.P.L (dφ D.toPre a mu β β') (dε n j)), u.IsGen → ∃ c : (FractionRing R), ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) c) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val := by
  first | exact @GlobalTheory.TwFac.fac_exists_unique_const | exact GlobalTheory.TwFac.fac_exists_unique_const | (intros; apply GlobalTheory.TwFac.fac_exists_unique_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationBundleTrivialAbelianPar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam.Gen0

section General

variable {X Y : Scheme.{0}}

def fs {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : FreeAbelianGroup (Y ⟶ X) :=
  ∑ k, ε k • FreeAbelianGroup.of (φ k)

theorem formEq_of_fs {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : fs φ ε = fs φ' ε') : FormEq φ ε φ' ε' := by
  intro U _ g
  have e := congrArg (FreeAbelianGroup.lift (fun ψ => Additive.ofMul (g ψ))) h
  simp only [fs, map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of] at e
  apply Additive.ofMul.injective
  simpa [ofMul_prod, ofMul_zpow] using e

theorem oneGen_isGen' (L : LB X) : (LB.oneGen L (Y := Y)).IsGen := by
  intro i j
  have e : (LB.LinComb L (Y := Y) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i j = 1 := by
    dsimp only [LB.LinComb]
    erw [Fintype.prod_empty]
    rfl
  show res _ (1 : Γ(Y, _)ˣ) = _ * res _ (1 : Γ(Y, _)ˣ)
  rw [map_one, map_one, e, _root_.one_mul]

def genSub (L : LB X) (Y : Scheme.{0}) : AddSubgroup (FreeAbelianGroup (Y ⟶ X)) where
  carrier := {f | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ), fs φ ε = f ∧
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen}
  zero_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, by simp [fs], LB.oneGen L, oneGen_isGen' L⟩
  add_mem' := by
    rintro _ _ ⟨K, _, φ, ε, rfl, t, ht⟩ ⟨K', _, φ', ε', rfl, t', ht'⟩
    exact ⟨K ⊕ K', inferInstance, Sum.elim φ φ', Sum.elim ε ε', by simp [fs, Fintype.sum_sum_type],
      LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen L φ ε φ' ε' t t' ht ht'⟩
  neg_mem' := by
    rintro _ ⟨K, _, φ, ε, rfl, t, ht⟩
    exact ⟨K, inferInstance, φ, fun k => - ε k, by simp [fs, neg_smul, Finset.sum_neg_distrib],
      LB.invGen L φ ε t, DVR.invGen_isGen L φ ε t ht⟩

variable {L : LB X}

theorem mem_of_gen {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) : fs φ ε ∈ genSub L Y := ⟨K, inferInstance, φ, ε, rfl, t, ht⟩

theorem gen_of_mem (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : fs φ ε ∈ genSub L Y) : ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  obtain ⟨K', _, φ', ε', e, t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := exists_gen hL (formEq_of_fs e) t ht
  exact ⟨t', ht'⟩

theorem exists_cl (hL : L.IsLB) (Y : Scheme.{0}) : ∃ (U : Type) (_ : CommGroup U) (c : (Y ⟶ X) → U),
    ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ),
      (∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen) ↔ ∏ k, c (φ k) ^ ε k = 1 := by
  refine ⟨Multiplicative (FreeAbelianGroup (Y ⟶ X) ⧸ genSub L Y), inferInstance,
    fun ψ => Multiplicative.ofAdd (QuotientAddGroup.mk' _ (FreeAbelianGroup.of ψ)), fun K _ φ ε => ?_⟩
  have e : ∏ k, Multiplicative.ofAdd (QuotientAddGroup.mk' (genSub L Y) (FreeAbelianGroup.of (φ k))) ^ ε k =
      Multiplicative.ofAdd (QuotientAddGroup.mk' (genSub L Y) (fs φ ε)) := by
    simp only [fs, map_sum, map_zsmul, ofAdd_sum, ofAdd_zsmul]
  rw [e, ofAdd_eq_one, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  exact ⟨fun ⟨t, ht⟩ => mem_of_gen t ht, gen_of_mem hL⟩

end General

section Deg

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem exists_gen_twist [IsLocalRing R] (a : D.P.A ⟶ D.P.A) [IsMonHom a] (n j : ℤ) (mu ν δ β : D.X)
    (hν : D.c ν = D.c mu ≫ a) (u : LB.Gen (IotaLB D a ν δ)) (hu : u.IsGen) :
    ∃ u₀ : LB.Gen (LB.LinComb D.P.L (Sum.elim (tφ D a (β + (n • mu + j • δ)))
      (fun k => (padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)).left ≫ tφ D a β k)) (dε n j)), u₀.IsGen := by
  obtain ⟨U, _, c, hc⟩ := exists_cl D.P.isLB D.P.A.left
  have k₀ : ∀ q : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A, c (toUnit D.P.A ≫ q).left = 1 := fun q => by
    obtain ⟨t, ht⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := PUnit) (fun _ => q.left) (fun _ => 1)
    have h := (hc PUnit (fun _ => (toUnit D.P.A).left ≫ q.left) (fun _ => 1)).1 ⟨_, DVR.pullGen_isGen _ _ _ _ ht _⟩
    rw [Fintype.prod_unique, zpow_one] at h
    exact h
  have k₁ : c (1 : D.P.A ⟶ D.P.A).left = 1 := k₀ _
  have k₂ : ∀ χ, c (DVR.cP D D.P.A χ).left = 1 := fun χ => k₀ _
  have sq : ∀ χ χ', c (𝟙 _ * DVR.cP D D.P.A (χ + χ')).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left =
      c (𝟙 _ * DVR.cP D D.P.A χ).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left *
        (c (𝟙 _ * DVR.cP D D.P.A χ').left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left) := fun χ χ' => by
    have h := (prod_cub (𝟙 D.P.A) (DVR.cP D _ χ) (DVR.cP D _ χ') c).symm.trans ((hc thK _ thε).1
      ⟨LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t _, DVR.pullGen_isGen _ _ _ _ D.cub.isGen _⟩)
    rw [_root_.mul_assoc (𝟙 D.P.A), ← DVR.cPoint_add, k₂, k₂, k₂, k₁] at h
    rw [← div_eq_one, ← h]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
    abel
  let Φ : D.X →+ Additive U := AddMonoidHom.mk' (fun χ => Additive.ofMul
    (c (𝟙 _ * DVR.cP D D.P.A χ).left / c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left)) (fun χ χ' => congrArg Additive.ofMul (sq χ χ'))
  have e : ∀ χ, Additive.ofMul (c (𝟙 _ * DVR.cP D D.P.A χ).left) =
      Φ χ + Additive.ofMul (c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left) := fun χ =>
    congrArg Additive.ofMul (div_mul_cancel _ _).symm
  clear_value Φ
  have e₃ : Additive.ofMul (c (a * DVR.cP D _ ν).left) = Φ δ + Additive.ofMul (c a.left) := by
    have h := (hc _ _ _).1 ⟨u, hu⟩
    rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four] at h
    have h' : c (𝟙 _ * DVR.cP D D.P.A δ).left ^ (1 : ℤ) * c (DVR.cP D D.P.A δ).left ^ (-1 : ℤ) *
        c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ) * c (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) *
        (c (a * DVR.cP D D.P.A ν).left ^ (-1 : ℤ) * c (DVR.cP D D.P.A ν).left ^ (1 : ℤ) * c a.left ^ (1 : ℤ) *
          c (1 : D.P.A ⟶ D.P.A).left ^ (-1 : ℤ)) = 1 := h
    have h'' := congrArg Additive.ofMul h'
    simp only [ofMul_mul, ofMul_zpow, k₁, k₂, e, ofMul_one] at h''
    rw [eq_comm, ← sub_eq_zero, ← h'']
    module
  let T : D.P.A ⟶ D.P.A := 𝟙 _ * DVR.cP D _ mu
  have i₀ : T ≫ 𝟙 _ = 𝟙 _ * DVR.cP D _ mu := Category.comp_id _
  have i₁ : T ≫ (𝟙 _ * DVR.cP D _ β) = 𝟙 _ * DVR.cP D _ (mu + β) := by
    rw [MonObj.comp_mul, DVR.comp_cP, i₀, DVR.cPoint_add, _root_.mul_assoc]
  have i₂ : T ≫ DVR.cP D _ β = DVR.cP D _ β := DVR.comp_cP D _ _
  have i₃ : T ≫ (1 : D.P.A ⟶ D.P.A) = 1 := MonObj.comp_one _
  have i₄ : T ≫ a = a * DVR.cP D _ ν := by
    rw [MonObj.mul_comp, Category.id_comp, DVR.cP, DVR.cP, hν, Category.assoc]
  have h : c (𝟙 D.P.A : D.P.A ⟶ D.P.A).left ^ (n - 1) * c (𝟙 _ * DVR.cP D D.P.A (β + (n • mu + j • δ))).left ^ (1 : ℤ) *
      c (DVR.cP D D.P.A (β + (n • mu + j • δ))).left ^ (-1 : ℤ) * c (1 : D.P.A ⟶ D.P.A).left ^ (1 : ℤ) * c a.left ^ j *
      (c (T ≫ 𝟙 _).left ^ (-(n - 1)) * c (T ≫ (𝟙 _ * DVR.cP D _ β)).left ^ (-1 : ℤ) *
        c (T ≫ DVR.cP D _ β).left ^ (-(-1) : ℤ) * c (T ≫ (1 : D.P.A ⟶ D.P.A)).left ^ (-1 : ℤ) * c (T ≫ a).left ^ (-j)) = 1 := by
    rw [i₀, i₁, i₂, i₃, i₄]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, k₁, k₂, e, e₃, ofMul_one, map_add, map_zsmul]
    module
  refine (hc _ _ _).2 ?_
  rw [Fintype.prod_sum_type, Fin.prod_univ_five, Fin.prod_univ_five]
  exact h

end Deg

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (n j : ℤ) (mu β β' : D.toPre.X), β' = β + shift h h' n j mu → ∃ u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a β') (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c mu)).left ≫ tφ D.toPre a β k)) (dε n j)), u₀.IsGen := by
  intro R _ _ _ hR D a a' h h' hE n j mu β β' hβ
  obtain ⟨u, hu, -⟩ := exists_iota R hR D a a' h h' hE (h mu)
  haveI := hE.1
  subst hβ
  exact exists_gen_twist D.toPre a n j mu (h mu) (h' (h mu)) β (hE.2.2.2.1 mu) u hu

end GlobalTheory.TwFam.Gen0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationPullbackOfIntegralThetaFunctionalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedRelation_pullback_of_integralThetaFunctionalEquation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (mu α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))) (u' : LB.Gen (IotaLB D.toPre a (α + k • h mu) (h' (α + k • h mu)))) (s : SecT D.toPre a 0 k (h' α)) (s' : SecT D.toPre a 0 k (h' (α + k • h mu))), IsIota u → IsIota u' → IsPullT u (F.f α) s → IsPullT u' (F.f (α + k • h mu)) s' → TRel h mu s s' := by
  first | exact @GlobalTheory.TwFam.PullRel.main | exact GlobalTheory.TwFam.PullRel.main | (intros; apply GlobalTheory.TwFam.PullRel.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoFlagsSineSquaredIdentity
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocalLelong

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.HermFrame (kappa)

section Point

variable {n : ℕ}

theorem del_mul_dbar {F φ₁ φ₀ : V n → ℝ} {g : V n → ℂ} {z : V n} (hg : ContDiffAt ℂ 2 g z)
    (h₁ : ContDiffAt ℝ 2 φ₁ z) (h₀ : ContDiffAt ℝ 2 φ₀ z)
    (e : F =ᶠ[𝓝 z] fun u => ‖g u‖ ^ 2 * Real.exp (-(φ₁ u - φ₀ u))) :
    ContDiffAt ℝ 2 F z ∧ ∀ ξ η : V n, del (fun u => (F u : ℂ)) z ξ * dbar (fun u => (F u : ℂ)) z η =
      F z * (leviForm F z ξ η + F z * (leviForm φ₁ z ξ η - leviForm φ₀ z ξ η)) := by
  have hn : ContDiffAt ℝ 2 (fun u => ‖g u‖ ^ 2) z := (hg.restrict_scalars ℝ).norm_sq ℂ
  have hF : ContDiffAt ℝ 2 F z := (hn.mul (h₁.sub h₀).neg.exp).congr_of_eventuallyEq e
  refine ⟨hF, fun ξ η => ?_⟩
  by_cases h : g z = 0
  · have hz : F z = 0 := by rw [e.self_of_nhds]; simp [h]
    have hm : IsLocalMin F z := e.mono fun u hu => by rw [hz, hu]; positivity
    have hd := hF.differentiableAt two_ne_zero
    rw [hz, del_apply, fderiv_ofReal_apply hd, fderiv_ofReal_apply hd, hm.fderiv_eq_zero]
    simp
  · have hz : F z ≠ 0 := by rw [e.self_of_nhds]; positivity
    have hl : ContDiffAt ℝ 2 (fun u => Real.log (‖g u‖ ^ 2)) z := hn.log (by simpa using h)
    have e₁ : (fun u => Real.log (F u)) =ᶠ[𝓝 z] fun u => Real.log (‖g u‖ ^ 2) - (φ₁ u - φ₀ u) := by
      filter_upwards [e, hg.continuousAt.eventually_ne h] with u hu hu'
      rw [hu, Real.log_mul (by positivity) (by positivity), Real.log_exp, sub_eq_add_neg _ (_ - _)]
    have e₂ := leviForm_real_comp (h := Real.log) (Real.contDiffAt_log.2 hz) hF ξ η
    rw [leviForm_congr e₁, leviForm_sub hl (h₁.sub h₀), leviForm_log_normSq_eq_zero hg h, leviForm_sub h₁ h₀,
      Real.deriv_log', deriv_inv] at e₂
    have hz' : (F z : ℂ) ≠ 0 := by exact_mod_cast hz
    simp only [zero_sub, ContinuousLinearMap.neg_apply, ContinuousLinearMap.sub_apply] at e₂
    push_cast at e₂
    field_simp at e₂
    linear_combination e₂

theorem delAt_fun (u : V n → ℂ) (v : V n) :
    delAt (fun x => algebraMap ℂ (Alt n) (u x)) v = ∑ a, del u v (coordVec a) • dz a := by
  simp only [delAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dbarAt_fun (u : V n → ℂ) (v : V n) :
    dbarAt (fun x => algebraMap ℂ (Alt n) (u x)) v = ∑ a, dbar u v (coordVec a) • dzb a := by
  simp only [dbarAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem coe_ofValues (α : V n → V n → ℂ) :
    (ofValues α : Alt n) = ∑ a, ∑ b, α (coordVec a) (coordVec b) • (dz a * dzb b) := by
  simp only [ofValues, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym]

theorem delAt_mul_dbarAt {F φ₁ φ₀ : V n → ℝ} {g : V n → ℂ} {z : V n} (hg : ContDiffAt ℂ 2 g z)
    (h₁ : ContDiffAt ℝ 2 φ₁ z) (h₀ : ContDiffAt ℝ 2 φ₀ z)
    (e : F =ᶠ[𝓝 z] fun u => ‖g u‖ ^ 2 * Real.exp (-(φ₁ u - φ₀ u))) :
    kappa • (delAt (fun x => algebraMap ℂ (Alt n) (F x)) z * dbarAt (fun x => algebraMap ℂ (Alt n) (F x)) z) =
      algebraMap ℂ (Alt n) (F z) * (kappa • delAt (dbarAt fun x => algebraMap ℂ (Alt n) (F x)) z +
        algebraMap ℂ (Alt n) (F z) * ((ofValues (HermFrame.ddc φ₁ z) : Alt n) - ofValues (HermFrame.ddc φ₀ z))) := by
  obtain ⟨hF, key⟩ := del_mul_dbar hg h₁ h₀ e
  rw [delAt_dbarAt_fun hF, delAt_fun, dbarAt_fun, ← Algebra.smul_def, ← Algebra.smul_def, Finset.sum_mul_sum]
  simp only [coe_ofValues, smul_mul_smul_comm, key, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul, ← sub_smul, ← add_smul, HermFrame.ddc]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

end Point

theorem del_mul_dbar_fn {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (f : M → ℝ) (x : A.Pt)
    {φ₁ φ₀ : V n → ℝ} {g : V n → ℂ} (hg : ContDiffAt ℂ 2 g x.crd)
    (h₁ : ContDiffAt ℝ 2 φ₁ x.crd) (h₀ : ContDiffAt ℝ 2 φ₀ x.crd)
    (e : (fun u => f (x.ch.symm u)) =ᶠ[𝓝 x.crd] fun u => ‖g u‖ ^ 2 * Real.exp (-(φ₁ u - φ₀ u))) :
    kappa • (A.del (A.fn f) x * A.dbar (A.fn f) x) = A.fn f x * (A.ddc (A.fn f) x +
      A.fn f x * ((ofValues (HermFrame.ddc φ₁ x.crd) : Alt n) - ofValues (HermFrame.ddc φ₀ x.crd))) := by
  have hc : x.crd ∈ x.ch.target := x.ch.map_source x.2
  have l₁ (v) (hv : v ∈ x.ch.target) : A.loc (A.fn f) x.1.1 =ᶠ[𝓝 v]
      fun u => algebraMap ℂ (Alt n) (f (x.ch.symm u)) := by
    filter_upwards [x.ch.open_target.mem_nhds hv] with u hu
    rw [HolAtlas.loc, dif_pos hu]
    rfl
  have l₂ : A.loc (A.dbar (A.fn f)) x.1.1 =ᶠ[𝓝 x.crd] dbarAt fun u => algebraMap ℂ (Alt n) (f (x.ch.symm u)) := by
    filter_upwards [x.ch.open_target.mem_nhds hc] with u hu
    rw [HolAtlas.loc, dif_pos hu, ← ((delAt_dbarAt_linear_local n u).2.2.2.1 _ _ (l₁ u hu)).2]
    exact congrArg (dbarAt _) (x.ch.right_inv hu)
  have key := delAt_mul_dbarAt hg h₁ h₀ e
  rw [← ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ l₂).1, ← ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ (l₁ _ hc)).1,
    ← ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ (l₁ _ hc)).2, x.ch.left_inv x.2] at key
  exact key

section Lines

open GlobalTheory.VMetric GlobalTheory.CurveDens
open GlobalTheory.Twist (resM resM_resM)
open scoped ComplexOrder

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem isFrame_resM {F : X.Modules} (c : Chart F 1) {U : X.Opens} (h : U ≤ c.U) :
    IsFrame fun _ : Fin 1 => resM F h (c.e 0) := fun W hW => by
  convert c.isFrame W (hW.trans h) using 3
  funext i
  rw [resM_resM, Subsingleton.elim i 0]

theorem form_frame_eq_exp {F : X.Modules} (m : Met p σ F 1) (c : Chart F 1) {U : X.Opens} (h : U ≤ c.U) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ U) :
    (m.form (resM F h (c.e 0)) (resM F h (c.e 0)) y).re = Real.exp (-m.detWeight.φ c y) := by
  have hc := ptsIn_mono h hy
  have hp := (Complex.pos_iff.1 ((m.posDef c y hc).diag_pos (i := 0))).1
  rw [m.form_resM _ _ h hy, m.form_frame c hc]
  change _ = Real.exp (- -Real.log (m.G c y).det.re)
  rw [neg_neg, Matrix.det_fin_one, Real.exp_log hp]

theorem two_flags [IsIntegral X] {D : ℕ} (hX : IsRegVar p D) {W : X.Modules} {h : VMetric p W 2} (H : h.IsCInf)
    (fl fl' : Vert.Flag W 2) {v : CxPts p σ → ℝ} (hv : IsCosSq (h.met σ) (fl.ι 1) (fl'.ι 1) v) (x : (hX.atlas σ).Pt) :
    kappa • ((hX.atlas σ).del ((hX.atlas σ).fn fun y => 1 - v y) x * (hX.atlas σ).dbar ((hX.atlas σ).fn fun y => 1 - v y) x) =
      (hX.atlas σ).fn (fun y => 1 - v y) x * ((hX.atlas σ).ddc ((hX.atlas σ).fn fun y => 1 - v y) x +
        (hX.atlas σ).fn (fun y => 1 - v y) x *
          ((c1F hX σ (grLB fl' 1 H) x : Alt D) - c1F hX σ (grLB fl 0 H) x)) := by
  have hS := shortExact_lineQuot fl'
  have hL := fl'.isVB 1
  have hL' := fl.isVB 1
  have hQ := fl'.isVB_gr 1
  have hl := fl'.isSubbundle 1
  have hl' := fl.isSubbundle 1
  have HQ := IsCInf.quot (S := .mk _ _ (line_lineQuot fl')) (r := 1) (s := 1) hS hL hQ H
  rw [← c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_zero H fl),
    ← c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_one H fl')]
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have hy' : y ∈ c.e.source := hy
  let a : Chart (fl'.F 1) 1 := hL.pick y
  let b : Chart (fl.F 1) 1 := hL'.pick y
  let e : Chart (fl'.gr 1) 1 := hQ.pick y
  let U : X.Opens := a.U ⊓ (b.U ⊓ e.U)
  have ha : U ≤ a.U := inf_le_left
  have hb : U ≤ b.U := inf_le_right.trans inf_le_left
  have he : U ≤ e.U := inf_le_right.trans inf_le_right
  have hU : y ∈ ptsIn p σ U := mem_ptsIn_inf.2 ⟨hL.mem_pick y, mem_ptsIn_inf.2 ⟨hL'.mem_pick y, hQ.mem_pick y⟩⟩
  obtain ⟨g, hg⟩ := exists_smul_frame e le_rfl he ((fl.ι 1 ≫ lineQuot fl').app U (resM _ hb (b.e 0)))
  rw [resM_resM] at hg
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
  have hm := ChartGlue.mem_over c.e hy' hU
  have hf : ContDiffAt ℂ 2 (ev p σ _ g ∘ c.e.symm) (c.e y) :=
    (SCV.analyticAt_of_differentiableOn (c.holo _ g) (ho.mem_nhds hm)).contDiffAt
  refine del_mul_dbar_fn (hX.atlas σ) _ ⟨(c, y), hy⟩ hf
    (((VMetric.det HQ).cInf σ).contDiffAt c hy' (mem_pick _ y))
    (((VMetric.det (H.restrict hl' hL')).cInf σ).contDiffAt c hy' (mem_pick _ y)) ?_
  filter_upwards [ho.mem_nhds hm] with u hu
  have key := AdjFlag.div_eq_one_sub hS hL hQ hL' hl hl' (h.met σ) hv.symm (isFrame_resM a ha) (isFrame_resM b hb) hu.2
  rw [hg, form_smul_smul, Complex.mul_conj, Complex.re_ofReal_mul, form_frame_eq_exp _ _ _ hu.2,
    form_frame_eq_exp _ _ _ hu.2, Complex.normSq_eq_norm_sq, mul_div_assoc, ← Real.exp_sub] at key
  refine key.symm.trans (congrArg (_ * Real.exp ·) ?_)
  rw [neg_sub_neg, neg_sub]
  rfl

end Lines

theorem local_identity : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    GlobalTheory.HermFrame.kappa • ((hY.atlas σ).del ((hY.atlas σ).fn (fun y => 1 - v y)) * (hY.atlas σ).dbar ((hY.atlas σ).fn (fun y => 1 - v y))) = ((hY.atlas σ).fn (fun y => 1 - v y)) * ((hY.atlas σ).ddc ((hY.atlas σ).fn (fun y => 1 - v y)) + ((hY.atlas σ).fn (fun y => 1 - v y)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 4 - X 0)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl _ A σ v hv
  funext x
  have key := two_flags hY (H.pull π w) fl (flB.pull π) hv x
  rw [c1F_eq_of_isometric k Y p _ hY σ _ _ (VMetric.isometric_grLB_pull k B Y q p E 2 h H flB π w 1)] at key
  refine key.trans ?_
  simp only [Pi.mul_apply, Pi.add_apply, evalF, fld, map_sub, map_X, aeval_X, Subalgebra.coe_sub]
  rfl

end GlobalTheory.LocalLelong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCubicalStructureGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericCube

theorem exists_iso_section {X H Y : Scheme.{0}} {L : LB X} {M : LB H} {f : Y ⟶ H} {ψ : Y ⟶ X} (g : H ⟶ Y)
    (hg : g ≫ f = 𝟙 H) (w : LB.Iso (M.pull f) (L.pull ψ)) (hw : w.IsGen) :
    ∃ w' : LB.Iso M (L.pull (g ≫ ψ)), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) (j : L.ι) (k : M.ι),
      ψ (g (r z)) ∈ L.U j → r z ∈ M.U k → Geo.Tor.gw w' r z j k = Geo.Tor.gw w (r ≫ g) z j (fun _ => k) := by
  have mm : ∀ (y : H) (k : M.ι), y ∈ M.U k → g y ∈ (M.pull f).U (fun _ => k) := fun y k hy => mem_pull.2 (by
    have e : (g ≫ f) y = y := by rw [hg]; rfl
    exact (congrArg (· ∈ M.U k) e).mpr hy)
  have le : ∀ (j : L.ι) (k : M.ι), (L.pull (g ≫ ψ)).U (fun _ => j) ⊓ M.U k ≤
      g ⁻¹ᵁ ((L.pull ψ).U (fun _ => j) ⊓ (M.pull f).U (fun _ => k)) := fun j k y hy =>
    ⟨mem_pull.2 (mem_pull₂.1 hy.1), mm y k hy.2⟩
  let w' : LB.Iso M (L.pull (g ≫ ψ)) :=
    ⟨fun p => res (le (p.1 PUnit.unit) p.2) (pullU g _ (w.s (fun _ => p.1 PUnit.unit, fun _ => p.2)))⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) (j : L.ι) (k : M.ι),
      ψ (g (r z)) ∈ L.U j → r z ∈ M.U k → Geo.Tor.gw w' r z j k = Geo.Tor.gw w (r ≫ g) z j (fun _ => k) :=
    fun Z r z j k hj hk => by
      have m : r z ∈ (L.pull (g ≫ ψ)).U (fun _ => j) ⊓ M.U k := ⟨mem_pull₂.2 hj, hk⟩
      exact (gm_res r z (le j k) m _).trans (gm_pull r g z _ (le j k m) _)
  refine ⟨w', (isGen_iff w').2 fun Z r z j j' k k' hj hj' hk hk' => ?_, hv⟩
  have e := (isGen_iff w).1 hw Z (r ≫ g) z j j' (fun _ => k) (fun _ => k') hj hj' (mm _ k hk) (mm _ k' hk')
  rw [Geo.Tor.gm_pull_g M f (r ≫ g) z _ _ (mm _ k hk) (mm _ k' hk'), Category.assoc r g f, hg, Category.comp_id,
    Category.assoc] at e
  rw [hv Z r z j k hj hk, hv Z r z j' k' hj' hk']
  exact e

theorem cube_through_iso : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (h : Finset (Fin 3) → ((𝟙_ (Over (Sp V))) ⟶ G)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → h ∅ = 1 → h {0, 1} = h {0} * h {1} → h {0, 2} = h {0} * h {2} → h {1, 2} = h {1} * h {2} → h {0, 1, 2} = h {0} * h {1} * h {2} → (∀ S, IntTerm.Ext U.toUnifPre (x S) (h S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1, 2}).left) (fun _ => JA (x {0, 1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}).left) (fun _ => JA (x {0}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}).left) (fun _ => JA (x {1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}).left) (fun _ => JA (x {2}).left)) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) = cubV U.cubG z JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}) * (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1}).left) (fun _ => JA (x {0, 1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 2}).left) (fun _ => JA (x {0, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1, 2}).left) (fun _ => JA (x {1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x ∅).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h ∅).left) (fun _ => JA (x ∅).left)) := by
  intro V _ _ _ _ D A G _ _ _ U w₀ hw₀ ρ hρ c x h x0 x01 x02 x12 x012 h0 h01 h02 h12 h012 hE z JA JG hJA hJG
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK V) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  obtain ⟨w, hw, hv⟩ := exists_iso_section U.gen.inv.left (congrArg (fun q => q.left) U.gen.inv_hom_id) w₀ hw₀
  have e := cub_w U.cubG c GlobalTheory.abelianSchemeLaws_all.1.globalFns A.isAb gp w hw
    (s' := jFK (R := V) (FractionRing V)) (s := jFK (R := V) (FractionRing V) ≫ jK V) (z := z) hJG hJA
    (x {0}) (x {1}) (x {2}) _ _ _ (hE {0}) (hE {1}) (hE {2})
  have k : ∀ S, Om w (s' := jFK (R := V) (FractionRing V)) z JG JA (x S) =
      Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x S).left ≫ U.gen.inv.left) z
        (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h S).left) (fun _ => JA (x S).left) := fun S => by
    refine (hv _ (x S).left z _ _ (hJG ((x S).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V))) (hJA _)).trans ?_
    exact congrArg (fun q => Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x S).left ≫ U.gen.inv.left) z
      (JG q) (fun _ => JA (x S).left)) (hE S)
  rw [← x012, ← x01, ← x02, ← x12, ← x0, k, k, k, k, k, k, k, k] at e
  refine Eq.trans ?_ (congrArg (· * _) e.symm)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, id]
  abel

end GlobalTheory.GenericCube
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGenericFibreEqSiegelFibrePullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_genericFibre_eq_siegelFibre_pullback : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (J' : Ideal V) (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀) (f : R →+* V) (D : DegData V J') (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif J' D A ((Over.pullback (specOf f)).obj G₀)), IsPullUnif f hD (Iso.refl _) U₀ U → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ κ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ ≫ jK R = jK V ≫ spMap f → ∃ α : A.A.left ⟶ c.A.left, OverPt c A (κ ≫ y₀) α ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ A.A.left) (x₀ : Z ⟶ A₀.A.left), x ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = x₀ ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) → x ≫ α = x₀ ≫ α₀ := by
  first | exact @GlobalTheory.TInj.overPt_genPull | exact GlobalTheory.TInj.overPt_genPull | (intros; apply GlobalTheory.TInj.overPt_genPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackAlongIdLiesOverDataIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationPullbackAlongId_lies_over_dataIso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (ψ : G ⟶ G) (bc : G ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (b : D'.toPre.P.A ⟶ D.toPre.P.A), IsMonHom ψ → bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.left → hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = b.left → IsPullUnif (RingHom.id R) hD bc U U' → Over₀ U'.toUnifPre U.toUnifPre ψ b ∧ OnTorus U'.toUnifPre U.toUnifPre ψ hD.xe.symm := by
  first | exact @GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus | exact GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus | (intros; apply GlobalTheory.Mum.Two.isPullUnif_id_over₀_onTorus <;> assumption)
end

